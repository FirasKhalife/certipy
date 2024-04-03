(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Production of Python syntax. *)

open Pp
open CErrors
open Util
open Names
open ModPath
open Table
open Miniml
open Mlutil
open Modutil
open Common
open Python_pp
open Python_ast

let starting_sym = Char.code 'a' - 1
let r = ref (starting_sym)
let reset_gensym () = r := starting_sym
let gensym () = incr r; String.make 1 (Char.chr !r)

module StringMap = Map.Make(String)
module RefMap = GlobRef.Map

(** a map of record field names to their getter name,
    in order to use the getter with its name possibly changed for renaming purposes *)
let getter_map = ref StringMap.empty

let add_getter_map key value = getter_map := StringMap.add key value !getter_map

let find_getter_map key = StringMap.find key !getter_map

(** a map of record constructors refs to their type ref,
   in order to use the record type only in the extracted code *)
let record_map = ref RefMap.empty

let add_record_map key value = record_map := RefMap.add key value !record_map

let find_record_map key = RefMap.find key !record_map

(** returns Type and the type ref of the constructor if the constructor ref is found ,
    else Cons and the constructor itself *)
let type_if_record_cons key =
  try Type, find_record_map key
  with Not_found -> Cons, key

(* let fst3 (a,_,_) = a *)

let tl_empty = function
  | [] -> []
  | _ :: l -> l

let cut2_infix_if_both a1 a2 = a1 ++ (if Pp.ismt a1 || Pp.ismt a2 then mt () else cut2 ()) ++ a2

let axiom_not_realized_msg = "AXIOM TO BE REALIZED"

let push_args_lam_fun_names ids env =
  let fun_names, env =
    py_push_vars ~save_db:false (List.map (fun id ->  py_fun_of_str id) ids) env in
  fun_names, env

let push_args_fun_names args env =
  let fun_names, env =
    py_push_vars ~save_db:false (List.map (fun a ->  py_fun_of_str (fst a)) args) env in
  fun_names, env

let push_var_fun_name id env =
  let fun_name, env = py_push_vars ~save_db:false [py_fun_of_str id] env in
  let fun_name = List.hd fun_name in
  fun_name, env

(* from the Python Language Reference 3.12.1, "Identifiers and Keywords" *)
let keywords =
  List.fold_right (fun s -> Id.Set.add (Id.of_string s))
  [ "False"; "None"; "True"; "and"; "as"; "assert"; "async"; "await";
    "break"; "class"; "continue"; "def"; "del"; "elif"; "else"; "except";
    "finally"; "for"; "from"; "global"; "if"; "import"; "in"; "is";
    "lambda"; "nonlocal"; "not"; "or"; "pass"; "raise"; "return";
    "try"; "while"; "with"; "yield" ]
  Id.Set.empty

(* the key is the canonical name, simply kn *)
let str_global_with_key ?(save = true) ?(snake_case = true) ?(prfx = "") k key r : string =
  if is_custom r then find_custom r
  else Common.str_py_global_with_key save snake_case prfx k key r

let str_global ?(save = true) ?(snake_case = true) ?(prfx = "") k r =
  str_global_with_key ~snake_case:snake_case ~prfx:prfx k (repr_of_r r) r

let pp_global ?(snake_case = true) ?(prfx = "") k r =
  str (str_global ~snake_case:snake_case ~prfx:prfx k r)

let pp_modname mp = str (Common.pp_module mp)

(* gets inductive reference, possibly extracting it from inductive constructor *)
let get_ind = let open GlobRef in function
  | IndRef _ as r -> r
  | ConstructRef (ind,_) -> IndRef ind
  | _ -> assert false

(* extracts user facing name from inductive reference *)
let kn_of_ind = let open GlobRef in function
  | IndRef (kn,_) -> MutInd.user kn
  | _ -> assert false

let str_one_field r i = function
  | Some r' -> str_global_with_key ~save:false Term (kn_of_ind (get_ind r)) r'
  | None -> str_global ~save:false Type (get_ind r) ^ "__" ^ (string_of_int i)

let str_field r fields i = str_one_field r i (List.nth fields i)

let str_fields r fields = List.map_i (str_one_field r) 0 fields

let is_bool_patt p s =
  try
    let r = match p with
      | Pusual r -> r
      | Pcons (r,[]) -> r
      | _ -> raise Not_found
    in
    String.equal (find_custom r) s
  with Not_found -> false

let is_ifthenelse = function
  | [|([],p1,_);([],p2,_)|] -> is_bool_patt p1 "True" && is_bool_patt p2 "False"
  | _ -> false

let rec extract_definition_top original_env name t a =
  let bl,a' = collect_lams a in
  let is_fun = is_pystatement_rec a' in
  (* not a py_statement and no args -> extracted as a variable*)
  if not is_fun && List.is_empty bl then
    let expr, _, env = extract_expr original_env a' in
    PyAssign (name, expr), env
  else
    (* py_statement or args -> extracted as a function *)
    let bl,env = py_push_vars (List.map id_of_mlid bl) original_env in
    let tv, params =
      match t with
      | None -> [||], []
      | Some t ->
          Array.map_of_list (extract_type []) (fst (collect_tarrs t)),
          (* List.fold_left (fun xs x -> if List.mem x xs then xs else x :: xs) [] |> *)
          List.map (fun i -> PyTypeId ("A" ^ string_of_int i)) (get_type_params t)
    in
    let args =
      List.rev (
        List.mapi (fun i id -> id, if i < Array.length tv then Some tv.(i) else None) bl)
    in
    let fun_names, env = push_args_fun_names (tl_empty args) env in
    let fun_args = List.combine (fun_names) (tl_empty args) in
    let body_stmt, env = extract_stmt env a' in
    let first_arg = if List.is_empty args then [] else [List.hd args] in
    PyFunDef (name, params, first_arg, nest_fundefs fun_args body_stmt), original_env

and extract_definition env name t a =
  let bl,a' = collect_lams a in
  let is_fun = is_pystatement_rec a' in
  (* if no args *)
  if is_fun && List.is_empty bl then
    (* no args, pystatement -> extracted as function then stored in a variable *)
    let fun_name, outer_env = push_var_fun_name name env in
    let stmt, env = extract_stmt env a' in
    PyFunDef (fun_name, [], [], stmt)
    :: PyAssign (name, (PyApp (PyId fun_name, [])))
    :: [], outer_env
  else
    let stmt, outer_env = extract_definition_top env name t a in
    [stmt], outer_env

and extract_type vl : ml_type -> py_type = function
  | Tmeta _ | Tvar' _ | Taxiom -> assert false
  | Tvar i ->
      (try PyTypeId (Id.to_string (List.nth vl (pred i)))
        with Failure _ -> PyTypeId ("A" ^ string_of_int i))
  | Tglob (r,[]) ->
      PyTypeId (str_global ~snake_case:false Type r)
  | Tglob (r,l) ->
      PyTypeGeneric (str_global ~snake_case:false Type r, List.map (extract_type vl) l)
  | Tarr (t1, t2) ->
      (* Callable[t1, t2] *)
      PyTypeGeneric ("Callable", extract_type vl t1 :: extract_type vl t2 :: [])
  | Tdummy _ -> PyTypeId "__"
  | Tunknown -> PyTypeId "__"

and get_type_params t =
  let rec get_params_rec acc = function
    | Tmeta _ | Tvar' _ | Taxiom -> acc
    | Tdummy _ | Tunknown -> acc
    | Tvar i ->
        if not (List.exists (Int.equal i) acc) then i :: acc
        else acc
    | Tglob (_,l) ->
        if not (List.is_empty l) then List.fold_left (get_params_rec) acc l
        else acc
    | Tarr (a1,a2) -> get_params_rec (get_params_rec acc a1) a2
  in
  List.rev (get_params_rec [] t)

and is_pystatement = function
| MLfix _ | MLexn _ | MLaxiom | MLletin _ -> true
| MLlam _ as a -> is_pystatement (snd (collect_lams a))
| MLmagic a -> is_pystatement a
| MLcase (typ, t, pv) ->
    not (is_custom_match pv)
    && not (is_ifthenelse pv)
    && not (is_record_proj typ t pv)
| _ -> false

and is_pystatement_rec = function
  | MLfix _ | MLexn _ | MLaxiom -> true
  | MLletin (_, a1, a2) -> is_pystatement_rec a1 || is_pystatement_rec a2
  | MLlam _ as a -> is_pystatement_rec (snd (collect_lams a))
  | MLapp (f, args) -> is_pystatement_rec f || List.exists (is_pystatement_rec) args
  | MLcons (_,_, args) -> List.exists is_pystatement_rec args
  | MLmagic a -> is_pystatement_rec a
  | MLcase (typ, t, pv) ->
      not (is_custom_match pv)
      && not (is_ifthenelse pv)
      && not (is_record_proj typ t pv)
  | _ -> false

and expr_to_stmt env expr : py_expr * py_stmt list * env =
  if not (is_pystatement expr) then extract_expr env expr
  else
    match expr with
    | MLlam (id, a) ->
      let arg, env' = py_push_vars [id_of_mlid id] env in
      let body_stmt, _ = extract_stmt env' a in
      let arg = List.hd arg in
      let fun_name, env = push_args_fun_names [(arg, None)] env in
      let fun_name = List.hd fun_name in
      PyId fun_name,
      [PyStmtTop (PyFunDef (fun_name, [], [(arg, None)], body_stmt))],
      env
    | _ ->
      let expr_stmt, env = extract_stmt env expr in
      let stmt_name, env = py_push_vars ~save_db:false [Id.of_string "_aux_fun"] env in
      let stmt_name = List.hd stmt_name in
      PyApp (PyId stmt_name, []),
      [PyStmtTop (PyFunDef (stmt_name, [], [], expr_stmt))],
      env

and map_expr_to_stmt env = function
  | [] -> [], [], env
  | exp :: exps ->
      let py_exp, exp_stmt, env = expr_to_stmt env exp in
      let py_exps, exps_stmt, env = map_expr_to_stmt env exps in
      (py_exp :: py_exps), (exp_stmt @ exps_stmt), env

and extract_stmt env = function
  | MLrel _ | MLglob _
  | MLapp _ | MLcons _ | MLtuple _
  | MLuint _ | MLfloat _ | MLparray _ as exp ->
      let py_exp, stmts, env = extract_expr env exp in
      stmts @ [PyStmtFunDef (PyReturn py_exp)], env
  | MLlam _ as a ->
      let ids,a' = collect_lams a in
      let ids,env' = py_push_vars (List.map id_of_mlid ids) env in
      let fun_names,env' = push_args_lam_fun_names ids env' in
      let args = List.map (fun id -> (id, None)) ids in
      let body, _ = extract_stmt env' a' in
      nest_fundefs (List.combine fun_names args) body, env
  | MLletin (mlid,a1,a2) ->
      (* get the renamed id in the initial env without passing it to a1 *)
      let id, _ = py_push_vars [id_of_mlid mlid] env in
      let id = List.hd id in
      let py_a1, env = extract_definition env id None a1 in
      (* get renamed id in the env returned by a1, pass it to a2 *)
      let id, env = py_push_vars [id_of_mlid mlid] env in
      let py_a2, env = extract_stmt env a2 in
      let let_in_def = List.map (fun stmt -> PyStmtTop stmt) py_a1 in
      let_in_def @ py_a2, env
  | MLfix (i,ids,defs) ->
      let ids',env = py_push_vars (List.rev (Array.to_list ids)) env in
      extract_fix env i (Array.of_list (List.rev ids'), defs), env
  | MLexn s -> [PyStmtTop (PyRaise ("Exception", s))], env
  | MLdummy k -> [PyStmtFunDef (PyReturn (PyId "__"))], env
  | MLmagic a -> extract_stmt env a
  | MLaxiom -> [PyStmtTop (PyRaise ("Exception", axiom_not_realized_msg))], env
  | MLcase (_, t, pv) when is_custom_match pv ->
      if not (is_regular_match pv) then
        user_err Pp.(str "Cannot mix yet user-given match and general patterns.");
      (* named_lams does the converse of collect_lams: a,b,e -> MLlam(a, MLlam (b, e)) *)
      let mkfun (ids,_,e) =
        if not (List.is_empty ids) then named_lams (List.rev ids) e
        else dummy_lams (ast_lift 1 e) 1
      in
      let rec extract_br i env acc_br acc_stmt =
        begin
          if i == Array.length pv then acc_br, acc_stmt, env
          else
            let py_exp, stmt, env = extract_expr env (mkfun pv.(i)) in
            extract_br (i + 1) env (py_exp :: acc_br) (stmt @ acc_stmt)
        end
      in
      let py_exp, py_stmt, env = extract_br 0 env [] [] in
      let branches, stmts = List.rev py_exp, List.rev py_stmt in
      let head, stmt_head, env = extract_expr env t in
      let input = find_custom_match pv in
      stmts @ [PyStmtFunDef (PyMatchCustom (head, branches, input))], env
  | MLcase (typ, t, pv) ->
    begin
      try
        let expr, stmts, env = extract_record_proj true env typ t pv in
        stmts @ [PyStmtFunDef (PyReturn (expr))], env
      with Impossible ->
        let head, stmt, env = extract_expr env t in
        begin
          try
            let expr, stmts, env = extract_ifthenelse env head pv in
            stmt @ stmts @ [PyStmtFunDef (PyReturn (expr))], env
          with Not_found ->
            (* standard match *)
            let head, stmt, env = extract_expr env t in
            let branches = extract_pat env pv in
            stmt @ [PyStmtFunDef (PyMatchFun (head, branches))], env
        end
    end

and extract_expr env : ml_ast -> py_expr * py_stmt list * env = function
  | MLaxiom | MLexn _
  | MLletin _ | MLfix _ -> assert false
  | MLcase (_,_,pv) when is_custom_match pv -> assert false
  | MLrel n ->
      let id = get_db_name n env in
      let id = if Id.equal id dummy_name then "__" else Id.to_string id in
    PyId id, [], env
  | MLapp (f,args) ->
      let expr, f_stmt, env = expr_to_stmt env f in
      let args_expr, args_stmt, env = map_expr_to_stmt env args in
      let stmt = f_stmt @ args_stmt in
    PyApp (expr, args_expr), stmt, env
  | MLlam _ as a ->
      let ids,a' = collect_lams a in
      let ids,env' = py_push_vars (List.map id_of_mlid ids) env in
      let body, stmt, _ = extract_expr env' a' in
      nest_lams ids body, stmt, env
  | MLglob r -> PyId (str_global Term r), [], env
  | MLdummy k -> PyId "__", [], env
  | MLmagic a -> extract_expr env a
  | MLcons (_,r,a) ->
      let kn, r = type_if_record_cons r in
      let args, stmts, env = map_expr_to_stmt env a in
    PyCons (PyId (str_global ~snake_case:false kn r), args), stmts, env
  | MLtuple l ->
      let args, stmts, env = map_expr_to_stmt env l in
    PyTuple args, stmts, env
  | MLcase (typ, t, pv) ->
      begin
        try extract_record_proj true env typ t pv
        with Impossible ->
          let head, stmt, env = extract_expr env t in
          begin
            try extract_ifthenelse env head pv
            with Not_found -> assert false
          end
      end
  | MLuint i -> assert false
      (* TODO str "MLuint", mt (), env *)
  | MLfloat f -> assert false
      (* TODO str "MLfloat", mt (), env *)
  | MLparray(t,def) -> assert false
      (* TODO str "MLparray", mt (), env *)

and is_record_proj typ t pv =
  try ignore (extract_record_proj false (empty_env ()) typ t pv); true
  with Impossible -> false

(* pretty print * env * MLcase type * expression to match * branches * args *)
and extract_record_proj extract env typ t pv : py_expr * py_stmt list * env =
  (* Can a match be printed as a mere record projection ? *)
  let fields = record_fields_of_type typ in
  (* if no fields then Impossible *)
  if List.is_empty fields then raise Impossible;
  (* if more than one branch then Impossible *)
  if not (Int.equal (Array.length pv) 1) then raise Impossible;
  (* if nested patterns then Impossible *)
  if has_deep_pattern pv then raise Impossible;
  (* destructuring the only branch: pattern ids, branch pattern, branch body *)
  let (ids,pat,body) = pv.(0) in
  let n = List.length ids in
  (* true if there is no [Rel i] in a for 1<=i<=n *)
  let no_patvar a = not (List.exists (ast_occurs_itvl 1 n) a) in
  (* De Bruijn index of the Rel in body * args of MLapp,
     only if body is MLrel or MLapp(MLrel...) with no [Rel i] in MLapp args - else Impossible.
     This means that the body must be an attribute of the record (represented by Rel i)
     that can also be an application of this attribute if this attribute is a function,
     but no stored variable can show in the application *)
  let rel_i, a = match body with
    | MLrel i | MLmagic(MLrel i) when i <= n -> i, []
    | MLapp(MLrel i, a) | MLmagic(MLapp(MLrel i, a))
      | MLapp(MLmagic(MLrel i), a) when i <= n && no_patvar a -> i, a
    | _ -> raise Impossible
  in
  let rec lookup_rel i idx = function
    | Prel j :: l -> if Int.equal i j then idx else lookup_rel i (idx + 1) l
    | Pwild :: l -> lookup_rel i (idx + 1) l
    | _ -> raise Impossible
  in
  let r, idx = match pat with
    | Pusual r -> r, n - rel_i
    | Pcons (r, l) -> r, lookup_rel rel_i 0 l
    | _ -> raise Impossible
  in
  if not extract then PyId "", [], env
  else
    (* first id of the field access chain (typically the class instance id) *)
    let py_left, left_stmt, env = extract_expr env t in
    (* field getter *)
    let getter = find_getter_map(str_field r fields idx) in
    (* MLapp args (could be empty) *)
    let args, args_stmts, env = map_expr_to_stmt env a in
    PyApp (PyFieldAccess (py_left, [getter]), args),
      left_stmt @ args_stmts, env

and nest_fundefs fun_args body =
  match fun_args with
    | [] -> body
    | (name, arg) :: [] -> [PyStmtTop (PyFunDef (name, [], [arg], body))]
    | (name, arg) :: args' -> [PyStmtTop (PyFunDef (name, [], [arg], nest_fundefs args' body))]

and nest_lams args body =
  match args with
  | [] -> body
  | arg :: args' -> PyLam ([arg], nest_lams args' body)

and extract_cons_pat r ppl =
  let kn, r = type_if_record_cons r in
  (* records and inductive type constructors are extracted the same *)
  PyCons (PyId (str_global ~snake_case:false kn r), ppl)

and extract_gen_pat ids env = function
(* constructor: pp_gen each argument, then pp_cons the whole *)
| Pcons (r, l) -> extract_cons_pat r (List.map (extract_gen_pat ids env) l)
(* Shortcut to Pcons with De Bruijn indices: Pcons (r,[Prel n;...;Prel 1]) *)
| Pusual r -> extract_cons_pat r ids
(* print tuple from generated pattern list *)
| Ptuple l -> PyTuple (List.map (extract_gen_pat ids env) l)
(* print wildcard pattern *)
| Pwild -> PyId "_"
(* search for lambda term with De Bruijn index n in env and print it *)
| Prel n -> PyId (Id.to_string (get_db_name n env))

and extract_ifthenelse env expr pv = match pv with
  | [|([],tru,the);([],fal,els)|] when
      (is_bool_patt tru "True") && (is_bool_patt fal "False")
      ->
      let py_then, stmt_then, env = extract_expr env the in
      let py_else, stmt_else, env = extract_expr env els in
      PyIfExpr (expr, py_then, py_else), stmt_then @ stmt_else, env
  | _ -> raise Not_found

and extract_pat env pv =
  let rec extract_one_pat i acc env pv =
    if i == (Array.length pv) then acc
    else
      let ids, pat, t = pv.(i) in
      let ids,env = py_push_vars (List.rev_map id_of_mlid ids) env in
      let ids = List.rev_map (fun id -> PyId id) ids in
      let stmt_body, env = extract_stmt env t in
      let acc =
        (extract_gen_pat ids env pat, stmt_body) :: acc
      in
      extract_one_pat (i+1) acc env pv
  in
  List.rev (extract_one_pat 0 [] env pv)

and extract_fix env i (ids,bl) : py_stmt list =
  let funs =
    Array.map2
      (fun id b -> fst (extract_definition env id None b))
      ids bl |>
    Array.to_list |>
    List.flatten
  in
  (List.map (fun f -> PyStmtTop f) funs)
  @ [PyStmtFunDef (PyReturn (PyId ids.(i)))]

let extract_Dfix rv c t : py_stmt_top list =
  let rec extract_rec env i : py_stmt_top list =
    if i = Array.length rv then []
    else
      let fix_name = if is_inline_custom rv.(i) then "" else str_global Term rv.(i) in
      (* void if inline_custom or (not_custom but unused) -> do not extract it *)
      let void = is_inline_custom rv.(i) ||
        (not (is_custom rv.(i)) &&
          match c.(i) with MLexn "UNUSED" -> true | _ -> false)
      in
      begin
        if void then extract_rec env (i+1)
        else
          let def =
            if is_custom rv.(i) then [PyCustomFunDef (fix_name, (find_custom rv.(i)))]
            else [fst (extract_definition_top env fix_name (Some t.(i)) c.(i))]
          in
          extract_rec env (i+1) @ def
      end
  in
  List.rev (extract_rec (empty_env ()) 0)

let has_equiv = function
  | NoEquiv -> false
  | Equiv _ | RenEquiv _ -> true

let extract_equiv name = function
| NoEquiv, _ -> assert false
| Equiv kn, i -> PyAssign (name, PyId (str_global Type (GlobRef.IndRef (MutInd.make1 kn,i))))
| RenEquiv ren, _  -> PyAssign (name, PyFieldAccess (PyId ren, [name]))

let extract_one_ind ip_equiv pl (names : string * string array) argtypes_array =
  if (has_equiv (fst ip_equiv)) then (extract_equiv (fst names) ip_equiv, [])
  else
    let pl_id = py_rename_tvars keywords pl in
    let pl = List.map (fun p -> PyTypeId (Id.to_string p)) pl_id in
    let extract_one_cons i argtypes =
      reset_gensym ();
      let fieldnames = List.map (fun _ -> py_private_field (gensym ())) argtypes in
      let fieldnames, env = py_push_vars fieldnames (empty_env ()) in
      let typenames = List.map (fun t -> Some (extract_type pl_id t)) argtypes in
      let fields = List.combine fieldnames typenames in
      let parent = PyTypeGeneric (fst names, pl) in
      PyClassDef ((snd names).(i), pl, [parent], fields, [])
    in
    PyClassDef ((fst names), pl, [], [], []),
      Array.to_list (Array.mapi extract_one_cons argtypes_array)

let comment_logical_ind packet =
    Id.to_string packet.ip_typename ^ " : logical inductive, with constructors : " ^
    String.concat " " (Array.map_to_list Id.to_string packet.ip_consnames)

let singleton_comment_str cons_name =
  "singleton inductive, whose constructor was " ^ Id.to_string cons_name

let extract_singleton kn packet =
  let name = str_global ~snake_case:false Type (GlobRef.IndRef (kn,0)) in
  let pl_id = py_rename_tvars keywords packet.ip_vars in
  let pl = List.map (fun p -> PyTypeId (Id.to_string p)) pl_id in
  let typ = extract_type pl_id (List.hd packet.ip_types.(0)) in
  PyTypeAlias (PyTypeGeneric (name, pl), typ)
  :: PyComment (singleton_comment_str packet.ip_consnames.(0))
  :: []

let extract_record kn fields ip_equiv packet =
  let rec_type = GlobRef.IndRef (kn,0) in
  let rec_cons = GlobRef.ConstructRef ((kn,0),1) in
  add_record_map rec_cons rec_type;

  let type_name = str_global ~snake_case:false Type rec_type in
  (* get fieldnames from global env without saving them in global ids *)
  let fieldnames = str_fields rec_type fields in
  (* save fieldnames to local env *)
  let fieldnames_local, env = py_push_vars (List.map py_private_field fieldnames) (empty_env ()) in
  (* add and save getters to local env to avoid conflicts *)
  let getternames, env = py_push_vars (List.map py_getter_from_private fieldnames_local) env in
  (* add getters to getters map *)
  List.iter2 (fun key value -> add_getter_map key value) fieldnames getternames;

  (* rename survivingTypes *)
  let pl_id = py_rename_tvars keywords packet.ip_vars in
  let pl = List.map (fun p -> PyTypeId (Id.to_string p)) pl_id in
  let fieldtypes = List.map (fun t -> Some (extract_type pl_id t)) packet.ip_types.(0) in
  let fields = List.combine fieldnames_local fieldtypes in
  PyClassDef (type_name, pl, [], fields, getternames)

(** Python does not care about mutually dependent types, they are just separate classes. *)
let extract_ind kn ind =
  (* (ind_name * cons_names) array *)
  let names =
    let map_names i p =
      (* exclude logical inductive types *)
      if p.ip_logical then "", [||]
      else
        let ind_name = str_global ~snake_case:false Type (GlobRef.IndRef (kn,i)) in
        (* mapping on constructors *)
        let cons_names =
          Array.mapi
            (fun j _ ->
              str_global ~snake_case:false ~prfx:ind_name Cons (GlobRef.ConstructRef ((kn,i),j+1)))
            p.ip_types
        in
        ind_name, cons_names
    in
    (* mapping on inductive types *)
    Array.mapi map_names ind.ind_packets
  in
  let rec extract_ind_rec acc_types acc_cons i =
    if i = Array.length names then acc_types, acc_cons
    else
      (* inductive type name * position of type in the list of mutually-recursive inductive types *)
      let ip = (kn,i) in
      let ip_equiv = ind.ind_equiv, i in
      let p = ind.ind_packets.(i) in
      (* if custom, do not redefine it *)
      if is_custom (GlobRef.IndRef ip) then extract_ind_rec acc_types acc_cons (i+1)
      else
        (* if logical, specify it and ignore it *)
        if p.ip_logical then
          extract_ind_rec (PyComment (comment_logical_ind p) :: acc_types) acc_cons (i+1)
        else
          let ind, cons = extract_one_ind ip_equiv p.ip_vars names.(i) p.ip_types in
          (* accumulators built in reverse *)
          extract_ind_rec (ind :: acc_types) (cons @ acc_cons) (i+1)
  in
  let ind, cons = extract_ind_rec [] [] 0 in
  (List.rev ind) @ (List.rev cons)

let extract_mind kn i : py_stmt_top list =
  match i.ind_kind with
    | Singleton -> extract_singleton kn i.ind_packets.(0)
    (* TODO *)
    | Coinductive -> []
    | Record fields -> [extract_record kn fields (i.ind_equiv,0) i.ind_packets.(0)]
    | Standard -> extract_ind kn i

(*s Extracting a declaration. *)
let extract_decl = function
  (* inline custom, no need for declaration *)
  | Dtype (r,_,_) when is_inline_custom r -> []
  | Dterm (r,_,_) when is_inline_custom r -> []
  | Dfix (rv,defs,typs) -> extract_Dfix rv defs typs
  | Dind (kn,i) -> extract_mind kn i
  | Dterm (r,a,t) ->
      let name = str_global Term r in
      if is_custom r then [PyCustomFunDef (name, find_custom r)]
      else [fst (extract_definition_top (empty_env ()) name (Some t) a)]
  | Dtype (r,l,t) ->
      let name = str_global ~snake_case:false Type r in
      let l = py_rename_tvars keywords l in
      begin
        try
        let ids,s = find_type_custom r in
        let params = List.map (fun id -> PyTypeId id) ids in
        [PyTypeAliasCustom (PyTypeGeneric (name, params), s)]
        with Not_found ->
          if t == Taxiom then [PyTypeDef (name, name)]
          else
            let params = List.map (fun id -> PyTypeId (Id.to_string id)) l in
            [PyTypeAlias (PyTypeGeneric (name, params), extract_type l t)]
      end

let rec pp_decl ml_decl =
  let py_decl = extract_decl ml_decl in
  pp_fold_stmt_top_list py_decl

(*s Pretty-printing of a py_stmt_top term. *)
and pp_py_stmt_top has_next stmt =
  let pp_stmt, pp_sep =
    match stmt with
    | PyAssign (id, expr) -> pp_py_vardef id (pp_py_expr expr), fnl ()
    | PyTypeAlias (t1, t2) -> pp_py_type_alias t1 t2, fnl ()
    | PyTypeAliasCustom (t1, s) -> pp_py_type_alias_custom t1 s, fnl ()
    | PyTypeDef (id, s) -> pp_py_typedef id s, fnl ()
    | PyRaise (exn, msg) -> pp_py_raise exn msg, fnl ()
    | PyFunDef (id, params, args, body) ->
        pp_py_fundef id params args (pp_fold_stmt_list body), cut2 ()
    | PyCustomFunDef (id, s) -> pp_py_fundef id [] [] (str s), cut2 ()
    | PyClassDef (id, type_params, parents, fields, getternames) ->
        pp_py_dataclass id type_params parents fields getternames, cut2 ()
    | PyMatch (head, cases) ->
        let branches =
          List.map (fun (pat, stmts) -> pp_py_expr pat, pp_fold_stmt_top_list stmts) cases
        in
        pp_py_match (pp_py_expr head) branches, fnl ()
    | PyComment s -> pp_comment_one_line s, fnl ()
  in
  if Pp.ismt pp_stmt then mt ()
  else (pp_stmt ++ if has_next then pp_sep else mt ())

and pp_py_stmt_fundef has_next stmt =
  let pp_stmt, pp_sep =
    match stmt with
    | PyReturn e -> pp_py_ret (pp_py_expr e), fnl ()
    | PyMatchFun (head, cases) ->
      let branches =
        List.map (fun (pat, stmts) -> pp_py_expr pat, pp_fold_stmt_list stmts) cases
      in
      pp_py_match (pp_py_expr head) branches, fnl ()
    | PyMatchCustom (head, cases, user_input) ->
        pp_py_match_custom (pp_py_expr head) (List.map pp_py_expr cases) user_input, fnl ()
  in
  if Pp.ismt pp_stmt then mt ()
  else (pp_stmt ++ if has_next then pp_sep else mt ())

and pp_py_stmt has_next = function
  | PyStmtTop s -> pp_py_stmt_top has_next s
  | PyStmtFunDef s -> pp_py_stmt_fundef has_next s

and pp_py_expr = function
  | PyId s -> str s
  | PyFieldAccess (obj, ids) -> pp_py_field_access (pp_py_expr obj) ids
  | PyApp (f, args) -> pp_py_app (pp_py_expr f) (List.map pp_py_expr args)
  | PyCons (head, args) -> pp_py_instance (pp_py_expr head) (List.map pp_py_expr args)
  | PyLam (ids, body) ->
      let nl = match body with PyLam _ -> true | _ -> false in
      pp_py_lambda nl ids (pp_py_expr body)
  | PyTuple args -> pp_py_tuple (List.map pp_py_expr args) false
  | PyIfExpr (cond, then_, else_) ->
      pp_py_ifexpr (pp_py_expr cond) (pp_py_expr then_) (pp_py_expr else_)

and pp_fold_stmt_top_list stmts =
  let rec pp_fold_rec acc = function
  | [] -> acc
  | [stmt] -> acc ++ pp_py_stmt_top false stmt
  | stmt :: stmts -> pp_fold_rec (acc ++ pp_py_stmt_top true stmt) stmts
  in
  pp_fold_rec (mt ()) stmts

and pp_fold_stmt_list stmts =
  let rec pp_fold_rec acc = function
  | [] -> acc
  | [stmt] -> acc ++ pp_py_stmt false stmt
  | stmt :: stmts -> pp_fold_rec (acc ++ pp_py_stmt true stmt) stmts
  in
  pp_fold_rec (mt ()) stmts

let pp_spec = function
  | Sval (r,_) when is_inline_custom r -> mt ()
  | Stype (r,_,_) when is_inline_custom r -> mt ()
  | Sind (kn,i) -> pp_decl (Dind (kn, i))
  | Sval (r,t) ->
      let def = pp_py_type (extract_type [] t) in
      let name = pp_global Term r in
      hov 2 (str "val " ++ name ++ str " :" ++ spc () ++ def)
  | Stype (r,vl,ot) ->
      let name = pp_global Type r in
      let l = py_rename_tvars keywords vl in
      let ids, def =
        try
          let ids, s = find_type_custom r in
          pp_py_type_params (List.map (fun id -> PyTypeId id) ids), str " =" ++ spc () ++ str s
        with Not_found ->
          let ids = pp_py_type_params (List.map (fun id -> PyTypeId (Id.to_string id)) l) in
          match ot with
            | None -> ids, mt ()
            | Some Taxiom -> ids, str " (* AXIOM TO BE REALIZED *)"
            | Some t -> ids, str " =" ++ spc () ++ pp_py_type (extract_type l t)
      in
      hov 2 (str "type " ++ ids ++ name ++ def)

let rec pp_specif = function
  | (_,Spec (Sval _ as s)) -> pp_spec s
  | (l,Spec s) ->
      (match Common.get_duplicate (top_visible_mp ()) l with
      | None -> pp_spec s
      | Some ren ->
          hov 1 (str ("module "^ren^" : sig") ++ fnl () ++ pp_spec s) ++
          fnl () ++ str "end" ++ fnl () ++
          str ("include module type of struct include "^ren^" end"))
  | (l,Smodule mt) ->
      let def = pp_module_type [] mt in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1 (str "module " ++ name ++ str " :" ++ fnl () ++ def) ++
      (match Common.get_duplicate (top_visible_mp ()) l with
        | None -> Pp.mt ()
        | Some ren ->
          fnl () ++
          hov 1 (str ("module "^ren^" :") ++ spc () ++
                str "module type of struct include " ++ name ++ str " end"))
  | (l,Smodtype mt) ->
      let def = pp_module_type [] mt in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1 (str "module type " ++ name ++ str " =" ++ fnl () ++ def) ++
      (match Common.get_duplicate (top_visible_mp ()) l with
        | None -> Pp.mt ()
        | Some ren -> fnl () ++ str ("module type "^ren^" = ") ++ name)

and pp_module_type params = function
  | MTident kn ->
      pp_modname kn
  | MTfunsig (mbid, mt, mt') ->
      let typ = pp_module_type [] mt in
      let name = pp_modname (MPbound mbid) in
      let def = pp_module_type (MPbound mbid :: params) mt' in
      str "functor (" ++ name ++ str ":" ++ typ ++ str ") ->" ++ fnl () ++ def
  | MTsig (mp, sign) ->
      push_visible mp params;
      let try_pp_specif l x =
        let px = pp_specif x in
        if Pp.ismt px then l else px::l
      in
      (* We cannot use fold_right here due to side effects in pp_specif *)
      let l = List.fold_left try_pp_specif [] sign in
      let l = List.rev l in
      pop_visible ();
      str "sig" ++ fnl () ++
      (if List.is_empty l then mt ()
        else
          v 1 (str " " ++ prlist_with_sep cut2 identity l) ++ fnl ())
      ++ str "end"
  | MTwith(mt,ML_With_type(idl,vl,typ)) ->
      let ids = pp_py_type_params (List.map (fun id -> PyTypeId (Id.to_string (id))) (py_rename_tvars keywords vl)) in
      let mp_mt = msid_of_mt mt in
      let l,idl' = List.sep_last idl in
      let mp_w =
        List.fold_left (fun mp l -> MPdot(mp,Label.of_id l)) mp_mt idl'
      in
      let r = GlobRef.ConstRef (Constant.make2 mp_w (Label.of_id l)) in
      push_visible mp_mt [];
      let pp_w = str " with type " ++ ids ++ pp_global Type r in
      pop_visible();
      pp_module_type [] mt ++ pp_w ++ str " = " ++ pp_py_type (extract_type vl typ)
  | MTwith(mt,ML_With_module(idl,mp)) ->
      let mp_mt = msid_of_mt mt in
      let mp_w =
        List.fold_left (fun mp id -> MPdot(mp,Label.of_id id)) mp_mt idl
      in
      push_visible mp_mt [];
      let pp_w = str " with module " ++ pp_modname mp_w in
      pop_visible ();
      pp_module_type [] mt ++ pp_w ++ str " = " ++ pp_modname mp

let is_short = function MEident _ | MEapply _ -> true | _ -> false

let rec pp_structure_elem = function
  | (l,SEdecl d) ->
      (match Common.get_duplicate (top_visible_mp ()) l with
      | None -> pp_decl d
      | Some ren ->
          v 1 (str ("module "^ren^" = struct") ++ fnl () ++ pp_decl d) ++
          fnl () ++ str "end" ++ fnl () ++ str ("include "^ren))
  | (l,SEmodule m) ->
      let typ =
        (* virtual printing of the type, in order to have a correct mli later*)
        if Common.get_phase () == Pre then
          str ": " ++ pp_module_type [] m.ml_mod_type
        else mt ()
      in
      let def = pp_module_expr [] m.ml_mod_expr in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1
        (str "module " ++ name ++ typ ++ str " =" ++
          (if is_short m.ml_mod_expr then spc () else fnl ()) ++ def) ++
      (match Common.get_duplicate (top_visible_mp ()) l with
        | Some ren -> fnl () ++ str ("module "^ren^" = ") ++ name
        | None -> mt ())
  | (l,SEmodtype m) ->
      let def = pp_module_type [] m in
      let name = pp_modname (MPdot (top_visible_mp (), l)) in
      hov 1 (str "module type " ++ name ++ str " =" ++ fnl () ++ def) ++
      (match Common.get_duplicate (top_visible_mp ()) l with
        | None -> mt ()
        | Some ren -> fnl () ++ str ("module type "^ren^" = ") ++ name)

and pp_module_expr params = function
  | MEident mp -> pp_modname mp
  | MEapply (me, me') ->
      pp_module_expr [] me ++ str "(" ++ pp_module_expr [] me' ++ str ")"
  | MEfunctor (mbid, mt, me) ->
      let name = pp_modname (MPbound mbid) in
      let typ = pp_module_type [] mt in
      let def = pp_module_expr (MPbound mbid :: params) me in
      str "functor (" ++ name ++ str ":" ++ typ ++ str ") ->" ++ fnl () ++ def
  | MEstruct (mp, sel) ->
      push_visible mp params;
      let try_pp_structure_elem l x =
        let px = pp_structure_elem x in
        if Pp.ismt px then l else px::l
      in
      (* We cannot use fold_right here due to side effects in pp_structure_elem *)
      let l = List.fold_left try_pp_structure_elem [] sel in
      let l = List.rev l in
      pop_visible ();
      str "struct" ++ fnl () ++
      (if List.is_empty l then mt ()
        else
          v 1 (str " " ++ prlist_with_sep cut2 identity l) ++ fnl ())
      ++ str "end"

let rec prlist_sep_nonempty sep f = function
  | [] -> mt ()
  | [h] -> f h
  | h::t ->
      let e = f h in
      let r = prlist_sep_nonempty sep f t in
      if Pp.ismt e then r
      else e ++ sep () ++ r

let do_struct f s =
  let ppl (mp,sel) =
    push_visible mp [];
    let p = prlist_sep_nonempty cut2 f sel in
    (* for monolithic extraction, we try to simulate the unavailability
        of [MPfile] in names by artificially nesting these [MPfile] *)
    (if modular () then pop_visible ()); p
  in
  let p = prlist_sep_nonempty cut2 ppl s in
  (if not (modular ()) then repeat (List.length s) pop_visible ());
  v 0 p ++ fnl ()

let pp_struct s = do_struct pp_structure_elem s

let pp_signature s = do_struct pp_specif s

let python_descr = {
  keywords = keywords;
  file_suffix = ".py";
  file_naming = file_of_modfile;
  preamble = preamble;
  pp_struct = pp_struct;
  sig_suffix = None;
  sig_preamble = sig_preamble;
  pp_sig = pp_signature;
  pp_decl = pp_decl;
}
