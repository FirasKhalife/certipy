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

let starting_sym = Char.code 'a' - 1
let r = ref (starting_sym)
let reset_gensym () = r := starting_sym
let gensym () = incr r; String.make 1 (Char.chr !r)

let fst3 (a,_,_) = a

let tl_empty = function
  | [] -> []
  | _ :: l -> l

let cut2_infix_if_both a1 a2 = a1 ++ (if Pp.ismt a1 || Pp.ismt a2 then mt () else cut2 ()) ++ a2

let axiom_not_realized_msg = "AXIOM TO BE REALIZED"

let push_args_fun_names args env =
  let fun_names, env =
    py_push_vars ~save_db:false (List.map (fun a -> Id.of_string (py_fun_of_id (fst a))) args) env in
  fun_names, env

let push_var_fun_name id env =
  let fun_name, env = py_push_vars ~save_db:false [Id.of_string (py_fun_of_id id)] env in
  let fun_name = Id.print (List.hd fun_name) in
  fun_name, env

module Record_Map = GlobRef.Map

(** a map of record constructors refs to their type ref,
   in order to only use the record type only in the extracted code *)
let record_map = ref Record_Map.empty

let add_rec_map key value = record_map := Record_Map.add key value !record_map

(** returns Type and the type ref of the constructor if the constructor ref is found ,
    else Cons and the constructor itself *)
let type_if_record_cons key =
  try Type, Record_Map.find key !record_map
  with Not_found -> Cons, key

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

let pp_type vl t =
  let rec pp_type_rec = function
    | Tmeta _ | Tvar' _ | Taxiom -> assert false
    | Tvar i -> (try pp_py_tvar (List.nth vl (pred i))
                 with Failure _ -> (str "A" ++ int i))
    | Tglob (r,[]) -> pp_global ~snake_case:false Type r
    | Tglob (r,l) ->
        pp_global ~snake_case:false Type r ++ pp_py_generics identity (List.map pp_type_rec l)
    | Tarr (t1, t2) ->
        pp_py_type_callable [pp_type_rec t1] (pp_type_rec t2)
    | Tdummy _ -> str "__"
    | Tunknown -> str "__"
  in
  hov 0 (pp_type_rec t)

let get_type_params t =
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
  get_params_rec [] t

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

(** in_fun specifies if the term is already inside a function *)
let rec pp_definition in_fun env params fun_names args def def_term : Pp.t =
  let is_fun = is_pystatement_rec env def_term in
  (* no args, pystatement -> extracted as function then stored in a variable *)
  if List.is_empty args && is_fun then
    let var_name = List.hd fun_names in
    let fun_name, env = push_var_fun_name var_name env in
    pp_py_fundef_with_var params (Id.print var_name) fun_name def
  else
    let fun_names = List.map Id.print fun_names in
    (* no args, no pystatement -> extracted as a variable *)
    if List.is_empty args && not is_fun then
      let var_name = List.hd fun_names in
      pp_py_vardef var_name [] def
    else
      (* args -> extracted as a function *)
      pp_py_fundef params fun_names args def

and pp_letin env params fun_names args def body def_term =
  pp_definition true env params fun_names args def def_term ++ fnl () ++ body

and is_pystatement env = function
| MLfix _ | MLexn _ | MLaxiom | MLletin _ -> true
| MLlam _ as a -> is_pystatement env (snd (collect_lams a))
| MLmagic a -> is_pystatement env a
| MLcase (typ, t, pv) -> not (is_record_proj typ t pv) && not (is_ifthenelse pv)
| _ -> false

and is_pystatement_rec env = function
  | MLfix _ | MLexn _ | MLaxiom -> true
  | MLletin (_, a1, a2) -> is_pystatement_rec env a1 || is_pystatement_rec env a2
  | MLlam _ as a -> is_pystatement_rec env (snd (collect_lams a))
  | MLapp (f, args) -> is_pystatement_rec env f || List.exists (is_pystatement_rec env) args
  | MLcons (_,_, args) -> List.exists (is_pystatement_rec env) args
  | MLmagic a -> is_pystatement_rec env a
  | MLcase (typ, t, pv) ->
      not (is_record_proj typ t pv) && not (is_ifthenelse pv)
  | _ -> false

and extract_statement ret env expr =
  if not (is_pystatement env expr) then pp_expr ret env expr
  else
    match expr with
    | MLlam (id, a) ->
      let arg, env' = py_push_vars [id_of_mlid id] env in
      let pp_expr, stmt, env' = pp_expr ret env' a in
      let arg = List.hd arg in
      let fun_name, env = push_args_fun_names [(arg, None)] env in
      let fun_name = Id.print (List.hd fun_name) in
      fun_name, pp_py_fundef [] [fun_name] [(Id.print arg, None)] (cut2_infix_if_both stmt pp_expr), env
    | _ ->
      let pp_expr, stmt, env = pp_expr ret env expr in
      let name_stmt, env' = py_push_vars ~save_db:false [Id.of_string "x"] env in
      let name_stmt = Id.print (List.hd name_stmt) in
      pp_py_funapp name_stmt [],
      pp_py_fundef [] [name_stmt] [] (cut2_infix_if_both stmt pp_expr),
      env'

and map_extract_statement ret env = function
  | [] -> [], mt (), env
  | x :: xs ->
      let x, stmt_x, env = extract_statement ret env x in
      let xs, stmt_xs, env = map_extract_statement ret env xs in
      (x :: xs), (cut2_infix_if_both stmt_x stmt_xs), env

and pp_expr ret env = function
  | MLrel n ->
      let id = get_db_name n env in
      let id = if Id.equal id dummy_name then Id.of_string "__" else id in
      pp_ret ret (Id.print id), mt (), env
  | MLapp (f,args') ->
      let needs_par = match f with MLlam _ -> true | _ -> false in
      let ret = ret && (match f with MLfix _ -> false | _ -> true) in
      let def, stmt_f, env = extract_statement false env f in
      let args, stmt_args, env = map_extract_statement false env args' in
      let stmt = cut2_infix_if_both stmt_f stmt_args in
      pp_ret ret (pp_py_funapp (pp_par needs_par def) args), stmt, env
  | MLlam _ as a ->
      let fl,a' = collect_lams a in
      let fl,env' = py_push_vars (List.map id_of_mlid fl) env in
      let body, stmt, env' = pp_expr true env' a' in
      if not (Pp.ismt stmt) || is_pystatement_rec env a'
        then
          let fun_names , env' =
            push_args_fun_names (List.map (fun a -> (a, None)) fl) env'
          in
          pp_py_nest_single_helper_fun [] (List.map Id.print fun_names)
            (List.rev (List.map (fun id -> (Id.print id, None)) fl))
            (cut2_infix_if_both stmt body),
          mt (), env
        else
          pp_ret ret (
            pp_py_nest_single_lambdas
              (List.rev (List.map Id.print fl)) (fst3 (pp_expr false env' a'))),
          mt (), env
  | MLletin (id,a1,a2) ->
      let id,env' = py_push_vars [id_of_mlid id] env in
      let fl,a1 = collect_lams a1 in
      let fl,env = py_push_vars (List.map id_of_mlid fl) env
      in
      let args = List.map (fun id -> (id, None)) fl in
      let fun_names, env = push_args_fun_names (tl_empty args) env in
      let args = List.map (fun (a, t) -> (Id.print a, t)) args
      in
      let pp_a1, stmt1, env = pp_expr false env a1 in
      let pp_a2, stmt2, env' = pp_expr ret env' a2 in
      pp_letin env [] (List.hd id :: fun_names) args
        (cut2_infix_if_both stmt1 pp_a1) (cut2_infix_if_both stmt2 pp_a2) a1, mt (), env'
  | MLglob r -> pp_ret ret (pp_global Term r), mt (), env
  | MLfix (i,ids,defs) ->
      let ids',env' = py_push_vars (List.rev (Array.to_list ids)) env in
      pp_fix env' i (Array.of_list (List.rev ids'), defs), mt (), env'
  | MLexn s -> pp_py_raise "Exception" s, mt (), env
  | MLdummy k -> pp_ret ret (str "__"), mt (), env
  | MLmagic a -> pp_expr ret env a
  | MLaxiom -> pp_py_raise "Exception" axiom_not_realized_msg, mt (), env
  | MLcons (_,r,a) ->
      let kn, r = type_if_record_cons r in
      if List.is_empty a then
      pp_ret ret (pp_py_instance (pp_global ~snake_case:false kn r) []), mt (), env
      else
        let fds = get_record_fields r in
        if not (List.is_empty fds) then
          let args, stmts, env = map_extract_statement false env a in
          pp_ret ret (pp_cons_pat r args), stmts, env
        else
          let args, stmts, env = map_extract_statement false env a in
          (* if String.is_empty (str_global kn r) (* hack Extract Inductive prod *)
          then pp_ret ret (pp_tuple identity args)
          else *) pp_ret ret (pp_py_instance (pp_global ~snake_case:false kn r) args), stmts, env
  | MLtuple l ->
      let args, stmts, env = map_extract_statement false env l in
      pp_ret ret (pp_py_tuple args), stmts, env
  | MLcase (_, t, pv) when is_custom_match pv ->
      if not (is_regular_match pv) then
        user_err Pp.(str "Cannot mix yet user-given match and general patterns.");
      (* named_lams does the converse of collect_lams: a,b,e -> MLlam(a, MLlam (b, e)) *)
      let mkfun (ids,_,e) =
        if not (List.is_empty ids) then named_lams (List.rev ids) e
        else dummy_lams (ast_lift 1 e) 1
      in
      (* pp_expr the MLlams with a new line *)
      let pp_branch tr = pp_expr false env (mkfun tr) in
      let head, stmt_head, env = pp_expr false env t in
      let res =
        (* head lambda function, comes raw from user input *)
        pp_par true (str (find_custom_match pv)) ++ fnl () ++
        (* each branch followed by a comma and a new line *)
        pp_par true (
          (prvect (fun br -> fst3 (pp_branch br) ++ str "," ++ fnl()) pv) ++
          (* the matched expression *)
          head)
      in
      v 4 res, stmt_head, env
  | MLcase (typ, t, pv) ->
    (* First, can this match be printed as a mere record projection ? *)
    (try
      let rec_proj, stmt, env = pp_record_proj true env typ t pv in
      pp_ret ret rec_proj, stmt, env
      with Impossible ->
        let head, stmt, env = pp_expr false env t in
        (* Can this match be printed as [if ... then ... else] ? *)
        (try
          let if_cond, stmt, env = pp_ifthenelse env head pv in
          pp_ret ret if_cond, stmt, env
          with Not_found ->
            (* Otherwise, standard match *)
            let pat = pp_pat env pv in
            pp_py_patmatch head pat, stmt, env))
  | MLuint i -> (* TODO *) str "MLuint", mt (), env
  | MLfloat f -> (* TODO *) str "MLfloat", mt (), env
  | MLparray(t,def) -> (* TODO *) str "MLparray", mt (), env

and is_record_proj typ t pv =
  try ignore (pp_record_proj false (empty_env ()) typ t pv); true
  with Impossible -> false

(* pretty print * env * MLcase type * expression to match * branches * args *)
and pp_record_proj pp env typ t pv =
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
  if not pp then mt (), mt (), env
  else
    let pp_head, stmt_head, env = pp_expr false env t in
    (* pp_expr of MLapp args (could be empty) *)
    let pp_args, stmt_args, env = map_extract_statement false env a in
    (* field getter *)
    let pp_head = pp_py_get_var pp_head (str_field r fields idx)
    in
    pp_py_funapp pp_head pp_args, stmt_head ++ stmt_args, env

(*
  pretty print constructor pattern
  (Pcons of GlobeRef.t * ml_pattern list)
*)
and pp_cons_pat r ppl : Pp.t =
  (* if String.is_empty (str_global Cons r) then
    pp_boxed_tuple identity ppl (* Hack Extract Inductive prod *)
  else *)
    let kn, r = type_if_record_cons r in
    (* records and inductive type constructors are extracted the same *)
    pp_py_instance (pp_global ~snake_case:false kn r) ppl

(* consecutive patterns with a same body are considered as different patterns,
   each wil have its own body (duplicated body)
*)
and pp_gen_pat ids env = function
  (* constructor: pp_gen each argument, then pp_cons the whole *)
  | Pcons (r, l) -> pp_cons_pat r (List.map (pp_gen_pat ids env) l)
  (* Shortcut to Pcons with De Bruijn indices: Pcons (r,[Prel n;...;Prel 1]) *)
  | Pusual r -> pp_cons_pat r (List.map Id.print ids)
  (* print tuple from generated pattern list *)
  | Ptuple l -> pp_boxed_tuple (pp_gen_pat ids env) l
  (* print wildcard pattern *)
  | Pwild -> str "_"
  (* search for lambda term with De Bruijn index n in env and print it *)
  | Prel n -> Id.print (get_db_name n env)

and pp_ifthenelse env expr pv = match pv with
  | [|([],tru,the);([],fal,els)|] when
      (is_bool_patt tru "True") && (is_bool_patt fal "False")
      ->
      let pp_then, stmt_the, env = pp_expr false env the in
      let pp_else, stmt_els, env = pp_expr false env els in
      pp_py_ifthenelse expr pp_then pp_else, stmt_the ++ stmt_els, env
  | _ -> raise Not_found

(* env * (ids, pattern, body) => pp pattern * pp_expr body *)
and pp_pat env pv =
  let rec pp_one_pat i acc env pv =
    if i == (Array.length pv) then acc
    else
      let ids, pat, t = pv.(i) in
      let ids',env = py_push_vars (List.rev_map id_of_mlid ids) env in
      let body, stmt_body, env = pp_expr true env t in
      let acc =
        (pp_gen_pat (List.rev ids') env pat, cut2_infix_if_both stmt_body body) :: acc
      in
      pp_one_pat (i+1) acc env pv
  in
  Array.rev_of_list (pp_one_pat 0 [] env pv)

and pp_function env name type_opt a =
  let bl,a' = collect_lams a in
  let tl =
    match type_opt with
    | None -> []
    | Some t -> fst (collect_tarrs t)
  in
  let tv, tv_len = Array.of_list tl, List.length tl in
  let bl,env = py_push_vars (List.map id_of_mlid bl) env in
  let map_args i id = id, if i < tv_len then (Some (pp_type [] tv.(i))) else None in
  let args = List.rev (List.mapi map_args bl)
  in
  let fun_names, env = push_args_fun_names (tl_empty args) env in
  let args = List.map (fun (a, t) -> (Id.print a, t)) args
  in
  let params =
    List.flatten (List.map get_type_params tl) |>
    List.fold_left (fun xs x -> if List.mem x xs then xs else x :: xs) [] |>
    List.map (fun i -> str "A" ++ int i)
  in
  let ret = (is_pystatement_rec env a') || not (List.is_empty bl) in
  let body, stmt, env' = pp_expr ret env a' in
  let body = if Pp.ismt stmt then body else (stmt ++ cut2 () ++ body) in
  (params, name :: fun_names, args, a', body)

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix env i (ids,bl) =
  prvecti
    (fun i (id, (params, fun_names, args, body, pp_body)) ->
      let id, env = py_push_vars [id] env in
      let var_name = Id.print (List.hd id) in
      (if i = 0 then mt () else cut2 ()) ++
      if not (List.is_empty args)
      then
        let fun_names = List.map Id.print fun_names in
        pp_py_fundef params (var_name :: fun_names) args pp_body
      else
        let fun_name, env = push_var_fun_name (List.hd id) env in
        pp_py_fundef_with_var params var_name fun_name pp_body)
    (Array.map2 (fun id b -> (id, pp_function env id None b)) ids bl) ++
  pp_ret true (Id.print ids.(i))

(*s Pretty-printing of [Dfix] *)

let pp_Dfix (rv,c,t) =
  (* name of every fix to print *)
  let names = Array.map
    (fun r -> if is_inline_custom r then "" else str_global Term r) rv
  in
  let rec pp_one_Dfix init env i =
    if i = Array.length rv then mt ()
    else
      (* void if inline_custom or (not_custom but unused) -> do not extract it *)
      let void = is_inline_custom rv.(0) ||
        (not (is_custom rv.(0)) &&
          match c.(i) with MLexn "UNUSED" -> true | _ -> false)
      in
      if void then pp_one_Dfix init env (i+1)
      else
        (if init then mt () else cut2 ()) ++
        (if is_custom rv.(0) then
          v 4 (str "def " ++ str names.(i) ++ str "():" ++ fnl () ++
            str (find_custom rv.(0)))
        else
          let params, fun_names, args, body, pp_body =
            pp_function (empty_env ()) (Id.of_string names.(i)) (Some t.(i)) c.(i) in
          if not (List.is_empty args) then
            let fun_names = List.map Id.print fun_names in
            pp_py_fundef params (str names.(i) :: fun_names) args pp_body
          else
            let fun_name, env = push_var_fun_name (Id.of_string names.(i)) env in
            pp_py_fundef_with_var params (str names.(i)) fun_name pp_body) ++
        pp_one_Dfix false env (i+1)
  in
  pp_one_Dfix true (empty_env ()) 0

let has_equiv = function
  | NoEquiv -> false
  | Equiv _ | RenEquiv _ -> true

let pp_equiv param_list name = function
| NoEquiv, _ -> mt ()
| Equiv kn, i -> pp_py_alias name None (str_global Type (GlobRef.IndRef (MutInd.make1 kn,i)))
| RenEquiv ren, _  -> pp_py_alias name (Some ren) name

(*s Pretty-printing of inductive types declaration. *)
(* pp_one_ind ip_equiv survivingTypes inductiveTypeName constructorNames constructorsArgsMLTypes*)
let pp_one_ind ip_equiv pl name cnames ctyps =
  let pl = rename_tvars keywords pl in
  let pp_constructor i typs =
    reset_gensym ();
    let fieldnames = List.map (fun _ -> py_private_field (gensym ())) typs in
    let fieldnames, env = py_push_vars fieldnames (empty_env ()) in
    let fieldnames = List.map Id.print fieldnames in
    let typenames = List.map (pp_type pl) typs in
    pp_py_dataclass cnames.(i) pl [(name, pl)] (List.combine fieldnames typenames) []
  in
  if (has_equiv (fst ip_equiv)) then (pp_equiv pl name ip_equiv, mt())
  else
    pp_py_empty_dataclass name pl [],
      prvecti_with_sep cut2 pp_constructor ctyps

let pp_logical_ind packet =
  pp_comment_one_line (
    Id.print packet.ip_typename ++ str " : logical inductive, with constructors : " ++
    prvect_with_sep spc Id.print packet.ip_consnames)

(* pretty prints an inductive type that has only one constructor,
   and only one argument to this constructor, seen as an alias to the argument type.

   e.g. Inductive singleton (A: Set) := single (n: A)
   OCaml --> type 'a singleton = 'a
   Python --> type singleton[A] = A
*)
let pp_singleton kn packet =
  let name = pp_global ~snake_case:false Type (GlobRef.IndRef (kn,0)) in
  let pl = rename_tvars keywords packet.ip_vars in
  let typ = pp_type pl (List.hd packet.ip_types.(0)) in
  pp_py_typedef name (pp_py_id_generics pl) typ ++ fnl () ++
  pp_comment_one_line (
    str "singleton inductive, whose constructor was " ++
    Id.print packet.ip_consnames.(0))

let pp_record kn fields ip_equiv packet =
  let rec_type = GlobRef.IndRef (kn,0) in
  let rec_cons = GlobRef.ConstructRef ((kn,0),1) in
  add_rec_map rec_cons rec_type;

  let type_name = str_global ~snake_case:false Type rec_type in
  (* get fieldnames from global env without saving them in global ids *)
  let fieldnames = str_fields rec_type fields in
  (* save fieldnames to local env *)
  let fieldnames, env =
    py_push_vars (List.map py_private_field fieldnames) (empty_env ()) in
  (* add and save getters to local env to avoid conflicts *)
  let getternames, env = py_push_vars (List.map py_getter_from_private fieldnames) env in
  (* rename survivingTypes if needed *)
  let pl = rename_tvars keywords packet.ip_vars in
  let fieldnames = List.map Id.print fieldnames in
  let fieldtypes = List.map (pp_type pl) packet.ip_types.(0) in
  pp_py_dataclass type_name pl []
    (List.combine fieldnames fieldtypes) (List.map Id.print getternames)

(* pp_ind parentTypeName mlInductiveTypeList *)
let pp_ind kn ind =
  (* python does not care about mutually dependent types. they are just separate types. *)
  let (names: string array) =
    (* mapping on inductive types, excluding logical ones *)
    Array.mapi
      (fun i p -> if p.ip_logical then "" else
        str_global ~snake_case:false Type (GlobRef.IndRef (kn,i)))
      ind.ind_packets
  in
  let (cnames: string array array) =
    (* mapping on inductive types *)
    Array.mapi
      (fun i p -> if p.ip_logical then [||] else
        (* mapping on ml_type list array, constructors array with their types in a list *)
        Array.mapi
          (fun j _ -> str_global ~snake_case:false ~prfx:names.(i) Cons (GlobRef.ConstructRef ((kn,i),j+1)))
          p.ip_types)
      ind.ind_packets
  in
  let rec pp_ind_rec acc_types acc_cons i =
    if i = Array.length ind.ind_packets then acc_types, acc_cons
    else
      let cut_if_not_mt p = if Pp.ismt p then mt () else cut2 () in
      (* inductive type name * position of type in the list of mutually-recursive inductive types *)
      let ip = (kn,i) in
      let ip_equiv = ind.ind_equiv, i in
      let p = ind.ind_packets.(i) in
      (* if custom, do not redefine it *)
      if is_custom (GlobRef.IndRef ip) then pp_ind_rec acc_types acc_cons (i+1)
      else
        (* if logical, specify it and ignore it *)
        if p.ip_logical then
          pp_ind_rec (acc_types ++ cut_if_not_mt acc_types ++ pp_logical_ind p) acc_cons (i+1)
        else
          let typ, cons = pp_one_ind ip_equiv p.ip_vars names.(i) cnames.(i) p.ip_types in
          pp_ind_rec
            (acc_types ++ cut_if_not_mt acc_types ++ typ)
            (acc_cons ++ cut_if_not_mt acc_cons ++ cons) (i+1)
  in
  let types, cons = pp_ind_rec (mt ()) (mt ()) 0 in
  types ++ cut2 () ++ cons

let pp_mind kn i =
  match i.ind_kind with
    | Singleton -> pp_singleton kn i.ind_packets.(0)
    (* TODO *)
    | Coinductive -> mt ()
    | Record fields -> pp_record kn fields (i.ind_equiv,0) i.ind_packets.(0)
    | Standard -> pp_ind kn i

(*s Pretty-printing of a declaration. *)
let pp_decl decl =
  match decl with
  (* inline custom, no need for declaration *)
  | Dtype (r,_,_) when is_inline_custom r -> mt ()
  | Dterm (r,_,_) when is_inline_custom r -> mt ()
  (* inductive declaration *)
  | Dind (kn,i) -> pp_mind kn i
  (* type declaration *)
  | Dtype (r, l, t) ->
      let name = pp_global ~snake_case:false Type r in
      let l = rename_tvars keywords l in
      (try
        let ids,s = find_type_custom r in
        pp_py_typedef name (pp_py_generics str ids) (str s)
      with Not_found ->
        if t == Taxiom then pp_py_typevar name ++ str (" # " ^ axiom_not_realized_msg)
        else pp_py_typedef name (pp_py_id_generics l) (pp_type l t))
  | Dterm (r, a, t) ->
      let name = str_global Term r in
      if is_custom r then pp_py_fundef [] [str name] [] (str (find_custom r))
      else
        let params, fun_names, args, body, pp_body =
          pp_function (empty_env ()) (Id.of_string name) (Some t) a in
        pp_definition false (empty_env ()) params fun_names args pp_body body
  | Dfix (rv,defs,typs) ->
      pp_Dfix (rv,defs,typs)

let pp_spec = function
  | Sval (r,_) when is_inline_custom r -> mt ()
  | Stype (r,_,_) when is_inline_custom r -> mt ()
  | Sind (kn,i) -> pp_mind kn i
  | Sval (r,t) ->
      let def = pp_type [] t in
      let name = pp_global Term r in
      hov 2 (str "val " ++ name ++ str " :" ++ spc () ++ def)
  | Stype (r,vl,ot) ->
      let name = pp_global Type r in
      let l = rename_tvars keywords vl in
      let ids, def =
        try
          let ids, s = find_type_custom r in
          pp_py_generics str ids, str " =" ++ spc () ++ str s
        with Not_found ->
          let ids = pp_py_id_generics l in
          match ot with
            | None -> ids, mt ()
            | Some Taxiom -> ids, str " (* AXIOM TO BE REALIZED *)"
            | Some t -> ids, str " =" ++ spc () ++ pp_type l t
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
      let ids = pp_py_id_generics (rename_tvars keywords vl) in
      let mp_mt = msid_of_mt mt in
      let l,idl' = List.sep_last idl in
      let mp_w =
        List.fold_left (fun mp l -> MPdot(mp,Label.of_id l)) mp_mt idl'
      in
      let r = GlobRef.ConstRef (Constant.make2 mp_w (Label.of_id l)) in
      push_visible mp_mt [];
      let pp_w = str " with type " ++ ids ++ pp_global Type r in
      pop_visible();
      pp_module_type [] mt ++ pp_w ++ str " = " ++ pp_type vl typ
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
