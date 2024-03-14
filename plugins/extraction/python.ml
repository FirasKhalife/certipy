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

let axiom_not_realized_msg = "AXIOM TO BE REALIZED"

(* from the Python Language Reference 3.12.1, "Identifiers and Keywords" *)
let keywords =
  List.fold_right (fun s -> Id.Set.add (Id.of_string s))
  [ "False"; "None"; "True"; "and"; "as"; "assert"; "async"; "await";
    "break"; "class"; "continue"; "def"; "del"; "elif"; "else"; "except";
    "finally"; "for"; "from"; "global"; "if"; "import"; "in"; "is";
    "lambda"; "nonlocal"; "not"; "or"; "pass"; "raise"; "return";
    "try"; "while"; "with"; "yield" ]
  Id.Set.empty

(* Beware of the side-effects of [pp_global] and [pp_modname].
   They are used to update table of content for modules. Many [let]
   below should not be altered since they force evaluation order.
*)

(* //////////////////////////////////////////////////// *)
(* the key is the canonical name, simply kn *)
let str_global_with_key k key r =
  if is_inline_custom r then find_custom r else Common.pp_global_with_key k key r

let str_global k r = str_global_with_key k (repr_of_r r) r

let pp_global_cap k r = str (String.capitalize_ascii (str_global k r))

(* for constuctor names: pp_global Cons (GlobRef.ConstructRef ((kn,typeIndx),consIdx)) *)
let pp_global k r = str (str_global k r)

(* //////////////////////////////////////////////////// *)

let str_global_name k r = Common.pp_global_with_key k (repr_of_r r) r

let pp_global_name_cap k r = str (String.capitalize_ascii (str_global_name k r))

(* for type names: pp_global_name Type (GlobRef.IndRef (kn,typeIndx)) *)

(* for inductive type names: pp_global_name Type (GlobRef.IndRef (kn,typeIndx)) *)
let pp_global_name k r = str (str_global_name k r)

(* for record fields *)
(* let pp_global_with_key k key r = str (str_global_with_key k key r) *)

let pp_modname mp = str (Common.pp_module mp)

(* grammar from OCaml 4.06 manual, "Prefix and infix symbols" *)

let infix_symbols =
  ['=' ; '<' ; '>' ; '@' ; '^' ; ';' ; '&' ; '+' ; '-' ; '*' ; '/' ; '$' ; '%' ]
let operator_chars =
  [ '!' ; '$' ; '%' ; '&' ; '*' ; '+' ; '-' ; '.' ; '/' ; ':' ; '<' ; '=' ; '>' ; '?' ; '@' ; '^' ; '|' ; '~' ]

(* infix ops in OCaml, but disallowed by preceding grammar *)

let builtin_infixes =
  [ "::" ; "," ]

(* returns true if all chars in list are ops *)
let substring_all_opchars s start stop =
  let rec check_char i =
    if i >= stop then true
    else
      List.mem s.[i] operator_chars && check_char (i+1)
  in
  check_char start

(* returns true if reference represents an infix operator *)
let is_infix r =
  is_inline_custom r &&
  (let s = find_custom r in
   let len = String.length s in
   len >= 3 &&
   (* parenthesized *)
   (s.[0] == '(' && s.[len-1] == ')' &&
      let inparens = String.trim (String.sub s 1 (len - 2)) in
      let inparens_len = String.length inparens in
      (* either, begins with infix symbol, any remainder is all operator chars *)
      (List.mem inparens.[0] infix_symbols && substring_all_opchars inparens 1 inparens_len) ||
      (* or, starts with #, at least one more char, all are operator chars *)
      (inparens.[0] == '#' && inparens_len >= 2 && substring_all_opchars inparens 1 inparens_len) ||
      (* or, is an OCaml built-in infix *)
      (List.mem inparens builtin_infixes)))

(* gets infix operator of reference, likely assuming it is in parenthesis*)
let get_infix r =
  let s = find_custom r in
  String.sub s 1 (String.length s - 2)

(* gets inductive reference, possibly extracting it from inductive constructor *)
let get_ind = let open GlobRef in function
  | IndRef _ as r -> r
  | ConstructRef (ind,_) -> IndRef ind
  | _ -> assert false

(* extracts user facing name from inductive reference? *)
let kn_of_ind = let open GlobRef in function
  | IndRef (kn,_) -> MutInd.user kn
  | _ -> assert false

let str_one_field r i = function
  | Some r' -> str_global_with_key Term (kn_of_ind (get_ind r)) r'
  | None -> str_global Type (get_ind r) ^ "__" ^ (string_of_int i)

let str_field r fields i = str_one_field r i (List.nth fields i)

let str_fields r fields = List.map_i (str_one_field r) 0 fields

let pp_type params vl t =
  let rec pp_rec = function
    | Tmeta _ | Tvar' _ | Taxiom -> assert false
    | Tvar i -> (try pp_py_tvar (List.nth vl (pred i))
                 with Failure _ -> (str "A" ++ int i))
    | Tglob (r,[a1;a2]) when is_infix r ->
        pp_rec a1 ++ str (get_infix r) ++ pp_rec a2
    | Tglob (r,[]) -> pp_global_cap Type r
    | Tglob (gr,l)
        when not (keep_singleton ()) && Coqlib.check_ref sig_type_name gr ->
        pp_py_generics identity (List.map pp_rec l)
    | Tglob (r,l) ->
      pp_global_cap Type r ++ pp_py_generics identity (List.map pp_rec l)
    | Tarr (t1, t2) ->
        pp_py_type_callable params [pp_rec t1] (pp_rec t2)
    | Tdummy _ -> str "__"
    | Tunknown -> str "__"
  in
  hov 0 (pp_rec t)

let get_type_params vl t =
  let rec get_params_rec vl acc = function
    | Tmeta _ | Tvar' _ | Taxiom -> acc
    | Tarr _ | Tdummy _ | Tunknown -> acc
    | Tvar i ->
        if i > List.length vl && not (List.exists (Int.equal i) acc)
        then i :: acc else acc
    | Tglob (_,l) ->
        if not (List.is_empty l) then List.fold_left (get_params_rec vl) acc l
        else acc
  in
  get_params_rec vl [] t

(*s Pretty-printing of expressions. [par] indicates whether
    parentheses are needed or not. [env] is the list of names for the
    de Bruijn variables. [args] is the list of collected arguments
    (already pretty-printed). *)

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
  | [|([],p1,_);([],p2,_)|] -> is_bool_patt p1 "true" && is_bool_patt p2 "false"
  | _ -> false

let expr_needs_par = function
  | MLlam _  -> true
  | MLcase (_,_,[|_|]) -> false
  | MLcase (_,_,pv) -> not (is_ifthenelse pv)
  | _        -> false

(** in_fun specifies if the term is already inside a function
    if true while it should treaten as a function,
      extracted as a helper function and stored inside a variable
    if false, presence of args automatically treats the term as a function *)
let rec pp_definition in_fun env params name args def def_term =
  (* (match def_term with MLfix _ -> str "fix" | _ -> str "notfix") ++ *)
  let is_fun = is_pyfunction env def_term in
  (* inside a function, a pyfunction with no args is extracted as one then stored in a variable *)
  if in_fun && is_fun && List.is_empty args then
    pp_py_fundef_with_var params name def
  else
  (* inside a function, a no-pyfunction with args is a var with lambdas *)
  if in_fun && not is_fun && not (List.is_empty args) then
    pp_py_vardef name (List.map fst args) def
  else
  (* outside, any term with args is extracted as a function *)
  if not in_fun && not (List.is_empty args) then
    pp_py_fundef params name args def
  else
  (* other cases: if a pyfunction or args then extract as a function, else as a variable *)
  if is_fun || not (List.is_empty args) then
    pp_py_fundef params name args def
  else
    pp_py_vardef name (List.map fst args) def

and pp_letin env params name args def body def_term =
  pp_definition true env params name args def def_term ++ cut2 () ++ body

and is_pyfunction env = function
| MLfix _ | MLexn _ | MLaxiom -> true
| MLletin (_, a1, a2) -> is_pyfunction env a1 || is_pyfunction env a2
| MLlam _ as a -> is_pyfunction env (snd (collect_lams a))
| MLapp (f, args) -> is_pyfunction env f || List.exists (is_pyfunction env) args
| MLcons (_,_, args) -> List.exists (is_pyfunction env) args
| MLmagic a -> is_pyfunction env a
| MLcase (typ, t, pv) ->
    not (is_record_proj typ t pv) && not (is_ifthenelse pv)
| _ -> false

and pp_expr ret par env args t =
  (* adds st at head of args and returns them sep by spc *)
  let apply st = pp_apply st par args
  (* same as apply but adds par to added arg if args is not empty or if par *)
  and apply2 st = pp_apply2 st par args in
  (* fnl () ++ str "((args: " ++ pp_boxed_tuple identity args ++ str " || " ++ *)
  (* fnl () ++ str "((env: " ++ pp_boxed_tuple identity (List.map Id.print (fst env)) ++ str "))" ++ fnl () ++ *)
  match t with
    | MLrel n ->
        (* str "Rel " ++ int n ++ str ": " ++ Id.print (get_db_name n env) ++ fnl () ++ *)
        (* search for lambda term with De Bruijn index n in env and print it *)
        let id = get_db_name n env in
        let id = if Id.equal id dummy_name then Id.of_string "__" else id in
        apply (pp_ret ret (Id.print id))
    | MLapp (f,args') ->
        (* HANDLE CASE OF PATTERN MATCHING INSIDE ARGS *)
        let needs_par = match f with MLlam _ -> true | _ -> false in
        (* str "(App: " ++ pp_expr needs_par par env args f ++ str " - APPLIED WITH ARGS: - " ++
         prlist (pp_expr false true env []) args' ++ str")" ++ fnl () ++ *)
        let ret = ret && (match f with MLfix _ -> false | _ -> true) in
        pp_ret ret (
          pp_py_funapp (pp_expr false needs_par env args f)
            (List.map (pp_expr false true env []) args'))
    | MLlam _ as a ->
        let fl,a' = collect_lams a in
        let fl = List.map id_of_mlid fl in
        let fl,env' = push_vars fl env in
        let st =
          if is_pyfunction env a'
            then
              pp_py_nest_single_helper_fun []
                (List.rev (List.map (fun id -> (Id.print id, None)) fl))
                (pp_expr true false env' [] a')
            else
              pp_ret ret (
                pp_py_nest_single_lambdas
                  (List.rev (List.map Id.print fl))
                  (pp_expr false false env' [] a'))
        in
        (* str "MLlam: " ++ prlist identity (List.rev (List.map Id.print fl)) ++ fnl () ++ *)
        (* (pp_expr ret false env' [] a') ++ fnl () ++ *)
        apply st
    | MLletin (id,a1,a2) ->
        (* push_vars adds renames id if already in env (incremental addition, foo becomes foo0...) and adds it to it,
            id_of_mlid returns dummy_name if id is Dummy and just the id otherwise.
            i is the list of ids in the env *)
        let i,env = push_vars [id_of_mlid id] env in
        let fl,a1' = collect_lams a1 in
        let fl = List.map id_of_mlid fl in
        let fl,env = push_vars fl env in
        let args = List.map (fun id -> (Id.print id, None)) fl in
        let pp_id = Id.print (List.hd i)
        (* pp_expr of the first part, no par *)
        and pp_a1' = pp_expr false false env [] a1'
        (* pp_expr of the second part, arguable par *)
        and pp_a2 = pp_expr ret (not par && expr_needs_par a2) env [] a2 in
        (* str "(MLletin: " ++ pp_id ++ str " = " ++ pp_a1'
          ++ str "in" ++ pp_a2  ++ str ")" ++ fnl () ++ *)
        hv 0 (apply2 (pp_letin env [] pp_id args pp_a1' pp_a2 a1'))
    | MLglob r ->
      (* str "Global: " ++  *)
      apply (pp_ret ret (pp_global Term r))
    | MLfix (i,ids,defs) ->
        (* adds renamed function args to env *)
        let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
        (* pp_fix with functions names and their bodies (definitions) *)
        (* str "(MLfix: " ++ prlist identity (List.map Id.print (Array.to_list ids)) ++ str ")" ++ fnl () ++ *)
        pp_fix env' i (Array.of_list (List.rev ids'),defs) args
    | MLexn s -> pp_py_raise "Exception" s
    | MLdummy k -> pp_ret ret (str "__")
    | MLmagic a -> pp_expr ret par env args a
    | MLaxiom -> pp_py_raise "Exception" axiom_not_realized_msg
    | MLcons (_,r,a) as c ->
        (* a is already the args of c *)
        assert (List.is_empty args);
        (* str "Cons: " ++ *)
        begin match a with
          | _ when is_native_char c -> pp_ret ret (pp_native_char c)
          | _ when is_native_string c -> pp_ret ret (pp_native_string c)
          | [a1;a2] when is_infix r ->
            let pp = pp_expr false true env [] in
            pp_ret ret (pp_par par (pp a1 ++ str (get_infix r) ++ pp a2))
          (* ///////////// TODO //////////// *)
          | _ when is_coinductive r ->
            let ne = not (List.is_empty a) in
            let tuple = space_if ne ++ pp_tuple (pp_expr ret true env []) a in
            pp_par par (str "lazy " ++ pp_par ne (pp_global Cons r ++ tuple))
          (* ////////////////////////////// *)
          | _ ->
            if List.is_empty a then
            (* str "[] (expr: " ++ pp_global Cons r ++ str ")" ++ fnl () ++ *)
            pp_ret ret (pp_py_instance (pp_global Cons r) [])
            else
              (* str "_ (expr: " ++ pp_global Cons r ++ str ")" ++ fnl() ++ *)
              let fds = get_record_fields r in
              if not (List.is_empty fds) then
                pp_ret ret (pp_cons_pat r (List.map (pp_expr false true env []) a))
              else
                let args = List.map (pp_expr false true env []) a in
                if String.is_empty (str_global Cons r) (* hack Extract Inductive prod *)
                then pp_ret ret (pp_tuple identity args)
                else pp_ret ret (pp_py_instance (pp_global Cons r) args)
        end
    | MLtuple l ->
        assert (List.is_empty args);
        (* pretty print expressions in list l and box them as a tuple *)
        pp_ret ret (pp_boxed_tuple (pp_expr false true env []) l)
    | MLcase (_, t, pv) when is_custom_match pv ->
        if not (is_regular_match pv) then
          user_err Pp.(str "Cannot mix yet user-given match and general patterns.");
        (* named_lams does the converse of collect_lams: a,b,e -> MLlam(a, MLlam (b, e));
           gets ids of the branch:
           if not empty then MLlams them, else MLlams with dummy types (with ast_lift) *)
        let mkfun (ids,_,e) =
          if not (List.is_empty ids) then named_lams (List.rev ids) e
          else dummy_lams (ast_lift 1 e) 1
        in
        (* pp_expr the MLlams with a new line *)
        let pp_branch tr = pp_expr false true env [] (mkfun tr) ++ fnl () in
        let inner =
          (* print custom match *)
          str (find_custom_match pv) ++ fnl () ++
          (* pp_branch every branch *)
          prvect pp_branch pv ++ fnl () ++
          str "printing expression to match" ++ fnl () ++
          (* pp_expr the expression to match...??? *)
          pp_expr false true env [] t
        in
        apply2 (hov 2 inner)
    | MLcase (typ, t, pv) ->
        let head =
          (* no pars if regular and pp_expr expression to match *)
          if not (is_coinductive_type typ) then pp_expr false false env [] t
          (* Lazy.force then pars and pp_expr expression to match *)
          else (str "Lazy.force" ++ spc () ++ pp_expr false true env [] t)
        in
        (* str "head expr: " ++ head ++ fnl () ++ *)
        (* First, can this match be printed as a mere record projection ? *)
        (try pp_record_proj true par env typ t pv args
         with Impossible ->
            (* Can this match be printed as [if ... then ... else] ? *)
            (try apply2 (pp_ret true (pp_ifthenelse env head pv))
            with Not_found ->
              (* Otherwise, standard match *)
              apply2 (v 0 (pp_py_patmatch head (pp_pat env pv)))))
    | MLuint i -> (* TODO *) str "MLuint"
    | MLfloat f -> (* TODO *) str "MLfloat"
    | MLparray(t,def) -> (* TODO *) str "MLparray"

and is_record_proj typ t pv =
  try ignore (pp_record_proj false false (empty_env ()) typ t pv []); true
  with Impossible -> false

(* par * env * MLcase type * expression to match * branches * args *)
and pp_record_proj pp par env typ t pv args =
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
  let rel_i,a = match body with
    | MLrel i | MLmagic(MLrel i) when i <= n -> i,[]
    | MLapp(MLrel i, a) | MLmagic(MLapp(MLrel i, a))
      | MLapp(MLmagic(MLrel i), a) when i<=n && no_patvar a -> i,a
    | _ -> raise Impossible
  in
  let rec lookup_rel i idx = function
    | Prel j :: l -> if Int.equal i j then idx else lookup_rel i (idx+1) l
    | Pwild :: l -> lookup_rel i (idx+1) l
    | _ -> raise Impossible
  in
  let r,idx = match pat with
    | Pusual r -> r, n-rel_i
    | Pcons (r,l) -> r, lookup_rel rel_i 0 l
    | _ -> raise Impossible
  in
  if is_infix r then raise Impossible;
  if not pp then mt ()
  else
    let env' = snd (push_vars (List.rev_map id_of_mlid ids) env) in
    (* pp_expr of MLapp args (could be empty) *)
    let pp_args = (List.map (pp_expr false true env' []) a) @ args in
    (* field getter *)
    let pp_head =
      pp_py_get_var (pp_expr false true env [] t) (str_field r fields idx)
    in
    pp_py_funapp pp_head pp_args

(*
  pretty print constructor pattern
  (Pcons of GlobeRef.t * ml_pattern list)
*)
and pp_cons_pat r ppl =
  (* if infix, print as infix *)
  if is_infix r && Int.equal (List.length ppl) 2 then
    List.hd ppl ++ str (get_infix r) ++ List.hd (List.tl ppl)
  else
    (* ??? *)
    if String.is_empty (str_global Cons r) then
      pp_boxed_tuple identity ppl (* Hack Extract Inductive prod *)
    else
      (* records and inductive type constructors are extracted the same *)
      pp_py_instance (pp_global Cons r) ppl


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
      (is_bool_patt tru "true") && (is_bool_patt fal "false")
      ->
      let pp_then = pp_expr false (expr_needs_par the) env [] the in
      let pp_else = pp_expr false (expr_needs_par els) env [] els in
      pp_py_ifthenelse expr pp_then pp_else
  | _ -> raise Not_found

(* env * (ids, pattern, body) => pp pattern * pp_expr body *)
and pp_one_pat env (ids,p,t) =
  let ids',env' = push_vars (List.rev_map id_of_mlid ids) env in
  pp_gen_pat (List.rev ids') env' p,
  pp_expr true false env' [] t

and pp_pat env pv = Array.map (pp_one_pat env) pv

and pp_function env type_opt a =
  (* collect nested lambdas, returns all lambda identifiers * final body *)
  let bl,a' = collect_lams a in
  (* push_vars renames id if already in env (incremental addition, foo becomes foo0...) and adds it to it,
      id_of_mlid returns dummy_name ('_') if id is Dummy and just the id if otherwise.
      bl is the list of ids in the env *)
  let bl,env' = push_vars (List.map id_of_mlid bl) env in
  let tl =
    match type_opt with
    | None -> []
    | Some t -> fst (collect_tarrs t)
  in
  let params = List.flatten (List.map (get_type_params []) tl) in
  let params = List.fold_left (fun xs x -> if List.mem x xs then xs else x :: xs) [] params in
  let params = List.map (fun i -> str "A" ++ int i) params in
  let body =
    match a' with
    | MLcase (Tglob(r,_),MLrel 1,pv) when
        not (is_coinductive r) && List.is_empty (get_record_fields r) &&
        not (is_custom_match pv) ->
          pp_py_patmatch (Id.print (List.hd bl)) (pp_pat env' pv)
    | _ ->
        pp_expr true false env' [] a'
  in
  let tv, t_len = Array.of_list tl, List.length tl in
  let map_args i id = Id.print id, if i < t_len then (Some (pp_type false [] tv.(i))) else None in
  let args = List.rev (List.mapi map_args bl) in
  (params, args, a', body)

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix env i (ids,bl) args =
  prvect
    (fun (id, (params, args, body, pp_body)) ->
      (if not (List.is_empty args) then
        pp_py_fundef params id args pp_body
      else
        pp_py_fundef_with_var params id pp_body) ++
      cut2 ())
    (Array.map2 (fun id b -> (Id.print id, pp_function env None b)) ids bl) ++
  (* adds pretty print i to args, no par *)
  str "# applying the Id.print of the fix:" ++ fnl () ++
  pp_apply (pp_ret true (Id.print ids.(i))) false args

(*s Pretty-printing of [Dfix] *)

let pp_Dfix (rv,c,t) =
  (* name of every fix to print *)
  let names = Array.map
    (fun r -> if is_inline_custom r then mt () else pp_global_name Term r) rv
  in
  let pp_one_Dfix i fix =
    (* void if inline_custom or (not_custom and unused) -> do not extract it *)
    let void = is_inline_custom fix ||
      (not (is_custom fix) &&
        match c.(i) with MLexn "UNUSED" -> true | _ -> false)
    in
    if void then str "VOID"
    else
      (if i == 0 then mt () else cut2 ()) ++
      (* if is_custom fix then str " = " ++ str (find_custom fix) *)
      let params, args, body, pp_body =
        pp_function (empty_env ()) (Some t.(i)) c.(i) in
      if not (List.is_empty args) then
        pp_py_fundef params names.(i) args pp_body
      else
        pp_py_fundef_with_var params names.(i) pp_body
  in
  prvecti pp_one_Dfix rv

let has_equiv = function
  | NoEquiv -> false
  | Equiv _ | RenEquiv _ -> true

let pp_equiv param_list name = function
| NoEquiv, _ -> mt ()
| Equiv kn, i -> pp_py_alias name None (pp_global_cap Type (GlobRef.IndRef (MutInd.make1 kn,i)))
| RenEquiv ren, _  -> pp_py_alias name (Some ren) name

(*s Pretty-printing of inductive types declaration. *)
(* pp_one_ind prefix ip_equiv survivingTypes inductiveTypeName constructorNames constructorsArgsMLTypes*)
let pp_one_ind prefix ip_equiv pl name cnames ctyps =
  (* rename survivingTypes if needed*)
  let pl = rename_tvars keywords pl in
  (* pp_constructor: index * this constructor's args *)
  let pp_constructor i typs =
    pp_py_dataclass cnames.(i) pl [(name, pl)] [] (List.map (pp_type true pl) typs) false in
  if (has_equiv (fst ip_equiv)) then (pp_equiv pl name ip_equiv, mt())
  else
  (* if one or more constructors, loop on ctyps *)
  pp_py_dataclass name pl [] [] [] false,
    prvecti_with_sep cut2 pp_constructor ctyps

let pp_logical_ind packet =
  pp_comment (Id.print packet.ip_typename ++ str " : logical inductive") ++ fnl () ++
  pp_comment (str "with constructors : " ++
    prvect_with_sep spc Id.print packet.ip_consnames)

(* pretty prints an inductive type that has only one constructor,
   and only one argument to this constructor, seen as an alias to the argument type.

   e.g. Inductive singleton (A: Set) := single (n: A)
   OCaml --> type 'a singleton = 'a
   Python --> type singleton[A] = A
*)
let pp_singleton kn packet =
  let name = pp_global_name_cap Type (GlobRef.IndRef (kn,0)) in
  let pl = rename_tvars keywords packet.ip_vars in
  let typ = pp_type true pl (List.hd packet.ip_types.(0)) in
  pp_py_typedef name (pp_py_id_generics pl) typ ++ fnl () ++
  pp_comment (str "singleton inductive, whose constructor was " ++
              Id.print packet.ip_consnames.(0))

let pp_record kn fields ip_equiv packet =
  let ind = GlobRef.IndRef (kn,0) in
  let type_name = pp_global_name_cap Type ind in
  let cons_name = pp_global Cons (GlobRef.ConstructRef ((kn,0),1)) in
  let fieldnames = str_fields ind fields in
  let pl = rename_tvars keywords packet.ip_vars in
  let fieldtypes = List.map (pp_type true pl) packet.ip_types.(0) in
  pp_py_dataclass type_name pl [] [] [] false ++ cut2 () ++
  pp_py_dataclass cons_name pl [(type_name, pl)] fieldnames fieldtypes true

(* let pp_coind pl name =
  let pl = rename_tvars keywords pl in
  pp_py_id_generics pl ++ name ++ str " = " ++
  pp_py_id_generics pl ++ str "__" ++ name ++ str " Lazy.t" ++
  fnl () ++ str "and " *)

(* pp_ind isCoinductive parentTypeName mlInductiveTypeList *)
let pp_ind co kn ind =
  let prefix = if co then "COINDUCTIVE: " else "" in
  (* python does not care about mutually dependent types. they are just separate types. *)
  let names =
    (* mapping on inductive types, excluding logical ones *)
    Array.mapi (fun i p -> if p.ip_logical then mt () else
                  pp_global_name_cap Type (GlobRef.IndRef (kn,i)))
      ind.ind_packets
  in
  let cnames =
    (* mapping on inductive types *)
    Array.mapi
      (fun i p -> if p.ip_logical then [||] else
         (* mapping on ml_type list array, constructors array with their types in a list *)
         Array.mapi (fun j _ -> pp_global_cap Cons (GlobRef.ConstructRef ((kn,i),j+1)))
           p.ip_types)
      ind.ind_packets
  in
  let pp_ind_rec i _ =
    (* inductive type name * position of type in the list of mutually-recursive inductive types *)
    let ip = (kn,i) in
    let ip_equiv = ind.ind_equiv, i in
    let p = ind.ind_packets.(i) in
    (* if custom, ignore it *)
    if is_custom (GlobRef.IndRef ip) then (mt (), mt())
    (* if logical, specify it and ignore it *)
    else
      if p.ip_logical then (pp_logical_ind p, mt())
      else
        (* if co then pp_coind p.ip_vars names.(i) else mt () *)
        pp_one_ind prefix ip_equiv p.ip_vars names.(i) cnames.(i) p.ip_types
  in
  prvecti_with_sep cut2 (fun i x -> fst (pp_ind_rec i x)) ind.ind_packets ++
  cut2 () ++
  prvecti_with_sep cut2 (fun i x -> snd (pp_ind_rec i x)) ind.ind_packets

let pp_mind kn i =
  match i.ind_kind with
    (* inductive type with only one constructor with only one argument *)
    | Singleton -> pp_singleton kn i.ind_packets.(0)
    | Coinductive -> pp_ind true kn i
    | Record fields -> pp_record kn fields (i.ind_equiv,0) i.ind_packets.(0)
    | Standard -> pp_ind false kn i

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
      let name = pp_global_name_cap Type r in
      let l = rename_tvars keywords l in
      (try
        let ids,s = find_type_custom r in
        pp_py_typedef name (pp_py_generics str ids) (str s)
      with Not_found ->
        if t == Taxiom then pp_py_typevar name ++ str (" # " ^ axiom_not_realized_msg)
        else pp_py_typedef name (pp_py_id_generics l) (pp_type true l t))
  | Dterm (r, a, t) ->
      let name = pp_global_name Term r in
      (* if is_custom r then str (": " ^ find_custom r) *)
      let params, args, body, pp_body = pp_function (empty_env ()) (Some t) a in
      pp_definition false (empty_env ()) params name args pp_body body
  | Dfix (rv,defs,typs) ->
      pp_Dfix (rv,defs,typs)

let pp_spec = function
  | Sval (r,_) when is_inline_custom r -> mt ()
  | Stype (r,_,_) when is_inline_custom r -> mt ()
  | Sind (kn,i) -> pp_mind kn i
  | Sval (r,t) ->
      let def = pp_type true [] t in
      let name = pp_global_name Term r in
      hov 2 (str "val " ++ name ++ str " :" ++ spc () ++ def)
  | Stype (r,vl,ot) ->
      let name = pp_global_name Type r in
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
            | Some t -> ids, str " =" ++ spc () ++ pp_type true l t
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
      pp_module_type [] mt ++ pp_w ++ str " = " ++ pp_type true vl typ
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
