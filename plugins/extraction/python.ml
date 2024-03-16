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

module Record_Map = GlobRef.Map

(** a map of record constructors refs to their type ref,
   in order to only use the record type only in the extracted code *)
let record_map = ref Record_Map.empty

let add_rec_map key value = record_map := Record_Map.add key value !record_map

(** returns Type and the type ref of the constructor if the constructor ref is found ,
    else Cons and the constructor itself *)
let type_if_rec_cons key =
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
let str_global_with_key ?(cap = false) k key r =
  if is_custom r then find_custom r
  else
    let s = Common.str_py_global_with_key k key r in
    if cap then String.capitalize_ascii s else s

let str_global ?(cap = false) k r =
  str_global_with_key ~cap:cap k (repr_of_r r) r

let pp_global ?(cap = false) k r = str (str_global ~cap:cap k r)

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
  | Some r' -> str_global_with_key Term (kn_of_ind (get_ind r)) r'
  | None -> str_global Type (get_ind r) ^ "__" ^ (string_of_int i)

let str_field r fields i = str_one_field r i (List.nth fields i)

let str_fields r fields = List.map_i (str_one_field r) 0 fields

let pp_type vl t =
  let rec pp_type_rec = function
    | Tmeta _ | Tvar' _ | Taxiom -> assert false
    | Tvar i -> (try pp_py_tvar (List.nth vl (pred i))
                 with Failure _ -> (str "A" ++ int i))
    | Tglob (r,[]) -> pp_global ~cap:true Type r
    | Tglob (r,l) ->
        pp_global ~cap:true Type r ++ pp_py_generics identity (List.map pp_type_rec l)
    | Tarr (t1, t2) ->
        pp_py_type_callable [pp_type_rec t1] (pp_type_rec t2)
    | Tdummy _ -> str "__"
    | Tunknown -> str "__"
  in
  hov 0 (pp_type_rec t)

let get_type_params t =
  let rec get_params_rec acc = function
    | Tmeta _ | Tvar' _ | Taxiom -> acc
    | Tarr _ | Tdummy _ | Tunknown -> acc
    | Tvar i ->
        if not (List.exists (Int.equal i) acc) then i :: acc
        else acc
    | Tglob (_,l) ->
        if not (List.is_empty l) then List.fold_left (get_params_rec) acc l
        else acc
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

(** in_fun specifies if the term is already inside a function
    if true while it should treaten as a function,
      extracted as a helper function and stored inside a variable
    if false, presence of args automatically treats the term as a function *)
let rec pp_definition in_fun env params name args def def_term =
  (* (match def_term with MLfix _ -> str "fix" | _ -> str "notfix") ++ *)
  let is_fun = is_pystatement env def_term in
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

and is_pystatement env = function
  | MLfix _ | MLexn _ | MLaxiom -> true
  | MLletin (_, a1, a2) -> is_pystatement env a1 || is_pystatement env a2
  | MLlam _ as a -> is_pystatement env (snd (collect_lams a))
  | MLapp (f, args) -> is_pystatement env f || List.exists (is_pystatement env) args
  | MLcons (_,_, args) -> List.exists (is_pystatement env) args
  | MLmagic a -> is_pystatement env a
  | MLcase (typ, t, pv) ->
      not (is_record_proj typ t pv) && not (is_ifthenelse pv)
  | _ -> false

and pp_expr ret env = function
  (* fnl () ++ str "((env: " ++ pp_boxed_tuple identity (List.map Id.print (fst env)) ++ str "))" ++ fnl () ++ *)
  | MLrel n ->
      (* str "Rel " ++ int n ++ str ": " ++ Id.print (get_db_name n env) ++ fnl () ++ *)
      (* search for lambda term with De Bruijn index n in env and print it *)
      let id = get_db_name n env in
      let id = if Id.equal id dummy_name then Id.of_string "__" else id in
      pp_ret ret (Id.print id)
  | MLapp (f,args') ->
      (* HANDLE CASE OF PATTERN MATCHING INSIDE ARGS *)
      let needs_par = match f with MLlam _ -> true | _ -> false in
      (* str "(App: " ++ pp_expr needs_par par env f ++ str " - APPLIED WITH ARGS: - " ++
        prlist (pp_expr false env) args' ++ str")" ++ fnl () ++ *)
      let ret = ret && (match f with MLfix _ -> false | _ -> true) in
      pp_ret ret (
        pp_py_funapp (pp_par needs_par (pp_expr false env f))
          (List.map (pp_expr false env) args'))
  | MLlam _ as a ->
      let fl,a' = collect_lams a in
      let fl = List.map id_of_mlid fl in
      let fl,env' = push_vars fl env in
      let st =
        if is_pystatement env a'
          then
            pp_py_nest_single_helper_fun []
              (List.rev (List.map (fun id -> (Id.print id, None)) fl))
              (pp_expr true env' a')
          else
            pp_ret ret (
              pp_py_nest_single_lambdas
                (List.rev (List.map Id.print fl))
                (pp_expr false env' a'))
      (* str "MLlam: " ++ prlist identity (List.rev (List.map Id.print fl)) ++ fnl () ++ *)
      (* (pp_expr ret false env' a') ++ fnl () ++ *)
      in st
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
      and pp_a1' = pp_expr false env a1'
      (* pp_expr of the second part, arguable par *)
      and pp_a2 = pp_expr ret env a2 in
      (* str "(MLletin: " ++ pp_id ++ str " = " ++ pp_a1'
        ++ str "in" ++ pp_a2  ++ str ")" ++ fnl () ++ *)
      pp_letin env [] pp_id args pp_a1' pp_a2 a1'
  | MLglob r ->
    (* str "Global: " ++  *)
    pp_ret ret (pp_global Term r)
  | MLfix (i,ids,defs) ->
      (* adds renamed function args to env *)
      let ids',env' = push_vars (List.rev (Array.to_list ids)) env in
      (* pp_fix with functions names and their bodies (definitions) *)
      (* str "(MLfix: " ++ prlist identity (List.map Id.print (Array.to_list ids)) ++ str ")" ++ fnl () ++ *)
      pp_fix env' i (Array.of_list (List.rev ids'), defs)
  | MLexn s -> pp_py_raise "Exception" s
  | MLdummy k -> pp_ret ret (str "__")
  | MLmagic a -> pp_expr ret env a
  | MLaxiom -> pp_py_raise "Exception" axiom_not_realized_msg
  | MLcons (_,r,a) ->
      (* a is already the args of c *)
      (* assert (List.is_empty args); *)
      (* str "Cons: " ++ *)
      let kn, r = type_if_rec_cons r in
      if List.is_empty a then
      (* str "[] (expr: " ++ pp_global Cons r ++ str ")" ++ fnl () ++ *)
      pp_ret ret (pp_py_instance (pp_global ~cap:true kn r) [])
      else
        (* str "_ (expr: " ++ pp_global Cons r ++ str ")" ++ fnl() ++ *)
        let fds = get_record_fields r in
        if not (List.is_empty fds) then
          pp_ret ret (pp_cons_pat r (List.map (pp_expr false env) a))
        else
          let args = List.map (pp_expr false env) a in
          if String.is_empty (str_global kn r) (* hack Extract Inductive prod *)
          then pp_ret ret (pp_tuple identity args)
          else pp_ret ret (pp_py_instance (pp_global ~cap:true kn r) args)
  | MLtuple l ->
      (* assert (List.is_empty args); *)
      (* pretty print expressions in list l and box them as a tuple *)
      pp_ret ret (pp_boxed_tuple (pp_expr false env) l)
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
      let res =
        (* head lambda function, comes raw from user input *)
        pp_par true (str (find_custom_match pv)) ++ fnl () ++
        (* each branch followed by a comma and a new line *)
        pp_par true (prvect (fun br -> pp_branch br ++ str "," ++ fnl()) pv ++
        (* the matched expression *)
          pp_expr false env t)
      in
      v 4 res
  | MLcase (typ, t, pv) ->
      let head = pp_expr false env t in
      (* str "head expr: " ++ head ++ fnl () ++ *)
      (* First, can this match be printed as a mere record projection ? *)
      (try pp_ret true (pp_record_proj true env typ t pv)
        with Impossible ->
          (* Can this match be printed as [if ... then ... else] ? *)
          (try pp_ret true (pp_ifthenelse env head pv)
          with Not_found ->
            (* Otherwise, standard match *)
            pp_py_patmatch head (pp_pat env pv)))
  | MLuint i -> (* TODO *) str "MLuint"
  | MLfloat f -> (* TODO *) str "MLfloat"
  | MLparray(t,def) -> (* TODO *) str "MLparray"

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
  if not pp then mt ()
  else
    (* pp_expr of MLapp args (could be empty) *)
    let pp_args = List.map (pp_expr false env) a in
    (* field getter *)
    let pp_head =
      pp_py_get_var (pp_expr false env t) (str_field r fields idx)
    in
    pp_py_funapp pp_head pp_args

(*
  pretty print constructor pattern
  (Pcons of GlobeRef.t * ml_pattern list)
*)
and pp_cons_pat r ppl =
  (* ??? *)
  if String.is_empty (str_global Cons r) then
    pp_boxed_tuple identity ppl (* Hack Extract Inductive prod *)
  else
    let kn, r = type_if_rec_cons r in
    (* records and inductive type constructors are extracted the same *)
    pp_py_instance (pp_global kn r) ppl


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
      (* HANDLE PARENTHESIS *)
      let pp_then = pp_expr false env the in
      let pp_else = pp_expr false env els in
      pp_py_ifthenelse expr pp_then pp_else
  | _ -> raise Not_found

(* env * (ids, pattern, body) => pp pattern * pp_expr body *)
and pp_one_pat env (ids,p,t) =
  let ids',env' = push_vars (List.rev_map id_of_mlid ids) env in
  pp_gen_pat (List.rev ids') env' p,
  pp_expr true env' t

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
  let params = List.flatten (List.map get_type_params tl) in
  let params = List.fold_left (fun xs x -> if List.mem x xs then xs else x :: xs) [] params in
  let params = List.map (fun i -> str "A" ++ int i) params in
  let body = pp_expr true env' a'
  in
  let tv, tv_len = Array.of_list tl, List.length tl in
  let map_args i id = Id.print id, if i < tv_len then (Some (pp_type [] tv.(i))) else None in
  let args = List.rev (List.mapi map_args bl) in
  (params, args, a', body)

(*s names of the functions ([ids]) are already pushed in [env],
    and passed here just for convenience. *)

and pp_fix env i (ids,bl) =
  prvect
    (fun (id, (params, args, body, pp_body)) ->
      (if not (List.is_empty args) then
        pp_py_fundef params id args pp_body
      else
        pp_py_fundef_with_var params id pp_body) ++
      cut2 ())
    (Array.map2 (fun id b -> (Id.print id, pp_function env None b)) ids bl) ++
  (* adds pretty print i to args, no par *)
  pp_ret true (Id.print ids.(i))

(*s Pretty-printing of [Dfix] *)

let pp_Dfix (rv,c,t) =
  (* name of every fix to print *)
  let names = Array.map
    (fun r -> if is_inline_custom r then mt () else pp_global Term r) rv
  in
  let rec pp_one_Dfix init i =
    if i = Array.length rv then mt ()
    else
      (* void if inline_custom or (not_custom and unused) -> do not extract it *)
      let void = is_inline_custom rv.(0) ||
        (not (is_custom rv.(0)) &&
          match c.(i) with MLexn "UNUSED" -> true | _ -> false)
      in
      if void then pp_one_Dfix init (i+1)
      else
        (if init then mt () else cut2 ()) ++
        (if is_custom rv.(0) then
          v 4 (str "def " ++ names.(i) ++ str "():" ++ fnl () ++
            str (find_custom rv.(0)))
        else
          let params, args, body, pp_body =
            pp_function (empty_env ()) (Some t.(i)) c.(i) in
          if not (List.is_empty args) then
            pp_py_fundef params names.(i) args pp_body
          else
            pp_py_fundef_with_var params names.(i) pp_body) ++
        pp_one_Dfix false (i+1)
  in
  pp_one_Dfix true 0

let has_equiv = function
  | NoEquiv -> false
  | Equiv _ | RenEquiv _ -> true

let pp_equiv param_list name = function
| NoEquiv, _ -> mt ()
| Equiv kn, i -> pp_py_alias name None (pp_global Type (GlobRef.IndRef (MutInd.make1 kn,i)))
| RenEquiv ren, _  -> pp_py_alias name (Some ren) name

(*s Pretty-printing of inductive types declaration. *)
(* pp_one_ind ip_equiv survivingTypes inductiveTypeName constructorNames constructorsArgsMLTypes*)
let pp_one_ind ip_equiv pl name cnames ctyps =
  (* rename survivingTypes if needed*)
  let pl = rename_tvars keywords pl in
  (* pp_constructor: index * this constructor's args *)
  let pp_constructor i typs =
    pp_py_dataclass cnames.(i) pl [(name, pl)] [] (List.map (pp_type pl) typs) false in
  if (has_equiv (fst ip_equiv)) then (pp_equiv pl name ip_equiv, mt())
  else
  (* if one or more constructors, loop on ctyps *)
  pp_py_dataclass name pl [] [] [] false,
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
  let name = pp_global Type (GlobRef.IndRef (kn,0)) in
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

  let type_name = pp_global Type rec_type in
  let fieldnames = str_fields rec_type fields in
  let pl = rename_tvars keywords packet.ip_vars in
  let fieldtypes = List.map (pp_type pl) packet.ip_types.(0) in
  pp_py_dataclass type_name pl [] fieldnames fieldtypes true

(* pp_ind parentTypeName mlInductiveTypeList *)
let pp_ind kn ind =
  (* python does not care about mutually dependent types. they are just separate types. *)
  let names =
    (* mapping on inductive types, excluding logical ones *)
    Array.mapi
      (fun i p -> if p.ip_logical then mt () else
        pp_global Type (GlobRef.IndRef (kn,i)))
      ind.ind_packets
  in
  let cnames =
    (* mapping on inductive types *)
    Array.mapi
      (fun i p -> if p.ip_logical then [||] else
        (* mapping on ml_type list array, constructors array with their types in a list *)
        Array.mapi
          (fun j _ -> pp_global Cons (GlobRef.ConstructRef ((kn,i),j+1)))
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
      let name = pp_global ~cap:true Type r in
      let l = rename_tvars keywords l in
      (try
        let ids,s = find_type_custom r in
        pp_py_typedef name (pp_py_generics str ids) (str s)
      with Not_found ->
        if t == Taxiom then pp_py_typevar name ++ str (" # " ^ axiom_not_realized_msg)
        else pp_py_typedef name (pp_py_id_generics l) (pp_type l t))
  | Dterm (r, a, t) ->
      let name = pp_global Term r in
      (* if is_custom r then str (": " ^ find_custom r) *)
      (* DISCREPANCY BETWEEN THE RETURN INSIDE THE BODY AND THE DEFINITION *)
      let params, args, body, pp_body = pp_function (empty_env ()) (Some t) a in
      pp_definition false (empty_env ()) params name args pp_body body
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
