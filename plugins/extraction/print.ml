
open Format
open Utils
open Ast

let decorator = dprintf "@%s"

let py_id = str

let py_none = str "None"

let attribute obj = function
  | [] -> obj
  | fl -> dprintf "%t.%t" obj (concat_sep "." identity fl)

let rec py_type = function
  | TypeId id -> str id
  | TypeGeneric (id, params) -> dprintf "%s%t" id (type_params params)
  | Callable (args, ret) -> dprintf "Callable[%t, %t]" (type_params args) (py_type ret)

and type_params = function
  | [] -> mt
  | l -> brak_pat $ concat_map_comma_pp py_type l

let typed_id (name, t_opt) =
  dprintf "%s%t" name (map_or_mt (fun t -> dprintf ": %t" $ py_type t) t_opt)

let equal_ids id1 id2 = dprintf "%t = %t" id1 id2
let equal_typed_ids id1 id2 = dprintf "%t = %s" id1 id2

let dict_item k v = dprintf "%t: %t" k v

let await = dprintf "await %t"
let py_star = dprintf "*%t"
let py_doublestar = dprintf "**%t"
let py_str = dprintf "\'%s\'"
let py_int = of_int
let py_float = of_float
let py_bool = of_bool
let py_img {Complex.re ; Complex.im} =
  if im = 0. then dprintf "%f" re
  else if re = 0. then dprintf "%fj" im
  else dprintf "%f + %fj" re im

let comp_for is_async targets =
  let targets = concat_comma_pp targets in
  dprintf " for %s%t in %t" (if is_async then "async " else "") targets
let comp_if = dprintf " if %t"
let dict_comp = dprintf "{%t : %t}"
let comprehension expr comp_iter_l =
  dprintf "%t %t" expr (concat_sep_pp spc identity comp_iter_l)

let proper_slice lower upper stride =
  let pp = dprintf "%t:%t" (get_or_mt lower) (get_or_mt upper) in
  match stride with
  | None -> pp
  | Some s -> dprintf "%t:%t" pp s

let slicing e slices =
  let pp =
    match slices with
    | [] -> e
    | _ -> concat_sep_pp spc identity slices
  in
  dprintf "%t[%t]" e pp

let lambda_def ?(nl = false) args body =
  dprintf "@[<v 4>lambda%t: %t"
    (if args = [] then mt
     else (dprintf " %t" (concat_sep ", " identity args)))
    (if nl then dprintf "(@\n%t@]@\n)" body else dprintf "%t@]" body)

let dotted = concat_sep "." identity

let import names =
  let pp =
    match names with
    | [] -> raise (Invalid_argument "Empty import")
    | _ -> concat_map_comma_pp dotted names
  in
  dprintf "import %t" pp

let from_import modul names =
  let pp =
    match names with
    | [] -> raise (Invalid_argument "Empty import")
    | _ ->
      concat_map_comma_pp (fun (id, alias) ->
        let id = dotted id in
        match alias with None -> id | Some a -> dprintf "%t as %s" id a)
      names
  in
  dprintf "from %s import %t" modul pp

let from_import_all modul = dprintf "from %s import *" modul

let maybe_append_block name suite initial =
  if ismt (asprintf "%t" suite) then initial
  else dprintf "%t@\n@[<v 4>%s:@\n%t@]" initial name suite

let if_stmt cond then_block elifs else_block =
  let if_cond = dprintf "@[<v 4>if %t:@\n%t@]" cond then_block in
  let if_elifs =
    dprintf "%t%t" if_cond
      (concat_sep_pp fnl (fun (cond, body) -> dprintf "@\n@[<v 4>elif %t:@\n%t@]" cond body) elifs)
  in
  maybe_append_block "else" else_block if_elifs

let while_stmt cond body else_block =
  let while_block = dprintf "@[<v 4>while %t:@\n%t@]" cond body in
  maybe_append_block "else" else_block while_block

let for_stmt targets iterables body else_block =
  let targets = concat_comma_pp targets in
  let iterables = concat_comma_pp iterables in
  let for_block = dprintf "@[<v 4>for %t in %t:@\n%t@]" targets iterables body in
  maybe_append_block "else" else_block for_block

let except star exn target_opt body =
  let star_str = if star then "*" else "" in
  if ismt (asprintf "%t" exn) then dprintf "@[<v 4>except:@\n%t@]" body
  else
    match target_opt with
    | None -> dprintf "@[<v 4>except%s %t:@\n%t@]" star_str exn body
    | Some target -> dprintf "@[<v 4>except%s %t as %s:@\n%t@]" star_str exn target body

let try_except try_block (star, exns) else_block finally_block =
  let try_block = dprintf "@[<v 4>try:@\n%t@]" try_block in
  let try_exn =
    dprintf "%t@\n%t"
      try_block
      (concat_sep_pp fnl (fun (exn, target_opt, body) -> except star exn target_opt body) exns)
  in
  maybe_append_block "finally" finally_block $
    maybe_append_block "else" else_block try_exn

let try_finally try_block finally_block =
  let try_block = dprintf "@[<v 4>try:@\n%t@]" try_block in
  dprintf "%t@\n@[<v 4>finally:@\n%t@]" try_block finally_block

let with_stmt expr target body =
  dprintf "@[<v 4>with %t as %s:@\n%t@]" expr target body

let comment_one_line = dprintf "# %s"

let comment = dprintf "''' @[<hv 0>%s@] '''"

let pass = str "pass"
let break = str "break"
let continue = str "continue"
let return = dprintf "return %t"
let delete = dprintf "del %t"
let global l = dprintf "global %t" (concat_comma l)
let nonlocal l = dprintf "nonlocal %t" (concat_comma l)
let print = dprintf "print(%t)"

let py_raise exn msg from =
  if ismt from then dprintf "raise %s('%s')" exn from
  else dprintf "raise %s('%s') from %s" exn msg from

let py_assert expr expr_opt =
  dprintf "assert %t%t" expr $
    map_or_mt (dprintf ", %t") expr_opt

let yield_from exp = dprintf "yield from %t" exp
let yield_raw l =
  match l with
  | [] -> str "yield"
  | _ -> dprintf "yield %t" $ concat_map_comma_pp identity l

(* TODO: DEFAULT PARAMETERS *)
let py_args args =
  par_pat $ concat_map_comma_pp typed_id args

let fun_def name params args (body, ret_type) =
  dprintf "@[<v 4>def %s%t%t%t:@\n%t@]"
    name (type_params params) (py_args args)
    (match ret_type with None -> mt | Some t -> dprintf " -> %t" $ py_type t)
    body

let self_field = "self", None

let class_fields = function
  | [] -> mt
  | fields ->
      concat_sep_pp fnl (fun (name, typ) ->
        typed_id (name, (match typ with None -> Some (TypeId "Any") | Some _ -> typ)))
      fields

let match_args fields =
  dprintf "__match_args__ = (%t)" (concat_map_comma (asprintf "'%s'") fields)

let init fields =
  let body =
    match fields with
    | [] -> pass
    | fields -> concat_sep_pp fnl (fun (name, _) -> dprintf "self.%s = %s" name name) fields
  in
  fun_def "__init__" [] (self_field :: fields) (body, None)

let getter ?(gettername = "") field =
  let fun_name =
    if ismt gettername then asprintf "get_%s" (fst field)
    else gettername
  in
  fun_def fun_name [] [self_field] (return $ attribute (py_id "self") [fst field], None)

let getters fields = concat_sep_pp fnl (fun (name, _) -> getter name) fields

let setter ?(settername = "") field =
  let fun_name =
    if ismt settername then asprintf "set_%s" (fst field)
    else settername
  in
  fun_def fun_name [] [self_field; field] (return $ attribute (py_id "self") [fst field], None)

let setters fields = concat_sep_pp fnl (fun field -> setter field) fields

let __str__ fields =
  let body =
    match fields with
    | [] -> return $ str "()"
    | fields ->
        let list = concat_sep_pp (str ", ") (fun (name, _) -> dprintf "{%s}" name) fields in
        return $ dprintf "f'(%t)'" list
  in
  fun_def "__str__" [] [self_field] (body, None)

let class_def name pl parents body =
  dprintf "@[<v 4>class %s%t%t:@\n%t@]"
    name (type_params pl)
    (par_if_not_mt parents $ concat_map_comma_pp py_type parents)
    body

let type_alias t1 t2 = dprintf "type %t = %t" (py_type t1) (py_type t2)

let type_alias_custom t1 input = dprintf "type %t = %s" (py_type t1) input

let type_def id name = dprintf "%s = TypeVar('%s')" id name

let var_def ids expr =
  let ids =
    match ids with
    | [] -> raise (Invalid_argument "Empty assignment")
    | [id] -> typed_id id
    | _ -> concat_map_comma (fun (name, _) -> name) ids
  in
  dprintf "%t = %t" ids expr

let assign_expr id expr =
  dprintf "%s := %t" id expr

(* TODO: NAMED PARAMETERS *)
let app f args = dprintf "%t(%t)" f (concat_map_comma_pp identity args)

let py_match head branches =
  dprintf "@[<v 4>match %t:@\n%t@]" head $
    concat_sep_pp fnl (fun (pat, body) -> dprintf "@[<v 4>case %t:@\n%t@]" pat body) branches

let py_match_custom head branches user_input =
  dprintf "@[<v 4>%s@\n(%t%t)" user_input
    (concat_sep_pp (dprintf "") (fun br -> dprintf "%t,@\n" br) branches)
    head

let pp_ifexpr cond pp_then pp_else =
  dprintf "%t if %t else %t" pp_then cond pp_else

let of_un_op_pp op_str e = combine_sep spc [str op_str; e]
let of_bin_op_pp op_str e1 e2 = combine_sep spc [e1; str op_str; e2]

let pos e = of_un_op_pp "+" e
let neg e = of_un_op_pp "-" e
let not_ e = of_un_op_pp "not" e
let bit_not e = of_un_op_pp "~" e
let add e1 e2 = of_bin_op_pp "+" e1 e2
let sub e1 e2 = of_bin_op_pp "-" e1 e2
let mul e1 e2 = of_bin_op_pp "*" e1 e2
let matrix_mul e1 e2 = of_bin_op_pp "@" e1 e2
let div e1 e2 = of_bin_op_pp "/" e1 e2
let floor_div e1 e2 = of_bin_op_pp "//" e1 e2
let mod_ e1 e2 = of_bin_op_pp "%" e1 e2
let pow e1 e2 = of_bin_op_pp "**" e1 e2
let lshift e1 e2 = of_bin_op_pp "<<" e1 e2
let rshift e1 e2 = of_bin_op_pp ">>" e1 e2
let bit_or e1 e2 = of_bin_op_pp "|" e1 e2
let bit_xor e1 e2 = of_bin_op_pp "^" e1 e2
let bit_and e1 e2 = of_bin_op_pp "&" e1 e2
let eq e1 e2 = of_bin_op_pp "==" e1 e2
let neq e1 e2 = of_bin_op_pp "!=" e1 e2
let lt e1 e2 = of_bin_op_pp "<" e1 e2
let lte e1 e2 = of_bin_op_pp "<=" e1 e2
let gt e1 e2 = of_bin_op_pp ">" e1 e2
let gte e1 e2 = of_bin_op_pp ">=" e1 e2
let is_ e1 e2 = of_bin_op_pp "is" e1 e2
let is_not e1 e2 = of_bin_op_pp "is not" e1 e2
let in_ e1 e2 = of_bin_op_pp "in" e1 e2
let not_in e1 e2 = of_bin_op_pp "not in" e1 e2
