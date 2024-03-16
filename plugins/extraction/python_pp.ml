
open Pp
(* open CErrors *)
open Util
open Names
(* open ModPath *)
open Table
(* open Miniml *)
(* open Mlutil *)
(* open Modutil *)
open Common

(* Some utility functions *)

let starting_sym = Char.code 'a' - 1
let r = ref (starting_sym)
let reset_gensym () = r := starting_sym
let gensym () = incr r; String.make 1 (Char.chr !r)

(* let singlequote s = "'" ^ s ^ "'" *)

let cut2 () = brk (0,-100000) ++ brk (0,0)

let pp_py_list f l =
  str "[" ++ prlist_with_sep (fun () -> str ", ") f l ++ str "]"

let pp_py_tuple = function
| [] -> mt ()
| l ->  str "(" ++ prlist_with_sep (fun () -> str ", ") identity l ++ str ")"

let pp_py_tvar id = str (String.capitalize_ascii (Id.to_string id))

let pp_py_generics f = function
| [] -> mt ()
| l -> pp_py_list f l

let pp_py_id_generics l = pp_py_generics pp_py_tvar l

let pp_py_lambda nl args body =
  let pp = str "lambda " ++ pp_boxed_tuple identity args ++ str ": " in
  if nl then v 4 (pp ++ str "(" ++ fnl () ++ body) ++ fnl () ++ str ")"
  else pp ++ body

let rec pp_py_nest_single_lambdas args body =
  match args with
  | [] -> body
  | [x] -> pp_py_lambda false [x] body
  | x :: xs -> pp_py_lambda true [x] (pp_py_nest_single_lambdas xs body)

let pp_comment_one_line s = str "# " ++ s

let pp_comment s = str "''' " ++ hv 0 s ++ str " '''"

(* pretty printing opening a module *)
let pp_open mp = str ("open "^ string_of_modfile mp) ++ fnl ()

(* pretty printing (header) comment, adding two new lines after it *)
let pp_header_comment = function
  | None -> mt ()
  | Some com -> pp_comment com ++ fnl2 ()

(* prints a new line following pretty printed expr if it is not empty *)
let then_nl pp = if Pp.ismt pp then mt () else pp ++ fnl ()

(* pretty printing to erase uncovered types *)
(* let pp_mldummy usf =
  if usf.mldummy then
    str "__ = lambda x: __" ++ fnl ()
  else mt () *)

let preamble _ comment used_modules usf =
  pp_header_comment comment ++
  then_nl (prlist pp_open used_modules)
  (* then_nl (pp_tdummy usf ++ pp_mldummy usf) *)

let sig_preamble _ comment used_modules usf =
  pp_header_comment comment ++
  then_nl (prlist pp_open used_modules)
  (* then_nl (pp_tdummy usf) *)

let pp_py_getters fieldname =
  let pp =
    str "def get" ++ str (String.capitalize_ascii fieldname) ++ str "(self):" ++ fnl () ++
    str "return self._" ++ str fieldname
  in
  v 4 pp

let rec pp_py_class name pl parents fieldnames fieldtypes getters =
  if List.is_empty fieldnames && not (List.is_empty fieldtypes) then
    (reset_gensym ();
    let fieldnames = List.map (fun _ -> gensym()) fieldtypes in
    pp_py_class name pl parents fieldnames fieldtypes getters)
  else
    v 4 (
      str "class " ++ name ++ pp_py_id_generics pl ++
      pp_py_tuple (List.map (fun (name, params) -> name ++ pp_py_id_generics params) parents) ++
      str ":" ++ fnl () ++
      if List.is_empty fieldnames then str "pass"
      else
        let priv_fieldnames = List.map (fun x -> str ("_" ^ x)) fieldnames in
        (* match args, with an extra comma at the end of the tuple *)
        str "__match_args__ = (" ++
        prlist_with_sep spc (fun x -> x ++ str ",") priv_fieldnames  ++
        str ")" ++ fnl () ++
        (* init function signature *)
        v 4 (str "def __init__(self, " ++
          prlist_with_sep (fun () -> str ", ") identity priv_fieldnames ++ str "):" ++ fnl () ++
          (* init function body *)
          prlist_with_sep fnl (fun x -> str "self." ++ x ++ str " = " ++ x) priv_fieldnames ++
          (* getters for every attributes if getters = true *)
          if getters then
            fnl2 () ++ prlist_with_sep fnl2 pp_py_getters fieldnames
          else mt ()
        )
    )

let rec pp_py_dataclass name pl parents fieldnames fieldtypes getters =
  if List.is_empty fieldnames && not (List.is_empty fieldtypes) then
    (reset_gensym ();
    let fieldnames = List.map (fun _ -> gensym()) fieldtypes in
    pp_py_dataclass name pl parents fieldnames fieldtypes getters)
  else
    str "@dataclass" ++ fnl () ++
    v 4 (
      str "class " ++ name ++ pp_py_id_generics pl ++
      pp_py_tuple (List.map (fun (name, params) -> name ++ pp_py_id_generics params) parents) ++
      str ":" ++ fnl () ++
      if List.is_empty fieldnames then str "pass"
      else
        let priv_fieldnames = List.map (fun x -> str ("_" ^ x)) fieldnames in
        prlist_with_sep fnl (fun (name, typ) -> name ++ str ": " ++ typ)
          (List.combine priv_fieldnames fieldtypes) ++
        (* getters for every attributes if getters = true *)
        if getters then
          fnl2 () ++ prlist_with_sep fnl2 pp_py_getters fieldnames
        else mt ()
    )

let pp_py_instance classname args =
  classname ++ str "(" ++ prlist_with_sep (fun () -> str ", ") identity args ++ str ")"

let pp_py_alias name opt_module original_name =
  name ++ str " = " ++
  match opt_module with None -> spc () | Some n -> str (n^".") ++
  original_name

let pp_py_typedef name generics typ =
  str "type " ++ name ++ generics ++ str " = " ++ typ

let pp_py_get_var classname field =
  classname ++ str ".get" ++ str (String.capitalize_ascii field)

let pp_py_typevar name =
  name ++ str " = TypeVar('" ++ name ++ str "')"

let pp_py_type_callable args return =
  str "Callable[" ++
    (if Int.equal (List.length args) 1 then List.hd args
    else pp_py_list identity args) ++ str ", " ++
    return ++ str "]"

let pp_py_vardef name args value =
  name ++ str " = " ++ pp_py_nest_single_lambdas args value

let pp_py_funapp f args =
  f ++ if List.is_empty args then str "()" else prlist (pp_par true) args

let pp_py_raise exc msg =
  str ("raise " ^ exc ^ "(" ^ msg ^ ")")

let pp_py_patmatch expr pat_br_list =
  v 4 (str "match " ++ expr ++ str ":" ++ fnl () ++
    prvect_with_sep fnl (fun (pat, body) -> v 4 (
      str "case " ++ pat ++ str ":" ++ fnl () ++ body
    )) pat_br_list
  )

let pp_ret ret s = if ret then (str "return " ++ s) else s

let rec pp_py_fundef params name args body =
  let pp =
    str "def " ++ name ++ pp_py_generics identity params ++
    let one_param (arg, typ) =
      str "(" ++ arg ++
      (match typ with None -> mt () | Some t -> str ": " ++ t) ++
      str "):" in
    match args with
    | [] -> str "():" ++ fnl() ++ body
    | [x] -> one_param x ++ fnl () ++ body
    | x :: xs -> one_param x ++ fnl () ++ pp_py_nest_single_helper_fun [] xs body
  in
  v 4 pp

and pp_py_nest_single_helper_fun params args body =
  match args with
  | [] -> body
  | [x] -> pp_py_helper_fun true params [x] body
  | x :: xs -> pp_py_helper_fun false params [x] (pp_py_nest_single_helper_fun [] xs body)

and pp_py_helper_fun last params args body =
  let fun_name = fst (List.hd args) ++ str "_fun" in
  pp_py_fundef params fun_name args body ++ fnl () ++
  (if last then fnl () else mt ()) ++
  pp_ret true fun_name

let pp_py_fundef_with_var params var_name body =
  let fun_name = var_name ++ str "_fun" in
  pp_py_fundef params fun_name [] body ++ fnl () ++
  (* store the result in a variable *)
  pp_py_vardef var_name [] (pp_py_funapp fun_name []) ++ fnl ()

let pp_py_ifthenelse cond pp_then pp_else =
  pp_then ++ str " if " ++ cond ++ str " else " ++ pp_else
