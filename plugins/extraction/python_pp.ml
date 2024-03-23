
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

(* Some utility functions *)

(* let singlequote s = "'" ^ s ^ "'" *)

let py_private_field str = Id.of_string ("_" ^ String.uncapitalize_ascii str)

let py_getter_from_private id =
  let s = Id.to_string id in
  Id.of_string ("get" ^ String.capitalize_ascii (String.sub s 1 (String.length s - 1)))

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
  | Some com -> pp_comment com ++ cut2 ()

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

let pp_py_getter fieldname =
  let pp =
    str "def get" ++ str (String.capitalize_ascii fieldname) ++
    str "(self):" ++ fnl () ++
    str "return self._" ++ str fieldname
  in
  v 4 pp

let pp_py_getter (fieldname, gettername) =
  let pp =
    str "def " ++ gettername ++ str "(self):" ++ fnl () ++
    str "return self." ++ fieldname
  in
  v 4 pp

(* let rec pp_py_class name pl parents fieldnames fieldtypes getters =
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
            cut2 () ++ prlist_with_sep cut2 pp_py_getters fieldnames
          else mt ()
        )
    ) *)

let pp_py_dataclass name pl parents fields getternames =
  str "@dataclass" ++ fnl () ++
  v 4 (
    str "class " ++ str name ++ pp_py_id_generics pl ++
    pp_py_tuple (List.map (fun (name, params) -> str name ++ pp_py_id_generics params) parents) ++
    str ":" ++ fnl () ++
    if List.is_empty fields then str "pass"
    else
      prlist_with_sep fnl (fun (name, typ) -> name ++ str ": " ++ typ) fields ++
      if List.is_empty getternames then mt ()
      else
        let fields = List.map (fun (name, _) -> name) fields in
        cut2 () ++ prlist_with_sep cut2 pp_py_getter (List.combine fields getternames)
    )

let pp_py_empty_dataclass name pl parents =
  pp_py_dataclass name pl parents [] []

let pp_py_instance classname args =
  classname ++ str "(" ++ prlist_with_sep (fun () -> str ", ") identity args ++ str ")"

let pp_py_alias name opt_module original_name =
  str name ++ str " = " ++
  match opt_module with None -> spc () | Some n -> str (n^".") ++
  str original_name

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

let pp_py_patmatch expr pat_br_vect =
  v 4 (str "match " ++ expr ++ str ":" ++ fnl () ++
    prvect_with_sep fnl (fun (pat, body) -> v 4 (
      str "case " ++ pat ++ str ":" ++ fnl () ++ body
    )) pat_br_vect
  )

let pp_ret ret s = if ret then (str "return " ++ s) else s

(* TODO: MAKE MORE GENERIC, NOW DONE AS FULL CURRIED *)
let rec pp_py_fundef params names args body =
  assert (not (List.is_empty names));
  let fundef_one_param params name (arg, typ) =
    str "def " ++ name ++ pp_py_generics identity params ++ str "(" ++ arg ++
    (match typ with None -> mt () | Some t -> str ": " ++ t) ++
    str "):" ++ fnl () in
  let pp =
    match names, args with
    | [], _ -> assert false
    | _ :: _ :: _, [] -> assert false
    | [n], [] -> fundef_one_param params n (mt (), None) ++ body
    | [n], [a] -> fundef_one_param params n a ++ body
    | n :: nl, a :: al -> fundef_one_param params n a ++ pp_py_nest_single_helper_fun [] nl al body
  in
  v 4 pp

and py_fun_of_str s = s ^ "_fun"

and py_fun_of_id id =
  if not (Id.equal id dummy_name) then Id.to_string id ^ "_fun"
  else "f"

and py_fun_of_mlid = function
  | Dummy -> "f"
  | Id id | Tmp id -> Id.to_string id ^ "_fun"

and pp_py_nest_single_helper_fun params names args body =
  match names, args with
  | [], _ :: _ -> assert false
  | _ :: _ :: _, [] -> assert false
  | [], [] -> body
  | [n], [] -> pp_py_helper_fun false params n (mt (), None) body
  | [n], [a] -> pp_py_helper_fun true params n a body
  | n :: nl, a :: al -> pp_py_helper_fun false params n a (pp_py_nest_single_helper_fun [] nl al body)

and pp_py_helper_fun last params name arg body =
  let fun_name = if Pp.ismt name then fst arg ++ str "_fun" else name in
  pp_py_fundef params [fun_name] [arg] body ++
  (if last then cut2 () else fnl ()) ++
  pp_ret true fun_name

let pp_py_fundef_with_var params var_name fun_name body =
  pp_py_fundef params [fun_name] [] body ++ fnl () ++
  (* store the result in a variable *)
  pp_py_vardef var_name [] (pp_py_funapp fun_name [])

let pp_py_ifthenelse cond pp_then pp_else =
  pp_then ++ str " if " ++ cond ++ str " else " ++ pp_else
