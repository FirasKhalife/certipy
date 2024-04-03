
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
open Python_ast

(* Some utility functions *)

let py_private_field str = Id.of_string ("_" ^ String.uncapitalize_ascii str)

let py_getter_from_private s =
  Id.of_string (
    "get" ^ String.capitalize_ascii (String.sub s 1 (String.length s - 1)))

let cut2 () = brk (0,-100000) ++ brk (0,0)

let pp_py_map_list f l =
  str "[" ++ prlist_with_sep (fun () -> str ", ") f l ++ str "]"

let pp_py_list l = pp_py_map_list identity l

let pp_py_map_tuple f l par =
  match l with
  | [] -> if par then str "()" else mt ()
  | l ->  str "(" ++ prlist_with_sep (fun () -> str ", ") f l ++ str ")"

let pp_py_tuple = pp_py_map_tuple identity

let rec pp_py_type = function
  | PyTypeId id -> str id
  | PyTypeGeneric (id, params) -> str id ++ pp_py_type_params params

and pp_py_type_params = function
| [] -> mt ()
| l -> pp_py_map_list pp_py_type l

let pp_py_lambda nl args body =
  let pp =
    str "lambda" ++
    (if List.is_empty args then mt ()
     else (str " " ++ prlist_with_sep (fun () -> str ", ") str args)) ++
    str ": "
  in
  if not nl then pp ++ body
  else (v 4 (pp ++ str "(" ++ fnl () ++ body) ++ fnl () ++ str ")")

let pp_comment_one_line s = str ("# " ^ s)

let pp_comment s = str "''' " ++ hv 0 (str s) ++ str " '''"

let pp_comment_pp s = str "''' " ++ hv 0 s ++ str " '''"

(* pretty printing opening a module *)
let pp_open mp = str ("open " ^ string_of_modfile mp) ++ fnl ()

(* pretty printing (header) comment, adding two new lines after it *)
let pp_header_comment = function
  | None -> mt ()
  | Some com -> pp_comment com ++ cut2 ()

let pp_header_comment_pp = function
| None -> mt ()
| Some com -> pp_comment_pp com ++ cut2 ()

let then_nl pp = if Pp.ismt pp then mt () else pp ++ fnl ()

(* pretty printing to erase uncovered types *)
let pp_mldummy usf =
  if usf.mldummy then
    str "__ = lambda x: __" ++ fnl ()
  else mt ()

  (* Id.t -> Pp.t option -> ModPath.t list -> unsafe_needs ->
    Pp.t*)
let preamble _ comment used_modules usf =
  pp_header_comment_pp comment ++
  then_nl (prlist pp_open used_modules)
  (* then_nl (pp_tdummy usf ++ pp_mldummy usf) *)

let sig_preamble _ comment used_modules usf =
  pp_header_comment_pp comment ++
  then_nl (prlist pp_open used_modules)
  (* then_nl (pp_tdummy usf) *)

let pp_py_getter (fieldname, gettername)  =
  let pp =
    str "def " ++ str gettername ++ str "(self):" ++ fnl () ++
    str "return self." ++ str fieldname
  in
  v 4 pp

let pp_py_alias name opt_module original_name =
  str name ++ str " = " ++
  match opt_module with None -> spc () | Some n -> str (n ^ ".") ++
  str original_name

let pp_py_field_access obj fl =
  obj ++ prlist (fun x -> str "." ++ str x) fl

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
    str "class " ++ str name ++ pp_py_type_params pl ++
    pp_py_tuple (List.map pp_py_type parents) false ++
    str ":" ++ fnl () ++
    if List.is_empty fields then str "pass"
    else
      prlist_with_sep fnl
        (fun (name, typ) ->
          str name ++ str ": " ++
          if Option.is_empty typ then str "any" else pp_py_type (Option.get typ))
        fields ++
      if List.is_empty getternames then mt ()
      else
        let fieldnames = List.map (fun (name, _) -> name) fields in
        cut2 () ++ prlist_with_sep cut2 pp_py_getter (List.combine fieldnames getternames)
    )

let pp_py_empty_dataclass name pl parents =
  pp_py_dataclass name pl parents [] []

let pp_py_instance expr args =
  expr ++ pp_py_tuple args true

let pp_py_type_alias t1 t2 =
  str "type " ++ pp_py_type t1 ++ str " = " ++ pp_py_type t2

let pp_py_type_alias_custom t1 s =
  str "type " ++ pp_py_type t1 ++ str " = " ++ str s

let pp_py_typedef id s =
  str id ++ str " = TypeVar('" ++ str s ++ str "')"

let pp_py_vardef name expr =
  str name ++ str " = " ++ expr

let pp_py_app f args =
  f ++ if List.is_empty args then str "()" else prlist (pp_par true) args

let pp_py_raise exc msg =
  str (Printf.sprintf "raise %s(%s)" exc msg)

let pp_py_match head branches =
  let pp =
    str "match " ++ head ++ str ":" ++ fnl () ++
    prlist_with_sep fnl
      (fun (pat, body) -> v 4 (
        str "case " ++ pat ++ str ":" ++ fnl () ++ body))
    branches
  in
  v 4 pp

let pp_py_match_custom head branches user_input =
  let pp =
    str user_input ++ fnl () ++
    prlist (fun br -> br ++ str "," ++ fnl()) branches ++
    head
  in
  v 4 pp

let pp_py_ret s = str "return " ++ s

let pp_py_args args =
  let pp_py_one_arg (name, typ_opt) =
    str name ++
    match typ_opt with
    | None -> mt ()
    | Some t -> str ": " ++ pp_py_type t
  in
  pp_py_map_tuple pp_py_one_arg args true


let pp_py_fundef name params args body =
  let pp =
    str "def " ++ str name ++ pp_py_type_params params ++ pp_py_args args ++
    str ":" ++ fnl () ++ body
  in
  v 4 pp

let py_fun_of_str s =
  let s =
    if not (Id.equal (Id.of_string s) dummy_name) then "_" ^ s ^ "_fun"
    else "_aux_fun"
  in
  Id.of_string s

let py_fun_of_mlid mlid =
  let s =
    match mlid with
    | Dummy -> "f"
    | Id id | Tmp id -> Id.to_string id ^ "_fun"
  in
  Id.of_string s

let pp_py_fundef_with_var fun_name params var_name body =
  pp_py_fundef fun_name params [] body ++ fnl () ++
  (* store the result in a variable *)
  pp_py_vardef var_name (pp_py_app (str fun_name) [])

let pp_py_ifexpr pp_cond pp_then pp_else =
  pp_then ++ str " if " ++ pp_cond ++ str " else " ++ pp_else
