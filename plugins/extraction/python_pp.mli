
(** returns the string field privatised as an Id *)
val py_private_field : string -> Names.Id.t

(** returns the Id field getter name as an Id *)
val py_getter_from_private : string -> Names.Id.t

(** Ad-hoc double-newline in v boxes, with enough negative whitespace
   to avoid indenting the intermediate blank line *)
val cut2 : unit -> Pp.t

(** pretty prints a mapped list *)
val pp_py_map_list : ('a -> Pp.t) -> 'a list -> Pp.t

(** pretty prints the passed list *)
val pp_py_list : Pp.t list -> Pp.t

(** pretty prints the passed list mapped as a tuple,
    possibly with empty parenthesis if the list is empty *)
val pp_py_map_tuple : ('a -> Pp.t) -> 'a list -> bool -> Pp.t

(** pretty prints the passed list as a tuple,
    possibly with empty parenthesis if the list is empty *)
val pp_py_tuple : Pp.t list -> bool -> Pp.t

(** pretty prints a type variable *)
val pp_py_type : Python_ast.py_type -> Pp.t

(** pretty prints type parameters *)
val pp_py_type_params : Python_ast.py_type list -> Pp.t

(** pretty prints a lambda abstraction, possibly with a new line and parenthesis *)
val pp_py_lambda : bool -> string list -> Pp.t -> Pp.t

(** pretty prints a one line comment *)
val pp_comment_one_line : string -> Pp.t

(** pretty prints a comment *)
val pp_comment : string -> Pp.t

(** pretty prints opening a module *)
val pp_open : Names.ModPath.t -> Pp.t

(** pretty prints a header comment *)
val pp_header_comment : string option -> Pp.t

(** pretty prints a new line if the passed element is not empty *)
val then_nl : Pp.t -> Pp.t

(** pretty prints the mldummy def *)
val pp_mldummy : Miniml.unsafe_needs -> Pp.t

(* the following pretty prints header and opening used modules and usf *)

val preamble : 'a -> Pp.t option -> Names.ModPath.t list
              -> Miniml.unsafe_needs -> Pp.t

val sig_preamble : 'a -> Pp.t option -> Names.ModPath.t list
                  -> Miniml.unsafe_needs -> Pp.t

(** pretty prints a getter definition based on the fieldname and gettername *)
val pp_py_getter : (string * string) -> Pp.t

(** pretty prints a term alias *)
val pp_py_alias : string -> string option -> string -> Pp.t

(** pretty prints a field access: object -> fields -> Pp.t *)
val pp_py_field_access : Pp.t -> string list -> Pp.t

(** pretty prints a dataclass *)
(* class name -> type params -> parents -> fields -> getternames -> Pp.t *)
val pp_py_dataclass : string -> Python_ast.py_type_params -> Python_ast.py_type list
                    -> Python_ast.py_params -> string list -> Pp.t

(** pretty prints an empty dataclass *)
val pp_py_empty_dataclass : string -> Python_ast.py_type list -> Python_ast.py_type list -> Pp.t

(** pretty prints creating an instance of a class *)
val pp_py_instance : Pp.t -> Pp.t list -> Pp.t

(** pretty prints a type alias *)
val pp_py_type_alias : Python_ast.py_type -> Python_ast.py_type -> Pp.t

(** pretty prints a custom type alias *)
val pp_py_type_alias_custom : Python_ast.py_type -> string -> Pp.t

(** pretty prints a type definition *)
val pp_py_typedef : string -> string -> Pp.t

(** pretty prints a variable definition with lambdas *)
val pp_py_vardef : string -> Pp.t -> Pp.t

(** pretty prints a function application *)
val pp_py_app : Pp.t -> Pp.t list -> Pp.t

(** pretty prints an exception raise *)
val pp_py_raise : string -> string -> Pp.t

(** pretty prints a pattern matching statement *)
(* head -> (pattern * body) list -> Pp.t *)
val pp_py_match : Pp.t -> (Pp.t * Pp.t) list -> Pp.t

(** pretty prints a custom pattern matching statement *)
(* head -> branch expressions -> user input -> Pp.t *)
val pp_py_match_custom : Pp.t -> Pp.t list -> string -> Pp.t

(** adds the "return" keyword before the element *)
val pp_py_ret : Pp.t -> Pp.t

(* pretty prints arguments and their types,
   possibly with the "any" type if the passed type is None *)
val pp_py_args : Python_ast.py_params -> Pp.t

(** pretty prints a function definition *)
(* name -> type params -> args -> body -> Pp.t *)
val pp_py_fundef : string -> Python_ast.py_type_params
                  -> Python_ast.py_params -> Pp.t -> Pp.t

(** returns a function name that would serve as a helper function from the arg name *)
val py_fun_of_str : string -> Names.Id.t

(** same as [py_fun_of_str] but takes a ml_ident *)
val py_fun_of_mlid : Miniml.ml_ident -> Names.Id.t

(** pretty prints a function definition followed by a variable storing the result *)
val pp_py_fundef_with_var : string -> Python_ast.py_type list -> string -> Pp.t -> Pp.t

(** pretty prints an if expression
    e.g. [pp_py_ifexpr cond then_ else_] will return
    [then_ if cond else else_]
*)
val pp_py_ifexpr : Pp.t -> Pp.t -> Pp.t -> Pp.t
