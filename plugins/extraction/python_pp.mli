(* the following pretty prints header and opening used modules and usf *)

val preamble : 'a -> Pp.t option -> Names.ModPath.t list
                  -> Miniml.unsafe_needs -> Pp.t

val sig_preamble : 'a -> Pp.t option -> Names.ModPath.t list
                  -> Miniml.unsafe_needs -> Pp.t

(** Ad-hoc double-newline in v boxes, with enough negative whitespace
   to avoid indenting the intermediate blank line *)
val cut2 : unit -> Pp.t

(** pretty prints a type variable *)
val pp_py_tvar : Names.Id.t -> Pp.t

(** pretty prints mapped type parameters *)
val pp_py_generics : ('a -> Pp.t) -> 'a list -> Pp.t

(** pretty prints ID type parameters *)
val pp_py_id_generics : Names.Id.t list -> Pp.t

(** pretty prints a one line comment *)
val pp_comment_one_line : Pp.t -> Pp.t

(** pretty prints a comment *)
val pp_comment : Pp.t -> Pp.t

(** pretty prints a lambda abstraction, possibly with a new line and parenthesis *)
val pp_py_lambda: bool -> Pp.t list -> Pp.t -> Pp.t

(** pretty prints successive lambda abstractions of a single argument *)
val pp_py_nest_single_lambdas : Pp.t list -> Pp.t -> Pp.t

(** pretty prints a class *)
(* class name -> param list -> parent class names ->
    fieldnames -> fieldtypes -> if getters -> Pp.t *)
val pp_py_class : Pp.t -> Names.Id.t list -> (Pp.t * Names.Id.t list) list
                    -> string list -> Pp.t list -> bool -> Pp.t

(** pretty prints a dataclass *)
(* class name -> param list -> parent class names ->
    fieldnames -> fieldtypes -> if getters -> Pp.t *)
val pp_py_dataclass : Pp.t -> Names.Id.t list -> (Pp.t * Names.Id.t list) list
                        -> string list -> Pp.t list -> bool -> Pp.t

(** pretty prints creating an instance of a class *)
val pp_py_instance : Pp.t -> Pp.t list -> Pp.t

(** pretty prints a class alias *)
val pp_py_alias : Pp.t -> string option -> Pp.t -> Pp.t

(** pretty prints access to a variable via a getter *)
val pp_py_get_var : Pp.t -> string -> Pp.t

(** pretty prints a type definition *)
val pp_py_typedef : Pp.t -> Pp.t -> Pp.t -> Pp.t

(** pretty prints a type variable declaration *)
val pp_py_typevar : Pp.t -> Pp.t

(** pretty prints a callable type, possibly with generic parameters *)
val pp_py_type_callable : bool -> Pp.t list -> Pp.t -> Pp.t

(** pretty prints a function definition *)
(* params -> name -> args -> body -> Pp.t *)
val pp_py_fundef : Pp.t list -> Pp.t -> (Pp.t * Pp.t option) list -> Pp.t -> Pp.t

(** pretty prints a variable definition with lambdas *)
val pp_py_vardef : Pp.t -> Pp.t list -> Pp.t -> Pp.t

(** pretty prints a function application *)
val pp_py_funapp : Pp.t -> Pp.t list -> Pp.t

(** pretty prints an exception raise *)
val pp_py_raise : string -> string -> Pp.t

(** pretty prints a pattern matching statement *)
(* name -> (pattern * body) array -> Pp.t *)
val pp_py_patmatch : Pp.t -> (Pp.t * Pp.t) array -> Pp.t

(** adds the "return" keyword before the element if first arg is true *)
val pp_ret : bool -> Pp.t -> Pp.t

(** pretty prints a helper function based on its arguments
    e.g. [pp_py_helper_fun [a; b] body] will return
    [def a_fun(a, b):
        body

     return lambda (a, b): a_fun(a, b)]
    the blank line between the body and the lambda shows only if the first argument is true
*)
val pp_py_helper_fun : bool -> Pp.t list -> (Pp.t * Pp.t option) list -> Pp.t -> Pp.t

(** pretty prints successive helper functions of one argument *)
val pp_py_nest_single_helper_fun : Pp.t list -> (Pp.t * Pp.t option) list -> Pp.t -> Pp.t

(** pretty prints a function definition followed by *)
val pp_py_fundef_with_var : Pp.t list -> Pp.t -> Pp.t -> Pp.t

(** pretty prints an if expression
    e.g. [pp_py_ifthenelse cond then_ else_] will return
    [then_ if cond else else_]
*)
val pp_py_ifthenelse : Pp.t -> Pp.t -> Pp.t -> Pp.t
