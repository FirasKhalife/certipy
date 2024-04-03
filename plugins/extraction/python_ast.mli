(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type py_id = string

type py_type_params = py_type list

and py_type =
  | PyTypeId of py_id
  | PyTypeGeneric of py_id * py_type_params

type py_params = (py_id * py_type option) list

type py_branch = py_expr * py_block

and py_branch_fundef = py_expr * py_block_fundef

and py_block = py_stmt_top list

and py_block_fundef = py_stmt list

and py_stmt =
  | PyStmtTop of py_stmt_top
  | PyStmtFunDef of py_stmt_fundef

and py_stmt_top =
  (* assignment (let-in): id * body *)
  | PyAssign of py_id * py_expr
  (* type alias * existing type *)
  | PyTypeAlias of py_type * py_type
  (* custom type definition: type alias * right-hand custom type *)
  | PyTypeAliasCustom of py_type * string
  (* type definition: id * var string *)
  | PyTypeDef of py_id * string
  (* raise exception: exception name * message. exception name should be exact! *)
  | PyRaise of py_id * string
  (* function definition: name * type params * parameters * body *)
  | PyFunDef of py_id * py_type_params * py_params * py_block_fundef
  (* custom function definition: name * body *)
  | PyCustomFunDef of py_id * string
  (* class definition: name * type params * parent classes * fields * getters *)
  | PyClassDef of py_id * py_type_params * py_type list * py_params * py_id list
  (* pattern matching: expression * list of branches *)
  | PyMatch of py_expr * py_branch list
  (* comment *)
  | PyComment of string

and py_stmt_fundef =
  (* return an expression *)
  | PyReturn of py_expr
  (* pattern matching: expression * list of branches *)
  | PyMatchFun of py_expr * py_branch_fundef list
  (* custom pattern matching: expression * list of branches * user input *)
  | PyMatchCustom of py_expr * py_expr list * string

and py_expr =
  (* id name *)
  | PyId of py_id
  (* class field access, dotted in practice; e.g. (exprReturningClassInstance).prop1.prop2 *)
  | PyFieldAccess of py_expr * py_id list
  (* function application: expression * args *)
  | PyApp of py_expr * py_expr list
  (* class instantiation: name * args *)
  | PyCons of py_expr * py_expr list
  (* lambda abstraction: parameters * body *)
  | PyLam of py_id list * py_expr
  (* tuple *)
  | PyTuple of py_expr list
  (* if expression *)
  | PyIfExpr of py_expr * py_expr * py_expr
