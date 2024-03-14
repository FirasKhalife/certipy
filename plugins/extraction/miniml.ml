(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s Target language for extraction: a core ML called MiniML. *)

open Names

(* The [signature] type is used to know how many arguments a CIC
   object expects, and what these arguments will become in the ML
   object. *)

(* We eliminate from terms:
   1) types
   2) logical parts
   3) user-declared implicit arguments of a constant of constructor
*)

type kill_reason =
  (* type *)
  | Ktype
  (* logical part (Prop) *)
  | Kprop
  (* implicit argument: arg name * arg index *)
  | Kimplicit of GlobRef.t * int  (* n-th arg of a cst or construct *)

type sign =
  (* Keep term *)
  | Keep
  (* Kill term with reason *)
  | Kill of kill_reason


(* Convention: outmost lambda/product gives the head of the list. *)

(* arguments expected by an ML term and whether to keep or kill them *)
type signature = sign list

(*s ML type expressions. *)

type ml_type =
  (* Tarrow: ml_type -> ml_type *)
  | Tarr    of ml_type * ml_type
  (* global type: global type name * arguments types *)
  | Tglob   of GlobRef.t * ml_type list
  (* simple type variable: index in env *)
  | Tvar    of int
  | Tvar'   of int (* same as Tvar, used to avoid clash *)
  | Tmeta   of ml_meta (* used during ML type reconstruction *)
  (* dummy type for killed types *)
  | Tdummy  of kill_reason
  (* unknown type *)
  | Tunknown
  (* axiom type *)
  | Taxiom

and ml_meta = { id : int; mutable contents : ml_type option }

(* ML type schema.
   The integer is the number of variable in the schema. *)

(* ??? *)
type ml_schema = int * ml_type

(*s ML inductive types. *)

type inductive_kind =
  (* a type with only one constructor and only one argument to this constructor
     e.g. Inductive natPair := pair (n: nat) --> type natPair = nat, seen as an alias to the argument *)
  | Singleton
  (* like standard inductive, but infinite (e.g. streams). Uses lazy computation. *)
  | Coinductive
  (* standard inductive type *)
  | Standard
  (* record: list of optional field names (None if anynomous, represented by _ in Gallina) *)
  | Record of GlobRef.t option list (* None for anonymous field *)

(* A [ml_ind_packet] is the miniml counterpart of a [one_inductive_body].
   If the inductive is logical ([ip_logical = false]), then all other fields
   are unused. Otherwise,
   [ip_sign] is a signature concerning the arguments of the inductive,
   [ip_vars] contains the names of the type variables surviving in ML,
   [ip_types] contains the ML types of all constructors.
*)

type ml_ind_packet = {
  (* inductive type name *)
  ip_typename : Id.t;
  (* constructor names *)
  ip_consnames : Id.t array;
  (* true if inductive is logical => not extracted *)
  ip_logical : bool;
  (* list of args as keep or kill of kill_reason *)
  ip_sign : signature;
  (* names of type variables surviving
     e.g. Inductive anyPair (A:Set) := pair (x: A) --> type 'a pair = 'a *)
  ip_vars : Id.t list;
  (* the arguments types (ml_type list) for each constructor (cons array) *)
  ip_types : (ml_type list) array
}

(* [ip_nparams] contains the number of parameters. *)

type equiv =
  (* no equivalent term *)
  | NoEquiv
  (* equivalent to a path name - usually closed module *)
  | Equiv of KerName.t
  (* equivalent to a term in an open module => purely alias (renaming) *)
  | RenEquiv of string

type ml_ind = {
  (* kind of inductive (Singleton, Co, Standard, Record)*)
  ind_kind : inductive_kind;
  (* number of parameters for each inductive type,
     as parameters should be syntactically the same (same names also) for each inductive type *)
  ind_nparams : int;
  (* array of mutually inductive types *)
  ind_packets : ml_ind_packet array;
  (* potential equivalence/alias *)
  ind_equiv : equiv
}

(*s ML terms. *)

type ml_ident =
  (* dummy identifier *)
  | Dummy
  (* regular identifier *)
  | Id of Id.t
  (* temporary identifier *)
  | Tmp of Id.t

(** We now store some typing information on constructors
    and cases to avoid type-unsafe optimisations. This will be
    either the type of the applied constructor or the type
    of the head of the match.
*)

(** Nota : the constructor [MLtuple] and the extension of [MLcase]
    to general patterns have been proposed by P.N. Tollitte for
    his Relation Extraction plugin. [MLtuple] is currently not
    used by the main extraction, as well as deep patterns. *)

(* ml_branch = id list * patternToCheckOn * branchBody *)
type ml_branch = ml_ident list * ml_pattern * ml_ast

and ml_ast =
  (* indice de De Bruijn *)
  | MLrel    of int
  (* function application : function * args *)
  | MLapp    of ml_ast * ml_ast list
  (* lambda abstraction: var * body. fun var -> body. *)
  | MLlam    of ml_ident * ml_ast
  (* let in expression: var * def * body. let var = def in body. *)
  | MLletin  of ml_ident * ml_ast * ml_ast
  (* global reference: name *)
  | MLglob   of GlobRef.t
  (* constructor: type (not used) * ref (used as is_infix... why?) * cons args *)
  | MLcons   of ml_type * GlobRef.t * ml_ast list
  (* tuple: list to print as tuple *)
  | MLtuple  of ml_ast list
  (* switch case: type (why?) * expr to match * patterns' branches(id list * pattern * branchBody) *)
  | MLcase   of ml_type * ml_ast * ml_branch array
  (* fixpoint abstraction: nameIndex * functionNames * functionBodies *)
  | MLfix    of int * Id.t array * ml_ast array
  (* exception: exceptionMessage *)
  | MLexn    of string
  (* dummy type, printed as '__' with kill reason as a comment *)
  | MLdummy  of kill_reason
  (* axiom to be realized? *)
  | MLaxiom
  (* expression to cast: expression *)
  | MLmagic  of ml_ast
  (* int *)
  | MLuint   of Uint63.t
  (* float *)
  | MLfloat  of Float64.t
  (* native array? *)
  | MLparray of ml_ast array * ml_ast

and ml_pattern =
  | Pcons   of GlobRef.t * ml_pattern list
  | Ptuple  of ml_pattern list
  | Prel    of int (** Cf. the idents in the branch. [Prel 1] is the last one. *)
  | Pwild   (* wildcard ('_') *)
  | Pusual  of GlobRef.t (** Shortcut for Pcons (r,[Prel n;...;Prel 1]) **)

(*s ML declarations. *)

type ml_decl =
  (* inductive type declaration: mutual inductive name * ind details *)
  | Dind  of MutInd.t * ml_ind
  (* type declaration: name * args name list * right hand ml_type. type 'a h = 'a list *)
  | Dtype of GlobRef.t * Id.t list * ml_type
  (* term declaration: name * term ast * term type *)
  | Dterm of GlobRef.t * ml_ast * ml_type
  (* mutually recursive definitions (Fixpoint... with...): names * definitions ast * type arrays *)
  | Dfix  of GlobRef.t array * ml_ast array * ml_type array

type ml_spec =
  | Sind  of MutInd.t * ml_ind
  | Stype of GlobRef.t * Id.t list * ml_type option
  | Sval  of GlobRef.t * ml_type

type ml_specif =
  | Spec of ml_spec
  | Smodule of ml_module_type
  | Smodtype of ml_module_type

and ml_module_type =
  | MTident of ModPath.t
  | MTfunsig of MBId.t * ml_module_type * ml_module_type
  | MTsig of ModPath.t * ml_module_sig
  | MTwith of ml_module_type * ml_with_declaration

and ml_with_declaration =
  | ML_With_type of Id.t list * Id.t list * ml_type
  | ML_With_module of Id.t list * ModPath.t

and ml_module_sig = (Label.t * ml_specif) list

type ml_structure_elem =
  | SEdecl of ml_decl
  | SEmodule of ml_module
  | SEmodtype of ml_module_type

and ml_module_expr =
  | MEident of ModPath.t
  | MEfunctor of MBId.t * ml_module_type * ml_module_expr
  | MEstruct of ModPath.t * ml_module_structure
  | MEapply of ml_module_expr * ml_module_expr

and ml_module_structure = (Label.t * ml_structure_elem) list

and ml_module =
    { ml_mod_expr : ml_module_expr;
      ml_mod_type : ml_module_type }

(* NB: we do not translate the [mod_equiv] field, since [mod_equiv = mp]
   implies that [mod_expr = MEBident mp]. Same with [msb_equiv]. *)

type ml_structure = (ModPath.t * ml_module_structure) list

type ml_signature = (ModPath.t * ml_module_sig) list

type unsafe_needs = {
  mldummy : bool;
  tdummy : bool;
  tunknown : bool;
  magic : bool
}

type language_descr = {
  keywords : Id.Set.t;

  (* Concerning the source file *)
  file_suffix : string;
  file_naming : ModPath.t -> string;
  (* the second argument is a comment to add to the preamble *)
  preamble :
    Id.t -> Pp.t option -> ModPath.t list -> unsafe_needs ->
    Pp.t;
  pp_struct : ml_structure -> Pp.t;

  (* Concerning a possible interface file *)
  sig_suffix : string option;
  (* the second argument is a comment to add to the preamble *)
  sig_preamble :
    Id.t -> Pp.t option -> ModPath.t list -> unsafe_needs ->
    Pp.t;
  pp_sig : ml_signature -> Pp.t;

  (* for an isolated declaration print *)
  pp_decl : ml_decl -> Pp.t;

}
