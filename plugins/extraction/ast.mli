
type py_id = string

(* dotted name * alias *)
type import = py_id list * py_id option

type typed_id = py_id * py_type option

and py_type =
  | TypeId of py_id
  | TypeGeneric of py_id * type_params
  | Callable of py_type list * py_type

and type_params = py_type list

type params = typed_id list

type branch = expr * block

and block = stmt list

and assigned_expr =
  | AssignedExpr of expr
  | AssignedYield of yield

and yield =
  (* yield from expr *)
  | YieldFrom of expr
  (* yield | yield exp1, exp2 *)
  | YieldRaw of expr list

and class_block = class_stmt list

and class_stmt =
  | ClassDecorator of py_id
  | ClassVarDef of typed_id list * expr
  | InstanceVarDef of py_id * py_type
  | MethodDef of py_id * type_params * params * (block * py_type option)

(* except [exception [as target]] : suite *)
and except = (expr * py_id option) option * block
(* except* exception [as target] : suite *)
and except_star = expr * py_id option * block
and except_list =
  | ExceptList of except list
  | ExceptStarList of except_star list

and stmt =
  (* import: dotted_name list *)
  | Import of (py_id list) list
  (* from import: module * (dotted_name list * alias) list *)
  | FromImport of py_id * (py_id list * py_id option) list
  (* from import all: module *)
  | FromImportAll of py_id
  (* expression: expression *)
  | Expression of expr
  (* decorator: expression *)
  | Decorator of py_id
  (* return an expression - only in function *)
  | Return of expr
  (* typed identifier: py_id * py_type *)
  | TypedId of typed_id
  (* assignment (let-in): typed_id * body *)
  | AssignStmt of typed_id list * assigned_expr
  (* type alias * existing type *)
  | TypeAlias of py_type * py_type
  (* type definition: py_id * var string *)
  | TypeDef of py_id * string
  (* raise exception: exception name * message * from expression *)
  | Raise of py_id * string * py_id option
  (* function definition: name * type params * parameters * body *)
  | FunDef of py_id * type_params * params * (block * py_type option)
  (* class definition: name * type params * parent classes * body *)
  | ClassDef of py_id * type_params * py_type list * class_block
  (* pattern matching: expression * list of branches *)
  | Match of expr * branch list
  (* if statement: condition * then block * elif block list * else block *)
  | IfStmt of expr * block * (expr * block) list * block
  (* while loop: condition * body * else block *)
  | While of expr * block * block
  (* for loop: variables * iterables * body * else block *)
  | For of expr list * expr list * block * block
  (* try-except: try block * (exception * target * catch block) list * else block * finally block *)
  | TryExcept of block * except_list * block * block
  (* try-finally: try block * finally block *)
  | TryFinally of block * block
  (* with: expression * target * body *)
  | With of expr * py_id * block
  (* print: expression *)
  | Print of expr list
  (* assert: expression, error message *)
  | Assert of expr * expr option
  (* delete: expr list *)
  | Delete of expr list
  (* global: py_id list *)
  | Global of py_id list
  (* nonlocal: py_id list *)
  | Nonlocal of py_id list
  (* comment *)
  | Comment of string
  (* pass *)
  | Pass
  (* break *)
  | Break
  (* continue *)
  | Continue

(* expr for expr in expr [if.. for.. if..] *)
and comp = expr * comp_iter list
and comp_iter =
  (* [async] for expr in expr *)
  | CompFor of bool * expr list * expr
  (* if expr *)
  | CompIf of expr

and slice =
  (* [lower bound] : [upper bound] [: stride] *)
  | ProperSlice of expr option * expr option * expr option
  (* any expr *)
  | SliceExpr of expr

and dict_item =
  (* key: value *)
  | DictItem of expr * expr
  (* **dict *)
  | DictUnpack of expr

and expr =
  (* identifier *)
  | Id of py_id
  (* await expression *)
  | Await of expr
  (* assignment expression: id := expr  *)
  | AssignExpr of py_id * expr
  (* class field access, dotted in practice; e.g. (exprReturningClassInstance).prop1.prop2 *)
  | Attribute of expr * py_id list
  (* function application: expression * args *)
  | App of expr * expr list
  (* lambda abstraction: parameters * body *)
  | Lam of py_id list * expr
  (* if expression: cond then else *)
  | IfExpr of expr * expr * expr
  (* yield: yield expression - only in function *)
  | Yield of yield
  (* tuple *)
  | PyTuple of expr list
  (* list *)
  | PyList of expr list
  (* set *)
  | PySet of expr list
  (* dictionary *)
  | Dict of dict_item list
  (* subscript: expr[e1, e2,...] *)
  | Subscription of expr * expr list
  (* slicing: primary * slice list  *)
  | Slicing of expr * slice list
  (* list comprehension: [comp] *)
  | ListComp of comp
  (* set comprehension: {comp} *)
  | SetComp of comp
  (* dictionary comprehension: {expr: comp} - syntactically identical but semantically different of a set *)
  | DictComp of expr * comp
  (* generator expression: (comp) *)
  | GenExpr of comp
  (* starred expression: *expr *)
  | Starred of expr
  (* double starred expression: **expr *)
  | DoubleStarred of expr
  (* string *)
  | String of string
  (* imaginary number *)
  | Img of Complex.t
  (* int *)
  | Int of int
  (* float *)
  | Float of float
  (* boolean *)
  | Bool of bool
  (* None *)
  | PyNone
  (* unary operators *)
  | UnOp of unary_op * expr
  (* binary operators *)
  | BinOp of binary_op * expr * expr

and unary_op =
  | Not
  | Pos
  | Neg
  | BitNot

and binary_op =
  | Add
  | Sub
  | Mul
  | MatrixMul
  | Div
  | FloorDiv
  | Mod
  | Pow
  | LShift
  | RShift
  | BitOr
  | BitAnd
  | BitXor
  | And
  | Or
  | Eq
  | Neq
  | Lt
  | LtE
  | Gt
  | GtE
  | Is
  | IsNot
  | In
  | NotIn
