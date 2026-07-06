type bop =
  | Add | Sub | Mul | Div | Mod
  | Lt | Gt | Le | Ge | Eq | Neq
  | And | Or

type uop = Neg | Not

type typ = Int | Void

type expr =
  | IntLit of int
  | Id of string
  | BinOp of bop * expr * expr
  | UnaryOp of uop * expr
  | Call of string * expr list

type decl =
  | ConstDecl of string * expr
  | VarDecl of string * expr

type stmt =
  | Block of stmt list
  | Empty
  | ExprStmt of expr
  | Assign of string * expr
  | DeclStmt of decl
  | If of expr * stmt * stmt option
  | While of expr * stmt
  | Break
  | Continue
  | Return of expr option

type param = string

type func_def = {
  ret_type: typ;
  name: string;
  params: param list;
  body: stmt list;
}

type comp_unit_item =
  | GlobalDecl of decl
  | FuncDef of func_def
  | FuncDecl of func_def

type program = comp_unit_item list
