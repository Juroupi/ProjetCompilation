type unop = Minus | Not | Addi of int
type binop =
  | Add | Sub | Mul | Div | Rem | Lsl | Lsr
  | Eq  | Neq | Lt  | Le  | Gt  | Ge
  | And | Or

let pp_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Rem -> "%"
  | Lsl -> "<<"
  | Lsr -> ">>"
  | Eq  -> "=="
  | Neq -> "!="
  | Lt  -> "<"
  | Le  -> "<="
  | Gt  -> ">"
  | Ge  -> ">="
  | And -> "&&"
  | Or  -> "||"
