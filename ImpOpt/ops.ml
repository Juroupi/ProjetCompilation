type unop = 
  | Minus | Not | Addi of int | Deref of int * int
  | Lsli of int | Lsri of int

let pp_unop x = function
  | Minus -> Printf.sprintf "(-%s)" x
  | Not -> Printf.sprintf "(!%s)" x
  | Addi n -> Printf.sprintf "(%s + %d)" x n
  | Deref(n, s) when n mod s = 0 -> Printf.sprintf "%s[%d:%d]" x (n/s) s
  | Deref(n, s) -> Printf.sprintf "(%s + %d)[0:%d]" x n s
  | Lsli n -> Printf.sprintf "(%s << %d)" x n
  | Lsri n -> Printf.sprintf "(%s >> %d)" x n


type binop =
  | Add | Sub | Mul | Div | Rem
  | Eq  | Neq | Lt  | Le  | Gt  | Ge
  | And | Or | Lsl | Lsr

let pp_binop = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Rem -> "%"
  | Eq  -> "=="
  | Neq -> "!="
  | Lt  -> "<"
  | Le  -> "<="
  | Gt  -> ">"
  | Ge  -> ">="
  | And -> "&&"
  | Or  -> "||"
  | Lsl -> "<<"
  | Lsr -> ">>"
