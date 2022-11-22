(**
   MIMP.
   Variante mineure de la syntaxe abstraite IMP qui intègre certaines
   opérations spécifiques de MIPS.

   Seule présente ici : addi, représentée comme un opérateur unaire.
   Vous pouvez en ajouter d'autres.
 *)

open Ops

type expression =
  | Cst     of int
  | Bool    of bool
  | Str     of string
  | Var     of string
  | Unop    of unop * expression
  | Binop   of binop * expression * expression
  | Call    of string * expression list
  | SysCall of expression * expression list
  | Addr    of string

type instruction =
  | Set      of string * expression
  | If       of expression * sequence * sequence
  | While    of expression * sequence
  | Return   of expression
  | Expr     of expression
  | TailCall of string * expression list
  | Write    of expression * int * int * expression
and sequence = instruction list

type function_def = {
    name: string;
    params: string list;
    locals: string list;
    code: sequence;
  }

type program = {
    globals: string list;
    functions: function_def list;
  }


(**
   Pretty-printer
 *)

open Printf

let rec pp_params = function
  | [] -> ""
  | [x] -> x
  | x::params -> sprintf "%s, %s" x (pp_params params)

let rec pp_expr = function
  | Cst n -> string_of_int n
  | Bool b -> if b then "true" else "false"
  | Str s -> "\"" ^ s ^ "\""
  | Var x -> x
  | Unop(op, e) -> pp_unop (pp_expr e) op
  | Binop(op, e1, e2) -> 
     sprintf "(%s %s %s)" (pp_expr e1) (pp_binop op) (pp_expr e2)
  | Call(f, args) ->
     sprintf "%s(%s)" f (pp_args args)
  | SysCall(code, args) ->
     sprintf "syscall(%s)(%s)" (pp_expr code) (pp_args args)
  | Addr(id) ->
     sprintf "(&%s)" id
and pp_args = function
  | [] -> ""
  | [a] -> pp_expr a
  | a::args -> sprintf "%s, %s" (pp_expr a) (pp_args args)

let pp_program prog out_channel =
  let print s = fprintf out_channel s in
  let margin = ref 0 in
  let print_margin () = for i=1 to !margin do print "  " done in

  let rec pp_instr = function
    | Set(x, e) ->
       print "%s = %s;" x (pp_expr e)
    | If(e, s1, s2) ->
       print "if (%s) {\n" (pp_expr e);
       incr margin; pp_seq s1; decr margin;
       print_margin(); print "} else {\n";
       incr margin; pp_seq s2; decr margin;
       print_margin(); print "}"
    | While(e, s) ->
       print "while (%s) {\n" (pp_expr e);
       incr margin; pp_seq s; decr margin;
       print_margin(); print "}"
    | Return e ->
       print "return(%s);" (pp_expr e)
    | Expr e ->
       print "%s;" (pp_expr e)
    | TailCall(f, args) ->
       print "return %s(%s);" f (pp_args args)
    | Write(array, index, size, v) ->
       print "%s[%d:%d] = %s;" (pp_expr array) index size (pp_expr v)
  and pp_seq = function
    | [] -> ()
    | i::seq -> print_margin(); pp_instr i; print "\n"; pp_seq seq
  in

  let pp_var x = print_margin(); print "var %s;\n" x in
  let rec pp_vars = function
    | [] -> ()
    | [x] -> pp_var x; print "\n";
    | x::vars -> pp_var x; pp_vars vars
  in

  let pp_function fdef =
    print "function %s(%s) {\n" fdef.name (pp_params fdef.params);
    incr margin;
    pp_vars fdef.locals;
    pp_seq fdef.code;
    decr margin;
    print "}\n\n"
  in
  
  pp_vars prog.globals;
  List.iter pp_function prog.functions;
  
