(**
   Explicit IMP.
   Identique à AIMP à un détail près : il n'y a plus de registre virtuels,
   mais seulement des registres physiques, ou des valeurs stockées dans
   la pile.
 *)
open Ops

type reg   = string

type mem_access =
  | Global of string
  | Stack  of int
  | Array  of reg * int * int

type instruction =
  | Read    of reg * mem_access
  | Write   of mem_access * reg
  | Move    of reg * reg
  | Push    of reg
  | Pop     of int
  | Cst     of reg * int
  | Unop    of reg * unop * reg
  | Binop   of reg * binop * reg * reg
  | Call    of string * int * reg list
  | If      of reg * sequence * sequence
  | While   of sequence * reg * sequence
  | Return
  | SysCall
  | TailCall of string * int
and sequence =
  | Seq     of sequence * sequence
  | Instr   of instruction
  | Nop

let (@@) i1 i2 = if i1 = Nop && i2 = Nop then Nop else Seq(i1, i2)
let rec seq = function
  | []   -> Nop
  | i::l -> Instr i @@ seq l

type function_def = {
  name: string;
  params: int; (* string list; *)
  locals: int; (* string list; *)
  temps: int;
  calls: int;
  returns: int;
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

let pp_mem_access = function
  | Global x       -> sprintf "*%s" x
  | Stack i        -> sprintf "*{%i}" i
  | Array(a, n, s) -> sprintf "%s[%d:%d]" a n s

let pp_program prog out_channel =
  let print s = fprintf out_channel s in
  let margin = ref 0 in
  let print_margin () = for i=1 to !margin do print "  " done in

  let rec pp_instr = function
    | Read(vrd, a) ->
       print "%s <- %s;" vrd (pp_mem_access a)
    | Write(a, vr) ->
       print "%s <- %s;" (pp_mem_access a) vr
    | Move(vrd, vr) ->
       print "%s <- %s;" vrd vr
    | Cst(vrd, n) ->
       print "%s <- %i;" vrd n
    | Unop(vrd, op, vr) ->
       print "%s <- %s;" vrd (pp_unop vr op)
    | Binop(vrd, op, vr1, vr2) -> 
       print "%s <- %s %s %s;" vrd vr1 (pp_binop op) vr2
    | Call(f, n, _) ->
       print "call %s (%i);" f n
    | Push vr ->
       print "push %s;" vr
    | Pop n ->
       print "pop %i;" n
    | If(vr, s1, s2) ->
       print "if (%s) {\n" vr;
       incr margin; pp_seq s1; decr margin;
       print_margin(); print "} else {\n";
       incr margin; pp_seq s2; decr margin;
       print_margin(); print "}"
    | While(s1, vr, s2) ->
       print "while (\n";
       incr margin; pp_seq s1;
       print_margin(); print "%s\n" vr;
       decr margin;
       print_margin(); print ") {\n";
       incr margin; pp_seq s2; decr margin;
       print_margin(); print "}"
    | Return ->
       print "return;"
    | SysCall ->
       print "syscall;"
    | TailCall(f, n) ->
       print "tailcall %s (%i);" f n
  and pp_seq = function
    | Nop -> ()
    | Seq(s1, s2) -> pp_seq s1; pp_seq s2
    | Instr i -> 
       print_margin(); pp_instr i; print "\n"
  in

  let pp_var x = print_margin(); print "var %s;\n" x in
  let rec pp_vars = function
    | [] -> ()
    | [x] -> pp_var x; print "\n";
    | x::vars -> pp_var x; pp_vars vars
  in

  let pp_function fdef =
    print "function %s {\n" fdef.name;
    incr margin;
    print "\t// %i params\n" fdef.params;
    print "\t// %i locals\n" fdef.locals;
    pp_seq fdef.code;
    decr margin;
    print "}\n\n"
  in
  
  pp_vars prog.globals;
  List.iter pp_function prog.functions;
  
