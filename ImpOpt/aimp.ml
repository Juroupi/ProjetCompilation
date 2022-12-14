(**
   Atomic IMP.
   Langage intermédiaire dans lequel les expressions ont été décomposées
   en séquences d'instructions atomiques.

   Tous les résultats intermédiaires du calcul d'une expression sont
   stockés dans des variables locales introduites à la volée.
   On appelle ces variables des "registres virtuels", et on s'autorise à
   en créer à volonté.

   On suppose que les programmes écrits dans ce langage respectent les
   conventions d'appels (passage des arguments sur la pile et/ou dans
   les registres dédiés, transmission du résultat dans $v0). Pour cela,
   ce langage peut manipuler directement les registres physiques de MIPS
   en plus des registres virtuels.
 *)
open Ops

(* Un registre virtuel est, comme une variable, identifié par une chaîne *)
type vreg = string

(* Il n'y a plus d'expressions. On accède au résultat d'un calcul par un
   registre virtuel. Une instruction qui "produit" un résultat le stocke
   dans un registre virtuel, qui est systématiquement le premier des
   paramètres de l'instruction. *)
type instruction =
  | SysCall
  (* Lecture de la valeur d'une variable ou d'un paramètre *)
  | Get       of vreg * string
  | Read      of vreg * vreg * int * int
  (* Mutation d'une variable *)
  | Set       of string * vreg
  | Write     of vreg * int * int * vreg
  (* Transfert entre deux registres virtuels *)
  | Move      of vreg * vreg
  (* Chargement d'une valeur constante *)
  | Cst       of vreg * int
  (* Chargement d'une adresse *)
  | Addr      of vreg * string
  (* Opérations arithmétiques *)
  | Unop      of vreg * unop * vreg
  | Binop     of vreg * binop * vreg * vreg
  (* Appel de fonction. On ne donne pas de registre virtuel pour le
     résultat car, par convention, le résultat doit être placé dans $v0.
     On ne donne pas non plus de paramètres car, par convention, ils doivent
     être passés par la pile et/ou des registres dédiés. On fournit
     simplement le nombre de paramètre, qui pourra servir lors d'une
     étape ultérieure. *)
  | Call      of string * int
  | PCall     of vreg * int
  (* Instructions supplémentaires pour réaliser les conventions d'appel :
     ajout d'un élément au sommet de la pile, et retrait de n éléments de
     la pile. *)
  | Push      of vreg
  | Pop       of int
  (* Fin d'exécution d'une fonction. La valeur renvoyée doit être placée
     dans $v0 avant d'exécuter cette instruction. *)
  | Return
  | TailCall  of string * int
  | TailPCall of vreg * int
  (* Les structures de contrôles sont toujours présentes.
     Attention, le test est fait sur un registre virtuel. *)
  | If        of vreg * sequence * sequence
  | While     of sequence * vreg * sequence
(* Pour éviter un surcoût lié aux concaténations de code, on donne aux
   séquences d'instruction une structure arborescente. Pour les besoins
   de la suite, chaque instruction est numérotée. *)
and sequence =
  | Seq     of sequence * sequence
  | Instr   of int * instruction
  | Nop

(* Création d'une instruction dotée d'un numéro unique. *)
let lift =
  let counter = ref 0 in
  fun i -> incr counter; Instr(!counter, i)

(* Raccourcis pour la construction de séquences :
    s1 @@ s2  concatène s1 et s2
    s  ++ i   ajoute l'instruction i à la fin de la séquence s
 *)
let (@@) s1 s2 = Seq(s1, s2)
let (++) s  i  = Seq(s, lift i)


type function_def = {
   name: string;
   params: string list;
   locals: string list;
   code: sequence;
}

type program = {
   strings: (string * string) list;
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

let pp_program prog out_channel =
  let print s = fprintf out_channel s in
  let margin = ref 0 in
  let print_margin () = for i=1 to !margin do print "  " done in


  let pp_var x = print_margin(); print "var %s;\n" x in
  let rec pp_vars = function
    | [] -> ()
    | [x] -> pp_var x; print "\n";
    | x::vars -> pp_var x; pp_vars vars
  in

  let pp_function fdef =
    let rec pp_instr = function
      | Get(vrd, x) ->
         print "%s <- *%s;" vrd x
      | Read(vrd, array, index, size) ->
         print "%s = (%s)[%d:%d];" vrd array index size
      | Set(x, vr) ->
         print "*%s <- %s;" x vr
      | Write(array, index, size, vr) ->
         print "(%s)[%d:%d] = %s;" array index size vr
      | Move(vrd, vr) ->
         print "%s <- %s;" vrd vr
      | Cst(vrd, n) ->
         print "%s <- %i;" vrd n
      | Addr(vrd, id) ->
         print "%s <- &%s;" vrd id
      | Unop(vrd, op, vr) ->
         print "%s <- %s;" vrd (pp_unop vr op)
      | Binop(vrd, op, vr1, vr2) -> 
         print "%s <- %s %s %s;" vrd vr1 (pp_binop op) vr2
      | Call(f, n) ->
         print "call %s (%i);" f n
      | PCall(vr, n) ->
         print "pcall %s (%i);" vr n
      | SysCall ->
         print "syscall;"
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
      | TailCall(f, n) ->
         print "tailcall %s (%i);" f n
      | TailPCall(vr, n) ->
         print "tailpcall %s (%i);" vr n
    and pp_seq = function
      | Nop -> ()
      | Seq(s1, s2) -> pp_seq s1; pp_seq s2
      | Instr(n, i) -> 
         print_margin(); pp_instr i;
         print " {%i}\n" n
    in

    print "function %s(%s) {\n" fdef.name (pp_params fdef.params);
    incr margin;
    pp_vars fdef.locals;
    pp_seq fdef.code;
    decr margin;
    print "}\n\n"
  in
  
  pp_vars prog.globals;
  List.iter pp_function prog.functions;
  
