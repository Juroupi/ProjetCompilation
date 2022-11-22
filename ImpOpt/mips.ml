open Format

type register = string
let v0 : register = "$v0"
let v1 : register = "$v1"
let a0 : register = "$a0"
let a1 : register = "$a1"
let a2 : register = "$a2"
let a3 : register = "$a3"
let t0 : register = "$t0"
let t1 : register = "$t1"
let t2 : register = "$t2"
let t3 : register = "$t3"
let t4 : register = "$t4"
let t5 : register = "$t5"
let t6 : register = "$t6"
let t7 : register = "$t7"
let t8 : register = "$t8"
let t9 : register = "$t9"
let s0 : register = "$s0"
let s1 : register = "$s1"
let s2 : register = "$s2"
let s3 : register = "$s3"
let s4 : register = "$s4"
let s5 : register = "$s5"
let s6 : register = "$s6"
let s7 : register = "$s7"
let ra : register = "$ra"
let sp : register = "$sp"
let fp : register = "$fp"
let gp : register = "$gp"
let zero : register = "$zero"

let t n : register = Printf.sprintf "$t%d" n
let s n : register = Printf.sprintf "$s%d" n

let (~$) r = r

type label = string

type 'a asm =
  | Nop
  | S of string
  | C of 'a asm * 'a asm

type text = [`text ] asm
type data = [`data ] asm

let buf = Buffer.create 17
let fmt = formatter_of_buffer buf
let ins x =
  Buffer.add_char buf '\t';
  kfprintf (fun fmt ->
      fprintf fmt "\n";
      pp_print_flush fmt ();
      let s = Buffer.contents buf in
      Buffer.clear buf;
      S s
    ) fmt x

let pr_list fmt pr l =
  match l with
    [] -> ()
  | [ i ] -> pr fmt i
  | i :: ll -> pr fmt i;
      List.iter (fun i -> fprintf fmt ", %a" pr i) ll

let pr_ilist fmt l =
  pr_list fmt (fun fmt i -> fprintf fmt "%i" i) l
    
let add  r1 r2 r3 = ins "add %s, %s, %s"  r1 r2 r3
let addi r1 r2 i  = ins "addi %s, %s, %d" r1 r2 i
let sub  r1 r2 r3 = ins "sub %s, %s, %s"  r1 r2 r3
let subi r1 r2 i  = ins "subi %s, %s, %d" r1 r2 i
let mul  r1 r2 r3 = ins "mul %s, %s, %s"  r1 r2 r3
let muli r1 r2 i  = ins "mul %s, %s, %d"  r1 r2 i
let div  r1 r2 r3 = ins "div %s, %s, %s"  r1 r2 r3
let rem  r1 r2 r3 = ins "rem %s, %s, %s"  r1 r2 r3

let and_ r1 r2 r3 = ins "and %s, %s, %s"  r1 r2 r3
let or_  r1 r2 r3 = ins "or %s, %s, %s"   r1 r2 r3
let not_ r1 r2    = ins "not %s, %s"      r1 r2
let lnot r1 r2    = ins "seq %s, %s, $zero" r1 r2
let neg  r1 r2    = ins "neg %s, %s"      r1 r2

let sll  r1 r2 n  = ins "sll %s, %s, %d"   r1 r2 n
let srl  r1 r2 n  = ins "srl %s, %s, %d"   r1 r2 n
let sllv r1 r2 r3 = ins "sllv %s, %s, %s"  r1 r2 r3
let srlv r1 r2 r3 = ins "srlv %s, %s, %s"  r1 r2 r3
  
let seq  r1 r2 r3 = ins "seq %s, %s, %s"  r1 r2 r3
let sne  r1 r2 r3 = ins "sne %s, %s, %s"  r1 r2 r3
let slt  r1 r2 r3 = ins "slt %s, %s, %s"  r1 r2 r3
let sle  r1 r2 r3 = ins "sle %s, %s, %s"  r1 r2 r3
let sgt  r1 r2 r3 = ins "sgt %s, %s, %s"  r1 r2 r3
let sge  r1 r2 r3 = ins "sge %s, %s, %s"  r1 r2 r3
  
let b (z: label)  = ins "b %s" z
let beq x y (z : label) = ins "beq %s, %s, %s" x y z
let beqi x y (z : label) = ins "beq %s, %d, %s" x y z
let bne x y (z : label) = ins "bne %s, %s, %s" x y z
let bnei x y (z : label) = ins "bne %s, %d, %s" x y z
let bge x y (z : label) = ins "bge %s, %s, %s" x y z
let bgei x y (z : label) = ins "bge %s, %d, %s" x y z
let bgt x y (z : label) = ins "bgt %s, %s, %s" x y z
let bgti x y (z : label) = ins "bgt %s, %d, %s" x y z
let ble x y (z : label) = ins "ble %s, %s, %s" x y z
let blei x y (z : label) = ins "ble %s, %d, %s" x y z
let blt x y (z : label) = ins "blt %s, %s, %s" x y z
let blti x y (z : label) = ins "blt %s, %d, %s" x y z
let beqz x (z : label)  = ins "beqz %s, %s" x z
let bnez x (z : label)  = ins "bnez %s, %s" x z
let bgez x (z : label)  = ins "bgez %s, %s" x z
let bgtz x (z : label)  = ins "bgtz %s, %s" x z
let blez x (z : label)  = ins "blez %s, %s" x z
let bltz x (z : label)  = ins "bltz %s, %s" x z

let j  (z : label) = ins "j %s" z
let jal  (z : label) = ins "jal %s" z
let jalr r = ins "jalr %s" r
let jr   r = ins "jr %s" r

let li   r i   = ins "li %s, %i"       r i
let la   x (a : label) = ins "la %s, %s" x a
let lbu  x i r = ins "lbu %s, %i(%s)"  x i r
let lw   x i r = ins "lw %s, %i(%s)"   x i r
let sw   x i r = ins "sw %s, %i(%s)"   x i r
let lb   x i r = ins "lb %s, %i(%s)"   x i r
let sb   x i r = ins "sb %s, %i(%s)"   x i r
let lh   x i r = ins "lh %s, %i(%s)"   x i r
let sh   x i r = ins "sh %s, %i(%s)"   x i r
let lvar x (v : label) = ins "lw %s, %s" x v
let svar x (v : label) = ins "sw %s, %s" x v

let larr s =
  match s with
  | 1 -> lb | 2 -> lh | 4 -> lw
  | _ -> failwith "taille de donnee non supportee"
  
let sarr s =
  match s with
  | 1 -> sb | 2 -> sh | 4 -> sw
  | _ -> failwith "taille de donnee non supportee"
  
let move r1 r2 = ins "move %s, %s"     r1 r2
  
let nop = Nop
let label (s: label) = S ( s ^ ":\n" )
let syscall = S "\tsyscall\n"
let comment s = S ("# " ^ s ^ "\n")
let newline = S ("\n")
let asciiz s = ins ".asciiz \"%s\"" s
let dword l = ins ".word %a" pr_ilist l

let (@@) x y = C (x, y)

let store r i = sw r (-i*4) sp (* ranger un registre au dessus de la pile *)
let restore r i = lw r (-i*4) sp (* restaurer un registre depuis la pile *)

let reserve n = if n > 0 then subi sp sp (n*4) else nop (* agrandir la pile *)
let pop n = if n > 0 then addi sp sp (4*n) else nop (* réduire la taille de la pile *)

let push r = store r 0 @@ reserve 1 (* ajouter un registre en haut de la pile *)

let local_shift calls i = if i < 0 then (-i*4) else (-i*4-(if calls > 0 then 8 else 0))
let write_local calls r i = sw r (local_shift calls i) (if calls > 0 then fp else sp)
let read_local calls r i = lw r (local_shift calls i) (if calls > 0 then fp else sp)

let map_live_out f live_out =
  let rec map_live_out n = function
  | [] -> nop
  | r :: live_out ->
    (if r.[1] = 't' then f (s n) r else nop) @@ map_live_out (n+1) live_out
  in map_live_out 0 live_out
let save_live_out = map_live_out (fun s t -> move s t)
let restore_live_out = map_live_out (fun s t -> move t s)

let push_list l =
  let seq, n = List.fold_left (fun (seq, i) r -> seq @@ store r i, i + 1) (nop, 0) l in
  seq @@ reserve n
let pop_list l =
  let seq, n = List.fold_left (fun (seq, i) r -> seq @@ restore r i, i + 1) (nop, 0) l in
  pop n @@ seq

let saved_list n = List.init n (fun i -> s i)
let push_saved n = push_list (saved_list n)
let pop_saved n = pop_list (saved_list n)

let init_fun locals saved calls =
  if calls > 0 then
    store fp 0 @@ store ra 1 @@ move fp sp @@ reserve (locals+2) @@ push_saved saved
  else
    reserve locals

let end_fun params locals saved calls =
  if calls > 0 then
    pop_saved saved @@ pop (locals+2) @@ restore fp 0 @@ restore ra 1 @@ pop params
  else
    pop locals @@ pop params

let return = jr ra

let tailcall fname src_params src_locals src_saved src_calls dst_params =
  let frame = src_params + 2 + src_locals + src_saved in
  let rec move_params n =
    if n = 0 then 
      nop 
    else
      move_params (n-1)
      @@ lw t0 (-frame*4) sp
      @@ push t0
  in
  pop dst_params
  @@ end_fun src_params src_locals src_saved src_calls
  @@ move_params dst_params
  @@ j fname

type program = { text : [ `text ] asm;
                 data : [ `data ] asm; }

let rec pr_asm fmt a =
  match a with
  | Nop -> ()
  | S s -> fprintf fmt "%s" s
  | C (a1, a2) ->
      let () = pr_asm fmt a1 in
      pr_asm fmt a2

let print_program fmt p =
  fprintf fmt ".text\n";
  pr_asm fmt p.text;
  fprintf fmt ".data\n";
  pr_asm fmt p.data
