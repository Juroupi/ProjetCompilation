(**
   La traduction de IMP vers MIMP rassemble deux objectifs :
   - simplifier les expressions qui peuvent l'être
   - remplacer certaines opérations génériques par des opérations
     spécifiques de MIPS.

   L'essentiel de la traduction est un morphisme direct entre les deux
   syntaxes. On utilise des "smart constructors" comme la fonction [mk_add]
   pour faire à la volée les simplifications qui peuvent être faites.
 *)

open Mimp
open Ops

(* L'appel [mk_add e1 e2] doit renvoyer une expression équivalente à la
   construction [Binop(Add, e1, e2)]. La fonction [mk_add] peut simplifier
   l'expression construite tant que cela préserve le comportement du
   programme en toute circonstantes. L'expression éventuellement simplifiée
   doit donc toujours produire
   -> le même résultat,
   -> ET les mêmes effets de bord éventuels. *)
let mk_add e1 e2 = match e1, e2 with
  | Cst n1, Cst n2 -> 
     Cst(n1+n2)
  | Cst 0, e | e, Cst 0 ->
     e
  | Cst n1, Unop(Addi n2, e) | Unop(Addi n2, e), Cst n1 ->
     Unop(Addi(n1+n2), e)
  | Cst n, e | e, Cst n ->
     Unop(Addi n, e)
  | Unop(Addi n1, e1), Unop(Addi n2, e2) ->
     (* Normalement, sous un Addi, pas d'autre élément simplifiable,
        mais à généraliser. *)
     Unop(Addi(n1+n2), Binop(Add, e1, e2))
  | _ ->
     Binop(Add, e1, e2)

let pow_of_2 i = (Int.logand i (i - 1)) = 0

let rec nbits i =
  if i < 2 then
    0
  else
    1 + nbits (i / 2)

let mk_mul e1 e2 = match e1, e2 with
  | Cst 1, e | e, Cst 1 -> e
  | Cst n1, Cst n2 -> Cst (n1 * n2)
  | Cst n, e when pow_of_2 n -> Unop(Lsli (nbits n), e)
  | e, Cst n when pow_of_2 n -> Unop(Lsli (nbits n), e)
  | _, _ -> Binop(Mul, e1, e2)

let mk_lt e1 e2 = match e1, e2 with
  | Cst n1, Cst n2 -> Bool (n1 < n2)
  | _, _ -> Binop(Lt, e1, e2)

let mk_lsl e1 e2 = match e1, e2 with
  | Cst n1, Cst n2 -> Cst (n1 lsl n2)
  | e, Cst n -> Unop(Lsli n, e)
  | _, _ -> Binop(Lsl, e1, e2)

let mk_lsr e1 e2 = match e1, e2 with
  | Cst n1, Cst n2 -> Cst (n1 lsr n2)
  | e, Cst n -> Unop(Lsri n, e)
  | _, _ -> Binop(Lsr, e1, e2)

let mk_deref n s = function
  | Unop(Addi i, e) -> Unop(Deref(n + i, s), e)
  | e -> Unop(Deref(n, s), e)

(* faire d'autres optimisations pour les autres opérateurs *)

let mk_binop = function
  | Add -> mk_add
  | Mul -> mk_mul
  | Lt -> mk_lt
  | Lsl -> mk_lsl
  | Lsr -> mk_lsr
  | op -> (fun e1 e2 -> Binop(op, e1, e2))

let mk_unop = function
  | Deref(n, s) -> mk_deref n s
  | op -> (fun e -> Unop(op, e))

(* Traduction directe, avec appel de "smart constructors" *)
let rec tr_expr = function
  | Imp.Cst n -> Cst n
  | Imp.Bool b -> Cst (if b then 1 else 0)
  | Imp.Str s -> Str s
  | Imp.Var x -> Var x
  | Imp.Unop(op, e) -> mk_unop op (tr_expr e)
  | Imp.Binop(op, e1, e2) -> mk_binop op (tr_expr e1) (tr_expr e2)
  | Imp.Call(f, args) -> Call(f, List.map tr_expr args)
  | Imp.PCall(e, args) -> PCall(tr_expr e, List.map tr_expr args)
  | Imp.SysCall(code, args) -> SysCall(tr_expr code, List.map tr_expr args)
  | Imp.Addr(id) -> Addr(id)

(* Traduction directe *)
let rec tr_instr = function
  | Imp.Set(x, e) -> Set(x, tr_expr e)
  | Imp.If(e, s1, s2) -> If(tr_expr e, tr_seq s1, tr_seq s2)
  | Imp.While(e, s) -> While(tr_expr e, tr_seq s)
  | Imp.Return e -> Return(tr_expr e)
  | Imp.Expr e -> Expr(tr_expr e)
  | Imp.TailCall(f, args) -> TailCall(f, List.map tr_expr args)
  | Imp.TailPCall(e, args) -> TailPCall(tr_expr e, List.map tr_expr args)
  | Imp.Write(array, n, s, v) ->
    begin match tr_expr array with
    | Unop(Addi i, array) -> Write(array, n + i, s, tr_expr v)
    | array -> Write(array, n, s, tr_expr v)
    end
and tr_seq s =
  List.map tr_instr s

(* Traduction directe *)
let tr_function fdef = {
    name = Imp.(fdef.name);
    params = Imp.(fdef.params);
    locals = Imp.(fdef.locals);
    code = tr_seq Imp.(fdef.code)
  }

(* Traduction directe *)
let tr_program prog ={
    globals = Imp.(prog.globals);
    functions = List.map tr_function Imp.(prog_used_functions prog)
  }
