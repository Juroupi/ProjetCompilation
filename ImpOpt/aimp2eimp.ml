(**
   La traduction de AIMP vers EIMP est faite indépendamment pour chaque
   fonction, et contient pour chacune deux tâches principales
   - associer chaque registre virtuel, soit à un registre physique, soit à
     un emplacement dans la pile,
   - lorsqu'une instruction prend ses opérandes ou place son résultat dans la
     pile, ajout d'une instruction de lecture ou d'écriture en mémoire.

   Convention : les valeurs qui viennent de la pile ou doivent y être stockées
   transitent par l'un des deux registres $t0 et $t1, dont on réserve l'usage
   à ce seul cas.
 *)

open Eimp
open Register_allocation

(* On donne des noms aux registres temporaires utilisés pour les échanges
   avec la pile, selon que l'on parle du résultat d'une instruction, de son
   premier opérande, ou de son deuxième opérande. *)
let dst_reg = "$t0"
let op1_reg = "$t0"
let op2_reg = "$t1"

(* Fonction principale, de traduction d'une définition de fonction *)
let tr_fdef fdef =

  let nparams = List.length Aimp.(fdef.params) in

  (* Première tâche : allocation de registres, telle que définie dans le
     module Register_allocation *)
  let alloc, num_stacked, num_actual_t = allocation fdef in

  (* Tester si deux registres virtuels ont le même registre réel *)
  let same_reg v1 v2 =
    match Graph.VMap.find_opt v1 alloc, Graph.VMap.find_opt v2 alloc with
    | Some (Actual r1), Some (Actual r2) when r1 = r2 -> true
    | Some (Stacked i1), Some (Stacked i2) when i1 = i2 -> true
    | _ -> false
  in
  
  (* Renvoie l'éventuelle instruction nécessaire pour sauvegarder un résultat
     ou aller chercher un opérande dans la pile, en fonction de la réalisation
     du registre virtuel correspondant. *)
  let save vr =
    match Graph.VMap.find vr alloc with
    | Actual r  -> Nop
    | Stacked i -> Instr(Write(Stack i, dst_reg))
  in

  let load op vr =
    match Graph.VMap.find vr alloc with
    | Actual r  -> Nop
    | Stacked i -> Instr(Read(op, Stack i))
  in
  let load1 = load op1_reg in
  let load2 = load op2_reg in
  
  (* Renvoie le registre réel où aller placer le résultat d'une instruction ou
     aller chercher un opérande, selon que le registre virtuel correspondant a
     été réalisé par un registre physique ou dans la pile. Dans ce dernier cas,
     le registre sera l'un des deux registres dédiés $t0 ou $t1. *)
  let reg op vr =
    match Graph.VMap.find vr alloc with
    | Actual r  -> r
    | Stacked i -> op
  in

  let dst = reg dst_reg in
  let op1 = reg op1_reg in
  let op2 = reg op2_reg in

  let find_param x params =
    let rec find_param x params i =
      match params with
      | [] -> None
      | param :: _ when param = x -> Some i
      | _ :: params -> find_param x params (i+1)
    in find_param x params 0
  in

  let mem_access x =
    match find_param x fdef.params with
    | None -> Global x
    | Some i -> Stack (-i - 1)
  in

  (* Fonction de traduction des instructions. Chaque registre virtuel est
     remplacé par un registre réel, en ajoutant une instruction de lecture
     ou une instruction d'écriture lorsqu'un registre virtuel est réalisé
     par un emplacement de pile. *)
  let rec tr_instr = function

    | Aimp.Read(vrd, x) ->
      Instr(Read(dst vrd, mem_access x))
      @@ save vrd

    | Aimp.Write(x, vr) ->
      load1 vr
      @@ Instr(Write(mem_access x, op1 vr))

    | Aimp.Move(vrd, vr) when same_reg vrd vr ->
      Nop
    | Aimp.Move(vrd, vr) ->
      let dst = dst vrd in
      let op1 = op1 vr in
      load1 vr
      @@ (if dst <> op1 then Instr(Move(dst, op1)) else Nop)
      @@ save vrd

    | Aimp.Push vr ->
      load1 vr
      @@ Instr(Push (op1 vr))

    | Aimp.Pop n ->
      Instr(Pop n)

    | Aimp.Cst(vrd, n) ->
      Instr(Cst(dst vrd, n))
      @@ save vrd

    | Aimp.Unop(vrd, op, vr) ->
      load1 vr
      @@ Instr(Unop(dst vrd, op, op1 vr))
      @@ save vrd

    | Aimp.Binop(vrd, op, vr1, vr2) ->
      load1 vr1 @@ load2 vr2
      @@ Instr(Binop(dst vrd, op, op1 vr1, op2 vr2))
      @@ save vrd

    | Aimp.Call(f, n) ->
      Instr(Call(f, n))

    | Aimp.If(vr, s1, s2) ->
      load1 vr
      @@ Instr(If(op1 vr, tr_seq s1, tr_seq s2))

    | Aimp.While(s1, vr, s2) ->
      Instr(While(tr_seq s1 @@ load1 vr, op1 vr, tr_seq s2))

    | Aimp.Return ->
      Instr(Return)

    | Aimp.SysCall ->
      Instr(SysCall)

    | Aimp.TailCall(f, n) ->
      Instr(TailCall(f, n))

  and tr_seq = function
    | Aimp.Seq(s1, s2) -> Seq(tr_seq s1, tr_seq s2)
    | Aimp.Instr(_, i) -> tr_instr i
    | Aimp.Nop         -> Nop
  in

  (* Traduction presque directe
     La liste des paramètres est résumée à sa taille, et la liste des
     variables locales au nombre d'emplacements utilisés dans la pile. *)
  {
    name = Aimp.(fdef.name);
    params = nparams;
    locals = num_stacked;
    temps = num_actual_t;
    code = tr_seq Aimp.(fdef.code);
  }

(* Traduction directe *)
let tr_prog prog = {
  globals = Aimp.(prog.globals);
  functions = List.map tr_fdef Aimp.(prog.functions);
}
