(**
	La traduction de MIMP vers AIMP réalise deux tâches principales
	- explosion des expressions en séquences d'instructions atomiques,
	  en introduisant au passage des registres virtuels pour stocker les
	  résultats intermédiaires des calcules
	- implémentation des conventions de passage des paramètres et résultats
	  des fonctions, ainsi que des conventions de sauvegarde des registres
	  physiques

	Conventions à réaliser :
	- pour la transmission des résultats : registre $v0
	- pour le passage des paramètres, AU CHOIX
	  * soit tout sur la pile (premier paramètre au sommets, les suivante
		 en progressant vers l'intérieur de la pile)
	  * soit les quatre premiers dans les $ai, puis les suivants sur la
		 pile
	- lors d'un appel de fonction, l'appelant doit gérer la sauvegarde des
	  registres $ti, $ai et $v0, et l'appelé doit gérer la sauvegarde des
	  registres $si

	La création des registres virtuels est faite indépendamment pour chaque
	fonction. Dans une fonction donnée, les registres virtuels sont vus
	comme des variables locales.
 *)

open Aimp

(* Fonction principale, de traduction d'une définition de fonction *)
let tr_fdef strings fdef =

	let stacked_params =
		match Mimp.(fdef.params) with
		| _ :: _ :: _ :: _ :: params -> params
		| _ -> []
	in
	let args_length args = max 0 (List.length args - 4) in

	(* Liste des registres virtuels. Elle est initialisée avec les variables
		locales et sera étendue à chaque création d'un nouveau registre
		virtuel. *)
	let arg i = Printf.sprintf "$a%i" i in
	let varg i = Printf.sprintf "#a%i" i in

	let nparams = List.length Mimp.(fdef.params) in
	let nvargs = min 4 nparams in

	let varg_regs = List.init nvargs varg in

	let vregs = ref Mimp.(varg_regs @ fdef.locals) in
	(* Fonction de génération de nouveaux registres virtuels.
		Renvoie le nouveau nom, et étend la liste. *)
	let vreg_counter = ref 0 in
	let new_vreg () =
		let name = Printf.sprintf "#%i" !vreg_counter in
		vregs := name :: !vregs;
		incr vreg_counter;
		name
	in

	let arg_id name =
		let rec arg_id i args name =
			match args with
			| _ when i >= nvargs -> 4
			| arg :: _ when arg = name -> i
			| _ :: args -> arg_id (i+1) args name
			| _ -> 4
		in arg_id 0 fdef.params name
	in

	let rec move_regs d s i =
		if i > 0 then
			move_regs d s (i-1) ++ Move(d (i-1), s (i-1))
		else
			Nop
	in

	(* Génération d'un label pour une chaine de caractères *)
	let str_counter = ref 0 in
	let new_str_name str =
		match Hashtbl.find_opt strings str with
		| Some name -> name
		| None ->
			let name = Printf.sprintf "_string_%s_%i" fdef.name !str_counter in
			Hashtbl.add strings name str;
			incr str_counter;
			name
	in

	(* Fonction de traduction des expressions.
		Renvoie une paire (r, s) d'une séquence s et du nom r du registre
		virtuel contenant la valeur de l'expression. *)
	let rec tr_expr = function
		| Mimp.Cst n ->
			let r = new_vreg() in r, Nop ++ Cst(r, n)
		| Mimp.Bool b -> 
			let r = new_vreg() in 
			let n = if b then 1 else 0 in
			r, Nop ++ Cst(r, n)
		| Mimp.Str str ->
			let r = new_vreg() in
			let name = new_str_name str in
			r, Nop ++ Addr(r, name)
		| Mimp.Var x ->
			(* Il faut distinguer ici entre variables locales, paramètres et
				variables globales. *)
			if List.mem x Mimp.(fdef.locals) then
				x, Nop
			else
				let arg_id = arg_id x in
				if arg_id < nvargs then
					varg arg_id, Nop
				else
					let r = new_vreg() in
					r, Nop ++ (Get (r, x))
		| Mimp.Unop(Deref(n, s), e) ->
			let r1, s1 = tr_expr e in
			let r = new_vreg() in
			r, s1 ++ Read(r, r1, n, s)
		| Mimp.Unop(op, e) ->
			let r1, s1 = tr_expr e in
			let r = new_vreg() in
			r, s1 ++ Unop(r, op, r1)
		| Mimp.Binop(op, e1, e2) ->
			let r1, s1 = tr_expr e1 in
			let r2, s2 = tr_expr e2 in
			let r = new_vreg() in
			r, s1 @@ s2 ++ Binop(r, op, r1, r2)
		| Mimp.Call(f, args) ->
			(* Il faut réaliser ici la convention d'appel : passer les arguments
			   de la bonne manière, et renvoyer le résultat dans $v0. *)
			let res = new_vreg() in
			res, (tr_args args) ++ (Call (f, args_length args)) ++ (Move(res, "$v0"))
		| Mimp.PCall(e, args) ->
			let res = new_vreg() in
			let rptr, sptr = tr_expr e in
			res, sptr @@ (tr_args args) ++ (PCall (rptr, args_length args)) ++ (Move(res, "$v0"))
		| Mimp.SysCall(code, args) ->
			let r, s = tr_expr code in
			let res = new_vreg () in
			res, s ++ (Move("$v0", r)) @@ (tr_syscall_args args) ++ SysCall ++ (Move(res, "$v0"))
		| Mimp.Addr(id) ->
			let r = new_vreg() in
			r, Nop ++ Addr(r, id)
	
	and tr_syscall_args args =
		let rec tr_syscall_args i args = match i, args with
		| _, [] -> Nop
		| 4, _ -> failwith "trop de parametres pour l'appel systeme"
		| i, a :: args ->
			let r, s = tr_expr a in
			(tr_syscall_args (i+1) args) @@ s ++ (Move(Printf.sprintf "$a%i" i, r))
		in tr_syscall_args 0 args

	and tr_args args =
		let rec tr_args i = function
		| [] -> Nop
		| a :: args -> 
			let r, s = tr_expr a in
			tr_args (i+1) args @@ s ++
				if i < 4 then
					(Move(arg i, r))
				else
					(Push r)
		in tr_args 0 args
	in 

	let rec tr_instr = function
		| Mimp.Set(x, e) ->
			let r, s = tr_expr e in
			if List.mem x Mimp.(fdef.locals) then
				s ++ (Move (x, r))
			else
				let arg_id = arg_id x in
				if arg_id < nvargs then
					s ++ (Move (varg arg_id, r))
				else
					s ++ (Set (x, r))
		| Mimp.Write(e1, n, s, e2) ->
			let r1, s1 = tr_expr e1 in
			let r2, s2 = tr_expr e2 in
			s1 @@ s2 ++ (Write (r1, n, s, r2))
		| Mimp.If(e, s1, s2) ->
			let r, s = tr_expr e in
			s ++ (If (r, tr_seq s1, tr_seq s2))	  
		| Mimp.While(e, s) ->
			let r, s1 = tr_expr e in
			Nop ++ (While (s1, r, tr_seq s))		  
		| Mimp.Return e ->
			(* Le résultat renvoyé doit être placé dans $v0. *)
			let r, s = tr_expr e in
			s ++ (Move ("$v0", r)) ++ Return
		| Mimp.Expr e ->
			let r, s = tr_expr e in
			s
		| Mimp.TailCall(f, args) ->
			(tr_args args) ++ (TailCall (f, args_length args))
		| Mimp.TailPCall(e, args) ->
			let rptr, sptr = tr_expr e in
			sptr @@ (tr_args args) ++ (TailPCall (rptr, args_length args))

	and tr_seq = function
		| []	  -> Nop
		| i :: s -> tr_instr i @@ tr_seq s
	in 

	let code =
		(* À ce code, il faut ajouter la sauvegarde et la restauration
			des registres virtuels callee_saved. *)
		move_regs varg arg nvargs @@ tr_seq Mimp.(fdef.code) 
	in
{
	name = Mimp.(fdef.name);
	params = stacked_params;
	locals = !vregs;
	code = code
}

(* Traduction directe *)
let tr_prog p =
	let strings : (string, string) Hashtbl.t = Hashtbl.create 16 in
	let functions = List.map (tr_fdef strings) Mimp.(p.functions) in
	{
		strings = Hashtbl.fold (fun name str l -> (name, str) :: l) strings [];
		globals = Mimp.(p.globals);
		functions = functions;
	}
