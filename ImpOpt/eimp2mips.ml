(**
   La traduction de EIMP vers MIPS est immédiate pour la plupart des
   instructions "de base". Il reste à traiter deux choses principales :
   - traduire les instructions de contrôle if et while à l'aide de sauts,
   - réaliser les convention d'appel pour les fonction, côté appelé.

   Convention d'appel, pour la fonction appelée :
   - Au début de l'appel, il faut stocker sur la pile
     * la valeur courante du pointeur $fp (qui contient le pointeur
       de base du tableau d'activation de la fonction appelante), et
     * la valeur courante de $ra.
     Il faut ensuite redéfinir le registre $fp pour qu'il représente cette
     fois le pointeur de base du tableau d'activation de la fonction appelée,
     et décaler $sp de sorte à réserver l'espace nécessaire aux variables
     locales.
   - À la fin de l'appel, il faut s'assurer que le résultat est stocké dans
     le registre $v0, remettre à jour $sp pour libérer l'espace de pile
     utilisé par le tableau d'activation de la fonction, puis restaurer
     les valeurs de $ra et $fp qui avaient été sauvegardées avant de rendre
     la main.
 *)

open Eimp
open Mips
open Ops

(* Fonction de création de nouvelles étiquettes, à utiliser notamment pour
   traduire les boucles et les branchements. *)
let new_labels =
  let count = ref 0 in
  fun fname names -> incr count; Array.map (fun name -> Printf.sprintf "__%s_%s_%i" fname name !count) names

let new_label fname name =
  (new_labels fname [| name |]).(0)

(**
   Fonction de traduction d'une fonction.
 *)
let tr_fdef prog fdef =

  let new_labels = new_labels fdef.name in
  let new_label = new_label fdef.name in

  (* Trouver la définition d'une autre fonction du programme *)
  let find_function fname =
    match List.find_opt (fun fdef -> fdef.name = fname) prog.functions with
    | None -> failwith (Printf.sprintf "la fonction %s n'est pas definie" fname)
    | Some fdef -> fdef
  in
  
  (* Vérifier qu'un appel de fonction est correct *)
  let assert_call fname params =
    let expected_params = (find_function fname).params in
    if expected_params <> params then
      failwith (Printf.sprintf 
        "la fonction %s attend exactement %d parametre(s)" fname expected_params);
  in

  (* Proposition : utiliser un point de retour unique pour tous les return
     (ou même en absence de return !). Cette étiquette est prévue pour cela. *)
  let return_label = new_label "return" in

  (* Traduction d'un opérateur binaire *)
  let tr_binop = function
    | Add -> add | Sub -> sub | Mul -> mul | Div -> div | Rem -> rem
    | Lsl -> sll | Lsr -> srl
    | Eq -> seq | Neq -> sne | Lt -> slt | Le -> sle | Gt -> sgt | Ge -> sge
    | And -> and_ | Or -> or_
  in

  (* Traduction des instructions : relativement direct, sauf pour les 
     branchements et les boucles *)
  let rec tr_instr = function
    | Read(rd, Global x)    -> lv rd x
    | Read(rd, Stack i)     -> read_local rd i
    | Write(Global x, r)    -> sv r x
    | Write(Stack i, r)     -> write_local r i
    | Move(rd, r)           -> move rd r
    | Push r                -> push r
    | Pop n                 -> pop n
    | Cst(rd, n)            -> li rd n
    | Unop(rd, Addi n, r)   -> addi rd r n
    | Unop(rd, Minus, r)    -> neg rd r
    | Unop(rd, Not, r)      -> not_ rd r
    | Binop(rd, op, r1, r2) -> (tr_binop op) rd r1 r2
    | Call(f, n)            ->
      assert_call f n; save_temps fdef.temps @@ jal f @@ restore_temps fdef.temps 
    | If(r, s1, s2)         -> tr_if r s1 s2
    | While(s1, r, s2)      -> tr_while s1 r s2
    | Return                -> b return_label
    | SysCall               -> syscall
    | TailCall(f, n)        ->
      assert_call f n; tailcall f fdef.params fdef.locals fdef.temps n

  and tr_if r s1 s2 =
    let labels = new_labels [| "if"; "else"; "end_if" |] in
    comment ("\t" ^ labels.(0) ^ ":")
    @@ beqz r labels.(1)
      @@ tr_seq s1
      @@ b labels.(2)
    @@ label labels.(1)
      @@ tr_seq s2 
    @@ label labels.(2)
  
  and tr_while s1 r s2 =
    let labels = new_labels [| "while"; "end_while" |] in
    label labels.(0)
    @@ tr_seq s1
    @@ beqz r labels.(1)
      @@ tr_seq s2
      @@ b labels.(0)
    @@ label labels.(1)

  and tr_seq (s: Eimp.sequence) = match s with
    | Nop         -> nop
    | Instr i     -> tr_instr i
    | Seq(s1, s2) -> tr_seq s1 @@ tr_seq s2
  in

  (* Code de la fonction. Il faut prévoir notamment ici, dans l'ordre
     - la convention d'appel, phase "début de l'appel",
     - le code de la fonction elle-même,
     - le point de retour unique,
     - la convention d'appel, phase "fin d'appel",
     - rendre la main.
   *)
  comment "\tsauvegarde des registres et allocation d'espace dans la pile"
  @@ init_fun fdef.locals fdef.temps
  @@ comment "\tcode de la fonction"
  @@ tr_seq fdef.code
  @@ label return_label
  @@ comment "\trestauration des registres sauvegardes et de la pile puis retour"
  @@ end_fun fdef.params fdef.locals fdef.temps
  @@ return


(**
   Fonction principale, de traduction d'un programme entier.
   Au-delà de la traduction de chaque fonction, on a
   - une initialisation qui donne la main à "main",
   - une fonction prédéfinie pour décoder un entier passsé en ligne de commande,
   - la déclaration des données globales.

   Attention, dans le code prédéfini d'initialisation il y a une adaptation à
   faire selon la convention d'appel (voir commentaire suivant).          
 *)
let tr_prog prog =
  let init =
    comment "s'il n'y a pas de parametre, on va directement a init_end"
    @@ beqz a0 "init_end"
    @@ comment "sinon on va a la fonction atoi"
    @@ lw a0 0 a1
    @@ jal "atoi"
    @@ label "init_end"
    (* Choix selon votre convention d'appel 
         move a0 v0 
       dans le cas où les premiers paramètres passent par les registres,
       mais 
         sw v0 0 sp
         subi sp sp 4
       dans le cas où tous passent par la pile.
     *)
    @@ comment "on push le resultat de atoi"
    @@ sw v0 0 sp
    @@ subi sp sp 4
    (* Choix : ici, on a sélectionné la version passant par la pile. *)
    @@ comment "on va a la fonction main"
    @@ jal "main"
    (* Après l'exécution de la fonction "main", appel système de fin de
       l'exécution. *)
    @@ comment "quand l'execution du main est finie, on termine le programme"
    @@ li v0 10
    @@ syscall
  and built_ins =
    (* Fonction de conversion chaîne -> entier, à base d'une boucle sur les
       caractères de la chaîne. *)
    newline @@ comment "fonction atoi"
    @@ label "atoi"
    @@ li   v0 0
    @@ label "atoi_loop"
    @@ lbu  t0 0 a0
    @@ beqz t0 "atoi_end"
    @@ addi t0 t0 (-48)
    @@ bltz t0 "atoi_error"
    @@ bgei t0 10 "atoi_error"
    @@ muli v0 v0 10
    @@ add  v0 v0 t0
    @@ addi a0 a0 1
    @@ b "atoi_loop"
    @@ label "atoi_error"
    @@ li   v0 10
    @@ syscall
    @@ label "atoi_end"
    @@ jr   ra
  in

  (**
     Code principal pour générer le code MIPS associé au programme source.
   *)
  let function_codes = List.fold_right
    (fun fdef code ->
      newline @@ comment (Printf.sprintf "fonction %s" fdef.name) @@ label fdef.name @@ tr_fdef prog fdef @@ code)
    prog.functions nop
  in
  let text = init @@ function_codes @@ built_ins @@ newline
  and data = comment "variables globales" @@ List.fold_right
    (fun id code -> label id @@ dword [0] @@ code)
    prog.globals nop
  in
  
  { text; data }
  
