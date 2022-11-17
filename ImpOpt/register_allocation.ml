(**
   Allocation de registres.
   On travaille sur la représentation intermédiaire AIMP.

   Objectif : 
     dans chaque fonction, associer chaque registre virtuel
     à un emplacement mémoire physique (on dit qu'on "réalise"
     le registre virtuel), les emplacements pouvant être :
     - des registres réels
     - des emplacements dans le tableau d'activation (pile)
   Deux critères antagonistes :
     - deux registres virtuels dont les valeurs doivent être
       mémorisées simultanément ne peuvent partager une même
       réalisation (OBLIGATOIRE)
     - il faut s'efforcer d'utiliser au mieux les registres,
       et minimiser l'utilisation d'emplacements de pile
   Cette question cache un problème NP-complet : on ne cherche
   pas la solution optimale, mais on fait des efforts pour
   trouver une solution convenable.

   La procédure est découpée en trois parties.
   1/ analyse de vivacité : en chaque point du programme, on
      détermine quels registres virtuels sont "vivants" et
      doivent être présents en mémoire,
   2/ construction d'un graphe d'interférence : sur la base
      de l'analyse de vivacité, déterminer quels registres
      virtuels ne peuvent pas partager une même réalisation,
   3/ allocation de registres : associer à chaque registre
      virtuel une réalisation qui respecte les interférences.

   Raffinement de la procédure : lorsque deux registres virtuels
   sont des copies l'un de l'autre, on essaie de leur faire
   partager une même réalisation.
 *)

open Aimp
open Graph

module VSet = Set.Make(String)
module IntSet = Set.Make(Int)

(**
   1/ Analyse de vivacité.
   En un point de programme donné, on dit qu'une variable est
   "vivante" si sa valeur actuelle est susceptible d'être utilisée
   plus tard. Autrement dit : s'il existe un scénario d'exécution
   future dans lequel cette variable est utilisée, sans avoir été
   modifiée au préalable.
   
   L'information de vivacité à un point donné vient donc du "futur",
   c'est-à-dire des instructions suivantes. Une lecture d'une variable
   crée de la vivacité (dans son passé), et une écriture détruit la
   vivacité. Comme chaque instruction est un point de modification de
   la vivacité, on distingue les variables vivantes "en entrée" et
   "en sortie" de chaque instruction (c'est-à-dire avant ou après)

   En notant 
   - IN[i] les variables vivantes en entrée de i
   - OUT[i] les variables vivantes en sortie de i
   - USE[i] les variables lues par i
   - DEF[i] les variables modifiées par i
   on exprime IN[i] en fonction de OUT[i] par l'équation
     IN[i] = (OUT[i] \ DEF[i]) u USE[i]

   Lorsque deux instructions i1; i2 se suivent, les variables vivantes
   en sortie de [i1] sont celles qui sont vivantes en entrée de [i2]
     OUT[i1] = IN[i2]
   Lors d'un branchement où deux blocs [s1] et [s2] peuvent suivre
   une instruction [i], il faut faire l'union des variables vivantes
   dans chacun des futurs possibles
     OUT[i] = IN[s1] u IN[s2]
 *)

let liveness fdef =
  (* Table associant à chaque instruction l'ensemble des variables qui
     sont vivantes en sortie. Rappel : en AIMP, chaque instruction
     atomique est identifiée par un numéro unique, que l'on utilise ici
     comme clé dans la table. *)
  let (liveness: (int, VSet.t) Hashtbl.t) = Hashtbl.create 64 in
  
  (** Calcul de vivacité pour une séquence.

      Utilisation :
        sequence s out
      en supposant que les variables vivantes en sortie de la séquence [s]
      sont données par [out], cet appel calcule et renvoie les variables
      vivantes en entrée de [s].

      Effet de bord : met à jour la table [liveness] pour toutes les
      instructions de la séquence. *)
  let rec sequence (s: sequence) (out: VSet.t): VSet.t = match s with
    | Nop -> out
    | Instr(n, i) ->
       Hashtbl.replace liveness n out; (* mise à jour par effet de bord *)
       instr i out
    | Seq(s1, s2) ->
       (* dans une séquence [s1 @@ s2], l'ensemble des variables vivantes
          en sortie de [s1] est donnée par l'ensemble des variables vivantes
          en entrée de [s2] *)
       sequence s1 (sequence s2 out)

  (** Calcul de vivacité pour une instruction.

      Utilisation :
        instr i out
     en supposant que les variables vivantes en sortie de l'instruction [i]
     sont données par [out], calcule et renvoie les variables vivantes
     en entrée de [i].

     Effet de bord : du fait d'appels à [sequence] dans les cas des branchements
     et des boucles, met à jour la table [liveness] pour toutes les 
     sous-instructions de [i]. *)
  and instr (i: instruction) (out: VSet.t): VSet.t = match i with
    | Write(_, r) ->
       (* Écriture dans une variable globale : le registre virtuel [r] est lu,
          et aucun registre n'est modifié. On ne fait donc qu'ajouter [r] aux
          registres vivants. *)
       VSet.add r out
    | Read(rd, _) | Cst(rd, _) -> 
       (* Lecture d'une variable globale, ou chargement d'une constante :
          aucun registre virtuel n'est lu, et un registre [rd] de destination
          est modifié. Le registre [rd] n'est donc pas vivant en entrée. *)
       VSet.remove rd out
    | Putchar r ->
       (* Le registre [r] est lu et les registres $a0 et $v0 sont modifiés. *)
       VSet.add r (VSet.diff out (VSet.of_list ["$a0"; "$v0"]))
    | Move(rd, r) | Unop(rd, _, r) -> 
       (* Le registre [r] est lu, le registre [rd] est modifié. *)
       VSet.add r (VSet.remove rd out)
    | Binop(rd, _, r1, r2) -> 
      (* Les registres [r1] et [r2] sont lus, le registre [rd] est modifié. *)
      VSet.union (VSet.remove rd out) (VSet.of_list [r1; r2])
    | Push r ->
      (* Le registre [r] est lu. *)
      VSet.add r out
    | Pop _ ->
      (* Rien n'est lu ou modifié. *)
       out
    | Call(_, n) ->
       (* Pour un appel de fonction :
          - les registres lus sont les éventuels registres $ai utilisés pour
            le passage des paramètres (selon la convention utilisée)
          - les registres caller-saved sont considérés comme modifiés par
            l'appel (on ne sait pas s'ils le seront pour de vrai, mais on ne
            peut pas l'exclure, alors on se protège en supposant le pire cas)
          Les registres caller-saved sont :
          - les registres $ti (sauf $t0 et $t1 qu'on garde en réserve)
          - les registres $ai
          - le registre $v0
        *)
        let modified = VSet.of_list [
          "$t2"; "$t3"; "$t4"; "$t5"; "$t6"; "$t7"; "$t8"; "$t9";
          "$a0"; "$a1"; "$a2"; "$a3";
          "$v0"
        ] in
        (* let read = VSet.of_list (List.init n (fun i -> Printf.sprintf "$a%d" i)) in *)
        let read = VSet.of_list [] in
        VSet.union read (VSet.diff out modified)
    | Return ->
       (* Rappel de la convention : on renvoie la valeur contenue dans $v0.
          Ce registre est donc considéré comme lu.
          En outre, on suppose que les registres callee-saved sont vivants
          en sortie de la fonction (on ne sait pas si l'appelant veut
          effectivement récupérer leur valeur, mais on doit faire comme si)
          Les registres callee-saved sont :
          - les registres $si
        *)
        VSet.union out 
          (VSet.of_list ["$v0"; "$s0"; "$s1"; "$s2"; "$s3"; "$s4"; "$s5"; "$s6"; "$s7"])
    | If(r, s1, s2) ->
       (* En sortie du test de la valeur de [r], les blocs [s1] et [s2]
          sont deux futurs possibles. Les variables vivantes dans ces deux
          blocs doivent donc être combinées. *)
       let live_in_true = sequence s1 out in
       let live_in_false = sequence s2 out in
       let live_in_test = VSet.add r (VSet.union live_in_true live_in_false) in
       live_in_test
    | While(st, r, s) ->
       (* La boucle induit une dépendance circulaire dans les équations
          de vivacité. Cela nécessite de calculer un point fixe à ces
          équations (qui existe en vertu d'un théorème général de Tarski).
          Dans ce cas particulier, on sait qu'on atteint le point fixe
          en faisant deux fois le calcul. *)
       (* Premier calcul en prenant [out] comme ensemble de sortie *)
       let live_in_body = sequence s out in
       let live_in_test = sequence st (VSet.add r live_in_body) in
       (* Deuxième calcul en prenant comme ensemble de sortie ce qui a
          été calculé lors du premier tour. *)
       let live_in_body = sequence s live_in_test in
       sequence st (VSet.add r live_in_body)
  in
       
  (* Pour remplir la table [liveness] d'une fonction, il suffit d'appliquer
     la fonction d'analyse précédente au code de cette fonction. *)
  ignore(sequence fdef.code VSet.empty);
  (* Remarque technique caml : [ignore] ne signifie pas que le code n'est
     pas exécuté ! Il s'agit simplement de déclarer que l'on n'utilisera
     pas le résultat renvoyé par l'appel [sequence fdef.code VSet.empty]
     (sans cette déclaration, le compilateur caml émettrait un avertissement).
     À propos de ce résultat qui ne sera pas utilisé : s'il est différent de
     [VSet.empty], on a risque d'accès à des variables non initialisées. *)

  (* À la fin, on renvoie la table de vivacité *)
  liveness


(**
   2/ Construction du graphe d'interférence

   On construit un graphe dont les sommets sont les registres (virtuels ou
   réels), et chaque arête dénote une interférence entre deux registres,
   c'est-à-dire l'impossibilité de leur affecter une même réalisation.

   Le critère principal pour ajouter une arête est :
   - si une instruction [i] modifie un registre [rd], alors [rd] est en
     interférence avec tous les registres [r] vivants en sortie de [i]
     (à part [rd] lui-même, le cas échéant).

   Exception à ce critère : dans le cas d'une instruction
     rd <- r
   de copie du registre [r] dans le registre [rd] (move), on ne déclare
   pas d'interférence entre [r] et [rd] : à ce stade du programme les
   deux registres contiennent la même valeur, et on peut imaginer les
   partager. Au contraire : on va placer entre les deux registres [r]
   et [rd] une arête de "préférence" indiquant qu'il serait judicieux
   de réaliser ces deux registres par le même emplacement physique,
   pour éviter une copie superflue.

   Attention toutefois, les arêtes d'interférence sont prioritaires sur
   les arêtes de préférence : si deux instructions affectent les deux
   types d'arêtes à la même paire (r, rd), on ne conserve que l'arête
   d'interférence.
 *)
let interference_graph fdef =

  (* Table de hachage contenant les informations de vivacité en sortie
     de chaque instruction, qu'on consultera pour appliquer le critère
     précédent. *)
  let live_out = liveness fdef in

  (* Initialisation d'un graphe sans arêtes, avec un sommet pour chaque
     variables locale (ie. chaque registre virtuel). *)
  let g = List.fold_left 
            (fun g x -> Graph.add_vertex x g) 
            Graph.empty 
            fdef.locals
  in
  (* La bibliothèque Graph donne une structure immuable. Les fonctions de
     construction du graphe renvoient donc le graphe construit. *)

  (* Ajouter une arête entre chaque registres dans rdl et chaque (autre) registre dans out *)
  let add_edges g out rdl =
    VSet.fold (fun r g' ->
      List.fold_left (fun g'' rd -> 
        if r <> rd then
          Graph.add_edge r rd Conflict g''
        else
          g''
      ) g' rdl
    ) out g
  in

  (** Recherche des interférences dans une séquence.

      Utilisation :
        seq s g
      renvoie le graphe obtenu en ajoutant au graphe [g] les
      interférences trouvées dans la séquence [s].

      Cette fonction se contente d'itérer la fonction [instr] de
      recherche d'interférences dans une instruction, en chaînant
      les résultats.      
   *)
  let rec seq s g = match s with
    | Nop -> g
    | Instr(n, i) -> instr n i g
    | Seq(s1, s2) -> seq s1 (seq s2 g)

  (** Recherche des interférences dans une instruction.

      Utilisation :
        instr n i g
      renvoie le graphe obtenu en ajoutant au graphe [g] les
      interférences trouvées dans l'instruction [i], de numéro [n].
   *)
  and instr n i g = match i with
    | Read(rd, _) | Cst(rd, _) | Unop(rd, _, _) | Binop(rd, _, _, _) ->
       (* Dans chacun de ces cas l'instruction écrit uniquement dans le
          registre [rd]. On ajoute à g une arête entre rd et chaque
          (autre) registre virtuel vivant en sortie. *)
       add_edges g (Hashtbl.find live_out n) [rd]
    | If(_, s1, s2) ->
      seq s1 (seq s2 g)
    | While(s1, _, s2) ->
      seq s1 (seq s2 g)
    | Move(rd, rs) ->
      let out = Hashtbl.find live_out n in
      VSet.fold (fun r g' ->
        if r <> rd && r <> rs then
          Graph.add_edge r rd Conflict g'
        else
          g'
      ) out (if rd <> rs then Graph.add_edge rd rs Preference g else g)
    | Putchar _ ->
      (* Putchar écrit dans les registres $v0 et $a0 *)
      add_edges g (Hashtbl.find live_out n) ["$v0"; "$a0"]
    | Call(_, _) -> 
      (* Ecriture dans les registres $v, $a et $t *)
      add_edges g (Hashtbl.find live_out n) [
        "$v0"; "$v1";
        "$a0"; "$a1"; "$a2"; "$a3";
        "$t2"; "$t3"; "$t4"; "$t5"; "$t6"; "$t7"; "$t8"; "$t9";
      ]
    | Write _ | Return | Push _ | Pop _ ->
      g
  in

  (* Pour calculer le graphe d'interférence d'une fonction, il suffit
     de lancer la recherche d'interférence sur la séquence globale de
     la fonction. *)
  seq fdef.code g


(**
   3/ Coloration du graphe d'interférence
   Objectif : associer à chaque registre virtuel une "couleur",
   représentée par un numéro.

   Idée de base : algorithme glouton
     1. sélectionner un sommet v de petit degré
     2. colorier récursivement le graphe obtenu en retirant v
     3. donner à v la plus petite couleur non utilisée par ses voisins
   On raffine cette idée de base pour tenir compte de spécificités du
   problème d'origine :
     - on veut de préférence utiliser les couleurs entre 0 et K-1,
       pour une constante K donnant le nombre de registres réels,
       mais on s'autorise à utiliser les suivantes au besoin,
     - les arêtes de préférence indiquent des paires de sommets auxquels
       on veut affecter la même couleur si cela est possible,
     - les sommets peuvent avoir des "coûts" différents, en fonction de
       la fréquence à laquelle le registre correspondant est utilisé
       dans le programme.
*)

(* Un coloriage est une association entre des chaînes de caractères
   (les registres virtuels) et des entiers (les couleurs). *)
type color = int VMap.t

(** Fonction auxiliaire pour le choix de la couleur d'un sommet.
    
    Utilisation :
      choose_color v colors
    renvoie la plus petite couleur non utilisée par la coloration
    [colors] de l'ensemble de sommets [v].
    On peut supposer que tous les sommets de [v] ont bien une
    couleur définie dans [colors].
 *)
let choose_color (v: VSet.t) (colors: color): int =
  let all_colors = VMap.fold (fun x c colors ->
    if c >= 0 then IntSet.add c colors else colors
  ) colors IntSet.empty in
  let impossible_colors = VSet.fold (fun x vcolors ->
    let c = VMap.find x colors in
    if c >= 0 then IntSet.add c vcolors else vcolors
  ) v IntSet.empty in
  let possible_colors = IntSet.diff all_colors impossible_colors in
  if IntSet.is_empty possible_colors then
    IntSet.cardinal all_colors
  else
    IntSet.min_elt possible_colors

(* Tester si un registre est un registre réel *)
let is_areg r =
  r.[0] = '$'

(* Coloration par défaut : les registres réels sont coloriés avec des couleurs négatives,
   il ne pourront pas être alloués sur la pile  *)
let default_colors =
  List.fold_left (fun colors (x, c) -> VMap.add x c colors) VMap.empty 
    (List.mapi (fun i x -> x, -(i+1)) 
      [ "$v0"; "$v1"; 
        "$a0"; "$a1"; "$a2"; "$a3";
        "$s0"; "$s1"; "$s2"; "$s3"; "$s4"; "$s5"; "$s6"; "$s7" ])

let num_default_colors = VMap.cardinal default_colors

(* Trouver le registre réel correspondant à une couleur négative *)
let find_areg_by_color c =
  fst (VMap.find_first (fun r -> VMap.find r default_colors = c) default_colors)

(** Fonction de coloriage simple : une couleur par sommet *)
let color_simple (g: graph) (k: int): color * int =

  let add_color r (c, n) =
    if is_areg r || VMap.mem r c then
      (c, n)
    else 
      (VMap.add r n c, n + 1)
  in

  VMap.fold (fun r1 g' (c, n) ->
    VMap.fold (fun r2 t (c, n) ->
      add_color r2 (c, n)
    ) g' (add_color r1 (c, n))
  ) g (VMap.empty, 0)

(** Fonction principale de coloriage.

    Utilisation :
      color g k
    renvoie un coloriage des sommets du graphe [g], calculé sous
    l'hypothèse qu'il y a [k] registres réels.

    La procédure de coloriage combine 5 fonctions mutuellement
    récursives :
      simplify g   cherche un sommet à écarter et à garder pour la fin
      coalesce g   cherche deux sommets à fusionner
      freeze g     abandonne des arêtes de préférence
      spill g      cherche un sommet à sacrifier
      select x g   colorie le graphe obtenu en retirant x, puis x
    (détail ci-dessous).
 *)
let color (g: graph) (k: int): color =

  (** Critère de George pour la fusion de sommets.
      
      Utilisation :
        george x y g
      renvoie [true] si le critère de fusion permet de fusionner 
      le sommet [x] avec le sommet [y] de [g].
      Hypothèse : les sommets [x] et [y] sont liés par une arête de
      préférence (et donc ne sont pas en interférence).

      Détail du critère :
      - [x] ne doit pas être un registre réel
      - tous les voisins de [x] de degré >= K ou qui sont des registres réels 
        doivent être des voisins de [y]
      - si [y] est un registre réel, alors [x] ne peut pas avoir
        de registre réel parmi ses voisins

      Objectif de ce critère : s'il était possible de colorier le graphe
      d'origine avec [k] couleurs, alors cela reste possible après avoir
      fusionné [x] avec [y], c'est-à-dire après avoir ajouté des arêtes
      entre [y] et tous les voisins de [x].
   *)
  let george x y g =
    let xn = VMap.find x g in
    let yn = VMap.find y g in
    (* [x] n'est pas réel *)
    not (is_areg x)
    (* pour tout [n] voisin de [x], ([n] est réel ou degré de [n] >= k) => [n] est voisin de [y]) *)
    && VMap.for_all (fun n _ -> n = y || (not (is_areg n || degree n g >= k) || VMap.mem n yn)) xn
    (* ([y] est réel) => (pour tout [n] voisin de [x], [n] n'est pas réel) *)
    && (not (is_areg y) || VMap.for_all (fun n _ -> n = y || not (is_areg n)) xn)
  in

  (** Recherche d'un sommet à colorier.
      On cherche un sommet [x] de degré < K, et qui n'a pas d'arêtes de
      préférence. Si on en trouve un on appelle [select x g], et sinon
      on passe à [coalesce].

      Heuristique : parmi les sommets sélectionnables, prendre un sommet
      de faible degré.
   *)
  let rec simplify g =
    let choice, _ = VMap.fold (fun x _ (choice, ydegree) ->
      let xdegree = degree x g in
      match xdegree < k && not (has_pref x g), choice with
      | true, None -> Some x, xdegree
      | true, Some y when xdegree < ydegree -> Some x, xdegree
      | _ -> choice, ydegree
    ) g (None, 0) in
    match choice with
    | None -> coalesce g
    | Some x -> select x g

  (** Recherche de deux sommets à fusionner.
      Parmi les sommets liés par des arêtes de préférence, on en cherche
      deux qui satisfont le critère de George. Si on trouve une telle
      paire (x, y), on colorie avec [simplify] le graphe [g'] obtenu en
      fusionnant [x] avec [y], puis on propage à [x] la couleur qui a
      été affectée à [y]. Dans le cas contraire, on passe à [freeze]
   *)
  and coalesce g =
    let choice = find_first_edge_opt (fun x y t -> t = Preference && george x y g) g in
    match choice with
    | None -> freeze g
    | Some (x, y, _) ->
      let colors = simplify (merge x y g) in
      let ycolor = VMap.find y colors in
      VMap.add x ycolor colors
     
  (** Abandon d'arêtes de préférence. 
      On cherche un sommet de degré < K. S'il existe un tel sommet [x],
      celui-ci a nécessairement des arêtes de préférence. On les retire
      et on revient à [simplify]. Sinon, on passe à [spill].
   *)
  and freeze g =
    let choice = VMap.find_first_opt (fun x -> degree x g < k) g in
    match choice with
    | None -> spill g
    | Some (x, _) -> simplify (remove_prefs x g)
    
  (** Sacrifice d'un sommet.
      On se résigne à ne (peut-être) pas pouvoir donner à l'un des sommets
      une couleur < K. On choisit un sommet [x] et on appelle [select x g].
      Note : le fait qu'un sommet [x] ait un degré >= K signifie qu'il n'est
      pas certain qu'il puisse recevoir une couleur < K après que ses voisins
      auront été coloriés. Mais avec un peu de chance cela fonctionnera
      quand même !

      Exception : on peut également arriver ici dans le cas où tous les
      sommets restants sont déjà coloriés (car il ne reste que des sommets
      correspondant à des registres réels). Dans ce cas on a atteint le cas
      de base de notre récursion.

      Heuristiques :
      - favoriser un sommet correspondant à un registre peu utilisé, pour
        limiter le nombre d'accès à la mémoire dans l'hypothèse où le sommet
        sacrifié serait effectivement associé à un emplacement de pile
        (note : ce critère demande d'avoir collecté des infos sur la
        fréquence d'utilisation estimée des différents registres),
      - favoriser des sommets de fort degré, dont la suppression va donc
        supprimer de nombreuses arêtes et faciliter le coloriage des autres
        registres.
   *)
  and spill g =
    let choice, _ = VMap.fold (fun x _ v ->
      let xdegree = degree x g in
      match v with
      | Some _, bdegree when xdegree > bdegree -> Some x, xdegree
      | None, _ -> Some x, degree x g
      | best -> best
    ) g (None, 0) in
    match choice with
    | None -> default_colors
    | Some x -> select x g

  (** Mettre de côté un sommet [x] et colorier récursivement le graphe [g']
      ainsi obtenu. À la fin, on choisit une couleur pour [x] compatible
      avec les couleurs sélectionnées pour ses voisins.
   *)
  and select x g =
    let colors = simplify (remove_vertex x g) in
    let xcolor = 
      match VMap.find_opt x colors with
      | Some c -> c
      | None -> choose_color (neighbours x Conflict g) colors
    in VMap.add x xcolor colors
  in

  simplify g

let print_colors c =
  Printf.(printf "Coloration : \n";
          VMap.iter (printf "  %s: %i\n") c)

(**
   4/ Conclusion
   Les couleurs sont des numéros. Les numéros de 0 à K-1 sont associés
   aux K registres physiques utilisés, et les numéros suivants à des
   emplacements dans la pile.   
 *)

type register =
  | Actual  of string
  | Stacked of int

let convert_vreg k r c =
  if is_areg r then
    Actual r
  else if c < 0 then
    Actual (find_areg_by_color c)
  else if c < k then
    Actual (Printf.sprintf "$t%d" (c + 2))
  else
    Stacked c

let allocation_num allocation =
  let stacked, actual_t = (VMap.fold (fun x r (stacked, actual_t) ->
    match r with
    | Stacked i -> IntSet.add i stacked, actual_t
    | Actual r when r.[1] = 't' -> stacked, VSet.add r actual_t
    | _ -> stacked, actual_t
  ) allocation (IntSet.empty, VSet.empty)) in
  IntSet.cardinal stacked, VSet.cardinal actual_t

let allocation (fdef: function_def): register Graph.VMap.t * int * int =
  (* Calculer les vivacités, en déduire un graphe d'interférence, 
     le colorier, puis en déduire :
     - une affectation concrète de chaque sommet à un registre réel
       ou un emplacement de pile,
     - le nombre d'emplacements de pile utilisés.
     - le nombre de registres $t utilisés.
   *)
  let graph = interference_graph fdef in
  let colors = color graph 8 in
  let allocation = VMap.mapi (convert_vreg 8) colors in
  let num_stacked, num_actual_t = allocation_num allocation in
  (* print_graph graph;
  print_colors colors; *)
  (allocation, num_stacked, num_actual_t)
