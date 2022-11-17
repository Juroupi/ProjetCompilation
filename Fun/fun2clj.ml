module VSet = Set.Make(String)

module VMap = Map.Make(String)
type vmap = (string option) VMap.t

let translate_program e =

  (* Liste des définitions de fonctions *)
  let fdefs = ref [] in

  (* Création d'un nouveau nom de fonction *)
  let new_fname =
    let cpt = ref (-1) in
    fun fname -> 
      incr cpt; 
      match fname with 
      | Some fname -> Printf.sprintf "fun_%s_%i" fname !cpt, fname
      | None -> Printf.sprintf "fun_%i" !cpt, ""
  in
  
  (* Conversion expression Fun -> expression + noms et identifiants des variables libres Clj *)
  let rec tr_expr (e: Fun.expression) (bvars: vmap) (recfname: string option):
      Clj.expression * (string * int) list =
    
    (* Liste des noms et identifiants des variables libres *)
    let cvars = ref [] in
    
    (* Création d'une nouvelle variable libre *)
    let new_cvar =
      let cpt = ref 0 in (* commencera à 1 *)
      fun x -> incr cpt; cvars := (x, !cpt) :: !cvars; !cpt
    in
    
    (* Conversion variable Fun -> variable Clj *)
    let convert_var x bvars = Clj.(
      match VMap.find_opt x bvars with
      | Some Some alias ->
        Clj.Var (Name alias)
      | Some None ->
        Clj.Var (Name x)
      | _ ->
        if (Some x) = recfname then
          Clj.Var (Name "closure")
        else if List.mem_assoc x !cvars then
          Clj.Var (CVar (List.assoc x !cvars))
        else
          Clj.Var (CVar (new_cvar x))
    ) in

    (* Récupérer le nom réel d'une variable *)
    let get_alias x bvars =
      match VMap.find_opt x bvars with
      | Some Some alias -> alias
      | _ -> x
    in
  
    (* Convertir un élément de cvar en variable Clj *)
    let convert_cvar bvars (x, _) =
      convert_var x bvars
    in

    (* Représentation d'une fonction *)
    let closure fname cvars =
      Clj.Tpl ((Clj.FunRef fname) :: cvars)
    in
    
    (* Création d'une nouvelle fonction *)
    let rec new_fdef fname pname code bvars recur =
      let fname, ofname = new_fname fname in
      let code, cvars = tr_expr code (VMap.singleton pname None) (if recur then Some ofname else None) in
      fdefs := Clj.{ name = fname; code = code; param = pname } :: !fdefs;
      fname, List.rev_map (convert_cvar bvars) cvars
    
    (* Conversion Fun -> Clj *)
    and crawl e bvars = match e with
      | Fun.Cst(n) ->
        Clj.Cst(n)

      | Fun.Bool(b) ->
        Clj.Bool(b)
          
      | Fun.Var(x) ->
        convert_var x bvars

      | Fun.Unop(op, e) ->
        Clj.Unop(op, crawl e bvars)
          
      | Fun.Binop(op, e1, e2) ->
        Clj.Binop(op, crawl e1 bvars, crawl e2 bvars)
          
      | Fun.Tpl(el) ->
        Clj.Tpl(List.map (fun e -> crawl e bvars) el)

      | Fun.TplGet(t, i) ->
        Clj.TplGet(crawl t bvars, i)
      
      | Fun.Fun(pname, code) ->
        let fname, cvars = new_fdef None pname code bvars false in
        closure fname cvars
      
      | Fun.App(e1, e2) ->
        Clj.App(crawl e1 bvars, crawl e2 bvars)

      | Fun.If(ce, te, fe) ->
        Clj.If(crawl ce bvars, crawl te bvars, crawl fe bvars)

      | Fun.LetIn(x, Fun.Fun(pname, code), e2) ->
        let fname, cvars = new_fdef (Some x) pname code bvars false in
        let bvars = VMap.add x None bvars in
        Clj.LetIn(x, closure fname cvars, crawl e2 bvars)

      | Fun.LetIn(x, Fun.Var v, e2) ->
        crawl e2 (VMap.add x (Some (get_alias v bvars)) bvars)

      | Fun.LetIn(x, e1, e2) ->
        Clj.LetIn(x, crawl e1 bvars, crawl e2 (VMap.add x None bvars))

      | Fun.LetRec(x, Fun.Fun(pname, code), e2) ->
        let fname, cvars = new_fdef (Some x) pname code bvars true in
        let bvars = VMap.add x None bvars in
        Clj.LetRec(x, closure fname cvars, crawl e2 bvars)

      | Fun.LetRec(x, Fun.Var v, e2) when x <> v ->
        crawl e2 (VMap.add x (Some (get_alias v bvars)) bvars)

      | Fun.LetRec(x, e1, e2) ->
        let bvars = VMap.add x None bvars in
        Clj.LetRec(x, crawl e1 bvars, crawl e2 bvars)
    in

    let te = crawl e bvars in
    te, !cvars

  in
  let code, _ = tr_expr e VMap.empty None in
  Clj.({
    functions = !fdefs;
    code = code;
  })
