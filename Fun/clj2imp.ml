module STbl = Map.Make(String)

let tr_var v env = match v with
  | Clj.Name(x) ->
    Imp.(if STbl.mem x env then Var(STbl.find x env) else Var x)
  | Clj.CVar(n) ->
    Imp.(array_get (Var "closure") (Cst n))


let cpt = ref (-1)

let return_expr tail s e =
  if tail then
    s @ [Imp.Return e], Imp.Void
  else
    s, e
      
let tr_expr e env tail =

  let vars = ref [] in

  let new_var id =
    incr cpt;
    let v = Printf.sprintf "%s_%i" id !cpt in
    vars := v :: !vars;
    v
  in

  let pcall closure param =
    Imp.PCall(Imp.Deref (Imp.array_get closure (Imp.Cst 0)), [ param; closure ])
  in
  
  let rec tr_expr (e: Clj.expression) (env: string STbl.t) (tail : bool):
      Imp.sequence * Imp.expression =
    let return_expr = return_expr tail in
    match e with
      | Clj.Cst(n) ->
        return_expr [] (Imp.Cst n)

      | Clj.Bool(b) ->
        return_expr [] (Imp.Bool b)

      | Clj.Var(v) ->
        return_expr [] (tr_var v env)
          
      | Clj.Unop(op, e) ->
        let is, te = tr_expr e env false in
        return_expr is (Imp.Unop(op, te))
          
      | Clj.Binop(op, e1, e2) ->
        let is1, te1 = tr_expr e1 env false in
        let is2, te2 = tr_expr e2 env false in
        return_expr (is1 @ is2) (Imp.Binop(op, te1, te2))
      
      | Clj.Tpl([]) ->
        return_expr [] (Imp.Cst 0)
      
      | Clj.Tpl(el) ->
        let s, e = tr_tuple (new_var "tuple") el env in
        return_expr s e
      
      | Clj.TplGet(t, i) ->
        let is, te = tr_expr t env false in
        return_expr is (Imp.array_get te (Imp.Cst i))
      
      | Clj.FunRef f ->
        return_expr [] (Imp.Addr f)

      | Clj.App(Clj.Var v, e2) ->
        let te1 = tr_var v env in
        let is2, te2 = tr_expr e2 env false in
        return_expr is2 (pcall te1 te2)

      | Clj.App(e1, e2) ->
        let is1, te1 = tr_expr e1 env false in
        let is2, te2 = tr_expr e2 env false in
        let closure = new_var "fclos" in
        return_expr (is1 @ is2 @ [ Imp.Set(closure, te1) ]) (pcall (Imp.Var closure) te2)
      
      | Clj.If(ce, te, fe) when tail ->
        let isc, tce = tr_expr ce env false in
        let ist, tte = tr_expr te env true in
        let isf, tfe = tr_expr fe env true in
        isc @ [Imp.If(tce, ist, isf)], Imp.Void
      
      | Clj.If(ce, te, fe) ->
        let isc, tce = tr_expr ce env false in
        let ist, tte = tr_expr te env false in
        let isf, tfe = tr_expr fe env false in
        let ifres = new_var "ifres" in
        isc @ [Imp.If(tce,
            ist @ [Imp.Set(ifres, tte)], 
            isf @ [Imp.Set(ifres, tfe)]
          )], Imp.Var ifres
          
      | Clj.LetIn(x, Clj.Tpl(el), e2) ->
        let lv = new_var x in
        let is1, t1 = tr_tuple lv el env in
        let is2, t2 = tr_expr e2 (STbl.add x lv env) tail in
        is1 @ is2, t2

      | Clj.LetIn(x, e1, e2) ->
        let lv = new_var x in
        let is1, t1 = tr_expr e1 env false in
        let is2, t2 = tr_expr e2 (STbl.add x lv env) tail in
        is1 @ [Imp.Set(lv, t1)] @ is2, t2

      | Clj.LetRec(x, Clj.Tpl(el), e2) ->
        let lv = new_var x in
        let env = STbl.add x lv env in
        let is1, t1 = tr_tuple lv el env in
        let is2, t2 = tr_expr e2 env tail in
        is1 @ is2, t2
          
      | Clj.LetRec(x, e1, e2) ->
        let lv = new_var x in
        let env = STbl.add x lv env in
        let is1, t1 = tr_expr e1 env false in
        let is2, t2 = tr_expr e2 env tail in
        is1 @ [Imp.Set(lv, t1)] @ is2, t2
  
  and tr_tuple lv el env =
    let tplInit = Imp.Set(lv, Imp.array_create (Imp.Cst (List.length el))) in
    let tplVar = Imp.Var(lv) in
    let is, _ = List.fold_left (fun (isl, idx) e ->
      let is, te = tr_expr e env false in
      let teInit = Imp.array_set tplVar (Imp.Cst idx) te in
      (isl @ is @ [teInit], idx + 1)
    ) ([tplInit], 0) el in
    is, tplVar
  in
    
  let is, te = tr_expr e env tail in
  is, te, !vars

    
let tr_fdef fdef =
  let x = Clj.(fdef.param) in
  let param = "param_" ^ x in
  let env = STbl.add x param STbl.empty in
  let is, te, locals = tr_expr Clj.(fdef.code) env true in
  Imp.({
    name = Clj.(fdef.name);
    code = is;
    params = [param; "closure"];
    locals = locals;
  })


let translate_program prog =
  let functions = List.map tr_fdef Clj.(prog.functions) in
  let is, te, globals = tr_expr Clj.(prog.code) STbl.empty false in
  let main = Imp.(is @ [Expr(Call("print_int", [te]))]) in
  Imp.({main; functions; globals})
    
