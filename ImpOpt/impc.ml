open Format

let () =

  let parse_imp file =
    let c = open_in file in
    let lb = Lexing.from_channel c in
    let imp = Impparser.program Implexer.token lb in
    close_in c;
    imp
  in

  (* Lecture et analyse syntaxique *)
  let file = Sys.argv.(1) in
  let stdfile = ((Filename.dirname Sys.argv.(0)) ^ "/std.imp") in
  let imp_prog = Imp.include_lib (parse_imp stdfile) (parse_imp file) in

  (* Simplification et sélection d'instructions *)
  let mimp_prog = Imp2mimp.tr_program imp_prog in
  let output_file = (Filename.chop_suffix file ".imp") ^ ".mimp" in
  let out = open_out output_file in
  Mimp.pp_program mimp_prog out;
  close_out out;

  (* Décomposition des expressions *)
  let aimp_prog = Mimp2aimp.tr_prog mimp_prog in
  let output_file = (Filename.chop_suffix file ".imp") ^ ".aimp" in
  let out = open_out output_file in
  Aimp.pp_program aimp_prog out;
  close_out out;

  (* Allocation de registres *)
  let eimp_prog = Aimp2eimp.tr_prog aimp_prog in
  let output_file = (Filename.chop_suffix file ".imp") ^ ".eimp" in
  let out = open_out output_file in
  Eimp.pp_program eimp_prog out;
  close_out out;

  (* Génération de code assembleur *)
  let asm = Eimp2mips.tr_prog eimp_prog in
  let output_file = (Filename.chop_suffix file ".imp") ^ ".asm" in
  let out = open_out output_file in
  let outf = formatter_of_out_channel out in
  Mips.print_program outf asm;
  pp_print_flush outf ();
  close_out out;
  
  exit 0
