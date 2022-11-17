open Format

let usage = "usage: ./func file.fun"

let spec = []
  
let file =
    let file = ref None in
    let set_params s =
      if !file <> None || not (Filename.check_suffix s ".fun") then
        raise (Arg.Bad "no .fun extension");
      file := Some s
    in
    Arg.parse spec set_params usage;
    match !file with 
      | Some f -> f
      | _ -> Arg.usage spec usage; exit 1

let () =
  let c  = open_in file in
  let lb = Lexing.from_channel c in

  let progfun = Funparser.program Funlexer.token lb in
  close_in c;
  let progclj = Fun2clj.translate_program progfun in
  let progimp = Clj2imp.translate_program progclj in

  let output_file = (Filename.chop_suffix file ".fun") ^ ".imp" in

  let out = open_out output_file in
  Imppp.pp_program progimp out;
  close_out out;

  exit 0
    
