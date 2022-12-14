{

  open Lexing
  open Impparser

    let keyword_or_ident =
    let h = Hashtbl.create 17 in
    List.iter (fun (s, k) -> Hashtbl.add h s k) [
        "if",       IF;
        "else",     ELSE;
        "while",    WHILE;
        "for",      FOR;
        "true",     BOOL true;
        "false",    BOOL false;
        "var",      VAR;
        "function", FUNCTION;
        "return",   RETURN;
        "syscall",  SYSCALL;
      ] ;
    fun s ->
      try  Hashtbl.find h s
      with Not_found -> IDENT(s)
    
    let escape = function
        | 'n' -> '\n'
        | 'r' -> '\r'
        | 't' -> '\t'
        | '0' -> Char.chr 0
        | c -> c
}

let digit = ['0'-'9']
let number = ['-']? digit+
let alpha = ['a'-'z' 'A'-'Z']
let ident = ['a'-'z' '_'] (alpha | '_' | digit)*
  
rule token = parse
  | ['\n']
      { new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r']+
      { token lexbuf }
  | "//" [^ '\n']* "\n"
      { new_line lexbuf; token lexbuf }
  | "/*" 
      { comment lexbuf; token lexbuf }
  | number as n
      { CST(int_of_string n) }
  | "'\\" (_ as c) "'"
      { CST(Char.code (escape c)) }
  | "'" ([^ '\\' '\''] as c) "'"
      { CST(Char.code c) }
  | "\"" (([^'"' '\\'] | ('\\' _))* as s) "\""
      { STR(s) }
  | ident as id
      { keyword_or_ident id }
  | ";"
      { SEMI }
  | ":"
      { COLON }
  | "="
      { SET }
  | "++"
      { INCR }
  | "--"
      { DECR }
  | "+"
      { PLUS }
  | "-"
      { MINUS }
  | "*"
      { STAR }
  | "/"
      { SLASH }
  | "%"
      { PRCT }
  | ">>"
      { LSR }
  | "<<"
      { LSL }
  | "=="
      { EQ }
  | "!="
      { NEQ }
  | "<"
      { LT }
  | "<="
      { LE }
  | ">"
      { GT }
  | ">="
      { GE }
  | "&&"
      { AND }
  | "&"
      { AMPERSAND }
  | "||"
      { OR }
  | "!"
      { NOT }
  | "("
      { LPAR }
  | ")"
      { RPAR }
  | "["
      { LBRACK }
  | "]"
      { RBRACK }
  | "{"
      { BEGIN }
  | "}"
      { END }
  | ","
      { COMMA }
  | _
      { failwith ("Unknown character : " ^ (lexeme lexbuf)) }
  | eof
      { EOF }

and comment = parse
  | "*/"
      { () }
  | _
      { comment lexbuf }
  | eof
      { failwith "unfinished comment" }
