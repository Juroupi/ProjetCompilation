%{

  open Lexing
  open Imp
  open Ops

%}

%token PLUS MINUS STAR SLASH PRCT
%token LSL LSR EQ NEQ LT LE GT GE
%token AND OR NOT

%token <int> CST
%token <bool> BOOL
%token <string> IDENT
%token VAR FUNCTION COMMA
%token LPAR RPAR BEGIN END (* LBRACKET RBRACKET *) SEMI
%token SET IF ELSE WHILE RETURN SYSCALL
%token EOF

%left AND OR
%left LT LE GT GE EQ NEQ
%left PLUS MINUS
%left STAR SLASH PRCT
%left LSL LSR
%nonassoc NOT
(* %nonassoc LBRACKET *)

%start program
%type <Imp.program> program

%%

global_decl:
| VAR ids=separated_nonempty_list(COMMA, IDENT) SEMI { ids }
;

program:
| globals=list(global_decl) functions=list(function_def) EOF
    { {functions; globals = List.concat globals} }
| error { let pos = $startpos in
          let message =
            Printf.sprintf
              "Syntax error at %d, %d"
              pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
          in
          failwith message }
;

function_def:
| FUNCTION name=IDENT LPAR params=separated_list(COMMA, IDENT) RPAR BEGIN 
    code=instruction_list
  END
  { { name; code = snd code; params; locals = fst code } }
;

variables_decl:
| VAR l=variable_init_list SEMI { l }
;

variable_init_list:
| v=variable_init { fst v, snd v }
| v=variable_init COMMA l=variable_init_list { fst v @ fst l, snd v @ snd l }

variable_init:
| id=IDENT SET e=expression { [id], [Set(id, e)] }
| id=IDENT { [id], [] }
;

instruction_list:
| { [], [] }
| i=instruction l=instruction_list { fst i @ fst l, snd i @ snd l }

instruction:
| locals=variables_decl { fst locals, snd locals }
| id=IDENT SET e=expression SEMI { [], [Set(id, e)] }
| IF LPAR c=expression RPAR
    BEGIN s1=instruction_list END
    ELSE BEGIN s2=instruction_list END { fst s1 @ fst s2, [If(c, snd s1, snd s2)] }
| IF LPAR c=expression RPAR
    BEGIN s1=instruction_list END
    ELSE s2=instruction { fst s1 @ fst s2, [If(c, snd s1, snd s2)] }
| IF LPAR c=expression RPAR
    BEGIN s1=instruction_list END { fst s1, [If(c, snd s1, [])] }
| WHILE LPAR c=expression RPAR
    BEGIN s=instruction_list END { fst s, [While(c, snd s)] }
| RETURN e=expression_except_call SEMI { [], [Return(e)] }
| RETURN SEMI { [], [Return(Cst(0))] }
| RETURN f=IDENT LPAR params=separated_list(COMMA, expression) RPAR SEMI { [], [TailCall(f, params)] }
| e=expression SEMI { [], [Expr(e)] }
;

expression_except_call:
| n=CST { Cst(n) }
| b=BOOL { Bool(b) }
| id=IDENT { Var(id) }
| LPAR e=expression RPAR { e }
| op=unop e=expression { Unop(op, e) }
| e1=expression op=binop e2=expression { Binop(op, e1, e2) }
| SYSCALL LPAR params=separated_nonempty_list(COMMA, expression) RPAR { SysCall(List.hd params, List.tl params) }
;

expression:
| e=expression_except_call { e }
| f=IDENT LPAR params=separated_list(COMMA, expression) RPAR { Call(f, params) }
;

%inline unop:
| MINUS { Minus }
| NOT { Not }
;

%inline binop:
| PLUS { Add }
| MINUS { Sub }
| STAR { Mul }
| SLASH { Div }
| PRCT { Rem }
| LSL { Lsl }
| LSR { Lsr }
| EQ { Eq }
| NEQ { Neq }
| LT { Lt }
| LE { Le }
| GT { Gt }
| GE { Ge }
| AND { And }
| OR { Or }
;

