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
%token PUTCHAR SET IF ELSE WHILE RETURN
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

program:
| globals=list(variable_decl) functions=list(function_def) EOF
    { {functions; globals} }
| error { let pos = $startpos in
          let message =
            Printf.sprintf
              "Syntax error at %d, %d"
              pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
          in
          failwith message }
;

variable_decl:
| VAR id=IDENT SEMI { id }
;

function_def:
| FUNCTION name=IDENT LPAR params=separated_list(COMMA, IDENT) RPAR
    BEGIN locals=list(variable_decl) code=list(instruction) END
    { {name; code; params; locals} }
;

instruction:
| PUTCHAR LPAR e=expression RPAR SEMI { Putchar(e) }
| id=IDENT SET e=expression SEMI { Set(id, e) }
| IF LPAR c=expression RPAR
    BEGIN s1=list(instruction) END
    ELSE BEGIN s2=list(instruction) END { If(c, s1, s2) }
| IF LPAR c=expression RPAR
    BEGIN s1=list(instruction) END
    ELSE s2=instruction { If(c, s1, [s2]) }
| IF LPAR c=expression RPAR
    BEGIN s1=list(instruction) END { If(c, s1, []) }
| WHILE LPAR c=expression RPAR
    BEGIN s=list(instruction) END { While(c, s) }
| RETURN e=expression_except_call SEMI { Return(e) }
| RETURN SEMI { Return(Cst(0)) }
| RETURN f=IDENT LPAR params=separated_list(COMMA, expression) RPAR SEMI { TailCall(f, params) }
| e=expression SEMI { Expr(e) }
;

expression_except_call:
| n=CST { Cst(n) }
| b=BOOL { Bool(b) }
| id=IDENT { Var(id) }
| LPAR e=expression RPAR { e }
| op=unop e=expression { Unop(op, e) }
| e1=expression op=binop e2=expression { Binop(op, e1, e2) }
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

