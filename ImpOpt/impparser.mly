%{

  open Lexing
  open Imp
  open Ops

%}

%token PLUS MINUS STAR SLASH PRCT
%token LSL LSR EQ NEQ LT LE GT GE
%token AND OR NOT
%token INCR DECR

%token <int> CST
%token <bool> BOOL
%token <string> IDENT
%token VAR FUNCTION COMMA
%token LPAR RPAR BEGIN END LBRACK RBRACK SEMI COLON
%token SET IF ELSE WHILE FOR RETURN SYSCALL
%token EOF

%left AND OR
%left LT LE GT GE EQ NEQ
%left PLUS MINUS
%left STAR SLASH PRCT
%left LSL LSR
%nonassoc NOT
%nonassoc LBRACK

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
| VAR l=variable_init_list { l }
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

for_incr_instruction:
| id=IDENT SET e=expression { [], [Set(id, e)] }
| id=IDENT INCR { [], [Set(id, Binop(Add, Var id, Cst 1))] }
| id=IDENT DECR { [], [Set(id, Binop(Sub, Var id, Cst 1))] }
| e=expression { [], [Expr(e)] }
| STAR ptr=expression SET e=expression { [], [Write(ptr, 0, 4, e)] }
| array=expression LBRACK index=expression RBRACK SET e=expression
    { [], [Write(Binop(Add, array, index), 0, 4, e)] }
| array=expression LBRACK index=expression COLON s=CST RBRACK SET e=expression
    { [], [Write(Binop(Add, array, Binop(Mul, index, Cst s)), 0, s, e)] }
;

for_init_instruction:
| locals=variables_decl { fst locals, snd locals }
| i=for_incr_instruction { i }
;

instruction:
| i=for_init_instruction SEMI { i }
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
| FOR LPAR init=for_init_instruction SEMI cond=expression SEMI incr=for_incr_instruction RPAR
    BEGIN s=instruction_list END { fst init @ fst incr @ fst s, snd init @ [While(cond, snd s @ snd incr)] }
| RETURN e=expression_except_call SEMI { [], [Return(e)] }
| RETURN SEMI { [], [Return(Cst(0))] }
| RETURN f=IDENT LPAR params=separated_list(COMMA, expression) RPAR SEMI { [], [TailCall(f, params)] }
;

expression_except_call:
| n=CST { Cst(n) }
| b=BOOL { Bool(b) }
| id=IDENT { Var(id) }
| LPAR e=expression RPAR { e }
| STAR ptr=expression { Unop(Deref(0, 4), ptr) }
| array=expression LBRACK index=expression RBRACK { Unop(Deref(0, 4), Binop(Add, array, index)) }
| array=expression LBRACK index=expression COLON s=CST RBRACK { Unop(Deref(0, s), Binop(Add, array, Binop(Mul, index, Cst s))) }
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

