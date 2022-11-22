%{

  open Lexing
  open Imp
  open Ops

  type function_content = {
    locals: string list;
    code: sequence;
  }

  let content locals code = {
    locals = locals;
    code = code;
  }

  let merge c1 c2 = {
    locals = c1.locals @ c2.locals;
    code = c1.code @ c2.code;
  }

  let control c1 c2 code = {
    locals = c1.locals @ c2.locals;
    code = code;
  }
%}

%token PLUS MINUS STAR SLASH PRCT
%token LSL LSR EQ NEQ LT LE GT GE
%token AND OR NOT
%token INCR DECR

%token <int> CST
%token <bool> BOOL
%token <string> STR
%token <string> IDENT
%token VAR FUNCTION COMMA
%token LPAR RPAR BEGIN END LBRACK RBRACK SEMI COLON AMPERSAND
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

program:
| EOF
    { { globals = []; functions = []; globals_init = [] } }
| v=variables_decl SEMI p=program
    { { globals = v.locals @ p.globals; functions = p.functions; globals_init = v.code @ p.globals_init } }
| f=function_def p=program
    { { globals = p.globals; functions = f :: p.functions; globals_init = p.globals_init } }

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
    content=instruction_list
  END
  { { name; code = content.code; params; locals = content.locals; } }
;

variables_decl:
| VAR l=variable_init_list { l }
;

variable_init_list:
| v=variable_init { v }
| v=variable_init COMMA l=variable_init_list { merge v l }

variable_init:
| id=IDENT SET e=expression { content [id] [Set(id, e)] }
| id=IDENT { content [id] [] }
;

instruction_list:
| { content [] [] }
| i=instruction l=instruction_list { merge i l }

for_incr_instruction:
| id=IDENT SET e=expression
    { content [] [Set(id, e)] }
| id=IDENT INCR
    { content [] [Set(id, Binop(Add, Var id, Cst 1))] }
| id=IDENT DECR
    { content [] [Set(id, Binop(Sub, Var id, Cst 1))] }
| e=expression
    { content [] [Expr(e)] }
| STAR ptr=expression SET e=expression
    { content [] [Write(ptr, 0, 4, e)] }
| array=expression LBRACK index=expression RBRACK SET e=expression
    { content [] [Write(Binop(Add, array, index), 0, 4, e)] }
| array=expression LBRACK index=expression COLON s=CST RBRACK SET e=expression
    { content [] [Write(Binop(Add, array, Binop(Mul, index, Cst s)), 0, s, e)] }
;

for_init_instruction:
| locals=variables_decl { locals }
| i=for_incr_instruction { i }
;

instruction:
| i=for_init_instruction SEMI { i }
| IF LPAR c=expression RPAR BEGIN s1=instruction_list END ELSE BEGIN s2=instruction_list END
    { control s1 s2 [If(c, s1.code, s2.code)] }
| IF LPAR c=expression RPAR BEGIN s1=instruction_list END ELSE s2=instruction
    { control s1 s2 [If(c, s1.code, s2.code)] }
| IF LPAR c=expression RPAR BEGIN s1=instruction_list END
    { content s1.locals [If(c, s1.code, [])] }
| WHILE LPAR c=expression RPAR BEGIN s=instruction_list END
    { content s.locals [While(c, s.code)] }
| FOR LPAR init=for_init_instruction SEMI cond=expression SEMI incr=for_incr_instruction RPAR
    BEGIN s=instruction_list END
    { merge init (control incr s [While(cond, s.code @ incr.code)]) }
| RETURN e=expression_except_call SEMI
    { content [] [Return(e)] }
| RETURN SEMI
    { content [] [Return(Cst(0))] }
| RETURN f=IDENT LPAR params=separated_list(COMMA, expression) RPAR SEMI
    { content [] [TailCall(f, params)] }
;

expression_except_call:
| n=CST { Cst(n) }
| b=BOOL { Bool(b) }
| s=STR { Str(s) }
| id=IDENT { Var(id) }
| LPAR e=expression RPAR { e }
| STAR ptr=expression { Unop(Deref(0, 4), ptr) }
| AMPERSAND id=IDENT { Addr(id) }
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

