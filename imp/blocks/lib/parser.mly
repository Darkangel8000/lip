%{
open Ast
%}

%token TRUE
%token FALSE
%token LPAREN
%token RPAREN
%token LCPAREN
%token RCPAREN
%token IF
%token WHILE
%token THEN
%token ELSE
%token OR
%token AND
%token NOT
%token ADD
%token SUB
%token MUL
%token EQ
%token LEQ /* less equal */
%token EOF
%token DO
%token SKIP
%token ASSIGN
%token <string> VAR 
%token <int> CONST 
%token SEQ
%token SEQ2
%token INTVAR

%start <cmd> prog

%left SEQ
%left SEQ2
%left AND
%left OR
%left NOT
%nonassoc ELSE
%nonassoc DO
%nonassoc EQ
%nonassoc LEQ
%left LCPAREN
%left RCPAREN


/* a && b && c */

%%

prog:
  | e = cmd EOF { e }
;

expr:
  | e1=VAR { Var(e1) } 
  | e1=CONST { Const(e1) }
  | TRUE { True }
  | FALSE { False }
  | LPAREN e=expr RPAREN { e }
  | e1=expr AND e2=expr { And(e1, e2) }
  | e1=expr OR e2=expr { Or(e1, e2) }
  | NOT e=expr; { Not(e) }
  | e1=expr ADD e2=expr { Add(e1, e2) }
  | e1=expr SUB e2=expr { Sub(e1, e2) }
  | e1=expr MUL e2=expr { Mul(e1, e2) }
  | e1=expr EQ e2=expr { Eq(e1, e2) }
  | e1=expr LEQ e2=expr { Leq(e1, e2) }
;

decl:
  | INTVAR v=VAR SEQ { IntVar(v) }
;

cmd:
  | SKIP { Skip }
  | LPAREN c=cmd RPAREN { c }
  | v=VAR ASSIGN e=expr { Assign(v, e) }
  | IF e=expr THEN c1=cmd ELSE c2=cmd { If(e, c1, c2) }
  | c1=cmd SEQ c2=cmd { Seq(c1, c2) }
  | WHILE e=expr DO c=cmd { While(e, c) }
  | LCPAREN c=cmd RCPAREN { Decl([], c) }
  | LCPAREN dl=list(decl) c=cmd RCPAREN { Decl(dl, c) }
;