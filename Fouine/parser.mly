%{

open Expr  

%}


/* list of tokens */
%token <int> INT
%token <bool> BOOL
%token <string> ID
%token LET IN PVPV
%token PLUS TIMES MINUS DIV
%token LPAREN RPAREN BEGIN END
%token IF THEN ELSE
%token GEQ LEQ LT GT EQ NEQ
%token AND OR
%token FUN MAPSTO REC
%token DEREF ASS UNIT PV
%token COMMA WILDCARD
%token TRY WITH E WHEN
%token PIPE MATCH FUNCTION
%token LBRA RBRA CONS CONC
%token EOF           /* end of file */


/* associativities */
%nonassoc IN MAPSTO
%right PV
%nonassoc ELSE
%right ASS
%left COMMA // we declare left associativity thus making tuples non-primitives : 1,2,3 is parsed as (1,2),3
%right OR
%right AND
%left PIPE
%left EQ NEQ LEQ GEQ GT LT
%right CONC
%right CONS
%left PLUS MINUS
%left TIMES DIV
%left E // E is given constructor associativity
%nonassoc UMINUS
		    
%start main            
%type <Expr.expr> main    

%%

/* --- grammar rules --- */

/* main "surface" expressions */
main:                 
  | e=expression EOF                                       { e }
  | EOF                                                    { Unit }
  | LET m=motif EQ e1=expression PVPV ma=main              { LetIn(m,e1,ma) } // in order to allow the variant syntax for let in
  | LET f=ID m=motif i=ident PVPV ma=main                  { LetIn(MVar f,Fun(m,i),ma) }
  | LET REC f=motif m=motif i=ident PVPV ma=main           { LetRec(f,Fun(m,i),ma) }
  | LET REC f=motif EQ e1=expression PVPV ma=main          { LetRec(f,e1,ma) }

/* normal expressions : with semicolon */
expression:
  | e=argexpr                          { e }

/* binary int operators */
  | e1=expression PLUS e2=expression   { BinIntOp(Add,e1,e2) }
  | e1=expression MINUS e2=expression  { BinIntOp(Min,e1,e2) }
  | e1=expression TIMES e2=expression  { BinIntOp(Mul,e1,e2) }
  | e1=expression DIV e2=expression    { BinIntOp(Div,e1,e2) }
  | MINUS e=expression %prec UMINUS    { BinIntOp(Min,ConstI 0, e) }

/* binary comparison operators */
  | e1=expression GEQ e2=expression    { BinCompOp(Geq,e1,e2) }
  | e1=expression LEQ e2=expression    { BinCompOp(Leq,e1,e2) }
  | e1=expression GT e2=expression     { BinCompOp(Gt,e1,e2) }
  | e1=expression LT e2=expression     { BinCompOp(Lt,e1,e2) }
  | e1=expression EQ e2=expression     { BinCompOp(Eq,e1,e2) }
  | e1=expression NEQ e2=expression    { BinCompOp(Neq,e1,e2) }

/* binary boolean operators */
  | b1=expression AND b2=expression    { BinBoolOp(And,b1,b2) }
  | b1=expression OR b2=expression     { BinBoolOp(Or,b1,b2) }

  | IF b=expression THEN e1=expression ELSE e2=expression      { IfThenElse(b,e1,e2) }
  | LET m=motif EQ e1=expression IN e2=expression              { LetIn(m,e1,e2) }

  | e1=evaluation e2=argexpr                                   { App(e1,e2) } // evaluation is only possible with argexpr (expressions that can be arguments)
  | FUN m=motif i=ident2                                       { Fun(m,i) }
  | LET f=ID m=motif i=ident IN e=expression                   { LetIn(MVar f,Fun(m,i),e) }
  | LET REC f=motif m=motif i=ident IN e2=expression           { LetRec(f,Fun(m,i),e2) }
  | LET REC f=motif EQ e1=expression IN e2=expression          { LetRec(f,e1,e2) }

  | e1=expression ASS e2=expression                            { Ass(e1, e2) }
  | e1=expression PV e2=expression                             { LetIn(MWC, e1, e2) } // the rule that differs with exprList

  | e1=expression COMMA e2=expression                          { Cpl(e1,e2) } // non-primitive tuples (see above)

  | e=expression CONS q=expression                             { Cons(e, q) } 
  | e1=expression CONC e2=expression                           { Conc(e1, e2) }
  | MATCH e=expression WITH l=motifMatch                       { MatchWith(e, l) }
  | MATCH e=expression WITH PIPE l=motifMatch                  { MatchWith(e, l) }
  | FUNCTION l=motifMatch                                      { Fun(MVar("x"), MatchWith(Var("x"), l)) } // function is immediately transformed using fun and match with
  | FUNCTION PIPE l=motifMatch                                 { Fun(MVar("x"), MatchWith(Var("x"), l)) }

  | E e=expression                                             { E(e) }
  | TRY e1=expression WITH l=motifMatch                        { TryWith(e1, l) } // two different rules since the first | is optional
  | TRY e1=expression WITH PIPE l=motifMatch                   { TryWith(e1, l) } // we added rich matching to try with, hence the motifMatch



/* expressions without semicolons that are used inside explicit lists 
   no further elaboration since the parsing is the same as above */
exprList:
  | e=argexpr                      { e }

  | e1=exprList PLUS e2=exprList   { BinIntOp(Add,e1,e2) }
  | e1=exprList MINUS e2=exprList  { BinIntOp(Min,e1,e2) }
  | e1=exprList TIMES e2=exprList  { BinIntOp(Mul,e1,e2) }
  | e1=exprList DIV e2=exprList    { BinIntOp(Div,e1,e2) }
  | MINUS e=exprList %prec UMINUS  { BinIntOp(Min,ConstI 0, e) }

  | e1=exprList GEQ e2=exprList    { BinCompOp(Geq,e1,e2) }
  | e1=exprList LEQ e2=exprList    { BinCompOp(Leq,e1,e2) }
  | e1=exprList GT e2=exprList     { BinCompOp(Gt,e1,e2) }
  | e1=exprList LT e2=exprList     { BinCompOp(Lt,e1,e2) }
  | e1=exprList EQ e2=exprList     { BinCompOp(Eq,e1,e2) }
  | e1=exprList NEQ e2=exprList    { BinCompOp(Neq,e1,e2) }

  | b1=exprList AND b2=exprList    { BinBoolOp(And,b1,b2) }
  | b1=exprList OR b2=exprList     { BinBoolOp(Or,b1,b2) }

  | IF b=exprList THEN e1=exprList ELSE e2=exprList     { IfThenElse(b,e1,e2) }
  | LET m=motif EQ e1=exprList IN e2=exprList           { LetIn(m,e1,e2) }

  | e1=evaluation e2=argexpr                            { App(e1,e2) }
  | FUN m=motif i=ident2                                { Fun(m,i) }
  | LET f=ID m=motif i=ident IN e=exprList              { LetIn(MVar f,Fun(m,i),e) }
  | LET REC f=motif m=motif i=ident IN e2=exprList      { LetRec(f,Fun(m,i),e2) }
  | LET REC f=motif EQ e1=exprList IN e2=exprList       { LetRec(f,e1,e2) }

  | e1=exprList ASS e2=exprList                         { Ass(e1, e2) }

  | e1=exprList COMMA e2=exprList                       { Cpl(e1,e2) }
  
  | e=exprList CONS q=exprList                          { Cons(e, q) }
  | e1=exprList CONC e2=exprList                        { Conc(e1, e2) }
  | MATCH e=exprList WITH l=motifMatch                  { MatchWith(e, l) }
  | MATCH e=exprList WITH PIPE l=motifMatch             { MatchWith(e, l) }
  | FUNCTION l=motifMatch                               { Fun(MVar "x", MatchWith(Var "x", l)) }
  | FUNCTION PIPE l=motifMatch                          { Fun(MVar "x", MatchWith(Var "x", l)) }

  | E e=exprList                                        { E(e) }
  | TRY e1=exprList WITH l=motifMatch                   { TryWith(e1, l) }
  | TRY e1=exprList WITH PIPE l=motifMatch              { TryWith(e1, l) }

/* grammar for patterns */
motif:
  | x=ID                       { MVar x }
  | n=INT                      { MInt n }
  | b=BOOL                     { MB b } 
  | m1=motif COMMA m2=motif    { MCpl(m1,m2) }
  | LBRA m=motifListInner RBRA { ML(m) }
  | LBRA RBRA                  { ML([]) }
  | m1=motif CONS m2=motif     { MCons(m1, m2) } 
  | WILDCARD                   { MWC }
  | UNIT                       { MUnit }
  | E m=motif                  { ME(m) }
  | LPAREN m=motif RPAREN      { m }

/* grammar for pattern matching */
motifMatch:
  | m=motif MAPSTO e=expression                                         { [(m, ConstB(true), e)] }                 
  | m=motif MAPSTO e=expression PIPE q=motifMatch                       { (m, ConstB(true), e)::q }
  | m=motif WHEN e1=expression MAPSTO e2=expression                     { [(m, e1, e2)] }                 
  | m=motif WHEN e1=expression MAPSTO e2=expression PIPE q=motifMatch   { (m, e1, e2)::q }


/* grammar for the inside of an explicit list (the empty list is treated on its own) */
listInner:
  | e=exprList                   { [e] } // inside a list, you cannot have expressions containing a sequence, hence exprList
  | e=exprList PV l=listInner    { e::l }

/* same but with patterns */
motifListInner:
  | m=motif                      { [m] }
  | m=motif PV l=motifListInner  { m::l }

/* first version of the inside for the allowed syntax for declaring a function : let f x1 x2 ... xn = e */
ident:
  | m=motif i=ident              { Fun(m,i) }
  | EQ e=expression              { e }

/* the other version : fun x1 x2 ... xn -> e */
ident2:
  | m=motif i=ident2             { Fun(m,i) }
  | MAPSTO e=expression          { e }

/* grammar for extended evaluation : e1 e2 ... en */
evaluation:
  | e1=evaluation e2=argexpr     { App(e1,e2) } 
  | e=argexpr                    { e }

/* grammar for expressions which can be passed directly as arguments */
argexpr:
  | LPAREN e=expression RPAREN   { e } // we want to be able to go back to normal expressions (even with semicolon) when going inside parentheses
  | BEGIN e=expression END       { e } // same for begin/end
  | i=INT                        { ConstI i }
  | x=ID                         { Var(x) }
  | b=BOOL                       { ConstB b }
  | DEREF e=argexpr              { Deref(e) }
  | UNIT                         { Unit }
  | LBRA l=listInner RBRA        { List(l) } // this is where we start to disallow expressions to contain a sequence (unless going inside parentheses c.f. above)
  | LBRA RBRA                    { List([]) }
