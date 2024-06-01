%{

open Typedef

%}


/* list of tokens */

%token EOL EOF
%token <string> ID TY
%token FUN COLON EXF LPAREN RPAREN MAPSTO
%token IMP BOT NOT GOAL
%token DOT ESP
%token HELP PRINT EXIT QED ADMIT ADMITTED
%token INTRO EXACT INTROS ASMP APPLY CUT
%token EXFALSO ABSURD ELIM
%token CASE COMMA IG IDR AND OR TOP FST SND I
%token SPLIT LEFT RIGHT

/* associativities */
%right MAPSTO
%right OR
%right AND
%right NOT




		    
%start main          
%start main_tactic
%start main_file
%type <Typedef.mode> main
%type <Typedef.mode> main_file
%type <Typedef.tactic list> main_tactic


%%

/* --- grammar rules --- */

/* main "surface" terms */ 
main:
  | m=term DOT EOL                                   { Red(m) }
  | m1=term ESP m2=term DOT EOL                      { Alph(m1, m2) }
  | m=term COLON a=types DOT EOL                     { Typ(m, a) }
  | GOAL a=types DOT EOL                             { Prf(a) }

/* lambda-terms */
term:                                                      
  | m=argexpr                                                      { m }
  | m1=evaluation m2=argexpr                                       { App(m1, m2) }
  | FUN LPAREN x=ID COLON a=types RPAREN IMP m=term                { Fun(x, a, m) } 
  | m1=argexpr FUN LPAREN x=ID COLON a=types RPAREN IMP m=term     { App(m1, Fun(x, a, m)) }
  | FST a=term                                                     { Fst(a) }
  | SND a=term                                                     { Snd(a) }
  | CASE LPAREN m1=term COMMA m2=term COMMA m3=term RPAREN         { Case(m1, m2, m3) }
  | IG LPAREN m=term COMMA b=types RPAREN                          { Ig(m, b) }
  | IDR LPAREN m=term COMMA a=types RPAREN                         { Id(m, a) }

  
evaluation:
  | m=argexpr                                        { m }
  | m1=evaluation m2=argexpr                         { App(m1, m2) }

/* sub-grammar for a list of variables, useful when implementing intros. */
idlist:
  | x=ID                                             { [x] }
  | x=ID q=idlist                                    { x::q }

/* expressions that are allowed in evaluation */
argexpr:
  | x=ID                                             { Var(x) }
  | LPAREN m=term RPAREN                             { m }
  | EXF LPAREN m=term COLON a=types RPAREN           { Exf(m, a) }
  | LPAREN a=term COMMA b=term RPAREN                { Cpl(a, b) }
  | I                                                { I }


types:
  | LPAREN a=types RPAREN                            { a }
  | a=TY                                             { TB(a) }
  | a=types MAPSTO b=types                           { TF(a, b) } 
  | BOT                                              { Bot }
  | NOT a=types                                      { TF(a, Bot) }
  | TOP                                              { Top }
  | a=types AND b=types                              { And(a, b) }
  | a=types OR b=types                               { Or(a, b) }


/* grammar variant when a file is put as argument */

main_file:
  | GOAL a=types DOT t=tactics_file                  { PrfFile(a, t) }

tactics_file:
  | t=tactic DOT t2=tactics_file                     { t::t2 }
  | EOL t2=tactics_file                              { t2 }
  | EOF                                              { [] }


/* tactics */
main_tactic:
  | t=tactic DOT m=main_tactic                       { t::m }
  | t=tactic DOT EOL                                 { [t] }

tactic:
  | INTRO                                            { Intro }
  | INTRO x=ID                                       { IntroName(x) }
  | EXACT m=term                                     { Exact(m) }
  | QED                                              { Qed }
  | ADMIT                                            { Admit }
  | ADMITTED                                         { Admitted }
  | INTROS                                           { Intros }
  | INTROS l=idlist                                  { IntrosNames(l) }
  | ASMP                                             { Assumption }
  | CUT a=types                                      { Cut(a) }
  | APPLY h=ID                                       { Apply(h) }
  | EXIT                                             { Exit }
  | PRINT                                            { Print }
  | ABSURD a=types                                   { Absurd(a) }
  | EXFALSO                                          { Exfalso }
  | ELIM h=ID                                        { Elim(h) }
  | SPLIT                                            { Split }
  | LEFT                                             { Left }
  | RIGHT                                            { Right }
  | h=help                                           { h }

help:
  | HELP t=tactic                                    { Help(t) }
  | HELP                                             { Help(Help(Intro)) } /* The Intro is dismissed, it serves as an arbirtary argument, since we want the general help menu */
  | HELP APPLY                                       { Help(Apply("x")) } /* Same thing for the following rules, we dismiss the arguments */
  | HELP EXACT                                       { Help(Exact(Var "x")) }
  | HELP CUT                                         { Help(Cut(TB "A")) }
  | HELP ABSURD                                      { Help(Absurd(TB "A")) }
  | HELP ELIM                                        { Help(Elim("x")) }
