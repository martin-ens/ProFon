{
  open Parser
}

(* useful regular expressions *)
let number = ['0'-'9']+
let bool = "true"|"false"
let id = ['a'-'z']+['0'-'9']* 
let ty_id = ['A'-'Z']+['0'-'9']*

rule token = parse
(* special characters *)
  | [' ' '\t']        { token lexbuf }
  | '\n'              { EOL }
  | eof               { EOF }
  | '('               { LPAREN }
  | ')'               { RPAREN }
  | ","               { COMMA }
  | "."               { DOT }
  | "&"               { ESP }

(* lexing of lambda-terms *)
  | "fun"             { FUN }
  | ":"               { COLON }
  | "exf"             { EXF }
  | "I"               { I }
  | "=>"              { IMP }
  | "fst"             { FST }
  | "snd"             { SND }
  | "ig"              { IG }
  | "id"              { IDR }
  | "case"            { CASE }

(* lexing of types *)
  | "False"           { BOT }
  | "True"            { TOP }
  | "->"              { MAPSTO }
  | "/\\"             { AND }
  | "\\/"             { OR }
  | "~"               { NOT }

(* lexing of tactics *)
  | "Goal"            { GOAL }
  | "intro"           { INTRO }
  | "intros"          { INTROS }
  | "exact"           { EXACT }
  | "Qed"             { QED }
  | "apply"           { APPLY }
  | "cut"             { CUT }
  | "assumption"      { ASMP }
  | "Help"            { HELP }
  | "Exit"            { EXIT }
  | "Print"           { PRINT }
  | "admit"           { ADMIT }
  | "Admitted"        { ADMITTED }
  | "exfalso"         { EXFALSO }
  | "absurd"          { ABSURD }
  | "elim"            { ELIM }
  | "split"           { SPLIT }
  | "left"            { LEFT }
  | "right"           { RIGHT }
  
(* variable/ type identificators *)
  | id as x           { ID x }
  | ty_id as a        { TY a }
