{
  open Parser
}

(* useful regular expressions *)
let number = ['0'-'9']+
let bool = "true"|"false"
let id = ['a'-'z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_' ''']* (* we get as close to OCaml's allowed variable names *)

rule token = parse
  | [' ' '\t' '\n']   { token lexbuf }
  | '+'               { PLUS }
  | '*'               { TIMES }
  | '/'	              { DIV }
  | '-'               { MINUS }
  | "()"              { UNIT }
  | '('               { LPAREN }
  | ')'               { RPAREN }
  | "begin"           { BEGIN }
  | "end"             { END }
  | ">="              { GEQ }
  | "<="              { LEQ }
  | "<>"              { NEQ }
  | "<"	              { LT }
  | ">"	              { GT }
  | "="	              { EQ }
  | "||"              { OR }
  | "&&"              { AND }
  | number as s       { INT (int_of_string s) }
  | bool as b  	      { BOOL (bool_of_string b) } 
  | "if"      	      { IF }
  | "then"            { THEN }
  | "else"            { ELSE }
  | "let"             { LET }
  | "in"              { IN }
  | ";;"              { PVPV }
  | ';'	              { PV }
  | "fun"             { FUN }
  | "->"              { MAPSTO }
  | "rec"             { REC }
  | "!"               { DEREF }
  | ":="              { ASS }
  | ","	              { COMMA }
  | '_'	              { WILDCARD } (* note : we transform _ BEFORE id, which means "_" will never be parsed as a valid variable identificator (useful for patterns) *)
  | "try"             { TRY }
  | "with"            { WITH }
  | "when"            { WHEN }
  | "E"               { E }
  | "|"               { PIPE }
  | "match"           { MATCH }
  | "["               { LBRA }
  | "]"               { RBRA }
  | "::"              { CONS }
  | "@"               { CONC }
  | "function"        { FUNCTION }
  | id as x           { ID x }
  | eof               { EOF }