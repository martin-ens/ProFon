open Affichage
open Eval
open Expr

let nom_fichier = ref ""

let recupere_entree () =
  let optlist = [
      ("-debug", Arg.Set verbose, "Enables debug mode." );
      ("-showsrc", Arg.Set src_code, "Displays the original code.")
    ] in
  
  let usage = "Usage : ./_build/default/main.exe [options] <file>. Here is a list of options : " in
  
  Arg.parse optlist (fun s -> nom_fichier := s) usage;
  try
    let where_from = match !nom_fichier with
      | "" -> stdin
      | s -> open_in s in
    let lexbuf = Lexing.from_channel where_from in
    let parse () = Parser.main Lexer.token lexbuf in
    parse () 
  with e -> (Printf.printf "Syntax error.\n"; raise e)

(* default error message for exceptions *)   
let kE v = match v with
  | VE i -> print_string ("Exception E("^(string_of_int i)^")\n") ; VE i
  | _ -> raise NotAnException

let executeK e =
  if !src_code then (affiche_code e ; print_newline ())
  else 
    begin
      if !verbose then
        (affiche_expr e ;
         print_newline() ;
         affiche_code e ; 
         print_newline ()) ;
      let _ = evalK e builtin_fun ((fun v -> v), kE) in ()
    end

(* main function *)
let run () =
  try
    let saisie = recupere_entree () in
    executeK saisie; flush stdout
  with
  | UnboundVariable(x) -> print_string ("\nError: Unbound value "^x^".\n") ; exit 1
  | NotACouple -> print_string "\nError: Attempt to use couple operation on a non-couple value.\n" ; exit 1
  | AttemptConvert(s1,s2) -> print_string ("\nError: Attempt to convert "^s1^" value to "^s2^".\n") ; exit 1
  | RefOverflow -> print_string ("\nError: Exceeded allocated memory for ref.\n") ; exit 1
  | NotAFunction -> print_string ("\nError: Attempt to apply expression to a non-function value.\n") ; exit 1
  | NotARef -> print_string ("\nError: Attempt to use ref operation on a non-ref value.\n") ; exit 1
  | NotAnException -> print_string ("\nError: Attempt to use exception operation on a non-exception value.\n") ; exit 1
  | MatchingFailure(m,v) -> print_string ("\nError: Failed to match motif "^(string_of_motif m 1)^" with value "^(string_of_val v)^".\n") ; exit 1
  | PartialMatch -> print_string "\nError: partial matching, missing at least one matching case.\n" ; exit 1
  | NotFunInLetRec -> print_string "\nError: Only functions are allowed in `let rec`.\n" ; exit 1
  | NotAList -> print_string "\nError: attempt to use :: on a non-list expression.\n" ; exit 1
  | IncorrectExnArg(m) -> print_string ("\nError: Incorrect exception argument : "^(string_of_motif m 1)^".\n") ; exit 1
  | CompFailure(x) -> print_string ("\nError: Comparison failure with "^x^" value.\n") ; exit 1

let _ = run ()
