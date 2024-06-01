open Typedef
open Calculus
open Proof
open Display

(* useful refs *)
let file_name = ref ""
let reduce_mode = ref false
let alpha_mode = ref false
let typecheck_mode = ref false
let proof_mode = ref false
let where_from = ref stdin
let channel = ref stdout

(* some bash color codes *)
let teal = "\027[36m"
let purp = "\027[35m"
let blue = "\027[34m"
let red = "\027[31m"
let normal = "\027[0m"

let get_input () =
  let optlist =
    [
      ( "-reduce",
        Arg.Set reduce_mode,
        ": reduces the input lambda-term m up to its normal form if it exists.\n\
        \ Input format: `m.`\n" );
      ( "-alpha",
        Arg.Set alpha_mode,
        ": tells if the two given lambda-terms m1 and m2 are alpha-equivalent.\n\
        \ Input format: `m1 & m2.`\n" );
      ( "-typecheck",
        Arg.Set typecheck_mode,
        ": checks if the input lambda-term m can have input type A.\n\
        \ Input format: `m : A.`\n" );
    ]
  in
  let usage =
    "Usage: ./_build/default/pieuvre.exe [options] <file>. With no options, an \
     interactive proof session is started. Here is a list of options : "
  in
  Arg.parse optlist (fun s -> file_name := s) usage;
  match !file_name with
  | "" ->
      if !reduce_mode then
        if !alpha_mode || !typecheck_mode then raise TwoOptions
        else
          print_string
            ("\nReduce mode: enter a lambda-term to reduce.\n\n" ^ teal ^ ">>> "
           ^ normal)
      else if !alpha_mode then
        if !typecheck_mode then raise TwoOptions
        else
          print_string
            ("\n\
              Alpha mode: enter two lambda-terms to compare for \
              alpha-equivalence.\n\n" ^ teal ^ ">>> " ^ normal)
      else if !typecheck_mode then
        print_string
          ("\n\
            Typecheck mode: enter a lambda-term and the type you want to check \
            it has (or hasn't).\n\n" ^ teal ^ ">>> " ^ normal)
      else
        print_string
          ("\nWelcome to " ^ purp ^ "ｐ" ^ blue ^ "ｉ" ^ purp ^ "ｅ" ^ blue ^ "ｕ"
         ^ purp ^ "ｖ" ^ blue ^ "ｒ" ^ purp ^ "ｅ" ^ normal
         ^ ".\nYou are running the " ^ teal ^ "𝓞𝓬𝓽𝓸𝓹𝓻𝓸𝓸𝓯©" ^ normal
         ^ " version made by Loarwenn and m12pp.\n\
            Enter a goal to start.\n\n" ^ teal ^ ">>> " ^ normal);
      flush stdout;
      let lexbuf = Lexing.from_channel !where_from in
      let parse () = Parser.main Lexer.token lexbuf in
      ( Bytes.sub_string lexbuf.lex_buffer 0 lexbuf.lex_buffer_len,
        parse ()
        (* returns the raw string input into stdin as well as the parsed input *)
      )
  | s ->
      where_from := open_in s;
      let lexbuf = Lexing.from_channel !where_from in
      let parse () = Parser.main_file Lexer.token lexbuf in
      ("", parse ())

let rec save_inp () =
  (* small recursive input function to save the proof *)
  match read_line () with
  | "yes" ->
      print_string "Enter file name: ";
      let file = read_line () in
      Sys.rename "SavedProofs/proof.8pus" ("SavedProofs/" ^ file ^ ".8pus");
      print_string "Proof saved successfully in SavedProofs directory!\n"
  | "no" -> Sys.remove "SavedProofs/proof.8pus"
  | _ ->
      print_string "Please type `yes` or `no`: ";
      save_inp ()

let rec proof_inp (p : proof_state) (a : ty) (s : string) =
  (* gets the tactics input to prove overall goal a, and changes the proof state p,
     and writes the previous tactics' string s in the adequate channel for saving *)
  Printf.fprintf !channel "%s" s;
  try
    let lexbuf = Lexing.from_channel !where_from in
    let parse () = Parser.main_tactic Lexer.token lexbuf in
    match proof_line a p (parse ()) with
    | _, Subgoals ([], _) ->
        Printf.fprintf !channel "%s"
          (Bytes.sub_string lexbuf.lex_buffer 0 lexbuf.lex_buffer_len);
        close_out !channel;
        print_string "\nWould you like to save your proof? (yes/no) : ";
        save_inp ()
    | print, p' ->
        if print then (
          print_newline ();
          print_proof p';
          print_newline ());
        print_string ("\n" ^ teal ^ ">>>" ^ normal ^ " ");
        flush stdout;
        proof_inp p' a
          (Bytes.sub_string lexbuf.lex_buffer 0 lexbuf.lex_buffer_len)
  with e ->
    print_error e;
    print_string ("\n" ^ teal ^ ">>>" ^ normal ^ " ");
    flush stdout;
    proof_inp p a ""

let execute (s, i) =
  (* executes the input i with the right mode
     string s is used in case of an interactive proof to save the goal entered previously *)
  match i with
  | Red m ->
      if !reduce_mode then (
        print_string "Here is a series of reductions of ";
        print_lam m;
        print_string " :\n\n";
        reduce m;
        print_newline ())
      else raise WrongInput
  | Alph (m, m') ->
      if !alpha_mode then (
        print_lam m;
        print_string " and ";
        print_lam m';
        print_string
          ("are"
          ^ (if alpha m m' then " indeed" else " not")
          ^ " alpha-equivalent.\n\n"))
      else raise WrongInput
  | Typ (m, a) ->
      if !typecheck_mode then (
        print_lam m;
        print_string
          (" can"
          ^ (if typecheck [] m a then " indeed" else "not")
          ^ " be typed with type ");
        print_ty a;
        print_string ".\n\n")
      else raise WrongInput
  | Prf a ->
      if !typecheck_mode || !reduce_mode || !alpha_mode then raise WrongInput
      else (
        channel := open_out "SavedProofs/proof.8pus";
        Printf.fprintf !channel "%s" s;
        print_string
          "Proof started. Type Help. for a list of tactics/commands and how to \
           use them. Type Exit. to quit.\n";
        let p = Subgoals ([ ([], a, (fun x -> x), Qed) ], 1) in
        print_proof p;
        print_string (teal ^ "\n\n>>>" ^ normal ^ " ");
        flush stdout;
        proof_inp p a "")
  | PrfFile (a, t) -> (
      if !typecheck_mode || !reduce_mode || !alpha_mode then raise WrongInput
      else
        let p = Subgoals ([ ([], a, (fun x -> x), Qed) ], 1) in
        try
          print_proof (snd (proof_line a p t));
          print_string "\n\n"
        with e ->
          print_error e;
          print_string "\n\n")

(* main function *)
let run () =
  try
    let inp = get_input () in
    print_newline ();
    flush stdout;
    execute inp;
    flush stdout
  with
  | TwoOptions ->
      print_string
        (red ^ "Error:" ^ normal
       ^ " Two incompatible options were specified. \n\
          Use -help for more info.\n");
      exit 1
  | WrongInput ->
      print_string
        (red ^ "Error:" ^ normal ^ " The input does not fit the specified mode.");
      print_string "\nUse -help for more info.\n";
      exit 1
  | _ ->
      print_string
        (red ^ "Error:" ^ normal ^ " Syntax error.\nUse -help for more info.\n");
      exit 1

let _ = run ()
