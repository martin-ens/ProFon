open Typedef

let rec print_ty (t : ty) =
  (* prints type t to stdout in ASCII *)
  match t with
  | TB a -> print_string a
  | Bot -> print_string "False"
  | Top -> print_string "True"
  | TF (a, b) -> (
      match b with
      | Bot -> (
          match a with
          | TB _ | Top | Bot ->
              print_string "~";
              print_ty a
          | _ ->
              print_string "~(";
              print_ty a;
              print_string ")")
      | _ ->
          (match a with
          | TF (_, x) when x <> Bot ->
              print_string "(";
              print_ty a;
              print_string ")"
          | _ -> print_ty a);
          print_string " -> ";
          print_ty b)
  | And (a, b) -> (
      (match a with
      | TF (_, x) when x <> Bot ->
          print_string "(";
          print_ty a;
          print_string ")"
      | Or (_, _) ->
          print_string "(";
          print_ty a;
          print_string ")"
      | _ -> print_ty a);
      print_string " /\\ ";
      match b with
      | TF (_, x) when x <> Bot ->
          print_string "(";
          print_ty b;
          print_string ")"
      | Or (_, _) ->
          print_string "(";
          print_ty b;
          print_string ")"
      | _ -> print_ty b)
  | Or (a, b) -> (
      (match a with
      | TF (_, x) when x <> Bot ->
          print_string "(";
          print_ty a;
          print_string ")"
      | _ -> print_ty a);
      print_string " \\/ ";
      match b with
      | TF (_, x) when x <> Bot ->
          print_string "(";
          print_ty b;
          print_string ")"
      | _ -> print_ty b)

let rec print_lam (m : lam) =
  (* prints lambda-term m to stdout in ASCII *)
  match m with
  | Var x -> print_string x
  | App (m1, m2) -> (
      (match m1 with
      | Fun (_, _, _) ->
          print_string "(";
          print_lam m1;
          print_string ")"
      | _ -> print_lam m1);
      print_string " ";
      match m2 with
      | Fun (_, _, _) | App (_, _) ->
          print_string "(";
          print_lam m2;
          print_string ")"
      | _ -> print_lam m2)
  | Exf (m1, t) ->
      print_string "exf(";
      print_lam m1;
      print_string ":";
      print_ty t;
      print_string ")"
  | Fun (x, a, m1) ->
      print_string "fun (";
      print_string x;
      print_string ":";
      print_ty a;
      print_string ") => ";
      print_lam m1
  | Any a ->
      print_string "any(";
      print_ty a;
      print_string ")"
  | I -> print_string "I"
  | Cpl (m1, n1) ->
      print_string "(";
      print_lam m1;
      print_string ", ";
      print_lam n1;
      print_string ")"
  | Fst m1 ->
      print_string "fst(";
      print_lam m1;
      print_string ")"
  | Snd m1 ->
      print_string "snd(";
      print_lam m1;
      print_string ")"
  | Ig (m1, a) ->
      print_string "ig(";
      print_lam m1;
      print_string ", ";
      print_ty a;
      print_string ")"
  | Id (m1, a) ->
      print_string "id(";
      print_lam m1;
      print_string ", ";
      print_ty a;
      print_string ")"
  | Case (m1, n, n') ->
      print_string "case(";
      print_lam m1;
      print_string ", ";
      print_lam n;
      print_string ", ";
      print_lam n';
      print_string ")"

let rec print_other_goals (q : (gam * ty * (lam -> lam) * tactic) list) =
  (* prints the subgoals different from the current one in q *)
  match q with
  | [] -> ()
  | (_, a, _, _) :: r ->
      print_newline ();
      print_ty a;
      print_other_goals r

let rec print_env (e : gam) =
  (* prints the contents of environment e *)
  match e with
  | [] -> ()
  | (x, a) :: q ->
      print_newline ();
      print_string (x ^ " : ");
      print_ty a;
      print_env q

let print_proof (p : proof_state) =
  (* prints the current state of the proof p *)
  match p with
  | End _ -> print_string "\027[32mNo more subgoals remaining.\027[0m"
  | Subgoals ([], _) -> ()
  | Subgoals ((env, a, _, _) :: q, n) ->
      print_string "\027[32m";
      print_int n;
      print_string
        (" subgoal"
        ^ (if n = 1 then "" else "s")
        ^ " remaining.\027[0m\nCurrent subgoal:\n");
      print_env env;
      print_string "\n=====================================================\n";
      print_ty a;
      if q <> [] then print_string "\n\nOther subgoals:";
      print_other_goals q

let display_help (t : tactic) =
  (* prints the help associated to tactic t *)
  match t with
  | Help _ ->
      print_string
        "Here is a list of tactics and commands and how to use them. Use Help \
         [tactic/command]. for specific info on how to use a tactic or \
         command.\n\n\
         - Help [opt arg]. : Displays this menu.\n\
         - Exit. : Quits the proof session.\n\
         - Print. : Prints the current proof to stdout.\n\
         - Qed. : Finishes the proof if there is no subgoal left.\n\
         - Admitted. : Finishes the proof by admitting it without further \
         notice.\n\
         - admit. : Finishes the current subgoal by admitting it. The proof \
         will require Admitted to finish.\n\
         - assumption. : Finishes the current subgoal if it occurs as a \
         hypothesis.\n\
         - exact [t]. : Finishes the current subgoal if the lambda-term t's \
         type corresponds to the subgoal.\n\
         - intro [opt arg]. : Introduces the implication's premise as a \
         hypothesis if there is one in the current subgoal.\n\
         Has an optional argument: the name of the hypothesis.\n\
         - intros [opt args]. : Performs multiple intro.'s at once.\n\
         Has optional arguments: the name of the hypotheses. With no \
         arguments, intro. is performed while possible.\n\
         - cut [A]. : Uses the rule of elimination of the implication with the \
         formula A.\n\
         - apply [h]. : Applies hypothesis h to the current subgoal if it \
         appears as a conclusion in h.\n\
         - absurd [A]. : Uses the rule of elimination of False by reverting to \
         proving formulas A and ~A.\n\
         - exfalso. : Reverts to proving False by using the logical principle \
         `ex falso quod libet`.\n\
         - elim [h]. : Uses the induction principle on the conclusion of \
         hypothesis h, adding eventual premises as subgoals.\n\
         - split. : Splits a subgoal of the form A /\\ B into two subgoals A \
         and B.\n\
         - left. : Reverts to proving the left formula A of a subgoal of the \
         form A \\/ B.\n\
         - right. : Reverts to proving the right formula B of a subgoal of the \
         form A \\/ B.\n"
  | Exit ->
      print_string
        "Quits the interactive \027[36m𝓞𝓬𝓽𝓸𝓹𝓻𝓸𝓸𝓯©\027[0m session right away, \
         by exiting with code 0.\n\
         This tactic does not save anything before exiting.\n"
  | Intro | IntroName _ ->
      print_string
        "Uses the rule of introduction of the implication, therefore \
         transforming A -> B to B with A added to the current environment.\n\
         For instance:\n\n\
        \                                      h : A\n\
         ==============================   ->   ============================== \n\
         A -> B -> (C -> A) -> D               B -> (C -> A) -> D\n\n\
         intro may also be used with an argument: the name of the hypothesis.\n\
         For instance: intro h42. names the newly added hypothesis h42.\n\
         Note that if the argument is already the name of a hypothesis, the \
         old hypothesis is overwritten.\n\
         The tactic does nothing if there is no implication in the current goal.\n"
  | Intros | IntrosNames _ ->
      print_string
        "Performs multiple intro.'s at once.\n\
         With no arguments, intro. is repeated while possible and names \
         hypotheses with the next available name starting with `h`.\n\
         For instance:\n\n\
        \                                      h : A\n\
        \                                      h0 : B\n\
        \                                      h2 : C\n\
        \                                      h3 : A -> B\n\
         h1 : B                                h1 : B\n\
         ==============================   ->   ============================== \n\
         A -> B -> C -> (A -> B) -> D          D\n\
         With k arguments, intros x1 x2 ... xk is almost equivalent to intro \
         x1. intro x2. ... intro xk.\n\
         The exception is if one of the variables cannot be introduced, in \
         which case none of them will be introduced.\n\
         See also intro. for more info.\n"
  | Cut _ ->
      print_string
        "Uses the rule of elimination of the implication. For instance, cut A. \
         would do:\n\n\
         h : C                  h : C             h : C\n\
         ===============   ->   =============== + ===============\n\
         B                      A -> B            A\n\
         Note that this rule can always be applied, and increments the number \
         of subgoals by one.\n"
  | Apply _ ->
      print_string
        "Uses the rule of elimination of the implication with the name of a \
         hypothesis as an argument.\n\
         The tactic will try to find the current subgoal as the conclusion of \
         a series of implications in the hypothesis given.\n\
         If it succeeds, every formula encountered in the series of \
         implications will be added as a subgoal, with the current environment.\n\
         For instance when using apply h. :\n\n\
         h : A -> (B -> A) -> D -> A -> C\n\
         ===================================== -> Subgoals remaining: A ; B -> \
         A ; D ; A\n\
         C\n\n\
         Note that if the hypothesis h given is equal to the subgoal wanted, \
         it can be seen as an empty series of implications.\n\
         Therefore, apply h. generates an empty series of subgoals, i.e. acts \
         like exact h.\n\
         If the current subgoal is not at the end of h, the tactic fails.\n"
  | Assumption ->
      print_string
        "Finishes the current subgoal if it occurs as a hypothesis in the \
         current environment.\n\
         If it does not appear, the tactic fails.\n"
  | Exact _ ->
      print_string
        "Finishes the current subgoal if the lambda-term put as argument can \
         be typed with the goal type in the current environment.\n\
         Note that the name of a hypothesis is the name of a variable, thus \
         you can call exact h. for any hypothesis h.\n\
         If the lambda-term has the wrong type or cannot be typed, the tactic \
         fails.\n"
  | Qed ->
      print_string
        "Finishes the proof when there is no subgoal remaining.\n\
         If there is at least one subgoal remaining, the tactic fails.\n\
         If it succeeds, the lambda-term constructed during the proof is \
         reduced, then typechecked, and displayed.\n\
         In that case, a file containing the tactics used may be saved.\n"
  | Print ->
      print_string
        "Prints the current proof to stdout.\n\
         Also prints the lambda-term constructed during the subgoal, with [?] \
         where the current subgoal needs a term.\n\
         If there is no subgoal left, the entire lambda-term is printed with \
         no [?].\n"
  | Admit ->
      print_string
        "Admits the current subgoal by generating a placeholder lambda-term \
         `any` of goal type.\n\
         When trying to finish the proof, it will be required to use Admitted \
         instead of Qed.\n"
  | Admitted ->
      print_string
        "Finishes the proof by calling it admitted. Required when the tactic \
         admit. was used.\n\
         This command can be called at any time in the proof (even if admit. \
         was not used), and will end the proof without generating a \
         lambda-term.\n"
  | Absurd _ ->
      print_string
        "Uses the elimination of False, generating two subgoals A and ~A with \
         the same environment,\n\
         where A is the formula put as argument. For instance, absurd A. would \
         do:\n\n\
         h : B                  h : B             h : B\n\
         ===============   ->   =============== + ===============\n\
         C                      A                 ~A\n\
         Note that this rule can always be applied, and increments the number \
         of subgoals by one.\n"
  | Exfalso ->
      print_string
        "Implements the `ex falso quod libet` logical principle by \
         transforming the current subgoal to False with the same environment.\n\
         For instance:\n\n\
         h : A                    h : A\n\
         =================   ->   =================\n\
         B                        False\n"
  | Elim _ ->
      print_string
        "Uses the principle of induction of the conclusion of hypothesis h put \
         as argument when h is a (possibly empty) series of implications.\n\
         The premises of this implication are then added as new subgoals.\n\
         In practice this applies to respectively False, True, /\\ and \\/ as \
         follows:\n\n\
         h : A -> B -> False           h : A -> B -> False      h : A -> B -> \
         False\n\
         ======================   ->   ====================== + \
         ======================\n\
         C                             A                        B\n\n\
         h : A -> B -> True            h : A -> B -> True       h : A -> B -> \
         True       h : A -> B -> True\n\
         ======================   ->   ====================== + \
         ====================== + ======================\n\
         C                             A                        \
         B                        C\n\n\
         h : A -> B -> X /\\ Y          h : A -> B -> X /\\ Y     h : A -> B \
         -> X /\\ Y     h : A -> B -> X /\\ Y\n\
         ======================   ->   ====================== + \
         ====================== + ======================\n\
         C                             A                        \
         B                        X -> Y -> C\n\n\
         h : A -> B -> X \\/ Y          h : A -> B -> X \\/ Y     h : A -> B \
         -> X \\/ Y     h : A -> B -> X \\/ Y     h : A -> B -> X \\/ Y\n\
         ======================   ->   ====================== + \
         ====================== + ====================== + \
         ======================\n\
         C                             A                        \
         B                        X -> C                   Y -> C\n\n\
         In case the conclusion of h is not among False, True, /\\ or \\/, the \
         tactic fails.\n"
  | Split ->
      print_string
        "Uses the rule of introduction of /\\ by splitting a conjunction into \
         its two parts.\n\
         For instance:\n\n\
         h : C                  h : C             h : C\n\
         ===============   ->   =============== + ===============\n\
         A /\\ B                 A                 B\n\n\
         If the current subgoal is not a conjunction, the tactic fails.\n"
  | Left ->
      print_string
        "Uses the left rule of introduction of \\/ by reverting to proving the \
         left formula of a disjunction.\n\
         For instance:\n\n\
         h : C                  h : C\n\
         ===============   ->   ===============\n\
         A \\/ B                 A\n\n\
         If the current subgoal is not a disjunction, the tactic fails. See \
         also right.\n"
  | Right ->
      print_string
        "Uses the right rule of introduction of \\/ by reverting to proving \
         the right formula of a disjunction.\n\
         For instance:\n\n\
         h : C                  h : C\n\
         ===============   ->   ===============\n\
         A \\/ B                 B\n\n\
         If the current subgoal is not a disjunction, the tactic fails. See \
         also left.\n"

let print_error (e : exn) =
  (* prints the adequate error message for exception e *)
  match e with
  | NoMoreGoals ->
      print_string "\n\027[33mInvalid tactic:\027[0m No more goals to prove.\n"
  | NotProven ->
      print_string
        "\n\027[33mInvalid tactic:\027[0m There are unproven goals remaining.\n"
  | IncorrectType (m, a) ->
      print_string "\n\027[33mInvalid:\027[0m ";
      print_lam m;
      print_string " cannot be typed with type ";
      print_ty a;
      print_string " in the current environment.\n"
  | NotUnifiable (t, g) ->
      print_string "\n\027[33mInvalid:\027[0m ";
      print_ty t;
      print_string " cannot be unified with ";
      print_ty g;
      print_string " in the current environment.\n"
  | InternalError ->
      print_string "\n\027[31mError:\027[0m Internal error.\n";
      Sys.remove "SavedProofs/proof.8pus";
      exit 1
  | IncorrectTactic ->
      print_string
        "\n\027[33mInvalid tactic:\027[0m Cannot be applied to current goal. \n"
  | GivenUpGoals ->
      print_string
        "\n\
         \027[33mInvalid:\027[0m Attempt to save proof with given up goals.\n\
         If this is really what you want to do, use Admitted. instead.\n"
  | NotAnAssumption ->
      print_string "\n\027[33mInvalid:\027[0m Not an assumption.\n"
  | _ -> print_string "\n\027[33mInvalid:\027[0m Syntax error.\n"
