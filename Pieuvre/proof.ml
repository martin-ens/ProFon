open Calculus
open Typedef
open Display

let replace_function (m : lam) (t : tactic) (f : lam -> lam) =
  (* - f = hole function of the current subgoal
     - m = lambda-term obtained at the end of the former subgoal
     - t = tactic used just before the current subgoal
     Thus, m is the result of the first branch of a proof that divided itself (elimination of ->,
     introduction of ∧ ...) and replace_function evaluates what t is in order to replace f
     with the right function in the proof process, taking m into account (see the report for more info)
  *)
  match t with
  | Cut _ | Apply _ -> fun x -> f (App (m, x))
  | Absurd _ -> fun x -> f (App (x, m))
  | Split -> fun x -> f (Cpl (m, x))
  | Elim "And" -> fun x -> f (App (App (x, Fst m), Snd m))
  | Elim "Or1" ->
      fun x -> App (m, x)
      (* a cheesy way to store the info about m which is picked up in Or2.
         It's not pretty but it works *)
  | Elim "Or2" -> (
      match m with
      | App (m', n) ->
          fun x -> f (Case (m', n, x)) (* the aforementioned pick up of m' *)
      | _ -> raise InternalError)
  | _ -> f

let new_hyp (x : id) (a : ty) (env : gam) =
  (* deletes any hypothesis named x in current environment env and adds (x : a) *)
  let rec del l =
    match l with
    | [] -> []
    | (y, _) :: q when y = x -> q
    | (y, b) :: q -> (y, b) :: del q
  in
  (x, a) :: del env

let rec assoc2 (a : 'b) (l : ('a * 'b) list) =
  (* the exact same thing as built-in function List.assoc, except here it is
     the second element of the couples that is sought out *)
  match l with
  | [] -> raise Not_found
  | (x, y) :: _ when a = y -> x
  | _ :: q -> assoc2 a q

let rec proof_step (a : ty) (p : proof_state) (t : tactic) =
  (* returns a couple containing
     - a bool indicating whether to print the changes or not
     - the updated version of p after the tactic t is used
     If applying t has ended the last subgoal (e.g. with exact or assumption),
     the final lambda-term is returned instead *)
  let rec intros_aux (pr : proof_state) (l : id list option) =
    (* auxiliary function for the intros tactic
       l contains the list of names used in IntrosNames,
       or is None if Intros is performed instead of IntrosNames *)
    match l with
    | None -> (
        match pr with
        | End _ | Subgoals ([], _) -> raise InternalError
        | Subgoals ((_, TF (_, _), _, _) :: _, _) ->
            let pro = snd (proof_step a pr Intro) in
            intros_aux pro None
        | Subgoals ((_, _, _, _) :: _, _) -> pr)
    | Some [] -> pr
    | Some (x :: q) -> (
        match pr with
        | End _ | Subgoals ([], _) -> raise InternalError
        | Subgoals ((_, TF (_, _), _, _) :: _, _) ->
            let pro = snd (proof_step a pr (IntroName x)) in
            intros_aux pro (Some q)
        | Subgoals ((_, _, _, _) :: _, _) -> raise IncorrectTactic)
  in

  (* =========== beginning of the tactics matching =========== *)
  match p with
  (* End m : a lambda-term m corresponding to the original goal a was constructed
     hence, normal tactics cannot be applied since there are no more goals *)
  | End m -> (
      match t with
      | Qed ->
          if contains_admit m then raise GivenUpGoals
          else
            let m' = normalize m in
            if typecheck [] m' a then (
              print_string
                "\n\
                 \027[36mProof finished. Congratulations!\n\n\
                 \027[0mHere is the lambda-term with type ";
              print_ty a;
              print_string " generated:\n";
              print_lam m';
              print_string ".\n";
              flush stdout;
              (true, Subgoals ([], 0)))
            else raise InternalError
      (* when a proof is admitted, a lambda-term was constructed, but some of its sub-terms may be replaced with any(a:ty) *)
      | Admitted ->
          let m' = normalize m in
          if typecheck [] m' a then
            print_string
              "\n\
               \027[33mProof admitted. \n\n\
               \027[0mHere is the resulting incomplete lambda-term with type ";
          print_ty a;
          print_string " generated:\n";
          print_lam m;
          print_string ".\n";
          flush stdout;
          (true, Subgoals ([], 0))
      | Help t' ->
          display_help t';
          (false, p)
      | Exit ->
          print_string "\nGoodbye!\n";
          flush stdout;
          Sys.remove "SavedProofs/proof.8pus";
          exit 0
      | Print ->
          print_newline ();
          print_proof p;
          print_string "\n\n";
          print_lam m;
          print_newline ();
          flush stdout;
          (false, p)
      | _ -> raise NoMoreGoals)
  (* in theory, the list of subgoals is never empty because as soon as the last subgoal is proved, the return type is End(bla) *)
  | Subgoals ([], _) -> raise InternalError
  (* most general case : there is at least one subgoal left *)
  | Subgoals ((env, g, f, _) :: q, n) -> (
      match t with
      | Qed -> raise NotProven
      | Admitted ->
          print_string "\n\027[33mProof admitted. \n\n\027[0m";
          (true, Subgoals ([], 0))
      | Help t' ->
          print_newline ();
          display_help t';
          (false, p)
      | Exit ->
          print_string "\nGoodbye!\n";
          flush stdout;
          Sys.remove "SavedProofs/proof.8pus";
          exit 0
      (* for exact and assumption, the hole function of the next subgoal is changed via replace_function *)
      | Exact m -> (
          match q with
          | [] ->
              if typecheck env m g then (true, End (f m))
              else raise (IncorrectType (m, g))
          | (env', g', f', tac') :: q' ->
              if typecheck env m g then
                ( true,
                  Subgoals
                    ( (env', g', replace_function (f m) tac' f', tac') :: q',
                      n - 1 ) )
              else raise (IncorrectType (m, g)))
      | Assumption -> (
          match q with
          | [] -> (
              try
                let x = assoc2 g env in
                (true, End (f (Var x)))
              with Not_found -> raise NotAnAssumption)
          | (env', g', f', tac') :: q' -> (
              try
                let x = assoc2 g env in
                ( true,
                  Subgoals
                    ( (env', g', replace_function (f (Var x)) tac' f', tac')
                      :: q',
                      n - 1 ) )
              with Not_found -> raise NotAnAssumption))
      | Intro -> (
          match g with
          | TF (c, b) ->
              let x = next_id "h" (List.map fst env) in
              ( true,
                Subgoals
                  ( ((x, c) :: env, b, (fun t -> f (Fun (x, c, t))), Intro) :: q,
                    n ) )
          | _ -> raise IncorrectTactic)
      | IntroName x -> (
          match g with
          | TF (c, b) ->
              ( true,
                Subgoals
                  ( (new_hyp x c env, b, (fun t -> f (Fun (x, c, t))), Intro)
                    :: q,
                    n ) )
          | _ -> raise IncorrectTactic)
      | Intros ->
          let pr = snd (proof_step a p Intro) in
          (true, intros_aux pr None)
      | IntrosNames l -> (true, intros_aux p (Some l))
      | Apply h -> (
          let v = List.assoc h env in
          let rec apply_aux (z : ty) =
            (* complicated auxiliary function for apply (see report for a detailed explanation) *)
            match z with
            | base when base = g -> (
                match q with
                | [] -> (false, End (f (Var h)))
                | (env', g', f', tac') :: q' ->
                    ( false,
                      Subgoals
                        ( (env', g', replace_function (f (Var h)) tac' f', tac')
                          :: q',
                          n - 1 ) ))
            | TF (b, c) when c = g ->
                (true, Subgoals ((env, b, f, Apply h) :: q, n))
            | TF (b, c) -> (
                let l = apply_aux c in
                match l with
                | _, End _ -> raise InternalError
                | _, Subgoals (q', k) ->
                    ( true,
                      Subgoals ((env, b, (fun x -> x), Apply h) :: q', k + 1) ))
            | _ -> raise (NotUnifiable (z, g))
            (* the hole function f' of the last subgoal created using apply (the term on the far left in the series of ->)
               must be changed in order to keep the info on h, but only in case there was an actual ->,
               hence the boolean values returned by apply_aux, not to be confused with the boolean values returned by proof_step
               which are used for deciding whether or not to print the new proof state *)
          in

          match apply_aux v with
          | false, l -> (true, l)
          | _, Subgoals ([], _) | true, End _ -> raise InternalError
          | _, Subgoals ((env', g', f', tac') :: q', k) ->
              ( true,
                Subgoals
                  ((env', g', (fun x -> f' (App (Var h, x))), tac') :: q', k) ))
      | Cut b ->
          ( true,
            Subgoals
              ( (env, TF (b, g), (fun x -> x), Cut b) :: (env, b, f, Cut b) :: q,
                n + 1 ) )
      | Print ->
          print_newline ();
          print_proof p;
          print_string "\n\n";
          print_lam (f (Var "[?]"));
          print_newline ();
          flush stdout;
          (false, p)
      | Admit -> (
          match q with
          | [] -> (true, End (f (Any g)))
          | (env', g', f', tac') :: q' ->
              ( true,
                Subgoals
                  ( (env', g', replace_function (Any g) tac' f', tac') :: q',
                    n - 1 ) ))
      | Exfalso ->
          ( true,
            Subgoals ((env, Bot, (fun x -> f (Exf (x, g))), Exfalso) :: q, n) )
      | Absurd a' ->
          ( true,
            Subgoals
              ( (env, a', (fun x -> x), Absurd a')
                :: (env, TF (a', Bot), (fun x -> f (Exf (x, g))), Absurd a')
                :: q,
                n + 1 ) )
      | Elim h -> (
          let v = List.assoc h env in
          (* this case is similar to apply since it also goes down a series of -> *)
          let rec elim_aux (z : ty) =
            match z with
            | And (a, b) ->
                (false, (env, TF (a, TF (b, g)), f, Elim "And") :: q, n)
            | Or (a, b) ->
                ( false,
                  (env, TF (a, g), (fun x -> x), Elim "Or1")
                  :: (env, TF (b, g), f, Elim "Or2")
                  :: q,
                  n + 1 )
            | Bot -> (false, q, n - 1)
            | Top -> (false, (env, g, f, Elim "Top") :: q, n)
            | TF (a, b) ->
                let _, q', k = elim_aux b in
                ( true,
                  ( env,
                    a,
                    (if k = n - 1 then fun x -> f (Exf (x, g)) else fun x -> x),
                    Apply h )
                  :: q',
                  k + 1 )
            | TB _ -> raise IncorrectTactic
          in
          match elim_aux v with
          | _, _, k when k = n - 1 ->
              (true, End (f (Exf (Var h, g))))
              (* elim False is treated separately since it can end the proof *)
          | true, (env', g', f', tac') :: q', k ->
              ( true,
                Subgoals
                  ((env', g', (fun x -> f' (App (Var h, x))), tac') :: q', k) )
              (* like apply_aux *)
          | false, (env', g', f', tac') :: q', k ->
              ( true,
                Subgoals
                  ( ( env',
                      g',
                      (match tac' with
                      | Elim "And" ->
                          fun x -> f' (App (App (x, Fst (Var h)), Snd (Var h)))
                      | Elim "Or1" -> fun x -> App (Var h, x)
                      | _ -> f'),
                      tac' )
                    :: q',
                    k ) )
          | _ -> raise InternalError)
      | Split -> (
          match g with
          | And (b, c) ->
              ( true,
                Subgoals
                  ( (env, b, (fun t -> t), Split) :: (env, c, f, Split) :: q,
                    n + 1 ) )
          | _ -> raise IncorrectTactic)
      | Left -> (
          match g with
          | Or (b, c) ->
              (true, Subgoals ((env, b, (fun t -> f (Ig (t, c))), Left) :: q, n))
          | _ -> raise IncorrectTactic)
      | Right -> (
          match g with
          | Or (b, c) ->
              ( true,
                Subgoals ((env, c, (fun t -> f (Id (t, b))), Right) :: q, n) )
          | _ -> raise IncorrectTactic))

let rec proof_line (a : ty) (p : proof_state) (l : tactic list) =
  (* recursively applies proof_step a p to each tactic in l *)
  match l with
  | [] -> (true, p)
  | [ t ] -> proof_step a p t
  | t :: q ->
      let b', p' = proof_step a p t in
      let b'', p'' = proof_line a p' q in
      (b' || b'', p'')
