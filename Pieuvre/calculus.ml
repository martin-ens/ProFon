open Typedef
open Display

let alpha (m1 : lam) (m2 : lam) =
  (* returns whether lambda-terms m1 and m2 are alpha-equivalent *)
  let rec aux m1 m2 l1 l2 nb =
    match (m1, m2) with
    | Var x, Var y ->
        let nb1 = try List.assoc x l1 with Not_found -> -1 in
        let nb2 = try List.assoc y l2 with Not_found -> -1 in
        if nb1 < 0 && nb2 < 0 then x = y
        else if nb1 >= 0 && nb2 >= 0 then nb1 = nb2
        else false
    | App (n1, n1'), App (n2, n2') -> aux n1 n2 l1 l2 nb && aux n1' n2' l1 l2 nb
    | Exf (n1, _), Exf (n2, _) -> aux n1 n2 l1 l2 nb
    | Fun (x, _, n1), Fun (y, _, n2) ->
        aux n1 n2 ((x, nb) :: l1) ((y, nb) :: l2) (nb + 1)
    | _ -> false
  in
  aux m1 m2 [] [] 0

let fv (m : lam) =
  (* returns a list containing the free variables of m *)
  let rec aux m bv =
    (* bv : list of bounded variables "from above"
       which means that for every Fun(x, ...) encountered, x is recursively added to bv *)
    match m with
    | Var x -> if List.mem x bv then [] else [ x ]
    | App (m1, m2) -> aux m1 bv @ aux m2 bv
    | Exf (m1, _) -> aux m1 bv
    | Fun (x, _, m1) -> aux m1 (x :: bv)
    | I -> []
    | Cpl (m1, m2) -> aux m1 bv @ aux m2 bv
    | Fst m1 -> aux m1 bv
    | Snd m1 -> aux m1 bv
    | Ig (m1, _) -> aux m1 bv
    | Id (m1, _) -> aux m1 bv
    | Case (m1, m2, m3) -> aux m1 bv @ aux m2 bv @ aux m3 bv
    | Any _ -> []
  in
  aux m []

let pref (x : id) =
  (* returns the letter part of x *)
  let rec aux x i =
    if i = String.length x || ('0' <= x.[i] && x.[i] <= '9') then i
    else aux x (i + 1)
  in
  String.sub x 0 (aux x 0)

let suff (x : id) =
  (* returns the int part of x if it exists and returns -1 otherwise *)
  let n = String.length x in
  let rec aux x i =
    if i = n || ('0' <= x.[i] && x.[i] <= '9') then i else aux x (i + 1)
  in
  let i = aux x 0 in
  if i = n then -1 else int_of_string (String.sub x i (n - i))

let next_id (s : id) (l : id list) =
  (* returns the next suitable id that can replace s, that is not in l
     to "replace" s means that the letter part of s is kept, and the number part may have to be changed *)
  let p = pref s in
  let n = List.length l in
  let a = Array.make (n + 1) false in
  let rec aux l =
    match l with
    | [] -> ()
    | x :: q ->
        if pref x = p then (
          let k = suff x in
          if k < n then a.(k + 1) <- true;
          aux q)
        else aux q
  in
  aux l;
  let k = ref (-2) in
  for i = 0 to n do
    if (not a.(i)) && !k = -2 then k := i - 1
  done;
  p ^ if !k < 0 then "" else string_of_int !k

let rec subst (m : lam) (n : lam) (x : id) =
  (* returns the term m where every free occurrence of x is replaced with n *)
  let l = fv n in
  let rec aux m =
    match m with
    | Var y -> if x = y then n else Var y
    | Exf (m', a) -> Exf (aux m', a)
    | App (m1, m2) -> App (aux m1, aux m2)
    | Fun (y, a, m') ->
        if y = x then m
        else if List.mem y l then
          let y' = next_id y l in
          Fun (y', a, aux (subst m' (Var y') y))
        else Fun (y, a, aux m')
    | Cpl (m1, m2) -> Cpl (aux m1, aux m2)
    | Fst m1 -> Fst (aux m1)
    | Snd m1 -> Snd (aux m1)
    | Ig (m1, b) -> Ig (aux m1, b)
    | Id (m1, a) -> Id (m1, a)
    | Case (m1, m2, m3) -> Case (aux m1, aux m2, aux m3)
    | I -> I
    | Any a -> Any a
  in
  aux m

let rec betastep (m : lam) =
  (* returns Some(m after one step of beta-reduction) if possible, None otherwise *)
  match m with
  | Var _ -> None
  | Fun (x, a, m1) -> (
      match betastep m1 with Some v -> Some (Fun (x, a, v)) | None -> None)
  | Exf (m1, a) -> (
      match betastep m1 with Some v -> Some (Exf (v, a)) | None -> None)
  | App (Fun (x, a, m1), m2) -> (
      match betastep m1 with
      | Some v -> Some (App (Fun (x, a, v), m2))
      | None -> Some (subst m1 m2 x))
  | App (m1, m2) -> (
      match betastep m1 with
      | Some v -> Some (App (v, m2))
      | None -> (
          match betastep m2 with Some v -> Some (App (m1, v)) | None -> None))
  | Cpl (m1, m2) -> (
      match betastep m1 with
      | Some v -> Some (Cpl (v, m2))
      | None -> (
          match betastep m2 with Some v -> Some (Cpl (m1, v)) | None -> None))
  | Fst m1 -> (
      match betastep m1 with
      | Some v -> Some (Fst v)
      | None -> ( match m1 with Cpl (m2, _) -> Some m2 | _ -> None))
  | Snd m1 -> (
      match betastep m1 with
      | Some v -> Some (Snd v)
      | None -> ( match m1 with Cpl (_, m3) -> Some m3 | _ -> None))
  | Ig (m1, b) -> (
      match betastep m1 with Some v -> Some (Ig (v, b)) | None -> None)
  | Id (m1, a) -> (
      match betastep m1 with Some v -> Some (Id (v, a)) | None -> None)
  | Case (m1, m2, m3) -> (
      match betastep m1 with
      | Some v -> Some (Case (v, m2, m3))
      | None -> (
          match m1 with
          | Ig (n, _) -> Some (App (m2, n))
          | Id (n, _) -> Some (App (m3, n))
          | _ -> (
              match betastep m2 with
              | Some v -> Some (Case (m1, v, m3))
              | None -> (
                  match betastep m3 with
                  | Some w -> Some (Case (m1, m2, w))
                  | None -> None))))
  | I -> None
  | Any _ -> None

let reduce (m : lam) =
  (* prints the reductions of m up to its normal form *)
  let rec aux m' =
    match m' with
    | None -> ()
    | Some m'' ->
        print_lam m'';
        print_newline ();
        aux (betastep m'')
  in
  print_lam m;
  print_newline ();
  aux (betastep m)

let rec normalize (m : lam) =
  (* returns the normalized version of m *)
  match betastep m with None -> m | Some v -> normalize v

(* typecheck is obtained by mutual recursivity with function infer *)
let rec infer (g : gam) (m : lam) =
  (* returns the type of m that is inferred from environment g using mutually recursive function typecheck *)
  match m with
  | Var x -> ( try List.assoc x g with Not_found -> raise TypeError)
  | Exf (m1, a) -> if typecheck g m1 Bot then a else raise TypeError
  | App (m1, m2) -> (
      let c = infer g m1 in
      match c with
      | TF (a, b) -> if typecheck g m2 a then b else raise TypeError
      | _ -> raise TypeError)
  | Fun (x, a, m1) ->
      let b = infer ((x, a) :: g) m1 in
      TF (a, b)
  | Cpl (m1, m2) ->
      let a = infer g m1 in
      let b = infer g m2 in
      And (a, b)
  | Fst m1 -> (
      let c = infer g m1 in
      match c with And (a, _) -> a | _ -> raise TypeError)
  | Snd m1 -> (
      let c = infer g m1 in
      match c with And (_, b) -> b | _ -> raise TypeError)
  | Ig (m1, b) ->
      let a = infer g m1 in
      Or (a, b)
  | Id (m1, a) ->
      let b = infer g m1 in
      Or (a, b)
  | Case (m1, m2, m3) -> (
      let d = infer g m1 in
      match d with
      | Or (a, b) -> (
          match infer g m2 with
          | TF (a', c) when a' = a -> (
              match infer g m3 with
              | TF (b', c') when b' = b && c' = c -> c
              | _ -> raise TypeError)
          | _ -> raise TypeError)
      | _ -> raise TypeError)
  | Any a -> a
  | I -> Top

and typecheck (g : gam) (m : lam) (a : ty) =
  try
    let b = infer g m in
    b = a
  with TypeError -> false
(* returns a boolean indicating whether lambda-term m has type a in environment g *)

let rec contains_admit (m : lam) =
  (* returns true if a subterm of m is Any *)
  match m with
  | Any _ -> true
  | Var _ -> false
  | Exf (n, _) -> contains_admit n
  | App (m1, m2) -> contains_admit m1 || contains_admit m2
  | Fun (_, _, m1) -> contains_admit m1
  | Cpl (m1, m2) -> contains_admit m1 || contains_admit m2
  | Fst m1 -> contains_admit m1
  | Snd m1 -> contains_admit m1
  | I -> false
  | Ig (m1, _) -> contains_admit m1
  | Id (m1, _) -> contains_admit m1
  | Case (m1, m2, m3) ->
      contains_admit m1 || contains_admit m2 || contains_admit m3
