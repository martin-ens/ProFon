open Expr

(* the following functions return the string associated to a certain argument
   it returns the constructor string if the mode is 0 and the source code string otherwise *)
let string_of_intop o mode = match o with
  | Add -> if mode = 0 then "Add" else "+"
  | Mul -> if mode = 0 then "Mul" else "*"
  | Div -> if mode = 0 then "Div" else "/"
  | Min -> if mode = 0 then "Min" else "-"

let string_of_boolop o mode = match o with
  | And -> if mode = 0 then "And" else "&&"
  | Or -> if mode = 0 then "Or" else "||"

let string_of_compop o mode = match o with
  | Geq -> if mode = 0 then "Geq" else ">="
  | Leq -> if mode = 0 then "Leq" else "<="
  | Gt -> if mode = 0 then "Gt" else ">"
  | Lt -> if mode = 0 then "Lt" else "<"
  | Neq -> if mode = 0 then "Neq" else "<>"
  | Eq -> if mode = 0 then "Eq" else "="

let rec string_of_motif m mode = match m with
  | MVar x -> x
  | MInt n -> if mode = 0 then "MInt("^(string_of_int n)^")" else (string_of_int n)
  | MB b -> if mode = 0 then "MB("^(string_of_bool b)^")" else (string_of_bool b)
  | MCpl(x,y) -> if mode = 0 then "MCpl("^(string_of_motif x 0)^","^(string_of_motif y 0)^")" else "("^(string_of_motif x 1)^","^(string_of_motif y 1)^")"
  | ML l -> let rec aux li = (match li with
                              | [] -> ""
                              | [x] -> string_of_motif x mode
                              | x::q -> (string_of_motif x mode)^","^(aux q))
            in if mode = 0 then "ML("^(aux l)^")" else "["^(aux l)^"]"
  | MCons(x, l) -> if mode = 0 then "MCons("^(string_of_motif x 0)^", "^(string_of_motif l 0)^")" 
                   else (string_of_motif x 1)^" :: ("^(string_of_motif l 1)^")"
  | MWC -> "_"
  | MUnit -> if mode = 0 then "MUnit " else "()"
  | ME m -> "E("^(string_of_motif m mode)^")"
(* used only for error messages thus no mode argument *)
let rec string_of_val v = match v with
  | VI k -> string_of_int k
  | VB b -> string_of_bool b
  | VF(_,_,_) | VR(_,_,_,_) -> "<fun>"
  | VRef k -> "ref ("^(string_of_val (ref_arr.(k)))^")"
  | VCpl(v1,v2) -> "("^(string_of_val v1)^","^(string_of_val v2)^")"
  | VL(l) -> let rec aux li = (match li with
                               | [] -> ""
                               | [x] -> string_of_val x 
                               | x::q -> (string_of_val x )^","^(aux q))
             in ""^(aux l)^"]"
  | VU -> "()"
  | VE k -> "E("^(string_of_int k)^")"

let rec affiche_expr e =
  (* prints out the expression e in debug mode, i.e. with prefix constructors *)
  let rec aff_aux s l = 
    (* prints out s with elements of l as arguments in a constructor fashion *)
    print_string s;
    match l with
    |[] -> print_string ")"
    |[x] -> affiche_expr x;
            print_string ")"
    |x::r -> affiche_expr x;
             print_string ", ";
             aff_aux "" r
  in
  
  match e with
  | Var x -> print_string x
  | ConstI k -> print_int k
  | ConstB b -> print_string (string_of_bool b)

  | BinIntOp(o,e1,e2) -> aff_aux ((string_of_intop o 0)^"(") [e1;e2]
  | BinCompOp(o,e1,e2) -> aff_aux ((string_of_compop o 0)^"(") [e1;e2]
  | BinBoolOp(o,e1,e2) -> aff_aux ((string_of_boolop o 0)^"(") [e1;e2]
  | Not(e1) -> aff_aux "Not(" [e1]

  | Print(e) -> aff_aux "Print(" [e]
  | IfThenElse(b,e1,e2) -> aff_aux "IfThenElse(" [b;e1;e2]

  | LetIn(m,e1,e2) -> aff_aux ("LetIn("^(string_of_motif m 0)^", ") [e1;e2]
  | LetRec(m,e1,e2) -> aff_aux ("LetRec("^(string_of_motif m 0)^", ") [e1;e2] 

  | Fun(m,e) -> aff_aux ("Fun("^(string_of_motif m 0)^", ") [e]
  | App(e1,e2) -> aff_aux "App(" [e1;e2]

  | Ref(e) -> aff_aux "Ref(" [e]
  | Deref(e) -> aff_aux "Deref(" [e]
  | Ass(e1, e2) -> aff_aux "Ass(" [e1;e2]
  | Unit -> print_string "Unit"

  | Cpl(e1,e2) -> aff_aux "Cpl(" [e1;e2]
  | Fst(e) -> aff_aux "Fst(" [e]
  | Snd(e) -> aff_aux "Snd(" [e]

  | List(l) -> aff_aux "List(" l
  | Cons(x,q) -> aff_aux "Cons(" [x;q]
  | Conc(e1,e2) -> aff_aux "Conc(" [e1;e2]
  | MatchWith(e, l) -> print_string "MatchWith(" ;
                       affiche_expr e ;
                       print_string ", [" ;
                       let rec aux l = (match l with
                                        | [] -> print_string "])"
                                        | (m, e1, e2)::q -> aff_aux ("("^(string_of_motif m 0)^", ") [e1;e2] ; aux q)
                       in aux l

  | E(e) -> aff_aux "E(" [e]
  | Raise(e) -> aff_aux "Raise(" [e]
  | TryWith(e1, l) -> print_string "TryWith(" ;
                      affiche_expr e1 ;
                      print_string ", [" ;
                      let rec aux l = (match l with
                                       | [] -> print_string "])"
                                       | (m, e1, e2)::q -> aff_aux ("("^(string_of_motif m 0)^", ") [e1;e2] ; aux q)
                      in aux l

let affiche_code e =
  (* prints out the OCaml/fouine code associated to expression e 
     note : our use of parentheses is not smart per se (one could call it "parenthesis-happy"),
     but the function returns a correct code which has the same behaviour as e, thus this function works *)
  let rec return_code e =
    (* returns the code of expression e *)
    let aff_aux s e1 e2 = 
      (* for binary infix operators *)
      "("^(return_code e1)^s^(return_code e2)^")"
    in
    
    match e with
    | Var x -> x
    | ConstI k -> string_of_int k
    | ConstB b -> string_of_bool b

    | BinIntOp(o,e1,e2) -> aff_aux (string_of_intop o 1) e1 e2
    | BinCompOp(o,e1,e2) -> aff_aux (string_of_compop o 1) e1 e2
    | BinBoolOp(o,e1,e2) -> aff_aux (string_of_boolop o 1) e1 e2
    | Not(e1) -> "(not "^(return_code e1)^")"
    
    | Print(e) -> "(prInt "^(return_code e)^")"
    | IfThenElse(b,e1,e2) -> "if "^(return_code b)^" then "^(return_code e1)^" else "^(return_code e2)

    | LetIn(m,e1,e2) -> "let "^(string_of_motif m 1)^" = "^(return_code e1)^" in "^(return_code e2)
    | LetRec(m,e1,e2) -> "let rec "^(string_of_motif m 1)^" = "^(return_code e1)^" in "^(return_code e2)

    | Fun(m,e) -> "(fun "^(string_of_motif m 1)^" -> "^(return_code e)^")"
    | App(e1,e2) -> aff_aux " " e1 e2

    | Ref(e) -> "(ref ("^(return_code e)^"))"
    | Deref(e) -> "!("^(return_code e)^")"
    | Ass(e1, e2) -> aff_aux ":=" e1 e2
    | Unit -> "()"

    | Cpl(e1,e2) -> aff_aux "," e1 e2
    | Fst(e) -> "(fst "^(return_code e)^")"
    | Snd(e) -> "(snd "^(return_code e)^")"

    | List(l) -> let rec aux li = (match li with
                                   | [] -> ""
                                   | [x] -> return_code x 
                                   | x::q -> (return_code x)^";"^(aux q))
                 in "["^(aux l)^"]"
    | Cons(x, q) -> aff_aux "::" x q
    | Conc(e1,e2) -> aff_aux "@" e1 e2
    | MatchWith(e, l) -> "match "^(return_code e)^" with"^
                           (let rec aux l = (match l with
                                             | [] -> ""
                                             | (m, e1, e2)::q -> " | "^(string_of_motif m 1)^" when "^(return_code e1)^" -> "^(return_code e2)^(aux q))
                            in aux l)

    | E(e) -> "(E ("^(return_code e)^"))"
    | Raise(e) -> "(raise ("^(return_code e)^"))"
    | TryWith(e1, l) -> "try "^(return_code e1)^" with "^
                          (let rec aux l = (match l with
                                            | [] -> ""
                                            | (m, e1, e2)::q -> " | "^(string_of_motif m 1)^" when "^(return_code e1)^" -> "^(return_code e2)^(aux q))
                           in aux l)

  in print_string (return_code e)
