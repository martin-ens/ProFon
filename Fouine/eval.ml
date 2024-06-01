open Expr
open Affichage

let int_of_val v = 
  (* gets an integer from a value, raises the appropriate exception if said value is not VI *)
  match v with
  | VI k -> k
  | VB _-> raise (AttemptConvert("boolean","int"))
  | VF(_,_,_) | VR(_,_,_,_) -> raise (AttemptConvert("function","int"))
  | VRef _ -> raise (AttemptConvert("reference","int"))
  | VU -> raise (AttemptConvert("unit","int"))
  | VCpl(_,_) -> raise (AttemptConvert("couple","int"))
  | VE(_) -> raise (AttemptConvert("exn", "int"))
  | VL(_) -> raise (AttemptConvert("list", "int"))

let bool_of_val v = 
  (* same as previous but with boolean values *)
  match v with
  | VB b -> b
  | VI _ -> raise (AttemptConvert("int","bool"))
  | VF(_,_,_) | VR(_,_,_,_) -> raise (AttemptConvert("function","bool"))
  | VRef _ -> raise (AttemptConvert("reference","bool"))
  | VU -> raise (AttemptConvert("unit","bool"))
  | VCpl(_,_) -> raise (AttemptConvert("couple","bool"))
  | VE(_) -> raise (AttemptConvert("exn", "bool"))
  | VL(_) -> raise (AttemptConvert("list", "bool"))

let list_of_val v = 
  (* same as previous but with lists *)
  match v with
  | VL(l) -> l
  | VI(_) -> raise (AttemptConvert("int","list"))
  | VB _-> raise (AttemptConvert("boolean","list"))
  | VF(_,_,_) | VR(_,_,_,_) -> raise (AttemptConvert("function","list"))
  | VRef _ -> raise (AttemptConvert("reference","list"))
  | VU -> raise (AttemptConvert("unit","list"))
  | VCpl(_,_) -> raise (AttemptConvert("couple","list"))
  | VE(_) -> raise (AttemptConvert("exn", "list"))

(* the 3 following functions associate the appropriate OCaml operator to each constructor *)
let intop_to_fun o = match o with
  | Add -> (+)
  | Mul -> ( * )
  | Min -> (-)
  | Div -> (/)

let compop_to_fun o = match o with
  | Geq -> (>=)
  | Leq -> (<=)
  | Lt -> (<)
  | Gt -> (>)
  | Eq -> (=)
  | Neq -> (<>)

let boolop_to_fun o = match o with
  | And -> (&&)
  | Or -> (||)

let rec assoc_mtf_val m v = 
  (* returns the bit of environment to add when trying to match pattern m with 
     value v and raises MatchingFailure if such matching is impossible *)
  match m with
  | MCpl(x,y) -> (match v with
                  | VCpl(v1,v2) -> (assoc_mtf_val x v1)@(assoc_mtf_val y v2)
                  | _ -> raise (MatchingFailure(m, v)))
  | ML(l) -> (match v with
              | VL(w) -> (match l, w with
                          | [], [] -> []
                          | [], _ -> raise (MatchingFailure(m, v))
                          | _, [] -> raise (MatchingFailure(m, v))
                          | x::q, y::r -> (assoc_mtf_val x y)@(assoc_mtf_val (ML q) (VL r)))
              | _ -> raise (MatchingFailure(m, v)))
  | MCons(x, q) -> (match v with
                    | VL(w) -> (match w with
                                | [] -> raise (MatchingFailure(m, v))
                                | y::r -> (assoc_mtf_val x y)@(assoc_mtf_val q (VL r)))
                    | _ -> raise (MatchingFailure(m, v)))
  | MUnit -> (match v with
              | VU -> []
              | _ -> raise (MatchingFailure(m, v)))
  | MWC -> []
  | MVar x -> [(x,v)]
  | MInt(n) -> (match v with
                | VI(p) when p = n -> []
                | _ -> raise (MatchingFailure(m, v)))
  | MB(b) -> (match v with
              | VB(p) when p = b -> []
              | _ -> raise (MatchingFailure(m, v)))

  | ME(mo) -> (match mo,v with
                 | MInt(i),VE(n) when i = n -> []
                 | MInt(_),VE(_) -> raise (MatchingFailure(ME(mo), v))
                 | MVar(x),VE(n) -> [(x,VI(n))]
                 | MWC,VE(_) -> []
                 | _, VE(_) -> raise (IncorrectExnArg(mo))
                 | _ -> raise (MatchingFailure(ME(mo), v)))



let assoc_match m v = 
  (* a funny-looking syntax used for MatchWith in order to re-use the previous function :
     instead of raising an exception when matching fails, we just return false *)
  try (true, (assoc_mtf_val m v)) with (MatchingFailure(_, _)) -> false, []


(* different options for the executable *)
let src_code = ref false;;
let verbose = ref false;;

(* used to print out what the evaluation has reached in debug mode *)
let p_verb s = (if !verbose then print_string s else ())



let rec evalK e envt (k, kE) =
  (* the main evaluation function implemented with continuations : 
     - envt is the current environment
     - k is used for the "normal" state of the evaluation
     - kE is used when raising an exception *)
  
  match e with
  (* basic constants *)
  | ConstI i -> k (VI i)
  | ConstB b -> k (VB b)
  | Var x -> (try k (List.assoc x envt) with Not_found -> raise (UnboundVariable x))

  (* basic operators *)
  | BinIntOp(o,e1,e2) -> p_verb ((string_of_intop o 0)^"; ") ; evalK e2 envt ((fun v2 -> evalK e1 envt ((fun v1 -> k (VI (intop_to_fun o (int_of_val v1) (int_of_val v2)))), kE)), kE)
  | BinCompOp(o,e1,e2) -> p_verb ((string_of_compop o 0)^"; ") ; evalK e2 envt ((fun v2 -> evalK e1 envt ((fun v1 -> (match v1 with
                                                                                                                      | VF(_,_,_) | VR(_,_,_,_) -> raise (CompFailure("function"))
                                                                                                                      | VRef(i) -> (match v2 with 
                                                                                                                                    | VRef(j) -> k (VB (compop_to_fun o (ref_arr.(i)) (ref_arr.(j))))
                                                                                                                                    | _ -> raise (CompFailure("ref")))
                                                                                                                      | VI i -> (match v2 with 
                                                                                                                                  | VI j -> k (VB (compop_to_fun o i j))
                                                                                                                                  | _ -> raise (CompFailure("int")))
                                                                                                                      | VB i -> (match v2 with 
                                                                                                                                  | VB j -> k (VB (compop_to_fun o i j))
                                                                                                                                  | _ -> raise (CompFailure("bool")))  
                                                                                                                      | VCpl(x, y) -> (match v2 with 
                                                                                                                                  | VCpl(a, b) -> k (VB (compop_to_fun o (x, y) (a, b)))
                                                                                                                                  | _ -> raise (CompFailure("couple")))
                                                                                                                      | VL l1 -> (match v2 with 
                                                                                                                                  | VL l2 -> k (VB (compop_to_fun o l1 l2))
                                                                                                                                  | _ -> raise (CompFailure("list")))
                                                                                                                      | VU -> (match v2 with 
                                                                                                                                  | VU -> k (VB (compop_to_fun o () ()))
                                                                                                                                  | _ -> raise (CompFailure("unit")))
                                                                                                                      | VE i -> (match v2 with 
                                                                                                                                  | VE j -> k (VB (compop_to_fun o i j))
                                                                                                                                  | _ -> raise (CompFailure("exception")))
                                                                                                                                    )
                                                                                                                                    ), kE)), kE)
  | BinBoolOp(o,e1,e2) -> p_verb ((string_of_boolop o 0)^"; ") ; evalK e1 envt ((fun v1 -> evalK e2 envt ((fun v2 -> k (VB (boolop_to_fun o (bool_of_val v1) (bool_of_val v2)))), kE)), kE)
  | Not(e) -> p_verb "Not; " ; evalK e envt ((fun v -> k (VB ((not (bool_of_val v))))), kE)
  (* note : OCaml treats boolean operators left to right for optimization reasons 
     hence the difference with the other two cases, even if we do not implement said optimizations *)

  (* if, print *)
  | IfThenElse(b,e1,e2) -> p_verb "If; " ; evalK b envt ((fun vb -> if (bool_of_val vb) then evalK e1 envt (k, kE) else evalK e2 envt (k, kE)), kE)
  | Print(e) -> p_verb "prInt; " ; evalK e envt ((fun v -> p_verb "\n**********\n" ;
                                                           print_int (int_of_val v);
                                                           p_verb "\n**********" ;
                                                           print_newline () ;
                                                           k v)
                                               , kE)

  (* let in declarations *)
  | LetIn(m,e1,e2) -> p_verb "LetIn; " ; 
                      evalK e1 envt ((fun v1 -> evalK e2 ((assoc_mtf_val m v1)@envt) (k, kE)), kE)
  | LetRec(m,e1,e2) -> p_verb "LetRec; " ;
                       evalK e1 envt ((fun v1 -> match m with
                                                 | MVar f -> (match v1 with
                                                              | VF(m,e,c) -> evalK e2 ((f, VR(f,m,e,c))::envt) (k, kE)
                                                              | VR(g,m,e,c) -> evalK e2 ((f, VR(f,m,e,c))::(g, VR(f,m,e,c))::envt) (k, kE)
                                                              | _ -> raise NotFunInLetRec)
                                                 | _ -> raise NotFunInLetRec)
                                    , kE)

  (* functions *)
  | Fun(m,e) -> p_verb "Fun; " ; k (VF(m,e,envt))
  | App(e1,e2) -> p_verb "App; " ;
                  evalK e2 envt ((fun v2 -> evalK e1 envt 
                                              ((fun v1 -> match v1 with
                                                          | VF(m,e,c) -> evalK e ((assoc_mtf_val m v2)@c) (k, kE)
                                                          | VR(f,m,e,c) -> evalK e ((f, VR(f,m,e,c))::((assoc_mtf_val m v2)@c)) (k, kE)
                                                          | _ -> raise NotAFunction), kE)), kE)

  (* imperative aspects *)
  | Ref(e) -> p_verb "Ref; " ;
              if !next_ref > 2047 then raise RefOverflow
              else evalK e envt ((fun v -> ref_arr.(!next_ref) <- v ; incr next_ref ; k (VRef(!next_ref -1))), kE)
  | Unit -> p_verb "Unit; " ; k VU
  | Deref(e) -> p_verb "Deref; " ; evalK e envt ((fun v -> match v with
                                                           | VRef(i) -> k (ref_arr.(i))
                                                           | _ -> raise NotARef), kE)
  | Ass(e, a) -> evalK a envt ((fun nv -> evalK e envt ((fun v -> match v with
                                                                  | VRef(i) -> ref_arr.(i) <- nv ; k VU
                                                                  | _ -> raise NotARef), kE)), kE)

  (* couples *)
  | Cpl(e1,e2) -> p_verb "Cpl; " ; evalK e2 envt ((fun v2 -> evalK e1 envt ((fun v1 -> k (VCpl(v1, v2))), kE)), kE)
  | Fst e -> p_verb "Fst; " ; evalK e envt ((fun v -> match v with
                                                      | VCpl(v1,_) -> k v1
                                                      | _ -> raise NotACouple), kE)
  | Snd e -> p_verb "Snd; " ; evalK e envt ((fun v -> match v with
                                                      | VCpl(_,v2) -> k v2
                                                      | _ -> raise NotACouple), kE)

  (* lists and matching *)
  | List l -> p_verb "List; " ; (match l with
                                | [] -> k (VL [])
                                | e :: q -> evalK (List q) envt ((fun li -> evalK e envt ((fun v -> k (VL (v :: (list_of_val li)))), kE))
                                                        , kE))
  | Cons(x, e) -> p_verb "Cons; " ; evalK e envt ((fun v -> match v with
                                                            | VL(l) -> evalK x envt ((fun vx -> k (VL (vx::l))), kE)
                                                            | _ -> raise NotAList)
                                                , kE)
  | Conc(e1, e2) -> p_verb "Conc; " ; evalK e2 envt ((fun v2 -> evalK e1 envt ((fun v1 -> match v1,v2 with
                                                                                          | VL(l),VL(l') -> k (VL (l@l'))
                                                                                          | _ -> raise NotAList)
                                                                             , kE))
                                                   , kE)
  | MatchWith(e, l) -> p_verb "MatchWith; " ; evalK e envt ((fun v -> match l with
                                                                      | [] -> raise PartialMatch
                                                                      | (m, e0, f) :: q -> let b, ev = assoc_match m v in 
                                                                                           let newenv = ev@envt in
                                                                                           if b then evalK e0 newenv
                                                                                                       ((fun v -> if bool_of_val v then evalK f newenv (k,kE)
                                                                                                                  else evalK (MatchWith(e, q)) envt (k, kE))
                                                                                                       , kE)
                                                                                           else evalK (MatchWith(e, q)) envt (k, kE))
                                                            , kE)

  (* exceptions *)
  | E(e) -> evalK e envt ((fun v -> k (VE (int_of_val v))), kE)
  | Raise(e) -> p_verb "Raise; " ; evalK e envt ((fun v -> match v with
                                                           | VE(n) -> kE (VE n)
                                                           | _ -> raise NotAnException), kE)
  | TryWith(e, l) -> p_verb "TryWith" ; evalK e envt (k, (fun v -> (match l with 
                                                                    | [] -> raise PartialMatch
                                                                    | (m, e0, f) :: q -> let b, ev = assoc_match m v in
                                                                                         let newenv = ev@envt in
                                                                                         if b then evalK e0 newenv
                                                                                                     ((fun v -> if bool_of_val v then evalK f newenv (k,kE)
                                                                                                                else evalK (TryWith(e, q)) envt (k, kE))
                                                                                                     , kE)
                                                                                         else evalK (TryWith(e, q)) envt (k, kE))))
