type id = string

type intop =
  | Add
  | Mul
  | Min
  | Div

type compop =
  | Geq
  | Leq
  | Lt
  | Gt
  | Eq
  | Neq

type boolop =
  | Or
  | And

type motif = (* patterns we want to match in let, fun, match, try, etc... *)
  | MVar of id (* any variable *)
  | MB of bool (* true or false *)
  | MInt of int (* any integer *)
  | MCpl of motif*motif (* a couple *)
  | ML of motif list (* a list *)
  | MCons of motif*motif (* a list with its first element explicited : x::q *)
  | MWC (* wildcard, i.e. anything *)
  | MUnit (* Unit *)
  | ME of motif (* exceptions *)
type expr =
  (* basic constants *)
  | ConstI of int
  | ConstB of bool
  | Var of id
  
  (* basic operators *)
  | BinIntOp of intop * expr * expr (* binary operators that turn two ints into another int *)
  | BinCompOp of compop * expr * expr (* binary comparison operators i.e. that take two integers and output a bool *)
  | BinBoolOp of boolop * expr * expr (* binary operators that turn two bools into another bool *)
  | Not of expr

  (* if, print, declarations and functions *)
  | IfThenElse of expr*expr*expr
  | Print of expr
  | LetIn of motif*expr*expr
  | LetRec of motif*expr*expr
  | Fun of motif*expr
  | App of expr*expr

  (* imperative aspects *)
  | Ref of expr (* reference *)
  | Deref of expr (* dereferencing operator *)
  | Ass of expr*expr (* assignment operator *)
  | Unit

  (* couples *)
  | Cpl of expr*expr
  | Fst of expr
  | Snd of expr
  
  (* lists and matching *)
  | List of expr list
  | MatchWith of expr*(motif*expr*expr) list 
  | Cons of expr*expr
  | Conc of expr*expr

  (* exceptions *)
  | E of expr
  | TryWith of expr*(motif*expr*expr) list (* our version of try with is "fancy", as you can have different exception cases *)
  | Raise of expr


and valeur =
  | VI of int (* value for ints *)
  | VB of bool (* value for bools *)
  | VF of motif*expr*env (* value for functions *)
  | VR of id*motif*expr*env (* value for recursive functions, the added id being the name of the function *)
  | VRef of int (* value for refs : the int parameter is the index at which to look in the array *)
  | VCpl of valeur*valeur (* value for couples *)
  | VL of valeur list (* value for lists *)
  | VU (* value for Unit *)
  | VE of int (* value for exceptions *)

and env = (id*valeur) list

(* a list of built-in functions that are added immediately to the environment,
   in order to allow overloading on these functions' definitions *)
let builtin_fun = [("fst", VF(MVar("x"), Fst(Var("x")), []));
                   ("snd", VF(MVar("x"), Snd(Var("x")), []));
                   ("raise", VF(MVar("x"), Raise(Var("x")), []));
                   ("ref", VF(MVar("x"), Ref(Var("x")), []));
                   ("not", VF(MVar("x"), Not(Var("x")), []));
                   ("prInt", VF(MVar("x"), Print(Var("x")), []));
                   ("incr", VF(MVar("x"), Ass(Var("x"), BinIntOp(Add,Deref(Var("x")),ConstI(1))), []));
                   ("decr", VF(MVar("x"), Ass(Var("x"), BinIntOp(Min,Deref(Var("x")),ConstI(1))), []));
                   ("succ", VF(MVar("x"), BinIntOp(Add,Var("x"),ConstI(1)), []));
                   ("pred", VF(MVar("x"), BinIntOp(Min,Var("x"),ConstI(1)), []))]


let ref_arr = Array.make 2048 (VI(0))
let next_ref = ref 0


(* see main.ml for their uses *)
exception NotACouple
exception AttemptConvert of string*string
exception RefOverflow
exception NotAFunction
exception NotARef 
exception NotAnException
exception MatchingFailure of motif*valeur
exception PartialMatch
exception UnboundVariable of id
exception NotFunInLetRec
exception NotAList
exception IncorrectExnArg of motif
exception CompFailure of string
