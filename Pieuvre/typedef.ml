type id = string

(* types type *)
type ty =
  | TB of string (* Base type *)
  | TF of ty * ty (* Arrow type *)
  | And of ty * ty
  | Or of ty * ty
  | Top (* True *)
  | Bot (* False *)

(* lambda-terms type *)
type lam =
  | App of lam * lam
  | Var of id
  | Fun of id * ty * lam
  | Exf of lam * ty
  | Cpl of lam * lam
  | Fst of lam
  | Snd of lam
  | Ig of lam * ty
  | Id of lam * ty
  | Case of lam * lam * lam
  | I (* lambda-term of type True *)
  | Any of ty (* obtained when the corresponding subgoal is admitted *)

(* environment type *)
type gam = (id * ty) list

(* tactics type *)
type tactic =
  | Intro
  | IntroName of id
  | Intros
  | IntrosNames of id list
  | Exact of lam
  | Qed
  | Admit
  | Admitted
  | Apply of id
  | Cut of ty
  | Assumption
  | Exit
  | Help of tactic
  | Print
  | Exfalso
  | Absurd of ty
  | Elim of id
  | Split
  | Left
  | Right

(* type for a state of a proof :
   - either a list of subgoals : (environment, subgoal, hole function, last tactic used)
     with an indication of the size of the list for optimization purposes
   - either a lambda-term constructed, needing to be reduced and typechecked *)
type proof_state =
  | Subgoals of (gam * ty * (lam -> lam) * tactic) list * int
  | End of lam

(* Octoproof modes constructors *)
type mode =
  | Red of lam
  | Alph of lam * lam
  | Typ of lam * ty
  | Prf of ty
  | PrfFile of ty * tactic list

(* declaration of exceptions *)
exception WrongInput
exception TypeError
exception TwoOptions
exception NoMoreGoals
exception NotProven
exception InternalError
exception IncorrectTactic
exception IncorrectType of lam * ty
exception NotUnifiable of ty * ty
exception GivenUpGoals
exception NotAnAssumption
