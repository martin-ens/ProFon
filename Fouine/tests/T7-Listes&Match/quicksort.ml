let rec arrange l x = 
  match l with
  | [] -> [],[]
  | y::q when y < x -> let q1,q2 = arrange q x in y::q1,q2
  | y::q -> let q1,q2 = arrange q x in q1,y::q2
;;
let rec print_list l = 
  match l with
  | [] -> ()
  | x::q -> let _ = prInt x in print_list q
;;
let rec quicksort l =
  match l with
  | [] -> []
  | [_] -> l
  | x::q -> let q1,q2 = arrange q x in (quicksort q1)@(x::(quicksort q2))
;;
print_list (quicksort [3;2;0;9;1;1;2;4;10;5;4;5])
