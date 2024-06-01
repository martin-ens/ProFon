let rec fusion l1 l2 = match l1,l2 with
| [],[] -> []
| [_],[] -> l1
| [],[_] -> l2
| x::q,y::s -> if x <= y then x::(fusion q l2) else y::(fusion l1 s)
in 
let rec separe l = match l with
| [] -> [], []
| [_] -> l, []
| x::y::q -> let (l1, l2) = separe q in x::l1, y::l2
in
let rec tri_fusion l = match l with
  | [] -> []
  | [_] -> l
  | _ -> let l1, l2 = separe l in fusion (tri_fusion l1) (tri_fusion l2)
in 
let rec aff_liste l = match l with
  | [] -> ()
  | x::q -> let _ = prInt x in aff_liste q
in
aff_liste (tri_fusion [1;4;7;2;0])