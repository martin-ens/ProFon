let f x y z = (x < y) || z in let g f x y = 
fun z -> not (f x y z) 
in
 if g f (let x=3 in let x = x+1 in x) 
(if true && false then 0 
	else 
   prInt (4/2*3+1) ) (not (not true)) then prInt (9- -3) else prInt (- prInt(3 *4 ))

