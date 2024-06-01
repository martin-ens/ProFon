let f x = fun y g -> if g (x<=y) then 1 else 2 in 
prInt (f 3 2 ((fun h b -> h b) not) )
