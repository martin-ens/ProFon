let f w x y z = if w<x && y<z then raise (E z) else 
                (if w>x && y>z then raise (E z) else prInt (let g a b = if a > b then a else b in g x y))
in try f 3 4 9 0 with E 0 -> prInt (-1) | E n -> prInt n
