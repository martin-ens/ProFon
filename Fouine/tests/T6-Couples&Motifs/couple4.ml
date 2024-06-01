let t = 1, 2, 3, 4 in match t with  
  | (x, y, _, a) when a < 3 -> prInt (x + y)
  | (x, y, z, _) -> prInt (x+y+z)