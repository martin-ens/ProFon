let f x = match x with 
  | (a, b) when a > 0 -> prInt b
  | (a, b) -> prInt a
in f (3, 4)