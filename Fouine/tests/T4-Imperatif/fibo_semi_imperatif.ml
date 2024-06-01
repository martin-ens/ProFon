let x = ref 1 in let y = ref 1 in
let fibo n =
  let rec aux n = 
    if n = 0 || n = 1 then (x := 1 ; y := 1)
    else (aux (n-1) ; 
          let temp = !x in
          x := !y ;
          y := !y + temp)
  in (aux n ; !y)
in prInt (fibo 25)