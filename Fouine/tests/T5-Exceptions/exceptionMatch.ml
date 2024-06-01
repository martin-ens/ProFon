try let x = ref 3 in x:=2 ; raise (if !x > 2 then (let _ = prInt !x in E 1) else E !x)
with | E 3 -> 1 | E x when x <= 1 -> prInt 0 
| E y when (let _ = prInt y in y <> 2) -> 3 + 2 
| E _ when false -> 3*2 
| _ when let _ = prInt 2 in true -> prInt (-2)
