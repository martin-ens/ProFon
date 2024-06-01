let rec expo x n = if n=0 then 1 else (if n/2*2 = n then (expo x (n/2))*(expo x (n/2)) else x*(expo x (n/2))*(expo x (n/2))) in prInt (expo 2 4)
