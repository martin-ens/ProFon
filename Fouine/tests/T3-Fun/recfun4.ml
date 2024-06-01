let rec fibo_naif n =
    if n = 0 || n = 1 then 1
    else (fibo_naif (n-1)) + (fibo_naif (n-2))
in prInt (fibo_naif 15)
