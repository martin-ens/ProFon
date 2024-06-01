let rec ack n k = if n = 0 then k + 1 else if k = 0 then ack (n-1) 1 else ack (n-1) (ack n (k-1)) in prInt (ack 3 5)
