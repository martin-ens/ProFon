((fun (f:A -> A) => (fun (x:A) => f (f x))) (fun (y:A) => (fun (z:A->(B->B)->A) => z y (fun (y0:B) => y0)) (fun (x0:A) => fun (b:B->B) => x0))) : A -> A.
