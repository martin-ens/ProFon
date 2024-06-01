let rec f = function
			| [] -> raise (E 0)
			| x::q when x > 10 -> prInt x
			| x::q -> f q
in try f [2;3;3;7;5;6;7;1;4;(let x = 3 in () ; x+4);42] with E n -> n