let f l =
	let rec aux l compt = match l, compt with
		| [], n when n = 0 -> raise (E 0)
		| [], n when n = 1 -> raise (E 1)
		| [], n when (if true then true else try raise (E 3) with (E n) -> false) -> raise (E 2)
		| [], n -> n
		| x::q, n -> aux q (n+1)
	in aux l 0

in try f [1;2] with E 0 -> prInt 42 | E 1 -> prInt 43 | E n -> prInt n
		