# ProFon 2024

*Made by m12pp and Loarwenn*

This repository contains the final versions of two projects done during a course taken at ENS de Lyon.
If you plan on studying there and on taking this course, it is advised that you do not look at the code.

The first project (`Fouine`) is an interpreter for a sublanguage of OCaml, written in OCaml.
The second project (`Pieuvre`) contains a Coq-like interactive proof assistant also written in OCaml, based on the lambda-calculus.

In order to compile the files, for each project you will need to have `dune` installed (it can be installed via `opam install dune` on Linux), and to use `dune build`.
Once compiled, the executable should be `_build/default/main.exe` or `_build/default/pieuvre.exe` depending on the project.

- `Fouine`:
  
  The default way of using `Fouine` is by passing a file as argument of the executable (use -help for additional info). Example files are present in the `tests` directory.
  You may also use it directly without arguments, in which case you may enter `Fouine` code ended with an end of file character (Ctrl+D in Unix).

- `Pieuvre`:
  
  `Pieuvre` is much more versatile, and allows different modes (use -help for specs).
  The standard use case is the interactive proof session, accessed with no file as argument and no options.

Have fun!
