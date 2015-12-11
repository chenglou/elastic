#!/usr/bin/env ocaml
#directory "pkg"
#use "topkg.ml"

let () =
  Pkg.describe "m17n" ~builder:`OCamlbuild [
    Pkg.lib "pkg/META";
    Pkg.lib ~exts:Exts.interface_opt "src/mylexer";
    Pkg.lib ~exts:Exts.interface_opt "src/myparser";
    Pkg.lib ~exts:Exts.interface_opt "src/mypprintast";
    Pkg.lib ~exts:Exts.interface_opt "src/ocamlpprintast";
    Pkg.lib ~exts:Exts.interface_opt "src/ocamlparser";
    Pkg.lib ~exts:Exts.interface_opt "src/m17n_util";
    Pkg.lib ~exts:Exts.library "src/m17n";
    Pkg.lib ~exts:[".cmo"] "src/m17n_toploop";
    Pkg.lib ~cond:(Env.bool "utop") ~exts:[".cmo"] "src/m17n_utop";
    Pkg.bin ~auto:true "src/m17n_pp" ~dst:"ocamlm17n";
    Pkg.doc "README.md";
    Pkg.doc "LICENSE.txt";
    Pkg.doc "CHANGELOG.md"; ]
