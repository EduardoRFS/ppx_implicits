(lang dune 2.8)

(name ppx_implicits)

(generate_opam_files true)

(package
 (name ppx_implicits)
 (depends
  (ocaml
   (and
    (>= "4.12.0")
    (< "4.13.0")))
  reason
  ppxlib))
