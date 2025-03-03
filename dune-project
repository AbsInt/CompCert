(lang dune 3.16)
(using coq 0.9)
(using menhir 3.0)
(using directory-targets 0.1)

(name compcert)

(package
 (name compcert)
 (synopsis "Full Compcert Compiler"))

(package
 (name MenhirLib)
 (synopsis "Menhir Components"))

(package
 (name Flocq)
 (synopsis "Flocq Components"))

(package
 (name documentation)
 (allow_empty)
 (synopsis "Documentation for compcert")
 (depends compcert MenhirLib Flocq))