open Ocamlbuild_plugin;;
dispatch begin function
| After_rules ->
    (* declare the tags "use_Cparser" and "include_Cparser" *)
    ocaml_lib "cparser/Cparser";

    (* libraries and syntax extensions accessed via ocamlfind *)
    flag ["ocaml"; "link"; "pkg_unix"] & S[A"-package"; A "unix"];
    flag ["ocaml"; "link"; "pkg_str"] & S[A"-package"; A "str"];
    flag ["ocaml"; "compile";  "pkg_bitstring"] & S[A"-package"; A"bitstring,bitstring.syntax"; A"-syntax"; A"bitstring.syntax,camlp4o"];
    flag ["ocaml"; "ocamldep";  "pkg_bitstring"] & S[A"-package"; A"bitstring,bitstring.syntax"; A"-syntax"; A"bitstring.syntax,camlp4o"];
    flag ["ocaml"; "link";  "pkg_bitstring"] & S[A"-package"; A"bitstring"]

| _ -> ()
end
