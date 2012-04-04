open Ocamlbuild_plugin;;
dispatch begin function
| After_rules ->
    (* declare the tags "use_Cparser" and "include_Cparser" *)
    ocaml_lib "cparser/Cparser";

    (* force linking of libCparser.a when use_Cparser is set *)
    flag ["link"; "ocaml"; "native"; "use_Cparser"]
         (S[A"cparser/libCparser.a"]);
    flag ["link"; "ocaml"; "byte"; "use_Cparser"]
         (S[A"-custom"; A"cparser/libCparser.a"]);

    (* make sure libCparser.a is up to date *)
    dep  ["link"; "ocaml"; "use_Cparser"] ["cparser/libCparser.a"];

    (* ocamlfind libraries *)
    flag ["ocaml"; "link"; "pkg_unix"] & S[A"-package"; A "unix"];
    flag ["ocaml"; "link"; "pkg_str"] & S[A"-package"; A "str"];
    flag ["ocaml"; "compile";  "pkg_bitstring"] & S[A"-package"; A"bitstring,bitstring.syntax"; A"-syntax"; A"bitstring.syntax,camlp4o"];
    flag ["ocaml"; "ocamldep";  "pkg_bitstring"] & S[A"-package"; A"bitstring,bitstring.syntax"; A"-syntax"; A"bitstring.syntax,camlp4o"];
    flag ["ocaml"; "link";  "pkg_bitstring"] & S[A"-package"; A"bitstring"]

| _ -> ()
end
