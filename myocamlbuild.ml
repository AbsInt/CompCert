open Ocamlbuild_plugin;;
dispatch begin function
| After_rules ->
    (* declare the tags "use_Cparser" and "include_Cparser" *)
    ocaml_lib "cfrontend/Cparser";

    (* force linking of libCparser.a when use_Cparser is set *)
    flag ["link"; "ocaml"; "native"; "use_Cparser"]
         (S[A"cfrontend/libCparser.a"]);
    flag ["link"; "ocaml"; "byte"; "use_Cparser"]
         (S[A"-custom"; A"cfrontend/libCparser.a"]);

    (* make sure libCparser.a is up to date *)
    dep  ["link"; "ocaml"; "use_Cparser"] ["cfrontend/libCparser.a"];

| _ -> ()
end
