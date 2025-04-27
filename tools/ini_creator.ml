open Printf
open MakefileConfig

let _ = printf "stdlib_path=%s\n" libdir;
        printf "prepro=%s\n" cprepro;
        printf "linker=%s\n" clinker;
        printf "asm=%s\n" casm;
        printf "prepro_options=%s\n" cprepro_options;
        printf "asm_options=%s\n" casm_options;
        printf "linker_options=%s\n" clinker_options;
        printf "arch=%s\n" arch;
        printf "model=%s\n" model;
        printf "abi=%s\n" abi;
        printf "endianness=%s\n" endianness;
        printf "system=%s\n" system;
        printf "has_runtime_lib=%s\n" has_runtime_lib;
        printf "has_standard_headers=%s\n" has_standard_headers;
        printf "has_double=%s\n" has_double;
        printf "asm_supports_cfi=%s\n" asm_supports_cfi;
        printf "response_file_style=%s\n" responsefile