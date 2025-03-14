open Printf
open MakefileConfig
open Version

let _ = printf "# CompCert configuration parameters\n";
        printf "COMPCERT_ARCH=%s\n" arch;
        printf "COMPCERT_MODEL=%s\n" model;
        printf "COMPCERT_ABI=%s\n" abi;
        printf "COMPCERT_ENDIANNESS=%s\n" endianness;
        printf "COMPCERT_BITSIZE=%s\n" bitsize;
        printf "COMPCERT_SYSTEM=%s\n" system;
        printf "COMPCERT_VERSION=%s\n" version;
        printf "COMPCERT_BUILDNR=%s\n" buildnr;
        printf "COMPCERT_TAG=%s\n" tag;
        printf "COMPCERT_BRANCH=%s\n" branch;
