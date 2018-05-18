# Compilation test

### with Coq 8.6

     ./configure -clightgen ia32-linux                                                 [42e4907]
    Testing assembler support for CFI directives... yes
    Testing Coq... version 8.6 -- good!
    Testing OCaml... version 4.04.0 -- good!
    Testing OCaml .opt compilers... yes
    Testing Menhir... version 20170101 -- good!
    Testing GNU make... version 4.0 (command 'make') -- good!

    CompCert configuration:
        Target architecture........... ia32
        Hardware model................ sse2
        Application binary interface.. standard
        Composite passing conventions. arguments: ints, return values: ref
        OS and development env........ linux
        C compiler.................... gcc -m32
        C preprocessor................ gcc
        Assembler..................... gcc
        Assembler supports CFI........ true
        Assembler for runtime lib..... gcc -m32 -c
        Linker........................ gcc
        Math library.................. -lm
        Binaries installed in......... /usr/local/bin
        Runtime library provided...... true
        Library files installed in.... /usr/local/lib/compcert
        Standard headers provided..... true
        Standard headers installed in. /usr/local/lib/compcert/include
        Build command to use.......... make
    
    If anything above looks wrong, please edit file ./Makefile.config to correct.

### with Coq 8.5.3

    ./configure -clightgen ia32-linux                                                 [42e4907]
    Testing assembler support for CFI directives... yes
    Testing Coq... version 8.5pl3 -- good!
    Testing OCaml... version 4.04.0 -- good!
    Testing OCaml .opt compilers... yes
    Testing Menhir... version 20170101 -- good!
    Testing GNU make... version 4.0 (command 'make') -- good!

    CompCert configuration:
        Target architecture........... ia32
        Hardware model................ sse2
        Application binary interface.. standard
        Composite passing conventions. arguments: ints, return values: ref
        OS and development env........ linux
        C compiler.................... gcc -m32
        C preprocessor................ gcc
        Assembler..................... gcc
        Assembler supports CFI........ true
        Assembler for runtime lib..... gcc -m32 -c
        Linker........................ gcc
        Math library.................. -lm
        Binaries installed in......... /usr/local/bin
        Runtime library provided...... true
        Library files installed in.... /usr/local/lib/compcert
        Standard headers provided..... true
        Standard headers installed in. /usr/local/lib/compcert/include
        Build command to use.......... make

    If anything above looks wrong, please edit file ./Makefile.config to correct
