open Printf


(* Command line args parsing *)


let usage_msg = "Usage: ./configure [options] target
For help on options and targets, do: ./configure -help
"

let prefix = ref "/usr/local"
let libdir = ref (!prefix ^ "/lib/compcert")
let bindir = ref (!prefix ^ "/bin")
let sharedir = ref ""
let mandir = ref (!prefix ^ "/share/man")
let toolprefix = ref ""
let ignore_coq_version = ref false
let ignore_ocaml_version = ref false
let has_runtime_lib = ref true
let has_standard_headers = ref true

(* Only used for compiler options for .ini/.config files*)
let target = ref ""
(* let no_runtime_lib = ref false; build via package *)

let anon_fun input = if !target = "" then 
    target := input else raise (Arg.Bad "Specify only one target")


let speclist = [
  ("-prefix", Arg.Set_string prefix, "Install in <dir>/bin and <dir>/lib/compcert");
  ("-bindir", Arg.Set_string bindir, "Install binaries in <dir>");
  ("-sharedir", Arg.Set_string sharedir, "Install configuration file in <dir>");
  ("-mandir", Arg.Set_string mandir, "Install man pages in <dir>");
  ("-libdir", Arg.Set_string libdir, "Install libraries in <dir>");
  ("-no-runtime-lib", Arg.Clear has_runtime_lib, "Do not compile nor install the runtime support library");
  ("-no-standard-headers", Arg.Clear has_standard_headers, "Do not install nor use the standard .h headers");
  ("-ignore-coq-version", Arg.Set ignore_coq_version, "Accept to use experimental or unsupported versions of Coq");
  ("-ignore-ocaml-version", Arg.Set ignore_ocaml_version, "Accept to use experimental or unsupported versions of OCaml");
  ("-toolprefix", Arg.Set_string toolprefix, "Prefix names of tools (\"gcc\", etc) with <pref>")
]

let _ = Arg.parse speclist anon_fun usage_msg

(* Quits configure process *)
let invalid_input reason = 
  printf "Error: %s\n" reason;
  printf "%s" usage_msg;
  exit 2


let has_double_ref = ref true
let abi_ref = ref ""

let rec check_target_starts_with choices = match choices with 
  | [] -> false
  | prefix::choices -> (String.starts_with ~prefix !target) || (check_target_starts_with choices)

(* detect target data *)
let (arch, model, endianess, bitsize) = 
  if check_target_starts_with [ "arm-" ; "armv7a-"] then
    "arm", "armv7a", "little", 32
  else if check_target_starts_with [ "armv6-"] then
    "arm", "armv6", "little", 32
  else if check_target_starts_with [ "armv6t2-"] then
    "arm", "armv6t2", "little", 32
  else if check_target_starts_with [ "armv7r-"] then 
    "arm", "armv7r", "little", 32
  else if check_target_starts_with [ "armv7m-"] then 
    "arm", "armv7m", "little", 32
  else if check_target_starts_with [ "armv7m+nofp.dp-"] then
    (has_double_ref := false; ("arm", "armv7m", "little", 32))
  else if check_target_starts_with [ "armeb-" ; "armebv7a"] then
    "arm", "armv7a", "big", 32
  else if check_target_starts_with [ "armebv6-"] then
    "arm", "armv6", "big", 32
  else if check_target_starts_with [ "armebv6t2-"] then
    "arm", "armv6t2", "big", 32
  else if check_target_starts_with [ "armebv7r-"] then 
    "arm", "armv7r", "big", 32
  else if check_target_starts_with [ "armebv7m-"] then
    "arm", "armv7m", "big", 32
  else if check_target_starts_with [ "x86_32-" ; "ia32-" ; "i386-"] then
    "x86", "32sse2", "little", 32
  else if check_target_starts_with [ "x86_64-" ; "amd64-"] then 
    "x86", "64", "little", 64
  else if check_target_starts_with [ "powerpc-" ; "ppc-"] then
    "powerpc", "ppc32", "big", 32
  else if check_target_starts_with [ "powerpc64-" ; "ppc64-"] then
    "powerpc", "ppc64", "big", 32
  else if check_target_starts_with [ "e5500-"] then
    "powerpc", "e5500", "big", 32
  else if check_target_starts_with [ "powerpcvle-" ; "ppcvle-"] then 
    (has_double_ref := false; "powerpc_vle", "ppc32", "big", 32 )
  else if check_target_starts_with [ "riscv32-" ; "rv32-"] then
    "riscV", "32", "little", 32
  else if check_target_starts_with [ "riscv64-" ; "rv64-"] then 
    "riscV", "64", "little", 64
  else if check_target_starts_with [ "aarch64-" ; "arm64-"] then 
    "aarch64", "default", "little", 64
  else if !target = "peaktop" then
    (abi_ref := "eabi"; has_double_ref := false; "peaktop", "default", "little", 32 )
  else if !target = "tricore-eabi" || !target = "tricore-eabi-llvm" then 
    (abi_ref := "eabi"; has_double_ref := false; "tricore", "tc161", "little", 32)
  else if !target = "manual" then 
    ("", "", "", 0)
  else if !target = "" then 
    invalid_input "no target architecture specified"
  else 
    invalid_input "unkown target architecture."

let target_suffix = let split =  Str.bounded_split (Str.regexp "-") !target 2 in 
  if List.length split = 2 then 
    List.nth split 1
  else ""

let rec check_target_suffix_in list = match list with 
  | [] -> false
  | suffix::list -> target_suffix = suffix || check_target_suffix_in list 

let _ = printf "arch: %s, model: %s, endianess: %s, bitsize: %d, suffix: %s\n" arch model endianess bitsize target_suffix


(* Target Configuration with defaults *)
let asm_supports_cfi = ref None
let cc = ref (!toolprefix ^ "gcc")
let cc_options = ref ""
let casm = ref (!toolprefix ^ "gcc")
let casm_options = ref "-c"
let casmruntime = ref ""
let clinker = ref (!toolprefix ^ "gcc")
let clinker_options = ref ""
let clinker_needs_no_pie = ref true 
let cprepro = ref (!toolprefix ^ "gcc")
let cprepro_options = ref "-E"
let archiver = ref (!toolprefix ^ "ar rcs")
let libmath = ref "-lm"
let responsefile = ref "gnu"
let system = ref ""

(* Set more flags depending on arch and target suffix *)
let _ = match arch with 
  | "arm" -> begin
    begin if check_target_suffix_in ["eabi"; "linux"] then 
      abi_ref := "eabi"
    else if check_target_suffix_in ["eabihf"; "hf"; "hardfloat"] then 
      abi_ref := "hardfloat"
    else 
      invalid_input (sprintf "invalid eabi/system '%s' for architecture ARM." target_suffix) end;
    cprepro_options := "-U__GNUC__ '-D__REDIRECT(name,proto,alias)=name proto' '-D__REDIRECT_NTH(name,proto,alias)=name proto' -E";
    system := "linux"
  end
  | "powerpc" | "powerpc_vle" -> begin 
    if check_target_suffix_in ["eabi"; "eabi-diab"; "linux"] then begin
      begin if target_suffix = "linux" then 
        abi_ref := "linux"
      else 
        abi_ref := "eabi" 
      end;
      if target_suffix = "eabi-diab" then begin
        asm_supports_cfi := Some false;
        casm := !toolprefix ^ "das";
        casm_options := "-Xalign-value";
        cc := !toolprefix ^ "dcc";
        clinker_needs_no_pie := false;
        clinker := !toolprefix ^ "dcc";
        cprepro := !toolprefix ^ "dcc";
        cprepro_options := "-E -D__GNUC__ -D__CHAR_UNSIGNED__";
        archiver := !toolprefix ^ "dar -q";
        libmath := "-lm";
        system := "diab";
        responsefile := "diab"
      end else begin 
        casmruntime := !toolprefix ^ "gcc -c -Wa,-mregnames";
        cprepro_options := "-U__GNUC__ -E";
        system := "linux"
      end
    end else 
      invalid_input (sprintf "invalid eabi/system '%s' for architecture PowerPC/PowerPC VLE." target_suffix)
  end 
  | "x86" when bitsize = 32 ->  
    if target_suffix = "bsd" then begin 
      abi_ref := "standard";
      cc_options := "-m32";
      casm_options := "-m32 -c";
      clinker_options := "-m32";
      cprepro_options := "-m32 -U__GNUC__ -E";
      system := "bsd"
    end else if target_suffix = "linux" then begin 
      abi_ref := "standard";
      cc_options := "-m32";
      casm_options := "-m32 -c";
      clinker_options := "-m32";
      cprepro_options := "-m32 -U__GNUC__ -E";
      system := "linux"
    end else 
      invalid_input (sprintf "invalid eabi/system '%s' for architecture IA32/X86_32." target_suffix)
  | "x86" when bitsize = 64 ->
    if target_suffix = "bsd" then begin 
      abi_ref := "standard";
      cc_options := "-m64";
      casm_options := "-m64 -c";
      clinker_options := "-m64";
      cprepro_options := "-m64 -U__GNUC__ -U__SIZEOF_INT128__ -E";
      system := "bsd"
    end else if target_suffix = "linux" then begin 
      abi_ref := "standard";
      cc_options := "-m64";
      casm_options := "-m64 -c";
      clinker_options := "-m64";
      cprepro_options := "-m64 -U__GNUC__ -U__SIZEOF_INT128__ -E";
      system := "linux"
    end else if check_target_suffix_in ["macos"; "macosx"] then begin 
      abi_ref := "macos";
      cc_options := "-arch x86_64"; 
      casm_options := "-arch x86_64 -c";
      clinker_options := "-arch x86_64"; 
      clinker_needs_no_pie := false;
      cprepro_options := "-arch x86_64 -U__GNUC__ -U__SIZEOF_INT128__ -U__clang__ -U__BLOCKS__ '-D__attribute__(x)=' '-D__asm(x)=' '-D_Nullable=' '-D_Nonnull=' '-D__DARWIN_OS_INLINE=static inline' -Wno-\\#warnings -E";
      libmath := "";
      system := "macos"
    end else if target_suffix = "cygwin" then begin 
      abi_ref := "standard";
      cc_options := "-m64";
      casm_options := "-m64 -c";
      clinker_options := "-m64";
      cprepro_options := "-m64 -U__GNUC__ -U__SIZEOF_INT128__ '-D__attribute__(x)=' -E";
      system := "cygwin"
    end else  
      invalid_input (sprintf "invalid eabi/system '%s' for architecture X86_64." target_suffix)
  | "riscV" -> begin
    let model_options = if model = "64" then 
      "-march=rv64imafd -mabi=lp64d" 
      else "-march=rv32imafd -mabi=ilp32d" in 
    abi_ref := "standard";
    cc_options := model_options;
    casm_options := model_options ^ " -c";
    clinker_options := model_options;
    cprepro_options := model_options ^ " -U__GNUC__ -E";
    system := "linux"
  end 
  | "aarch64" -> if target_suffix = "linux" then begin 
      abi_ref := "standard";
      cprepro_options := "-U__GNUC__ -E";
      system := "linux"
    end else if check_target_suffix_in ["macos"; "macosx"] then begin 
      abi_ref := "apple";
      casm := !toolprefix ^ "cc";
      casm_options := "-c -arch arm64";
      cc := !toolprefix ^ "cc -arch arm64";
      clinker := !toolprefix ^ "cc";
      clinker_needs_no_pie := false;
      cprepro := !toolprefix ^ "cc";
      cprepro_options := "-arch arm64 -U__GNUC__ -U__clang__ -U__BLOCKS__ '-D__attribute__(x)=' '-D__asm(x)=' '-D_Nullable=' '-D_Nonnull=' '-D__DARWIN_OS_INLINE=static inline' -Wno-\\#warnings -E";
      libmath := "";
      system := "macos"
    end else 
      invalid_input (sprintf "invalid eabi/system '%s' for architecture AArch64." target_suffix)
  | "peaktop" -> begin 
    asm_supports_cfi := Some false;
    casm := !toolprefix ^ "gcc";
    casm_options := "-c";
    cc := !toolprefix ^ "gcc";
    clinker := !toolprefix ^ "gcc";
    cprepro := !toolprefix ^ "gcc";
    cprepro_options := "-E -U__GNUC__";
    libmath := "";
    system := "peaktop"
  end 
  | "tricore" -> begin
    asm_supports_cfi := Some false;
    system := "tricore";
    if target_suffix = "eabi-llvm" then begin 
      casm := !toolprefix ^ "clang";
      cc := !toolprefix ^ "clang";
      clinker := !toolprefix ^ "clang";
      cprepro := !toolprefix ^ "clang";
      archiver := !toolprefix ^ "llvm-ar rcs";
      casm_options := "-march=tc162 -c";
      cprepro_options := "-march=tc162 -std=c99 -E -U__GNUC__";
      clinker_options := "-march=tc162"
    end else begin 
      casm := !toolprefix ^ "gcc";
      cc := !toolprefix ^ "gcc";
      clinker := !toolprefix ^ "gcc";
      cprepro := !toolprefix ^ "gcc";
      casm_options := "-mtc161 -mcpu=tc22xx -c";
      cprepro_options := "-mtc161 -mcpu=tc22xx -std=c99 -E -U__GNUC__";
      clinker_options := "-mtc161 -mcpu=tc22xx"
    end
  end
  | "" when !target = "manual" -> begin end 
  | _ -> begin
    invalid_input (sprintf "somehow got invalid system with architecture %s." arch)
  end 

let _ = begin if !casmruntime = "" then casmruntime := !casm ^ " " ^ !casm_options end

(* TODO test C compiler with cmd-line options *)

(* test assembler support for CFI directives *)
let _ = begin if not (!target = "manual") && !asm_supports_cfi = None then 
  printf "Testing assembler support for CFI directives...";
  let (asm_file, oc) = Filename.open_temp_file "compcert-configure-temp" ".s" in 
  let content = {|testfun:
  .file 1 "testfun.c"
  .loc 1 1
  .cfi_startproc
  .cfi_adjust_cfa_offset 16
  .cfi_endproc|} in 
  Printf.fprintf oc "%s\n" content;
  let command = Printf.sprintf "%s %s -o %s \"%s\" 2>%s" !casm !casm_options Filename.null asm_file Filename.null in 
  let ec = Sys.command command in 
  asm_supports_cfi := Some (ec = 0);
  Printf.printf "%s\n" (if !asm_supports_cfi = Some true then "yes" else "no")
end


(* TODO Test Availability of Option '-no-pie' or '-nopie' *)
(* Availability of Required Tools: Not necessary *)

(* TODO Determine $sharedir or check that user-provided $sharedir is valid *)

(* Generate Makefile.config *)
let config_base = sprintf "PREFIX=%s
BINDIR=%s
LIBDIR=%s
MANDIR=%s 
SHAREDIR=%s
COMPFLAGS=-bin-annot
" !prefix !bindir !libdir !mandir !sharedir

let config_extension = if !target = "manual" then 
  "
# Target architecture
# ARCH=powerpc
# ARCH=powerpc_vle
# ARCH=arm
# ARCH=x86
# ARCH=riscV
# ARCH=aarch6
# ARCH=peaktop
# ARCH=tricore
ARCH=

# Hardware variant
# MODEL=ppc32       # for plain PowerPC
# MODEL=ppc64       # for PowerPC with 64-bit instructions
# MODEL=e5500       # for Freescale e5500 PowerPC variant
# MODEL=armv6       # for ARM
# MODEL=armv6t2     # for ARM
# MODEL=armv7a      # for ARM
# MODEL=armv7r      # for ARM
# MODEL=armv7m      # for ARM
# MODEL=32sse2      # for x86 in 32-bit mode
# MODEL=64          # for x86 in 64-bit mode
# MODEL=default     # for others
MODEL=

# Target ABI
# ABI=eabi          # for PowerPC / Linux and other SVR4 or EABI platforms
# ABI=eabi          # for ARM
# ABI=hardfloat     # for ARM
# ABI=standard      # for others
ABI=

# Target bit width
# BITSIZE=64        # for x86 in 64-bit mode, RiscV in 64-bit mode, AArch64
# BITSIZE=32        # otherwise
BITSIZE=

# Target endianness
# ENDIANNESS=big     # for ARM or PowerPC
# ENDIANNESS=little  # for ARM or x86 or RiscV or AArch64
ENDIANNESS=

# Target operating system and development environment
#
# Possible choices for PowerPC:
# SYSTEM=linux
# SYSTEM=diab
#
# Possible choices for ARM, AArch64, RiscV:
# SYSTEM=linux
#
# Possible choices for x86:
# SYSTEM=linux
# SYSTEM=bsd
# SYSTEM=macos
# SYSTEM=cygwin
SYSTEM=

# C compiler (for testing only)
CC=cc

# Assembler for assembling compiled files
CASM=cc
CASM_OPTIONS=-c

# Assembler for assembling runtime library files
CASMRUNTIME=$(CASM) $(CASM_OPTIONS)

# Linker
CLINKER=cc
CLINKER_OPTIONS=-no-pie

# Preprocessor for .c files
CPREPRO=cc
CPREPRO_OPTIONS=-U__GNUC__ -E

# Archiver to build .a libraries
ARCHIVER=ar rcs

# Math library. Set to empty under macOS
LIBMATH=-lm

# Turn on/off the installation and use of the runtime support library
HAS_RUNTIME_LIB=true

# Turn on/off the installation and use of the standard header files
HAS_STANDARD_HEADERS=true

# Turn on/off support for double precision floating point only for selected architectures
HAS_DOUBLE=true

# Whether the assembler $(CASM) supports .cfi debug directives
ASM_SUPPORTS_CFI=false
#ASM_SUPPORTS_CFI=true

# Turn on/off compilation of clightgen
CLIGHTGEN=false

# Turn on/off compilation of only clightgen
CLIGHTGEN_ONLY=false

# Whether the other tools support responsefiles in GNU syntax or Diab syntax
RESPONSEFILE=gnu  # diab

# Whether to use the local copies of Flocq and MenhirLib
LIBRARY_FLOCQ=local      # external
LIBRARY_MENHIRLIB=local  # external
" else begin 
  let s = format_of_string "ABI=%s
ARCH=%s
ASM_SUPPORTS_CFI=%B
BITSIZE=%d
CASM=%s
CASM_OPTIONS=%s
CASMRUNTIME=%s
CC=%s %s
CLINKER=%s
CLINKER_OPTIONS=%s
CPREPRO=%s
CPREPRO_OPTIONS=%s
ARCHIVER=%s
ENDIANNESS=%s
HAS_RUNTIME_LIB=%B
HAS_STANDARD_HEADERS=%B
HAS_DOUBLE=%B
LIBMATH=%s
MODEL=%s
SYSTEM=%s
RESPONSEFILE=%s
" in
 sprintf s !abi_ref arch (Option.get !asm_supports_cfi) bitsize !casm !casm_options !casmruntime !cc !cc_options !clinker !clinker_options !cprepro !cprepro_options !archiver endianess !has_runtime_lib !has_standard_headers !has_double_ref !libmath model !system !responsefile
end

let _ = let config_oc = open_out "Makefile.config" in 
  output_string config_oc (config_base ^ config_extension);
  close_out config_oc

(* Write default _CoqProject file with dune support *)
let coq_project_content = "-R _build/default/platform/lib compcert.lib -R _build/default/platform/common compcert.common -R _build/default/platform/TargetPlatformCopy compcert.TargetPlatformCopy -R _build/default/platform/backend compcert.backend -R _build/default/platform/cfrontend compcert.cfrontend -R _build/default/platform/driver compcert.driver -R _build/default/platform/cparser compcert.cparser -R _build/default/platform/export compcert.export -R _build/default/flocq Flocq -R _build/default/MenhirLib MenhirLib\n"

let _ = let coqproject_oc = open_out "_CoqProject" in 
  output_string coqproject_oc coq_project_content;
  close_out coqproject_oc

