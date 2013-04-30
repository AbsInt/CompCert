open Camlcoq
open Asm
open Asm_printers
open AST
open Bitstring_utils
open C2C
open Camlcoq
open ELF_parsers
open ELF_printers
open ELF_types
open ELF_utils
open Frameworks
open Lens
open Library
open PPC_parsers
open PPC_printers
open PPC_types
open PPC_utils
open Sections

(** Enables immediate printing of log information to stdout.
    Warning: will print out everything even when backtracking.
*)
let debug = ref false

(** Whether to print the ELF map. *)
let print_elfmap = ref false

(** Whether to dump the ELF map. *)
let dump_elfmap = ref false

(** Whether to check that all ELF function/data symbols have been matched
    against CompCert idents. *)
let exhaustivity = ref true

(** Whether to print the list of all symbols (function and data) that were not
    found in .sdump files. *)
let list_missing = ref false

(** CompCert Asm *)
type ccode = Asm.instruction list

let print_debug s =
  if !debug then print_endline (string_of_log_entry true (DEBUG(s)))

(** Adds a log entry into the framework. *)
let add_log (entry: log_entry) (efw: e_framework): e_framework =
  if !debug then print_endline ("--DEBUG-- " ^ string_of_log_entry true entry);
  {efw with log = entry :: efw.log}

(** [flag] should have only one bit set. *)
let is_set_flag (flag: int32) (bitset: int32): bool =
  Int32.logand bitset flag <> 0l

(** Checks that [atom]'s binding matches [sym]'s. *)
let check_st_bind atom (sym: elf32_sym): s_framework -> s_framework =
  let static = atom.a_storage = C.Storage_static || atom.a_inline in
  match static, sym.st_bind with
  | true, STB_LOCAL -> id
  | false, STB_GLOBAL -> id
  | _ -> (
    sf_ef ^%=
      add_log (ERROR(
        "Symbol: " ^ sym.st_name ^ " has a wrong binding (local vs. global)"
      ))
  )

(** Adapted from CompCert *)
let name_of_section_Linux: section_name -> string = function
| Section_text -> ".text"
| Section_data i -> if i then ".data" else ".bss"
| Section_small_data i -> if i then ".sdata" else ".sbss"
| Section_const -> ".rodata"
| Section_small_const -> ".sdata2"
| Section_string -> ".rodata"
| Section_literal -> ".rodata.cst8"
| Section_jumptable -> ".text"
| Section_user(s, wr, ex) -> s

(** Adapted from CompCert *)
let name_of_section_Diab: section_name -> string = function
| Section_text -> ".text"
| Section_data i -> if i then ".data" else ".bss"
| Section_small_data i -> if i then ".sdata" else ".sbss"
| Section_const -> ".text"
| Section_small_const -> ".sdata2"
| Section_string -> ".text"
| Section_literal -> ".text"
| Section_jumptable -> ".text"
| Section_user(s, wr, ex) -> s

(** Taken from CompCert *)
let name_of_section: section_name -> string =
  begin match Configuration.system with
  | "macosx" -> fatal "Unsupported CompCert configuration: macosx"
  | "linux"  -> name_of_section_Linux
  | "diab"   -> name_of_section_Diab
  | _        -> fatal "Unsupported CompCert configuration"
  end

(** Compares a CompCert section name with an ELF section name. *)
let match_sections_name
    (c_section: section_name) (e_name: string) (sfw: s_framework):
    s_framework
    =
  let c_name = name_of_section c_section in
  try
    let (value, conflicts) = StringMap.find c_name sfw.ef.section_map in
    let expected = from_inferrable value in
    if e_name = expected
    then sfw
    else (
      sfw
      >>> (sf_ef |-- section_map) ^%=
        StringMap.add c_name (value, StringSet.add e_name conflicts)
    )
  with Not_found -> (
    sfw
    >>> (sf_ef |-- section_map) ^%=
      StringMap.add c_name (Inferred(e_name), StringSet.empty)
  )

(** Checks the symbol table entry of the function symbol number [sym_ndx],
    according to CompCert's [ident].
*)
let check_fun_symtab
    (ident: ident) (sym_ndx: int) (sfw: s_framework):
    s_framework
    =
  let elf = sfw.ef.elf in
  let symtab_sndx = from_some (section_ndx_by_name elf ".symtab") in
  let symtab_ent_start =
    Int32.(add
             elf.e_shdra.(symtab_sndx).sh_offset
             (Safe32.of_int (16 * sym_ndx))) in
  let sym = sfw.ef.elf.e_symtab.(sym_ndx) in
  let atom = Hashtbl.find sfw.atoms ident in
  let section =
    match atom.a_sections with
    | [t; _; _] -> t
    | _ -> Section_text
  in
  sfw
  >>> check_st_bind atom sym
  >>> (
    if sym.st_type = STT_FUNC
    then id
    else (sf_ef ^%=
        add_log (ERROR("Symbol should have type STT_FUNC"))
    )
  )
  >>> (
    if sym.st_other = 0
    then id
    else (sf_ef ^%=
        add_log (ERROR("Symbol should have st_other set to 0"))
    )
  )
  >>> match_sections_name section elf.e_shdra.(sym.st_shndx).sh_name
  >>> sf_ef ^%=
      add_range symtab_ent_start 16l 4 (Symtab_function(sym))

(** Checks that the offset [ofs] is well aligned with regards to [al], expressed
    in bytes. *)
let is_well_aligned (ofs: int32) (al: int): bool =
  al = 0 || Int32.rem ofs (Safe32.of_int al) = 0l

(** Adds a function symbol to the set of covered symbols. *)
let mark_covered_fun_sym_ndx (ndx: int) ffw: f_framework =
  let elf = ffw.sf.ef.elf in
  let sym = elf.e_symtab.(ndx) in
  let sym_sndx = sym.st_shndx in
  let sym_size = sym.st_size in
  let sym_shdr = elf.e_shdra.(sym_sndx) in
  let sym_vaddr = sym.st_value in
  let sym_ofs_local = Int32.sub sym_vaddr sym_shdr.sh_addr in
  let sxn_ofs = sym_shdr.sh_offset in
  let sym_begin = Int32.add sxn_ofs sym_ofs_local in
  let atom = Hashtbl.find ffw.sf.atoms ffw.this_ident in
  let align =
    match atom.a_alignment with
    | Some(a) -> a
    | None -> 0
  in
  ffw.sf.ef.chkd_fun_syms.(ndx) <- true;
  ffw
  >>> (ff_ef ^%= add_range sym_begin sym_size align (Function_symbol(sym)))
  >>> (ff_sf ^%=
      if not (is_well_aligned sym_ofs_local align)
      then (
        sf_ef ^%=
          add_log (ERROR("Symbol not correctly aligned in the ELF file"))
      )
      else id
  )
  >>> (ff_sf ^%= check_fun_symtab ffw.this_ident ndx)

(** Taken from CompCert *)
let re_variadic_stub: Str.regexp = Str.regexp "\\(.*\\)\\$[if]*$"

(** Tries to refine the mapping for key [k] in [ident_to_sym_ndx] so that it is
    mapped to [vaddr]. Fails if no symbol in [k]'s mapping has that virtual
    address, unless the symbol is a stub from CompCert. Otherwise, it filters
    out all symbols whose virtual address does not match [vaddr].
*)
let idmap_unify (k: P.t) (vaddr: int32) (sfw: s_framework)
    : s_framework or_err =
  try (
    (* get the list of possible symbols for ident [k] *)
    let id_ndxes = PosMap.find k sfw.ident_to_sym_ndx in
    (* consider only the ones at the correct virtual address *)
    match List.filter
      (fun ndx -> sfw.ef.elf.e_symtab.(ndx).st_value = vaddr)
      id_ndxes
    with
    | [] ->
        (* no symbol has that virtual address *)
        let ident_name = Hashtbl.find sfw.ident_to_name k in
        if Str.string_match re_variadic_stub ident_name 0
        then (* this ident needs a stub, whose address is [vaddr] *)
          try (
            (* fetch the registered virtual address for this stub *)
            let v = PosMap.find k sfw.stub_ident_to_vaddr in
            (* if there is one, we're good if it's the same as [vaddr] *)
            if vaddr = v
            then OK(sfw)
            else ERR(
              Printf.sprintf
                "Incoherent constraints for stub: %s"
                (Hashtbl.find sfw.ident_to_name k)
            )
          )
          with Not_found ->
            (* if the stub has no previously registered virtual address,
               register [vaddr] *)
            OK(
              sfw
              >>> (stub_ident_to_vaddr ^%= PosMap.add k vaddr)
            )
        else (* not a stub, so this is a real error *)
          ERR(
            Printf.sprintf
              "Incoherent constraints for ident %s with value %s and candidates [%s]"
              (Hashtbl.find sfw.ident_to_name k)
              (string_of_int32 vaddr)
              (string_of_list
                 (fun ndx -> string_of_int32 sfw.ef.elf.e_symtab.(ndx).st_value)
                 ", " id_ndxes
              )
          )
    | ndxes ->
        if id_ndxes = ndxes
        then OK(sfw)
        else OK((ident_to_sym_ndx ^%= (PosMap.add k ndxes)) sfw)
  )
  with
  | Not_found ->
      ERR(
        Printf.sprintf
          "Missing ident: %s should be at vaddr: %s"
          (Hashtbl.find sfw.ident_to_name k)
          (string_of_int32 vaddr)
      )

(** Checks whether the label [k] points to [v] in [label_to_vaddr]. If it points
    to another virtual address, this returns an ERR. If it points to nothing,
    the mapping [k] -> [v] is added. Thus, the first time a label is
    encountered determines the expected virtual address of its destination.
    Subsequent references to the label will have to conform.
*)
let lblmap_unify (k: label) (v: int32) (ffw: f_framework)
    : f_framework or_err =
  try (
    let v' = PosMap.find k ffw.label_to_vaddr in
    if v = v'
    then OK ffw
    else (
      ERR(
        "Incoherent constraints for label " ^
          string_of_positive k ^ " with values " ^
          string_of_int32 v ^ " and " ^ string_of_int32 v'
      )
    )
  )
  with
  | Not_found ->
      OK {
        ffw with
          label_to_vaddr = PosMap.add k v ffw.label_to_vaddr
      }

let ireg_arr: ireg array =
  [|
    GPR0; GPR1; GPR2; GPR3; GPR4; GPR5; GPR6; GPR7; GPR8; GPR9; GPR10; GPR11;
    GPR12; GPR13; GPR14; GPR15; GPR16; GPR17; GPR18; GPR19; GPR20; GPR21; GPR22;
    GPR23; GPR24; GPR25; GPR26; GPR27; GPR28; GPR29; GPR30; GPR31
  |]

let freg_arr: freg array =
  [|
    FPR0; FPR1; FPR2; FPR3; FPR4; FPR5; FPR6; FPR7; FPR8; FPR9; FPR10; FPR11;
    FPR12; FPR13; FPR14; FPR15; FPR16; FPR17; FPR18; FPR19; FPR20; FPR21; FPR22;
    FPR23; FPR24; FPR25; FPR26; FPR27; FPR28; FPR29; FPR30; FPR31
  |]

let crbit_arr: crbit array =
  [|
    CRbit_0; CRbit_1; CRbit_2; CRbit_3
  |]

type checker = f_framework -> f_framework or_err
let check (cond: bool) (msg: string): checker =
  fun ffw -> if cond then OK(ffw) else ERR(msg)
let check_eq (msg: string) (a: 'a) (b: 'a): checker =
  check (a = b) msg
let match_bools a b =
  check_eq (
    Printf.sprintf "match_bools %s %s" (string_of_bool a) (string_of_bool b)
  ) a b
let match_ints a b =
  check_eq (
    Printf.sprintf "match_ints %s %s" (string_of_int a) (string_of_int b)
  ) a b
let match_int32s a b: checker =
  check_eq (
    Printf.sprintf "match_int32s %s %s" (string_of_int32 a) (string_of_int32 b)
  ) a b
(** We compare floats by their bit representation, so that 0.0 and -0.0 are
    different. *)
let match_floats (a: Floats.float) (b: float): checker =
  let a = Int64.bits_of_float (camlfloat_of_coqfloat a) in
  let b = Int64.bits_of_float b in
  check_eq (
    Printf.sprintf "match_floats %s %s" (string_of_int64 a) (string_of_int64 b)
  ) a b
let match_crbits cb eb =
  let eb = crbit_arr.(eb) in
  check_eq (
    Printf.sprintf "match_crbits %s %s" (string_of_crbit cb) (string_of_crbit eb)
  ) cb eb
let match_iregs  cr er =
  let er = ireg_arr.(er) in
  check_eq (
    Printf.sprintf "match_iregs %s %s" (string_of_ireg cr) (string_of_ireg er)
  ) cr er
let match_fregs  cr er =
  let er = freg_arr.(er) in
  check_eq (
    Printf.sprintf "match_fregs %s %s" (string_of_freg cr) (string_of_freg er)
  ) cr er

let name_of_ndx (efw: e_framework) (ndx: int): string =
  let st = efw.elf.e_symtab.(ndx) in
  st.st_name ^ " at address " ^ (string_of_int32 st.st_value)

(** Filters the lower 16 bits of an int32. *)
let low: int32 -> int32 = Int32.logand 0x0000ffffl

(** high_exts x is equal to:

    - the 16 high bits of x if its lower 16 bits form a positive 16 bit integer

    - the 16 high bits of x plus one otherwise

    This is so that: x == high_exts x + exts (low x)
*)
let high_exts (x: int32): int32 = Int32.(
  if logand x 0x00008000l = 0l
  then logand x 0xffff0000l
  else add 0x00010000l (logand x 0xffff0000l)
)

(** Matches a CompCert constant against an [int32]. *)
let match_csts (cc: constant) (ec: int32): checker = fun ffw ->
  let sfw = ffw |. ff_sf in
  let efw = ffw |. ff_ef in
  match cc with
  | Cint (i) ->
      let i = z_int32_lax i in
      let msg =
        Printf.sprintf "match_csts Cint %s %s"
          (string_of_int32 i)
          (string_of_int32 ec)
      in
      check_eq msg ec i ffw
  | Csymbol_low (ident, i) ->
      let candidates =
        try PosMap.find ident sfw.ident_to_sym_ndx
        with Not_found -> []
      in
      let vaddrs =
        List.filter
          (fun ndx ->
            let ident_vaddr = efw.elf.e_symtab.(ndx).st_value in
            Int32.(low (add ident_vaddr (z_int32_lax i)) = low ec)
          )
          candidates
      in
      begin match vaddrs with
      | [] ->
          let sym_names = List.map (name_of_ndx efw) candidates in
          ERR("Csymbol_low " ^ string_of_list id ", " sym_names)
      | _  ->
          if candidates = vaddrs
          then OK(ffw)
          else OK(
            ffw
            >>> ((ff_sf |-- ident_to_sym_ndx) ^%= (PosMap.add ident vaddrs))
          )
      end
  | Csymbol_high (ident, i) ->
      (* In this case, ec is 0x0000XXXX standing for XXXX0000 *)
      let candidates =
        try PosMap.find ident sfw.ident_to_sym_ndx
        with Not_found -> []
      in
      let vaddrs =
        List.filter
          (fun ndx ->
            let ident_vaddr = efw.elf.e_symtab.(ndx).st_value in
            Int32.(high_exts (add ident_vaddr (z_int32_lax i))
                   = shift_left ec 16))
          candidates in
      begin match vaddrs with
      | [] ->
          let sym_names = List.map (name_of_ndx efw) candidates in
          ERR("Csymbol_high " ^ string_of_list id ", " sym_names)
      | _  ->
          if candidates = vaddrs
          then OK(ffw)
          else OK(
            ffw
            >>> ((ff_sf |-- ident_to_sym_ndx) ^%= (PosMap.add ident vaddrs))
          )
      end
  | Csymbol_sda (ident, i) ->
      (* sda should be handled separately in places it occurs *)
      fatal "Unhandled Csymbol_sda, please report."

let match_z_int32 (cz: Z.t) (ei: int32) =
  let cz = z_int32 cz in
  check_eq (
    Printf.sprintf "match_z_int32 %s %s" (string_of_int32 cz) (string_of_int32 ei)
  ) cz ei

let match_z_int (cz: Z.t) (ei: int) =
  let cz = z_int32 cz in
  let ei = Safe32.of_int ei in
  check_eq (
    Printf.sprintf "match_z_int %s %s" (string_of_int32i cz) (string_of_int32i ei)
  ) cz ei

(* [m] is interpreted as a bitmask, and checked against [ei]. *)
let match_mask (m: Z.t) (ei: int32) =
  let m = z_int32_lax m in
  check_eq (
    Printf.sprintf "match_mask %s %s"
      (string_of_int32 m)
      (string_of_int32 ei)
  ) m ei

(** Checks that the special register referred to in [spr] is [r]. *)
let match_spr (str: string) (r: int) (spr: bitstring): checker = fun ffw ->
  bitmatch spr with
  | { v:5; 0:5 } when v = r -> OK(ffw)
  | { _ }                   -> ERR(str)

let match_xer   = match_spr "match_xer" 1
let match_lr    = match_spr "match_lr"  8
let match_ctr   = match_spr "match_ctr" 9

(** Read a n-bits bitstring as a signed integer, two's complement representation
    (n < 32).
*)
let exts (bs: bitstring): int32 =
  let signif_bits = Bitstring.bitstring_length bs - 1 in
  bitmatch bs with
  | { sign : 1                 ;
      rest : signif_bits : int } ->
      Int64.(
        to_int32 (
          if sign
          then logor rest (lognot (sub (shift_left one signif_bits) one))
          else rest
        )
      )

(** Creates a bitmask from bits mb to me, according to the specification in
    "4.2.1.4 Integer Rotate and Shift Instructions" of the PowerPC manual.
*)
let rec bitmask mb me =
  assert (0 <= mb); assert (0 <= me); assert (mb < 32); assert (me < 32);
  if (mb, me) = (0, 31)
  then -1l (* this case does not compute correctly otherwise *)
  else if mb <= me
  (* 0 ... mb ... me ... 31
     0 0 0 1 1 1 1 1 0 0 0
  *)
  then Int32.(shift_left
                (sub (shift_left 1l (me - mb + 1)) 1l)
                (31 - me)
  )
  (*
    0 ... me ... mb ... 31
    1 1 1 1 0 0 0 1 1 1 1
    ==
    1 1 1 1 1 1 1 1 1 1 1    -1l
    -
    0 0 0 0 1 1 1 0 0 0 0    bitmask (me + 1) (mb - 1)
  *)
  else if mb = me + 1
  then (-1l) (* this needs special handling *)
  else Int32.(sub (-1l) (bitmask (me + 1) (mb - 1)))

(** Checks that a label did not occur twice in the same function. *)
let check_label_unicity ffw =
  let rec check_label_unicity_aux l ffw =
    match l with
    | []   -> ffw
    | h::t ->
        ffw
        >>> (
          if List.mem h t
          then (
            ff_ef ^%=
              (add_log (ERROR("Duplicate label: " ^ string_of_positive h)))
          )
          else id
        )
        >>> check_label_unicity_aux t
  in
  check_label_unicity_aux ffw.label_list ffw

(** Checks that all the labels that have been referred to in instructions
    actually appear in the code. *)
let check_label_existence ffw =
  PosMap.fold
    (fun k v ->
      if List.mem k ffw.label_list
      then id
      else (
        ff_ef ^%=
          (add_log (ERROR("Missing label: " ^ string_of_positive k)))
      )
    )
    ffw.label_to_vaddr
    ffw

(** Matches the segment at virtual address [vaddr] with the jumptable expected
    from label list [lbllist]. Then checks whether the matched chunk of the code
    had the expected [size].
*)
let rec match_jmptbl lbllist vaddr size ffw =
  let atom = Hashtbl.find ffw.sf.atoms ffw.this_ident in
  let jmptbl_section =
    match atom.a_sections with
    | [_; _; j] -> j
    | _ -> Section_jumptable
  in
  let rec match_jmptbl_aux lbllist bs ffw =
    match lbllist with
    | [] -> OK ffw
    | lbl :: lbls -> (
      bitmatch bs with
      | { vaddr : 32 : int;
          rest : -1 : bitstring } ->
          ffw
          >>> lblmap_unify lbl vaddr
          >>= match_jmptbl_aux lbls rest
      | { _ } ->
          ERR("Ill-formed jump table")
    )
  in
  let elf = ffw.sf.ef.elf in
  begin match section_at_vaddr elf vaddr with
  | None -> ERR("No section for the jumptable")
  | Some(sndx) ->
      begin match bitstring_at_vaddr elf vaddr size with
      | None -> ERR("")
      | Some(bs, pofs, psize) ->
          ffw
          >>> (ff_sf ^%=
              match_sections_name jmptbl_section elf.e_shdra.(sndx).sh_name
          )
          >>> match_jmptbl_aux lbllist bs
          >>^ (ff_ef ^%=
              add_range pofs psize 0 Jumptable
          )
      end
  end

(** Matches [ecode] agains the expected code for a small memory copy
    pseudo-instruction. Returns a triple containing the updated framework,
    the remaining ELF code, and the updated program counter.
*)
let match_memcpy_small ecode pc sz al src dst (fw: f_framework)
    : (f_framework * ecode * int32) or_err =
  let error = ERR("match_memcpy_small") in
  let rec match_memcpy_small_aux ofs sz ecode pc (fw: f_framework) =
    let ofs32 = Safe32.of_int ofs in
    if sz >= 8 && al >= 4
    then (
      match ecode with
      |   LFD (frD0, rA0, d0) ::
          STFD(frS1, rA1, d1) :: es ->
          OK(fw)
          >>= match_fregs  FPR0  frD0
          >>= match_iregs  src   rA0
          >>= match_int32s ofs32 (exts d0)
          >>= match_fregs  FPR0  frS1
          >>= match_iregs  dst   rA1
          >>= match_int32s ofs32 (exts d1)
          >>= match_memcpy_small_aux (ofs + 8) (sz - 8) es (Int32.add 8l pc)
      | _ -> error
    )
    else if sz >= 4
    then (
      match ecode with
      |   LWZ(rD0, rA0, d0) ::
          STW(rS1, rA1, d1) :: es ->
          OK(fw)
          >>= match_iregs  GPR0  rD0
          >>= match_iregs  src   rA0
          >>= match_int32s ofs32 (exts d0)
          >>= match_iregs  GPR0  rS1
          >>= match_iregs  dst   rA1
          >>= match_int32s ofs32 (exts d0)
          >>= match_memcpy_small_aux (ofs + 4) (sz - 4) es (Int32.add 8l pc)
      | _ -> error
    )
    else if sz >= 2
    then (
      match ecode with
      |   LHZ(rD0, rA0, d0) ::
          STH(rS1, rA1, d1) :: es ->
          OK(fw)
          >>= match_iregs  GPR0  rD0
          >>= match_iregs  src   rA0
          >>= match_int32s ofs32 (exts d0)
          >>= match_iregs  GPR0  rS1
          >>= match_iregs  dst   rA1
          >>= match_int32s ofs32 (exts d0)
          >>= match_memcpy_small_aux (ofs + 2) (sz - 2) es (Int32.add 8l pc)
      | _ -> error
    )
    else if sz >= 1
    then (
      match ecode with
      |   LBZ(rD0, rA0, d0) ::
          STB(rS1, rA1, d1) :: es ->
          OK(fw)
          >>= match_iregs  GPR0  rD0
          >>= match_iregs  src   rA0
          >>= match_int32s ofs32 (exts d0)
          >>= match_iregs  GPR0  rS1
          >>= match_iregs  dst   rA1
          >>= match_int32s ofs32 (exts d0)
          >>= match_memcpy_small_aux (ofs + 1) (sz - 1) es (Int32.add 8l pc)
      | _ -> error
    )
    else OK(fw, ecode, pc)
  in match_memcpy_small_aux 0 sz ecode pc fw

(** Matches [ecode] agains the expected code for a big memory copy
    pseudo-instruction. Returns a triple containing the updated framework,
    the remaining ELF code, and the updated program counter.
*)
let match_memcpy_big ecode pc sz al src dst fw
    : (f_framework * ecode * int32) or_err =
  let error = ERR("match_memcpy_big") in
  match ecode with
  |   ADDI (rD0, rA0, simm0)           :: (* pc *)
      MTSPR(rS1, spr1)                 ::
      ADDI (rD2, rA2, simm2)           ::
      ADDI (rD3, rA3, simm3)           ::
      LWZU (rD4, rA4, d4)              :: (* pc + 16 <-  *)
      STWU (rS5, rA5, d5)              :: (*           | *)
      BCx  (bo6,  bi6,  bd6, aa6, lk6) :: (* pc + 24 --  *)
      es ->
      let sz' = Safe32.of_int (sz / 4) in
      let (s, d) = if dst <> GPR11 then (GPR11, GPR12) else (GPR12, GPR11) in
      let target_vaddr = Int32.(add 16l pc) in
      let dest_vaddr = Int32.(add (add 24l pc) (mul 4l (exts bd6))) in
      OK(fw)
      >>= match_iregs  GPR0  rD0
      >>= match_iregs  GPR0  rA0
      >>= match_int32s sz'   (exts simm0)
      >>= match_iregs  GPR0  rS1
      >>= match_ctr    spr1
      >>= match_iregs  s     rD2
      >>= match_iregs  src   rA2
      >>= match_int32s (-4l) (exts simm2)
      >>= match_iregs  d     rD3
      >>= match_iregs  dst   rA3
      >>= match_int32s (-4l) (exts simm3)
      >>= match_iregs  GPR0  rD4
      >>= match_iregs  s     rA4
      >>= match_int32s 4l    (exts d4)
      >>= match_iregs  GPR0  rS5
      >>= match_iregs  d     rA5
      >>= match_int32s 4l    (exts d5)
      >>= (fun ffw ->
        bitmatch bo6 with
        | { 16:5:int } -> OK(ffw)
        | { _ }        -> ERR("bitmatch bo")
      )
      >>= match_ints   bi6   0
      >>= match_int32s dest_vaddr target_vaddr
      >>= match_bools  false aa6
      >>= match_bools  false lk6
      >>= (fun fw ->
        match sz land 3 with
        | 1 ->
            begin match es with
            |   LBZ(rD0, rA0, d0) ::
                STB(rS1, rA1, d1) :: es ->
                OK(fw)
                >>= match_iregs  GPR0 rD0
                >>= match_iregs  s    rA0
                >>= match_int32s 4l   (exts d0)
                >>= match_iregs  GPR0 rS1
                >>= match_iregs  d    rA1
                >>= match_int32s 4l   (exts d1)
                >>= (fun fw -> OK(fw, es, Int32.add 36l pc))
            | _ -> error
            end
        | 2 ->
            begin match es with
            |   LHZ(rD0, rA0, d0) ::
                STH(rS1, rA1, d1) :: es ->
                OK(fw)
                >>= match_iregs  GPR0 rD0
                >>= match_iregs  s    rA0
                >>= match_int32s 4l   (exts d0)
                >>= match_iregs  GPR0 rS1
                >>= match_iregs  d    rA1
                >>= match_int32s 4l   (exts d1)
                >>= (fun fw -> OK(fw, es , Int32.add 36l pc))
            | _ -> error
            end
        | 3 ->
            begin match es with
            |   LHZ(rD0, rA0, d0) ::
                STH(rS1, rA1, d1) ::
                LBZ(rD2, rA2, d2) ::
                STB(rS3, rA3, d3) :: es ->
                OK(fw)
                >>= match_iregs  GPR0 rD0
                >>= match_iregs  s    rA0
                >>= match_int32s 4l   (exts d0)
                >>= match_iregs  GPR0 rS1
                >>= match_iregs  d    rA1
                >>= match_int32s 4l   (exts d1)
                >>= match_iregs  GPR0 rD2
                >>= match_iregs  s    rA2
                >>= match_int32s 6l   (exts d2)
                >>= match_iregs  GPR0 rS3
                >>= match_iregs  d    rA3
                >>= match_int32s 6l   (exts d3)
                >>= (fun fw -> OK(fw, es, Int32.add 44l pc))
            | _ -> error
            end
        | _ -> OK(fw, es, Int32.add 28l pc)
      )
  | _ -> error

let match_bo_bt_bool bo =
  bitmatch bo with
  | { false:1; true:1; true:1; false:1; false:1 } -> true
  | { _ } -> false

let match_bo_bf_bool bo =
  bitmatch bo with
  | { false:1; false:1; true:1; false:1; false:1 } -> true
  | { _ } -> false

let match_bo_bt bo: checker = fun ffw ->
  bitmatch bo with
  | { false:1; true:1; true:1; false:1; false:1 } -> OK(ffw)
  | { _ } -> ERR("match_bo_bt")

let match_bo_bf bo: checker = fun ffw ->
  if match_bo_bf_bool bo
  then OK(ffw)
  else ERR("match_bo_bf")

let match_bo_ctr bo: checker = fun ffw ->
  bitmatch bo with
  | { true:1; false:1; true:1; false:1; false:1 } -> OK(ffw)
  | { _ } -> ERR("match_bo_ctr")

(** Checks whether it is feasible that the position at offset [ofs] from the
    CompCert symbol [ident] is situated at a relative address [addr] from
    the SDA register [r]. This means that the following equation must hold:
    [r] + addr = @ident + ofs
    This allows us to determine what address [r] has to contain. If it is the
    first such guess or if it matches previous expectations, it's fine.
    Otherwise, there is a conflict that is reported in sda_map.
*)
let check_sda ident ofs r addr ffw: f_framework or_err =
  let ofs = z_int32 ofs in
  let check_sda_aux ndx: (int * f_framework) or_err =
    let elf = ffw.sf.ef.elf in
    let sym = elf.e_symtab.(ndx) in
    let expected_addr = Safe32.(sym.st_value + ofs - addr) in
    try
      let r_addr = from_inferrable (IntMap.find r ffw.sf.ef.sda_map) in
      if r_addr = expected_addr
      then OK(ndx, ffw)
      else ERR(
        Printf.sprintf
          "SDA register %d is expected to point both at 0x%lx and 0x%lx"
          r r_addr expected_addr
      )
    with Not_found ->
      OK(ndx,
         ffw >>> (ff_ef |-- sda_map) ^%= IntMap.add r (Inferred(expected_addr))
      )
  in
  (* We might not know yet what symbols is the one for that ident *)
  let sym_list = PosMap.find ident ffw.sf.ident_to_sym_ndx in
  (* So we test all the candidates *)
  let res = List.map check_sda_aux sym_list in
  (* For now, we hope at most one matches *)
  match filter_ok res with
  | [] -> ERR("No satisfying SDA mapping, errors were: " ^
                 string_of_list id ", " (filter_err res))
  | [(ndx, ffw)] -> OK(
    ffw
    (* We instantiate the relationship for that ident to the matching symbol *)
    >>> (ff_sf |-- ident_to_sym_ndx) ^%= PosMap.add ident [ndx]
  )
  | _ -> fatal "Multiple possible SDA mappings, please report."

(** Compares a whole CompCert function code against an ELF code, starting at
    program counter [pc].
*)
let rec compare_code ccode ecode pc: checker = fun fw ->
  match ccode, ecode with
  | [], [] -> OK(fw)
  | [], e_rest ->
      let rest_str = String.concat "\n" (List.map string_of_instr e_rest) in
      ERR("CompCert code exhausted before the end of ELF code, remaining:\n"
          ^ rest_str)
  | c_rest, [] ->
      let rest_str = String.concat "\n" (List.map string_of_instruction c_rest) in
      ERR("ELF code exhausted before the end of CompCert code, remaining:\n"
          ^ rest_str)
  | c::cs, e::es  ->
      let recur_simpl = compare_code cs es (Int32.add 4l pc) in
      let current_instr =
        "[" ^ string_of_int32 pc ^ "] " ^ string_of_instruction c ^ " - " ^ string_of_instr e in
      let error = ERR("Non-matching instructions: " ^ current_instr) in
      let fw =
        if !debug
        then (ff_ef ^%= add_log (DEBUG(current_instr))) fw
        else fw
      in
      match c with
      | Padd(rd, r1, r2) ->
          begin match ecode with
          | ADDx(rD, rA, rB, oe, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rD
              >>= match_iregs r1    rA
              >>= match_iregs r2    rB
              >>= match_bools false oe
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Padde(rd, r1, r2) ->
          begin match ecode with
          | ADDEx(rD, rA, rB, oe, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rD
              >>= match_iregs r1    rA
              >>= match_iregs r2    rB
              >>= match_bools false oe
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Paddi(rd, r1, Csymbol_sda(ident, ofs)) ->
          begin match ecode with
          | ADDI(rD, rA, simm) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= check_sda ident ofs rA (exts simm)
              >>= recur_simpl
          | _ -> error
          end
      | Paddi(rd, r1, cst) ->
          begin match ecode with
          | ADDI(rD, rA, simm) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= match_iregs r1  rA
              >>= match_csts  cst (exts simm)
              >>= recur_simpl
          | _ -> error
          end
      | Paddic(rd, r1, cst) ->
          begin match ecode with
          | ADDIC(rD, rA, simm) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= match_iregs r1  rA
              >>= match_csts  cst (exts simm)
              >>= recur_simpl
          | _ -> error
          end
      | Paddis(rd, r1, cst) ->
          begin match ecode with
          | ADDIS(rD, rA, simm) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= match_iregs r1  rA
              >>= match_csts  cst (Safe32.of_int simm)
              >>= recur_simpl
          | _ -> error
          end
      | Paddze(rd, r1) ->
          begin match ecode with
          | ADDZEx(rD, rA, oe, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rD
              >>= match_iregs r1    rA
              >>= match_bools false oe
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pallocframe(sz, ofs) ->
          begin match ecode with
          | STWU(rS, rA, d) :: es ->
              OK(fw)
              >>= match_iregs   GPR1 rS
              >>= match_iregs   GPR1 rA
              >>= match_z_int32 sz   (Int32.neg (exts d))
              >>= match_z_int32 ofs  0l
              >>= recur_simpl
          |   ADDIS   (rD0, rA0, simm0)  ::
              ORI     (rS1, rA1, uimm1)  ::
              STWUX   (rS2, rA2, rB2)    :: es ->
              let sz32 = Int32.neg (z_int32 sz) in
              let sz_hi = Int32.shift_right_logical sz32 16 in
              let sz_lo = Int32.logand sz32 0xFFFFl in
              OK(fw)
              >>= match_iregs  GPR12 rD0
              >>= match_iregs  GPR0  rA0
              >>= match_int32s sz_hi (Safe32.of_int simm0)
              >>= match_iregs  GPR12 rS1
              >>= match_iregs  GPR12 rA1
              >>= match_int32s sz_lo (Safe32.of_int uimm1)
              >>= match_iregs  GPR1  rS2
              >>= match_iregs  GPR1  rA2
              >>= match_iregs  GPR12 rB2
              >>= compare_code cs es (Int32.add 12l pc)
          | _ -> error
          end
      | Pandc(rd, r1, r2) ->
          begin match ecode with
          | ANDCx(rS, rA, rB, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_iregs r2    rB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pand_(rd, r1, r2) ->
          begin match ecode with
          | ANDx(rS, rA, rB, rc) :: es ->
              OK(fw)
              >>= match_iregs rd   rA
              >>= match_iregs r1   rS
              >>= match_iregs r2   rB
              >>= match_bools true rc
              >>= recur_simpl
          | _ -> error
          end
      | Pandis_(rd, r1, cst) ->
          begin match ecode with
          | ANDIS_(rS, rA, uimm) :: es ->
              OK(fw)
              >>= match_iregs rd  rA
              >>= match_iregs r1  rS
              >>= match_csts  cst (Safe32.of_int uimm)
              >>= recur_simpl
          | _ -> error
          end
      | Pandi_(rd, r1, cst) ->
          begin match ecode with
          | ANDI_(rS, rA, uimm) :: es ->
              OK(fw)
              >>= match_iregs rd  rA
              >>= match_iregs r1  rS
              >>= match_csts  cst (Safe32.of_int uimm)
              >>= recur_simpl
          | _ -> error
          end
      | Pannot(ef, args) ->
          OK(fw)
          >>= compare_code cs ecode pc
      | Pb(lbl) ->
          begin match ecode with
          | Bx(li, aa, lk) :: es ->
              let lblvaddr = Int32.(add pc (mul 4l (exts li))) in
              OK(fw)
              >>= lblmap_unify lbl   lblvaddr
              >>= match_bools  false aa
              >>= match_bools  false lk
              >>= recur_simpl
          | _ -> error
          end
      | Pbctr ->
          begin match ecode with
          | BCCTRx(bo, bi, lk) :: es ->
              OK(fw)
              >>= match_bo_ctr bo
              >>= match_ints  0     bi
              >>= match_bools false lk
              >>= recur_simpl
          | _ -> error
          end
      | Pbctrl ->
          begin match ecode with
          | BCCTRx(bo, bi, lk) :: es ->
              OK(fw)
              >>= match_bo_ctr bo
              >>= match_ints  0    bi
              >>= match_bools true lk
              >>= recur_simpl
          | _ -> error
          end
      | Pbf(bit, lbl) ->
          begin match ecode with
          | BCx(bo, bi, bd, aa, lk) :: es when match_bo_bf_bool bo ->
              let lblvaddr = Int32.(add pc (mul 4l (exts bd))) in
              OK(fw)
              (*>>= match_bo_bf  bo   already done in pattern match *)
              >>= match_crbits bit   bi
              >>= lblmap_unify lbl   lblvaddr
              >>= match_bools  false aa
              >>= match_bools  false lk
              >>= recur_simpl
          |   BCx(bo0, bi0, bd0, aa0, lk0) ::
              Bx (li1, aa1, lk1)           :: es ->
              let cnext = Int32.add pc 8l in
              let enext = Int32.(add pc (mul 4l (exts bd0))) in
              let lblvaddr = Int32.(add pc (mul 4l (exts bd0))) in
              OK(fw)
              >>= match_bo_bt  bo0
              >>= match_crbits bit bi0
              >>= match_int32s cnext enext
              >>= match_bools  false aa0
              >>= match_bools  false lk0
              >>= lblmap_unify lbl   lblvaddr
              >>= match_bools  false aa1
              >>= match_bools  false lk1
              >>= compare_code cs es (Int32.add 8l pc)
          | _ -> error
          end
      | Pbl(ident) ->
          begin match ecode with
          | Bx(li, aa, lk) :: es ->
              let dest = Int32.(add pc (mul 4l (exts li))) in
              OK(fw)
              >>= (ff_sf ^%=? idmap_unify ident dest)
              >>= match_bools false aa
              >>= match_bools true  lk
              >>= recur_simpl
          | _ -> error
          end
      | Pblr ->
          begin match ecode with
          | BCLRx(bo, bi, lk) :: es ->
              OK(fw)
              >>= match_bo_ctr bo
              >>= match_ints  0     bi
              >>= match_bools false lk
              >>= recur_simpl
          | _ -> error
          end
      | Pbs(ident) ->
          begin match ecode with
          | Bx(li, aa, lk) :: es ->
              let dest = Int32.(add pc (mul 4l (exts li))) in
              OK(fw)
              >>= match_bools false aa
              >>= match_bools false lk
              >>= (ff_sf ^%=? idmap_unify ident dest)
              >>= recur_simpl
          | _ -> error
          end
      | Pbt(bit, lbl) ->
          begin match ecode with
          | BCx(bo, bi, bd, aa, lk) :: es when match_bo_bt_bool bo ->
              let lblvaddr = Int32.(add pc (mul 4l (exts bd))) in
              OK(fw)
              (*>>= match_bo_bt  bo   already done in pattern match *)
              >>= match_crbits bit   bi
              >>= lblmap_unify lbl   lblvaddr
              >>= match_bools  false aa
              >>= match_bools  false lk
              >>= recur_simpl
          |   BCx(bo0, bi0, bd0, aa0, lk0) ::
              Bx (li1, aa1, lk1)           :: es ->
              let cnext = Int32.add pc 8l in
              let enext = Int32.(add pc (mul 4l (exts bd0))) in
              let lblvaddr = Int32.(add pc (mul 4l (exts bd0))) in
              OK(fw)
              >>= match_bo_bf  bo0
              >>= match_crbits bit bi0
              >>= match_int32s cnext enext
              >>= match_bools  false aa0
              >>= match_bools  false lk0
              >>= lblmap_unify lbl   lblvaddr
              >>= match_bools  false aa1
              >>= match_bools  false lk1
              >>= compare_code cs es (Int32.add 8l pc)
          | _ -> error
          end
      | Pbtbl(reg, table) ->
          begin match ecode with
          |   RLWINMx(rS0, rA0, sh, mb, me, rc0) ::
              ADDIS (rD1, rA1, simm1) ::
              LWZ   (rD2, rA2, d2)    ::
              MTSPR (rS3, spr3)       ::
              BCCTRx(bo4, bi4, rc4)   :: es ->
              let tblvaddr = Int32.(
                add (shift_left (Safe32.of_int simm1) 16) (exts d2)
              ) in
              let tblsize = Safe32.of_int (32 * List.length table) in
              OK(fw)
              >>= match_iregs  GPR12 rA0
              >>= match_iregs  reg   rS0
              >>= match_ints   sh    2
              >>= match_ints   mb    0
              >>= match_ints   me    29
              >>= match_bools  false rc0
              >>= match_iregs  GPR12 rA1
              >>= match_iregs  GPR12 rD1
              >>= match_iregs  GPR12 rA2
              >>= match_iregs  GPR12 rD2
              >>= match_iregs  GPR12 rS3
              >>= match_ctr    spr3
              >>= match_bo_ctr bo4
              >>= match_ints   0     bi4
              >>= match_bools  false rc4
              >>= match_jmptbl table tblvaddr tblsize
              >>= compare_code cs es (Int32.add 20l pc)
          | _ -> error
          end
      | Pbuiltin(ef, args, res) ->
          begin match ef with
          | EF_builtin(name, sg) ->
              begin match Hashtbl.find
                  (fw |. ff_sf).ident_to_name name, args, res with
                  | "__builtin_mulhw", [IR a1; IR a2], [IR res] ->
                      begin match ecode with
                      | MULHWx(rD, rA, rB, rc) :: es ->
                          OK(fw)
                          >>= match_iregs res   rD
                          >>= match_iregs a1    rA
                          >>= match_iregs a2    rB
                          >>= match_bools false rc
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_mulhwu", [IR a1; IR a2], [IR res] ->
                      begin match ecode with
                      | MULHWUx(rD, rA, rB, rc) :: es ->
                          OK(fw)
                          >>= match_iregs res   rD
                          >>= match_iregs a1    rA
                          >>= match_iregs a2    rB
                          >>= match_bools false rc
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_cntlz", [IR a1], [IR res] ->
                      begin match ecode with
                      | CNTLZWx(rS, rA, rc) :: es ->
                          OK(fw)
                          >>= match_iregs a1    rS
                          >>= match_iregs res   rA
                          >>= match_bools false rc
                          >>= recur_simpl
                      | _ -> error
                      end
                  | ("__builtin_bswap"|"__builtin_bswap32"), [IR a1], [IR res] ->
                      begin match ecode with
                      |   STWU (rS0, rA0, d0)    ::
                          LWBRX(rD1, rA1, rB1)   ::
                          ADDI (rD2, rA2, simm2) :: es ->
                          OK(fw)
                          >>= match_iregs  a1    rS0
                          >>= match_iregs  GPR1  rA0
                          >>= match_int32s (-8l) (exts d0)
                          >>= match_iregs  res   rD1
                          >>= match_iregs  GPR0  rA1
                          >>= match_iregs  GPR1  rB1
                          >>= match_iregs  GPR1  rD2
                          >>= match_iregs  GPR1  rA2
                          >>= match_int32s 8l    (exts simm2)
                          >>= compare_code cs es (Int32.add 12l pc)
                      | _ -> error
                      end
                  | "__builtin_bswap16", [IR a1], [IR res] ->
                      begin match ecode with
                      |   RLWINMx(rS1, rA1, sh1, mb1, me1, rc1) ::
                          RLWINMx(rS2, rA2, sh2, mb2, me2, rc2) ::
                          ORx(rS3, rA3, rB3, rc3) :: es ->
                          OK(fw)
                          >>= match_iregs  GPR0  rS1
                          >>= match_iregs  a1    rA1
                          >>= check_eq "bswap16-1" sh1 8
                          >>= check_eq "bswap16-2" mb1 16
                          >>= check_eq "bswap16-3" me1 23
                          >>= match_iregs  res   rS2
                          >>= match_iregs  a1    rA2
                          >>= check_eq "bswap16-4" sh2 24
                          >>= check_eq "bswap16-5" mb2 24
                          >>= check_eq "bswap16-6" me2 31
                          >>= match_iregs  res   rS3
                          >>= match_iregs  GPR0  rA3
                          >>= match_iregs  res   rB3
                          >>= compare_code cs es (Int32.add 12l pc)
                      | _ -> error
                      end
                  | "__builtin_fmadd", [FR a1; FR a2; FR a3], [FR res] ->
                      begin match ecode with
                      | FMADDx(frD, frA, frB, frC, rc) :: es ->
                          OK(fw)
                          >>= match_fregs res frD
                          >>= match_fregs a1 frA
                          >>= match_fregs a3 frB
                          >>= match_fregs a2 frC
                          >>= match_bools false rc
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fmsub", [FR a1; FR a2; FR a3], [FR res] ->
                      begin match ecode with
                      | FMSUBx(frD, frA, frB, frC, rc) :: es ->
                          OK(fw)
                          >>= match_fregs res frD
                          >>= match_fregs a1 frA
                          >>= match_fregs a3 frB
                          >>= match_fregs a2 frC
                          >>= match_bools false rc
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fnmadd", [FR a1; FR a2; FR a3], [FR res] ->
                      begin match ecode with
                      | FNMADDx(frD, frA, frB, frC, rc) :: es ->
                          OK(fw)
                          >>= match_fregs res frD
                          >>= match_fregs a1 frA
                          >>= match_fregs a3 frB
                          >>= match_fregs a2 frC
                          >>= match_bools false rc
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fnmsub", [FR a1; FR a2; FR a3], [FR res] ->
                      begin match ecode with
                      | FNMSUBx(frD, frA, frB, frC, rc) :: es ->
                          OK(fw)
                          >>= match_fregs res frD
                          >>= match_fregs a1 frA
                          >>= match_fregs a3 frB
                          >>= match_fregs a2 frC
                          >>= match_bools false rc
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fabs", [FR a1], [FR res] ->
                      begin match ecode with
                      | FABSx(frD, frB, rc) :: es ->
                          OK(fw)
                          >>= match_fregs res   frD
                          >>= match_fregs a1    frB
                          >>= match_bools false rc
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fsqrt", [FR a1], [FR res] ->
                      begin match ecode with
                      | FSQRTx(frD, frB, rc) :: es ->
                          OK(fw)
                          >>= match_fregs res   frD
                          >>= match_fregs a1    frB
                          >>= match_bools false rc
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_frsqrte", [FR a1], [FR res] ->
                      begin match ecode with
                      | FRSQRTEx(frD, frB, rc) :: es ->
                          OK(fw)
                          >>= match_fregs res   frD
                          >>= match_fregs a1    frB
                          >>= match_bools false rc
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fres", [FR a1], [FR res] ->
                      begin match ecode with
                      | FRESx(frD, frB, rc) :: es ->
                          OK(fw)
                          >>= match_fregs res   frD
                          >>= match_fregs a1    frB
                          >>= match_bools false rc
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fsel", [FR a1; FR a2; FR a3], [FR res] ->
                      begin match ecode with
                      | FSELx(frD, frA, frB, frC, rc) :: es ->
                          OK(fw)
                          >>= match_fregs res frD
                          >>= match_fregs a1 frA
                          >>= match_fregs a3 frB
                          >>= match_fregs a2 frC
                          >>= match_bools false rc
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fcti", [FR r1], [IR rd] ->
                      begin match ecode with
                      | FCTIWx(frD0, frB0, rc0)   ::
                        STFDU  (frS1, rA1,  d1)    ::
                        LWZ    (rD2,  rA2,  d2)    ::
                        ADDI   (rD3,  rA3,  simm3) :: es ->
                          OK(fw)
                          >>= match_fregs  FPR13 frD0
                          >>= match_fregs  r1    frB0
                          >>= match_bools  false rc0
                          >>= match_fregs  FPR13 frS1
                          >>= match_iregs  GPR1  rA1
                          >>= match_int32s (-8l) (exts d1)
                          >>= match_iregs  rd    rD2
                          >>= match_iregs  GPR1  rA2
                          >>= match_int32s 4l    (exts d2)
                          >>= match_iregs  GPR1  rD3
                          >>= match_iregs  GPR1  rA3
                          >>= match_int32s 8l    (exts simm3)
                          >>= compare_code cs es (Int32.add 16l pc)
                      | _ -> error
                      end
                  | "__builtin_read16_reversed", [IR a1], [IR res] ->
                      begin match ecode with
                      | LHBRX(rD, rA, rB):: es ->
                          OK(fw)
                          >>= match_iregs res  rD
                          >>= match_iregs GPR0 rA
                          >>= match_iregs a1   rB
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_read32_reversed", [IR a1], [IR res] ->
                      begin match ecode with
                      | LWBRX(rD, rA, rB) :: es ->
                          OK(fw)
                          >>= match_iregs res  rD
                          >>= match_iregs GPR0 rA
                          >>= match_iregs a1   rB
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_write16_reversed", [IR a1; IR a2], _ ->
                      begin match ecode with
                      | STHBRX(rS, rA, rB) :: es ->
                          OK(fw)
                          >>= match_iregs a2   rS
                          >>= match_iregs GPR0 rA
                          >>= match_iregs a1   rB
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_write32_reversed", [IR a1; IR a2], _ ->
                      begin match ecode with
                      | STWBRX(rS, rA, rB) :: es ->
                          OK(fw)
                          >>= match_iregs a2   rS
                          >>= match_iregs GPR0 rA
                          >>= match_iregs a1   rB
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_eieio", [], _ ->
                      begin match ecode with
                      | EIEIO :: es ->
                          OK(fw)
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_sync", [], _ ->
                      begin match ecode with
                      | SYNC :: es ->
                          OK(fw)
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_isync", [], _ ->
                      begin match ecode with
                      | ISYNC :: es ->
                          OK(fw)
                          >>= recur_simpl
                      | _ -> error
                      end
                  | "__builtin_trap", [], _ ->
                      begin match ecode with
                      | TW(tO, rA, rB) :: es ->
                          OK(fw)
                          >>= (fun ffw ->
                            bitmatch tO with
                            | { 31 : 5 : int } -> OK(ffw)
                            | { _ } -> ERR("bitmatch")
                          )
                          >>= match_iregs GPR0 rA
                          >>= match_iregs GPR0 rB
                          >>= recur_simpl
                      | _ -> error
                      end
                  | _ -> error
              end
          | EF_vload(chunk) ->
              begin match args with
              | [IR addr] ->
                  OK(fw)
                  >>= check_builtin_vload_common
                    cs ecode pc chunk addr (Cint Integers.Int.zero) res
              | _ -> fatal "Unexpected args in EF_vload, please report."
              end
          | EF_vstore(chunk) ->
              begin match args with
              | [IR addr; src] ->
                  OK(fw)
                  >>= check_builtin_vstore_common
                    cs ecode pc chunk addr (Cint Integers.Int.zero) src
              | _ -> fatal "Unexpected args in EF_vstore, please report."
              end
          | EF_vload_global(chunk, ident, ofs) ->
              begin match ecode with
              | ADDIS(rD, rA, simm) :: es ->
                  let high = Csymbol_high(ident, ofs) in
                  OK(fw)
                  >>= match_iregs  GPR11 rD
                  >>= match_iregs  GPR0  rA
                  >>= match_csts   high  (Safe32.of_int simm)
                  >>= check_builtin_vload_common
                    cs es (Int32.add pc 4l) chunk GPR11
                    (Csymbol_low(ident, ofs)) res
              | _ -> error
              end
          | EF_vstore_global(chunk, ident, ofs) ->
              begin match args with
              | [src] ->
                  begin match ecode with
                  | ADDIS(rD, rA, simm) :: es ->
                      let tmp =
                        if src = IR GPR11
                        then GPR12
                        else GPR11
                      in
                      let high = Csymbol_high(ident, ofs) in
                      OK(fw)
                      >>= match_iregs  tmp   rD
                      >>= match_iregs  GPR0  rA
                      >>= match_csts   high  (Safe32.of_int simm)
                      >>= check_builtin_vstore_common
                        cs es (Int32.add pc 4l) chunk tmp
                        (Csymbol_low(ident, ofs)) src
                  | _ -> error
                  end
              | _ -> fatal "Unexpected args in EF_vstore_global, please report."
              end
          | EF_memcpy(sz, al) ->
              let sz = z_int sz in
              let al = z_int al in
              begin match args with
              | [IR dst; IR src] ->
                  if sz <= 64
                  then (
                    match match_memcpy_small ecode pc sz al src dst fw with
                    | ERR(s) -> ERR(s)
                    | OK(fw, es, pc) -> compare_code cs es pc fw
                  )
                  else (
                    match match_memcpy_big ecode pc sz al src dst fw with
                    | ERR(s) -> ERR(s)
                    | OK(fw, es, pc) -> compare_code cs es pc fw
                  )
              | _ -> error
              end
          | EF_annot_val(text, targ) ->
              begin match args, res with
              | IR src :: _, [IR dst] ->
                  if dst <> src
                  then (
                    match ecode with
                    | ORx(rS, rA, rB, rc) :: es ->
                        OK(fw)
                        >>= match_iregs src rS
                        >>= match_iregs dst rA
                        >>= match_iregs src rB
                        >>= match_bools false rc
                        >>= recur_simpl
                    | _ -> error
                  )
                  else compare_code cs ecode pc fw
              | FR src :: _, [FR dst] ->
                  if dst <> src
                  then (
                    match ecode with
                    | FMRx(frD, frB, rc) :: es ->
                        OK(fw)
                        >>= match_fregs dst frD
                        >>= match_fregs src frB
                        >>= match_bools false rc
                        >>= recur_simpl
                    | _ -> error
                  )
                  else compare_code cs ecode pc fw
              | _ -> error
              end
          | EF_annot(_, _)    -> fatal "Unexpected EF_annot, please report."
          | EF_external(_, _) -> fatal "Unexpected EF_external, please report."
          | EF_free           -> fatal "Unexpected EF_free, please report."
          | EF_malloc         -> fatal "Unexpected EF_malloc, please report."
          | EF_inline_asm(_)  -> fatal "Unsupported: inline asm statement."
          end
      | Pcmplw(r1, r2) ->
          begin match ecode with
          | CMPL(crfD, l, rA, rB) :: es ->
              OK(fw)
              >>= match_crbits CRbit_0 crfD
              >>= match_bools  false   l
              >>= match_iregs  r1      rA
              >>= match_iregs  r2      rB
              >>= recur_simpl
          | _ -> error
          end
      | Pcmplwi(r1, cst) ->
          begin match ecode with
          | CMPLI(crfD, l, rA, uimm) :: es ->
              OK(fw)
              >>= match_iregs  r1      rA
              >>= match_csts   cst     (Safe32.of_int uimm)
              >>= match_crbits CRbit_0 crfD
              >>= match_bools  false   l
              >>= recur_simpl
          | _ -> error
          end
      | Pcmpw(r1, r2) ->
          begin match ecode with
          | CMP(crfD, l, rA, rB) :: es ->
              OK(fw)
              >>= match_ints  crfD 0
              >>= match_bools l    false
              >>= match_iregs r1   rA
              >>= match_iregs r2   rB
              >>= recur_simpl
          | _ -> error
          end
      | Pcmpwi(r1, cst) ->
          begin match ecode with
          | CMPI(crfD, l, rA, simm) :: es ->
              OK(fw)
              >>= match_ints  crfD  0
              >>= match_bools false l
              >>= match_iregs r1    rA
              >>= match_csts  cst   (exts simm)
              >>= recur_simpl
          | _ -> error
          end
      | Pcror(bd, b1, b2) ->
          begin match ecode with
          | CROR(crbD, crbA, crbB) :: es ->
              OK(fw)
              >>= match_crbits bd crbD
              >>= match_crbits b1 crbA
              >>= match_crbits b2 crbB
              >>= recur_simpl
          | _ -> error
          end
      | Pdivw(rd, r1, r2) ->
          begin match ecode with
          | DIVWx(rD, rA, rB, oe, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rD
              >>= match_iregs r1    rA
              >>= match_iregs r2    rB
              >>= match_bools false oe
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pdivwu(rd, r1, r2) ->
          begin match ecode with
          | DIVWUx(rD, rA, rB, oe, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rD
              >>= match_iregs r1    rA
              >>= match_iregs r2    rB
              >>= match_bools false oe
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Peqv(rd, r1, r2) ->
          begin match ecode with
          | EQVx(rS, rA, rB, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_iregs r2    rB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pextsb(rd, r1) ->
          begin match ecode with
          | EXTSBx(rS, rA, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pextsh(rd, r1) ->
          begin match ecode with
          | EXTSHx(rS, rA, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pfabs(rd, r1) ->
          begin match ecode with
          | FABSx(frD, frB, rc) :: es ->
              OK(fw)
              >>= match_fregs rd    frD
              >>= match_fregs r1    frB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pfadd(rd, r1, r2) ->
          begin match ecode with
          | FADDx(frD, frA, frB, rc) :: es ->
              OK(fw)
              >>= match_fregs rd    frD
              >>= match_fregs r1    frA
              >>= match_fregs r2    frB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pfcmpu(r1, r2) ->
          begin match ecode with
          | FCMPU(crfD, frA, frB) :: es ->
              OK(fw)
              >>= match_crbits CRbit_0 crfD
              >>= match_fregs  r1      frA
              >>= match_fregs  r2      frB
              >>= recur_simpl
          | _ -> error
          end
      | Pfcti(rd, r1) ->
          begin match ecode with
          |   FCTIWZx(frD0, frB0, rc0)   ::
              STFDU  (frS1, rA1,  d1)    ::
              LWZ    (rD2,  rA2,  d2)    ::
              ADDI   (rD3,  rA3,  simm3) :: es ->
              OK(fw)
              >>= match_fregs  FPR13 frD0
              >>= match_fregs  r1    frB0
              >>= match_bools  false rc0
              >>= match_fregs  FPR13 frS1
              >>= match_iregs  GPR1  rA1
              >>= match_int32s (-8l) (exts d1)
              >>= match_iregs  rd    rD2
              >>= match_iregs  GPR1  rA2
              >>= match_int32s 4l    (exts d2)
              >>= match_iregs  GPR1  rD3
              >>= match_iregs  GPR1  rA3
              >>= match_int32s 8l    (exts simm3)
              >>= compare_code cs es (Int32.add 16l pc)
          | _ -> error
          end
      | Pfdiv(rd, r1, r2) ->
          begin match ecode with
          | FDIVx(frD, frA, frB, rc) :: es ->
              OK(fw)
              >>= match_fregs rd    frD
              >>= match_fregs r1    frA
              >>= match_fregs r2    frB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pfmake(rd, r1, r2) ->
          begin match ecode with
          |   STWU  (rS0, rA0, d0)    ::
              STW   (rS1, rA1, d1)    ::
              LFD   (frD2, rA2, d2)   ::
              ADDI  (rD3, rA3, simm3) :: es ->
              OK(fw)
              >>= match_iregs  r1    rS0
              >>= match_iregs  GPR1  rA0
              >>= match_int32s (-8l) (exts d0)
              >>= match_iregs  r2    rS1
              >>= match_iregs  GPR1  rA1
              >>= match_int32s 4l    (exts d1)
              >>= match_fregs  rd    frD2
              >>= match_iregs  GPR1  rA2
              >>= match_int32s 0l    (exts d2)
              >>= match_iregs  GPR1  rD3
              >>= match_iregs  GPR1  rA3
              >>= match_int32s 8l    (exts simm3)
              >>= compare_code cs es (Int32.add 16l pc)
          | _ -> error
          end
      | Pfmr(rd, r1) ->
          begin match ecode with
          | FMRx(frD, frB, rc) :: es ->
              OK(fw)
              >>= match_fregs rd    frD
              >>= match_fregs r1    frB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pfmul(rd, r1, r2) ->
          begin match ecode with
          | FMULx(frD, frA, frC, rc) :: es ->
              OK(fw)
              >>= match_fregs rd    frD
              >>= match_fregs r1    frA
              >>= match_fregs r2    frC
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pfneg (rd, r1) ->
          begin match ecode with
          | FNEGx(frD, frB, rc) :: es ->
              OK(fw)
              >>= match_fregs rd    frD
              >>= match_fregs r1    frB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pfreeframe(sz, ofs) ->
          begin match ecode with
          | ADDI(rD, rA, simm) :: es ->
              OK(fw)
              >>= match_iregs   GPR1 rD
              >>= match_iregs   GPR1 rA
              >>= match_z_int32 sz (exts simm)
              >>= recur_simpl
          | LWZ(rD, rA, d) :: es ->
              OK(fw)
              >>= match_iregs   GPR1 rD
              >>= match_iregs   GPR1 rA
              >>= match_z_int32 ofs  (exts d)
              >>= recur_simpl
          | _ -> error
          end
      | Pfrsp(rd, r1) ->
          begin match ecode with
          | FRSPx(frD, frB, rc) :: es ->
              OK(fw)
              >>= match_fregs rd    frD
              >>= match_fregs r1    frB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pfsub(rd, r1, r2) ->
          begin match ecode with
          | FSUBx(frD, frA, frB, rc) :: es ->
              OK(fw)
              >>= match_fregs rd    frD
              >>= match_fregs r1    frA
              >>= match_fregs r2    frB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Plabel(lbl) ->
          OK(fw)
          >>= lblmap_unify lbl pc
          >>^ (fun fw -> {fw with label_list = lbl :: fw.label_list})
          >>= compare_code cs ecode pc
      | Plbz(rd, Csymbol_sda(ident, ofs), r1) ->
          begin match ecode with
          | LBZ(rD, rA, d) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= check_sda ident ofs rA (exts d)
              >>= recur_simpl
          | _ -> error
          end
      | Plbz(rd, cst, r1) ->
          begin match ecode with
          | LBZ(rD, rA, d) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= match_csts  cst (exts d)
              >>= match_iregs r1  rA
              >>= recur_simpl
          | _ -> error
          end
      | Plbzx(rd, r1, r2) ->
          begin match ecode with
          | LBZX(rD, rA, rB) :: es ->
              OK(fw)
              >>= match_iregs rd rD
              >>= match_iregs r1 rA
              >>= match_iregs r2 rB
              >>= recur_simpl
          | _ -> error
          end
      | Plfd(rd, Csymbol_sda(ident, ofs), r1) ->
          begin match ecode with
          | LFD(frD, rA, d) :: es ->
              OK(fw)
              >>= match_fregs rd  frD
              >>= check_sda ident ofs rA (exts d)
              >>= recur_simpl
          | _ -> error
          end
      | Plfd(rd, cst, r1) ->
          begin match ecode with
          | LFD(frD, rA, d) :: es ->
              OK(fw)
              >>= match_fregs rd  frD
              >>= match_csts  cst (exts d)
              >>= match_iregs r1  rA
              >>= recur_simpl
          | _ -> error
          end
      | Plfdx(rd, r1, r2) ->
          begin match ecode with
          | LFDX(frD, rA, rB) :: es ->
              OK(fw)
              >>= match_fregs rd frD
              >>= match_iregs r1 rA
              >>= match_iregs r2 rB
              >>= recur_simpl
          | _ -> error
          end
      | Plfi(r1, c) ->
          begin match ecode with
          |   ADDIS(rD0, rA0, simm0) ::
              LFD  (frD1, rA1, d1)   :: es ->
              let vaddr = Int32.(
                add (shift_left (Safe32.of_int simm0) 16) (exts d1)
              ) in
              if Int32.rem vaddr 8l <> 0l
              then ERR("Float constants should be 8-byte aligned")
              else
                let elf = fw.sf.ef.elf in
                let atom = Hashtbl.find fw.sf.atoms fw.this_ident in
                let literal_section =
                  begin match atom.a_sections with
                  | [_; l; _] -> l
                  | _ -> Section_literal
                  end
                in
                let continue = compare_code cs es (Int32.add 8l pc) in
                begin match bitstring_at_vaddr elf vaddr 8l with
                | None ->
                    ERR("Floating point constant address is wrong")
                | Some(bs, pofs, psize) ->
                    let f =
                      bitmatch bs with
                      | { f : 64 : int } -> Int64.float_of_bits f
                    in
                    OK(fw)
                    >>= (fun ffw ->
                      begin match section_at_vaddr elf vaddr with
                      | None -> ERR("No section at that virtual address")
                      | Some(sndx) ->
                          let section_name = elf.e_shdra.(sndx).sh_name in
                          OK(
                            ffw
                            >>> (
                              ff_sf ^%=
                                match_sections_name literal_section section_name
                            )
                          )
                      end
                    )
                    >>= match_iregs  GPR12 rD0
                    >>= match_iregs  GPR0  rA0
                    >>= match_fregs  r1    frD1
                    >>= match_floats c     f
                    >>^ (ff_ef ^%= add_range pofs psize 8 (Float_literal(f)))
                    >>= match_iregs  GPR12 rA1
                    >>= continue
                end
          | _ -> error
          end
      | Plfs(rd, Csymbol_sda(ident, ofs), r1) ->
          begin match ecode with
          | LFS(frD, rA, d) :: es ->
              OK(fw)
              >>= match_fregs rd  frD
              >>= check_sda ident ofs rA (exts d)
              >>= recur_simpl
          | _ -> error
          end
      | Plfs(rd, cst, r1) ->
          begin match ecode with
          | LFS(frD, rA, d) :: es ->
              OK(fw)
              >>= match_fregs rd  frD
              >>= match_csts  cst (exts d)
              >>= match_iregs r1  rA
              >>= recur_simpl
          | _ -> error
          end
      | Plfsx(rd, r1, r2) ->
          begin match ecode with
          | LFSX(frD, rA, rB) :: es ->
              OK(fw)
              >>= match_fregs rd frD
              >>= match_iregs r1 rA
              >>= match_iregs r2 rB
              >>= recur_simpl
          | _ -> error
          end
      | Plha(rd, Csymbol_sda(ident, ofs), r1) ->
          begin match ecode with
          | LHA(rD, rA, d) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= check_sda ident ofs rA (exts d)
              >>= recur_simpl
          | _ -> error
          end
      | Plha(rd, cst, r1) ->
          begin match ecode with
          | LHA(rD, rA, d) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= match_csts  cst (exts d)
              >>= match_iregs r1  rA
              >>= recur_simpl
          | _ -> error
          end
      | Plhax(rd, r1, r2) ->
          begin match ecode with
          | LHAX(rD, rA, rB) :: es ->
              OK(fw)
              >>= match_iregs rd rD
              >>= match_iregs r1 rA
              >>= match_iregs r2 rB
              >>= recur_simpl
          | _ -> error
          end
      | Plhz(rd, Csymbol_sda(ident, ofs), r1) ->
          begin match ecode with
          | LHZ(rD, rA, d) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= check_sda ident ofs rA (exts d)
              >>= recur_simpl
          | _ -> error
          end
      | Plhz(rd, cst, r1) ->
          begin match ecode with
          | LHZ(rD, rA, d) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= match_csts  cst (exts d)
              >>= match_iregs r1  rA
              >>= recur_simpl
          | _ -> error
          end
      | Plhzx(rd, r1, r2) ->
          begin match ecode with
          | LHZX(rD, rA, rB) :: es ->
              OK(fw)
              >>= match_iregs rd rD
              >>= match_iregs r1 rA
              >>= match_iregs r2 rB
              >>= recur_simpl
          | _ -> error
          end
      | Plwz(rd, Csymbol_sda(ident, ofs), r1) ->
          begin match ecode with
          | LWZ(rD, rA, d) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= check_sda ident ofs rA (exts d)
              >>= recur_simpl
          | _ -> error
          end
      | Plwz(rd, cst, r1) ->
          begin match ecode with
          | LWZ(rD, rA, d) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= match_iregs r1  rA
              >>= match_csts  cst (exts d)
              >>= recur_simpl
          | _ -> error
          end
      | Plwzx(rd, r1, r2) ->
          begin match ecode with
          | LWZX(rD, rA, rB) :: es ->
              OK(fw)
              >>= match_iregs rd rD
              >>= match_iregs r1 rA
              >>= match_iregs r2 rB
              >>= recur_simpl
          | _ -> error
          end
      | Pmfcrbit(rd, bit) ->
          begin match ecode with
          |   MFCR   (rD0)                          ::
              RLWINMx(rS1, rA1, sh1, mb1, me1, rc1) :: es ->
              OK(fw)
              >>= match_iregs  rd    rD0
              >>= match_iregs  rd    rS1
              >>= match_iregs  rd    rA1
              >>= match_crbits bit   (sh1 - 1)
              >>= match_ints   31    mb1
              >>= match_ints   31    me1
              >>= match_bools  false rc1
              >>= compare_code cs es (Int32.add 8l pc)
          | _ -> error
          end
      | Pmflr(r) ->
          begin match ecode with
          | MFSPR(rD, spr) :: es ->
              OK(fw)
              >>= match_iregs r   rD
              >>= match_lr    spr
              >>= recur_simpl
          | _ -> error
          end
      | Pmr(rd, r1) ->
          begin match ecode with
          | ORx(rS, rA, rB, rc) :: es when (rB = rS) ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pmtctr(r1) ->
          begin match ecode with
          | MTSPR(rS, spr) :: es ->
              OK(fw)
              >>= match_iregs r1 rS
              >>= match_ctr   spr
              >>= recur_simpl
          | _ -> error
          end
      | Pmtlr(r1) ->
          begin match ecode with
          | MTSPR(rS, spr) :: es ->
              OK(fw)
              >>= match_iregs r1  rS
              >>= match_lr    spr
              >>= recur_simpl
          | _ -> error
          end
      | Pmulli(rd, r1, cst) ->
          begin match ecode with
          | MULLI(rD, rA, simm) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= match_iregs r1  rA
              >>= match_csts  cst (exts simm)
              >>= recur_simpl
          | _ -> error
          end
      | Pmullw(rd, r1, r2) ->
          begin match ecode with
          | MULLWx(rD, rA, rB, oe, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rD
              >>= match_iregs r1    rA
              >>= match_iregs r2    rB
              >>= match_bools false oe
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pnand(rd, r1, r2) ->
          begin match ecode with
          | NANDx(rS, rA, rB, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_iregs r2    rB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pnor(rd, r1, r2) ->
          begin match ecode with
          | NORx(rS, rA, rB, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_iregs r2    rB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Por(rd, r1, r2) ->
          begin match ecode with
          | ORx(rS, rA, rB, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_iregs r2    rB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Porc(rd, r1, r2) ->
          begin match ecode with
          | ORCx(rS, rA, rB, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_iregs r2    rB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pori(rd, r1, cst) ->
          begin match ecode with
          | ORI(rS, rA, uimm) :: es ->
              OK(fw)
              >>= match_iregs rd  rA
              >>= match_iregs r1  rS
              >>= match_csts  cst (Safe32.of_int uimm)
              >>= recur_simpl
          | _ -> error
          end
      | Poris(rd, r1, cst) ->
          begin match ecode with
          | ORIS(rS, rA, uimm) :: es ->
              OK(fw)
              >>= match_iregs rd  rA
              >>= match_iregs r1  rS
              >>= match_csts  cst (Safe32.of_int uimm)
              >>= recur_simpl
          | _ -> error
          end
      | Prlwimi(rd, r1, amount, mask) ->
          begin match ecode with
          | RLWIMIx(rS, rA, sh, mb, me, rc) :: es ->
              OK(fw)
              >>= match_iregs r1     rS
              >>= match_iregs rd     rA
              >>= match_z_int amount sh
              >>= match_mask  mask   (bitmask mb me)
              >>= match_bools false  rc
              >>= recur_simpl
          | _ -> error
          end
      | Prlwinm(rd, r1, amount, mask) ->
          begin match ecode with
          | RLWINMx(rS, rA, sh, mb, me, rc) :: es ->
              OK(fw)
              >>= match_iregs r1     rS
              >>= match_iregs rd     rA
              >>= match_z_int amount sh
              >>= match_mask  mask   (bitmask mb me)
              >>= match_bools false  rc
              >>= recur_simpl
          | _ -> error
          end
      | Pslw(rd, r1, r2) ->
          begin match ecode with
          | SLWx(rS, rA, rB, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_iregs r2    rB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Psraw(rd, r1, r2) ->
          begin match ecode with
          | SRAWx(rS, rA, rB, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_iregs r2    rB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Psrawi(rd, r1, n) ->
          begin match ecode with
          | SRAWIx(rS, rA, sh, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_z_int n     sh
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Psrw(rd, r1, r2) ->
          begin match ecode with
          | SRWx(rS, rA, rB, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_iregs r2    rB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pstb(rd, cst, r1) ->
          begin match ecode with
          | STB(rS, rA, d) :: es ->
              OK(fw)
              >>= match_iregs rd  rS
              >>= match_iregs r1  rA
              >>= match_csts  cst (exts d)
              >>= recur_simpl
          | _ -> error
          end
      | Pstbx(rd, r1, r2) ->
          begin match ecode with
          | STBX(rS, rA, rB) :: es ->
              OK(fw)
              >>= match_iregs rd rS
              >>= match_iregs r1 rA
              >>= match_iregs r2 rB
              >>= recur_simpl
          | _ -> error
          end
      | Pstfd(rd, cst, r1) ->
          begin match ecode with
          | STFD(frS, rA, d) :: es ->
              OK(fw)
              >>= match_fregs rd  frS
              >>= match_iregs r1  rA
              >>= match_csts  cst (exts d)
              >>= recur_simpl
          | _ -> error
          end
      | Pstfdx(rd, r1, r2) ->
          begin match ecode with
          | STFDX(frS, rA, rB) :: es ->
              OK(fw)
              >>= match_fregs rd frS
              >>= match_iregs r1 rA
              >>= match_iregs r2 rB
              >>= recur_simpl
          | _ -> error
          end
      | Pstfs(rd, cst, r1) ->
          begin match ecode with
          |   FRSPx(frD0, frB0, rc0) ::
              STFS (frS1, rA1,  d1)  :: es ->
              OK(fw)
              >>= match_fregs FPR13 frD0
              >>= match_fregs rd    frB0
              >>= match_bools false rc0
              >>= match_fregs FPR13 frS1
              >>= match_iregs r1    rA1
              >>= match_csts  cst (exts d1)
              >>= compare_code cs es (Int32.add 8l pc)
          | _ -> error
          end
      | Pstfsx(rd, r1, r2) ->
          begin match ecode with
          |   FRSPx(frD0, frB0, rc0) ::
              STFSX(frS1, rA1,  rB1) :: es ->
              OK(fw)
              >>= match_fregs FPR13 frD0
              >>= match_fregs rd    frB0
              >>= match_bools false rc0
              >>= match_fregs FPR13 frS1
              >>= match_iregs r1    rA1
              >>= match_iregs r2    rB1
              >>= compare_code cs es (Int32.add 8l pc)
          | _ -> error
          end
      | Psth(rd, cst, r1) ->
          begin match ecode with
          | STH(rS, rA, d) :: es ->
              OK(fw)
              >>= match_iregs rd  rS
              >>= match_iregs r1  rA
              >>= match_csts  cst (exts d)
              >>= recur_simpl
          | _ -> error
          end
      | Psthx(rd, r1, r2) ->
          begin match ecode with
          | STHX(rS, rA, rB) :: es ->
              OK(fw)
              >>= match_iregs rd rS
              >>= match_iregs r1 rA
              >>= match_iregs r2 rB
              >>= recur_simpl
          | _ -> error
          end
      | Pstw(rd, cst, r1) ->
          begin match ecode with
          | STW(rS, rA, d) :: es ->
              OK(fw)
              >>= match_iregs rd  rS
              >>= match_iregs r1  rA
              >>= match_csts  cst (exts d)
              >>= recur_simpl
          | _ -> error
          end
      | Pstwx(rd, r1, r2) ->
          begin match ecode with
          | STWX(rS, rA, rB) :: es ->
              OK(fw)
              >>= match_iregs rd rS
              >>= match_iregs r1 rA
              >>= match_iregs r2 rB
              >>= recur_simpl
          | _ -> error
          end
      | Psubfc(rd, r1, r2) ->
          begin match ecode with
          | SUBFCx(rD, rA, rB, oe, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rD
              >>= match_iregs r1    rA
              >>= match_iregs r2    rB
              >>= match_bools false oe
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Psubfe(rd, r1, r2) ->
          begin match ecode with
          | SUBFEx(rD, rA, rB, oe, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rD
              >>= match_iregs r1    rA
              >>= match_iregs r2    rB
              >>= match_bools false oe
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Psubfic(rd, r1, cst) ->
          begin match ecode with
          | SUBFIC(rD, rA, simm) :: es ->
              OK(fw)
              >>= match_iregs rd  rD
              >>= match_iregs r1  rA
              >>= match_csts  cst (exts simm)
              >>= recur_simpl
          | _ -> error
          end
      | Pxor(rd, r1, r2) ->
          begin match ecode with
          | XORx(rS, rA, rB, rc) :: es ->
              OK(fw)
              >>= match_iregs rd    rA
              >>= match_iregs r1    rS
              >>= match_iregs r2    rB
              >>= match_bools false rc
              >>= recur_simpl
          | _ -> error
          end
      | Pxori(rd, r1, cst) ->
          begin match ecode with
          | XORI(rS, rA, uimm) :: es ->
              OK(fw)
              >>= match_iregs rd  rA
              >>= match_iregs r1  rS
              >>= match_csts  cst (Safe32.of_int uimm)
              >>= recur_simpl
          | _ -> error
          end
      | Pxoris(rd, r1, cst) ->
          begin match ecode with
          | XORIS(rS, rA, uimm) :: es ->
              OK(fw)
              >>= match_iregs rd  rA
              >>= match_iregs r1  rS
              >>= match_csts  cst (Safe32.of_int uimm)
              >>= recur_simpl
          | _ -> error
          end
and check_builtin_vload_common ccode ecode pc chunk addr offset res fw =
  let error = ERR("Non-matching instructions") in
  let recur_simpl = compare_code ccode (List.tl ecode) (Int32.add pc 4l) in
  begin match chunk, res with
  | Mint8unsigned, [IR res] ->
      begin match ecode with
      | LBZ(rD, rA, d) :: es ->
          OK(fw)
          >>= match_iregs  res    rD
          >>= match_iregs  addr   rA
          >>= match_csts   offset (exts d)
          >>= recur_simpl
      | _ -> error
      end
  | Mint8signed, [IR res] ->
      begin match ecode with
      |   LBZ   (rD0, rA0, d0)  ::
          EXTSBx(rS1, rA1, rc1) :: es ->
          OK(fw)
          >>= match_iregs  res    rD0
          >>= match_iregs  addr   rA0
          >>= match_csts   offset (exts d0)
          >>= match_iregs  res    rS1
          >>= match_iregs  res    rA1
          >>= match_bools  false  rc1
          >>= compare_code ccode es (Int32.add 8l pc)
      | _ -> error
      end
  | Mint16unsigned, [IR res] ->
      begin match ecode with
      | LHZ(rD, rA, d) :: es ->
          OK(fw)
          >>= match_iregs  res    rD
          >>= match_iregs  addr   rA
          >>= match_csts   offset (exts d)
          >>= recur_simpl
      | _ -> error
      end
  | Mint16signed, [IR res] ->
      begin match ecode with
      | LHA(rD, rA, d) :: es ->
          OK(fw)
          >>= match_iregs  res    rD
          >>= match_iregs  addr   rA
          >>= match_csts   offset (exts d)
          >>= recur_simpl
      | _ -> error
      end
  | Mint32, [IR res] ->
      begin match ecode with
      | LWZ(rD, rA, d) :: es ->
          OK(fw)
          >>= match_iregs  res    rD
          >>= match_iregs  addr   rA
          >>= match_csts   offset (exts d)
          >>= recur_simpl
      | _ -> error
      end
  | Mfloat32, [FR res] ->
      begin match ecode with
      | LFS(frD, rA, d) :: es ->
          OK(fw)
          >>= match_fregs  res    frD
          >>= match_iregs  addr   rA
          >>= match_csts   offset (exts d)
          >>= recur_simpl
      | _ -> error
      end
  | (Mfloat64 | Mfloat64al32), [FR res] ->
      begin match ecode with
      | LFD(frD, rA, d) :: es ->
          OK(fw)
          >>= match_fregs  res    frD
          >>= match_iregs  addr   rA
          >>= match_csts   offset (exts d)
          >>= recur_simpl
      | _ -> error
      end
  | _ -> error
  end
and check_builtin_vstore_common ccode ecode pc chunk addr offset src fw =
  let recur_simpl = compare_code ccode (List.tl ecode) (Int32.add pc 4l) in
  let error = ERR("Non-matching instructions") in
  begin match chunk, src with
  | (Mint8signed | Mint8unsigned), IR src ->
      begin match ecode with
      | STB(rS, rA, d) :: es ->
          OK(fw)
          >>= match_iregs  src    rS
          >>= match_iregs  addr   rA
          >>= match_csts   offset (exts d)
          >>= recur_simpl
      | _ -> error
      end
  | (Mint16signed | Mint16unsigned), IR src ->
      begin match ecode with
      | STH(rS, rA, d) :: es ->
          OK(fw)
          >>= match_iregs  src    rS
          >>= match_iregs  addr   rA
          >>= match_csts   offset (exts d)
          >>= recur_simpl
      | _ -> error
      end
  | Mint32, IR src ->
      begin match ecode with
      | STW(rS, rA, d) :: es ->
          OK(fw)
          >>= match_iregs  src    rS
          >>= match_iregs  addr   rA
          >>= match_csts   offset (exts d)
          >>= recur_simpl
      | _ -> error
      end
  | Mfloat32, FR src ->
      begin match ecode with
      |   FRSPx(frD0, frB0, rc0) ::
          STFS (frS1, rA1,  d1)  :: es ->
          OK(fw)
          >>= match_fregs  FPR13  frD0
          >>= match_fregs  src    frB0
          >>= match_bools  false  rc0
          >>= match_fregs  FPR13  frS1
          >>= match_iregs  addr   rA1
          >>= match_csts   offset (exts d1)
          >>= compare_code ccode es (Int32.add pc 8l)
      | _ -> error
      end
  | (Mfloat64 | Mfloat64al32), FR src ->
      begin match ecode with
      | STFD(frS, rA, d) :: es ->
          OK(fw)
          >>= match_fregs  src    frS
          >>= match_iregs  addr   rA
          >>= match_csts   offset (exts d)
          >>= recur_simpl
      | _ -> error
      end
  | _ -> error
  end

(** A work element is a triple giving a CompCert ident for the function to
    analyze, its name as a string, and the actual code. It is not obvious how
    to recover one of the three components given the other two.
*)
type worklist = (ident * string * ccode) list

(** Pops a work element from the worklist, ensuring that fully-determined idents
    (i.e. those for which the possible virtual address have been narrowed to one
    candidate) are picked first.
    When the first element is not fully-determined, the whole list is sorted so
    that hopefully several fully-determined idents are brought at the beginning
    at the same time.
*)
let worklist_pop fw wl =
  match wl with
  | []           -> None
  | h::t ->
      let (i, _, _) = h in
      let candidates =
        try PosMap.find i fw.ident_to_sym_ndx
        with Not_found -> []
      in
      match candidates with
      | [] | [_] -> Some (h, t, candidates)
      | _ ->
          let wl = List.fast_sort
            (fun (i1, _, _) (i2, _, _) ->
              compare
                (List.length (PosMap.find i1 fw.ident_to_sym_ndx))
                (List.length (PosMap.find i2 fw.ident_to_sym_ndx)))
            wl in
          let winner = List.hd wl in
          let (i, _, _) = winner in
          Some (winner, List.tl wl, PosMap.find i fw.ident_to_sym_ndx)

(** Processes a worklist, threading in the framework.
*)
let rec worklist_process (wl: worklist) sfw: s_framework =
  match worklist_pop sfw wl with
  | None -> sfw (*done*)
  | Some ((ident, name, ccode), wl, candidates) ->
      let process_ndx ndx = (
        let elf = (sfw |. sf_ef).elf in
        let pc = elf.e_symtab.(ndx).st_value in
        match code_of_sym_ndx elf ndx with
        | None -> ERR("Could not find symbol data for function symbol " ^ name)
        | Some ecode ->
            sfw
            >>> sf_ef ^%=
            add_log (DEBUG("Processing function: " ^ name))
            >>> (fun sfw ->
              {
                sf = sfw;
                this_sym_ndx = ndx;
                this_ident = ident;
                label_to_vaddr = PosMap.empty;
                label_list = [];
              }
            )
            >>> compare_code ccode ecode pc
            >>^ mark_covered_fun_sym_ndx ndx
      ) in
      begin match candidates with
      | []    ->
          sfw
          >>> sf_ef ^%=
          add_log (ERROR("Skipping missing symbol " ^ name))
          >>> worklist_process wl
      | [ndx] ->
          begin match process_ndx ndx with
          | OK(ffw) ->
              ffw
              >>> check_label_existence
              >>> check_label_unicity
              >>> (fun ffw ->
                worklist_process wl ffw.sf
              )
          | ERR(s) ->
              sfw
              >>> sf_ef ^%=
              add_log (ERROR(
                Printf.sprintf
                  "Unique candidate for %s did not match: %s"
                  name
                  s
              ))
              >>> worklist_process wl
          end
      | ndxes ->
          (* Multiple candidates for one symbol *)
          let fws = filter_ok (List.map process_ndx ndxes) in
          begin match fws with
          | [] ->
              sfw
              >>> sf_ef ^%=
              add_log (ERROR("No matching candidate for: " ^ name))
              >>> worklist_process wl
          | [ffw] ->
              worklist_process wl ffw.sf
          | fws ->
              sfw
              >>> sf_ef ^%=
              add_log (ERROR(
                "Multiple matching candidates for: " ^ name
              ))
              >>> worklist_process wl
          end
      end

(** Compares a data symbol with its expected contents. Returns the updated
    framework as well as the size of the data matched.
**)
let compare_data (l: init_data list) (bs: bitstring) (sfw: s_framework)
    : (s_framework * int) or_err =
  let error = ERR("Reached end of data bitstring too soon") in
  let rec compare_data_aux l bs s (sfw: s_framework):
      (s_framework * int) or_err =
    match l with
    | [] -> OK(sfw, s)
    | d::l ->
        let sfw =
          if !debug
          then (
            (sf_ef ^%= add_log (DEBUG("  " ^ string_of_init_data d))) sfw
          )
          else sfw
        in
        begin match d with
        | Init_int8(i) -> (
          bitmatch bs with
          | { j : 8 : int; bs : -1 : bitstring } ->
              if (z_int_lax i) land 0xFF = j
              then compare_data_aux l bs (s + 1) sfw
              else ERR("Wrong int8")
          | { _ } -> error
        )
        | Init_int16(i) -> (
          bitmatch bs with
          | { j : 16 : int; bs : -1 : bitstring } ->
              if (z_int_lax i) land 0xFFFF = j
              then compare_data_aux l bs (s + 2) sfw
              else ERR("Wrong int16")
          | { _ } -> error
        )
        | Init_int32(i) -> (
          bitmatch bs with
          | { j : 32 : int; bs : -1 : bitstring } ->
              if z_int32_lax i = j
              then compare_data_aux l bs (s + 4) sfw
              else ERR("Wrong int32")
          | { _ } -> error
        )
        | Init_float32(f) -> (
          bitmatch bs with
          | { j : 32 : int; bs : -1 : bitstring } ->
              if camlfloat_of_coqfloat f = Int32.float_of_bits j
              then compare_data_aux l bs (s + 4) sfw
              else ERR("Wrong float32")
          | { _ } -> error
        )
        | Init_float64(f) -> (
          bitmatch bs with
          | { j : 64 : int; bs : -1 : bitstring } ->
              if camlfloat_of_coqfloat f = Int64.float_of_bits j
              then compare_data_aux l bs (s + 8) sfw
              else ERR("Wrong float64")
          | { _ } -> error
        )
        | Init_int64(i) -> (
          bitmatch bs with
          | { j : 64 : int; bs : -1 : bitstring } ->
              if z_int64 i = j
              then compare_data_aux l bs (s + 8) sfw
              else ERR("Wrong int64")
          | { _ } -> error
        )
        | Init_space(z) -> (
          let space_size = z_int z in
          bitmatch bs with
          | { space : space_size * 8 : bitstring; bs : -1 : bitstring } ->
              if is_zeros space (space_size * 8)
              then compare_data_aux l bs (s + space_size) sfw
              else ERR("Wrong space " ^
                          string_of_int (z_int z) ^ " " ^
                          string_of_bitstring space)
          | { _ } -> error
        )
        | Init_addrof(ident, ofs) -> (
          bitmatch bs with
          | { vaddr : 32 : int; bs : -1 : bitstring } ->
              sfw
              >>> idmap_unify ident (Int32.sub vaddr (z_int32 ofs))
              >>= compare_data_aux l bs (s + 4)
          | { _ } -> error
        )
        end
  in
  compare_data_aux l bs 0 sfw

(** Checks the data symbol table.
*)
let check_data_symtab ident sym_ndx size sfw =
  let elf = sfw.ef.elf in
  let symtab_ent_start = Int32.(
    add
      elf.e_shdra.(elf.e_symtab_sndx).sh_offset
      (Safe32.of_int (16 * sym_ndx))
  ) in
  let sym = sfw.ef.elf.e_symtab.(sym_ndx) in
  let atom = Hashtbl.find sfw.atoms ident in
  let section =
    match atom.a_sections with
    | [s] -> s
    | _ -> Section_data true
  in
  sfw
  >>> (
    if sym.st_size = Safe32.of_int size
    then id
    else (
      sf_ef ^%=
        add_log (ERROR(
          "Incorrect symbol size (" ^ sym.st_name ^
            "): expected " ^ string_of_int32i sym.st_size ^
            ", counted: " ^ string_of_int size
        ))
    )
  )
  >>> check_st_bind atom sym
  >>> (
    match sym.st_type with
    | STT_OBJECT -> id
    | STT_NOTYPE -> (sf_ef ^%=
        add_log (WARNING("Missing type for symbol " ^ sym.st_name))
    )
    | _ -> (sf_ef ^%=
        add_log (ERROR("Symbol should have type STT_OBJECT"))
    )
  )
  >>> (
    if sym.st_other = 0
    then id
    else (sf_ef ^%=
        add_log (ERROR("Symbol should have st_other set to 0"))
    )
  )
  >>> match_sections_name section elf.e_shdra.(sym.st_shndx).sh_name
  >>> (sf_ef ^%=
      add_range symtab_ent_start 16l 4 (Symtab_data(sym))
  )

(** Checks all the program variables.
*)
let check_data (pv: (ident * unit globvar) list) (sfw: s_framework)
    : s_framework =
  let process_ndx ident ldata sfw ndx =
    let elf = sfw.ef.elf in
    let sym = elf.e_symtab.(ndx) in
    let sym_vaddr = sym.st_value in
    begin match bitstring_at_vaddr_nosize elf sym_vaddr with
    | None -> ERR("Could not find symbol data for data symbol " ^ sym.st_name)
    | Some(sym_bs, pofs, psize) ->
        let res =
          sfw
          >>> (sf_ef ^%= add_log (DEBUG("Processing data: " ^ sym.st_name)))
          >>> compare_data ldata sym_bs
        in
        begin match res with
        | ERR(s) -> ERR(s)
        | OK(sfw, size) ->
            let align =
              begin match (Hashtbl.find sfw.atoms ident).a_alignment with
              | None -> 0
              | Some(a) -> a
              end
            in
            sfw.ef.chkd_data_syms.(ndx) <- true;
            OK(sfw)
            >>= (fun sfw ->
              if size = 0
              then OK(sfw) (* These occupy no space, for now we just forget them *)
              else OK(
                sfw
                >>> sf_ef ^%=
                  add_range pofs (Safe32.of_int size) align (Data_symbol(sym))
              )
            )
            >>= (fun sfw ->
              if not (is_well_aligned sym_vaddr align)
              then ERR("Symbol not correctly aligned in the ELF file")
              else OK(sfw)
            )
            >>^ check_data_symtab ident ndx size
        end
    end
  in
  let check_data_aux sfw ig =
    let (ident, gv) = ig in
    let init_data = gv.gvar_init in
    let ident_ndxes = PosMap.find ident sfw.ident_to_sym_ndx in
    (*print_endline ("Candidates: " ^ string_of_list id ", "
      (List.map
      (fun ndx -> fw.elf.e_symtab.(ndx).st_name)
      ident_ndxes));*)
    let results = List.map (process_ndx ident init_data sfw) ident_ndxes in
    let successes = filter_ok results in
    match successes with
    | [] ->
        sfw
        >>> sf_ef ^%=
        add_log (ERROR(
          "No matching data segment among candidates [" ^
            (string_of_list
               (fun ndx -> sfw.ef.elf.e_symtab.(ndx).st_name)
               ", "
               ident_ndxes
            ) ^
            "], Errors: [" ^
            string_of_list
            (function OK(_) -> "" | ERR(s) -> s)
            ", "
            (List.filter (function ERR(_) -> true | _ -> false) results)
                        ^ "]"
        ))
    | [sfw] -> sfw
    | fws ->
        sfw
        >>> sf_ef ^%= add_log (ERROR("Multiple matching data segments!"))
  in
  List.fold_left check_data_aux sfw
    (* Empty lists mean the symbol is external, no need for check *)
    (List.filter (fun (_, gv) -> gv.gvar_init <> []) pv)

(** Checks that everything that has been assimiled as a stub during checks
    indeed looks like a stub.
*)
let check_stubs sfw =
  let check cond msg sfw =
    sfw
    >>> (if cond then id else (sf_ef ^%= add_log (ERROR(msg))))
  in
  let check_eq msg a b = check (a = b) msg in
  let match_bools = check_eq "match_bools" in
  let match_ints = check_eq "match_ints" in
  let check_stub ident vaddr sfw =
    let fundef = List.find (fun (i, _) -> i = ident) sfw.program.prog_defs in
    let elf = sfw.ef.elf in
    let stub_ecode = from_some (code_at_vaddr elf vaddr 2) in
    let stub_offset = from_some (physical_offset_of_vaddr elf vaddr) in
    begin match fundef with
    | (_, Gfun(External(EF_external(dest_ident, _) as ef))) ->
        let args = (ef_sig ef).sig_args in
        if List.mem Tfloat args
        then
          begin match stub_ecode with
          |   CREQV(crbD, crbA, crbB) :: (* vaddr *)
              Bx(li, aa, lk)          :: (* vaddr + 4 *)
              [] ->
              let dest_vaddr = Int32.(add (add vaddr 4l) (mul 4l (exts li))) in
              begin match idmap_unify dest_ident dest_vaddr sfw with
              | ERR(s) ->
                  sfw
                  >>> (sf_ef ^%= add_log (ERROR(
                    "Couldn't match stub, " ^ s
                  )))
              | OK(sfw) ->
                  sfw
                  >>> match_ints 6 crbD
                  >>> match_ints 6 crbA
                  >>> match_ints 6 crbB
                  >>> match_bools false aa
                  >>> match_bools false lk
                  >>> (sf_ef ^%=
                      add_range stub_offset 8l 4
                        (Stub(Hashtbl.find sfw.ident_to_name ident))
                  )
              end
          | _ ->
              sfw
              >>> (sf_ef ^%= add_log (ERROR("Couldn't match stub")))
          end
        else
          begin match stub_ecode with
          |   CRXOR(crbD, crbA, crbB) :: (* vaddr *)
              Bx(li, aa, lk)          :: (* vaddr + 4 *)
              [] ->
              let dest_vaddr = Int32.(add (add vaddr 4l) (mul 4l (exts li))) in
              begin match idmap_unify dest_ident dest_vaddr sfw with
              | ERR(s) ->
                  sfw
                  >>> (sf_ef ^%= add_log (ERROR(
                    "Couldn't match stub, " ^ s
                  )))
              | OK(sfw) ->
                  sfw
                  >>> match_ints 6 crbD
                  >>> match_ints 6 crbA
                  >>> match_ints 6 crbB
                  >>> match_bools false aa
                  >>> match_bools false lk
                  >>> (sf_ef ^%=
                      add_range stub_offset 8l 4
                        (Stub(Hashtbl.find sfw.ident_to_name ident))
                  )
              end
          | _ ->
              sfw
              >>> (sf_ef ^%= add_log (ERROR("Couldn't match stub")))
          end
    | _ -> fatal "Unexpected fundef in check_stubs, please report."
    end
  in
  PosMap.fold check_stub sfw.stub_ident_to_vaddr sfw

(** Read a .sdump file *)

let sdump_magic_number = "CompCertSDUMP" ^ Configuration.version

let read_sdump file =
  let ic = open_in_bin file in
  try
    let magic = String.create (String.length sdump_magic_number) in
    really_input ic magic 0 (String.length sdump_magic_number);
    if magic <> sdump_magic_number then fatal "Bad magic number";
    let prog = (input_value ic: Asm.program) in
    let names = (input_value ic: (ident, string) Hashtbl.t) in
    let atoms = (input_value ic: (ident, C2C.atom_info) Hashtbl.t) in
    close_in ic;
    (prog, names, atoms)
  with
  | End_of_file ->
      close_in ic; Printf.eprintf "Truncated file %s\n" file; exit 2
  | Failure msg ->
      close_in ic; Printf.eprintf "Corrupted file %s: %s\n" file msg; exit 2

(** Split program definitions into functions and variables *)

let split_prog_defs p =
  let rec split fns vars = function
  | [] -> (List.rev fns, List.rev vars)
  | (id, Gfun fd) :: defs -> split ((id, fd) :: fns) vars defs
  | (id, Gvar vd) :: defs -> split fns ((id, vd) :: vars) defs
  in split [] [] p.prog_defs

(** Processes a .sdump file.
*)
let process_sdump efw sdump: e_framework =
  print_debug ("Beginning reading " ^ sdump);
  let (prog, names, atoms) = read_sdump sdump in
  let (prog_funct, prog_vars) = split_prog_defs prog in
  print_debug ("Constructing mapping from idents to symbol indices");
  let ident_to_sym_ndx =
    Hashtbl.fold
      (fun ident name m ->
        match ndxes_of_sym_name efw.elf name with
        | []    -> m (* skip if missing *)
        | ndxes -> PosMap.add ident ndxes m
      )
      names
      PosMap.empty
  in
  print_debug("Constructing worklist");
  let worklist_fundefs =
    List.filter
      (fun f ->
        match snd f with
        | Internal _ -> true
        | External _ -> false
      )
      prog_funct
  in
  let wl =
    List.map
      (fun f ->
        match f with
        | ident, Internal ccode -> (ident, Hashtbl.find names ident, ccode)
        | _,     External _     -> fatal "IMPOSSIBRU!"
      )
      worklist_fundefs
  in
  print_debug("Beginning processing of the worklist");
  efw
  >>> (fun efw ->
    { ef                  = efw
    ; program             = prog
    ; ident_to_name       = names
    ; ident_to_sym_ndx    = ident_to_sym_ndx
    ; stub_ident_to_vaddr = PosMap.empty
    ; atoms               = atoms
    }
  )
  >>> worklist_process wl
  >>> (fun sfw ->
    print_debug "Checking stubs";
    sfw
  )
  >>> check_stubs
  >>> (fun sfw ->
    print_debug "Checking data";
    sfw
  )
  >>> check_data prog_vars
  >>> (fun sfw -> sfw.ef)

(** Returns true if [a, b] intersects [ofs, ofs + size - 1]. *)
let intersect (a, b) ofs size: bool =
  let within (a, b) x = (a <= x) && (x <= b) in
  (within (a, b) ofs) || (within (ofs, Int32.(sub (add ofs size) 1l)) a)

let string_of_range a b = "[0x" ^ Printf.sprintf "%08lx" a ^ " - 0x" ^
  Printf.sprintf "%08lx" b ^ "]"

(** Checks that the bits from [start] to [stop] in [bs] are zeroed. *)
let is_padding bs start stop =
  let bs_start = start * 8 in
  let bs_length = (stop - start + 1) * 8 in
  start <= stop &&
    is_zeros (Bitstring.subbitstring bs bs_start bs_length) bs_length

(** This functions goes through the list of checked bytes, and tries to find
    padding in it. That is, it takes pairs of chunks in order, and adds a
    padding chunk in between if these conditions are met:

    - the second chunk needs to be aligned.

    - the difference between the two chunks is strictly less than the alignment.

    - the data in this space is zeroed.

    Otherwise, it fills holes with an Unknown chunk.
    Returns a framework where [chkd_bytes_list] is sorted and full.
*)
let check_padding efw =
  print_debug "Checking padding";
  let elf = efw.elf in
  let sndxes = list_n elf.e_hdr.e_shnum in
  let matching_sections x y =
    string_of_list
      id
      ", "
      (List.map
         (fun ndx -> elf.e_shdra.(ndx).sh_name)
         (List.filter
            (fun ndx ->
              let shdr = elf.e_shdra.(ndx) in
              intersect (x, y) shdr.sh_offset shdr.sh_size
            )
            sndxes
         )
      )
  in
  let matching_symbols x y =
    string_of_list
      id
      ", "
      (List.map
         (fun sym -> sym.st_name)
         (List.filter
            (fun sym ->
              if sym.st_shndx >= Array.length elf.e_shdra
              then false (* special section *)
              else
                match physical_offset_of_vaddr elf sym.st_value with
                | None -> false
                | Some(ofs) -> intersect (x, y) ofs sym.st_size
            )
            (Array.to_list elf.e_symtab)
         )
      )
  in
  let unknown x y = Unknown(
    "\nSections: " ^ matching_sections x y ^ "\nSymbols: " ^ matching_symbols x y
  )
  in
  (* check_padding_aux assumes a sorted list *)
  let rec check_padding_aux efw accu l =
    match l with
    | [] -> efw
    (* if there is only one chunk left, we add an unknown space between it and
       the end. *)
    | [(_, e, _, _) as h] ->
        let elf_size =
          Safe32.of_int ((Bitstring.bitstring_length efw.elf.e_bitstring) / 8) in
        let elf_end = Int32.sub elf_size 1l in
        if e = elf_end
        then { efw with
          chkd_bytes_list = List.rev (h :: accu);
        }
        else (
          let start = Int32.add e 1l in
          { efw with
            chkd_bytes_list = List.rev
              ((start, elf_end, 0, unknown start elf_end) :: h :: accu);
          }
        )
    | ((b1, e1, a1, n1) as h1) :: ((b2, e2, a2, n2) as h2) :: rest ->
        let pad_start = Int32.add e1 1l in
        let pad_stop = Int32.sub b2 1l in
        if pad_start = b2 (* if they are directly consecutive *)
        || Safe.(of_int32 b2 - of_int32 e1) > a2 (* or if they are too far away *)
        || not (is_padding efw.elf.e_bitstring
                  (Safe32.to_int pad_start) (Safe32.to_int pad_stop))
        then (* not padding *)
          if pad_start <= pad_stop
          then
            check_padding_aux efw
              ((pad_start, pad_stop, 0, unknown pad_start pad_stop) :: h1 :: accu)
              (h2 :: rest)
          else
            check_padding_aux efw (h1 :: accu) (h2 :: rest)
        else ( (* this is padding! *)
          check_padding_aux efw
            ((pad_start, pad_stop, 0, Padding) :: h1 :: accu)
            (h2 :: rest)
        )
  in
  let sorted_chkd_bytes_list =
    List.fast_sort
      (fun (a, _, _, _) (b, _, _, _) -> Int32.compare a b)
      efw.chkd_bytes_list
  in check_padding_aux efw [] sorted_chkd_bytes_list

(** Checks a boolean. *)
let ef_checkb b msg =
  if b then id else add_log(ERROR(msg))

let check_elf_identification efw =
  let ei = efw.elf.e_hdr.e_ident in
  efw
  >>> ef_checkb (ei.ei_class = ELFCLASS32) "ELF class should be ELFCLASS32"
  >>> ef_checkb (ei.ei_data = ELFDATA2MSB || ei.ei_data = ELFDATA2LSB)
    "ELF should be MSB or LSB"
  >>> ef_checkb (ei.ei_version = EV_CURRENT)
    "ELF identification version should be EV_CURRENT"

let check_elf_header efw: e_framework =
  let eh = efw.elf.e_hdr in
  efw
  >>> check_elf_identification
  >>> ef_checkb (eh.e_type = ET_EXEC) "ELF type should be ET_EXEC"
  >>> ef_checkb (eh.e_machine = EM_PPC) "ELF machine should be PPC"
  >>> ef_checkb (eh.e_version = EV_CURRENT) "ELF version should be EV_CURRENT"
  >>> add_range 0l 52l 0 ELF_header (* Header is always 52-bytes long *)

(** Checks the index 0 of the symbol table. This index is reserved to hold
    special values. *)
let check_sym_tab_zero efw =
  let elf = efw.elf in
  let sym0 = efw.elf.e_symtab.(0) in
  (* First, let's mark it checked as a data symbol, to avoid warnings *)
  efw.chkd_data_syms.(0) <- true;
  efw
  >>> (
    if sym0.st_name = ""
    then id
    else add_log (ERROR("Symbol 0 should not have a name"))
  )
  >>> (
    if sym0.st_value = 0l
    then id
    else add_log (ERROR("Symbol 0 should have st_value = 0"))
  )
  >>> (
    if sym0.st_size = 0l
    then id
    else add_log (ERROR("Symbol 0 should have st_size = 0"))
  )
  >>> (
    if sym0.st_bind = STB_LOCAL
    then id
    else add_log (ERROR("Symbol 0 should have STB_LOCAL binding"))
  )
  >>> (
    if sym0.st_type = STT_NOTYPE
    then id
    else add_log (ERROR("Symbol 0 should have STT_NOTYPE type"))
  )
  >>> (
    if sym0.st_other = 0
    then id
    else add_log (ERROR("Symbol 0 should have st_other = 0"))
  )
  >>> (
    if sym0.st_shndx = shn_UNDEF
    then id
    else add_log (ERROR("Symbol 0 should have st_shndx = SHN_UNDEF"))
  )
  >>> add_range elf.e_shdra.(elf.e_symtab_sndx).sh_offset 16l 4 Zero_symbol

(** If CompCert sections have been mapped to an ELF section whose name is
    not the same, we warn the user.
*)
let warn_sections_remapping efw =
  print_debug "Checking remapped sections";
  StringMap.fold
    (fun c_name (e_name, conflicts) efw ->
      if StringSet.is_empty conflicts
      then
        match e_name with
        | Provided(e_name) ->
            efw
        | Inferred(e_name) ->
            if c_name = e_name
            then efw
            else
              begin
                efw
                >>> add_log (WARNING(
                  Printf.sprintf
                    "Detected linker script remapping: section %S -> %S"
                    c_name e_name
                ))
              end
      else (* conflicts not empty *)
        match e_name with
        | Provided(e_name) ->
            efw
            >>> add_log (ERROR(
              Printf.sprintf "
    Conflicting remappings for section %s:
      Specified: %s
      Expected:  %s"
                c_name e_name (string_of_list id ", " (StringSet.elements conflicts))
            ))
        | Inferred(e_name) ->
            efw
            >>> add_log (ERROR(
              Printf.sprintf "
    Conflicting remappings for section %s:
      %s"
                c_name (string_of_list id ", " (e_name :: (StringSet.elements conflicts)))
            ))
    )
    efw.section_map
    efw

let warn_sda_mapping efw =
  print_debug "Checking SDA mappings";
  if IntMap.is_empty efw.sda_map
  then efw
  else (
    IntMap.fold
      (fun r vaddr efw ->
        match vaddr with
        | Provided(_) -> efw
        | Inferred(vaddr) ->
            efw >>> add_log (WARNING(
              Printf.sprintf
                "This SDA register mapping was inferred: register r%u = 0x%lX"
                r vaddr
            ))
      )
      efw.sda_map
      efw
  )

let (>>=) li f = List.flatten (List.map f li)

(** Returns the list of all strictly-ordered pairs of [[0; len - 1]] that don't
    satisfy f. *)
let forall_sym (len: int) (f: 'a -> 'a -> bool): ('a * 'a) list =
  (list_n len)                >>= fun x ->
  (list_ab (x + 1) (len - 1)) >>= fun y ->
  (if f x y then [] else [(x, y)])

let check_overlaps efw =
  let shdra = efw.elf.e_shdra in
  let intersect a asize b bsize =
    asize <> 0l && bsize <> 0l &&
      (
        let last x xsize = Int32.(sub (add x xsize) 1l) in
        let alast = last a asize in
        let blast = last b bsize in
        let within (a, b) x = (a <= x) && (x <= b) in
        (within (a, alast) b) || (within (b, blast) a)
      )
  in
  match
    forall_sym (Array.length shdra)
      (fun i j ->
        let ai = shdra.(i) in
        let aj = shdra.(j) in
        (ai.sh_type = SHT_NOBITS)
        || (aj.sh_type = SHT_NOBITS)
        || (not (intersect ai.sh_offset ai.sh_size aj.sh_offset aj.sh_size))
      )
  with
  | [] -> efw
  | l  ->
      List.fold_left
        (fun efw (i, j) ->
          let msg =
            Printf.sprintf "Sections %s and %s overlap" shdra.(i).sh_name shdra.(j).sh_name
          in
          add_log (ERROR(msg)) efw
        )
        efw l

let check_unknown_chunks efw =
  if
    List.exists
      (function (_, _, _, Unknown(_)) -> true | _ -> false)
      efw.chkd_bytes_list
  then add_log (WARNING(
    "Some parts of the ELF file are unknown." ^
      (if !print_elfmap then "" else " Use -print-elfmap to see what was covered.")
  )) efw
  else efw

let check_missed_symbols efw =
  if not !exhaustivity
  then efw
  else
    let chkd_syms_a =
      Array.init
        (Array.length efw.elf.e_symtab)
        (
          fun ndx ->
            match efw.elf.e_symtab.(ndx).st_type with
            (* we only care about function and data symbols *)
            | STT_SECTION | STT_FILE -> true
            | STT_OBJECT | STT_FUNC | STT_NOTYPE | STT_UNKNOWN ->
                (* checked as either a function or a data symbol *)
                efw.chkd_fun_syms.(ndx)
                || efw.chkd_data_syms.(ndx)
                (* or part of the symbols we know are mising *)
                || StringSet.mem efw.elf.e_symtab.(ndx).st_name efw.missing_syms
        )
    in
    let missed_syms_l = list_false_indices chkd_syms_a in
    match missed_syms_l with
    | [] -> efw
    | _  ->
        let symtab = efw.elf.e_symtab in
        let symlist_names = string_of_list (fun ndx -> symtab.(ndx).st_name) " " in
        let missed_funs =
          List.filter (fun ndx -> symtab.(ndx).st_type = STT_FUNC) missed_syms_l in
        let missed_data =
          List.filter (fun ndx -> symtab.(ndx).st_type = STT_OBJECT) missed_syms_l in
        let missed_unknown =
          List.filter (fun ndx ->
            match symtab.(ndx).st_type with
            | STT_NOTYPE | STT_UNKNOWN -> true
            | _ -> false
          ) missed_syms_l in
        if !list_missing
        then
          efw
           >>> add_log (WARNING(
             Printf.sprintf
               "
    The following function symbol(s) do not appear in .sdump files:
      %s
    The following data symbols do not appear in .sdump files:
      %s
    The following unknown type symbols do not appear in .sdump files:
      %s"
               (symlist_names missed_funs)
               (symlist_names missed_data)
               (symlist_names missed_unknown)
           ))
        else
          efw
           >>> add_log (WARNING(
             Printf.sprintf
               "%u function symbol(s), %u data symbol(s) and %u unknown type symbol(s) do not appear in .sdump files. Add -list-missing to list them."
               (List.length missed_funs)
               (List.length missed_data)
               (List.length missed_unknown)
           ))

let print_diagnosis efw =
  let (nb_err, nb_warn) = List.fold_left
    (fun (e, w) -> function
    | DEBUG(_)   -> (e, w)
    | ERROR(_)   -> (e + 1, w)
    | INFO(_)    -> (e, w)
    | WARNING(_) -> (e, w + 1)
    )
    (0, 0)
    efw.log
  in
  if !debug
  then Printf.printf "\n\nFINAL LOG:\n\n";
  List.(iter
          (fun e ->
            match string_of_log_entry false e with
            | "" -> ()
            | s -> print_endline s
          )
          (rev efw.log)
  );
  let plural n = if n > 1 then "s" else "" in
  Printf.printf " SUMMARY: %d error%s, %d warning%s\n"
    nb_err (plural nb_err) nb_warn (plural nb_warn);
  efw

let conf_file = ref (None: string option)

let parse_conf filename =
  let section_map = ref StringMap.empty in
  let sda_map = ref IntMap.empty in
  let missing_syms = ref StringSet.empty in
  let ic = open_in filename in
  try
    while true
    do
      let line = input_line ic in
      (* Test different patterns one by one, until one of them works *)
      let rec match_line = function
      | [] -> failwith (Printf.sprintf "Couldn't read configuration line: %s" line)
      | try_match::rest ->
          try try_match ()
          with Scanf.Scan_failure(_) -> match_line rest
      in
      (* an empty line is ignored *)
      if line <> ""
      then
        match_line
          (* a comment *)
          [ (fun () ->
            Scanf.sscanf line
              "#%s"
              (fun _ -> ())
            )
          (* a section remapping *)
          ; (fun () ->
            Scanf.sscanf line
              "section %S -> %S"
              (fun sfrom sto ->
                if StringMap.mem sfrom !section_map
                then failwith (
                  Printf.sprintf
                    "Your configuration file contains multiple mappings for section %s"
                    sfrom
                )
                else
                  section_map :=
                    StringMap.add sfrom (Provided(sto), StringSet.empty) !section_map
              )
          )
          (* a SDA mapping *)
          ; (fun () ->
            Scanf.sscanf line
              "register r%u = %li"
              (fun r addr ->
                if IntMap.mem r !sda_map
                then failwith (
                  Printf.sprintf
                    "Your configuration file contains multiple SDA mappings for register %u"
                    r
                )
                else
                  sda_map := IntMap.add r (Provided(addr)) !sda_map)
          )
          (* a list of symbols supposed to be missing from the .sdump files *)
          ; (fun () ->
            Scanf.sscanf line
              "external %s@\n"
              (fun sym_list_s ->
                let sym_list = Str.split (Str.regexp "[ \t]+") sym_list_s in
                List.iter
                  (fun sym -> missing_syms := StringSet.add sym !missing_syms)
                  sym_list
              )
          )
          ]
    done; raise End_of_file (* unreachable, just to please the typer *)
  with
  | End_of_file -> (!section_map, !sda_map, !missing_syms)

(** Checks a whole ELF file according to a list of .sdump files. This never
    dumps anything, so it can be safely used when fuzz-testing even if the
    user accidentally enabled dumping options. *)
let check_elf_nodump elf sdumps =
  let eh = elf.e_hdr in
  let nb_syms = Array.length elf.e_symtab in
  let section_strtab = elf.e_shdra.(eh.e_shstrndx) in
  let symtab_shdr = elf.e_shdra.(elf.e_symtab_sndx) in
  let symbol_strtab = elf.e_shdra.(Safe32.to_int symtab_shdr.sh_link) in
  let (section_map, sda_map, missing_syms) =
    match !conf_file with
    | None -> (StringMap.empty, IntMap.empty, StringSet.empty)
    | Some(filename) -> parse_conf filename
  in
  let efw =
    { elf             = elf
    ; log             = []
    ; chkd_bytes_list = []
    ; chkd_fun_syms   = Array.make nb_syms false
    ; chkd_data_syms  = Array.make nb_syms false
    ; section_map     = section_map
    ; sda_map         = sda_map
    ; missing_syms    = missing_syms
    }
    >>> check_elf_header
    >>> add_range
      eh.e_phoff
      Safe.(to_int32 (eh.e_phnum * eh.e_phentsize))
      4
      ELF_progtab
    >>> add_range
      eh.e_shoff
      Safe.(to_int32 (eh.e_shnum * eh.e_shentsize))
      4
      ELF_shtab
    >>> add_range
      section_strtab.sh_offset
      section_strtab.sh_size
      0
      ELF_section_strtab
    >>> add_range
      symbol_strtab.sh_offset
      symbol_strtab.sh_size
      0
      ELF_symbol_strtab
    >>> check_sym_tab_zero
  in
  print_debug "Done checking header, beginning processing of .sdumps";
  (* Thread the framework through the processing of all .sdump files *)
  List.fold_left process_sdump efw sdumps
  (* check the padding in between identified byte chunks *)
  >>> check_padding
  (* warn if some CompCert sections have been remapped by the linker script *)
  >>> warn_sections_remapping
  (* warn if there exists non-empty overlapping sections *)
  >>> check_overlaps
  (* warn about inferred SDA registers *)
  >>> warn_sda_mapping
  (* warn about regions of the ELF file that could not be identified *)
  >>> check_unknown_chunks
  >>> check_missed_symbols
  >>> print_diagnosis

(** Checks a whole ELF file according to .sdump files.
    If requested, dump the calculated bytes mapping, so that it can be
    reused by the fuzzer. *)
let check_elf_dump elffilename sdumps =
  print_debug "Beginning ELF parsing";
  let elf = read_elf elffilename in
  print_debug "Beginning ELF checking";
  let efw = check_elf_nodump elf sdumps in
  (* print the elfmap if requested *)
  if !print_elfmap
  then
    begin
      Printf.printf "\n\n%s\n\n\n"
        (string_of_list
           (fun (a, b, align, r) -> string_of_range a b ^ " (" ^
             string_of_int align ^ ") " ^ string_of_byte_chunk_desc r)
           "\n"
           efw.chkd_bytes_list
        )
    end;
  (* dump the elfmap if requested *)
  if !dump_elfmap
  then
    begin
      let oc = open_out (elffilename ^ ".elfmap") in
      output_value oc efw.chkd_bytes_list;
      close_out oc
    end
