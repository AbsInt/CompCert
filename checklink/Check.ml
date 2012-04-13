open Asm
open Asm_printers
open AST
open BinInt
open BinPos
open Bitstring_utils
open C2C
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

(** Whether to print the ELF map *)
let print_elfmap = ref false

(** Whether to dump the ELF map *)
let dump_elfmap = ref false

(** Whether to check that all ELF function/data symbols have been matched
    against CompCert idents *)
let exhaustivity = ref true

(** CompCert Asm *)
type ccode = Asm.instruction list

(** Adds a log entry into the framework. *)
let add_log (entry: log_entry) (efw: e_framework): e_framework =
  if !debug then print_endline (string_of_log_entry true entry);
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

(** Taken from CompCert *)
let name_of_section_Linux:
    section_name -> string
  = function
  | Section_text -> ".text"
  | Section_data i -> if i then ".data" else ".bss"
  | Section_small_data i -> if i then ".sdata" else ".sbss"
  | Section_const -> ".rodata"
  | Section_small_const -> ".sdata2"
  | Section_string -> ".rodata"
  | Section_literal -> ".rodata" (* should have been .rodata.cst8, but ld script
                                    merges it with .rodata *)
  | Section_jumptable -> ".text"
  | Section_user(s, wr, ex) -> s

(** Taken from CompCert *)
let name_of_section_Diab:
    section_name -> string
  = function
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
let name_of_section:
    section_name -> string
  =
  begin match Configuration.system with
  | "macosx" -> assert false
  | "linux"  -> name_of_section_Linux
  | "diab"   -> name_of_section_Diab
  | _        -> assert false
  end

(** Compares a CompCert section name with an ELF section name. *)
let match_sections_name
    (c_section: section_name) (e_name: string) (sfw: s_framework):
    s_framework
    =
  let c_name = name_of_section c_section in
  try
    let expected = StringMap.find c_name sfw.ef.section_map in
    if e_name = expected
    then sfw
    else (
      sfw
      >>> sf_ef ^%=
        add_log (ERROR(
          Printf.sprintf
            "CompCert section %s was mapped to both %s and %s"
            c_name expected e_name
        ))
    )
  with Not_found -> (
    sfw
    >>> (sf_ef |-- section_map) ^%= StringMap.add c_name e_name
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
let idmap_unify
    (k: positive) (vaddr: int32) (sfw: s_framework): s_framework or_err =
  try (
    let id_ndxes = PosMap.find k sfw.ident_to_sym_ndx in
    match List.filter
      (fun ndx -> sfw.ef.elf.e_symtab.(ndx).st_value = vaddr)
      id_ndxes with
      | [] ->
          if Str.string_match
            re_variadic_stub (Hashtbl.find sfw.ident_to_name k) 0
          then (* this points to a stub *)
            try (
              let v = PosMap.find k sfw.stub_ident_to_vaddr in
              if vaddr = v
              then OK(sfw)
              else ERR(
                "Incoherent constraints for stub: " ^
                  Hashtbl.find sfw.ident_to_name k
              )
            )
            with Not_found ->
              OK(
                sfw
                >>> (stub_ident_to_vaddr ^%= PosMap.add k vaddr)
              )
          else (* not a stub, so this is a real error *)
            ERR(
              "Incoherent constraints for ident " ^
                Hashtbl.find sfw.ident_to_name k ^
                " with value " ^
                string_of_int32 vaddr ^
                " and candidates [" ^
                (string_of_list
                   (fun ndx ->
                     string_of_int32
                       sfw.ef.elf.e_symtab.(ndx).st_value
                   )
                   ", " id_ndxes
                ) ^
                "]"
            )
      | ndxes ->
          if id_ndxes = ndxes
          then OK(sfw)
          else OK((ident_to_sym_ndx ^%= (PosMap.add k ndxes)) sfw)
  )
  with
  | Not_found ->
      ERR(
        "Missing ident: " ^ Hashtbl.find sfw.ident_to_name k ^
          " should be at vaddr: " ^ string_of_int32 vaddr
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

(** Generic condition checker *)
let check (cond: bool) (msg: string) (ffw: f_framework): f_framework =
  if cond
  then ffw
  else ffw >>> ff_ef ^%= add_log (ERROR(msg))

let check_eq (msg: string) (a: 'a) (b: 'a): f_framework -> f_framework =
  check (a = b) msg

let match_bools:  bool  -> bool  -> f_framework -> f_framework =
  check_eq "match_bools"
let match_ints:   int   -> int   -> f_framework -> f_framework =
  check_eq "match_ints"
let match_int32s: int32 -> int32 -> f_framework -> f_framework =
  check_eq "match_int32s"
let match_floats: float -> float -> f_framework -> f_framework =
  check_eq "match_floats"
let match_crbits cb eb = check_eq "match_crbits" cb (crbit_arr.(eb))
let match_iregs  cr er = check_eq "match_iregs" cr (ireg_arr.(er))
let match_fregs  cr er = check_eq "match_fregs" cr (freg_arr.(er))

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
let match_csts (cc: constant) (ec: int32) (ffw: f_framework): f_framework =
  let sfw = ffw |. ff_sf in
  let efw = ffw |. ff_ef in
  match cc with
  | Cint (i) ->
      check_eq "match_csts Cint" ec (z_int32_lax i) ffw
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
          (ff_ef ^%=
              (add_log (ERROR("Csymbol_low " ^ string_of_list id ", " sym_names)))
          ) ffw
      | _  ->
          if candidates = vaddrs
          then ffw
          else (
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
          let sym_names =
            List.map (name_of_ndx efw) candidates in
          (ff_ef ^%=
              (add_log (ERROR("Csymbol_high " ^ string_of_list id ", " sym_names)))
          ) ffw
      | _  ->
          if candidates = vaddrs
          then ffw
          else ((ff_sf |-- ident_to_sym_ndx) ^%= (PosMap.add ident vaddrs)) ffw
      end
  | Csymbol_sda (ident, i) ->
      ffw
      >>> ff_ef ^%= (add_log (ERROR("TODO")))

let match_z_int32 (cz: coq_Z) (ei: int32) =
  check_eq "match_z_int32" (z_int32 cz) ei

let match_z_int (cz: coq_Z) (ei: int) =
  check_eq "match_z_int" (z_int32 cz) (Safe32.of_int ei)

(* [m] is interpreted as a bitmask, and checked against [ei]. *)
let match_mask (m: coq_Z) (ei: int32) =
  check_eq
    ("match_mask " ^ string_of_int32 (z_int32_lax m) ^ " and " ^
        string_of_int32 ei)
    (z_int32_lax m) ei

(** Checks that the special register referred to in [spr] is [r]. *)
let match_spr (str: string) (r: int) (spr: bitstring)
    : f_framework -> f_framework =
  bitmatch spr with
  | { v:5; 0:5 } when v = r -> id
  | { _ }                   -> ff_ef ^%= (add_log (ERROR(str)))

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
          print_endline "Ill-formed jump table";
          ERR("Ill-formed jump table")
    )
  in
  let elf = ffw.sf.ef.elf in
  let cur_sym_ndx = elf.e_symtab.(ffw.this_sym_ndx).st_shndx in
  begin match bitstring_at_vaddr elf cur_sym_ndx vaddr size with
  | None -> ERR("Symbol out of its parent section")
  | Some(bs) ->
      begin match section_at_vaddr elf vaddr with
      | None -> ERR("Jumptable's virtual address is out of any section")
      | Some(sndx) ->
          let ofs = physical_offset_of_vaddr elf sndx vaddr in
          ffw
          >>> (ff_sf ^%=
              match_sections_name jmptbl_section elf.e_shdra.(sndx).sh_name
          )
          >>> match_jmptbl_aux lbllist bs
          >>? (ff_ef ^%=
              add_range ofs (Safe32.of_int (size / 8)) 0 Jumptable)
      end
  end

(** Matches [ecode] agains the expected code for a small memory copy
    pseudo-instruction. Returns a triple containing the updated framework,
    the remaining ELF code, and the updated program counter.
*)
let match_memcpy_small ecode pc sz al src dst (fw: f_framework)
    : (f_framework * ecode * int32) option =
  let rec match_memcpy_small_aux ofs sz ecode pc (fw: f_framework) =
    let ofs32 = Safe32.of_int ofs in
    if sz >= 8 && al >= 4
    then (
      match ecode with
      |   LFD (frD0, rA0, d0) ::
          STFD(frS1, rA1, d1) :: es ->
          fw
          >>> match_fregs  FPR0  frD0
          >>> match_iregs  src   rA0
          >>> match_int32s ofs32 (exts d0)
          >>> match_fregs  FPR0  frS1
          >>> match_iregs  dst   rA1
          >>> match_int32s ofs32 (exts d1)
          >>> match_memcpy_small_aux (ofs + 8) (sz - 8) es (Int32.add 8l pc)
      | _ -> None
    )
    else if sz >= 4
    then (
      match ecode with
      |   LWZ(rD0, rA0, d0) ::
          STW(rS1, rA1, d1) :: es ->
          fw
          >>> match_iregs  GPR0  rD0
          >>> match_iregs  src   rA0
          >>> match_int32s ofs32 (exts d0)
          >>> match_iregs  GPR0  rS1
          >>> match_iregs  dst   rA1
          >>> match_int32s ofs32 (exts d0)
          >>> match_memcpy_small_aux (ofs + 4) (sz - 4) es (Int32.add 8l pc)
      | _ -> None
    )
    else if sz >= 2
    then (
      match ecode with
      |   LHZ(rD0, rA0, d0) ::
          STH(rS1, rA1, d1) :: es ->
          fw
          >>> match_iregs  GPR0  rD0
          >>> match_iregs  src   rA0
          >>> match_int32s ofs32 (exts d0)
          >>> match_iregs  GPR0  rS1
          >>> match_iregs  dst   rA1
          >>> match_int32s ofs32 (exts d0)
          >>> match_memcpy_small_aux (ofs + 2) (sz - 2) es (Int32.add 8l pc)
      | _ -> None
    )
    else if sz >= 1
    then (
      match ecode with
      |   LBZ(rD0, rA0, d0) ::
          STB(rS1, rA1, d1) :: es ->
          fw
          >>> match_iregs  GPR0  rD0
          >>> match_iregs  src   rA0
          >>> match_int32s ofs32 (exts d0)
          >>> match_iregs  GPR0  rS1
          >>> match_iregs  dst   rA1
          >>> match_int32s ofs32 (exts d0)
          >>> match_memcpy_small_aux (ofs + 1) (sz - 1) es (Int32.add 8l pc)
      | _ -> None
    )
    else Some(fw, ecode, pc)
  in match_memcpy_small_aux 0 sz ecode pc fw

(** Matches [ecode] agains the expected code for a big memory copy
    pseudo-instruction. Returns a triple containing the updated framework,
    the remaining ELF code, and the updated program counter.
*)
let match_memcpy_big ecode pc sz al src dst fw
    : (f_framework * ecode * int32) option =
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
      fw
      >>> match_iregs  GPR0  rD0
      >>> match_iregs  GPR0  rA0
      >>> match_int32s sz'   (exts simm0)
      >>> match_iregs  GPR0  rS1
      >>> match_ctr    spr1
      >>> match_iregs  s     rD2
      >>> match_iregs  src   rA2
      >>> match_int32s (-4l) (exts simm2)
      >>> match_iregs  d     rD3
      >>> match_iregs  dst   rA3
      >>> match_int32s (-4l) (exts simm3)
      >>> match_iregs  GPR0  rD4
      >>> match_iregs  s     rA4
      >>> match_int32s 4l    (exts d4)
      >>> match_iregs  GPR0  rS5
      >>> match_iregs  d     rA5
      >>> match_int32s 4l    (exts d5)
      >>> (
        bitmatch bo6 with
        | { 16:5:int } -> id
        | { _ } ->
            ff_ef ^%= add_log (ERROR("bitmatch bo"))
      )
      >>> match_ints   bi6   0
      >>> match_int32s dest_vaddr target_vaddr
      >>> match_bools  false aa6
      >>> match_bools  false lk6
      >>> (fun fw ->
        match sz land 3 with
        | 1 ->
            begin match es with
            |   LBZ(rD0, rA0, d0) ::
                STB(rS1, rA1, d1) :: es ->
                fw
                >>> match_iregs  GPR0 rD0
                >>> match_iregs  s    rA0
                >>> match_int32s 4l   (exts d0)
                >>> match_iregs  GPR0 rS1
                >>> match_iregs  d    rA1
                >>> match_int32s 4l   (exts d1)
                >>> (fun fw -> Some(fw, es, Int32.add 36l pc))
            | _ -> None
            end
        | 2 ->
            begin match es with
            |   LHZ(rD0, rA0, d0) ::
                STH(rS1, rA1, d1) :: es ->
                fw
                >>> match_iregs  GPR0 rD0
                >>> match_iregs  s    rA0
                >>> match_int32s 4l   (exts d0)
                >>> match_iregs  GPR0 rS1
                >>> match_iregs  d    rA1
                >>> match_int32s 4l   (exts d1)
                >>> (fun fw -> Some(fw, es , Int32.add 36l pc))
            | _ -> None
            end
        | 3 ->
            begin match es with
            |   LHZ(rD0, rA0, d0) ::
                STH(rS1, rA1, d1) ::
                LBZ(rD2, rA2, d2) ::
                STB(rS3, rA3, d3) :: es ->
                fw
                >>> match_iregs  GPR0 rD0
                >>> match_iregs  s    rA0
                >>> match_int32s 4l   (exts d0)
                >>> match_iregs  GPR0 rS1
                >>> match_iregs  d    rA1
                >>> match_int32s 4l   (exts d1)
                >>> match_iregs  GPR0 rD2
                >>> match_iregs  s    rA2
                >>> match_int32s 6l   (exts d2)
                >>> match_iregs  GPR0 rS3
                >>> match_iregs  d    rA3
                >>> match_int32s 6l   (exts d3)
                >>> (fun fw -> Some(fw, es, Int32.add 44l pc))
            | _ -> None
            end
        | _ -> Some(fw, es, Int32.add 28l pc)
      )
  | _ -> None

let match_bo_bt_bool bo =
  bitmatch bo with
  | { false:1; true:1; true:1; false:1; false:1 } -> true
  | { _ } -> false

let match_bo_bf_bool bo =
  bitmatch bo with
  | { false:1; false:1; true:1; false:1; false:1 } -> true
  | { _ } -> false

let match_bo_bt bo ffw =
  ffw >>> (ff_ef ^%=
      bitmatch bo with
      | { false:1; true:1; true:1; false:1; false:1 } -> id
      | { _ } -> add_log (ERROR("match_bo_bt"))
  )

let match_bo_bf bo ffw =
  ffw >>> (ff_ef ^%=
      if match_bo_bf_bool bo
      then id
      else add_log (ERROR("match_bo_bf"))
  )

let match_bo_ctr bo ffw =
  ffw
  >>> (ff_ef ^%=
      bitmatch bo with
      | { true:1; false:1; true:1; false:1; false:1 } -> id
      | { _ } -> add_log (ERROR("bitmatch"))
  )

(** Compares a whole CompCert function code against an ELF code, starting at
    program counter [pc].
*)
let rec compare_code ccode ecode pc fw: f_framework or_err =
  let error = ERR("Non-matching instructions") in
  match ccode, ecode with
  | [], []        -> OK(fw)
  | [], _ | _, [] -> ERR("Codes have different lengths")
  | c::cs, e::es  ->
      let recur_simpl = compare_code cs es (Int32.add 4l pc) in
      let fw =
        if !debug
        then (
          let curr_instr = "  [" ^ string_of_int32 pc ^ "] " ^
            string_of_instruction c ^ " - " ^ string_of_instr e in
          (ff_ef ^%= add_log (DEBUG(curr_instr))) fw
        )
        else fw
      in
      match c with
      | Padd(rd, r1, r2) ->
          begin match ecode with
          | ADDx(rD, rA, rB, oe, rc) :: es ->
              fw
              >>> match_iregs rd    rD
              >>> match_iregs r1    rA
              >>> match_iregs r2    rB
              >>> match_bools false oe
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Padde(rd, r1, r2) ->
          begin match ecode with
          | ADDEx(rD, rA, rB, oe, rc) :: es ->
              fw
              >>> match_iregs rd    rD
              >>> match_iregs r1    rA
              >>> match_iregs r2    rB
              >>> match_bools false oe
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Paddi(rd, r1, cst) ->
          begin match ecode with
          | ADDI(rD, rA, simm) :: es ->
              fw
              >>> match_iregs rd  rD
              >>> match_iregs r1  rA
              >>> match_csts  cst (exts simm)
              >>> recur_simpl
          | _ -> error
          end
      | Paddic(rd, r1, cst) ->
          begin match ecode with
          | ADDIC(rD, rA, simm) :: es ->
              fw
              >>> match_iregs rd  rD
              >>> match_iregs r1  rA
              >>> match_csts  cst (exts simm)
              >>> recur_simpl
          | _ -> error
          end
      | Paddis(rd, r1, cst) ->
          begin match ecode with
          | ADDIS(rD, rA, simm) :: es ->
              fw
              >>> match_iregs rd  rD
              >>> match_iregs r1  rA
              >>> match_csts  cst (Safe32.of_int simm)
              >>> recur_simpl
          | _ -> error
          end
      | Paddze(rd, r1) ->
          begin match ecode with
          | ADDZEx(rD, rA, oe, rc) :: es ->
              fw
              >>> match_iregs rd    rD
              >>> match_iregs r1    rA
              >>> match_bools false oe
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pallocframe(sz, ofs) ->
          begin match ecode with
          | STWU(rS, rA, d) :: es ->
              fw
              >>> match_iregs   GPR1 rS
              >>> match_iregs   GPR1 rA
              >>> match_z_int32 sz   (Int32.neg (exts d))
              >>> match_z_int32 ofs  0l
              >>> recur_simpl
          |   ADDIS   (rD0, rA0, simm0)  ::
              ORI     (rS1, rA1, uimm1)  ::
              STWUX   (rS2, rA2, rB2)    :: es ->
              let sz32 = Int32.neg (z_int32 sz) in
              let sz_hi = Int32.shift_right_logical sz32 16 in
              let sz_lo = Int32.logand sz32 0xFFFFl in
              fw
              >>> match_iregs  GPR12 rD0
              >>> match_iregs  GPR0  rA0
              >>> match_int32s sz_hi (Safe32.of_int simm0)
              >>> match_iregs  GPR12 rS1
              >>> match_iregs  GPR12 rA1
              >>> match_int32s sz_lo (Safe32.of_int uimm1)
              >>> match_iregs  GPR1  rS2
              >>> match_iregs  GPR1  rA2
              >>> match_iregs  GPR12 rB2
              >>> compare_code cs es (Int32.add 12l pc)
          | _ -> error
          end
      | Pandc(rd, r1, r2) ->
          begin match ecode with
          | ANDCx(rS, rA, rB, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_iregs r2    rB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pand_(rd, r1, r2) ->
          begin match ecode with
          | ANDx(rS, rA, rB, rc) :: es ->
              fw
              >>> match_iregs rd   rA
              >>> match_iregs r1   rS
              >>> match_iregs r2   rB
              >>> match_bools true rc
              >>> recur_simpl
          | _ -> error
          end
      | Pandis_(rd, r1, cst) ->
          begin match ecode with
          | ANDIS_(rS, rA, uimm) :: es ->
              fw
              >>> match_iregs rd  rA
              >>> match_iregs r1  rS
              >>> match_csts  cst (Safe32.of_int uimm)
              >>> recur_simpl
          | _ -> error
          end
      | Pandi_(rd, r1, cst) ->
          begin match ecode with
          | ANDI_(rS, rA, uimm) :: es ->
              fw
              >>> match_iregs rd  rA
              >>> match_iregs r1  rS
              >>> match_csts  cst (Safe32.of_int uimm)
              >>> recur_simpl
          | _ -> error
          end
      | Pannot(ef, args) ->
          fw
          >>> compare_code cs ecode pc
      | Pb(lbl) ->
          begin match ecode with
          | Bx(li, aa, lk) :: es ->
              let lblvaddr = Int32.(add pc (mul 4l (exts li))) in
              fw
              >>> lblmap_unify lbl   lblvaddr
              >>? match_bools  false aa
              >>? match_bools  false lk
              >>= recur_simpl
          | _ -> error
          end
      | Pbctr ->
          begin match ecode with
          | BCCTRx(bo, bi, lk) :: es ->
              fw
              >>> match_bo_ctr bo
              >>> match_ints  0     bi
              >>> match_bools false lk
              >>> recur_simpl
          | _ -> error
          end
      | Pbctrl ->
          begin match ecode with
          | BCCTRx(bo, bi, lk) :: es ->
              fw
              >>> match_bo_ctr bo
              >>> match_ints  0    bi
              >>> match_bools true lk
              >>> recur_simpl
          | _ -> error
          end
      | Pbf(bit, lbl) ->
          begin match ecode with
          | BCx(bo, bi, bd, aa, lk) :: es when match_bo_bf_bool bo ->
              let lblvaddr = Int32.(add pc (mul 4l (exts bd))) in
              fw
              (* >>> match_bo_bf  bo   already done in pattern match *)
              >>> match_crbits bit   bi
              >>> lblmap_unify lbl   lblvaddr
              >>? match_bools  false aa
              >>? match_bools  false lk
              >>= recur_simpl
          |   BCx(bo0, bi0, bd0, aa0, lk0) ::
              Bx (li1, aa1, lk1)           :: es ->
              let cnext = Int32.add pc 8l in
              let enext = Int32.(add pc (mul 4l (exts bd0))) in
              let lblvaddr = Int32.(add pc (mul 4l (exts bd0))) in
              fw
              >>> match_bo_bt  bo0
              >>> match_crbits bit bi0
              >>> match_int32s cnext enext
              >>> match_bools  false aa0
              >>> match_bools  false lk0
              >>> lblmap_unify lbl   lblvaddr
              >>? match_bools  false aa1
              >>? match_bools  false lk1
              >>= compare_code cs es (Int32.add 8l pc)
          | _ -> error
          end
      | Pbl(ident) ->
          begin match ecode with
          | Bx(li, aa, lk) :: es ->
              let dest = Int32.(add pc (mul 4l (exts li))) in
              fw
              >>> (ff_sf ^%=? idmap_unify ident dest)
              >>? match_bools false aa
              >>? match_bools true  lk
              >>= recur_simpl
          | _ -> error
          end
      | Pblr ->
          begin match ecode with
          | BCLRx(bo, bi, lk) :: es ->
              fw
              >>> match_bo_ctr bo
              >>> match_ints  0     bi
              >>> match_bools false lk
              >>> recur_simpl
          | _ -> error
          end
      | Pbs(ident) ->
          begin match ecode with
          | Bx(li, aa, lk) :: es ->
              let dest = Int32.(add pc (mul 4l (exts li))) in
              fw
              >>> match_bools false aa
              >>> match_bools false lk
              >>> (ff_sf ^%=? idmap_unify ident dest)
              >>= recur_simpl
          | _ -> error
          end
      | Pbt(bit, lbl) ->
          begin match ecode with
          | BCx(bo, bi, bd, aa, lk) :: es when match_bo_bt_bool bo ->
              let lblvaddr = Int32.(add pc (mul 4l (exts bd))) in
              fw
              (* >>> match_bo_bt  bo   already done in pattern match *)
              >>> match_crbits bit   bi
              >>> lblmap_unify lbl   lblvaddr
              >>? match_bools  false aa
              >>? match_bools  false lk
              >>= recur_simpl
          |   BCx(bo0, bi0, bd0, aa0, lk0) ::
              Bx (li1, aa1, lk1)           :: es ->
              let cnext = Int32.add pc 8l in
              let enext = Int32.(add pc (mul 4l (exts bd0))) in
              let lblvaddr = Int32.(add pc (mul 4l (exts bd0))) in
              fw
              >>> match_bo_bf  bo0
              >>> match_crbits bit bi0
              >>> match_int32s cnext enext
              >>> match_bools  false aa0
              >>> match_bools  false lk0
              >>> lblmap_unify lbl   lblvaddr
              >>? match_bools  false aa1
              >>? match_bools  false lk1
              >>= compare_code cs es (Int32.add 8l pc)
          | _ -> error
          end
      | Pbtbl(reg, table) ->
          begin match ecode with
          |   ADDIS (rD0, rA0, simm0) ::
              LWZ   (rD1, rA1, d1)    ::
              MTSPR (rS2, spr2)       ::
              BCCTRx(bo3, bi3, rc3)   :: es ->
              let tblvaddr = Int32.(
                add (shift_left (Safe32.of_int simm0) 16) (exts d1)
              ) in
              let tblsize = (32 * List.length table) in
              fw
              >>> match_iregs  GPR12 rD0
              >>> match_iregs  reg   rA0
              >>> match_iregs  GPR12 rD1
              >>> match_iregs  GPR12 rA1
              >>> match_iregs  GPR12 rS2
              >>> match_ctr    spr2
              >>> match_bo_ctr bo3
              >>> match_ints   0     bi3
              >>> match_bools  false rc3
              >>> match_jmptbl table tblvaddr tblsize
              >>= compare_code cs es (Int32.add 16l pc)
          | _ -> error
          end
      | Pbuiltin(ef, args, res) ->
          begin match ef with
          | EF_builtin(name, sg) ->
              begin match Hashtbl.find
                  (fw |. ff_sf).ident_to_name name, args, res with
                  | "__builtin_mulhw", [IR a1; IR a2], IR res ->
                      begin match ecode with
                      | MULHWx(rD, rA, rB, rc) :: es ->
                          fw
                          >>> match_iregs res   rD
                          >>> match_iregs a1    rA
                          >>> match_iregs a2    rB
                          >>> match_bools false rc
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_mulhwu", [IR a1; IR a2], IR res ->
                      begin match ecode with
                      | MULHWUx(rD, rA, rB, rc) :: es ->
                          fw
                          >>> match_iregs res   rD
                          >>> match_iregs a1    rA
                          >>> match_iregs a2    rB
                          >>> match_bools false rc
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_cntlz", [IR a1], IR res ->
                      begin match ecode with
                      | CNTLZWx(rS, rA, rc) :: es ->
                          fw
                          >>> match_iregs a1    rS
                          >>> match_iregs res   rA
                          >>> match_bools false rc
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_bswap", [IR a1], IR res ->
                      begin match ecode with
                      |   STWU (rS0, rA0, d0)    ::
                          LWBRX(rD1, rA1, rB1)   ::
                          ADDI (rD2, rA2, simm2) :: es ->
                          fw
                          >>> match_iregs  a1    rS0
                          >>> match_iregs  GPR1  rA0
                          >>> match_int32s (-8l) (exts d0)
                          >>> match_iregs  res   rD1
                          >>> match_iregs  GPR0  rA1
                          >>> match_iregs  GPR1  rB1
                          >>> match_iregs  GPR1  rD2
                          >>> match_iregs  GPR1  rA2
                          >>> match_int32s 8l    (exts simm2)
                          >>> compare_code cs es (Int32.add 12l pc)
                      | _ -> error
                      end
                  | "__builtin_fmadd", [FR a1; FR a2; FR a3], FR res ->
                      begin match ecode with
                      | FMADDx(frD, frA, frB, frC, rc) :: es ->
                          fw
                          >>> match_fregs res frD
                          >>> match_fregs a1 frA
                          >>> match_fregs a3 frB
                          >>> match_fregs a2 frC
                          >>> match_bools false rc
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fmsub", [FR a1; FR a2; FR a3], FR res ->
                      begin match ecode with
                      | FMSUBx(frD, frA, frB, frC, rc) :: es ->
                          fw
                          >>> match_fregs res frD
                          >>> match_fregs a1 frA
                          >>> match_fregs a3 frB
                          >>> match_fregs a2 frC
                          >>> match_bools false rc
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fnmadd", [FR a1; FR a2; FR a3], FR res ->
                      begin match ecode with
                      | FNMADDx(frD, frA, frB, frC, rc) :: es ->
                          fw
                          >>> match_fregs res frD
                          >>> match_fregs a1 frA
                          >>> match_fregs a3 frB
                          >>> match_fregs a2 frC
                          >>> match_bools false rc
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fnmsub", [FR a1; FR a2; FR a3], FR res ->
                      begin match ecode with
                      | FNMSUBx(frD, frA, frB, frC, rc) :: es ->
                          fw
                          >>> match_fregs res frD
                          >>> match_fregs a1 frA
                          >>> match_fregs a3 frB
                          >>> match_fregs a2 frC
                          >>> match_bools false rc
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fabs", [FR a1], FR res ->
                      begin match ecode with
                      | FABSx(frD, frB, rc) :: es ->
                          fw
                          >>> match_fregs res   frD
                          >>> match_fregs a1    frB
                          >>> match_bools false rc
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fsqrt", [FR a1], FR res ->
                      begin match ecode with
                      | FSQRTx(frD, frB, rc) :: es ->
                          fw
                          >>> match_fregs res   frD
                          >>> match_fregs a1    frB
                          >>> match_bools false rc
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_frsqrte", [FR a1], FR res ->
                      begin match ecode with
                      | FRSQRTEx(frD, frB, rc) :: es ->
                          fw
                          >>> match_fregs res   frD
                          >>> match_fregs a1    frB
                          >>> match_bools false rc
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fres", [FR a1], FR res ->
                      begin match ecode with
                      | FRESx(frD, frB, rc) :: es ->
                          fw
                          >>> match_fregs res   frD
                          >>> match_fregs a1    frB
                          >>> match_bools false rc
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_fsel", [FR a1; FR a2; FR a3], FR res ->
                      begin match ecode with
                      | FSELx(frD, frA, frB, frC, rc) :: es ->
                          fw
                          >>> match_fregs res frD
                          >>> match_fregs a1 frA
                          >>> match_fregs a3 frB
                          >>> match_fregs a2 frC
                          >>> match_bools false rc
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_read16_reversed", [IR a1], IR res ->
                      begin match ecode with
                      | LHBRX(rD, rA, rB):: es ->
                          fw
                          >>> match_iregs res  rD
                          >>> match_iregs GPR0 rA
                          >>> match_iregs a1   rB
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_read32_reversed", [IR a1], IR res ->
                      begin match ecode with
                      | LWBRX(rD, rA, rB) :: es ->
                          fw
                          >>> match_iregs res  rD
                          >>> match_iregs GPR0 rA
                          >>> match_iregs a1   rB
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_write16_reversed", [IR a1; IR a2], _ ->
                      begin match ecode with
                      | STHBRX(rS, rA, rB) :: es ->
                          fw
                          >>> match_iregs a2   rS
                          >>> match_iregs GPR0 rA
                          >>> match_iregs a1   rB
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_write32_reversed", [IR a1; IR a2], _ ->
                      begin match ecode with
                      | STWBRX(rS, rA, rB) :: es ->
                          fw
                          >>> match_iregs a2   rS
                          >>> match_iregs GPR0 rA
                          >>> match_iregs a1   rB
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_eieio", [], _ ->
                      begin match ecode with
                      | EIEIO :: es ->
                          fw
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_sync", [], _ ->
                      begin match ecode with
                      | SYNC :: es ->
                          fw
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_isync", [], _ ->
                      begin match ecode with
                      | ISYNC :: es ->
                          fw
                          >>> recur_simpl
                      | _ -> error
                      end
                  | "__builtin_trap", [], _ ->
                      begin match ecode with
                      | TW(tO, rA, rB) :: es ->
                          fw
                          >>> (ff_ef ^%=
                              bitmatch tO with
                              | { 31 : 5 : int } -> id
                              | { _ } -> add_log (ERROR("bitmatch"))
                          )
                          >>> match_iregs GPR0 rA
                          >>> match_iregs GPR0 rB
                          >>> recur_simpl
                      | _ -> error
                      end
                  | _ -> error
              end
          | EF_vload(chunk) ->
              begin match args with
              | [IR addr] ->
                  fw
                  >>> check_builtin_vload_common
                    cs ecode pc chunk addr (Cint Integers.Int.zero) res
              | _ -> assert false
              end
          | EF_vstore(chunk) ->
              begin match args with
              | [IR addr; src] ->
                  fw
                  >>> check_builtin_vstore_common
                    cs ecode pc chunk addr (Cint Integers.Int.zero) src
              | _ -> assert false
              end
          | EF_vload_global(chunk, ident, ofs) ->
              begin match ecode with
              | ADDIS(rD, rA, simm) :: es ->
                  let high = Csymbol_high(ident, ofs) in
                  fw
                  >>> match_iregs  GPR11 rD
                  >>> match_iregs  GPR0  rA
                  >>> match_csts   high  (Safe32.of_int simm)
                  >>> check_builtin_vload_common
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
                      fw
                      >>> match_iregs  tmp   rD
                      >>> match_iregs  GPR0  rA
                      >>> match_csts   high  (Safe32.of_int simm)
                      >>> check_builtin_vstore_common
                        cs es (Int32.add pc 4l) chunk tmp
                        (Csymbol_low(ident, ofs)) src
                  | _ -> error
                  end
              | _ -> assert false
              end
          | EF_memcpy(sz, al) ->
              let sz = z_int sz in
              let al = z_int al in
              begin match args with
              | [IR dst; IR src] ->
                  if sz <= 64
                  then (
                    match match_memcpy_small ecode pc sz al src dst fw with
                    | None -> error
                    | Some(fw, es, pc) -> compare_code cs es pc fw
                  )
                  else (
                    match match_memcpy_big ecode pc sz al src dst fw with
                    | None -> error
                    | Some(fw, es, pc) -> compare_code cs es pc fw
                  )
              | _ -> error
              end
          | EF_annot_val(text, targ) ->
              begin match args, res with
              | IR src :: _, IR dst ->
                  if dst <> src
                  then (
                    match ecode with
                    | ORx(rS, rA, rB, rc) :: es ->
                        fw
                        >>> match_iregs src rS
                        >>> match_iregs dst rA
                        >>> match_iregs src rB
                        >>> match_bools false rc
                        >>> recur_simpl
                    | _ -> error
                  )
                  else compare_code cs ecode pc fw
              | FR src :: _, FR dst ->
                  if dst <> src
                  then (
                    match ecode with
                    | FMRx(frD, frB, rc) :: es ->
                        fw
                        >>> match_fregs dst frD
                        >>> match_fregs src frB
                        >>> match_bools false rc
                        >>> recur_simpl
                    | _ -> error
                  )
                  else compare_code cs ecode pc fw
              | _ -> error
              end
          | EF_annot(_, _) -> assert false
          | EF_external(_, _) -> assert false
          | EF_free -> assert false
          | EF_malloc -> assert false
          end
      | Pcmplw(r1, r2) ->
          begin match ecode with
          | CMPL(crfD, l, rA, rB) :: es ->
              fw
              >>> match_crbits CRbit_0 crfD
              >>> match_bools  false   l
              >>> match_iregs  r1      rA
              >>> match_iregs  r2      rB
              >>> recur_simpl
          | _ -> error
          end
      | Pcmplwi(r1, cst) ->
          begin match ecode with
          | CMPLI(crfD, l, rA, uimm) :: es ->
              fw
              >>> match_iregs  r1      rA
              >>> match_csts   cst     (Safe32.of_int uimm)
              >>> match_crbits CRbit_0 crfD
              >>> match_bools  false   l
              >>> recur_simpl
          | _ -> error
          end
      | Pcmpw(r1, r2) ->
          begin match ecode with
          | CMP(crfD, l, rA, rB) :: es ->
              fw
              >>> match_ints  crfD 0
              >>> match_bools l    false
              >>> match_iregs r1   rA
              >>> match_iregs r2   rB
              >>> recur_simpl
          | _ -> error
          end
      | Pcmpwi(r1, cst) ->
          begin match ecode with
          | CMPI(crfD, l, rA, simm) :: es ->
              fw
              >>> match_ints  crfD  0
              >>> match_bools false l
              >>> match_iregs r1    rA
              >>> match_csts  cst   (exts simm)
              >>> recur_simpl
          | _ -> error
          end
      | Pcror(bd, b1, b2) ->
          begin match ecode with
          | CROR(crbD, crbA, crbB) :: es ->
              fw
              >>> match_crbits bd crbD
              >>> match_crbits b1 crbA
              >>> match_crbits b2 crbB
              >>> recur_simpl
          | _ -> error
          end
      | Pdivw(rd, r1, r2) ->
          begin match ecode with
          | DIVWx(rD, rA, rB, oe, rc) :: es ->
              fw
              >>> match_iregs rd    rD
              >>> match_iregs r1    rA
              >>> match_iregs r2    rB
              >>> match_bools false oe
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pdivwu(rd, r1, r2) ->
          begin match ecode with
          | DIVWUx(rD, rA, rB, oe, rc) :: es ->
              fw
              >>> match_iregs rd    rD
              >>> match_iregs r1    rA
              >>> match_iregs r2    rB
              >>> match_bools false oe
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Peqv(rd, r1, r2) ->
          begin match ecode with
          | EQVx(rS, rA, rB, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_iregs r2    rB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pextsb(rd, r1) ->
          begin match ecode with
          | EXTSBx(rS, rA, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pextsh(rd, r1) ->
          begin match ecode with
          | EXTSHx(rS, rA, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pfabs(rd, r1) ->
          begin match ecode with
          | FABSx(frD, frB, rc) :: es ->
              fw
              >>> match_fregs rd    frD
              >>> match_fregs r1    frB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pfadd(rd, r1, r2) ->
          begin match ecode with
          | FADDx(frD, frA, frB, rc) :: es ->
              fw
              >>> match_fregs rd    frD
              >>> match_fregs r1    frA
              >>> match_fregs r2    frB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pfcmpu(r1, r2) ->
          begin match ecode with
          | FCMPU(crfD, frA, frB) :: es ->
              fw
              >>> match_crbits CRbit_0 crfD
              >>> match_fregs  r1      frA
              >>> match_fregs  r2      frB
              >>> recur_simpl
          | _ -> error
          end
      | Pfcti(rd, r1) ->
          begin match ecode with
          |   FCTIWZx(frD0, frB0, rc0)   ::
              STFDU  (frS1, rA1,  d1)    ::
              LWZ    (rD2,  rA2,  d2)    ::
              ADDI   (rD3,  rA3,  simm3) :: es ->
              fw
              >>> match_fregs  FPR13 frD0
              >>> match_fregs  r1    frB0
              >>> match_bools  false rc0
              >>> match_fregs  FPR13 frS1
              >>> match_iregs  GPR1  rA1
              >>> match_int32s (-8l) (exts d1)
              >>> match_iregs  rd    rD2
              >>> match_iregs  GPR1  rA2
              >>> match_int32s 4l    (exts d2)
              >>> match_iregs  GPR1  rD3
              >>> match_iregs  GPR1  rA3
              >>> match_int32s 8l    (exts simm3)
              >>> compare_code cs es (Int32.add 16l pc)
          | _ -> error
          end
      | Pfdiv(rd, r1, r2) ->
          begin match ecode with
          | FDIVx(frD, frA, frB, rc) :: es ->
              fw
              >>> match_fregs rd    frD
              >>> match_fregs r1    frA
              >>> match_fregs r2    frB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pfmake(rd, r1, r2) ->
          begin match ecode with
          |   STWU  (rS0, rA0, d0)    ::
              STW   (rS1, rA1, d1)    ::
              LFD   (frD2, rA2, d2)   ::
              ADDI  (rD3, rA3, simm3) :: es ->
              fw
              >>> match_iregs  r1    rS0
              >>> match_iregs  GPR1  rA0
              >>> match_int32s (-8l) (exts d0)
              >>> match_iregs  r2    rS1
              >>> match_iregs  GPR1  rA1
              >>> match_int32s 4l    (exts d1)
              >>> match_fregs  rd    frD2
              >>> match_iregs  GPR1  rA2
              >>> match_int32s 0l    (exts d2)
              >>> match_iregs  GPR1  rD3
              >>> match_iregs  GPR1  rA3
              >>> match_int32s 8l    (exts simm3)
              >>> compare_code cs es (Int32.add 16l pc)
          | _ -> error
          end
      | Pfmr(rd, r1) ->
          begin match ecode with
          | FMRx(frD, frB, rc) :: es ->
              fw
              >>> match_fregs rd    frD
              >>> match_fregs r1    frB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pfmul(rd, r1, r2) ->
          begin match ecode with
          | FMULx(frD, frA, frC, rc) :: es ->
              fw
              >>> match_fregs rd    frD
              >>> match_fregs r1    frA
              >>> match_fregs r2    frC
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pfneg (rd, r1) ->
          begin match ecode with
          | FNEGx(frD, frB, rc) :: es ->
              fw
              >>> match_fregs rd    frD
              >>> match_fregs r1    frB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pfreeframe(sz, ofs) ->
          begin match ecode with
          | LWZ(rD, rA, d) :: es ->
              fw
              >>> match_iregs   GPR1 rD
              >>> match_iregs   GPR1 rA
              >>> match_z_int32 ofs  (Int32.neg (exts d))
              >>> recur_simpl
          | _ -> error
          end
      | Pfrsp(rd, r1) ->
          begin match ecode with
          | FRSPx(frD, frB, rc) :: es ->
              fw
              >>> match_fregs rd    frD
              >>> match_fregs r1    frB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pfsub(rd, r1, r2) ->
          begin match ecode with
          | FSUBx(frD, frA, frB, rc) :: es ->
              fw
              >>> match_fregs rd    frD
              >>> match_fregs r1    frA
              >>> match_fregs r2    frB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Plabel(lbl) ->
          fw
          >>> lblmap_unify lbl pc
          >>? (fun fw -> {fw with label_list = lbl :: fw.label_list})
          >>= compare_code cs ecode pc
      | Plbz(rd, cst, r1) ->
          begin match ecode with
          | LBZ(rD, rA, d) :: es ->
              fw
              >>> match_iregs rd  rD
              >>> match_csts  cst (exts d)
              >>> match_iregs r1  rA
              >>> recur_simpl
          | _ -> error
          end
      | Plbzx(rd, r1, r2) ->
          begin match ecode with
          | LBZX(rD, rA, rB) :: es ->
              fw
              >>> match_iregs rd rD
              >>> match_iregs r1 rA
              >>> match_iregs r2 rB
              >>> recur_simpl
          | _ -> error
          end
      | Plfd(rd, cst, r1) ->
          begin match ecode with
          | LFD(frD, rA, d) :: es ->
              fw
              >>> match_fregs rd  frD
              >>> match_csts  cst (exts d)
              >>> match_iregs r1  rA
              >>> recur_simpl
          | _ -> error
          end
      | Plfdx(rd, r1, r2) ->
          begin match ecode with
          | LFDX(frD, rA, rB) :: es ->
              fw
              >>> match_fregs rd frD
              >>> match_iregs r1 rA
              >>> match_iregs r2 rB
              >>> recur_simpl
          | _ -> error
          end
      | Plfs(rd, cst, r1) ->
          begin match ecode with
          | LFS(frD, rA, d) :: es ->
              fw
              >>> match_fregs rd  frD
              >>> match_csts  cst (exts d)
              >>> match_iregs r1  rA
              >>> recur_simpl
          | _ -> error
          end
      | Plfsx(rd, r1, r2) ->
          begin match ecode with
          | LFSX(frD, rA, rB) :: es ->
              fw
              >>> match_fregs rd frD
              >>> match_iregs r1 rA
              >>> match_iregs r2 rB
              >>> recur_simpl
          | _ -> error
          end
      | Plha(rd, cst, r1) ->
          begin match ecode with
          | LHA(rD, rA, d) :: es ->
              fw
              >>> match_iregs rd  rD
              >>> match_csts  cst (exts d)
              >>> match_iregs r1  rA
              >>> recur_simpl
          | _ -> error
          end
      | Plhax(rd, r1, r2) ->
          begin match ecode with
          | LHAX(rD, rA, rB) :: es ->
              fw
              >>> match_iregs rd rD
              >>> match_iregs r1 rA
              >>> match_iregs r2 rB
              >>> recur_simpl
          | _ -> error
          end
      | Plhzx(rd, r1, r2) ->
          begin match ecode with
          | LHZX(rD, rA, rB) :: es ->
              fw
              >>> match_iregs rd rD
              >>> match_iregs r1 rA
              >>> match_iregs r2 rB
              >>> recur_simpl
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
                begin match section_at_vaddr elf vaddr with
                | None ->
                    ERR("Float literal's virtual address out of any section")
                | Some(sndx) ->
                    let section_bitstring = bitstring_at_vaddr elf sndx in
                    let f = (
                      let bs =
                        begin match section_bitstring vaddr 64 with
                        | None -> assert false
                        | Some(bs) -> bs
                        end
                      in
                      bitmatch bs with
                      | { f : 64 : int } -> Int64.float_of_bits f
                    ) in
                    let ofs = physical_offset_of_vaddr elf sndx vaddr in
                    fw
                    >>> (ff_sf ^%=
                        match_sections_name
                          literal_section
                          elf.e_shdra.(sndx).sh_name
                    )
                    >>> match_iregs  GPR12 rD0
                    >>> match_iregs  GPR0  rA0
                    >>> match_fregs  r1    frD1
                    >>> match_floats c     f
                    >>> (ff_ef ^%= add_range ofs 8l 8 (Float_literal(f)))
                    >>> match_iregs  GPR12 rA1
                    >>> compare_code cs es (Int32.add 8l pc)
                end
          | _ -> error
          end
      | Plhz(rd, cst, r1) ->
          begin match ecode with
          | LHZ(rD, rA, d) :: es ->
              fw
              >>> match_iregs rd  rD
              >>> match_csts  cst (exts d)
              >>> match_iregs r1  rA
              >>> recur_simpl
          | _ -> error
          end
      | Plwz(rd, cst, r1) ->
          begin match ecode with
          | LWZ(rD, rA, d) :: es ->
              fw
              >>> match_iregs rd  rD
              >>> match_iregs r1  rA
              >>> match_csts  cst (exts d)
              >>> recur_simpl
          | _ -> error
          end
      | Plwzx(rd, r1, r2) ->
          begin match ecode with
          | LWZX(rD, rA, rB) :: es ->
              fw
              >>> match_iregs rd rD
              >>> match_iregs r1 rA
              >>> match_iregs r2 rB
              >>> recur_simpl
          | _ -> error
          end
      | Pmfcrbit(rd, bit) ->
          begin match ecode with
          |   MFCR   (rD0)                          ::
              RLWINMx(rS1, rA1, sh1, mb1, me1, rc1) :: es ->
              fw
              >>> match_iregs  rd    rD0
              >>> match_iregs  rd    rS1
              >>> match_iregs  rd    rA1
              >>> match_crbits bit   (sh1 - 1)
              >>> match_ints   31    mb1
              >>> match_ints   31    me1
              >>> match_bools  false rc1
              >>> compare_code cs es (Int32.add 8l pc)
          | _ -> error
          end
      | Pmflr(r) ->
          begin match ecode with
          | MFSPR(rD, spr) :: es ->
              fw
              >>> match_iregs r   rD
              >>> match_lr    spr
              >>> recur_simpl
          | _ -> error
          end
      | Pmr(rd, r1) ->
          begin match ecode with
          | ORx(rS, rA, rB, rc) :: es when (rB = rS) ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pmtctr(r1) ->
          begin match ecode with
          | MTSPR(rS, spr) :: es ->
              fw
              >>> match_iregs r1 rS
              >>> match_ctr   spr
              >>> recur_simpl
          | _ -> error
          end
      | Pmtlr(r1) ->
          begin match ecode with
          | MTSPR(rS, spr) :: es ->
              fw
              >>> match_iregs r1  rS
              >>> match_lr    spr
              >>> recur_simpl
          | _ -> error
          end
      | Pmulli(rd, r1, cst) ->
          begin match ecode with
          | MULLI(rD, rA, simm) :: es ->
              fw
              >>> match_iregs rd  rD
              >>> match_iregs r1  rA
              >>> match_csts  cst (exts simm)
              >>> recur_simpl
          | _ -> error
          end
      | Pmullw(rd, r1, r2) ->
          begin match ecode with
          | MULLWx(rD, rA, rB, oe, rc) :: es ->
              fw
              >>> match_iregs rd    rD
              >>> match_iregs r1    rA
              >>> match_iregs r2    rB
              >>> match_bools false oe
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pnand(rd, r1, r2) ->
          begin match ecode with
          | NANDx(rS, rA, rB, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_iregs r2    rB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pnor(rd, r1, r2) ->
          begin match ecode with
          | NORx(rS, rA, rB, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_iregs r2    rB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Por(rd, r1, r2) ->
          begin match ecode with
          | ORx(rS, rA, rB, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_iregs r2    rB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Porc(rd, r1, r2) ->
          begin match ecode with
          | ORCx(rS, rA, rB, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_iregs r2    rB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pori(rd, r1, cst) ->
          begin match ecode with
          | ORI(rS, rA, uimm) :: es ->
              fw
              >>> match_iregs rd  rA
              >>> match_iregs r1  rS
              >>> match_csts  cst (Safe32.of_int uimm)
              >>> recur_simpl
          | _ -> error
          end
      | Poris(rd, r1, cst) ->
          begin match ecode with
          | ORIS(rS, rA, uimm) :: es ->
              fw
              >>> match_iregs rd  rA
              >>> match_iregs r1  rS
              >>> match_csts  cst (Safe32.of_int uimm)
              >>> recur_simpl
          | _ -> error
          end
      | Prlwimi(rd, r1, amount, mask) ->
          begin match ecode with
          | RLWIMIx(rS, rA, sh, mb, me, rc) :: es ->
              fw
              >>> match_iregs r1     rS
              >>> match_iregs rd     rA
              >>> match_z_int amount sh
              >>> match_mask  mask   (bitmask mb me)
              >>> match_bools false  rc
              >>> recur_simpl
          | _ -> error
          end
      | Prlwinm(rd, r1, amount, mask) ->
          begin match ecode with
          | RLWINMx(rS, rA, sh, mb, me, rc) :: es ->
              fw
              >>> match_iregs r1     rS
              >>> match_iregs rd     rA
              >>> match_z_int amount sh
              >>> match_mask  mask   (bitmask mb me)
              >>> match_bools false  rc
              >>> recur_simpl
          | _ -> error
          end
      | Pslw(rd, r1, r2) ->
          begin match ecode with
          | SLWx(rS, rA, rB, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_iregs r2    rB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Psraw(rd, r1, r2) ->
          begin match ecode with
          | SRAWx(rS, rA, rB, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_iregs r2    rB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Psrawi(rd, r1, n) ->
          begin match ecode with
          | SRAWIx(rS, rA, sh, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_z_int n     sh
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Psrw(rd, r1, r2) ->
          begin match ecode with
          | SRWx(rS, rA, rB, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_iregs r2    rB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pstb(rd, cst, r1) ->
          begin match ecode with
          | STB(rS, rA, d) :: es ->
              fw
              >>> match_iregs rd  rS
              >>> match_iregs r1  rA
              >>> match_csts  cst (exts d)
              >>> recur_simpl
          | _ -> error
          end
      | Pstbx(rd, r1, r2) ->
          begin match ecode with
          | STBX(rS, rA, rB) :: es ->
              fw
              >>> match_iregs rd rS
              >>> match_iregs r1 rA
              >>> match_iregs r2 rB
              >>> recur_simpl
          | _ -> error
          end
      | Pstfd(rd, cst, r1) ->
          begin match ecode with
          | STFD(frS, rA, d) :: es ->
              fw
              >>> match_fregs rd  frS
              >>> match_iregs r1  rA
              >>> match_csts  cst (exts d)
              >>> recur_simpl
          | _ -> error
          end
      | Pstfdx(rd, r1, r2) ->
          begin match ecode with
          | STFDX(frS, rA, rB) :: es ->
              fw
              >>> match_fregs rd frS
              >>> match_iregs r1 rA
              >>> match_iregs r2 rB
              >>> recur_simpl
          | _ -> error
          end
      | Pstfs(rd, cst, r1) ->
          begin match ecode with
          |   FRSPx(frD0, frB0, rc0) ::
              STFS (frS1, rA1,  d1)  :: es ->
              fw
              >>> match_fregs FPR13 frD0
              >>> match_fregs rd    frB0
              >>> match_bools false rc0
              >>> match_fregs FPR13 frS1
              >>> match_iregs r1    rA1
              >>> match_csts  cst (exts d1)
              >>> compare_code cs es (Int32.add 8l pc)
          | _ -> error
          end
      | Pstfsx(rd, r1, r2) ->
          begin match ecode with
          |   FRSPx(frD0, frB0, rc0) ::
              STFSX(frS1, rA1,  rB1) :: es ->
              fw
              >>> match_fregs FPR13 frD0
              >>> match_fregs rd    frB0
              >>> match_bools false rc0
              >>> match_fregs FPR13 frS1
              >>> match_iregs r1    rA1
              >>> match_iregs r2    rB1
              >>> compare_code cs es (Int32.add 8l pc)
          | _ -> error
          end
      | Psth(rd, cst, r1) ->
          begin match ecode with
          | STH(rS, rA, d) :: es ->
              fw
              >>> match_iregs rd  rS
              >>> match_iregs r1  rA
              >>> match_csts  cst (exts d)
              >>> recur_simpl
          | _ -> error
          end
      | Psthx(rd, r1, r2) ->
          begin match ecode with
          | STHX(rS, rA, rB) :: es ->
              fw
              >>> match_iregs rd rS
              >>> match_iregs r1 rA
              >>> match_iregs r2 rB
              >>> recur_simpl
          | _ -> error
          end
      | Pstw(rd, cst, r1) ->
          begin match ecode with
          | STW(rS, rA, d) :: es ->
              fw
              >>> match_iregs rd  rS
              >>> match_iregs r1  rA
              >>> match_csts  cst (exts d)
              >>> recur_simpl
          | _ -> error
          end
      | Pstwx(rd, r1, r2) ->
          begin match ecode with
          | STWX(rS, rA, rB) :: es ->
              fw
              >>> match_iregs rd rS
              >>> match_iregs r1 rA
              >>> match_iregs r2 rB
              >>> recur_simpl
          | _ -> error
          end
      | Psubfc(rd, r1, r2) ->
          begin match ecode with
          | SUBFCx(rD, rA, rB, oe, rc) :: es ->
              fw
              >>> match_iregs rd    rD
              >>> match_iregs r1    rA
              >>> match_iregs r2    rB
              >>> match_bools false oe
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Psubfe(rd, r1, r2) ->
          begin match ecode with
          | SUBFEx(rD, rA, rB, oe, rc) :: es ->
              fw
              >>> match_iregs rd    rD
              >>> match_iregs r1    rA
              >>> match_iregs r2    rB
              >>> match_bools false oe
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Psubfic(rd, r1, cst) ->
          begin match ecode with
          | SUBFIC(rD, rA, simm) :: es ->
              fw
              >>> match_iregs rd  rD
              >>> match_iregs r1  rA
              >>> match_csts  cst (exts simm)
              >>> recur_simpl
          | _ -> error
          end
      | Pxor(rd, r1, r2) ->
          begin match ecode with
          | XORx(rS, rA, rB, rc) :: es ->
              fw
              >>> match_iregs rd    rA
              >>> match_iregs r1    rS
              >>> match_iregs r2    rB
              >>> match_bools false rc
              >>> recur_simpl
          | _ -> error
          end
      | Pxori(rd, r1, cst) ->
          begin match ecode with
          | XORI(rS, rA, uimm) :: es ->
              fw
              >>> match_iregs rd  rA
              >>> match_iregs r1  rS
              >>> match_csts  cst (Safe32.of_int uimm)
              >>> recur_simpl
          | _ -> error
          end
      | Pxoris(rd, r1, cst) ->
          begin match ecode with
          | XORIS(rS, rA, uimm) :: es ->
              fw
              >>> match_iregs rd  rA
              >>> match_iregs r1  rS
              >>> match_csts  cst (Safe32.of_int uimm)
              >>> recur_simpl
          | _ -> error
          end
and check_builtin_vload_common ccode ecode pc chunk addr offset res fw =
  let error = ERR("Non-matching instructions") in
  let recur_simpl = compare_code ccode (List.tl ecode) (Int32.add pc 4l) in
  begin match chunk, res with
  | Mint8unsigned, IR res ->
      begin match ecode with
      | LBZ(rD, rA, d) :: es ->
          fw
          >>> match_iregs  res    rD
          >>> match_iregs  addr   rA
          >>> match_csts   offset (exts d)
          >>> recur_simpl
      | _ -> error
      end
  | Mint8signed, IR res ->
      begin match ecode with
      |   LBZ   (rD0, rA0, d0)  ::
          EXTSBx(rS1, rA1, rc1) :: es ->
          fw
          >>> match_iregs  res    rD0
          >>> match_iregs  addr   rA0
          >>> match_csts   offset (exts d0)
          >>> match_iregs  res    rS1
          >>> match_iregs  res    rA1
          >>> match_bools  false  rc1
          >>> compare_code ccode es (Int32.add 8l pc)
      | _ -> error
      end
  | Mint16unsigned, IR res ->
      begin match ecode with
      | LHZ(rD, rA, d) :: es ->
          fw
          >>> match_iregs  res    rD
          >>> match_iregs  addr   rA
          >>> match_csts   offset (exts d)
          >>> recur_simpl
      | _ -> error
      end
  | Mint16signed, IR res ->
      begin match ecode with
      | LHA(rD, rA, d) :: es ->
          fw
          >>> match_iregs  res    rD
          >>> match_iregs  addr   rA
          >>> match_csts   offset (exts d)
          >>> recur_simpl
      | _ -> error
      end
  | Mint32, IR res ->
      begin match ecode with
      | LWZ(rD, rA, d) :: es ->
          fw
          >>> match_iregs  res    rD
          >>> match_iregs  addr   rA
          >>> match_csts   offset (exts d)
          >>> recur_simpl
      | _ -> error
      end
  | Mfloat32, FR res ->
      begin match ecode with
      | LFS(frD, rA, d) :: es ->
          fw
          >>> match_fregs  res    frD
          >>> match_iregs  addr   rA
          >>> match_csts   offset (exts d)
          >>> recur_simpl
      | _ -> error
      end
  | Mfloat64, FR res ->
      begin match ecode with
      | LFD(frD, rA, d) :: es ->
          fw
          >>> match_fregs  res    frD
          >>> match_iregs  addr   rA
          >>> match_csts   offset (exts d)
          >>> recur_simpl
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
          fw
          >>> match_iregs  src    rS
          >>> match_iregs  addr   rA
          >>> match_csts   offset (exts d)
          >>> recur_simpl
      | _ -> error
      end
  | (Mint16signed | Mint16unsigned), IR src ->
      begin match ecode with
      | STH(rS, rA, d) :: es ->
          fw
          >>> match_iregs  src    rS
          >>> match_iregs  addr   rA
          >>> match_csts   offset (exts d)
          >>> recur_simpl
      | _ -> error
      end
  | Mint32, IR src ->
      begin match ecode with
      | STW(rS, rA, d) :: es ->
          fw
          >>> match_iregs  src    rS
          >>> match_iregs  addr   rA
          >>> match_csts   offset (exts d)
          >>> recur_simpl
      | _ -> error
      end
  | Mfloat32, FR src ->
      begin match ecode with
      |   FRSPx(frD0, frB0, rc0) ::
          STFS (frS1, rA1,  d1)  :: es ->
          fw
          >>> match_fregs  FPR13  frD0
          >>> match_fregs  src    frB0
          >>> match_bools  false  rc0
          >>> match_fregs  FPR13  frS1
          >>> match_iregs  addr   rA1
          >>> match_csts   offset (exts d1)
          >>> compare_code ccode es (Int32.add pc 8l)
      | _ -> error
      end
  | Mfloat64, FR src ->
      begin match ecode with
      | STFD(frS, rA, d) :: es ->
          fw
          >>> match_fregs  src    frS
          >>> match_iregs  addr   rA
          >>> match_csts   offset (exts d)
          >>> recur_simpl
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
            >>? mark_covered_fun_sym_ndx ndx
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
                "Unique candidate did not match: " ^ s
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
              add_log (ERROR("No matching candidate"))
              >>> worklist_process wl
          | [ffw] ->
              worklist_process wl ffw.sf
          | fws ->
              sfw
              >>> sf_ef ^%=
              add_log (ERROR(
                "Multiple matching candidates for symbol: " ^ name
              ))
              >>> worklist_process wl
          end
      end

(** This variant helps representing big empty bitstrings without allocating
    memory. It is useful to create a bitstring for an STT_NOBITS symbol, for
    instance.
*)
type maybe_bitstring =
  | Empty of int
  | NonEmpty of bitstring

(** Compares a data symbol with its expected contents. Returns the updated
    framework as well as the size of the data matched.
**)
let compare_data (l: init_data list) (maybebs: maybe_bitstring) (sfw: s_framework)
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
            (sf_ef ^%= add_log (DEBUG(string_of_init_data d))) sfw
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
              if f = Int32.float_of_bits j
              then compare_data_aux l bs (s + 4) sfw
              else ERR("Wrong float32")
          | { _ } -> error
        )
        | Init_float64(f) -> (
          bitmatch bs with
          | { j : 64 : int; bs : -1 : bitstring } ->
              if f = Int64.float_of_bits j
              then compare_data_aux l bs (s + 8) sfw
              else ERR("Wrong float64")
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
  let rec compare_data_empty l s (sfw: s_framework):
      (s_framework * int) or_err =
    match l with
    | [] -> OK(sfw, s)
    | d::l ->
        begin match d with
        | Init_space(z) -> compare_data_empty l (s + z_int z) sfw
        | _ -> ERR("Expected empty data")
        end
  in
  match maybebs with
  | Empty(_)     -> compare_data_empty l 0 sfw
  | NonEmpty(bs) -> compare_data_aux l bs 0 sfw

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
    let elf = (sfw |. sf_ef).elf in
    let sym = elf.e_symtab.(ndx) in
    let sym_vaddr = sym.st_value in
    let sym_size = sym.st_size in
    let sym_sndx = sym.st_shndx in
    let sym_bs_opt =
      begin match elf.e_shdra.(sym_sndx).sh_type with
      | SHT_NOBITS ->
          Some(Empty(Safe.(of_int32 sym.st_size * 8)))
      | SHT_PROGBITS ->
          begin match bitstring_at_vaddr_nosize elf sym_sndx sym_vaddr with
          | None -> None
          | Some(bs) -> Some(NonEmpty(bs))
          end
      | _ -> assert false
      end
    in
    let res =
      begin match sym_bs_opt with
      | None -> ERR("Could not find symbol data for data symbol " ^ sym.st_name)
      | Some(sym_bs) ->
          sfw
          >>> (sf_ef ^%= add_log (DEBUG("Processing data: " ^ sym.st_name)))
          >>> compare_data ldata sym_bs
      end
    in
    match res with
    | ERR(s) -> ERR(s)
    | OK(sfw, size) ->
        let sym_shdr = (sfw |. sf_ef).elf.e_shdra.(sym_sndx) in
        let sym_ofs_local = Int32.sub sym_vaddr sym_shdr.sh_addr in
        let sxn_ofs = sym_shdr.sh_offset in
        let sym_begin = Int32.add sxn_ofs sym_ofs_local in
        let align =
          begin match (Hashtbl.find sfw.atoms ident).a_alignment with
          | None -> 0
          | Some(a) -> a
          end
        in
        sfw.ef.chkd_data_syms.(ndx) <- true;
        sfw
        >>> (
          begin match sym_shdr.sh_type with
          | SHT_NOBITS ->
              id (* These occupy no space, for now we just forget them *)
          | _ ->
              sf_ef ^%=
              add_range sym_begin sym_size align (Data_symbol(sym))
          end
        )
        >>> (
          if not (is_well_aligned sym_ofs_local align)
          then (
            sf_ef ^%= add_log (ERROR(
              "Symbol not correctly aligned in the ELF file"
            ))
          )
          else id
        )
        >>> check_data_symtab ident ndx size
        >>> (fun sfw -> OK(sfw))
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
    let fundef = List.find (fun (i, _) -> i = ident) sfw.program.prog_funct
    in
    let elf = sfw.ef.elf in
    let stub_ecode = from_some (code_at_vaddr elf vaddr 2) in
    let stub_sndx = from_some (section_at_vaddr elf vaddr) in
    let stub_offset = physical_offset_of_vaddr elf stub_sndx vaddr in
    begin match fundef with
    | (_, External(EF_external(dest_ident, _) as ef)) ->
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
    | _ -> assert false
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
    if magic <> sdump_magic_number then failwith "bad magic number";
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

(** Processes a .sdump file.
*)
let process_sdump efw sdump: e_framework =
  if !debug then print_endline ("Beginning reading " ^ sdump);
  let (prog, names, atoms) = read_sdump sdump in
  if !debug then print_endline "Constructing mapping from idents to symbol indices";
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
  if !debug then print_endline "Constructing worklist";
  let worklist_fundefs =
    List.filter
      (fun f ->
        match snd f with
        | Internal _ -> true
        | External _ -> false
      )
      prog.prog_funct
  in
  let wl =
    List.map
      (fun f ->
        match f with
        | ident, Internal ccode -> (ident, Hashtbl.find names ident, ccode)
        | _,     External _     -> assert false
      )
      worklist_fundefs
  in
  if !debug then print_endline "Beginning processing of the worklist";
  efw
  >>> (fun efw ->
    {
      ef                  = efw;
      program             = prog;
      ident_to_name       = names;
      ident_to_sym_ndx    = ident_to_sym_ndx;
      stub_ident_to_vaddr = PosMap.empty;
      atoms               = atoms;
    }
  )
  >>> worklist_process wl
  >>> (fun sfw ->
    if !debug then print_endline "Checking stubs";
    sfw
  )
  >>> check_stubs
  >>> (fun sfw ->
    if !debug then print_endline "Checking data";
    sfw
  )
  >>> check_data prog.prog_vars
  >>> (fun sfw -> sfw.ef)

(** Builds the list [0; 1; ...; n - 1]. *)
let list_n (n: int): int list =
  let rec list_n_aux x l =
    if x < 0
    then l
    else list_n_aux (x - 1) (x :: l)
  in list_n_aux (n - 1) []

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
                let offset =
                  physical_offset_of_vaddr elf sym.st_shndx sym.st_value
                in
                intersect (x, y) offset sym.st_size
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
    | [] -> assert false
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
        if
          pad_start = b2 (* if they are directly consecutive *)
          || Safe.(of_int32 b2 - of_int32 e1) > a2 (* or if they are too far away *)
          || not (is_padding efw.elf.e_bitstring
                    (Safe32.to_int pad_start) (Safe32.to_int pad_stop))
        then (* not padding *)
          if pad_start <= pad_stop
          then check_padding_aux efw
            ((pad_start, pad_stop, 0, unknown pad_start pad_stop) :: h1 :: accu)
            (h2 :: rest)
          else check_padding_aux efw (h1 :: accu) (h2 :: rest)
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

let warn_sections_remapping efw =
  StringMap.fold
    (fun c_name e_name efw ->
      if c_name = e_name
      then efw
      else (
        efw >>> add_log (WARNING(
          Printf.sprintf
            "Section %s has been re-mapped to %s by your linker script"
            c_name e_name
        ))
      )
    )
    efw.section_map
    efw

(** Checks a whole ELF file according to a list of .sdump files. This never
    dumps anything, so it can be safely used when fuzz-testing even if the
    user accidentally enabled dumping options. *)
let check_elf_nodump elf sdumps =
  let eh = elf.e_hdr in
  let nb_syms = Array.length elf.e_symtab in
  let section_strtab = elf.e_shdra.(eh.e_shstrndx) in
  let symtab_shdr = elf.e_shdra.(elf.e_symtab_sndx) in
  let symbol_strtab = elf.e_shdra.(Safe32.to_int symtab_shdr.sh_link) in
  let efw =
    {
      elf = elf;
      log = [];
      chkd_bytes_list = [];
      chkd_fun_syms = Array.make nb_syms false;
      chkd_data_syms = Array.make nb_syms false;
      section_map = StringMap.empty;
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
  if !debug then print_endline "Done checking header, beginning processing of .sdumps";
  (* Thread the framework through the processing of all .sdump files *)
  List.fold_left process_sdump efw sdumps
  (* check the padding in between identified byte chunks *)
  >>> check_padding
  (* warn if some CompCert sections have been remapped by the linker script *)
  >>> warn_sections_remapping

(** Checks a whole ELF file according to .sdump files.
    If requested, dump the calculated bytes mapping, so that it can be
    reused by the fuzzer. *)
let check_elf_dump elffilename sdumps =
  if !debug then print_endline "Beginning ELF parsing";
  let elf = read_elf elffilename in
  if !debug then print_endline "Beginning ELF checking";
  let efw = check_elf_nodump elf sdumps in
  (* print the elfmap if requested *)
  if !print_elfmap then begin
    print_endline (
      string_of_list
        (fun (a, b, align, r) -> string_of_range a b ^ " (" ^
          string_of_int align ^ ") " ^ string_of_byte_chunk_desc r)
        "\n"
        efw.chkd_bytes_list
    )
  end;
  (* dump the elfmap if requested *)
  if !dump_elfmap then begin
    let oc = open_out (elffilename ^ ".elfmap") in
    output_value oc efw.chkd_bytes_list;
    close_out oc
  end;
  (* indicate function symbols that have not been checked *)
  let miss_fun =
    List.filter
      (fun ndx ->
        let symtype = efw.elf.e_symtab.(ndx).st_type in
        symtype = STT_FUNC || symtype = STT_NOTYPE
      )
      (filter_some
         (Array.to_list
            (Array.mapi
               (fun ndx b -> if b then None else Some(ndx))
               efw.chkd_fun_syms
            )
         )
      )
  in
  if !exhaustivity
  then
    begin match miss_fun with
    | [] -> ()
    | _  ->
        print_endline
          "\nWARNING: the following function symbols do not appear in .sdump files.";
        print_endline (
          string_of_list (fun ndx -> efw.elf.e_symtab.(ndx).st_name) " " miss_fun
        )
    end
  ;
  (* indicate data symbols that have not been checked *)
  let miss_data =
    List.filter
      (fun ndx ->
        let symtype = efw.elf.e_symtab.(ndx).st_type in
        symtype = STT_OBJECT || symtype = STT_NOTYPE
      )
      (filter_some
         (Array.to_list
            (Array.mapi
               (fun ndx b -> if b then None else Some(ndx))
               efw.chkd_data_syms
            )
         )
      )
  in
  if !exhaustivity
  then
    begin match miss_data with
    | [] -> ()
    | _  ->
        print_endline
          "\nWARNING: the following data symbols do not appear in .sdump files.";
        print_endline (
          string_of_list (fun ndx -> efw.elf.e_symtab.(ndx).st_name) " " miss_data
        )
    end
  ;
  (* print diagnosis *)
  let worrysome = List.filter
    (function ERROR(_) -> true | WARNING(_) -> true | DEBUG(_) -> false)
    efw.log
  in
  let exists_unknown_chunk =
    List.exists
      (function (_, _, _, Unknown(_)) -> true | _ -> false)
      efw.chkd_bytes_list
  in
  begin match worrysome with
  | [] ->
      print_endline "\nEverything seems fine with this ELF.";
      if exists_unknown_chunk
      then begin
        print_endline (
          "However, some parts of the ELF could not be identified." ^
            if !print_elfmap
            then ""
            else " Use -printelfmap to see what was covered."
        )
      end
  | _ ->
      List.(iter
              (fun e ->
                match string_of_log_entry false e with
                | "" -> ()
                | s -> print_endline s
              )
              (rev efw.log)
      )
  end
