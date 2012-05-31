open Library
open PPC_types

let parse_instr bs =
  bitmatch bs with
  | { 31:6; d:5;    a:5;    b:5;    oe:1;   266:9;  rc:1 }
    -> ADDx(d, a, b, oe, rc)
  | { 31:6; d:5;    a:5;    b:5;    oe:1;   10:9;   rc:1 }
    -> ADDCx(d, a, b, oe, rc)
  | { 31:6; d:5;    a:5;    b:5;    oe:1;   138:9;  rc:1 }
    -> ADDEx(d, a, b, oe, rc)
  | { 14:6; d:5;    a:5;    simm:16:bitstring }
    -> ADDI(d, a, simm)
  | { 12:6; d:5;    a:5;    simm:16:bitstring }
    -> ADDIC(d, a, simm)
  | { 13:6; d:5;    a:5;    simm:16:bitstring }
    -> ADDIC_(d, a, simm)
  | { 15:6; d:5;    a:5;    simm:16 }
    -> ADDIS(d, a, simm)
  | { 31:6; d:5;    a:5;    0:5;    oe:1;   234:9;  rc:1 }
    -> ADDMEx(d, a, oe, rc)
  | { 31:6; d:5;    a:5;    0:5;    oe:1;   202:9;  rc:1 }
    -> ADDZEx(d, a, oe, rc)
  | { 31:6; s:5;    a:5;    b:5;    28:10;  rc:1 }
    -> ANDx(s, a, b, rc)
  | { 31:6; s:5;    a:5;    b:5;    60:10;  rc:1 }
    -> ANDCx(s, a, b, rc)
  | { 28:6; s:5;    a:5;    uimm:16 }
    -> ANDI_(s, a, uimm)
  | { 29:6; s:5;    a:5;    uimm:16 }
    -> ANDIS_(s, a, uimm)
  | { 18:6; li:24:bitstring;  aa:1;   lk:1 }
    -> Bx(li, aa, lk)
  | { 16:6; bo:5:bitstring;   bi:5;   bd:14:bitstring;  aa:1;   lk:1 }
    -> BCx(bo, bi, bd, aa, lk)
  | { 19:6; bo:5:bitstring;   bi:5;   0:5;    528:10; lk:1 }
    -> BCCTRx(bo, bi, lk)
  | { 19:6; bo:5:bitstring;   bi:5;   0:5;    16:10;  lk:1 }
    -> BCLRx(bo, bi, lk)
  | { 31:6; crfD:3; false:1;    l:1;    a:5;    b:5;    0:10;   false:1 }
    -> CMP(crfD, l, a, b)
  | { 11:6; crfD:3; false:1;    l:1;    a:5;    simm:16:bitstring }
    -> CMPI(crfD, l, a, simm)
  | { 31:6; crfD:3; false:1;    l:1;    a:5;    b:5;    32:10;  false:1 }
    -> CMPL(crfD, l, a, b)
  | { 10:6; crfD:3; false:1;    l:1;    a:5;    uimm:16 }
    -> CMPLI(crfD, l, a, uimm)
  | { 31:6; s:5;    a:5;    0:5;    26:10;  rc:1 }
    -> CNTLZWx(s, a, rc)
  | { 19:6; crbD:5; crbA:5; crbB:5; 257:10; false:1 }
    -> CRAND(crbD, crbA, crbB)
  | { 19:6; crbD:5; crbA:5; crbB:5; 129:10; false:1 }
    -> CRANDC(crbD, crbA, crbB)
  | { 19:6; crbD:5; crbA:5; crbB:5; 289:10; false:1 }
    -> CREQV(crbD, crbA, crbB)
  | { 19:6; crbD:5; crbA:5; crbB:5; 225:10; false:1 }
    -> CRNAND(crbD, crbA, crbB)
  | { 19:6; crbD:5; crbA:5; crbB:5; 33:10;  false:1 }
    -> CRNOR(crbD, crbA, crbB)
  | { 19:6; crbD:5; crbA:5; crbB:5; 449:10; false:1 }
    -> CROR(crbD, crbA, crbB)
  | { 19:6; crbD:5; crbA:5; crbB:5; 417:10; false:1 }
    -> CRORC(crbD, crbA, crbB)
  | { 19:6; crbD:5; crbA:5; crbB:5; 193:10; false:1 }
    -> CRXOR(crbD, crbA, crbB)
  | { 31:6; 0:5;    a:5;    b:5;    758:10; false:1 }
    -> DCBA(a, b)
  | { 31:6; 0:5;    a:5;    b:5;    86:10;  false:1 }
    -> DCBF(a, b)
  | { 31:6; 0:5;    a:5;    b:5;    470:10; false:1 }
    -> DCBI(a, b)
  | { 31:6; 0:5;    a:5;    b:5;    54:10;  false:1 }
    -> DCBST(a, b)
  | { 31:6; 0:5;    a:5;    b:5;    278:10; false:1 }
    -> DCBT(a, b)
  | { 31:6; 0:5;    a:5;    b:5;    246:10; false:1 }
    -> DCBTST(a, b)
  | { 31:6; 0:5;    a:5;    b:5;    1014:10;    false:1 }
    -> DCBZ(a, b)
  | { 31:6; d:5;    a:5;    b:5;    oe:1;   491:9;  rc:1 }
    -> DIVWx(d, a, b, oe, rc)
  | { 31:6; d:5;    a:5;    b:5;    oe:1;   459:9;  rc:1 }
    -> DIVWUx(d, a, b, oe, rc)
  | { 31:6; d:5;    a:5;    b:5;    310:10;     false:1 }
    -> ECIWX(d, a, b)
  | { 31:6; s:5;    a:5;    b:5;    438:10; false:1 }
    -> ECOWX(s, a, b)
  | { 31:6; 0:5;    0:5;    0:5;    854:10; false:1 }
    -> EIEIO
  | { 31:6; s:5;    a:5;    b:5;    284:10; rc:1 }
    -> EQVx(s, a, b, rc)
  | { 31:6; s:5;    a:5;    0:5;    954:10; rc:1 }
    -> EXTSBx(s, a, rc)
  | { 31:6; s:5;    a:5;    0:5;    922:10; rc:1 }
    -> EXTSHx(s, a, rc)
  | { 63:6; d:5;    0:5;    b:5;    264:10; rc:1 }
    -> FABSx(d, b, rc)
  | { 63:6; d:5;    a:5;    b:5;    0:5;    21:5;   rc:1 }
    -> FADDx(d, a, b, rc)
  | { 59:6; d:5;    a:5;    b:5;    0:5;    21:5;   rc:1 }
    -> FADDSx(d, a, b, rc)
  | { 63:6; crfD:3; 0:2;    a:5;    b:5;    32:10;  false:1 }
    -> FCMPO(crfD, a, b)
  | { 63:6; crfD:3; 0:2;    a:5;    b:5;    0:10;   false:1 }
    -> FCMPU(crfD, a, b)
  | { 63:6; d:5;    0:5;    b:5;    14:10;  rc:1 }
    -> FCTIWx(d, b, rc)
  | { 63:6; d:5;    0:5;    b:5;    15:10;  rc:1 }
    -> FCTIWZx(d, b, rc)
  | { 63:6; d:5;    a:5;    b:5;    0:5;    18:5;   rc:1 }
    -> FDIVx(d, a, b, rc)
  | { 59:6; d:5;    a:5;    b:5;    0:5;    18:5;   rc:1 }
    -> FDIVSx(d, a, b, rc)
  | { 63:6; d:5;    a:5;    b:5;    c:5;    29:5;   rc:1 }
    -> FMADDx(d, a, b, c, rc)
  | { 59:6; d:5;    a:5;    b:5;    c:5;    29:5;   rc:1 }
    -> FMADDSx(d, a, b, c, rc)
  | { 63:6; d:5;    0:5;    b:5;    72:10;  rc:1 }
    -> FMRx(d, b, rc)
  | { 63:6; d:5;    a:5;    b:5;    c:5;    28:5;   rc:1 }
    -> FMSUBx(d, a, b, c, rc)
  | { 59:6; d:5;    a:5;    b:5;    c:5;    28:5;   rc:1 }
    -> FMSUBSx(d, a, b, c, rc)
  | { 63:6; d:5;    a:5;    0:5;    c:5;    25:5;   rc:1 }
    -> FMULx(d, a, c, rc)
  | { 59:6; d:5;    a:5;    0:5;    c:5;    25:5;   rc:1 }
    -> FMULSx(d, a, c, rc)
  | { 63:6; d:5;    0:5;    b:5;    136:10; rc:1 }
    -> FNABSx(d, b, rc)
  | { 63:6; d:5;    0:5;    b:5;    40:10;  rc:1 }
    -> FNEGx(d, b, rc)
  | { 63:6; d:5;    a:5;    b:5;    c:5;    31:5;   rc:1 }
    -> FNMADDx(d, a, b, c, rc)
  | { 59:6; d:5;    a:5;    b:5;    c:5;    31:5;   rc:1 }
    -> FNMADDSx(d, a, b, c, rc)
  | { 63:6; d:5;    a:5;    b:5;    c:5;    30:5;   rc:1 }
    -> FNMSUBx(d, a, b, c, rc)
  | { 59:6; d:5;    a:5;    b:5;    c:5;    30:5;   rc:1 }
    -> FNMSUBSx(d, a, b, c, rc)
  | { 59:6; d:5;    0:5;    b:5;    0:5;    24:5;   rc:1 }
    -> FRESx(d, b, rc)
  | { 63:6; d:5;    0:5;    b:5;    12:10;  rc:1 }
    -> FRSPx(d, b, rc)
  | { 63:6; d:5;    0:5;    b:5;    0:5;    26:5;   rc:1 }
    -> FRSQRTEx(d, b, rc)
  | { 63:6; d:5;    a:5;    b:5;    c:5;    23:5;   rc:1 }
    -> FSELx(d, a, b, c, rc)
  | { 63:6; d:5;    0:5;    b:5;    0:5;    22:5;   rc:1 }
    -> FSQRTx(d, b, rc)
  | { 59:6; d:5;    0:5;    b:5;    0:5;    22:5;   rc:1 }
    -> FSQRTSx(d, b, rc)
  | { 63:6; d:5;    a:5;    b:5;    0:5;    20:5;   rc:1 }
    -> FSUBx(d, a, b, rc)
  | { 59:6; d:5;    a:5;    b:5;    0:5;    20:5;   rc:1 }
    -> FSUBSx(d, a, b, rc)
  | { 31:6; 0:5;    a:5;    b:5;    982:10; false:1 }
    -> ICBI(a, b)
  | { 19:6; 0:5;    0:5;    0:5;    150:10; false:1 }
    -> ISYNC
  | { 34:6; d:5;    a:5;    dd:16:bitstring }
    -> LBZ(d, a, dd)
  | { 35:6; d:5;    a:5;    dd:16:bitstring }
    -> LBZU(d, a, dd)
  | { 31:6; d:5;    a:5;    b:5;    119:10; false:1 }
    -> LBZUX(d, a, b)
  | { 31:6; d:5;    a:5;    b:5;    87:10;  false:1 }
    -> LBZX(d, a, b)
  | { 50:6; d:5;    a:5;    dd:16:bitstring }
    -> LFD(d, a, dd)
  | { 51:6; d:5;    a:5;    dd:16:bitstring }
    -> LFDU(d, a, dd)
  | { 31:6; d:5;    a:5;    b:5;    631:10; false:1 }
    -> LFDUX(d, a, b)
  | { 31:6; d:5;    a:5;    b:5;    599:10; false:1 }
    -> LFDX(d, a, b)
  | { 48:6; d:5;    a:5;    dd:16:bitstring }
    -> LFS(d, a, dd)
  | { 49:6; d:5;    a:5;    dd:16:bitstring }
    -> LFSU(d, a, dd)
  | { 31:6; d:5;    a:5;    b:5;    567:10; false:1 }
    -> LFSUX(d, a, b)
  | { 31:6; d:5;    a:5;    b:5;    535:10; false:1 }
    -> LFSX(d, a, b)
  | { 42:6; d:5;    a:5;    dd:16:bitstring }
    -> LHA(d, a, dd)
  | { 43:6; d:5;    a:5;    dd:16:bitstring }
    -> LHAU(d, a, dd)
  | { 31:6; d:5;    a:5;    b:5;    375:10; false:1 }
    -> LHAUX(d, a, b)
  | { 31:6; d:5;    a:5;    b:5;    343:10; false:1 }
    -> LHAX(d, a, b)
  | { 31:6; d:5;    a:5;    b:5;    790:10; false:1 }
    -> LHBRX(d, a, b)
  | { 40:6; d:5;    a:5;    dd:16:bitstring }
    -> LHZ(d, a, dd)
  | { 41:6; d:5;    a:5;    dd:16:bitstring }
    -> LHZU(d, a, dd)
  | { 31:6; d:5;    a:5;    b:5;    311:10; false:1 }
    -> LHZUX(d, a, b)
  | { 31:6; d:5;    a:5;    b:5;    279:10; false:1 }
    -> LHZX(d, a, b)
  | { 46:6; d:5;    a:5;    dd:16 }
    -> LMW(d, a, dd)
  | { 31:6; d:5;    a:5;    nb:5;   597:10; false:1 }
    -> LSWI(d, a, nb)
  | { 31:6; d:5;    a:5;    b:5;    533:10; false:1 }
    -> LSWX(d, a, b)
  | { 31:6; d:5;    a:5;    b:5;    20:10;  false:1 }
    -> LWARX(d, a, b)
  | { 31:6; d:5;    a:5;    b:5;    534:10; false:1 }
    -> LWBRX(d, a, b)
  | { 32:6; d:5;    a:5;    dd:16:bitstring }
    -> LWZ(d, a, dd)
  | { 33:6; d:5;    a:5;    dd:16:bitstring }
    -> LWZU(d, a, dd)
  | { 31:6; d:5;    a:5;    b:5;    55:10;  false:1 }
    -> LWZUX(d, a, b)
  | { 31:6; d:5;    a:5;    b:5;    23:10;  false:1 }
    -> LWZX(d, a, b)
  | { 19:6; crfD:3; 0:2;    crfS:3; 0:2;    0:5;    0:10;   false:1 }
    -> MCRF(crfD, crfS)
  | { 63:6; crfD:3; 0:2;    crfS:3; 0:2;    0:5;    64:10;  false:1 }
    -> MCRFS(crfD, crfS)
  | { 31:6; crfD:3; 0:2;    0:5;    0:5;    0:10;   false:1 }
    -> MCRXR(crfD)
  | { 31:6; d:5;    0:5;    0:5;    19:10;  false:1 }
    -> MFCR(d)
  | { 63:6; d:5;    0:5;    0:5;    583:10; rc:1 }
    -> MFFSx(d, rc)
  | { 31:6; d:5;    0:5;    0:5;    83:10;  false:1 }
    -> MFMSR(d)
  | { 31:6; d:5;    spr:10:bitstring; 339:10; false:1 }
    -> MFSPR(d, spr)
  | { 31:6; d:5;    false:1;    sr:4;   0:5;    595:10; false:1 }
    -> MFSR(d, sr)
  | { 31:6; d:5;    0:5;    b:5;    659:10; false:1 }
    -> MFSRIN(d, b)
  | { 31:6; d:5;    tbr:10; 371:10; false:1 }
    -> MFTB(d, tbr)
  | { 31:6; s:5;    false:1;    crm:8;  false:1;    144:10; false:1 }
    -> MTCRF(s, crm)
  | { 63:6; crbD:5; 0:5;    0:5;    70:10;  rc:1 }
    -> MTFSB0x(crbD, rc)
  | { 63:6; crbD:5; 0:5;    0:5;    38:10;  rc:1 }
    -> MTFSB1x(crbD, rc)
  | { 63:6; false:1;    fm:8;   false:1;    b:5;    711:10; rc:1 }
    -> MTFSF(fm, b, rc)
  | { 63:6; crfD:3; 0:2;    0:5;    imm:4;  false:1;    134:10; rc:1 }
    -> MTFSFIx(crfD, imm, rc)
  | { 31:6; s:5;    0:5;    0:5;    146:10; false:1 }
    -> MTMSR(s)
  | { 31:6; s:5;    spr:10:bitstring; 467:10; false:1 }
    -> MTSPR(s, spr)
  | { 31:6; s:5;    false:1;    sr:4;   0:5;    210:10; false:1 }
    -> MTSR(s, sr)
  | { 31:6; s:5;    0:5;    b:5;    242:10; false:1 }
    -> MTSRIN(s, b)
  | { 31:6; d:5;    a:5;    b:5;    false:1;    75:9;   rc:1 }
    -> MULHWx(d, a, b, rc)
  | { 31:6; d:5;    a:5;    b:5;    false:1;    11:9;   rc:1 }
    -> MULHWUx(d, a, b, rc)
  | { 7:6; d:5; a:5;    simm:16:bitstring }
    -> MULLI(d, a, simm)
  | { 31:6; id:5;   a:5;    b:5;    oe:1;   235:9;  rc:1 }
    -> MULLWx(id, a, b, oe, rc)
  | { 31:6; s:5;    a:5;    b:5;    476:10; rc:1 }
    -> NANDx(s, a, b, rc)
  | { 31:6; d:5;    a:5;    0:5;    oe:1;   104:9;  rc:1 }
    -> NEGx(d, a, oe, rc)
  | { 31:6; s:5;    a:5;    b:5;    124:10; rc:1 }
    -> NORx(s, a, b, rc)
  | { 31:6; s:5;    a:5;    b:5;    444:10; rc:1 }
    -> ORx(s, a, b, rc)
  | { 31:6; s:5;    a:5;    b:5;    412:10; rc:1 }
    -> ORCx(s, a, b, rc)
  | { 24:6; s:5;    a:5;    uimm:16 }
    -> ORI(s, a, uimm)
  | { 25:6; s:5;    a:5;    uimm:16 }
    -> ORIS(s, a, uimm)
  | { 19:6; 0:5;    0:5;    0:5;    50:10;  false:1 }
    -> RFI
  | { 20:6; s:5;    a:5;    sh:5;   mb:5;   me:5;   rc:1 }
    -> RLWIMIx(s, a, sh, mb, me, rc)
  | { 21:6; s:5;    a:5;    sh:5;   mb:5;   me:5;   rc:1 }
    -> RLWINMx(s, a, sh, mb, me, rc)
  | { 23:6; s:5;    a:5;    b:5;    mb:5;   me:5;   rc:1 }
    -> RLWNMx(s, a, b, mb, me, rc)
  | { 17:6; 0:5;    0:5;    0:14;   true:1; false:1 }
    -> SC
  | { 31:6; s:5;    a:5;    b:5;    24:10;  rc:1 }
    -> SLWx(s, a, b, rc)
  | { 31:6; s:5;    a:5;    b:5;    792:10; rc:1 }
    -> SRAWx(s, a, b, rc)
  | { 31:6; s:5;    a:5;    sh:5;   824:10; rc:1 }
    -> SRAWIx(s, a, sh, rc)
  | { 31:6; s:5;    a:5;    b:5;    536:10; rc:1 }
    -> SRWx(s, a, b, rc)
  | { 38:6; s:5;    a:5;    dd:16:bitstring }
    -> STB(s, a, dd)
  | { 39:6; s:5;    a:5;    dd:16:bitstring }
    -> STBU(s, a, dd)
  | { 31:6; s:5;    a:5;    b:5;    247:10; false:1 }
    -> STBUX(s, a, b)
  | { 31:6; s:5;    a:5;    b:5;    215:10; false:1 }
    -> STBX(s, a, b)
  | { 54:6; s:5;    a:5;    dd:16:bitstring }
    -> STFD(s, a, dd)
  | { 55:6; s:5;    a:5;    dd:16:bitstring }
    -> STFDU(s, a, dd)
  | { 31:6; s:5;    a:5;    b:5;    759:10; false:1 }
    -> STFDUX(s, a, b)
  | { 31:6; s:5;    a:5;    b:5;    727:10; false:1 }
    -> STFDX(s, a, b)
  | { 31:6; s:5;    a:5;    b:5;    983:10; false:1 }
    -> STFIWX(s, a, b)
  | { 52:6; s:5;    a:5;    dd:16:bitstring }
    -> STFS(s, a, dd)
  | { 53:6; s:5;    a:5;    dd:16:bitstring }
    -> STFSU(s, a, dd)
  | { 31:6; s:5;    a:5;    b:5;    695:10; false:1 }
    -> STFSUX(s, a, b)
  | { 31:6; s:5;    a:5;    b:5;    663:10; false:1 }
    -> STFSX(s, a, b)
  | { 44:6; s:5;    a:5;    dd:16:bitstring }
    -> STH(s, a, dd)
  | { 31:6; s:5;    a:5;    b:5;    918:10; false:1 }
    -> STHBRX(s, a, b)
  | { 45:6; s:5;    a:5;    dd:16:bitstring }
    -> STHU(s, a, dd)
  | { 31:6; s:5;    a:5;    b:5;    439:10; false:1 }
    -> STHUX(s, a, b)
  | { 31:6; s:5;    a:5;    b:5;    407:10; false:1 }
    -> STHX(s, a, b)
  | { 47:6; s:5;    a:5;    dd:16 }
    -> STMW(s, a, dd)
  | { 31:6; s:5;    a:5;    nb:5;   725:10; false:1 }
    -> STSWI(s, a, nb)
  | { 31:6; s:5;    a:5;    b:5;    661:10; false:1 }
    -> STSWX(s, a, b)
  | { 36:6; s:5;    a:5;    dd:16:bitstring }
    -> STW(s, a, dd)
  | { 31:6; s:5;    a:5;    b:5;    662:10; false:1 }
    -> STWBRX(s, a, b)
  | { 31:6; s:5;    a:5;    b:5;    150:10; false:1 }
    -> STWCX_(s, a, b)
  | { 37:6; s:5;    a:5;    dd:16:bitstring }
    -> STWU(s, a, dd)
  | { 31:6; s:5;    a:5;    b:5;    183:10; false:1 }
    -> STWUX(s, a, b)
  | { 31:6; s:5;    a:5;    b:5;    151:10; false:1 }
    -> STWX(s, a, b)
  | { 31:6; d:5;    a:5;    b:5;    oe:1;   40:9;   rc:1 }
    -> SUBFx(d, a, b, oe, rc)
  | { 31:6; d:5;    a:5;    b:5;    oe:1;   8:9;    rc:1 }
    -> SUBFCx(d, a, b, oe, rc)
  | { 31:6; d:5;    a:5;    b:5;    oe:1;   136:9;  rc:1 }
    -> SUBFEx(d, a, b, oe, rc)
  | { 8:6; d:5; a:5;    simm:16:bitstring }
    -> SUBFIC(d, a, simm)
  | { 31:6; d:5;    a:5;    0:5;    oe:1;   232:9;  rc:1 }
    -> SUBFMEx(d, a, oe, rc)
  | { 31:6; d:5;    a:5;    0:5;    oe:1;   200:9;  rc:1 }
    -> SUBFZEx(d, a, oe, rc)
  | { 31:6; 0:5;    0:5;    0:5;    598:10; false:1 }
    -> SYNC
  | { 31:6; 0:5;    0:5;    0:5;    370:10; false:1 }
    -> TLBIA
  | { 31:6; 0:5;    0:5;    b:5;    306:10; false:1 }
    -> TLBIE(b)
  | { 31:6; 0:5;    0:5;    0:5;    566:10; false:1 }
    -> TLBSYNC
  | { 31:6; t:5:bitstring;  a:5;    b:5;    4:10;   false:1 }
    -> TW(t, a, b)
  | { 3:6;  t:5:bitstring;  a:5;    simm:16 }
    -> TWI(t, a, simm)
  | { 31:6; s:5;    a:5;    b:5;    316:10; rc:1 }
    -> XORx(s, a, b, rc)
  | { 26:6; s:5;    a:5;    uimm:16 }
    -> XORI(s, a, uimm)
  | { 27:6; s:5;    a:5;    uimm:16 }
    -> XORIS(s, a, uimm)
  | { bits:32:bitstring }
    -> UNKNOWN(bits)

let rec parse_code_as_list bs =
  bitmatch bs with
  | { instr:32:bitstring; rest:-1:bitstring } ->
      parse_instr instr :: parse_code_as_list rest
  | { rest:-1:bitstring } ->
      if Bitstring.bitstring_length rest = 0
      then []
      else assert false

let parse_nth_instr bs n = parse_instr (Bitstring.subbitstring bs (n * 32) 32)

let parse_code_as_array (bs: bitstring) (num: int): instr array =
  Array.init num (parse_nth_instr bs)
