open Library

type eireg = int
type efreg = int

type instr =
| ADDx      of eireg * eireg * eireg * bool * bool
| ADDCx     of eireg * eireg * eireg * bool * bool
| ADDEx     of eireg * eireg * eireg * bool * bool
| ADDI      of eireg * eireg * bitstring
| ADDIC     of eireg * eireg * bitstring
| ADDIC_    of eireg * eireg * bitstring
| ADDIS     of eireg * eireg * int
| ADDMEx    of eireg * eireg * bool * bool
| ADDZEx    of eireg * eireg * bool * bool
| ANDx      of eireg * eireg * eireg * bool
| ANDCx     of eireg * eireg * eireg * bool
| ANDI_     of eireg * eireg * int
| ANDIS_    of eireg * eireg * int
| Bx        of bitstring * bool * bool
| BCx       of bitstring * int * bitstring * bool * bool
| BCCTRx    of bitstring * int * bool
| BCLRx     of bitstring * int * bool
| CMP       of int * bool * eireg * eireg
| CMPI      of int * bool * eireg * bitstring
| CMPL      of int * bool * eireg * eireg
| CMPLI     of int * bool * eireg * int
| CNTLZWx   of eireg * eireg * bool
| CRAND     of int * int * int
| CRANDC    of int * int * int
| CREQV     of int * int * int
| CRNAND    of int * int * int
| CRNOR     of int * int * int
| CROR      of int * int * int
| CRORC     of int * int * int
| CRXOR     of int * int * int
| DCBA      of eireg * eireg
| DCBF      of eireg * eireg
| DCBI      of eireg * eireg
| DCBST     of eireg * eireg
| DCBT      of eireg * eireg
| DCBTST    of eireg * eireg
| DCBZ      of eireg * eireg
| DIVWx     of eireg * eireg * eireg * bool * bool
| DIVWUx    of eireg * eireg * eireg * bool * bool
| ECIWX     of eireg * eireg * eireg
| ECOWX     of eireg * eireg * eireg
| EIEIO
| EQVx      of eireg * eireg * eireg * bool
| EXTSBx    of eireg * eireg * bool
| EXTSHx    of eireg * eireg * bool
| FABSx     of efreg * efreg * bool
| FADDx     of efreg * efreg * efreg * bool
| FADDSx    of efreg * efreg * efreg * bool
| FCMPO     of int * efreg * efreg
| FCMPU     of int * efreg * efreg
| FCTIWx    of efreg * efreg * bool
| FCTIWZx   of efreg * efreg * bool
| FDIVx     of efreg * efreg * efreg * bool
| FDIVSx    of efreg * efreg * efreg * bool
| FMADDx    of efreg * efreg * efreg * efreg * bool
| FMADDSx   of efreg * efreg * efreg * efreg * bool
| FMRx      of efreg * efreg * bool
| FMSUBx    of efreg * efreg * efreg * efreg * bool
| FMSUBSx   of efreg * efreg * efreg * efreg * bool
| FMULx     of efreg * efreg * efreg * bool
| FMULSx    of efreg * efreg * efreg * bool
| FNABSx    of efreg * efreg * bool
| FNEGx     of efreg * efreg * bool
| FNMADDx   of efreg * efreg * efreg * efreg * bool
| FNMADDSx  of efreg * efreg * efreg * efreg * bool
| FNMSUBx   of efreg * efreg * efreg * efreg * bool
| FNMSUBSx  of efreg * efreg * efreg * efreg * bool
| FRESx     of efreg * efreg * bool
| FRSPx     of efreg * efreg * bool
| FRSQRTEx  of efreg * efreg * bool
| FSELx     of efreg * efreg * efreg * efreg * bool
| FSQRTx    of efreg * efreg * bool
| FSQRTSx   of efreg * efreg * bool
| FSUBx     of efreg * efreg * efreg * bool
| FSUBSx    of efreg * efreg * efreg * bool
| ICBI      of eireg * eireg
| ISYNC
| LBZ       of eireg * eireg * bitstring
| LBZU      of eireg * eireg * bitstring
| LBZUX     of eireg * eireg * eireg
| LBZX      of eireg * eireg * eireg
| LFD       of efreg * eireg * bitstring
| LFDU      of efreg * eireg * bitstring
| LFDUX     of efreg * eireg * eireg
| LFDX      of efreg * eireg * eireg
| LFS       of efreg * eireg * bitstring
| LFSU      of efreg * eireg * bitstring
| LFSUX     of efreg * eireg * eireg
| LFSX      of efreg * eireg * eireg
| LHA       of eireg * eireg * bitstring
| LHAU      of eireg * eireg * bitstring
| LHAUX     of eireg * eireg * eireg
| LHAX      of eireg * eireg * eireg
| LHBRX     of eireg * eireg * eireg
| LHZ       of eireg * eireg * bitstring
| LHZU      of eireg * eireg * bitstring
| LHZUX     of eireg * eireg * eireg
| LHZX      of eireg * eireg * eireg
| LMW       of eireg * eireg * int
| LSWI      of eireg * eireg * eireg
| LSWX      of eireg * eireg * eireg
| LWARX     of eireg * eireg * eireg
| LWBRX     of eireg * eireg * eireg
| LWZ       of eireg * eireg * bitstring
| LWZU      of eireg * eireg * bitstring
| LWZUX     of eireg * eireg * eireg
| LWZX      of eireg * eireg * eireg
| MCRF      of int * int
| MCRFS     of int * int
| MCRXR     of int
| MFCR      of eireg
| MFFSx     of efreg * bool
| MFMSR     of eireg
| MFSPR     of eireg * bitstring
| MFSR      of eireg * int
| MFSRIN    of eireg * eireg
| MFTB      of eireg * int
| MTCRF     of eireg * int
| MTFSB0x   of int * bool
| MTFSB1x   of int * bool
| MTFSF     of int * efreg * bool
| MTFSFIx   of int * int * bool
| MTMSR     of eireg
| MTSPR     of eireg * bitstring
| MTSR      of eireg * int
| MTSRIN    of eireg * eireg
| MULHWx    of eireg * eireg * eireg * bool
| MULHWUx   of eireg * eireg * eireg * bool
| MULLI     of eireg * eireg * bitstring
| MULLWx    of eireg * eireg * eireg * bool * bool
| NANDx     of eireg * eireg * eireg * bool
| NEGx      of eireg * eireg * bool * bool
| NORx      of eireg * eireg * eireg * bool
| ORx       of eireg * eireg * eireg * bool
| ORCx      of eireg * eireg * eireg * bool
| ORI       of eireg * eireg * int
| ORIS      of eireg * eireg * int
| RFI
| RLWIMIx   of eireg * eireg * int * int * int * bool
| RLWINMx   of eireg * eireg * int * int * int * bool
| RLWNMx    of eireg * eireg * eireg * int * int * bool
| SC
| SLWx      of eireg * eireg * eireg * bool
| SRAWx     of eireg * eireg * eireg * bool
| SRAWIx    of eireg * eireg * int * bool
| SRWx      of eireg * eireg * eireg * bool
| STB       of eireg * eireg * bitstring
| STBU      of eireg * eireg * bitstring
| STBUX     of eireg * eireg * eireg
| STBX      of eireg * eireg * eireg
| STFD      of efreg * eireg * bitstring
| STFDU     of efreg * eireg * bitstring
| STFDUX    of efreg * eireg * eireg
| STFDX     of efreg * eireg * eireg
| STFIWX    of eireg * eireg * eireg
| STFS      of efreg * eireg * bitstring
| STFSU     of efreg * eireg * bitstring
| STFSUX    of efreg * eireg * eireg
| STFSX     of efreg * eireg * eireg
| STH       of eireg * eireg * bitstring
| STHBRX    of eireg * eireg * eireg
| STHU      of eireg * eireg * bitstring
| STHUX     of eireg * eireg * eireg
| STHX      of eireg * eireg * eireg
| STMW      of eireg * eireg * int
| STSWI     of eireg * eireg * eireg
| STSWX     of eireg * eireg * eireg
| STW       of eireg * eireg * bitstring
| STWBRX    of eireg * eireg * eireg
| STWCX_    of eireg * eireg * eireg
| STWU      of eireg * eireg * bitstring
| STWUX     of eireg * eireg * eireg
| STWX      of eireg * eireg * eireg
| SUBFx     of eireg * eireg * eireg * bool * bool
| SUBFCx    of eireg * eireg * eireg * bool * bool
| SUBFEx    of eireg * eireg * eireg * bool * bool
| SUBFIC    of eireg * eireg * bitstring
| SUBFMEx   of eireg * eireg * bool * bool
| SUBFZEx   of eireg * eireg * bool * bool
| SYNC
| TLBIA
| TLBIE     of eireg
| TLBSYNC
| TW        of bitstring * eireg * eireg
| TWI       of bitstring * eireg * int
| XORx      of eireg * eireg * eireg * bool
| XORI      of eireg * eireg * int
| XORIS     of eireg * eireg * int
| UNKNOWN   of bitstring

(* ELF parsed code *)
type ecode = instr list
