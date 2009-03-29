(* MODIF: Loop constructor replaced by 3 constructors: While, DoWhile, For. *)
(* MODIF: useLogicalOperators flag set to true by default. *)

(*
 *
 * Copyright (c) 2001-2003,
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  Ben Liblit          <liblit@cs.berkeley.edu>
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

open Escape
open Pretty
open Trace      (* sm: 'trace' function *)
module E = Errormsg
module H = Hashtbl
module IH = Inthash

(*
 * CIL: An intermediate language for analyzing C progams.
 *
 * Version Tue Dec 12 15:21:52 PST 2000 
 * Scott McPeak, George Necula, Wes Weimer
 *
 *)

(* The module Cilversion is generated automatically by Makefile from 
 * information in configure.in *)
let cilVersion         = Cilversion.cilVersion
let cilVersionMajor    = Cilversion.cilVersionMajor
let cilVersionMinor    = Cilversion.cilVersionMinor
let cilVersionRevision = Cilversion.cilVersionRev

(* A few globals that control the interpretation of C source *)
let msvcMode = ref false              (* Whether the pretty printer should 
                                       * print output for the MS VC 
                                       * compiler. Default is GCC *)

let useLogicalOperators = ref (*false*) true


module M = Machdep
(* Cil.initCil will set this to the current machine description.
   Makefile.cil generates the file obj/@ARCHOS@/machdep.ml,
   which contains the descriptions of gcc and msvc. *)
let theMachine : M.mach ref = ref M.gcc


let lowerConstants: bool ref = ref true
    (** Do lower constants (default true) *)
let insertImplicitCasts: bool ref = ref true
    (** Do insert implicit casts (default true) *)


let little_endian = ref true
let char_is_unsigned = ref false
let underscore_name = ref false

type lineDirectiveStyle =
  | LineComment
  | LinePreprocessorInput
  | LinePreprocessorOutput

let lineDirectiveStyle = ref (Some LinePreprocessorInput)
 
let print_CIL_Input = ref false
           
let printCilAsIs = ref false

let lineLength = ref 80
                      
(* sm: return the string 's' if we're printing output for gcc, suppres
 * it if we're printing for CIL to parse back in.  the purpose is to
 * hide things from gcc that it complains about, but still be able
 * to do lossless transformations when CIL is the consumer *)
let forgcc (s: string) : string =
  if (!print_CIL_Input) then "" else s


let debugConstFold = false

(** The Abstract Syntax of CIL *)


(** The top-level representation of a CIL source file. Its main contents is 
    the list of global declarations and definitions. *)
type file = 
    { mutable fileName: string;   (** The complete file name *)
      mutable globals: global list; (** List of globals as they will appear 
                                        in the printed file *)
      mutable globinit: fundec option;  
      (** An optional global initializer function. This is a function where 
       * you can put stuff that must be executed before the program is 
       * started. This function, is conceptually at the end of the file, 
       * although it is not part of the globals list. Use {!Cil.getGlobInit} 
       * to create/get one. *)
      mutable globinitcalled: bool;     
      (** Whether the global initialization function is called in main. This 
          should always be false if there is no global initializer. When 
          you create a global initialization CIL will try to insert code in 
          main to call it. *)
    } 

and comment = location * string

(** The main type for representing global declarations and definitions. A list 
    of these form a CIL file. The order of globals in the file is generally 
    important. *)
and global =
  | GType of typeinfo * location    
    (** A typedef. All uses of type names (through the [TNamed] constructor) 
        must be preceeded in the file by a definition of the name. The string 
        is the defined name and always not-empty. *)

  | GCompTag of compinfo * location     
    (** Defines a struct/union tag with some fields. There must be one of 
        these for each struct/union tag that you use (through the [TComp] 
        constructor) since this is the only context in which the fields are 
        printed. Consequently nested structure tag definitions must be 
        broken into individual definitions with the innermost structure 
        defined first. *)

  | GCompTagDecl of compinfo * location
    (** Declares a struct/union tag. Use as a forward declaration. This is 
      * printed without the fields.  *)

  | GEnumTag of enuminfo * location
   (** Declares an enumeration tag with some fields. There must be one of 
      these for each enumeration tag that you use (through the [TEnum] 
      constructor) since this is the only context in which the items are 
      printed. *)

  | GEnumTagDecl of enuminfo * location
    (** Declares an enumeration tag. Use as a forward declaration. This is 
      * printed without the items.  *)

  | GVarDecl of varinfo * location
   (** A variable declaration (not a definition). If the variable has a 
       function type then this is a prototype. There can be several 
       declarations and at most one definition for a given variable. If both 
       forms appear then they must share the same varinfo structure. A 
       prototype shares the varinfo with the fundec of the definition. Either 
       has storage Extern or there must be a definition in this file *)

  | GVar  of varinfo * initinfo * location
     (** A variable definition. Can have an initializer. The initializer is 
      * updateable so that you can change it without requiring to recreate 
      * the list of globals. There can be at most one definition for a 
      * variable in an entire program. Cannot have storage Extern or function 
      * type. *)


  | GFun of fundec * location           
     (** A function definition. *)

  | GAsm of string * location           (** Global asm statement. These ones 
                                            can contain only a template *)
  | GPragma of attribute * location     (** Pragmas at top level. Use the same 
                                            syntax as attributes *)
  | GText of string                     (** Some text (printed verbatim) at 
                                            top level. E.g., this way you can 
                                            put comments in the output.  *)


(** The various types available. Every type is associated with a list of 
 * attributes, which are always kept in sorted order. Use {!Cil.addAttribute} 
 * and {!Cil.addAttributes} to construct list of attributes. If you want to 
 * inspect a type, you should use {!Cil.unrollType} to see through the uses 
 * of named types. *)
and typ =
    TVoid of attributes   (** Void type *)
  | TInt of ikind * attributes (** An integer type. The kind specifies 
                                       the sign and width. *)
  | TFloat of fkind * attributes (** A floating-point type. The kind 
                                         specifies the precision. *)

  | TPtr of typ * attributes  
           (** Pointer type. *)

  | TArray of typ * exp option * attributes
           (** Array type. It indicates the base type and the array length. *)

  | TFun of typ * (string * typ * attributes) list option * bool * attributes
          (** Function type. Indicates the type of the result, the name, type 
           * and name attributes of the formal arguments ([None] if no 
           * arguments were specified, as in a function whose definition or 
           * prototype we have not seen; [Some \[\]] means void). Use 
           * {!Cil.argsToList} to obtain a list of arguments. The boolean 
           * indicates if it is a variable-argument function. If this is the 
           * type of a varinfo for which we have a function declaration then 
           * the information for the formals must match that in the 
           * function's sformals. *)

  | TNamed of typeinfo * attributes 
          (* The use of a named type. All uses of the same type name must 
           * share the typeinfo. Each such type name must be preceeded 
           * in the file by a [GType] global. This is printed as just the 
           * type name. The actual referred type is not printed here and is 
           * carried only to simplify processing. To see through a sequence 
           * of named type references, use {!Cil.unrollType}. The attributes 
           * are in addition to those given when the type name was defined. *)

  | TComp of compinfo * attributes
          (** A reference to a struct or a union type. All references to the 
             same struct or union must share the same compinfo among them and 
             with a [GCompTag] global that preceeds all uses (except maybe 
             those that are pointers to the composite type). The attributes 
             given are those pertaining to this use of the type and are in 
             addition to the attributes that were given at the definition of 
             the type and which are stored in the compinfo.  *)

  | TEnum of enuminfo * attributes
           (** A reference to an enumeration type. All such references must
               share the enuminfo among them and with a [GEnumTag] global that 
               preceeds all uses. The attributes refer to this use of the 
               enumeration and are in addition to the attributes of the 
               enumeration itself, which are stored inside the enuminfo  *)


  
  | TBuiltin_va_list of attributes
            (** This is the same as the gcc's type with the same name *)

(** Various kinds of integers *)
and ikind = 
    IChar       (** [char] *)
  | ISChar      (** [signed char] *)
  | IUChar      (** [unsigned char] *)
  | IInt        (** [int] *)
  | IUInt       (** [unsigned int] *)
  | IShort      (** [short] *)
  | IUShort     (** [unsigned short] *)
  | ILong       (** [long] *)
  | IULong      (** [unsigned long] *)
  | ILongLong   (** [long long] (or [_int64] on Microsoft Visual C) *)
  | IULongLong  (** [unsigned long long] (or [unsigned _int64] on Microsoft 
                    Visual C) *)

(** Various kinds of floating-point numbers*)
and fkind = 
    FFloat      (** [float] *)
  | FDouble     (** [double] *)
  | FLongDouble (** [long double] *)

(** An attribute has a name and some optional parameters *)
and attribute = Attr of string * attrparam list

(** Attributes are lists sorted by the attribute name *)
and attributes = attribute list

(** The type of parameters in attributes *)
and attrparam = 
  | AInt of int                          (** An integer constant *)
  | AStr of string                       (** A string constant *)
  | ACons of string * attrparam list       (** Constructed attributes. These 
                                             are printed [foo(a1,a2,...,an)]. 
                                             The list of parameters can be 
                                             empty and in that case the 
                                             parentheses are not printed. *)
  | ASizeOf of typ                       (** A way to talk about types *)
  | ASizeOfE of attrparam
  | ASizeOfS of typsig                   (** Replacement for ASizeOf in type
                                             signatures.  Only used for
                                             attributes inside typsigs.*)
  | AAlignOf of typ
  | AAlignOfE of attrparam
  | AAlignOfS of typsig
  | AUnOp of unop * attrparam
  | ABinOp of binop * attrparam * attrparam
  | ADot of attrparam * string           (** a.foo **)


(** Information about a composite type (a struct or a union). Use 
    {!Cil.mkCompInfo} 
    to create non-recursive or (potentially) recursive versions of this. Make 
    sure you have a [GCompTag] for each one of these.  *)
and compinfo = {
    mutable cstruct: bool;              (** True if struct, False if union *)
    mutable cname: string;              (** The name. Always non-empty. Use 
                                         * {!Cil.compFullName} to get the 
                                         * full name of a comp (along with 
                                         * the struct or union) *)
    mutable ckey: int;                  (** A unique integer constructed from 
                                         * the name. Use {!Hashtbl.hash} on 
                                         * the string returned by 
                                         * {!Cil.compFullName}. All compinfo 
                                         * for a given key are shared. *)
    mutable cfields: fieldinfo list;    (** Information about the fields *) 
    mutable cattr:   attributes;        (** The attributes that are defined at
                                            the same time as the composite
                                            type *)
    mutable cdefined: bool;             (** Whether this is a defined 
                                         * compinfo. *)
    mutable creferenced: bool;          (** True if used. Initially set to 
                                         * false *)
  }

(** Information about a struct/union field *)
and fieldinfo = { 
    mutable fcomp: compinfo;            (** The compinfo of the host. Note 
                                            that this must be shared with the 
                                            host since there can be only one 
                                            compinfo for a given id *)
    mutable fname: string;              (** The name of the field. Might be 
                                         * the value of 
                                         * {!Cil.missingFieldName} in which 
                                         * case it must be a bitfield and is 
                                         * not printed and it does not 
                                         * participate in initialization *)
    mutable ftype: typ;                 (** The type *)
    mutable fbitfield: int option;      (** If a bitfield then ftype should be 
                                            an integer type *)
    mutable fattr: attributes;          (** The attributes for this field 
                                          * (not for its type) *)
    mutable floc: location;             (** The location where this field
                                          * is defined *)
}



(** Information about an enumeration. This is shared by all references to an
    enumeration. Make sure you have a [GEnumTag] for each of of these.   *)
and enuminfo = {
    mutable ename: string;              (** The name. Always non-empty *)
    mutable eitems: (string * exp * location) list; (** Items with names
                                                      and values. This list
                                                      should be
                                                      non-empty. The item
                                                      values must be
                                                      compile-time
                                                      constants. *) 
    mutable eattr: attributes;         (** Attributes *)
    mutable ereferenced: bool;         (** True if used. Initially set to false*)
}

(** Information about a defined type *)
and typeinfo = {
    mutable tname: string;              
    (** The name. Can be empty only in a [GType] when introducing a composite 
     * or enumeration tag. If empty cannot be refered to from the file *)
    mutable ttype: typ;
    (** The actual type. *)
    mutable treferenced: bool;         
    (** True if used. Initially set to false*)
}


(** Information about a variable. These structures are shared by all 
 * references to the variable. So, you can change the name easily, for 
 * example. Use one of the {!Cil.makeLocalVar}, {!Cil.makeTempVar} or 
 * {!Cil.makeGlobalVar} to create instances of this data structure. *)
and varinfo = { 
    mutable vname: string;		(** The name of the variable. Cannot 
                                          * be empty. *)
    mutable vtype: typ;                 (** The declared type of the 
                                          * variable. *)
    mutable vattr: attributes;          (** A list of attributes associated 
                                          * with the variable. *)
    mutable vstorage: storage;          (** The storage-class *)
    (* The other fields are not used in varinfo when they appear in the formal 
     * argument list in a [TFun] type *)


    mutable vglob: bool;	        (** True if this is a global variable*)

    (** Whether this varinfo is for an inline function. *)
    mutable vinline: bool;

    mutable vdecl: location;            (** Location of variable declaration *)

    mutable vid: int;  (** A unique integer identifier.  *)
    mutable vaddrof: bool;              (** True if the address of this
                                            variable is taken. CIL will set 
                                         * these flags when it parses C, but 
                                         * you should make sure to set the 
                                         * flag whenever your transformation 
                                         * create [AddrOf] expression. *)

    mutable vreferenced: bool;          (** True if this variable is ever 
                                            referenced. This is computed by 
                                            [removeUnusedVars]. It is safe to 
                                            just initialize this to False *)
}

(** Storage-class information *)
and storage = 
    NoStorage |                         (** The default storage. Nothing is 
                                         * printed  *)
    Static |                           
    Register |                          
    Extern                              


(** Expressions (Side-effect free)*)
and exp =
    Const      of constant              (** Constant *)
  | Lval       of lval                  (** Lvalue *)
  | SizeOf     of typ                   (** sizeof(<type>). Has [unsigned 
                                         * int] type (ISO 6.5.3.4). This is 
                                         * not turned into a constant because 
                                         * some transformations might want to 
                                         * change types *)

  | SizeOfE    of exp                   (** sizeof(<expression>) *)
  | SizeOfStr  of string
    (** sizeof(string_literal). We separate this case out because this is the 
      * only instance in which a string literal should not be treated as 
      * having type pointer to character. *)

  | AlignOf    of typ                   (** Has [unsigned int] type *)
  | AlignOfE   of exp 

                                        
  | UnOp       of unop * exp * typ      (** Unary operation. Includes 
                                            the type of the result *)

  | BinOp      of binop * exp * exp * typ
                                        (** Binary operation. Includes the 
                                            type of the result. The arithemtic
                                            conversions are made  explicit
                                            for the arguments *)
  | CastE      of typ * exp            (** Use {!Cil.mkCast} to make casts *)

  | AddrOf     of lval                 (** Always use {!Cil.mkAddrOf} to 
                                        * construct one of these. Apply to an 
                                        * lvalue of type [T] yields an 
                                        * expression of type [TPtr(T)] *)

  | StartOf    of lval   (** There is no C correspondent for this. C has 
                          * implicit coercions from an array to the address 
                          * of the first element. [StartOf] is used in CIL to 
                          * simplify type checking and is just an explicit 
                          * form of the above mentioned implicit conversion. 
                          * It is not printed. Given an lval of type 
                          * [TArray(T)] produces an expression of type 
                          * [TPtr(T)]. *)


(** Literal constants *)
and constant =
  | CInt64 of int64 * ikind * string option 
                 (** Integer constant. Give the ikind (see ISO9899 6.1.3.2) 
                  * and the textual representation, if available. Use 
                  * {!Cil.integer} or {!Cil.kinteger} to create these. Watch 
                  * out for integers that cannot be represented on 64 bits. 
                  * OCAML does not give Overflow exceptions. *)
  | CStr of string (** String constant (of pointer type) *)
  | CWStr of int64 list (** Wide string constant (of type "wchar_t *") *)
  | CChr of char (** Character constant.  This has type int, so use
                  *  charConstToInt to read the value in case
                  *  sign-extension is needed. *)
  | CReal of float * fkind * string option (** Floating point constant. Give
                                               the fkind (see ISO 6.4.4.2) and
                                               also the textual representation,
                                               if available *)
  | CEnum of exp * string * enuminfo
     (** An enumeration constant with the given value, name, from the given 
      * enuminfo. This is not used if {!Cil.lowerEnum} is false (default). 
      * Use {!Cillower.lowerEnumVisitor} to replace these with integer 
      * constants. *)

(** Unary operators *)
and unop =
    Neg                                 (** Unary minus *)
  | BNot                                (** Bitwise complement (~) *)
  | LNot                                (** Logical Not (!) *)

(** Binary operations *)
and binop =
    PlusA                               (** arithmetic + *)
  | PlusPI                              (** pointer + integer *)
  | IndexPI                             (** pointer + integer but only when 
                                         * it arises from an expression 
                                         * [e\[i\]] when [e] is a pointer and 
                                         * not an array. This is semantically 
                                         * the same as PlusPI but CCured uses 
                                         * this as a hint that the integer is 
                                         * probably positive. *)
  | MinusA                              (** arithmetic - *)
  | MinusPI                             (** pointer - integer *)
  | MinusPP                             (** pointer - pointer *)
  | Mult                                (** * *)
  | Div                                 (** / *)
  | Mod                                 (** % *)
  | Shiftlt                             (** shift left *)
  | Shiftrt                             (** shift right *)

  | Lt                                  (** <  (arithmetic comparison) *)
  | Gt                                  (** >  (arithmetic comparison) *)  
  | Le                                  (** <= (arithmetic comparison) *)
  | Ge                                  (** >  (arithmetic comparison) *)
  | Eq                                  (** == (arithmetic comparison) *)
  | Ne                                  (** != (arithmetic comparison) *)            
  | BAnd                                (** bitwise and *)
  | BXor                                (** exclusive-or *)
  | BOr                                 (** inclusive-or *)

  | LAnd                                (** logical and *)
  | LOr                                 (** logical or *)




(** An lvalue denotes the contents of a range of memory addresses. This range 
 * is denoted as a host object along with an offset within the object. The 
 * host object can be of two kinds: a local or global variable, or an object 
 * whose address is in a pointer expression. We distinguish the two cases so 
 * that we can tell quickly whether we are accessing some component of a 
 * variable directly or we are accessing a memory location through a pointer.*)
and lval =
    lhost * offset

(** The host part of an {!Cil.lval}. *)
and lhost = 
  | Var        of varinfo    
    (** The host is a variable. *)

  | Mem        of exp        
    (** The host is an object of type [T] when the expression has pointer 
     * [TPtr(T)]. *)


(** The offset part of an {!Cil.lval}. Each offset can be applied to certain 
  * kinds of lvalues and its effect is that it advances the starting address 
  * of the lvalue and changes the denoted type, essentially focussing to some 
  * smaller lvalue that is contained in the original one. *)
and offset = 
  | NoOffset          (** No offset. Can be applied to any lvalue and does 
                        * not change either the starting address or the type. 
                        * This is used when the lval consists of just a host 
                        * or as a terminator in a list of other kinds of 
                        * offsets. *)

  | Field      of fieldinfo * offset    
                      (** A field offset. Can be applied only to an lvalue 
                       * that denotes a structure or a union that contains 
                       * the mentioned field. This advances the offset to the 
                       * beginning of the mentioned field and changes the 
                       * type to the type of the mentioned field. *)

  | Index    of exp * offset
                     (** An array index offset. Can be applied only to an 
                       * lvalue that denotes an array. This advances the 
                       * starting address of the lval to the beginning of the 
                       * mentioned array element and changes the denoted type 
                       * to be the type of the array element *)



(* The following equivalences hold *)
(* Mem(AddrOf(Mem a, aoff)), off   = Mem a, aoff + off                *)
(* Mem(AddrOf(Var v, aoff)), off   = Var v, aoff + off                *)
(* AddrOf (Mem a, NoOffset)        = a                                *)

(** Initializers for global variables.  You can create an initializer with 
 * {!Cil.makeZeroInit}. *)
and init = 
  | SingleInit   of exp   (** A single initializer *)
  | CompoundInit   of typ * (offset * init) list
            (** Used only for initializers of structures, unions and arrays. 
             * The offsets are all of the form [Field(f, NoOffset)] or 
             * [Index(i, NoOffset)] and specify the field or the index being 
             * initialized. For structures all fields
             * must have an initializer (except the unnamed bitfields), in 
             * the proper order. This is necessary since the offsets are not 
             * printed. For arrays the list must contain a prefix of the 
             * initializers; the rest are 0-initialized. 
             * For unions there must be exactly one initializer. If 
             * the initializer is not for the first field then a field 
             * designator is printed, so you better be on GCC since MSVC does 
             * not understand this. You can scan an initializer list with 
             * {!Cil.foldLeftCompound}. *)

(** We want to be able to update an initializer in a global variable, so we 
 * define it as a mutable field *)
and initinfo = {
    mutable init : init option;
  } 


(** Function definitions. *)
and fundec =
    { mutable svar:     varinfo;        
         (** Holds the name and type as a variable, so we can refer to it 
          * easily from the program. All references to this function either 
          * in a function call or in a prototype must point to the same 
          * varinfo. *)
      mutable sformals: varinfo list;   
        (** Formals. These must be shared with the formals that appear in the 
         * type of the function. Use {!Cil.setFormals} or 
         * {!Cil.setFunctionType} to set these 
         * formals and ensure that they are reflected in the function type. 
         * Do not make copies of these because the body refers to them. *)
      mutable slocals: varinfo list;    
        (** Locals. Does not include the sformals. Do not make copies of 
         * these because the body refers to them. *)
      mutable smaxid: int;           (** Max local id. Starts at 0. *)
      mutable sbody: block;          (** The function body. *)
      mutable smaxstmtid: int option;  (** max id of a (reachable) statement 
                                        * in this function, if we have 
                                        * computed it. range = 0 ... 
                                        * (smaxstmtid-1). This is computed by 
                                        * {!Cil.computeCFGInfo}. *)
      mutable sallstmts: stmt list;   (** After you call {!Cil.computeCFGInfo} 
                                      * this field is set to contain all 
                                      * statements in the function *)
    }


(** A block is a sequence of statements with the control falling through from 
    one element to the next *)
and block = 
   { mutable battrs: attributes;      (** Attributes for the block *)
     mutable bstmts: stmt list;       (** The statements comprising the block*)
   } 


(** Statements. 
    The statement is the structural unit in the control flow graph. Use mkStmt 
    to make a statement and then fill in the fields. *)
and stmt = {
    mutable labels: label list;        (** Whether the statement starts with 
                                           some labels, case statements or 
                                           default statement *)
    mutable skind: stmtkind;           (** The kind of statement *)

    (* Now some additional control flow information. Initially this is not 
     * filled in. *)
    mutable sid: int;                  (** A number (>= 0) that is unique 
                                           in a function. *)
    mutable succs: stmt list;          (** The successor statements. They can 
                                           always be computed from the skind 
                                           and the context in which this 
                                           statement appears *)
    mutable preds: stmt list;          (** The inverse of the succs function*)
  } 

(** Labels *)
and label = 
    Label of string * location * bool   
          (** A real label. If the bool is "true", the label is from the 
           * input source program. If the bool is "false", the label was 
           * created by CIL or some other transformation *)
  | Case of exp * location              (** A case statement *)
  | Default of location                 (** A default statement *)



(* The various kinds of statements *)
and stmtkind = 
  | Instr  of instr list               (** A group of instructions that do not 
                                           contain control flow. Control
                                           implicitly falls through. *)
  | Return of exp option * location     (** The return statement. This is a 
                                            leaf in the CFG. *)

  | Goto of stmt ref * location         (** A goto statement. Appears from 
                                            actual goto's in the code. *)
  | Break of location                   (** A break to the end of the nearest 
                                             enclosing loop or Switch *)
  | Continue of location                (** A continue to the start of the 
                                            nearest enclosing loop *)
  | If of exp * block * block * location (** A conditional. 
                                             Two successors, the "then" and 
                                             the "else" branches. Both 
                                             branches  fall-through to the 
                                             successor of the If statement *)
  | Switch of exp * block * (stmt list) * location  
                                       (** A switch statement. The block 
                                           contains within all of the cases. 
                                           We also have direct pointers to the 
                                           statements that implement the 
                                           cases. Which cases they implement 
                                           you can get from the labels of the 
                                           statement *)

(*
  | Loop of block * location * (stmt option) * (stmt option) 
                                           (** A [while(1)] loop. The 
                                            * termination test is implemented 
                                            * in the body of a loop using a 
                                            * [Break] statement. If 
                                            * prepareCFG has been called, the 
                                            * first stmt option will point to 
                                            * the stmt containing the 
                                            * continue label for this loop 
                                            * and the second will point to 
                                            * the stmt containing the break 
                                            * label for this loop. *)
*)
  | While of exp * block * location                 (** A while loop. *)
  | DoWhile of exp * block * location               (** A do...while loop. *)
  | For of block * exp * block * block * location   (** A for loop. *)

  | Block of block                      (** Just a block of statements. Use it 
                                            as a way to keep some attributes 
                                            local *)
    (** On MSVC we support structured exception handling. This is what you 
     * might expect. Control can get into the finally block either from the 
     * end of the body block, or if an exception is thrown. The location 
     * corresponds to the try keyword. *)
  | TryFinally of block * block * location

    (** On MSVC we support structured exception handling. The try/except 
     * statement is a bit tricky: 
         __try { blk } 
         __except (e) {
            handler
         }

         The argument to __except  must be an expression. However, we keep a 
         list of instructions AND an expression in case you need to make 
         function calls. We'll print those as a comma expression. The control 
         can get to the __except expression only if an exception is thrown. 
         After that, depending on the value of the expression the control 
         goes to the handler, propagates the exception, or retries the 
         exception !!! The location corresponds to the try keyword. 
     *)      
  | TryExcept of block * (instr list * exp) * block * location
    

(** Instructions. They may cause effects directly but may not have control
    flow.*)
and instr =
    Set        of lval * exp * location  (** An assignment. A cast is present 
                                             if the exp has different type 
                                             from lval *)
  | Call       of lval option * exp * exp list * location
 			 (** optional: result is an lval. A cast might be 
                             necessary if the declared result type of the 
                             function is not the same as that of the 
                             destination. If the function is declared then 
                             casts are inserted for those arguments that 
                             correspond to declared formals. (The actual 
                             number of arguments might be smaller or larger 
                             than the declared number of arguments. C allows 
                             this.) If the type of the result variable is not 
                             the same as the declared type of the function 
                             result then an implicit cast exists. *)

                         (* See the GCC specification for the meaning of ASM. 
                          * If the source is MS VC then only the templates 
                          * are used *)
                         (* sm: I've added a notes.txt file which contains more
                          * information on interpreting Asm instructions *)
  | Asm        of attributes * (* Really only const and volatile can appear 
                               * here *)
                  string list *         (* templates (CR-separated) *)
                  (string * lval) list * (* outputs must be lvals with 
                                          * constraints. I would like these 
                                          * to be actually variables, but I 
                                          * run into some trouble with ASMs 
                                          * in the Linux sources  *)
                  (string * exp) list * (* inputs with constraints *)
                  string list *         (* register clobbers *)
                  location
        (** An inline assembly instruction. The arguments are (1) a list of 
            attributes (only const and volatile can appear here and only for 
            GCC), (2) templates (CR-separated), (3) a list of 
            outputs, each of which is an lvalue with a constraint, (4) a list 
            of input expressions along with constraints, (5) clobbered 
            registers, and (5) location information *)



(** Describes a location in a source file *)
and location = { 
    line: int;		   (** The line number. -1 means "do not know" *)
    file: string;          (** The name of the source file*)
    byte: int;             (** The byte position in the source file *)
}

(* Type signatures. Two types are identical iff they have identical 
 * signatures *)
and typsig = 
    TSArray of typsig * int64 option * attribute list
  | TSPtr of typsig * attribute list
  | TSComp of bool * string * attribute list
  | TSFun of typsig * typsig list * bool * attribute list
  | TSEnum of string * attribute list
  | TSBase of typ



(** To be able to add/remove features easily, each feature should be package 
   * as an interface with the following interface. These features should be *)
type featureDescr = {
    fd_enabled: bool ref; 
    (** The enable flag. Set to default value  *)

    fd_name: string; 
    (** This is used to construct an option "--doxxx" and "--dontxxx" that 
     * enable and disable the feature  *)

    fd_description: string; 
    (* A longer name that can be used to document the new options  *)

    fd_extraopt: (string * Arg.spec * string) list; 
    (** Additional command line options *)

    fd_doit: (file -> unit);
    (** This performs the transformation *)

    fd_post_check: bool; 
    (* Whether to perform a CIL consistency checking after this stage, if 
     * checking is enabled (--check is passed to cilly) *)
}

let locUnknown = { line = -1; 
		   file = ""; 
		   byte = -1;}

(* A reference to the current location *)
let currentLoc : location ref = ref locUnknown

(* A reference to the current global being visited *)
let currentGlobal: global ref = ref (GText "dummy")


let compareLoc (a: location) (b: location) : int =
  let namecmp = compare a.file b.file in
  if namecmp != 0 
  then namecmp
  else
    let linecmp = a.line - b.line in
    if linecmp != 0 
    then linecmp
    else a.byte - b.byte

let argsToList : (string * typ * attributes) list option 
                  -> (string * typ * attributes) list 
    = function
    None -> []
  | Some al -> al


(* A hack to allow forward reference of d_exp *)
let pd_exp : (unit -> exp -> doc) ref = 
  ref (fun _ -> E.s (E.bug "pd_exp not initialized"))

(** Different visiting actions. 'a will be instantiated with [exp], [instr],
    etc. *)
type 'a visitAction = 
    SkipChildren                        (** Do not visit the children. Return 
                                            the node as it is. *)
  | DoChildren                          (** Continue with the children of this 
                                            node. Rebuild the node on return 
                                            if any of the children changes 
                                            (use == test) *)
  | ChangeTo of 'a                      (** Replace the expression with the 
                                            given one *)
  | ChangeDoChildrenPost of 'a * ('a -> 'a) (** First consider that the entire 
                                           exp is replaced by the first 
                                           parameter. Then continue with 
                                           the children. On return rebuild 
                                           the node if any of the children 
                                           has changed and then apply the 
                                           function on the node *)



(* sm/gn: cil visitor interface for traversing Cil trees. *)
(* Use visitCilStmt and/or visitCilFile to use this. *)
(* Some of the nodes are changed in place if the children are changed. Use 
 * one of Change... actions if you want to copy the node *)

(** A visitor interface for traversing CIL trees. Create instantiations of 
 * this type by specializing the class {!Cil.nopCilVisitor}. *)
class type cilVisitor = object

  method vvdec: varinfo -> varinfo visitAction  
    (** Invoked for each variable declaration. The subtrees to be traversed 
     * are those corresponding to the type and attributes of the variable. 
     * Note that variable declarations are all the [GVar], [GVarDecl], [GFun], 
     * all the [varinfo] in formals of function types, and the formals and 
     * locals for function definitions. This means that the list of formals 
     * in a function definition will be traversed twice, once as part of the 
     * function type and second as part of the formals in a function 
     * definition. *)

  method vvrbl: varinfo -> varinfo visitAction  
    (** Invoked on each variable use. Here only the [SkipChildren] and 
     * [ChangeTo] actions make sense since there are no subtrees. Note that 
     * the type and attributes of the variable are not traversed for a 
     * variable use *)

  method vexpr: exp -> exp visitAction          
    (** Invoked on each expression occurence. The subtrees are the 
     * subexpressions, the types (for a [Cast] or [SizeOf] expression) or the 
     * variable use. *)

  method vlval: lval -> lval visitAction        
    (** Invoked on each lvalue occurence *)

  method voffs: offset -> offset visitAction    
    (** Invoked on each offset occurrence that is *not* as part
      * of an initializer list specification, i.e. in an lval or
      * recursively inside an offset. *)

  method vinitoffs: offset -> offset visitAction
    (** Invoked on each offset appearing in the list of a 
      * CompoundInit initializer.  *)

  method vinst: instr -> instr list visitAction 
    (** Invoked on each instruction occurrence. The [ChangeTo] action can 
     * replace this instruction with a list of instructions *)

  method vstmt: stmt -> stmt visitAction        
    (** Control-flow statement. *)

  method vblock: block -> block visitAction     (** Block. Replaced in 
                                                    place. *)
  method vfunc: fundec -> fundec visitAction    (** Function definition. 
                                                    Replaced in place. *)
  method vglob: global -> global list visitAction (** Global (vars, types,
                                                      etc.)  *)
  method vinit: init -> init visitAction        (** Initializers for globals *)
  method vtype: typ -> typ visitAction          (** Use of some type. Note 
                                                 * that for structure/union 
                                                 * and enumeration types the 
                                                 * definition of the 
                                                 * composite type is not 
                                                 * visited. Use [vglob] to 
                                                 * visit it.  *)
  method vattr: attribute -> attribute list visitAction 
    (** Attribute. Each attribute can be replaced by a list *)
  method vattrparam: attrparam -> attrparam visitAction 
    (** Attribute parameters. *)

    (** Add here instructions while visiting to queue them to 
     * preceede the current statement or instruction being processed *)
  method queueInstr: instr list -> unit

    (** Gets the queue of instructions and resets the queue *)
  method unqueueInstr: unit -> instr list

end

(* the default visitor does nothing at each node, but does *)
(* not stop; hence they return true *)
class nopCilVisitor : cilVisitor = object
  method vvrbl (v:varinfo) = DoChildren (* variable *)
  method vvdec (v:varinfo) = DoChildren (* variable 
                                                               * declaration *)
  method vexpr (e:exp) = DoChildren   (* expression *) 
  method vlval (l:lval) = DoChildren  (* lval (base is 1st 
                                                         * field)  *)
  method voffs (o:offset) = DoChildren      (* lval or recursive offset *)
  method vinitoffs (o:offset) = DoChildren  (* initializer offset *)
  method vinst (i:instr) = DoChildren       (* imperative instruction *)
  method vstmt (s:stmt) = DoChildren        (* constrol-flow statement *)
  method vblock (b: block) = DoChildren
  method vfunc (f:fundec) = DoChildren      (* function definition *)
  method vglob (g:global) = DoChildren      (* global (vars, types, etc.) *)
  method vinit (i:init) = DoChildren        (* global initializers *)
  method vtype (t:typ) = DoChildren         (* use of some type *)
  method vattr (a: attribute) = DoChildren
  method vattrparam (a: attrparam) = DoChildren

  val mutable instrQueue = []
      
  method queueInstr (il: instr list) = 
    List.iter (fun i -> instrQueue <- i :: instrQueue) il

  method unqueueInstr () = 
    let res = List.rev instrQueue in
    instrQueue <- [];
    res

end

let assertEmptyQueue vis =
  if vis#unqueueInstr () <> [] then 
    (* Either a visitor inserted an instruction somewhere that it shouldn't
       have (i.e. at the top level rather than inside of a statement), or
       there's a bug in the visitor engine. *)
    E.s (E.bug "Visitor's instruction queue is not empty.\n  You should only use queueInstr inside a function body!");
  ()


let lu = locUnknown

(* sm: utility *)
let startsWith (prefix: string) (s: string) : bool =
(
  let prefixLen = (String.length prefix) in
  (String.length s) >= prefixLen &&
  (String.sub s 0 prefixLen) = prefix
)


let get_instrLoc (inst : instr) =
  match inst with
      Set(_, _, loc) -> loc
    | Call(_, _, _, loc) -> loc
    | Asm(_, _, _, _, _, loc) -> loc
let get_globalLoc (g : global) =
  match g with
  | GFun(_,l) -> (l)
  | GType(_,l) -> (l)
  | GEnumTag(_,l) -> (l) 
  | GEnumTagDecl(_,l) -> (l) 
  | GCompTag(_,l) -> (l) 
  | GCompTagDecl(_,l) -> (l) 
  | GVarDecl(_,l) -> (l) 
  | GVar(_,_,l) -> (l)
  | GAsm(_,l) -> (l)
  | GPragma(_,l) -> (l) 
  | GText(_) -> locUnknown

let rec get_stmtLoc (statement : stmtkind) =
  match statement with 
      Instr([]) -> lu
    | Instr(hd::tl) -> get_instrLoc(hd)
    | Return(_, loc) -> loc
    | Goto(_, loc) -> loc
    | Break(loc) -> loc
    | Continue(loc) -> loc
    | If(_, _, _, loc) -> loc
    | Switch (_, _, _, loc) -> loc
(*
    | Loop (_, loc, _, _) -> loc
*)
    | While (_, _, loc) -> loc
    | DoWhile (_, _, loc) -> loc
    | For (_, _, _, _, loc) -> loc
    | Block b -> if b.bstmts == [] then lu 
                 else get_stmtLoc ((List.hd b.bstmts).skind)
    | TryFinally (_, _, l) -> l
    | TryExcept (_, _, _, l) -> l


(* The next variable identifier to use. Counts up *)
let nextGlobalVID = ref 1

(* The next compindo identifier to use. Counts up. *)
let nextCompinfoKey = ref 1

(* Some error reporting functions *)
let d_loc (_: unit) (loc: location) : doc =  
  text loc.file ++ chr ':' ++ num loc.line

let d_thisloc (_: unit) : doc = d_loc () !currentLoc

let error (fmt : ('a,unit,doc) format) : 'a = 
  let f d = 
    E.hadErrors := true; 
    ignore (eprintf "@!%t: Error: %a@!" 
              d_thisloc insert d);
    nil
  in
  Pretty.gprintf f fmt

let unimp (fmt : ('a,unit,doc) format) : 'a = 
  let f d = 
    E.hadErrors := true; 
    ignore (eprintf "@!%t: Unimplemented: %a@!" 
              d_thisloc insert d);
    nil
  in
  Pretty.gprintf f fmt

let bug (fmt : ('a,unit,doc) format) : 'a = 
  let f d = 
    E.hadErrors := true; 
    ignore (eprintf "@!%t: Bug: %a@!" 
              d_thisloc insert d);
    E.showContext ();
    nil
  in
  Pretty.gprintf f fmt

let errorLoc (loc: location) (fmt : ('a,unit,doc) format) : 'a = 
  let f d = 
    E.hadErrors := true; 
    ignore (eprintf "@!%a: Error: %a@!" 
              d_loc loc insert d);
    E.showContext ();
    nil
  in
  Pretty.gprintf f fmt

let warn (fmt : ('a,unit,doc) format) : 'a = 
  let f d =
    ignore (eprintf "@!%t: Warning: %a@!" 
              d_thisloc insert d);
    nil
  in
  Pretty.gprintf f fmt


let warnOpt (fmt : ('a,unit,doc) format) : 'a = 
  let f d =
    if !E.warnFlag then 
      ignore (eprintf "@!%t: Warning: %a@!" 
                d_thisloc insert d);
    nil
  in
  Pretty.gprintf f fmt

let warnContext (fmt : ('a,unit,doc) format) : 'a = 
  let f d =
    ignore (eprintf "@!%t: Warning: %a@!" 
              d_thisloc insert d);
    E.showContext ();
    nil
  in
  Pretty.gprintf f fmt

let warnContextOpt (fmt : ('a,unit,doc) format) : 'a = 
  let f d =
    if !E.warnFlag then 
      ignore (eprintf "@!%t: Warning: %a@!" 
                d_thisloc insert d);
    E.showContext ();
    nil
  in
  Pretty.gprintf f fmt

let warnLoc (loc: location) (fmt : ('a,unit,doc) format) : 'a = 
  let f d =
    ignore (eprintf "@!%a: Warning: %a@!" 
              d_loc loc insert d);
    E.showContext ();
    nil
  in
  Pretty.gprintf f fmt



(* Construct an integer. Use only for values that fit on 31 bits.
   For larger values, use kinteger *)
let integer (i: int) = Const (CInt64(Int64.of_int i, IInt, None))
            
let zero      = integer 0
let one       = integer 1
let mone      = integer (-1)

(** Given the character c in a (CChr c), sign-extend it to 32 bits.
  (This is the official way of interpreting character constants, according to
  ISO C 6.4.4.4.10, which says that character constants are chars cast to ints)
  Returns CInt64(sign-extened c, IInt, None) *)
let charConstToInt (c: char) : constant =
  let c' = Char.code c in
  let value = 
    if c' < 128 
    then Int64.of_int c'
    else Int64.of_int (c' - 256)
  in
  CInt64(value, IInt, None)
  
  
let rec isInteger = function
  | Const(CInt64 (n,_,_)) -> Some n
  | Const(CChr c) -> isInteger (Const (charConstToInt c))  (* sign-extend *) 
  | Const(CEnum(v, s, ei)) -> isInteger v
  | CastE(_, e) -> isInteger e
  | _ -> None
        


let rec isZero (e: exp) : bool = isInteger e = Some Int64.zero

let voidType = TVoid([])
let intType = TInt(IInt,[])
let uintType = TInt(IUInt,[])
let longType = TInt(ILong,[])
let ulongType = TInt(IULong,[])
let charType = TInt(IChar, [])

let charPtrType = TPtr(charType,[])
let charConstPtrType = TPtr(TInt(IChar, [Attr("const", [])]),[])
let stringLiteralType = ref charPtrType

let voidPtrType = TPtr(voidType, [])
let intPtrType = TPtr(intType, [])
let uintPtrType = TPtr(uintType, [])

let doubleType = TFloat(FDouble, [])


(* An integer type that fits pointers. Initialized by initCIL *)
let upointType = ref voidType 

(* An integer type that fits wchar_t. Initialized by initCIL *)
let wcharKind = ref IChar
let wcharType = ref voidType 


(* An integer type that is the type of sizeof. Initialized by initCIL *)
let typeOfSizeOf = ref voidType
let kindOfSizeOf = ref IUInt

let initCIL_called = ref false

(** Returns true if and only if the given integer type is signed. *)
let isSigned = function
  | IUChar
  | IUShort
  | IUInt
  | IULong
  | IULongLong ->
      false
  | ISChar
  | IShort
  | IInt
  | ILong
  | ILongLong ->
      true
  | IChar ->
      not !theMachine.M.char_is_unsigned

let mkStmt (sk: stmtkind) : stmt = 
  { skind = sk;
    labels = [];
    sid = -1; succs = []; preds = [] }

let mkBlock (slst: stmt list) : block = 
  { battrs = []; bstmts = slst; }

let mkEmptyStmt () = mkStmt (Instr [])
let mkStmtOneInstr (i: instr) = mkStmt (Instr [i])

let dummyInstr = (Asm([], ["dummy statement!!"], [], [], [], lu))
let dummyStmt =  mkStmt (Instr [dummyInstr])

let compactStmts (b: stmt list) : stmt list =  
      (* Try to compress statements. Scan the list of statements and remember 
       * the last instrunction statement encountered, along with a Clist of 
       * instructions in it. *)
  let rec compress (lastinstrstmt: stmt) (* Might be dummStmt *)
                   (lastinstrs: instr Clist.clist) 
                   (body: stmt list) =
    let finishLast (tail: stmt list) : stmt list = 
      if lastinstrstmt == dummyStmt then tail
      else begin
        lastinstrstmt.skind <- Instr (Clist.toList lastinstrs);
        lastinstrstmt :: tail
      end
    in
    match body with 
      [] -> finishLast []
    | ({skind=Instr il} as s) :: rest ->
        let ils = Clist.fromList il in
        if lastinstrstmt != dummyStmt && s.labels == [] then
          compress lastinstrstmt (Clist.append lastinstrs ils) rest
        else
          finishLast (compress s ils rest)

    | s :: rest -> 
        let res = s :: compress dummyStmt Clist.empty rest in
        finishLast res
  in
  compress dummyStmt Clist.empty b


(** Construct sorted lists of attributes ***)
let rec addAttribute (Attr(an, _) as a: attribute) (al: attributes) = 
  let rec insertSorted = function
      [] -> [a]
    | ((Attr(an0, _) as a0) :: rest) as l -> 
        if an < an0 then a :: l
        else if Util.equals a a0 then l (* Do not add if already in there *)
        else a0 :: insertSorted rest (* Make sure we see all attributes with 
                                      * this name *)
  in
  insertSorted al

(** The second attribute list is sorted *)
and addAttributes al0 (al: attributes) : attributes = 
    if al0 == [] then al else
    List.fold_left (fun acc a -> addAttribute a acc) al al0

and dropAttribute (an: string) (al: attributes) = 
  List.filter (fun (Attr(an', _)) -> an <> an') al

and dropAttributes (anl: string list) (al: attributes) = 
  List.fold_left (fun acc an -> dropAttribute an acc) al anl
  
and filterAttributes (s: string) (al: attribute list) : attribute list = 
  List.filter (fun (Attr(an, _)) -> an = s) al

(* sm: *)
let hasAttribute s al =
  (filterAttributes s al <> [])


type attributeClass = 
    AttrName of bool 
        (* Attribute of a name. If argument is true and we are on MSVC then 
         * the attribute is printed using __declspec as part of the storage 
         * specifier  *)
  | AttrFunType of bool 
        (* Attribute of a function type. If argument is true and we are on 
         * MSVC then the attribute is printed just before the function name *)

  | AttrType  (* Attribute of a type *)

(* This table contains the mapping of predefined attributes to classes. 
 * Extend this table with more attributes as you need. This table is used to 
 * determine how to associate attributes with names or type during cabs2cil 
 * conversion *)
let attributeHash: (string, attributeClass) H.t = 
  let table = H.create 13 in
  List.iter (fun a -> H.add table a (AttrName false))
    [ "section"; "constructor"; "destructor"; "unused"; "used"; "weak"; 
      "no_instrument_function"; "alias"; "no_check_memory_usage";
      "exception"; "model"; (* "restrict"; *)
      "aconst"; "__asm__" (* Gcc uses this to specifiy the name to be used in 
                           * assembly for a global  *)];

  (* Now come the MSVC declspec attributes *)
  List.iter (fun a -> H.add table a (AttrName true))
    [ "thread"; "naked"; "dllimport"; "dllexport";
      "selectany"; "allocate"; "nothrow"; "novtable"; "property";  "noreturn";
      "uuid"; "align" ];

  List.iter (fun a -> H.add table a (AttrFunType false))
    [ "format"; "regparm"; "longcall"; 
      "noinline"; "always_inline"; ];

  List.iter (fun a -> H.add table a (AttrFunType true))
    [ "stdcall";"cdecl"; "fastcall" ];

  List.iter (fun a -> H.add table a AttrType)
    [ "const"; "volatile"; "restrict"; "mode" ];
  table
      

(* Partition the attributes into classes *)
let partitionAttributes 
    ~(default:attributeClass)  
    (attrs:  attribute list) :
    attribute list * attribute list * attribute list = 
  let rec loop (n,f,t) = function
      [] -> n, f, t
    | (Attr(an, _) as a) :: rest -> 
        match (try H.find attributeHash an with Not_found -> default) with 
          AttrName _ -> loop (addAttribute a n, f, t) rest
        | AttrFunType _ -> 
            loop (n, addAttribute a f, t) rest
        | AttrType -> loop (n, f, addAttribute a t) rest
  in
  loop ([], [], []) attrs


(* Get the full name of a comp *)
let compFullName comp = 
  (if comp.cstruct then "struct " else "union ") ^ comp.cname

 
let missingFieldName = "___missing_field_name"

(** Creates a a (potentially recursive) composite type. Make sure you add a 
  * GTag for it to the file! **)
let mkCompInfo
      (isstruct: bool) 
      (n: string)  
      (* fspec is a function that when given a forward 
       * representation of the structure type constructs the type of 
       * the fields. The function can ignore this argument if not 
       * constructing a recursive type.  *)
       (mkfspec: compinfo -> (string * typ * int option * attribute list *
                             location) list)   
       (a: attribute list) : compinfo =

  (* make an new name for anonymous structs *)
   if n = "" then 
     E.s (E.bug "mkCompInfo: missing structure name\n");
   (* Make a new self cell and a forward reference *)
   let comp = 
     { cstruct = isstruct; cname = ""; ckey = 0; cfields = [];
       cattr = a; creferenced = false; 
       (* Make this compinfo undefined by default *)
       cdefined = false; } 
   in
   comp.cname <- n;
   comp.ckey <- !nextCompinfoKey;
   incr nextCompinfoKey;
   let flds = 
       List.map (fun (fn, ft, fb, fa, fl) -> 
          { fcomp = comp;
            ftype = ft;
            fname = fn;
            fbitfield = fb;
            fattr = fa;
            floc = fl}) (mkfspec comp) in
   comp.cfields <- flds;
   if flds <> [] then comp.cdefined <- true;
   comp

(** Make a copy of a compinfo, changing the name and the key *)
let copyCompInfo (ci: compinfo) (n: string) : compinfo = 
  let ci' = {ci with cname = n; 
                     ckey = !nextCompinfoKey; } in
  incr nextCompinfoKey;
  (* Copy the fields and set the new pointers to parents *)
  ci'.cfields <- List.map (fun f -> {f with fcomp = ci'}) ci'.cfields;
  ci'

(**** Utility functions ******)

let rec typeAttrs = function
    TVoid a -> a
  | TInt (_, a) -> a
  | TFloat (_, a) -> a
  | TNamed (t, a) -> addAttributes a (typeAttrs t.ttype)
  | TPtr (_, a) -> a
  | TArray (_, _, a) -> a
  | TComp (comp, a) -> addAttributes comp.cattr a
  | TEnum (enum, a) -> addAttributes enum.eattr a
  | TFun (_, _, _, a) -> a
  | TBuiltin_va_list a -> a


let setTypeAttrs t a =
  match t with
    TVoid _ -> TVoid a
  | TInt (i, _) -> TInt (i, a)
  | TFloat (f, _) -> TFloat (f, a)
  | TNamed (t, _) -> TNamed(t, a)
  | TPtr (t', _) -> TPtr(t', a)
  | TArray (t', l, _) -> TArray(t', l, a)
  | TComp (comp, _) -> TComp (comp, a)
  | TEnum (enum, _) -> TEnum (enum, a)
  | TFun (r, args, v, _) -> TFun(r,args,v,a)
  | TBuiltin_va_list _ -> TBuiltin_va_list a


let typeAddAttributes a0 t =
begin
  match a0 with
  | [] ->
      (* no attributes, keep same type *)
      t
  | _ ->
      (* anything else: add a0 to existing attributes *)
      let add (a: attributes) = addAttributes a0 a in
      match t with
        TVoid a -> TVoid (add a)
      | TInt (ik, a) -> TInt (ik, add a)
      | TFloat (fk, a) -> TFloat (fk, add a)
      | TEnum (enum, a) -> TEnum (enum, add a)
      | TPtr (t, a) -> TPtr (t, add a)
      | TArray (t, l, a) -> TArray (t, l, add a)
      | TFun (t, args, isva, a) -> TFun(t, args, isva, add a)
      | TComp (comp, a) -> TComp (comp, add a)
      | TNamed (t, a) -> TNamed (t, add a)
      | TBuiltin_va_list a -> TBuiltin_va_list (add a)
end

let typeRemoveAttributes (anl: string list) t = 
  let drop (al: attributes) = dropAttributes anl al in
  match t with 
    TVoid a -> TVoid (drop a)
  | TInt (ik, a) -> TInt (ik, drop a)
  | TFloat (fk, a) -> TFloat (fk, drop a)
  | TEnum (enum, a) -> TEnum (enum, drop a)
  | TPtr (t, a) -> TPtr (t, drop a)
  | TArray (t, l, a) -> TArray (t, l, drop a)
  | TFun (t, args, isva, a) -> TFun(t, args, isva, drop a)
  | TComp (comp, a) -> TComp (comp, drop a)
  | TNamed (t, a) -> TNamed (t, drop a)
  | TBuiltin_va_list a -> TBuiltin_va_list (drop a)

let unrollType (t: typ) : typ = 
  let rec withAttrs (al: attributes) (t: typ) : typ =     
    match t with 
      TNamed (r, a') -> withAttrs (addAttributes al a') r.ttype
    | x -> typeAddAttributes al x
  in
  withAttrs [] t

let rec unrollTypeDeep (t: typ) : typ = 
  let rec withAttrs (al: attributes) (t: typ) : typ =     
    match t with 
      TNamed (r, a') -> withAttrs (addAttributes al a') r.ttype
    | TPtr(t, a') -> TPtr(unrollTypeDeep t, addAttributes al a')
    | TArray(t, l, a') -> TArray(unrollTypeDeep t, l, addAttributes al a')
    | TFun(rt, args, isva, a') -> 
        TFun (unrollTypeDeep rt, 
              (match args with 
                None -> None
              | Some argl -> 
                  Some (List.map (fun (an,at,aa) -> 
                  (an, unrollTypeDeep at, aa)) argl)), 
              isva, 
              addAttributes al a')
    | x -> typeAddAttributes al x
  in
  withAttrs [] t

let isVoidType t = 
  match unrollType t with
    TVoid _ -> true
  | _ -> false
let isVoidPtrType t = 
  match unrollType t with
    TPtr(tau,_) when isVoidType tau -> true
  | _ -> false

let var vi : lval = (Var vi, NoOffset)
(* let assign vi e = Instrs(Set (var vi, e), lu) *)

let mkString s = Const(CStr s)


let mkWhile ~(guard:exp) ~(body: stmt list) : stmt list = 
  (* Do it like this so that the pretty printer recognizes it *)
(*
  [ mkStmt (Loop (mkBlock (mkStmt (If(guard, 
                                      mkBlock [ mkEmptyStmt () ], 
                                      mkBlock [ mkStmt (Break lu)], lu)) ::
                           body), lu, None, None)) ]
*)
  [ mkStmt (While (guard, mkBlock body, lu)) ]



let mkFor ~(start: stmt list) ~(guard: exp) ~(next: stmt list) 
          ~(body: stmt list) : stmt list = 
  (start @ 
     (mkWhile guard (body @ next)))

    
let mkForIncr ~(iter : varinfo) ~(first: exp) ~stopat:(past: exp) ~(incr: exp) 
    ~(body: stmt list) : stmt list = 
      (* See what kind of operator we need *)
  let compop, nextop = 
    match unrollType iter.vtype with
      TPtr _ -> Lt, PlusPI
    | _ -> Lt, PlusA
  in
  mkFor 
    [ mkStmt (Instr [(Set (var iter, first, lu))]) ]
    (BinOp(compop, Lval(var iter), past, intType))
    [ mkStmt (Instr [(Set (var iter, 
                           (BinOp(nextop, Lval(var iter), incr, iter.vtype)),
                           lu))])] 
    body
  

let rec stripCasts (e: exp) = 
  match e with CastE(_, e') -> stripCasts e' | _ -> e



(* the name of the C function we call to get ccgr ASTs
external parse : string -> file = "cil_main"
*)
(* 
  Pretty Printing
 *)

let d_ikind () = function
    IChar -> text "char"
  | ISChar -> text "signed char"
  | IUChar -> text "unsigned char"
  | IInt -> text "int"
  | IUInt -> text "unsigned int"
  | IShort -> text "short"
  | IUShort -> text "unsigned short"
  | ILong -> text "long"
  | IULong -> text "unsigned long"
  | ILongLong -> 
      if !msvcMode then text "__int64" else text "long long"
  | IULongLong -> 
      if !msvcMode then text "unsigned __int64" 
      else text "unsigned long long"

let d_fkind () = function
    FFloat -> text "float"
  | FDouble -> text "double"
  | FLongDouble -> text "long double"

let d_storage () = function
    NoStorage -> nil
  | Static -> text "static "
  | Extern -> text "extern "
  | Register -> text "register "

(* sm: need this value below *)
let mostNeg32BitInt : int64 = (Int64.of_string "-0x80000000")
let mostNeg64BitInt : int64 = (Int64.of_string "-0x8000000000000000")

(* constant *)
let d_const () c = 
  match c with
    CInt64(_, _, Some s) -> text s (* Always print the text if there is one *)
  | CInt64(i, ik, None) -> 
      (** We must make sure to capture the type of the constant. For some 
       * constants this is done with a suffix, for others with a cast prefix.*)
      let suffix : string = 
        match ik with
          IUInt -> "U"
        | ILong -> "L"
        | IULong -> "UL"
        | ILongLong -> if !msvcMode then "L" else "LL"
        | IULongLong -> if !msvcMode then "UL" else "ULL"
        | _ -> ""
      in
      let prefix : string = 
        if suffix <> "" then "" 
        else if ik = IInt then ""
        else "(" ^ (sprint !lineLength (d_ikind () ik)) ^ ")"
      in
      (* Watch out here for negative integers that we should be printing as 
       * large positive ones *)
      if i < Int64.zero 
          && (match ik with 
            IUInt | IULong | IULongLong | IUChar | IUShort -> true | _ -> false) then
        let high = Int64.shift_right i 32 in
        if ik <> IULongLong && ik <> ILongLong && high = Int64.of_int (-1) then
          (* Print only the low order 32 bits *)
          text (prefix ^ "0x" ^ 
                (Int64.format "%x" 
                  (Int64.logand i (Int64.shift_right_logical high 32))
                ^ suffix))
        else
          text (prefix ^ "0x" ^ Int64.format "%x" i ^ suffix)
      else (
        if (i = mostNeg32BitInt) then
          (* sm: quirk here: if you print -2147483648 then this is two tokens *)
          (* in C, and the second one is too large to represent in a signed *)
          (* int.. so we do what's done in limits.h, and print (-2147483467-1); *)
          (* in gcc this avoids a warning, but it might avoid a real problem *)
          (* on another compiler or a 64-bit architecture *)
          text (prefix ^ "(-0x7FFFFFFF-1)")
        else if (i = mostNeg64BitInt) then
          (* The same is true of the largest 64-bit negative. *)
          text (prefix ^ "(-0x7FFFFFFFFFFFFFFF-1)")
        else
          text (prefix ^ (Int64.to_string i ^ suffix))
      )

  | CStr(s) -> text ("\"" ^ escape_string s ^ "\"")
  | CWStr(s) -> 
      (* text ("L\"" ^ escape_string s ^ "\"")  *)
      (List.fold_left (fun acc elt -> 
        acc ++ 
        if (elt >= Int64.zero &&
            elt <= (Int64.of_int 255)) then 
          text (escape_char (Char.chr (Int64.to_int elt)))
        else
          ( text (Printf.sprintf "\\x%LX\"" elt) ++ break ++
            (text "\""))
      ) (text "L\"") s ) ++ text "\""
      (* we cannot print L"\xabcd" "feedme" as L"\xabcdfeedme" --
       * the former has 7 wide characters and the later has 3. *)

  | CChr(c) -> text ("'" ^ escape_char c ^ "'")
  | CReal(_, _, Some s) -> text s
  | CReal(f, _, None) -> text (string_of_float f)
  | CEnum(_, s, ei) -> text s


(* Parentheses level. An expression "a op b" is printed parenthesized if its 
 * parentheses level is >= that that of its context. Identifiers have the 
 * lowest level and weakly binding operators (e.g. |) have the largest level. 
 * The correctness criterion is that a smaller level MUST correspond to a 
 * stronger precedence!
 *)
let derefStarLevel = 20
let indexLevel = 20
let arrowLevel = 20
let addrOfLevel = 30
let additiveLevel = 60
let comparativeLevel = 70
let bitwiseLevel = 75
let getParenthLevel = function
  | BinOp((LAnd | LOr), _,_,_) -> 80
                                        (* Bit operations. *)
  | BinOp((BOr|BXor|BAnd),_,_,_) -> bitwiseLevel (* 75 *)

                                        (* Comparisons *)
  | BinOp((Eq|Ne|Gt|Lt|Ge|Le),_,_,_) ->
      comparativeLevel (* 70 *)
                                        (* Additive. Shifts can have higher 
                                         * level than + or - but I want 
                                         * parentheses around them *)
  | BinOp((MinusA|MinusPP|MinusPI|PlusA|
           PlusPI|IndexPI|Shiftlt|Shiftrt),_,_,_)  
    -> additiveLevel (* 60 *)

                                        (* Multiplicative *)
  | BinOp((Div|Mod|Mult),_,_,_) -> 40

                                        (* Unary *)
  | CastE(_,_) -> 30
  | AddrOf(_) -> 30
  | StartOf(_) -> 30
  | UnOp((Neg|BNot|LNot),_,_) -> 30

                                        (* Lvals *)
  | Lval(Mem _ , _) -> 20                   
  | Lval(Var _, (Field _|Index _)) -> 20
  | SizeOf _ | SizeOfE _ | SizeOfStr _ -> 20
  | AlignOf _ | AlignOfE _ -> 20

  | Lval(Var _, NoOffset) -> 0        (* Plain variables *)
  | Const _ -> 0                        (* Constants *)



(* Separate out the storage-modifier name attributes *)
let separateStorageModifiers (al: attribute list) = 
  let isstoragemod (Attr(an, _): attribute) : bool =
    try 
      match H.find attributeHash an with
        AttrName issm -> issm
      | _ -> E.s (E.bug "separateStorageModifier: %s is not a name attribute" an)
    with Not_found -> false
  in
    let stom, rest = List.partition isstoragemod al in
    if not !msvcMode then
      stom, rest
    else
      (* Put back the declspec. Put it without the leading __ since these will 
       * be added later *)
      let stom' = 
	List.map (fun (Attr(an, args)) -> 
          Attr("declspec", [ACons(an, args)])) stom in
      stom', rest


let isIntegralType t = 
  match unrollType t with
    (TInt _ | TEnum _) -> true
  | _ -> false

let isArithmeticType t = 
  match unrollType t with
    (TInt _ | TEnum _ | TFloat _) -> true
  | _ -> false
    

let isPointerType t = 
  match unrollType t with
    TPtr _ -> true
  | _ -> false

let isFunctionType t = 
  match unrollType t with
    TFun _ -> true
  | _ -> false

(**** Compute the type of an expression ****)
let rec typeOf (e: exp) : typ = 
  match e with
  | Const(CInt64 (_, ik, _)) -> TInt(ik, [])

    (* Character constants have type int.  ISO/IEC 9899:1999 (E),
     * section 6.4.4.4 [Character constants], paragraph 10, if you
     * don't believe me. *)
  | Const(CChr _) -> intType

    (* The type of a string is a pointer to characters ! The only case when 
     * you would want it to be an array is as an argument to sizeof, but we 
     * have SizeOfStr for that *)
  | Const(CStr s) -> !stringLiteralType

  | Const(CWStr s) -> TPtr(!wcharType,[])

  | Const(CReal (_, fk, _)) -> TFloat(fk, [])

  | Const(CEnum(_, _, ei)) -> TEnum(ei, [])

  | Lval(lv) -> typeOfLval lv
  | SizeOf _ | SizeOfE _ | SizeOfStr _ -> !typeOfSizeOf
  | AlignOf _ | AlignOfE _ -> !typeOfSizeOf
  | UnOp (_, _, t) -> t
  | BinOp (_, _, _, t) -> t
  | CastE (t, _) -> t
  | AddrOf (lv) -> TPtr(typeOfLval lv, [])
  | StartOf (lv) -> begin
      match unrollType (typeOfLval lv) with
        TArray (t,_, _) -> TPtr(t, [])
     | _ -> E.s (E.bug "typeOf: StartOf on a non-array")
  end
      
and typeOfInit (i: init) : typ = 
  match i with 
    SingleInit e -> typeOf e
  | CompoundInit (t, _) -> t

and typeOfLval = function
    Var vi, off -> typeOffset vi.vtype off
  | Mem addr, off -> begin
      match unrollType (typeOf addr) with
        TPtr (t, _) -> typeOffset t off
      | _ -> E.s (bug "typeOfLval: Mem on a non-pointer")
  end

and typeOffset basetyp =
  let blendAttributes baseAttrs =
    let (_, _, contageous) = 
      partitionAttributes ~default:(AttrName false) baseAttrs in
    typeAddAttributes contageous
  in
  function
    NoOffset -> basetyp
  | Index (_, o) -> begin
      match unrollType basetyp with
        TArray (t, _, baseAttrs) ->
	  let elementType = typeOffset t o in
	  blendAttributes baseAttrs elementType
      | t -> E.s (E.bug "typeOffset: Index on a non-array")
  end 
  | Field (fi, o) ->
      match unrollType basetyp with
        TComp (_, baseAttrs) ->
	  let fieldType = typeOffset fi.ftype o in
	  blendAttributes baseAttrs fieldType
      | _ -> E.s (bug "typeOffset: Field on a non-compound")


(**
 **
 ** MACHINE DEPENDENT PART
 **
 **)
exception SizeOfError of string * typ

        
(* Get the minimum aligment in bytes for a given type *)
let rec alignOf_int = function
  | TInt((IChar|ISChar|IUChar), _) -> 1
  | TInt((IShort|IUShort), _) -> !theMachine.M.alignof_short
  | TInt((IInt|IUInt), _) -> !theMachine.M.alignof_int
  | TInt((ILong|IULong), _) -> !theMachine.M.alignof_long
  | TInt((ILongLong|IULongLong), _) -> !theMachine.M.alignof_longlong
  | TEnum _ -> !theMachine.M.alignof_enum
  | TFloat(FFloat, _) -> !theMachine.M.alignof_float 
  | TFloat(FDouble, _) -> !theMachine.M.alignof_double
  | TFloat(FLongDouble, _) -> !theMachine.M.alignof_longdouble
  | TNamed (t, _) -> alignOf_int t.ttype
  | TArray (t, _, _) -> alignOf_int t
  | TPtr _ | TBuiltin_va_list _ -> !theMachine.M.alignof_ptr

        (* For composite types get the maximum alignment of any field inside *)
  | TComp (c, _) ->
      (* On GCC the zero-width fields do not contribute to the alignment. On 
       * MSVC only those zero-width that _do_ appear after other 
       * bitfields contribute to the alignment. So we drop those that 
       * do not occur after othe bitfields *)
      let rec dropZeros (afterbitfield: bool) = function
        | f :: rest when f.fbitfield = Some 0 && not afterbitfield -> 
            dropZeros afterbitfield rest
        | f :: rest -> f :: dropZeros (f.fbitfield <> None) rest
        | [] -> []
      in
      let fields = dropZeros false c.cfields in
      List.fold_left 
        (fun sofar f -> 
          (* Bitfields with zero width do not contribute to the alignment in 
           * GCC *)
          if not !msvcMode && f.fbitfield = Some 0 then sofar else
          max sofar (alignOf_int f.ftype)) 1 fields
        (* These are some error cases *)
  | TFun _ when not !msvcMode -> !theMachine.M.alignof_fun
      
  | TFun _ as t -> raise (SizeOfError ("function", t))
  | TVoid _ as t -> raise (SizeOfError ("void", t))
      

let bitsSizeOfInt (ik: ikind): int = 
  match ik with 
  | IChar | ISChar | IUChar -> 8 
  | IInt | IUInt -> 8 * !theMachine.M.sizeof_int
  | IShort | IUShort -> 8 * !theMachine.M.sizeof_short
  | ILong | IULong -> 8 * !theMachine.M.sizeof_long
  | ILongLong | IULongLong -> 8 * !theMachine.M.sizeof_longlong

(* Represents an integer as for a given kind. 
   Returns a flag saying whether the value was changed
   during truncation (because it was too large to fit in k). *)
let truncateInteger64 (k: ikind) (i: int64) : int64 * bool = 
  let nrBits = bitsSizeOfInt k in
  let signed = isSigned k in
  if nrBits = 64 then 
    i, false
  else begin
    let i1 = Int64.shift_left i (64 - nrBits) in
    let i2 = 
      if signed then Int64.shift_right i1 (64 - nrBits) 
      else Int64.shift_right_logical i1 (64 - nrBits)
    in
    let truncated =
      if i2 = i then false
      else
        (* Examine the bits that we chopped off.  If they are all zero, then
         * any difference between i2 and i is due to a simple sign-extension.
         *   e.g. casting the constant 0x80000000 to int makes it
         *        0xffffffff80000000.
         * Suppress the truncation warning in this case.      *)
        let chopped = Int64.shift_right_logical i (64 - nrBits)
        in chopped <> Int64.zero
    in
    i2, truncated
  end

(* Construct an integer constant with possible truncation *)
let kinteger64 (k: ikind) (i: int64) : exp = 
  let i', truncated = truncateInteger64 k i in
  if truncated then 
    ignore (warnOpt "Truncating integer %s to %s\n" 
              (Int64.format "0x%x" i) (Int64.format "0x%x" i'));
  Const (CInt64(i', k,  None))

(* Construct an integer of a given kind. *)
let kinteger (k: ikind) (i: int) = kinteger64 k (Int64.of_int i)

     
type offsetAcc = 
    { oaFirstFree: int;        (* The first free bit *)
      oaLastFieldStart: int;   (* Where the previous field started *)
      oaLastFieldWidth: int;   (* The width of the previous field. Might not 
                                * be same as FirstFree - FieldStart because 
                                * of internal padding *)
      oaPrevBitPack: (int * ikind * int) option; (* If the previous fields 
                                                   * were packed bitfields, 
                                                   * the bit where packing 
                                                   * has started, the ikind 
                                                   * of the bitfield and the 
                                                   * width of the ikind *)
    } 


(* GCC version *)
(* Does not use the sofar.oaPrevBitPack *)
let rec offsetOfFieldAcc_GCC (fi: fieldinfo) 
                             (sofar: offsetAcc) : offsetAcc = 
  (* field type *)
  let ftype = unrollType fi.ftype in
  let ftypeAlign = 8 * alignOf_int ftype in
  let ftypeBits = bitsSizeOf ftype in
(*
  if fi.fcomp.cname = "comp2468" ||
     fi.fcomp.cname = "comp2469" ||
     fi.fcomp.cname = "comp2470" ||
     fi.fcomp.cname = "comp2471" ||
     fi.fcomp.cname = "comp2472" ||
     fi.fcomp.cname = "comp2473" ||
     fi.fcomp.cname = "comp2474" ||
     fi.fcomp.cname = "comp2475" ||
     fi.fcomp.cname = "comp2476" ||
     fi.fcomp.cname = "comp2477" ||
     fi.fcomp.cname = "comp2478" then

    ignore (E.log "offsetOfFieldAcc_GCC(%s of %s:%a%a,firstFree=%d,pack=%a)\n" 
              fi.fname fi.fcomp.cname 
              d_type ftype
              insert
              (match fi.fbitfield with
                None -> nil
              | Some wdthis -> dprintf ":%d" wdthis)
              sofar.oaFirstFree 
              insert
              (match sofar.oaPrevBitPack with 
                None -> text "None"
              | Some (packstart, _, wdpack) -> 
                  dprintf "Some(packstart=%d,wd=%d)"
                    packstart wdpack));
*)
  match ftype, fi.fbitfield with
    (* A width of 0 means that we must end the current packing. It seems that 
     * GCC pads only up to the alignment boundary for the type of this field. 
     * *)
  | _, Some 0 -> 
      let firstFree      = addTrailing sofar.oaFirstFree ftypeAlign in
      { oaFirstFree      = firstFree;
        oaLastFieldStart = firstFree;
        oaLastFieldWidth = 0;
        oaPrevBitPack    = None }

    (* A bitfield cannot span more alignment boundaries of its type than the 
     * type itself *)
  | _, Some wdthis 
      when (sofar.oaFirstFree + wdthis + ftypeAlign - 1) / ftypeAlign 
            - sofar.oaFirstFree / ftypeAlign > ftypeBits / ftypeAlign -> 
          let start = addTrailing sofar.oaFirstFree ftypeAlign in    
          { oaFirstFree      = start + wdthis;
            oaLastFieldStart = start;
            oaLastFieldWidth = wdthis;
            oaPrevBitPack    = None }
        
   (* Try a simple method. Just put the field down *)
  | _, Some wdthis -> 
      { oaFirstFree      = sofar.oaFirstFree + wdthis;
        oaLastFieldStart = sofar.oaFirstFree; 
        oaLastFieldWidth = wdthis;
        oaPrevBitPack    = None
      } 

     (* Non-bitfield *)
  | _, None -> 
      (* Align this field *)
      let newStart = addTrailing sofar.oaFirstFree ftypeAlign  in
      { oaFirstFree = newStart + ftypeBits;
        oaLastFieldStart = newStart;
        oaLastFieldWidth = ftypeBits;
        oaPrevBitPack = None;
      } 

(* MSVC version *)
and offsetOfFieldAcc_MSVC (fi: fieldinfo) 
                              (sofar: offsetAcc) : offsetAcc = 
  (* field type *)
  let ftype = unrollType fi.ftype in
  let ftypeAlign = 8 * alignOf_int ftype in
  let ftypeBits = bitsSizeOf ftype in
(*
  ignore (E.log "offsetOfFieldAcc_MSVC(%s of %s:%a%a,firstFree=%d, pack=%a)\n" 
            fi.fname fi.fcomp.cname 
            d_type ftype
            insert
            (match fi.fbitfield with
              None -> nil
            | Some wdthis -> dprintf ":%d" wdthis)
            sofar.oaFirstFree 
            insert
            (match sofar.oaPrevBitPack with 
              None -> text "None"
            | Some (prevpack, _, wdpack) -> dprintf "Some(prev=%d,wd=%d)"
                  prevpack wdpack));
*)
  match ftype, fi.fbitfield, sofar.oaPrevBitPack with
    (* Ignore zero-width bitfields that come after non-bitfields *)
  | TInt (ikthis, _), Some 0, None -> 
      let firstFree      = sofar.oaFirstFree in
      { oaFirstFree      = firstFree;
        oaLastFieldStart = firstFree;
        oaLastFieldWidth = 0;
        oaPrevBitPack    = None }

    (* If we are in a bitpack and we see a bitfield for a type with the 
     * different width than the pack, then we finish the pack and retry *)
  | _, Some _, Some (packstart, _, wdpack) when wdpack != ftypeBits ->
      let firstFree = 
        if sofar.oaFirstFree = packstart then packstart else
        packstart + wdpack
      in
      offsetOfFieldAcc_MSVC fi
        { oaFirstFree      = addTrailing firstFree ftypeAlign;
          oaLastFieldStart = sofar.oaLastFieldStart;
          oaLastFieldWidth = sofar.oaLastFieldWidth;
          oaPrevBitPack    = None }

    (* A width of 0 means that we must end the current packing. *)
  | TInt (ikthis, _), Some 0, Some (packstart, _, wdpack) -> 
      let firstFree = 
        if sofar.oaFirstFree = packstart then packstart else
        packstart + wdpack
      in
      let firstFree      = addTrailing firstFree ftypeAlign in
      { oaFirstFree      = firstFree;
        oaLastFieldStart = firstFree;
        oaLastFieldWidth = 0;
        oaPrevBitPack    = Some (firstFree, ikthis, ftypeBits) }

   (* Check for a bitfield that fits in the current pack after some other 
    * bitfields *)
  | TInt(ikthis, _), Some wdthis, Some (packstart, ikprev, wdpack)
      when  packstart + wdpack >= sofar.oaFirstFree + wdthis ->
              { oaFirstFree = sofar.oaFirstFree + wdthis;
                oaLastFieldStart = sofar.oaFirstFree; 
                oaLastFieldWidth = wdthis;
                oaPrevBitPack = sofar.oaPrevBitPack
              } 


  | _, _, Some (packstart, _, wdpack) -> (* Finish up the bitfield pack and 
                                          * restart. *)
      let firstFree = 
        if sofar.oaFirstFree = packstart then packstart else
        packstart + wdpack
      in
      offsetOfFieldAcc_MSVC fi
        { oaFirstFree      = addTrailing firstFree ftypeAlign;
          oaLastFieldStart = sofar.oaLastFieldStart;
          oaLastFieldWidth = sofar.oaLastFieldWidth;
          oaPrevBitPack    = None }

        (* No active bitfield pack. But we are seeing a bitfield. *)
  | TInt(ikthis, _), Some wdthis, None -> 
      let firstFree     = addTrailing sofar.oaFirstFree ftypeAlign in
      { oaFirstFree     = firstFree + wdthis;
        oaLastFieldStart = firstFree;
        oaLastFieldWidth = wdthis;
        oaPrevBitPack = Some (firstFree, ikthis, ftypeBits); }

     (* No active bitfield pack. Non-bitfield *)
  | _, None, None -> 
      (* Align this field *)
      let firstFree = addTrailing sofar.oaFirstFree ftypeAlign  in
      { oaFirstFree = firstFree + ftypeBits;
        oaLastFieldStart = firstFree;
        oaLastFieldWidth = ftypeBits;
        oaPrevBitPack = None;
      } 

  | _, Some _, None -> E.s (E.bug "offsetAcc")


and offsetOfFieldAcc ~(fi: fieldinfo) 
                     ~(sofar: offsetAcc) : offsetAcc = 
  if !msvcMode then offsetOfFieldAcc_MSVC fi sofar
  else offsetOfFieldAcc_GCC fi sofar

(* The size of a type, in bits. If struct or array then trailing padding is 
 * added *)
and bitsSizeOf t = 
  if not !initCIL_called then 
    E.s (E.error "You did not call Cil.initCIL before using the CIL library");
  match t with 
  | TInt (ik,_) -> bitsSizeOfInt ik
  | TFloat(FDouble, _) -> 8 * !theMachine.M.sizeof_double
  | TFloat(FLongDouble, _) -> 8 * !theMachine.M.sizeof_longdouble
  | TFloat _ -> 8 * !theMachine.M.sizeof_float
  | TEnum _ -> 8 * !theMachine.M.sizeof_enum
  | TPtr _ -> 8 * !theMachine.M.sizeof_ptr
  | TBuiltin_va_list _ -> 8 * !theMachine.M.sizeof_ptr
  | TNamed (t, _) -> bitsSizeOf t.ttype
  | TComp (comp, _) when comp.cfields == [] -> begin
      (* Empty structs are allowed in msvc mode *)
      if not comp.cdefined && not !msvcMode then
        raise (SizeOfError ("abstract type", t)) (*abstract type*)
      else
        0
  end

  | TComp (comp, _) when comp.cstruct -> (* Struct *)
        (* Go and get the last offset *)
      let startAcc = 
        { oaFirstFree = 0;
          oaLastFieldStart = 0;
          oaLastFieldWidth = 0;
          oaPrevBitPack = None;
        } in
      let lastoff = 
        List.fold_left (fun acc fi -> offsetOfFieldAcc ~fi ~sofar:acc) 
          startAcc comp.cfields 
      in
      if !msvcMode && lastoff.oaFirstFree = 0 && comp.cfields <> [] then
          (* On MSVC if we have just a zero-width bitfields then the length 
           * is 32 and is not padded  *)
        32
      else
        addTrailing lastoff.oaFirstFree (8 * alignOf_int t)
        
  | TComp (comp, _) -> (* when not comp.cstruct *)
        (* Get the maximum of all fields *)
      let startAcc = 
        { oaFirstFree = 0;
          oaLastFieldStart = 0;
          oaLastFieldWidth = 0;
          oaPrevBitPack = None;
        } in
      let max = 
        List.fold_left (fun acc fi -> 
          let lastoff = offsetOfFieldAcc ~fi ~sofar:startAcc in
          if lastoff.oaFirstFree > acc then
            lastoff.oaFirstFree else acc) 0 comp.cfields in
        (* Add trailing by simulating adding an extra field *)
      addTrailing max (8 * alignOf_int t)

  | TArray(t, Some len, _) -> begin
      match constFold true len with 
        Const(CInt64(l,_,_)) -> 
          addTrailing ((bitsSizeOf t) * (Int64.to_int l)) (8 * alignOf_int t)
      | _ -> raise (SizeOfError ("array non-constant length", t))
  end


  | TVoid _ -> 8 * !theMachine.M.sizeof_void
  | TFun _ when not !msvcMode -> (* On GCC the size of a function is defined *)
      8 * !theMachine.M.sizeof_fun

  | TArray (_, None, _) -> (* it seems that on GCC the size of such an 
                            * array is 0 *) 
      0

  | TFun _ -> raise (SizeOfError ("function", t))


and addTrailing nrbits roundto = 
    (nrbits + roundto - 1) land (lnot (roundto - 1))

and sizeOf t = 
  try
    integer ((bitsSizeOf t) lsr 3)
  with SizeOfError _ -> SizeOf(t)

 
and bitsOffset (baset: typ) (off: offset) : int * int = 
  let rec loopOff (baset: typ) (width: int) (start: int) = function
      NoOffset -> start, width
    | Index(e, off) -> begin
        let ei = 
          match isInteger e with
            Some i64 -> Int64.to_int i64
          | None -> raise (SizeOfError ("index not constant", baset))
        in
        let bt = 
          match unrollType baset with
            TArray(bt, _, _) -> bt
          | _ -> E.s (E.bug "bitsOffset: Index on a non-array")
        in
        let bitsbt = bitsSizeOf bt in
        loopOff bt bitsbt (start + ei * bitsbt) off
    end
    | Field(f, off) when not f.fcomp.cstruct -> 
        (* All union fields start at offset 0 *)
        loopOff f.ftype (bitsSizeOf f.ftype) start off

    | Field(f, off) -> 
        (* Construct a list of fields preceeding and including this one *)
        let prevflds = 
          let rec loop = function
              [] -> E.s (E.bug "bitsOffset: Cannot find field %s in %s\n" 
                           f.fname f.fcomp.cname)
            | fi' :: _ when fi' == f -> [fi']
            | fi' :: rest -> fi' :: loop rest
          in
          loop f.fcomp.cfields
        in
        let lastoff =
          List.fold_left (fun acc fi' -> offsetOfFieldAcc ~fi:fi' ~sofar:acc)
            { oaFirstFree      = 0; (* Start at 0 because each struct is done 
                                     * separately *)
              oaLastFieldStart = 0;
              oaLastFieldWidth = 0;
              oaPrevBitPack    = None } prevflds
        in
        (* ignore (E.log "Field %s of %s: start=%d, lastFieldStart=%d\n"
                  f.fname f.fcomp.cname start lastoff.oaLastFieldStart); *)
        loopOff f.ftype lastoff.oaLastFieldWidth 
               (start + lastoff.oaLastFieldStart) off
  in
  loopOff baset (bitsSizeOf baset) 0 off
        



(*** Constant folding. If machdep is true then fold even sizeof operations ***)
and constFold (machdep: bool) (e: exp) : exp = 
  match e with
    BinOp(bop, e1, e2, tres) -> constFoldBinOp machdep bop e1 e2 tres
  | UnOp(unop, e1, tres) -> begin
      try
        let tk = 
          match unrollType tres with
            TInt(ik, _) -> ik
          | TEnum _ -> IInt
          | _ -> raise Not_found (* probably a float *)
        in
        match constFold machdep e1 with
          Const(CInt64(i,ik,_)) -> begin
            match unop with 
              Neg -> kinteger64 tk (Int64.neg i)
            | BNot -> kinteger64 tk (Int64.lognot i)
            | LNot -> if i = Int64.zero then one else zero
            end
        | e1c -> UnOp(unop, e1c, tres)
      with Not_found -> e
  end
        (* Characters are integers *)
  | Const(CChr c) -> Const(charConstToInt c)
  | Const(CEnum (v, _, _)) -> constFold machdep v
  | SizeOf t when machdep -> begin
      try
        let bs = bitsSizeOf t in
        kinteger !kindOfSizeOf (bs / 8)
      with SizeOfError _ -> e
  end
  | SizeOfE e when machdep -> constFold machdep (SizeOf (typeOf e))
  | SizeOfStr s when machdep -> kinteger !kindOfSizeOf (1 + String.length s)
  | AlignOf t when machdep -> kinteger !kindOfSizeOf (alignOf_int t)
  | AlignOfE e when machdep -> begin
      (* The alignmetn of an expression is not always the alignment of its 
       * type. I know that for strings this is not true *)
      match e with 
        Const (CStr _) when not !msvcMode -> 
          kinteger !kindOfSizeOf !theMachine.M.alignof_str
            (* For an array, it is the alignment of the array ! *)
      | _ -> constFold machdep (AlignOf (typeOf e))
  end

  | CastE(it, 
          AddrOf (Mem (CastE(TPtr(bt, _), z)), off)) 
    when machdep && isZero z -> begin
      try 
        let start, width = bitsOffset bt off in
        if start mod 8 <> 0 then 
          E.s (error "Using offset of bitfield\n");
        constFold machdep (CastE(it, (integer (start / 8))))
      with SizeOfError _ -> e
  end

 
  | CastE (t, e) -> begin
      match constFold machdep e, unrollType t with 
        (* Might truncate silently *)
        Const(CInt64(i,k,_)), TInt(nk,_) -> 
          let i', _ = truncateInteger64 nk i in
          Const(CInt64(i', nk, None))
      | e', _ -> CastE (t, e')
  end

  | _ -> e

and constFoldBinOp (machdep: bool) bop e1 e2 tres = 
  let e1' = constFold machdep e1 in
  let e2' = constFold machdep e2 in
  if isIntegralType tres then begin
    let newe = 
      let rec mkInt = function
          Const(CChr c) -> Const(charConstToInt c)
        | Const(CEnum (v, s, ei)) -> mkInt v
        | CastE(TInt (ik, ta), e) -> begin
            match mkInt e with
              Const(CInt64(i, _, _)) -> 
                let i', _ = truncateInteger64 ik i in
                Const(CInt64(i', ik, None))

            | e' -> CastE(TInt(ik, ta), e')
        end
        | e -> e
      in
      let tk = 
        match unrollType tres with
          TInt(ik, _) -> ik
        | TEnum _ -> IInt
        | _ -> E.s (bug "constFoldBinOp")
      in
      (* See if the result is unsigned *)
      let isunsigned typ = not (isSigned typ) in
      let ge (unsigned: bool) (i1: int64) (i2: int64) : bool = 
        if unsigned then 
          let l1 = Int64.shift_right_logical i1 1 in
          let l2 = Int64.shift_right_logical i2 1 in (* Both positive now *)
          (l1 > l2) || (l1 = l2 && 
                        Int64.logand i1 Int64.one >= Int64.logand i2 Int64.one)
        else i1 >= i2
      in
      let shiftInBounds i2 =
        (* We only try to fold shifts if the second arg is positive and 
           less than 64.  Otherwise, the semantics are processor-dependent,
           so let the compiler sort it out. *)
        i2 >= Int64.zero && i2 < (Int64.of_int 64)
      in
      (* Assume that the necessary promotions have been done *)
      match bop, mkInt e1', mkInt e2' with
      | PlusA, Const(CInt64(z,_,_)), e2'' when z = Int64.zero -> e2''
      | PlusA, e1'', Const(CInt64(z,_,_)) when z = Int64.zero -> e1''
      | PlusPI, e1'', Const(CInt64(z,_,_)) when z = Int64.zero -> e1''
      | IndexPI, e1'', Const(CInt64(z,_,_)) when z = Int64.zero -> e1''
      | MinusPI, e1'', Const(CInt64(z,_,_)) when z = Int64.zero -> e1''
      | PlusA, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 -> 
          kinteger64 tk (Int64.add i1 i2)
      | MinusA, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 -> 
          kinteger64 tk (Int64.sub i1 i2)
      | Mult, Const(CInt64(i1,ik1,_)), Const(CInt64(i2,ik2,_)) when ik1 = ik2 -> 
          kinteger64 tk (Int64.mul i1 i2)
      | Mult, Const(CInt64(0L,_,_)), _ -> zero
      | Mult, Const(CInt64(1L,_,_)), e2'' -> e2''
      | Mult, _,    Const(CInt64(0L,_,_)) -> zero
      | Mult, e1'', Const(CInt64(1L,_,_)) -> e1''
      | Div, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 -> begin
          try kinteger64 tk (Int64.div i1 i2)
          with Division_by_zero -> BinOp(bop, e1', e2', tres)
      end
      | Div, e1'', Const(CInt64(1L,_,_)) -> e1''

      | Mod, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 -> begin
          try kinteger64 tk (Int64.rem i1 i2)
          with Division_by_zero -> BinOp(bop, e1', e2', tres) 
      end
      | BAnd, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 -> 
          kinteger64 tk (Int64.logand i1 i2)
      | BAnd, Const(CInt64(0L,_,_)), _ -> zero
      | BAnd, _, Const(CInt64(0L,_,_)) -> zero
      | BOr, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 -> 
          kinteger64 tk (Int64.logor i1 i2)
      | BOr, _, _ when isZero e1' -> e2'
      | BOr, _, _ when isZero e2' -> e1'
      | BXor, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 -> 
          kinteger64 tk (Int64.logxor i1 i2)

      | Shiftlt, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,_,_)) when shiftInBounds i2 -> 
          kinteger64 tk (Int64.shift_left i1 (Int64.to_int i2))
      | Shiftlt, Const(CInt64(0L,_,_)), _ -> zero
      | Shiftlt, e1'', Const(CInt64(0L,_,_)) -> e1''

      | Shiftrt, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,_,_)) when shiftInBounds i2 -> 
          if isunsigned ik1 then 
            kinteger64 tk (Int64.shift_right_logical i1 (Int64.to_int i2))
          else
            kinteger64 tk (Int64.shift_right i1 (Int64.to_int i2))
      | Shiftrt, Const(CInt64(0L,_,_)), _ -> zero
      | Shiftrt, e1'', Const(CInt64(0L,_,_)) -> e1''

      | Eq, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 -> 
          integer (if i1 = i2 then 1 else 0)
      | Ne, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 -> 
          integer (if i1 <> i2 then 1 else 0)
      | Le, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 ->
          integer (if ge (isunsigned ik1) i2 i1 then 1 else 0)

      | Ge, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 ->
          integer (if ge (isunsigned ik1) i1 i2 then 1 else 0)

      | Lt, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 ->
          integer (if i1 <> i2 && ge (isunsigned ik1) i2 i1 then 1 else 0)

      | Gt, Const(CInt64(i1,ik1,_)),Const(CInt64(i2,ik2,_)) when ik1 = ik2 ->
          integer (if i1 <> i2 && ge (isunsigned ik1) i1 i2 then 1 else 0)
      | LAnd, _, _ when isZero e1' || isZero e2' -> zero
      | LOr, _, _ when isZero e1' -> e2'
      | LOr, _, _ when isZero e2' -> e1'
      | _ -> BinOp(bop, e1', e2', tres)
    in
    if debugConstFold then 
      ignore (E.log "Folded %a to %a\n" 
                (!pd_exp) (BinOp(bop, e1', e2', tres)) (!pd_exp) newe);
    newe
  end else
    BinOp(bop, e1', e2', tres)



let parseInt (str: string) : exp = 
  let hasSuffix str = 
    let l = String.length str in
    fun s -> 
      let ls = String.length s in
      l >= ls && s = String.uppercase (String.sub str (l - ls) ls)
  in
  let l = String.length str in
  (* See if it is octal or hex *)
  let octalhex = (l >= 1 && String.get str 0 = '0') in 
  (* The length of the suffix and a list of possible kinds. See ISO 
  * 6.4.4.1 *)
  let hasSuffix = hasSuffix str in
  let suffixlen, kinds = 
    if hasSuffix "ULL" || hasSuffix "LLU" then 
      3, [IULongLong]
    else if hasSuffix "LL" then
      2, if octalhex then [ILongLong; IULongLong] else [ILongLong]
    else if hasSuffix "UL" || hasSuffix "LU" then
      2, [IULong; IULongLong]
    else if hasSuffix "L" then
      1, if octalhex then [ILong; IULong; ILongLong; IULongLong] 
      else [ILong; ILongLong]
    else if hasSuffix "U" then
      1, [IUInt; IULong; IULongLong]
    else if (!msvcMode && hasSuffix "UI64") then
      4, [IULongLong]
    else if (!msvcMode && hasSuffix "I64") then
      3, [ILongLong]
    else
      0, if octalhex || true (* !!! This is against the ISO but it 
        * is what GCC and MSVC do !!! *)
      then [IInt; IUInt; ILong; IULong; ILongLong; IULongLong]
      else [IInt; ILong; IUInt; ILongLong]
  in
  (* Convert to integer. To prevent overflow we do the arithmetic 
  * on Int64 and we take care of overflow. We work only with 
  * positive integers since the lexer takes care of the sign *)
  let rec toInt (base: int64) (acc: int64) (idx: int) : int64 = 
    let doAcc (what: int) = 
      let acc' = 
        Int64.add (Int64.mul base acc)  (Int64.of_int what) in
      if acc < Int64.zero || (* We clearly overflow since base >= 2 
      * *)
      (acc' > Int64.zero && acc' < acc) then 
        E.s (unimp "Cannot represent on 64 bits the integer %s\n"
               str)
      else
        toInt base acc' (idx + 1)
    in 
    if idx >= l - suffixlen then begin
      acc
    end else 
      let ch = String.get str idx in
      if ch >= '0' && ch <= '9' then
        doAcc (Char.code ch - Char.code '0')
      else if  ch >= 'a' && ch <= 'f'  then
        doAcc (10 + Char.code ch - Char.code 'a')
      else if  ch >= 'A' && ch <= 'F'  then
        doAcc (10 + Char.code ch - Char.code 'A')
      else
        E.s (bug "Invalid integer constant: %s (char %c at idx=%d)" 
               str ch idx)
  in
  try
    let i = 
      if octalhex then
        if l >= 2 && 
          (let c = String.get str 1 in c = 'x' || c = 'X') then
          toInt (Int64.of_int 16) Int64.zero 2
        else
          toInt (Int64.of_int 8) Int64.zero 1
      else
        toInt (Int64.of_int 10) Int64.zero 0
    in
    (* Construct an integer of the first kinds that fits. i must be 
    * POSITIVE  *)
    let res = 
      let rec loop = function
        | ((IInt | ILong) as k) :: _ 
                  when i < Int64.shift_left (Int64.of_int 1) 31 ->
                    kinteger64 k i
        | ((IUInt | IULong) as k) :: _ 
                  when i < Int64.shift_left (Int64.of_int 1) 32
          ->  kinteger64 k i
        | (ILongLong as k) :: _ 
                 when i <= Int64.sub (Int64.shift_left 
                                              (Int64.of_int 1) 63) 
                                          (Int64.of_int 1) 
          -> 
            kinteger64 k i
        | (IULongLong as k) :: _ -> kinteger64 k i
        | _ :: rest -> loop rest
        | [] -> E.s (E.unimp "Cannot represent the integer %s\n" 
                       (Int64.to_string i))
      in
      loop kinds 
    in
    res
  with e -> begin
    ignore (E.log "int_of_string %s (%s)\n" str 
              (Printexc.to_string e));
    zero
  end



let d_unop () u =
  match u with
    Neg -> text "-"
  | BNot -> text "~"
  | LNot -> text "!"

let d_binop () b =
  match b with
    PlusA | PlusPI | IndexPI -> text "+"
  | MinusA | MinusPP | MinusPI -> text "-"
  | Mult -> text "*"
  | Div -> text "/"
  | Mod -> text "%"
  | Shiftlt -> text "<<"
  | Shiftrt -> text ">>"
  | Lt -> text "<"
  | Gt -> text ">"
  | Le -> text "<="
  | Ge -> text ">="
  | Eq -> text "=="
  | Ne -> text "!="
  | BAnd -> text "&"
  | BXor -> text "^"
  | BOr -> text "|"
  | LAnd -> text "&&"
  | LOr -> text "||"

let invalidStmt = mkStmt (Instr [])

(** Construct a hash with the builtins *)
let gccBuiltins : (string, typ * typ list * bool) H.t = 
  let h = H.create 17 in
  (* See if we have builtin_va_list *)
  let hasbva = M.gccHas__builtin_va_list in
  let ulongLongType = TInt(IULongLong, []) in
  let floatType = TFloat(FFloat, []) in
  let longDoubleType = TFloat (FLongDouble, []) in
  let voidConstPtrType = TPtr(TVoid [Attr ("const", [])], []) in
  let sizeType = uintType in

  H.add h "__builtin___fprintf_chk" (intType, [ voidPtrType; intType; charConstPtrType ], true) (* first argument is really FILE*, not void*, but we don't want to build in the definition for FILE *);
  H.add h "__builtin___memcpy_chk" (voidPtrType, [ voidPtrType; voidConstPtrType; sizeType; sizeType ], false);
  H.add h "__builtin___memmove_chk" (voidPtrType, [ voidPtrType; voidConstPtrType; sizeType; sizeType ], false);
  H.add h "__builtin___mempcpy_chk" (voidPtrType, [ voidPtrType; voidConstPtrType; sizeType; sizeType ], false);
  H.add h "__builtin___memset_chk" (voidPtrType, [ voidPtrType; intType; sizeType; sizeType ], false);
  H.add h "__builtin___printf_chk" (intType, [ intType; charConstPtrType ], true);
  H.add h "__builtin___snprintf_chk" (intType, [ charPtrType; sizeType; intType; sizeType; charConstPtrType ], true);
  H.add h "__builtin___sprintf_chk" (intType, [ charPtrType; intType; sizeType; charConstPtrType ], true);
  H.add h "__builtin___stpcpy_chk" (charPtrType, [ charPtrType; charConstPtrType; sizeType ], false);
  H.add h "__builtin___strcat_chk" (charPtrType, [ charPtrType; charConstPtrType; sizeType ], false);
  H.add h "__builtin___strcpy_chk" (charPtrType, [ charPtrType; charConstPtrType; sizeType ], false);
  H.add h "__builtin___strncat_chk" (charPtrType, [ charPtrType; charConstPtrType; sizeType; sizeType ], false);
  H.add h "__builtin___strncpy_chk" (charPtrType, [ charPtrType; charConstPtrType; sizeType; sizeType ], false);
  H.add h "__builtin___vfprintf_chk" (intType, [ voidPtrType; intType; charConstPtrType; TBuiltin_va_list [] ], false) (* first argument is really FILE*, not void*, but we don't want to build in the definition for FILE *);
  H.add h "__builtin___vprintf_chk" (intType, [ intType; charConstPtrType; TBuiltin_va_list [] ], false);
  H.add h "__builtin___vsnprintf_chk" (intType, [ charPtrType; sizeType; intType; sizeType; charConstPtrType; TBuiltin_va_list [] ], false);
  H.add h "__builtin___vsprintf_chk" (intType, [ charPtrType; intType; sizeType; charConstPtrType; TBuiltin_va_list [] ], false);

  H.add h "__builtin_acos" (doubleType, [ doubleType ], false);
  H.add h "__builtin_acosf" (floatType, [ floatType ], false);
  H.add h "__builtin_acosl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_alloca" (voidPtrType, [ uintType ], false);
  
  H.add h "__builtin_asin" (doubleType, [ doubleType ], false);
  H.add h "__builtin_asinf" (floatType, [ floatType ], false);
  H.add h "__builtin_asinl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_atan" (doubleType, [ doubleType ], false);
  H.add h "__builtin_atanf" (floatType, [ floatType ], false);
  H.add h "__builtin_atanl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_atan2" (doubleType, [ doubleType; doubleType ], false);
  H.add h "__builtin_atan2f" (floatType, [ floatType; floatType ], false);
  H.add h "__builtin_atan2l" (longDoubleType, [ longDoubleType; 
                                                longDoubleType ], false);

  H.add h "__builtin_ceil" (doubleType, [ doubleType ], false);
  H.add h "__builtin_ceilf" (floatType, [ floatType ], false);
  H.add h "__builtin_ceill" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_cos" (doubleType, [ doubleType ], false);
  H.add h "__builtin_cosf" (floatType, [ floatType ], false);
  H.add h "__builtin_cosl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_cosh" (doubleType, [ doubleType ], false);
  H.add h "__builtin_coshf" (floatType, [ floatType ], false);
  H.add h "__builtin_coshl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_clz" (intType, [ uintType ], false);
  H.add h "__builtin_clzl" (intType, [ ulongType ], false);
  H.add h "__builtin_clzll" (intType, [ ulongLongType ], false);
  H.add h "__builtin_constant_p" (intType, [ intType ], false);
  H.add h "__builtin_ctz" (intType, [ uintType ], false);
  H.add h "__builtin_ctzl" (intType, [ ulongType ], false);
  H.add h "__builtin_ctzll" (intType, [ ulongLongType ], false);

  H.add h "__builtin_exp" (doubleType, [ doubleType ], false);
  H.add h "__builtin_expf" (floatType, [ floatType ], false);
  H.add h "__builtin_expl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_expect" (longType, [ longType; longType ], false);

  H.add h "__builtin_fabs" (doubleType, [ doubleType ], false);
  H.add h "__builtin_fabsf" (floatType, [ floatType ], false);
  H.add h "__builtin_fabsl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_ffs" (intType, [ uintType ], false);
  H.add h "__builtin_ffsl" (intType, [ ulongType ], false);
  H.add h "__builtin_ffsll" (intType, [ ulongLongType ], false);
  H.add h "__builtin_frame_address" (voidPtrType, [ uintType ], false);

  H.add h "__builtin_floor" (doubleType, [ doubleType ], false);
  H.add h "__builtin_floorf" (floatType, [ floatType ], false);
  H.add h "__builtin_floorl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_huge_val" (doubleType, [], false);
  H.add h "__builtin_huge_valf" (floatType, [], false);
  H.add h "__builtin_huge_vall" (longDoubleType, [], false);
  H.add h "__builtin_inf" (doubleType, [], false);
  H.add h "__builtin_inff" (floatType, [], false);
  H.add h "__builtin_infl" (longDoubleType, [], false);
  H.add h "__builtin_memcpy" (voidPtrType, [ voidPtrType; voidConstPtrType; uintType ], false);
  H.add h "__builtin_mempcpy" (voidPtrType, [ voidPtrType; voidConstPtrType; sizeType ], false);

  H.add h "__builtin_fmod" (doubleType, [ doubleType ], false);
  H.add h "__builtin_fmodf" (floatType, [ floatType ], false);
  H.add h "__builtin_fmodl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_frexp" (doubleType, [ doubleType; intPtrType ], false);
  H.add h "__builtin_frexpf" (floatType, [ floatType; intPtrType  ], false);
  H.add h "__builtin_frexpl" (longDoubleType, [ longDoubleType; 
                                                intPtrType  ], false);

  H.add h "__builtin_ldexp" (doubleType, [ doubleType; intType ], false);
  H.add h "__builtin_ldexpf" (floatType, [ floatType; intType  ], false);
  H.add h "__builtin_ldexpl" (longDoubleType, [ longDoubleType; 
                                                intType  ], false);

  H.add h "__builtin_log" (doubleType, [ doubleType ], false);
  H.add h "__builtin_logf" (floatType, [ floatType ], false);
  H.add h "__builtin_logl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_log10" (doubleType, [ doubleType ], false);
  H.add h "__builtin_log10f" (floatType, [ floatType ], false);
  H.add h "__builtin_log10l" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_modff" (floatType, [ floatType; 
                                          TPtr(floatType,[]) ], false);
  H.add h "__builtin_modfl" (longDoubleType, [ longDoubleType; 
                                               TPtr(longDoubleType, []) ], 
                             false);

  H.add h "__builtin_nan" (doubleType, [ charConstPtrType ], false);
  H.add h "__builtin_nanf" (floatType, [ charConstPtrType ], false);
  H.add h "__builtin_nanl" (longDoubleType, [ charConstPtrType ], false);
  H.add h "__builtin_nans" (doubleType, [ charConstPtrType ], false);
  H.add h "__builtin_nansf" (floatType, [ charConstPtrType ], false);
  H.add h "__builtin_nansl" (longDoubleType, [ charConstPtrType ], false);
  H.add h "__builtin_next_arg" ((if hasbva then TBuiltin_va_list [] else voidPtrType), [], false) (* When we parse builtin_next_arg we drop the second argument *);
  H.add h "__builtin_object_size" (sizeType, [ voidPtrType; intType ], false);

  H.add h "__builtin_parity" (intType, [ uintType ], false);
  H.add h "__builtin_parityl" (intType, [ ulongType ], false);
  H.add h "__builtin_parityll" (intType, [ ulongLongType ], false);

  H.add h "__builtin_popcount" (intType, [ uintType ], false);
  H.add h "__builtin_popcountl" (intType, [ ulongType ], false);
  H.add h "__builtin_popcountll" (intType, [ ulongLongType ], false);

  H.add h "__builtin_powi" (doubleType, [ doubleType; intType ], false);
  H.add h "__builtin_powif" (floatType, [ floatType; intType ], false);
  H.add h "__builtin_powil" (longDoubleType, [ longDoubleType; intType ], false);
  H.add h "__builtin_prefetch" (voidType, [ voidConstPtrType ], true);
  H.add h "__builtin_return" (voidType, [ voidConstPtrType ], false);
  H.add h "__builtin_return_address" (voidPtrType, [ uintType ], false);

  H.add h "__builtin_sin" (doubleType, [ doubleType ], false);
  H.add h "__builtin_sinf" (floatType, [ floatType ], false);
  H.add h "__builtin_sinl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_sinh" (doubleType, [ doubleType ], false);
  H.add h "__builtin_sinhf" (floatType, [ floatType ], false);
  H.add h "__builtin_sinhl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_sqrt" (doubleType, [ doubleType ], false);
  H.add h "__builtin_sqrtf" (floatType, [ floatType ], false);
  H.add h "__builtin_sqrtl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_stpcpy" (charPtrType, [ charPtrType; charConstPtrType ], false);
  H.add h "__builtin_strchr" (charPtrType, [ charPtrType; charType ], false);
  H.add h "__builtin_strcmp" (intType, [ charConstPtrType; charConstPtrType ], false);
  H.add h "__builtin_strcpy" (charPtrType, [ charPtrType; charConstPtrType ], false);
  H.add h "__builtin_strcspn" (uintType, [ charConstPtrType; charConstPtrType ], false);
  H.add h "__builtin_strncat" (charPtrType, [ charPtrType; charConstPtrType; sizeType ], false);
  H.add h "__builtin_strncmp" (intType, [ charConstPtrType; charConstPtrType; sizeType ], false);
  H.add h "__builtin_strncpy" (charPtrType, [ charPtrType; charConstPtrType; sizeType ], false);
  H.add h "__builtin_strspn" (intType, [ charConstPtrType; charConstPtrType ], false);
  H.add h "__builtin_strpbrk" (charPtrType, [ charConstPtrType; charConstPtrType ], false);
  (* When we parse builtin_types_compatible_p, we change its interface *)
  H.add h "__builtin_types_compatible_p"
                              (intType, [ uintType; (* Sizeof the type *)
                                          uintType  (* Sizeof the type *) ],
                               false);
  H.add h "__builtin_tan" (doubleType, [ doubleType ], false);
  H.add h "__builtin_tanf" (floatType, [ floatType ], false);
  H.add h "__builtin_tanl" (longDoubleType, [ longDoubleType ], false);

  H.add h "__builtin_tanh" (doubleType, [ doubleType ], false);
  H.add h "__builtin_tanhf" (floatType, [ floatType ], false);
  H.add h "__builtin_tanhl" (longDoubleType, [ longDoubleType ], false);


  if hasbva then begin
    H.add h "__builtin_va_end" (voidType, [ TBuiltin_va_list [] ], false);
    H.add h "__builtin_varargs_start" 
      (voidType, [ TBuiltin_va_list [] ], false);
    H.add h "__builtin_va_start" (voidType, [ TBuiltin_va_list [] ], false);
    (* When we parse builtin_stdarg_start, we drop the second argument *)
    H.add h "__builtin_stdarg_start" (voidType, [ TBuiltin_va_list []; ],
                                      false);
    (* When we parse builtin_va_arg we change its interface *)
    H.add h "__builtin_va_arg" (voidType, [ TBuiltin_va_list [];
                                            uintType; (* Sizeof the type *)
                                            voidPtrType; (* Ptr to res *) ],
                               false);
    H.add h "__builtin_va_copy" (voidType, [ TBuiltin_va_list [];
					     TBuiltin_va_list [] ],
                                false);
  end;
  h

(** Construct a hash with the builtins *)
let msvcBuiltins : (string, typ * typ list * bool) H.t = 
  (* These are empty for now but can be added to depending on the application*)
  let h = H.create 17 in
  (** Take a number of wide string literals *)
  H.add h "__annotation" (voidType, [ ], true);
  h



let pTypeSig : (typ -> typsig) ref =
  ref (fun _ -> E.s (E.bug "pTypeSig not initialized"))


(** A printer interface for CIL trees. Create instantiations of 
 * this type by specializing the class {!Cil.defaultCilPrinter}. *)
class type cilPrinter = object
  method pVDecl: unit -> varinfo -> doc
    (** Invoked for each variable declaration. Note that variable 
     * declarations are all the [GVar], [GVarDecl], [GFun], all the [varinfo] 
     * in formals of function types, and the formals and locals for function 
     * definitions. *)

  method pVar: varinfo -> doc
    (** Invoked on each variable use. *)

  method pLval: unit -> lval -> doc
    (** Invoked on each lvalue occurence *)

  method pOffset: doc -> offset -> doc
    (** Invoked on each offset occurence. The second argument is the base. *)

  method pInstr: unit -> instr -> doc
    (** Invoked on each instruction occurrence. *)

  method pStmt: unit -> stmt -> doc
    (** Control-flow statement. This is used by 
     * {!Cil.printGlobal} and by {!Cil.dumpGlobal}. *)

  method dStmt: out_channel -> int -> stmt -> unit
    (** Dump a control-flow statement to a file with a given indentation. This is used by 
     * {!Cil.dumpGlobal}. *)

  method dBlock: out_channel -> int -> block -> unit
    (** Dump a control-flow block to a file with a given indentation. This is 
     * used by {!Cil.dumpGlobal}. *)

  method pBlock: unit -> block -> Pretty.doc
    (** Print a block. *)

  method pGlobal: unit -> global -> doc
    (** Global (vars, types, etc.). This can be slow and is used only by 
     * {!Cil.printGlobal} but by {!Cil.dumpGlobal} for everything else except 
     * [GVar] and [GFun]. *)

  method dGlobal: out_channel -> global -> unit
    (** Dump a global to a file. This is used by {!Cil.dumpGlobal}. *)

  method pFieldDecl: unit -> fieldinfo -> doc
    (** A field declaration *)

  method pType: doc option -> unit -> typ -> doc  
  (* Use of some type in some declaration. The first argument is used to print 
   * the declared element, or is None if we are just printing a type with no 
   * name being decalred. Note that for structure/union and enumeration types 
   * the definition of the composite type is not visited. Use [vglob] to 
   * visit it.  *)

  method pAttr: attribute -> doc * bool
    (** Attribute. Also return an indication whether this attribute must be 
      * printed inside the __attribute__ list or not. *)
   
  method pAttrParam: unit -> attrparam -> doc 
    (** Attribute paramter *)
   
  method pAttrs: unit -> attributes -> doc
    (** Attribute lists *)

  method pLabel: unit -> label -> doc
    (** Label *)

  method pLineDirective: ?forcefile:bool -> location -> Pretty.doc
    (** Print a line-number. This is assumed to come always on an empty line. 
     * If the forcefile argument is present and is true then the file name 
     * will be printed always. Otherwise the file name is printed only if it 
     * is different from the last time time this function is called. The last 
     * file name is stored in a private field inside the cilPrinter object. *)

  method pStmtKind : stmt -> unit -> stmtkind -> Pretty.doc
    (** Print a statement kind. The code to be printed is given in the
     * {!Cil.stmtkind} argument.  The initial {!Cil.stmt} argument
     * records the statement which follows the one being printed;
     * {!Cil.defaultCilPrinterClass} uses this information to prettify
     * statement printing in certain special cases. *)

  method pExp: unit -> exp -> doc
    (** Print expressions *) 

  method pInit: unit -> init -> doc
    (** Print initializers. This can be slow and is used by 
     * {!Cil.printGlobal} but not by {!Cil.dumpGlobal}. *)

  method dInit: out_channel -> int -> init -> unit
    (** Dump a global to a file with a given indentation. This is used by 
     * {!Cil.dumpGlobal}. *)
end


class defaultCilPrinterClass : cilPrinter = object (self)
  val mutable currentFormals : varinfo list = []
  method private getLastNamedArgument (s: string) : exp =
    match List.rev currentFormals with 
      f :: _ -> Lval (var f)
    | [] -> 
        E.s (warn "Cannot find the last named argument when priting call to %s\n" s)

  (*** VARIABLES ***)
  (* variable use *)
  method pVar (v:varinfo) = text v.vname

  (* variable declaration *)
  method pVDecl () (v:varinfo) =
    let stom, rest = separateStorageModifiers v.vattr in
    (* First the storage modifiers *)
    text (if v.vinline then "__inline " else "")
      ++ d_storage () v.vstorage
      ++ (self#pAttrs () stom)
      ++ (self#pType (Some (text v.vname)) () v.vtype)
      ++ text " "
      ++ self#pAttrs () rest

  (*** L-VALUES ***)
  method pLval () (lv:lval) =  (* lval (base is 1st field)  *)
    match lv with
      Var vi, o -> self#pOffset (self#pVar vi) o
    | Mem e, Field(fi, o) ->
        self#pOffset
          ((self#pExpPrec arrowLevel () e) ++ text ("->" ^ fi.fname)) o
    | Mem e, o ->
        self#pOffset
          (text "(*" ++ self#pExpPrec derefStarLevel () e ++ text ")") o

  (** Offsets **)
  method pOffset (base: doc) = function
    | NoOffset -> base
    | Field (fi, o) -> 
        self#pOffset (base ++ text "." ++ text fi.fname) o
    | Index (e, o) ->
        self#pOffset (base ++ text "[" ++ self#pExp () e ++ text "]") o

  method private pLvalPrec (contextprec: int) () lv = 
    if getParenthLevel (Lval(lv)) >= contextprec then
      text "(" ++ self#pLval () lv ++ text ")"
    else
      self#pLval () lv

  (*** EXPRESSIONS ***)
  method pExp () (e: exp) : doc = 
    let level = getParenthLevel e in
    match e with
      Const(c) -> d_const () c
    | Lval(l) -> self#pLval () l
    | UnOp(u,e1,_) -> 
        (d_unop () u) ++ chr ' ' ++ (self#pExpPrec level () e1)
          
    | BinOp(b,e1,e2,_) -> 
        align 
          ++ (self#pExpPrec level () e1)
          ++ chr ' ' 
          ++ (d_binop () b)
          ++ chr ' '
          ++ (self#pExpPrec level () e2)
          ++ unalign

    | CastE(t,e) -> 
        text "(" 
          ++ self#pType None () t
          ++ text ")"
          ++ self#pExpPrec level () e

    | SizeOf (t) -> 
        text "sizeof(" ++ self#pType None () t ++ chr ')'
    | SizeOfE (e) ->  
        text "sizeof(" ++ self#pExp () e ++ chr ')'

    | SizeOfStr s -> 
        text "sizeof(" ++ d_const () (CStr s) ++ chr ')'

    | AlignOf (t) -> 
        text "__alignof__(" ++ self#pType None () t ++ chr ')'
    | AlignOfE (e) -> 
        text "__alignof__(" ++ self#pExp () e ++ chr ')'
    | AddrOf(lv) -> 
        text "& " ++ (self#pLvalPrec addrOfLevel () lv)
          
    | StartOf(lv) -> self#pLval () lv

  method private pExpPrec (contextprec: int) () (e: exp) = 
    let thisLevel = getParenthLevel e in
    let needParens =
      if thisLevel >= contextprec then
	true
      else if contextprec == bitwiseLevel then
        (* quiet down some GCC warnings *)
	thisLevel == additiveLevel || thisLevel == comparativeLevel
      else
	false
    in
    if needParens then
      chr '(' ++ self#pExp () e ++ chr ')'
    else
      self#pExp () e

  method pInit () = function 
      SingleInit e -> self#pExp () e
    | CompoundInit (t, initl) -> 
      (* We do not print the type of the Compound *)
(*
      let dinit e = d_init () e in
      dprintf "{@[%a@]}"
        (docList ~sep:(chr ',' ++ break) dinit) initl
*)
        let printDesignator = 
          if not !msvcMode then begin
            (* Print only for union when we do not initialize the first field *)
            match unrollType t, initl with
              TComp(ci, _), [(Field(f, NoOffset), _)] -> 
                if not (ci.cstruct) && ci.cfields != [] && 
                  (List.hd ci.cfields) != f then
                  true
                else
                  false
            | _ -> false
          end else 
            false 
        in
        let d_oneInit = function
            Field(f, NoOffset), i -> 
              (if printDesignator then 
                text ("." ^ f.fname ^ " = ") 
              else nil) ++ self#pInit () i
          | Index(e, NoOffset), i -> 
              (if printDesignator then 
                text "[" ++ self#pExp () e ++ text "] = " else nil) ++ 
                self#pInit () i
          | _ -> E.s (unimp "Trying to print malformed initializer")
        in
        chr '{' ++ (align 
                      ++ ((docList ~sep:(chr ',' ++ break) d_oneInit) () initl) 
                      ++ unalign)
          ++ chr '}'
(*
    | ArrayInit (_, _, il) -> 
        chr '{' ++ (align 
                      ++ ((docList (chr ',' ++ break) (self#pInit ())) () il) 
                      ++ unalign)
          ++ chr '}'
*)
  (* dump initializers to a file. *)
  method dInit (out: out_channel) (ind: int) (i: init) = 
    (* Dump an array *)
    let dumpArray (bt: typ) (il: 'a list) (getelem: 'a -> init) = 
      let onALine = (* How many elements on a line *)
        match unrollType bt with TComp _ | TArray _ -> 1 | _ -> 4
      in
      let rec outputElements (isfirst: bool) (room_on_line: int) = function
          [] -> output_string out "}"
        | (i: 'a) :: rest -> 
            if not isfirst then output_string out ", ";
            let new_room_on_line = 
              if room_on_line == 0 then begin 
                output_string out "\n"; output_string out (String.make ind ' ');
                onALine - 1
              end else 
                room_on_line - 1
            in
            self#dInit out (ind + 2) (getelem i);
            outputElements false new_room_on_line rest
      in
      output_string out "{ ";
      outputElements true onALine il
    in
    match i with 
      SingleInit e -> 
        fprint out !lineLength (indent ind (self#pExp () e))
    | CompoundInit (t, initl) -> begin 
        match unrollType t with 
          TArray(bt, _, _) -> 
            dumpArray bt initl (fun (_, i) -> i)
        | _ -> 
            (* Now a structure or a union *)
            fprint out !lineLength (indent ind (self#pInit () i))
    end
(*
    | ArrayInit (bt, len, initl) -> begin
        (* If the base type does not contain structs then use the pInit 
        match unrollType bt with 
          TComp _ | TArray _ -> 
            dumpArray bt initl (fun x -> x)
        | _ -> *)
            fprint out !lineLength (indent ind (self#pInit () i))
    end
*)
        
  (** What terminator to print after an instruction. sometimes we want to 
   * print sequences of instructions separated by comma *)
  val mutable printInstrTerminator = ";"

  (*** INSTRUCTIONS ****)
  method pInstr () (i:instr) =       (* imperative instruction *)
    match i with
    | Set(lv,e,l) -> begin
        (* Be nice to some special cases *)
        match e with
          BinOp((PlusA|PlusPI|IndexPI),Lval(lv'), Const(CInt64(one,_,_)),_)
            when Util.equals lv lv' && one = Int64.one && not !printCilAsIs ->
              self#pLineDirective l
                ++ self#pLval () lv
                ++ text (" ++" ^ printInstrTerminator)

        | BinOp((MinusA|MinusPI),Lval(lv'),
                Const(CInt64(one,_,_)), _) 
            when Util.equals lv lv' && one = Int64.one && not !printCilAsIs ->
                  self#pLineDirective l
                    ++ self#pLval () lv
                    ++ text (" --" ^ printInstrTerminator) 

        | BinOp((PlusA|PlusPI|IndexPI),Lval(lv'),Const(CInt64(mone,_,_)),_)
            when Util.equals lv lv' && mone = Int64.minus_one 
                && not !printCilAsIs ->
              self#pLineDirective l
                ++ self#pLval () lv
                ++ text (" --" ^ printInstrTerminator)

        | BinOp((PlusA|PlusPI|IndexPI|MinusA|MinusPP|MinusPI|BAnd|BOr|BXor|
          Mult|Div|Mod|Shiftlt|Shiftrt) as bop,
                Lval(lv'),e,_) when Util.equals lv lv' ->
                  self#pLineDirective l
                    ++ self#pLval () lv
                    ++ text " " ++ d_binop () bop
                    ++ text "= "
                    ++ self#pExp () e
                    ++ text printInstrTerminator
                    
        | _ ->
            self#pLineDirective l
              ++ self#pLval () lv
              ++ text " = "
              ++ self#pExp () e
              ++ text printInstrTerminator
              
    end
      (* In cabs2cil we have turned the call to builtin_va_arg into a 
       * three-argument call: the last argument is the address of the 
       * destination *)
    | Call(None, Lval(Var vi, NoOffset), [dest; SizeOf t; adest], l) 
        when vi.vname = "__builtin_va_arg" && not !printCilAsIs -> 
          let destlv = match stripCasts adest with 
            AddrOf destlv -> destlv
          | _ -> E.s (E.error "Encountered unexpected call to %s\n" vi.vname)
          in
          self#pLineDirective l
	    ++ self#pLval () destlv ++ text " = "
                   
            (* Now the function name *)
            ++ text "__builtin_va_arg"
            ++ text "(" ++ (align
                              (* Now the arguments *)
                              ++ self#pExp () dest 
                              ++ chr ',' ++ break 
                              ++ self#pType None () t
                              ++ unalign)
            ++ text (")" ^ printInstrTerminator)

      (* In cabs2cil we have dropped the last argument in the call to 
       * __builtin_stdarg_start. *)
    | Call(None, Lval(Var vi, NoOffset), [marker], l) 
        when vi.vname = "__builtin_stdarg_start" && not !printCilAsIs -> begin
          let last = self#getLastNamedArgument vi.vname in
          self#pInstr () (Call(None,Lval(Var vi,NoOffset),[marker; last],l))
        end

      (* In cabs2cil we have dropped the last argument in the call to 
       * __builtin_next_arg. *)
    | Call(res, Lval(Var vi, NoOffset), [ ], l) 
        when vi.vname = "__builtin_next_arg" && not !printCilAsIs -> begin
          let last = self#getLastNamedArgument vi.vname in
          self#pInstr () (Call(res,Lval(Var vi,NoOffset),[last],l))
        end

      (* In cparser we have turned the call to 
       * __builtin_types_compatible_p(t1, t2) into 
       * __builtin_types_compatible_p(sizeof t1, sizeof t2), so that we can
       * represent the types as expressions. 
       * Remove the sizeofs when printing. *)
    | Call(dest, Lval(Var vi, NoOffset), [SizeOf t1; SizeOf t2], l) 
        when vi.vname = "__builtin_types_compatible_p" && not !printCilAsIs -> 
        self#pLineDirective l
          (* Print the destination *)
        ++ (match dest with
              None -> nil
            | Some lv -> self#pLval () lv ++ text " = ")
          (* Now the call itself *)
        ++ dprintf "%s(%a, %a)" vi.vname
             (self#pType None) t1  (self#pType None) t2
        ++ text printInstrTerminator
    | Call(_, Lval(Var vi, NoOffset), _, l) 
        when vi.vname = "__builtin_types_compatible_p" && not !printCilAsIs -> 
        E.s (bug "__builtin_types_compatible_p: cabs2cil should have added sizeof to the arguments.")
          
    | Call(dest,e,args,l) ->
        self#pLineDirective l
          ++ (match dest with
            None -> nil
          | Some lv -> 
              self#pLval () lv ++ text " = " ++
                (* Maybe we need to print a cast *)
                (let destt = typeOfLval lv in
                match unrollType (typeOf e) with
                  TFun (rt, _, _, _) 
                      when not (Util.equals (!pTypeSig rt)
                                            (!pTypeSig destt)) ->
                    text "(" ++ self#pType None () destt ++ text ")"
                | _ -> nil))
          (* Now the function name *)
          ++ (let ed = self#pExp () e in
              match e with 
                Lval(Var _, _) -> ed
              | _ -> text "(" ++ ed ++ text ")")
          ++ text "(" ++ 
          (align
             (* Now the arguments *)
             ++ (docList ~sep:(chr ',' ++ break) 
                   (self#pExp ()) () args)
             ++ unalign)
        ++ text (")" ^ printInstrTerminator)

    | Asm(attrs, tmpls, outs, ins, clobs, l) ->
        if !msvcMode then
          self#pLineDirective l
            ++ text "__asm {"
            ++ (align
                  ++ (docList ~sep:line text () tmpls)
                  ++ unalign)
            ++ text ("}" ^ printInstrTerminator)
        else
          self#pLineDirective l
            ++ text ("__asm__ ") 
            ++ self#pAttrs () attrs 
            ++ text " ("
            ++ (align
                  ++ (docList ~sep:line
                        (fun x -> text ("\"" ^ escape_string x ^ "\""))
                        () tmpls)
                  ++
                  (if outs = [] && ins = [] && clobs = [] then
                    chr ':'
                else
                  (text ": "
                     ++ (docList ~sep:(chr ',' ++ break)
                           (fun (c, lv) ->
                             text ("\"" ^ escape_string c ^ "\" (")
                               ++ self#pLval () lv
                               ++ text ")") () outs)))
                ++
                  (if ins = [] && clobs = [] then
                    nil
                  else
                    (text ": "
                       ++ (docList ~sep:(chr ',' ++ break)
                             (fun (c, e) ->
                               text ("\"" ^ escape_string c ^ "\" (")
                                 ++ self#pExp () e
                                 ++ text ")") () ins)))
                  ++
                  (if clobs = [] then nil
                  else
                    (text ": "
                       ++ (docList ~sep:(chr ',' ++ break)
                             (fun c -> text ("\"" ^ escape_string c ^ "\""))
                             ()
                             clobs)))
                  ++ unalign)
            ++ text (")" ^ printInstrTerminator)
            

  (**** STATEMENTS ****)
  method pStmt () (s:stmt) =        (* control-flow statement *)
    self#pStmtNext invalidStmt () s

  method dStmt (out: out_channel) (ind: int) (s:stmt) : unit = 
    fprint out !lineLength (indent ind (self#pStmt () s))

  method dBlock (out: out_channel) (ind: int) (b:block) : unit = 
    fprint out !lineLength (indent ind (align ++ self#pBlock () b))

  method private pStmtNext (next: stmt) () (s: stmt) =
    (* print the labels *)
    ((docList ~sep:line (fun l -> self#pLabel () l)) () s.labels)
      (* print the statement itself. If the labels are non-empty and the
      * statement is empty, print a semicolon  *)
      ++ 
      (if s.skind = Instr [] && s.labels <> [] then
        text ";"
      else
        (if s.labels <> [] then line else nil) 
          ++ self#pStmtKind next () s.skind)

  method private pLabel () = function
      Label (s, _, true) -> text (s ^ ": ")
    | Label (s, _, false) -> text (s ^ ": /* CIL Label */ ")
    | Case (e, _) -> text "case " ++ self#pExp () e ++ text ": "
    | Default _ -> text "default: "

  (* The pBlock will put the unalign itself *)
  method pBlock () (blk: block) = 
    let rec dofirst () = function
        [] -> nil
      | [x] -> self#pStmtNext invalidStmt () x
      | x :: rest -> dorest nil x rest
    and dorest acc prev = function
        [] -> acc ++ (self#pStmtNext invalidStmt () prev)
      | x :: rest -> 
          dorest (acc ++ (self#pStmtNext x () prev) ++ line)
            x rest
    in
    (* Let the host of the block decide on the alignment. The d_block will 
     * pop the alignment as well  *)
    text "{" 
      ++ 
      (if blk.battrs <> [] then 
        self#pAttrsGen true blk.battrs
      else nil)
      ++ line
      ++ (dofirst () blk.bstmts)
      ++ unalign ++ line ++ text "}"

  
  (* Store here the name of the last file printed in a line number. This is 
   * private to the object *)
  val mutable lastFileName = ""
  (* Make sure that you only call self#pLineDirective on an empty line *)
  method pLineDirective ?(forcefile=false) l = 
    currentLoc := l;
    match !lineDirectiveStyle with
    | Some style when l.line > 0 ->
	let directive =
	  match style with
	  | LineComment -> text "//#line "
	  | LinePreprocessorOutput when not !msvcMode -> chr '#'
	  | _ -> text "#line"
	in
	let filename =
          if forcefile || l.file <> lastFileName then
	    begin
	      lastFileName <- l.file;
	      text " \"" ++ text l.file ++ text "\""
            end
	  else
	    nil
	in
	leftflush ++ directive ++ chr ' ' ++ num l.line ++ filename ++ line
    | _ ->
	nil


  method private pStmtKind (next: stmt) () = function
      Return(None, l) ->
        self#pLineDirective l
          ++ text "return;"

    | Return(Some e, l) ->
        self#pLineDirective l
          ++ text "return ("
          ++ self#pExp () e
          ++ text ");"
          
    | Goto (sref, l) -> begin
        (* Grab one of the labels *)
        let rec pickLabel = function
            [] -> None
          | Label (l, _, _) :: _ -> Some l
          | _ :: rest -> pickLabel rest
        in
        match pickLabel !sref.labels with
          Some l -> text ("goto " ^ l ^ ";")
        | None -> 
            ignore (error "Cannot find label for target of goto\n");
            text "goto __invalid_label;"
    end

    | Break l ->
        self#pLineDirective l
          ++ text "break;"

    | Continue l -> 
        self#pLineDirective l
          ++ text "continue;"

    | Instr il ->
        align
          ++ (docList ~sep:line (fun i -> self#pInstr () i) () il)
          ++ unalign

    | If(be,t,{bstmts=[];battrs=[]},l) when not !printCilAsIs ->
        self#pLineDirective l
          ++ text "if"
          ++ (align
                ++ text " ("
                ++ self#pExp () be
                ++ text ") "
                ++ self#pBlock () t)
          
    | If(be,t,{bstmts=[{skind=Goto(gref,_);labels=[]}];
                battrs=[]},l)
     when !gref == next && not !printCilAsIs ->
       self#pLineDirective l
         ++ text "if"
         ++ (align
               ++ text " ("
               ++ self#pExp () be
               ++ text ") "
               ++ self#pBlock () t)

    | If(be,{bstmts=[];battrs=[]},e,l) when not !printCilAsIs ->
        self#pLineDirective l
          ++ text "if"
          ++ (align
                ++ text " ("
                ++ self#pExp () (UnOp(LNot,be,intType))
                ++ text ") "
                ++ self#pBlock () e)

    | If(be,{bstmts=[{skind=Goto(gref,_);labels=[]}];
           battrs=[]},e,l)
      when !gref == next && not !printCilAsIs ->
        self#pLineDirective l
          ++ text "if"
          ++ (align
                ++ text " ("
                ++ self#pExp () (UnOp(LNot,be,intType))
                ++ text ") "
                ++ self#pBlock () e)
          
    | If(be,t,e,l) ->
        self#pLineDirective l
          ++ (align
                ++ text "if"
                ++ (align
                      ++ text " ("
                      ++ self#pExp () be
                      ++ text ") "
                      ++ self#pBlock () t)
                ++ text " "   (* sm: indent next code 2 spaces (was 4) *)
                ++ (align
                      ++ text "else "
                      ++ self#pBlock () e)
          ++ unalign)
          
    | Switch(e,b,_,l) ->
        self#pLineDirective l
          ++ (align
                ++ text "switch ("
                ++ self#pExp () e
                ++ text ") "
                ++ self#pBlock () b)

(*
    | Loop(b, l, _, _) -> begin
        (* Maybe the first thing is a conditional. Turn it into a WHILE *)
        try
          let term, bodystmts =
            let rec skipEmpty = function
                [] -> []
              | {skind=Instr [];labels=[]} :: rest -> skipEmpty rest
              | x -> x
            in
            (* Bill McCloskey: Do not remove the If if it has labels *)
            match skipEmpty b.bstmts with
              {skind=If(e,tb,fb,_); labels=[]} :: rest 
                                              when not !printCilAsIs -> begin
                match skipEmpty tb.bstmts, skipEmpty fb.bstmts with
                  [], {skind=Break _; labels=[]} :: _  -> e, rest
                | {skind=Break _; labels=[]} :: _, [] 
                                     -> UnOp(LNot, e, intType), rest
                | _ -> raise Not_found
              end
            | _ -> raise Not_found
          in
          self#pLineDirective l
            ++ text "wh"
            ++ (align
                  ++ text "ile ("
                  ++ self#pExp () term
                  ++ text ") "
                  ++ self#pBlock () {bstmts=bodystmts; battrs=b.battrs})

        with Not_found ->
          self#pLineDirective l
            ++ text "wh"
            ++ (align
                  ++ text "ile (1) "
                  ++ self#pBlock () b)
    end
*)

    | While (e, b, l) ->
        self#pLineDirective l
          ++ (align
                ++ text "while ("
                ++ self#pExp () e
                ++ text ") "
                ++ self#pBlock () b)

    | DoWhile (e, b, l) ->
        self#pLineDirective l
          ++ (align
                ++ text "do "
                ++ self#pBlock () b
                ++ text " while ("
                ++ self#pExp () e
                ++ text ");")

    | For (bInit, e, bIter, b, l) ->
	ignore (E.warn
		  "in for loops, the 1st and 3rd expressions are not printed");
          self#pLineDirective l
            ++ (align
                  ++ text "for ("
                  ++ text "/* ??? */"   (* self#pBlock () bInit *)
                  ++ text "; "
                  ++ self#pExp () e
                  ++ text "; "
                  ++ text "/* ??? */"   (* self#pBlock() bIter *)
                  ++ text ") "
                  ++ self#pBlock () b)

    | Block b -> align ++ self#pBlock () b
      
    | TryFinally (b, h, l) -> 
        self#pLineDirective l 
          ++ text "__try "
          ++ align 
          ++ self#pBlock () b
          ++ text " __fin" ++ align ++ text "ally "
          ++ self#pBlock () h

    | TryExcept (b, (il, e), h, l) -> 
        self#pLineDirective l 
          ++ text "__try "
          ++ align 
          ++ self#pBlock () b
          ++ text " __e" ++ align ++ text "xcept(" ++ line
          ++ align
          (* Print the instructions but with a comma at the end, instead of 
           * semicolon *)
          ++ (printInstrTerminator <- ","; 
              let res = 
                (docList ~sep:line (self#pInstr ())
                   () il) 
              in
              printInstrTerminator <- ";";
              res)
          ++ self#pExp () e
          ++ text ") " ++ unalign
          ++ self#pBlock () h


  (*** GLOBALS ***)
  method pGlobal () (g:global) : doc =       (* global (vars, types, etc.) *)
    match g with 
    | GFun (fundec, l) ->
        (* If the function has attributes then print a prototype because 
        * GCC cannot accept function attributes in a definition *)
        let oldattr = fundec.svar.vattr in
        (* Always pring the file name before function declarations *)
        let proto = 
          if oldattr <> [] then 
            (self#pLineDirective l) ++ (self#pVDecl () fundec.svar) 
              ++ chr ';' ++ line 
          else nil in
        (* Temporarily remove the function attributes *)
        fundec.svar.vattr <- [];
        let body = (self#pLineDirective ~forcefile:true l) 
                      ++ (self#pFunDecl () fundec) in
        fundec.svar.vattr <- oldattr;
        proto ++ body ++ line
          
    | GType (typ, l) ->
        self#pLineDirective ~forcefile:true l ++
          text "typedef "
          ++ (self#pType (Some (text typ.tname)) () typ.ttype)
          ++ text ";\n"

    | GEnumTag (enum, l) ->
        self#pLineDirective l ++
          text "enum" ++ align ++ text (" " ^ enum.ename) ++
          text " {" ++ line
          ++ (docList ~sep:(chr ',' ++ line)
                (fun (n,i, loc) -> 
                  text (n ^ " = ") 
                    ++ self#pExp () i)
                () enum.eitems)
          ++ unalign ++ line ++ text "} " 
          ++ self#pAttrs () enum.eattr ++ text";\n"

    | GEnumTagDecl (enum, l) -> (* This is a declaration of a tag *)
        self#pLineDirective l ++
          text ("enum " ^ enum.ename ^ ";\n")

    | GCompTag (comp, l) -> (* This is a definition of a tag *)
        let n = comp.cname in
        let su, su1, su2 =
          if comp.cstruct then "struct", "str", "uct"
          else "union",  "uni", "on"
        in
        let sto_mod, rest_attr = separateStorageModifiers comp.cattr in
        self#pLineDirective ~forcefile:true l ++
          text su1 ++ (align ++ text su2 ++ chr ' ' ++ (self#pAttrs () sto_mod)
                         ++ text n
                         ++ text " {" ++ line
                         ++ ((docList ~sep:line (self#pFieldDecl ())) () 
                               comp.cfields)
                         ++ unalign)
          ++ line ++ text "}" ++
          (self#pAttrs () rest_attr) ++ text ";\n"

    | GCompTagDecl (comp, l) -> (* This is a declaration of a tag *)
        self#pLineDirective l ++
          text (compFullName comp) ++ text ";\n"

    | GVar (vi, io, l) ->
        self#pLineDirective ~forcefile:true l ++
          self#pVDecl () vi
          ++ chr ' '
          ++ (match io.init with
            None -> nil
          | Some i -> text " = " ++ 
                (let islong = 
                  match i with
                    CompoundInit (_, il) when List.length il >= 8 -> true
                  | _ -> false 
                in
                if islong then 
                  line ++ self#pLineDirective l ++ text "  " 
                else nil) ++
                (self#pInit () i))
          ++ text ";\n"
      
    (* print global variable 'extern' declarations, and function prototypes *)    
    | GVarDecl (vi, l) ->
        self#pLineDirective l ++
          (self#pVDecl () vi)
          ++ text ";\n"

    | GAsm (s, l) ->
        self#pLineDirective l ++
          text ("__asm__(\"" ^ escape_string s ^ "\");\n")

    | GPragma (Attr(an, args), l) ->
        (* sm: suppress printing pragmas that gcc does not understand *)
        (* assume anything starting with "ccured" is ours *)
        (* also don't print the 'combiner' pragma *)
        (* nor 'cilnoremove' *)
        let suppress =
          not !print_CIL_Input && 
          not !msvcMode &&
          ((startsWith "box" an) ||
           (startsWith "ccured" an) ||
           (an = "merger") ||
           (an = "cilnoremove")) in
        let d =
	  match an, args with
	  | _, [] ->
              text an
	  | "weak", [ACons (symbol, [])] ->
	      text "weak " ++ text symbol
	  | _ ->
            text (an ^ "(")
              ++ docList ~sep:(chr ',') (self#pAttrParam ()) () args
              ++ text ")"
        in
        self#pLineDirective l 
          ++ (if suppress then text "/* " else text "")
          ++ (text "#pragma ")
          ++ d
          ++ (if suppress then text " */\n" else text "\n")

    | GText s  -> 
        if s <> "//" then 
          text s ++ text "\n"
        else
          nil


   method dGlobal (out: out_channel) (g: global) : unit = 
     (* For all except functions and variable with initializers, use the 
      * pGlobal *)
     match g with 
       GFun (fdec, l) -> 
         (* If the function has attributes then print a prototype because 
          * GCC cannot accept function attributes in a definition *)
         let oldattr = fdec.svar.vattr in
         let proto = 
           if oldattr <> [] then 
             (self#pLineDirective l) ++ (self#pVDecl () fdec.svar) 
               ++ chr ';' ++ line
           else nil in
         fprint out !lineLength
           (proto ++ (self#pLineDirective ~forcefile:true l));
         (* Temporarily remove the function attributes *)
         fdec.svar.vattr <- [];
         fprint out !lineLength (self#pFunDecl () fdec);               
         fdec.svar.vattr <- oldattr;
         output_string out "\n"

     | GVar (vi, {init = Some i}, l) -> begin
         fprint out !lineLength 
           (self#pLineDirective ~forcefile:true l ++
              self#pVDecl () vi
              ++ text " = " 
              ++ (let islong = 
                match i with
                  CompoundInit (_, il) when List.length il >= 8 -> true
                | _ -> false 
              in
              if islong then 
                line ++ self#pLineDirective l ++ text "  " 
              else nil)); 
         self#dInit out 3 i;
         output_string out ";\n"
     end

     | g -> fprint out !lineLength (self#pGlobal () g)

   method pFieldDecl () fi = 
     (self#pType
        (Some (text (if fi.fname = missingFieldName then "" else fi.fname)))
        () 
        fi.ftype)
       ++ text " "
       ++ (match fi.fbitfield with None -> nil 
       | Some i -> text ": " ++ num i ++ text " ")
       ++ self#pAttrs () fi.fattr
       ++ text ";"
       
  method private pFunDecl () f =
      self#pVDecl () f.svar
      ++  line
      ++ text "{ "
      ++ (align
            (* locals. *)
            ++ (docList ~sep:line (fun vi -> self#pVDecl () vi ++ text ";") 
                  () f.slocals)
            ++ line ++ line
            (* the body *)
            ++ ((* remember the declaration *) currentFormals <- f.sformals; 
                let body = self#pBlock () f.sbody in
                currentFormals <- [];
                body))
      ++ line
      ++ text "}"

  (***** PRINTING DECLARATIONS and TYPES ****)
    
  method pType (nameOpt: doc option) (* Whether we are declaring a name or 
                                      * we are just printing a type *)
               () (t:typ) =       (* use of some type *)
    let name = match nameOpt with None -> nil | Some d -> d in
    let printAttributes (a: attributes) = 
      let pa = self#pAttrs () a in
      match nameOpt with 
      | None when not !print_CIL_Input && not !msvcMode -> 
          (* Cannot print the attributes in this case because gcc does not 
           * like them here, except if we are printing for CIL, or for MSVC. 
           * In fact, for MSVC we MUST print attributes such as __stdcall *)
          if pa = nil then nil else 
          text "/*" ++ pa ++ text "*/"
      | _ -> pa
    in
    match t with 
      TVoid a ->
        text "void"
          ++ self#pAttrs () a 
          ++ text " " 
          ++ name

    | TInt (ikind,a) -> 
        d_ikind () ikind 
          ++ self#pAttrs () a 
          ++ text " "
          ++ name

    | TFloat(fkind, a) -> 
        d_fkind () fkind 
          ++ self#pAttrs () a 
          ++ text " " 
          ++ name

    | TComp (comp, a) -> (* A reference to a struct *)
        let su = if comp.cstruct then "struct" else "union" in
        text (su ^ " " ^ comp.cname ^ " ") 
          ++ self#pAttrs () a 
          ++ name
          
    | TEnum (enum, a) -> 
        text ("enum " ^ enum.ename ^ " ")
          ++ self#pAttrs () a 
          ++ name
    | TPtr (bt, a)  -> 
        (* Parenthesize the ( * attr name) if a pointer to a function or an 
         * array. However, on MSVC the __stdcall modifier must appear right 
         * before the pointer constructor "(__stdcall *f)". We push them into 
         * the parenthesis. *)
        let (paren: doc option), (bt': typ) = 
          match bt with 
            TFun(rt, args, isva, fa) when !msvcMode -> 
              let an, af', at = partitionAttributes ~default:AttrType fa in
              (* We take the af' and we put them into the parentheses *)
              Some (text "(" ++ printAttributes af'), 
              TFun(rt, args, isva, addAttributes an at)

          | TFun _ | TArray _ -> Some (text "("), bt

          | _ -> None, bt
        in
        let name' = text "*" ++ printAttributes a ++ name in
        let name'' = (* Put the parenthesis *)
          match paren with 
            Some p -> p ++ name' ++ text ")" 
          | _ -> name' 
        in
        self#pType 
          (Some name'')
          () 
          bt'

    | TArray (elemt, lo, a) -> 
        (* ignore the const attribute for arrays *)
        let a' = dropAttributes [ "const" ] a in 
        let name' = 
          if a' == [] then name else
          if nameOpt == None then printAttributes a' else 
          text "(" ++ printAttributes a' ++ name ++ text ")" 
        in
        self#pType 
          (Some (name'
                   ++ text "[" 
                   ++ (match lo with None -> nil | Some e -> self#pExp () e)
                   ++ text "]"))
          ()
          elemt
          
    | TFun (restyp, args, isvararg, a) -> 
        let name' = 
          if a == [] then name else 
          if nameOpt == None then printAttributes a else
          text "(" ++ printAttributes a ++ name ++ text ")" 
        in
        self#pType 
          (Some
             (name'
                ++ text "("
                ++ (align 
                      ++ 
                      (if args = Some [] && isvararg then 
                        text "..."
                      else
                        (if args = None then nil 
                        else if args = Some [] then text "void"
                        else 
                          let pArg (aname, atype, aattr) = 
                            let stom, rest = separateStorageModifiers aattr in
                            (* First the storage modifiers *)
                            (self#pAttrs () stom)
                              ++ (self#pType (Some (text aname)) () atype)
                              ++ text " "
                              ++ self#pAttrs () rest
                          in
                          (docList ~sep:(chr ',' ++ break) pArg) () 
                            (argsToList args))
                          ++ (if isvararg then break ++ text ", ..." else nil))
                      ++ unalign)
                ++ text ")"))
          ()
          restyp

  | TNamed (t, a) ->
      text t.tname ++ self#pAttrs () a ++ text " " ++ name

  | TBuiltin_va_list a -> 
      text "__builtin_va_list"
       ++ self#pAttrs () a 
        ++ text " " 
        ++ name


  (**** PRINTING ATTRIBUTES *********)
  method pAttrs () (a: attributes) = 
    self#pAttrsGen false a


  (* Print one attribute. Return also an indication whether this attribute 
   * should be printed inside the __attribute__ list *)
  method pAttr (Attr(an, args): attribute) : doc * bool =
    (* Recognize and take care of some known cases *)
    match an, args with 
      "const", [] -> text "const", false
          (* Put the aconst inside the attribute list *)
    | "aconst", [] when not !msvcMode -> text "__const__", true
    | "thread", [] when not !msvcMode -> text "__thread", false
(*
    | "used", [] when not !msvcMode -> text "__attribute_used__", false 
*)
    | "volatile", [] -> text "volatile", false
    | "restrict", [] -> text "__restrict", false
    | "missingproto", [] -> text "/* missing proto */", false
    | "cdecl", [] when !msvcMode -> text "__cdecl", false
    | "stdcall", [] when !msvcMode -> text "__stdcall", false
    | "fastcall", [] when !msvcMode -> text "__fastcall", false
    | "declspec", args when !msvcMode -> 
        text "__declspec(" 
          ++ docList (self#pAttrParam ()) () args
          ++ text ")", false
    | "w64", [] when !msvcMode -> text "__w64", false
    | "asm", args -> 
        text "__asm__(" 
          ++ docList (self#pAttrParam ()) () args
          ++ text ")", false
    (* we suppress printing mode(__si__) because it triggers an *)
    (* internal compiler error in all current gcc versions *)
    (* sm: I've now encountered a problem with mode(__hi__)... *)
    (* I don't know what's going on, but let's try disabling all "mode"..*)
    | "mode", [ACons(tag,[])] -> 
        text "/* mode(" ++ text tag ++ text ") */", false

    (* sm: also suppress "format" because we seem to print it in *)
    (* a way gcc does not like *)
    | "format", _ -> text "/* format attribute */", false

    (* sm: here's another one I don't want to see gcc warnings about.. *)
    | "mayPointToStack", _ when not !print_CIL_Input 
    (* [matth: may be inside another comment.]
      -> text "/*mayPointToStack*/", false 
    *)
      -> text "", false

    | _ -> (* This is the dafault case *)
        (* Add underscores to the name *)
        let an' = if !msvcMode then "__" ^ an else "__" ^ an ^ "__" in
        if args = [] then 
          text an', true
        else
          text (an' ^ "(") 
            ++ (docList (self#pAttrParam ()) () args)
            ++ text ")", 
          true

  method pAttrParam () = function 
    | AInt n -> num n
    | AStr s -> text ("\"" ^ escape_string s ^ "\"")
    | ACons(s, []) -> text s
    | ACons(s,al) ->
        text (s ^ "(")
          ++ (docList (self#pAttrParam ()) () al)
          ++ text ")"
    | ASizeOfE a -> text "sizeof(" ++ self#pAttrParam () a ++ text ")"
    | ASizeOf t -> text "sizeof(" ++ self#pType None () t ++ text ")"
    | ASizeOfS ts -> text "sizeof(<typsig>)"
    | AAlignOfE a -> text "__alignof__(" ++ self#pAttrParam () a ++ text ")"
    | AAlignOf t -> text "__alignof__(" ++ self#pType None () t ++ text ")"
    | AAlignOfS ts -> text "__alignof__(<typsig>)"
    | AUnOp(u,a1) -> 
        (d_unop () u) ++ text " (" ++ (self#pAttrParam () a1) ++ text ")"

    | ABinOp(b,a1,a2) -> 
        align 
          ++ text "(" 
          ++ (self#pAttrParam () a1)
          ++ text ") "
          ++ (d_binop () b)
          ++ break 
          ++ text " (" ++ (self#pAttrParam () a2) ++ text ") "
          ++ unalign
    | ADot (ap, s) -> (self#pAttrParam () ap) ++ text ("." ^ s)
          
  (* A general way of printing lists of attributes *)
  method private pAttrsGen (block: bool) (a: attributes) = 
    (* Scan all the attributes and separate those that must be printed inside 
     * the __attribute__ list *)
    let rec loop (in__attr__: doc list) = function
        [] -> begin 
          match in__attr__ with
            [] -> nil
          | _ :: _->
              (* sm: added 'forgcc' calls to not comment things out
               * if CIL is the consumer; this is to address a case
               * Daniel ran into where blockattribute(nobox) was being
               * dropped by the merger
               *)
              (if block then 
                text (" " ^ (forgcc "/*") ^ " __blockattribute__(")
               else
                 text "__attribute__((")

                ++ (docList ~sep:(chr ',' ++ break)
                      (fun a -> a)) () in__attr__
                ++ text ")"
                ++ (if block then text (forgcc "*/") else text ")")
        end
      | x :: rest -> 
          let dx, ina = self#pAttr x in
          if ina then 
            loop (dx :: in__attr__) rest
          else
            dx ++ text " " ++ loop in__attr__ rest
    in
    let res = loop [] a in
    if res = nil then
      res
    else
      text " " ++ res ++ text " "

end (* class defaultCilPrinterClass *)

let defaultCilPrinter = new defaultCilPrinterClass

(* Top-level printing functions *)
let printType (pp: cilPrinter) () (t: typ) : doc = 
  pp#pType None () t
  
let printExp (pp: cilPrinter) () (e: exp) : doc = 
  pp#pExp () e

let printLval (pp: cilPrinter) () (lv: lval) : doc = 
  pp#pLval () lv

let printGlobal (pp: cilPrinter) () (g: global) : doc = 
  pp#pGlobal () g

let dumpGlobal (pp: cilPrinter) (out: out_channel) (g: global) : unit = 
  pp#dGlobal out g

let printAttr (pp: cilPrinter) () (a: attribute) : doc = 
  let ad, _ = pp#pAttr a in ad

let printAttrs (pp: cilPrinter) () (a: attributes) : doc = 
  pp#pAttrs () a

let printInstr (pp: cilPrinter) () (i: instr) : doc = 
  pp#pInstr () i

let printStmt (pp: cilPrinter) () (s: stmt) : doc = 
  pp#pStmt () s

let printBlock (pp: cilPrinter) () (b: block) : doc = 
  (* We must add the alignment ourselves, beucase pBlock will pop it *)
  align ++ pp#pBlock () b

let dumpStmt (pp: cilPrinter) (out: out_channel) (ind: int) (s: stmt) : unit = 
  pp#dStmt out ind s

let dumpBlock (pp: cilPrinter) (out: out_channel) (ind: int) (b: block) : unit = 
  pp#dBlock out ind b

let printInit (pp: cilPrinter) () (i: init) : doc = 
  pp#pInit () i

let dumpInit (pp: cilPrinter) (out: out_channel) (ind: int) (i: init) : unit = 
  pp#dInit out ind i

(* Now define some short cuts *)
let d_exp () e = printExp defaultCilPrinter () e
let _ = pd_exp := d_exp
let d_lval () lv = printLval defaultCilPrinter () lv
let d_offset base () off = defaultCilPrinter#pOffset base off
let d_init () i = printInit defaultCilPrinter () i
let d_type () t = printType defaultCilPrinter () t
let d_global () g = printGlobal defaultCilPrinter () g
let d_attrlist () a = printAttrs defaultCilPrinter () a 
let d_attr () a = printAttr defaultCilPrinter () a
let d_attrparam () e = defaultCilPrinter#pAttrParam () e
let d_label () l = defaultCilPrinter#pLabel () l
let d_stmt () s = printStmt defaultCilPrinter () s
let d_block () b = printBlock defaultCilPrinter () b
let d_instr () i = printInstr defaultCilPrinter () i

let d_shortglobal () = function
    GPragma (Attr(an, _), _) -> dprintf "#pragma %s" an
  | GType (ti, _) -> dprintf "typedef %s" ti.tname
  | GVarDecl (vi, _) -> dprintf "declaration of %s" vi.vname
  | GVar (vi, _, _) -> dprintf "definition of %s" vi.vname
  | GCompTag(ci,_) -> dprintf "definition of %s" (compFullName ci)
  | GCompTagDecl(ci,_) -> dprintf "declaration of %s" (compFullName ci)
  | GEnumTag(ei,_) -> dprintf "definition of enum %s" ei.ename
  | GEnumTagDecl(ei,_) -> dprintf "declaration of enum %s" ei.ename
  | GFun(fd, _) -> dprintf "definition of %s" fd.svar.vname
  | GText _ -> text "GText"
  | GAsm _ -> text "GAsm"


(* sm: given an ordinary CIL object printer, yield one which
 * behaves the same, except it never prints #line directives
 * (this is useful for debugging printfs) *)
let dn_obj (func: unit -> 'a -> doc) : (unit -> 'a -> doc) =
begin
  (* construct the closure to return *)
  let theFunc () (obj:'a) : doc =
  begin
    let prevStyle = !lineDirectiveStyle in
    lineDirectiveStyle := None;
    let ret = (func () obj) in    (* call underlying printer *)
    lineDirectiveStyle := prevStyle;
    ret
  end in
  theFunc
end

(* now define shortcuts for the non-location-printing versions,
 * with the naming prefix "dn_" *)
let dn_exp       = (dn_obj d_exp)
let dn_lval      = (dn_obj d_lval)
(* dn_offset is missing because it has a different interface *)
let dn_init      = (dn_obj d_init)
let dn_type      = (dn_obj d_type)
let dn_global    = (dn_obj d_global)
let dn_attrlist  = (dn_obj d_attrlist)
let dn_attr      = (dn_obj d_attr)
let dn_attrparam = (dn_obj d_attrparam)
let dn_stmt      = (dn_obj d_stmt)
let dn_instr     = (dn_obj d_instr)


(* Now define a cilPlainPrinter *)
class plainCilPrinterClass =
  (* We keep track of the composite types that we have done to avoid
   * recursion *)
  let donecomps : (int, unit) H.t = H.create 13 in
  object (self)

  inherit defaultCilPrinterClass as super
  
  (*** PLAIN TYPES ***)
  method pType (dn: doc option) () (t: typ) = 
    match dn with 
      None -> self#pOnlyType () t
    | Some d -> d ++ text " : " ++ self#pOnlyType () t

 method private pOnlyType () = function 
     TVoid a -> dprintf "TVoid(@[%a@])" self#pAttrs a
   | TInt(ikind, a) -> dprintf "TInt(@[%a,@?%a@])" 
         d_ikind ikind self#pAttrs a
   | TFloat(fkind, a) -> 
       dprintf "TFloat(@[%a,@?%a@])" d_fkind fkind self#pAttrs a
   | TNamed (t, a) ->
       dprintf "TNamed(@[%s,@?%a,@?%a@])" 
         t.tname self#pOnlyType t.ttype self#pAttrs a
   | TPtr(t, a) -> dprintf "TPtr(@[%a,@?%a@])" self#pOnlyType t self#pAttrs a
   | TArray(t,l,a) -> 
       let dl = match l with 
         None -> text "None" | Some l -> dprintf "Some(@[%a@])" self#pExp l in
       dprintf "TArray(@[%a,@?%a,@?%a@])" 
         self#pOnlyType t insert dl self#pAttrs a
   | TEnum(enum,a) -> dprintf "Enum(%s,@[%a@])" enum.ename self#pAttrs a
   | TFun(tr,args,isva,a) -> 
       dprintf "TFun(@[%a,@?%a%s,@?%a@])"
         self#pOnlyType tr 
         insert 
         (if args = None then text "None"
         else (docList ~sep:(chr ',' ++ break) 
                 (fun (an,at,aa) -> 
                   dprintf "%s: %a" an self#pOnlyType at)) 
             () 
             (argsToList args))
         (if isva then "..." else "") self#pAttrs a
   | TComp (comp, a) -> 
       if H.mem donecomps comp.ckey then 
         dprintf "TCompLoop(%s %s, _, %a)" 
           (if comp.cstruct then "struct" else "union") comp.cname 
           self#pAttrs comp.cattr
       else begin
         H.add donecomps comp.ckey (); (* Add it before we do the fields *)
         dprintf "TComp(@[%s %s,@?%a,@?%a,@?%a@])" 
           (if comp.cstruct then "struct" else "union") comp.cname
           (docList ~sep:(chr ',' ++ break) 
              (fun f -> dprintf "%s : %a" f.fname self#pOnlyType f.ftype)) 
           comp.cfields
           self#pAttrs comp.cattr
           self#pAttrs a
       end
   | TBuiltin_va_list a -> 
       dprintf "TBuiltin_va_list(%a)" self#pAttrs a

    
  (* Some plain pretty-printers. Unlike the above these expose all the 
   * details of the internal representation *)
  method pExp () = function
    Const(c) -> 
      let d_plainconst () c = 
        match c with
          CInt64(i, ik, so) -> 
            dprintf "Int64(%s,%a,%s)" 
              (Int64.format "%d" i)
              d_ikind ik
              (match so with Some s -> s | _ -> "None")
        | CStr(s) -> 
            text ("CStr(\"" ^ escape_string s ^ "\")")
        | CWStr(s) -> 
            dprintf "CWStr(%a)" d_const c
              
        | CChr(c) -> text ("CChr('" ^ escape_char c ^ "')")
        | CReal(f, fk, so) -> 
            dprintf "CReal(%f, %a, %s)" 
              f
              d_fkind fk 
              (match so with Some s -> s | _ -> "None")
        | CEnum(_, s, _) -> text s
      in
      text "Const(" ++ d_plainconst () c ++ text ")"


  | Lval(lv) -> 
      text "Lval(" 
        ++ (align
              ++ self#pLval () lv
              ++ unalign)
        ++ text ")"
        
  | CastE(t,e) -> dprintf "CastE(@[%a,@?%a@])" self#pOnlyType t self#pExp e

  | UnOp(u,e1,_) -> 
      dprintf "UnOp(@[%a,@?%a@])"
        d_unop u self#pExp e1
          
  | BinOp(b,e1,e2,_) -> 
      let d_plainbinop () b =
        match b with
          PlusA -> text "PlusA"
        | PlusPI -> text "PlusPI"
        | IndexPI -> text "IndexPI"
        | MinusA -> text "MinusA"
        | MinusPP -> text "MinusPP"
        | MinusPI -> text "MinusPI"
        | _ -> d_binop () b
      in
      dprintf "%a(@[%a,@?%a@])" d_plainbinop b
        self#pExp e1 self#pExp e2

  | SizeOf (t) -> 
      text "sizeof(" ++ self#pType None () t ++ chr ')'
  | SizeOfE (e) -> 
      text "sizeofE(" ++ self#pExp () e ++ chr ')'
  | SizeOfStr (s) -> 
      text "sizeofStr(" ++ d_const () (CStr s) ++ chr ')'
  | AlignOf (t) -> 
      text "__alignof__(" ++ self#pType None () t ++ chr ')'
  | AlignOfE (e) -> 
      text "__alignof__(" ++ self#pExp () e ++ chr ')'

  | StartOf lv -> dprintf "StartOf(%a)" self#pLval lv
  | AddrOf (lv) -> dprintf "AddrOf(%a)" self#pLval lv



  method private d_plainoffset () = function
      NoOffset -> text "NoOffset"
    | Field(fi,o) -> 
        dprintf "Field(@[%s:%a,@?%a@])" 
          fi.fname self#pOnlyType fi.ftype self#d_plainoffset o
     | Index(e, o) -> 
         dprintf "Index(@[%a,@?%a@])" self#pExp e self#d_plainoffset o

  method pInit () = function
      SingleInit e -> dprintf "SI(%a)" d_exp e
    | CompoundInit (t, initl) -> 
        let d_plainoneinit (o, i) = 
          self#d_plainoffset () o ++ text " = " ++ self#pInit () i
        in
        dprintf "CI(@[%a,@?%a@])" self#pOnlyType t
          (docList ~sep:(chr ',' ++ break) d_plainoneinit) initl
(*
    | ArrayInit (t, len, initl) -> 
        let idx = ref (- 1) in
        let d_plainoneinit i = 
          incr idx;
          text "[" ++ num !idx ++ text "] = " ++ self#pInit () i
        in
        dprintf "AI(@[%a,%d,@?%a@])" self#pOnlyType t len
          (docList ~sep:(chr ',' ++ break) d_plainoneinit) initl
*)           
  method pLval () (lv: lval) =  
    match lv with 
    | Var vi, o -> dprintf "Var(@[%s,@?%a@])" vi.vname self#d_plainoffset o
    | Mem e, o -> dprintf "Mem(@[%a,@?%a@])" self#pExp e self#d_plainoffset o


end
let plainCilPrinter = new plainCilPrinterClass

(* And now some shortcuts *)
let d_plainexp () e = plainCilPrinter#pExp () e
let d_plaintype () t = plainCilPrinter#pType None () t
let d_plaininit () i = plainCilPrinter#pInit () i
let d_plainlval () l = plainCilPrinter#pLval () l

(* zra: this allows pretty printers not in cil.ml to
   be exposed to cilmain.ml *)
let printerForMaincil = ref defaultCilPrinter

let rec d_typsig () = function
    TSArray (ts, eo, al) -> 
      dprintf "TSArray(@[%a,@?%a,@?%a@])" 
        d_typsig ts 
        insert (text (match eo with None -> "None" 
                       | Some e -> "Some " ^ Int64.to_string e))
        d_attrlist al
  | TSPtr (ts, al) -> 
      dprintf "TSPtr(@[%a,@?%a@])"
        d_typsig ts d_attrlist al
  | TSComp (iss, name, al) -> 
      dprintf "TSComp(@[%s %s,@?%a@])"
        (if iss then "struct" else "union") name
        d_attrlist al
  | TSFun (rt, args, isva, al) -> 
      dprintf "TSFun(@[%a,@?%a,%b,@?%a@])"
        d_typsig rt
        (docList ~sep:(chr ',' ++ break) (d_typsig ())) args isva
        d_attrlist al
  | TSEnum (n, al) -> 
      dprintf "TSEnum(@[%s,@?%a@])"
        n d_attrlist al
  | TSBase t -> dprintf "TSBase(%a)" d_type t


let newVID () = 
  let t = !nextGlobalVID in 
  incr nextGlobalVID;
  t

   (* Make a varinfo. Used mostly as a helper function below  *)
let makeVarinfo global name typ =
  (* Strip const from type for locals *)
  let vi = 
    { vname = name;
      vid   = newVID ();
      vglob = global;
      vtype = if global then typ else typeRemoveAttributes ["const"] typ;
      vdecl = lu;
      vinline = false;
      vattr = [];
      vstorage = NoStorage;
      vaddrof = false;
      vreferenced = false;    (* sm *)
    } in
  vi
      
let copyVarinfo (vi: varinfo) (newname: string) : varinfo = 
  let vi' = {vi with vname = newname; vid = newVID () } in
  vi'

let makeLocal fdec name typ = (* a helper function *)
  fdec.smaxid <- 1 + fdec.smaxid;
  let vi = makeVarinfo false name typ in
  vi
  
   (* Make a local variable and add it to a function *)
let makeLocalVar fdec ?(insert = true) name typ =
  let vi = makeLocal fdec name typ in
  if insert then fdec.slocals <- fdec.slocals @ [vi];
  vi


let makeTempVar fdec ?(name = "__cil_tmp") typ : varinfo =
  let name = name ^ (string_of_int (1 + fdec.smaxid)) in
  makeLocalVar fdec name typ

 
  (* Set the formals and re-create the function name based on the information*)
let setFormals (f: fundec) (forms: varinfo list) = 
  f.sformals <- forms; (* Set the formals *)
  match unrollType f.svar.vtype with
    TFun(rt, _, isva, fa) -> 
      f.svar.vtype <- 
         TFun(rt, 
              Some (List.map (fun a -> (a.vname, a.vtype, a.vattr)) forms), 
              isva, fa)
  | _ -> E.s (E.bug "Set formals. %s does not have function type\n"
                f.svar.vname)
    
   (* Set the types of arguments and results as given by the function type 
    * passed as the second argument *)
let setFunctionType (f: fundec) (t: typ) = 
  match unrollType t with
    TFun (rt, Some args, va, a) -> 
      if List.length f.sformals <> List.length args then 
        E.s (E.bug "setFunctionType: number of arguments differs from the number of formals");
      (* Change the function type. *)
      f.svar.vtype <- t; 
      (* Change the sformals and we know that indirectly we'll change the 
       * function type *)
      List.iter2 
        (fun (an,at,aa) f -> 
          f.vtype <- at; f.vattr <- aa) 
        args f.sformals

  | _ -> E.s (E.bug "setFunctionType: not a function type")
      

   (* Set the types of arguments and results as given by the function type 
    * passed as the second argument *)
let setFunctionTypeMakeFormals (f: fundec) (t: typ) = 
  match unrollType t with
    TFun (rt, Some args, va, a) -> 
      if f.sformals <> [] then 
        E.s (E.warn "setFunctionTypMakeFormals called on function %s with some formals already"
               f.svar.vname);
      (* Change the function type. *)
      f.svar.vtype <- t; 
      f.sformals <- [];
      
      f.sformals <- List.map (fun (n,t,a) -> makeLocal f n t) args;

      setFunctionType f t

  | _ -> E.s (E.bug "setFunctionTypeMakeFormals: not a function type: %a"
             d_type t)
      

let setMaxId (f: fundec) = 
  f.smaxid <- List.length f.sformals + List.length f.slocals

  
  (* Make a formal variable for a function. Insert it in both the sformals 
   * and the type of the function. You can optionally specify where to insert 
   * this one. If where = "^" then it is inserted first. If where = "$" then 
   * it is inserted last. Otherwise where must be the name of a formal after 
   * which to insert this. By default it is inserted at the end. *)
let makeFormalVar fdec ?(where = "$") name typ : varinfo = 
  (* Search for the insertion place *)
  let thenewone = ref fdec.svar in (* Just a placeholder *)
  let makeit () : varinfo = 
    let vi = makeLocal fdec name typ in
    thenewone := vi;
    vi
  in
  let rec loopFormals = function
      [] -> 
        if where = "$" then [makeit ()]
        else E.s (E.error "makeFormalVar: cannot find insert-after formal %s"
                    where)
    | f :: rest when f.vname = where -> f :: makeit () :: rest
    | f :: rest -> f :: loopFormals rest
  in
  let newformals = 
    if where = "^" then makeit () :: fdec.sformals else 
    loopFormals fdec.sformals in
  setFormals fdec newformals;
  !thenewone

   (* Make a global variable. Your responsibility to make sure that the name
    * is unique *)
let makeGlobalVar name typ =
  let vi = makeVarinfo true name typ in
  vi


   (* Make an empty function *)
let emptyFunction name = 
  { svar  = makeGlobalVar name (TFun(voidType, Some [], false,[]));
    smaxid = 0;
    slocals = [];
    sformals = [];
    sbody = mkBlock [];
    smaxstmtid = None;
    sallstmts = [];
  } 



    (* A dummy function declaration handy for initialization *)
let dummyFunDec = emptyFunction "@dummy"
let dummyFile = 
  { globals = [];
    fileName = "<dummy>";
    globinit = None;
    globinitcalled = false;}

let saveBinaryFile (cil_file : file) (filename : string) =
  let outchan = open_out_bin filename in
  Marshal.to_channel outchan cil_file [] ;
  close_out outchan 

let saveBinaryFileChannel (cil_file : file) (outchan : out_channel) =
  Marshal.to_channel outchan cil_file [] 

let loadBinaryFile (filename : string) : file = 
  let inchan = open_in_bin filename in
  let cil_file = (Marshal.from_channel inchan : file) in
  close_in inchan ;
  cil_file


(* Take the name of a file and make a valid symbol name out of it. There are 
 * a few chanracters that are not valid in symbols *)
let makeValidSymbolName (s: string) = 
  let s = String.copy s in (* So that we can update in place *)
  let l = String.length s in
  for i = 0 to l - 1 do
    let c = String.get s i in
    let isinvalid = 
      match c with
        '-' | '.' -> true
      | _ -> false
    in
    if isinvalid then 
      String.set s i '_';
  done;
  s


(*** Define the visiting engine ****)
(* visit all the nodes in a Cil expression *)
let doVisit (vis: cilVisitor)
            (startvisit: 'a -> 'a visitAction) 
            (children: cilVisitor -> 'a -> 'a) 
            (node: 'a) : 'a = 
  let action = startvisit node in
  match action with
    SkipChildren -> node
  | ChangeTo node' -> node'
  | _ -> (* DoChildren and ChangeDoChildrenPost *)
      let nodepre = match action with
        ChangeDoChildrenPost (node', _) -> node'
      | _ -> node
      in
      let nodepost = children vis nodepre in
      match action with
        ChangeDoChildrenPost (_, f) -> f nodepost
      | _ -> nodepost

(* mapNoCopy is like map but avoid copying the list if the function does not 
 * change the elements. *)
let rec mapNoCopy (f: 'a -> 'a) = function
    [] -> []
  | (i :: resti) as li -> 
      let i' = f i in
      let resti' = mapNoCopy f resti in
      if i' != i || resti' != resti then i' :: resti' else li 

let rec mapNoCopyList (f: 'a -> 'a list) = function
    [] -> []
  | (i :: resti) as li -> 
      let il' = f i in
      let resti' = mapNoCopyList f resti in
      match il' with
        [i'] when i' == i && resti' == resti -> li
      | _ -> il' @ resti'

(* A visitor for lists *)
let doVisitList  (vis: cilVisitor)
                 (startvisit: 'a -> 'a list visitAction)
                 (children: cilVisitor -> 'a -> 'a)
                 (node: 'a) : 'a list = 
  let action = startvisit node in
  match action with
    SkipChildren -> [node]
  | ChangeTo nodes' -> nodes'
  | _ -> 
      let nodespre = match action with
        ChangeDoChildrenPost (nodespre, _) -> nodespre
      | _ -> [node]
      in
      let nodespost = mapNoCopy (children vis) nodespre in
      match action with
        ChangeDoChildrenPost (_, f) -> f nodespost
      | _ -> nodespost
  
let debugVisit = false

let rec visitCilExpr (vis: cilVisitor) (e: exp) : exp = 
  doVisit vis vis#vexpr childrenExp e
and childrenExp (vis: cilVisitor) (e: exp) : exp = 
  let vExp e = visitCilExpr vis e in
  let vTyp t = visitCilType vis t in
  let vLval lv = visitCilLval vis lv in
  match e with
  | Const (CEnum(v, s, ei)) -> 
      let v' = vExp v in 
      if v' != v then Const (CEnum(v', s, ei)) else e

  | Const _ -> e
  | SizeOf t -> 
      let t'= vTyp t in 
      if t' != t then SizeOf t' else e
  | SizeOfE e1 -> 
      let e1' = vExp e1 in
      if e1' != e1 then SizeOfE e1' else e
  | SizeOfStr s -> e

  | AlignOf t -> 
      let t' = vTyp t in
      if t' != t then AlignOf t' else e
  | AlignOfE e1 -> 
      let e1' = vExp e1 in
      if e1' != e1 then AlignOfE e1' else e
  | Lval lv -> 
      let lv' = vLval lv in
      if lv' != lv then Lval lv' else e
  | UnOp (uo, e1, t) -> 
      let e1' = vExp e1 in let t' = vTyp t in
      if e1' != e1 || t' != t then UnOp(uo, e1', t') else e
  | BinOp (bo, e1, e2, t) -> 
      let e1' = vExp e1 in let e2' = vExp e2 in let t' = vTyp t in
      if e1' != e1 || e2' != e2 || t' != t then BinOp(bo, e1',e2',t') else e
  | CastE (t, e1) ->           
      let t' = vTyp t in let e1' = vExp e1 in
      if t' != t || e1' != e1 then CastE(t', e1') else e
  | AddrOf lv -> 
      let lv' = vLval lv in
      if lv' != lv then AddrOf lv' else e
  | StartOf lv -> 
      let lv' = vLval lv in
      if lv' != lv then StartOf lv' else e

and visitCilInit (vis: cilVisitor) (i: init) : init = 
  doVisit vis vis#vinit childrenInit i
and childrenInit (vis: cilVisitor) (i: init) : init = 
  let fExp e = visitCilExpr vis e in
  let fInit i = visitCilInit vis i in
  let fTyp t = visitCilType vis t in
  match i with
  | SingleInit e -> 
      let e' = fExp e in
      if e' != e then SingleInit e' else i
  | CompoundInit (t, initl) ->
      let t' = fTyp t in
      (* Collect the new initializer list, in reverse. We prefer two 
       * traversals to ensure tail-recursion. *)
      let newinitl : (offset * init) list ref = ref [] in
      (* Keep track whether the list has changed *)
      let hasChanged = ref false in
      let doOneInit ((o, i) as oi) = 
        let o' = visitCilInitOffset vis o in    (* use initializer version *)
        let i' = fInit i in
        let newio = 
          if o' != o || i' != i then 
            begin hasChanged := true; (o', i') end else oi 
        in
        newinitl := newio :: !newinitl
      in
      List.iter doOneInit initl;
      let initl' = if !hasChanged then List.rev !newinitl else initl in
      if t' != t || initl' != initl then CompoundInit (t', initl') else i
  
and visitCilLval (vis: cilVisitor) (lv: lval) : lval =
  doVisit vis vis#vlval childrenLval lv
and childrenLval (vis: cilVisitor) (lv: lval) : lval =  
  (* and visit its subexpressions *)
  let vExp e = visitCilExpr vis e in
  let vOff off = visitCilOffset vis off in
  match lv with
    Var v, off ->
      let v'   = doVisit vis vis#vvrbl (fun _ x -> x) v in
      let off' = vOff off in
      if v' != v || off' != off then Var v', off' else lv
  | Mem e, off -> 
      let e' = vExp e in
      let off' = vOff off in
      if e' != e || off' != off then Mem e', off' else lv

and visitCilOffset (vis: cilVisitor) (off: offset) : offset =
  doVisit vis vis#voffs childrenOffset off
and childrenOffset (vis: cilVisitor) (off: offset) : offset =
  let vOff off = visitCilOffset vis off in
  match off with
    Field (f, o) -> 
      let o' = vOff o in
      if o' != o then Field (f, o') else off
  | Index (e, o) -> 
      let e' = visitCilExpr vis e in
      let o' = vOff o in
      if e' != e || o' != o then Index (e', o') else off
  | NoOffset -> off

(* sm: for offsets in initializers, the 'startvisit' will be the
 * vinitoffs method, but we can re-use the childrenOffset from
 * above since recursive offsets are visited by voffs.  (this point
 * is moot according to cil.mli which claims the offsets in 
 * initializers will never recursively contain offsets)
 *)
and visitCilInitOffset (vis: cilVisitor) (off: offset) : offset =
  doVisit vis vis#vinitoffs childrenOffset off

and visitCilInstr (vis: cilVisitor) (i: instr) : instr list =
  let oldloc = !currentLoc in
  currentLoc := (get_instrLoc i);
  assertEmptyQueue vis;
  let res = doVisitList vis vis#vinst childrenInstr i in
  currentLoc := oldloc;
  (* See if we have accumulated some instructions *)
  vis#unqueueInstr () @ res

and childrenInstr (vis: cilVisitor) (i: instr) : instr =
  let fExp = visitCilExpr vis in
  let fLval = visitCilLval vis in
  match i with
  | Set(lv,e,l) -> 
      let lv' = fLval lv in let e' = fExp e in
      if lv' != lv || e' != e then Set(lv',e',l) else i
  | Call(None,f,args,l) -> 
      let f' = fExp f in let args' = mapNoCopy fExp args in
      if f' != f || args' != args then Call(None,f',args',l) else i
  | Call(Some lv,fn,args,l) -> 
      let lv' = fLval lv in let fn' = fExp fn in 
      let args' = mapNoCopy fExp args in
      if lv' != lv || fn' != fn || args' != args 
      then Call(Some lv', fn', args', l) else i

  | Asm(sl,isvol,outs,ins,clobs,l) -> 
      let outs' = mapNoCopy (fun ((s,lv) as pair) -> 
                               let lv' = fLval lv in
                               if lv' != lv then (s,lv') else pair) outs in
      let ins'  = mapNoCopy (fun ((s,e) as pair) -> 
                               let e' = fExp e in
                               if e' != e then (s,e') else pair) ins in
      if outs' != outs || ins' != ins then
        Asm(sl,isvol,outs',ins',clobs,l) else i


(* visit all nodes in a Cil statement tree in preorder *)
and visitCilStmt (vis: cilVisitor) (s: stmt) : stmt =
  let oldloc = !currentLoc in
  currentLoc := (get_stmtLoc s.skind) ;
  assertEmptyQueue vis;
  let toPrepend : instr list ref = ref [] in (* childrenStmt may add to this *)
  let res = doVisit vis vis#vstmt (childrenStmt toPrepend) s in
  (* Now see if we have saved some instructions *)
  toPrepend := !toPrepend @ vis#unqueueInstr ();
  (match !toPrepend with 
    [] -> () (* Return the same statement *)
  | _ -> 
      (* Make our statement contain the instructions to prepend *)
      res.skind <- Block { battrs = []; bstmts = [ mkStmt (Instr !toPrepend);
                                                   mkStmt res.skind ] });
  currentLoc := oldloc;
  res
  
and childrenStmt (toPrepend: instr list ref) (vis:cilVisitor) (s:stmt): stmt =
  let fExp e = (visitCilExpr vis e) in
  let fBlock b = visitCilBlock vis b in
  let fInst i = visitCilInstr vis i in
  (* Just change the statement kind *)
  let skind' = 
    match s.skind with
      Break _ | Continue _ | Goto _ | Return (None, _) -> s.skind
    | Return (Some e, l) -> 
        let e' = fExp e in
        if e' != e then Return (Some e', l) else s.skind
(*
    | Loop (b, l, s1, s2) -> 
        let b' = fBlock b in
        if b' != b then Loop (b', l, s1, s2) else s.skind
*)
    | While (e, b, l) ->
	let e' = fExp e in 
        let b' = fBlock b in
          if e' != e || b' != b then While (e', b', l) else s.skind
    | DoWhile (e, b, l) ->
	let b' = fBlock b in
        let e' = fExp e in 
          if e' != e || b' != b then DoWhile (e', b', l) else s.skind
    | For (bInit, e, bIter, b, l) -> 
	let bInit' = fBlock bInit in
	let e' = fExp e in
	let bIter' = fBlock bIter in
	let b' = fBlock b in
	  if bInit' != bInit || e' != e || bIter' != bIter || b' != b then
	    For (bInit', e', bIter', b', l) else s.skind
    | If(e, s1, s2, l) -> 
        let e' = fExp e in 
        (*if e queued any instructions, pop them here and remember them so that
          they are inserted before the If stmt, not in the then block. *)
        toPrepend := vis#unqueueInstr (); 
        let s1'= fBlock s1 in let s2'= fBlock s2 in
        (* the stmts in the blocks should have cleaned up after themselves.*)
        assertEmptyQueue vis;
        if e' != e || s1' != s1 || s2' != s2 then 
          If(e', s1', s2', l) else s.skind
    | Switch (e, b, stmts, l) -> 
        let e' = fExp e in 
        toPrepend := vis#unqueueInstr (); (* insert these before the switch *)
        let b' = fBlock b in
        (* the stmts in b should have cleaned up after themselves.*)
        assertEmptyQueue vis;
        (* Don't do stmts, but we better not change those *)
        if e' != e || b' != b then Switch (e', b', stmts, l) else s.skind
    | Instr il -> 
        let il' = mapNoCopyList fInst il in
        if il' != il then Instr il' else s.skind
    | Block b -> 
        let b' = fBlock b in 
        if b' != b then Block b' else s.skind
    | TryFinally (b, h, l) -> 
        let b' = fBlock b in
        let h' = fBlock h in
        if b' != b || h' != h then TryFinally(b', h', l) else s.skind
    | TryExcept (b, (il, e), h, l) -> 
        let b' = fBlock b in
        assertEmptyQueue vis;
        (* visit the instructions *)
        let il' = mapNoCopyList fInst il in
        (* Visit the expression *)
        let e' = fExp e in
        let il'' = 
          let more = vis#unqueueInstr () in
          if more != [] then 
            il' @ more
          else
            il'
        in
        let h' = fBlock h in
        (* Now collect the instructions *)
        if b' != b || il'' != il || e' != e || h' != h then 
          TryExcept(b', (il'', e'), h', l) 
        else s.skind
  in
  if skind' != s.skind then s.skind <- skind';
  (* Visit the labels *)
  let labels' = 
    let fLabel = function
        Case (e, l) as lb -> 
          let e' = fExp e in
          if e' != e then Case (e', l) else lb
        | lb -> lb
    in
    mapNoCopy fLabel s.labels
  in
  if labels' != s.labels then s.labels <- labels';
  s
      
    
 
and visitCilBlock (vis: cilVisitor) (b: block) : block = 
  doVisit vis vis#vblock childrenBlock b
and childrenBlock (vis: cilVisitor) (b: block) : block = 
  let fStmt s = visitCilStmt vis s in
  let stmts' = mapNoCopy fStmt b.bstmts in
  if stmts' != b.bstmts then { battrs = b.battrs; bstmts = stmts'} else b


and visitCilType (vis : cilVisitor) (t : typ) : typ =
  doVisit vis vis#vtype childrenType t
and childrenType (vis : cilVisitor) (t : typ) : typ =
  (* look for types referred to inside t's definition *)
  let fTyp t  = visitCilType vis t in
  let fAttr a = visitCilAttributes vis a in
  match t with
    TPtr(t1, a) -> 
      let t1' = fTyp t1 in
      let a' = fAttr a in
      if t1' != t || a' != a then TPtr(t1', a') else t
  | TArray(t1, None, a) -> 
      let t1' = fTyp t1 in
      let a' = fAttr a in
      if t1' != t || a' != a  then TArray(t1', None, a') else t
  | TArray(t1, Some e, a) -> 
      let t1' = fTyp t1 in
      let e' = visitCilExpr vis e in
      let a' = fAttr a in
      if t1' != t || e' != e  || a' != a then TArray(t1', Some e', a') else t

      (* DON'T recurse into the compinfo, this is done in visitCilGlobal.
	 User can iterate over cinfo.cfields manually, if desired.*)
  | TComp(cinfo, a) ->
      let a' = fAttr a in
      if a != a' then TComp(cinfo, a') else t

  | TFun(rettype, args, isva, a) -> 
      let rettype' = fTyp rettype in
      (* iterate over formals, as variable declarations *)
      let argslist = argsToList args in
      let visitArg ((an,at,aa) as arg) = 
        let at' = fTyp at in
        let aa' = fAttr aa in
        if at' != at || aa' != aa then (an,at',aa') else arg
      in
      let argslist' = mapNoCopy visitArg argslist in
      let a' = fAttr a in
      if rettype' != rettype || argslist' != argslist || a' != a  then 
        let args' = if argslist' == argslist then args else Some argslist' in
        TFun(rettype', args', isva, a') else t

  | TNamed(t1, a) -> (* Do not go into the type. Will do it at the time of 
                      * GType *)
      let a' = fAttr a in
      if a' != a  then TNamed (t1, a') else t

  | _ ->  (* other types (TVoid, TInt, TFloat, TEnum, and TBuiltin_va_list)
             don't contain nested types, but they do have attributes. *)
      let a = typeAttrs t in
      let a' = fAttr a in
      if a' != a  then setTypeAttrs t a' else t
      

(* for declarations, we visit the types inside; but for uses, *)
(* we just visit the varinfo node *)
and visitCilVarDecl (vis : cilVisitor) (v : varinfo) : varinfo =
  doVisit vis vis#vvdec childrenVarDecl v 
and childrenVarDecl (vis : cilVisitor) (v : varinfo) : varinfo =
  v.vtype <- visitCilType vis v.vtype;
  v.vattr <- visitCilAttributes vis v.vattr;  
  v

and visitCilAttributes (vis: cilVisitor) (al: attribute list) : attribute list=
   let al' = 
     mapNoCopyList (doVisitList vis vis#vattr childrenAttribute) al in
   if al' != al then 
     (* Must re-sort *)
     addAttributes al' []
   else
     al
and childrenAttribute (vis: cilVisitor) (a: attribute) : attribute = 
  let fAttrP a = visitCilAttrParams vis a in
  match a with 
    Attr (n, args) -> 
      let args' = mapNoCopy fAttrP args in
      if args' != args then Attr(n, args') else a
      

and visitCilAttrParams (vis: cilVisitor) (a: attrparam) : attrparam =
   doVisit vis vis#vattrparam childrenAttrparam a
and childrenAttrparam (vis: cilVisitor) (aa: attrparam) : attrparam = 
  let fTyp t  = visitCilType vis t in
  let fAttrP a = visitCilAttrParams vis a in
  match aa with 
      AInt _ | AStr _ -> aa
    | ACons(n, args) -> 
        let args' = mapNoCopy fAttrP args in
        if args' != args then ACons(n, args') else aa
    | ASizeOf t -> 
        let t' = fTyp t in
        if t' != t then ASizeOf t' else aa
    | ASizeOfE e -> 
        let e' = fAttrP e in
        if e' != e then ASizeOfE e' else aa
    | AAlignOf t -> 
        let t' = fTyp t in
        if t' != t then AAlignOf t' else aa
    | AAlignOfE e -> 
        let e' = fAttrP e in
        if e' != e then AAlignOfE e' else aa
    | ASizeOfS _ | AAlignOfS _ ->
        ignore (warn "Visitor inside of a type signature.");
        aa
    | AUnOp (uo, e1) -> 
        let e1' = fAttrP e1 in
        if e1' != e1 then AUnOp (uo, e1') else aa
    | ABinOp (bo, e1, e2) -> 
        let e1' = fAttrP e1 in
        let e2' = fAttrP e2 in
        if e1' != e1 || e2' != e2 then ABinOp (bo, e1', e2') else aa
    | ADot (ap, s) ->
        let ap' = fAttrP ap in
        if ap' != ap then ADot (ap', s) else aa
 

let rec visitCilFunction (vis : cilVisitor) (f : fundec) : fundec =
  if debugVisit then ignore (E.log "Visiting function %s\n" f.svar.vname);
  assertEmptyQueue vis;
  let f = doVisit vis vis#vfunc childrenFunction f in

  let toPrepend = vis#unqueueInstr () in
  if toPrepend <> [] then 
    f.sbody.bstmts <- mkStmt (Instr toPrepend) :: f.sbody.bstmts;
  f

and childrenFunction (vis : cilVisitor) (f : fundec) : fundec =
  f.svar <- visitCilVarDecl vis f.svar; (* hit the function name *)
  (* visit local declarations *)
  f.slocals <- mapNoCopy (visitCilVarDecl vis) f.slocals;
  (* visit the formals *)
  let newformals = mapNoCopy (visitCilVarDecl vis) f.sformals in
  (* Make sure the type reflects the formals *)
  setFormals f newformals;
  (* Remember any new instructions that were generated while visiting
     variable declarations. *)
  let toPrepend = vis#unqueueInstr () in

  f.sbody <- visitCilBlock vis f.sbody;        (* visit the body *)
  if toPrepend <> [] then 
    f.sbody.bstmts <- mkStmt (Instr toPrepend) :: f.sbody.bstmts;
  f

let rec visitCilGlobal (vis: cilVisitor) (g: global) : global list =
  (*(trace "visit" (dprintf "visitCilGlobal\n"));*)
  let oldloc = !currentLoc in
  currentLoc := (get_globalLoc g) ;
  currentGlobal := g;
  let res = doVisitList vis vis#vglob childrenGlobal g in
  currentLoc := oldloc;
  res
and childrenGlobal (vis: cilVisitor) (g: global) : global =
  match g with
  | GFun (f, l) -> 
      let f' = visitCilFunction vis f in
      if f' != f then GFun (f', l) else g
  | GType(t, l) ->
      t.ttype <- visitCilType vis t.ttype;
      g

  | GEnumTagDecl _ | GCompTagDecl _ -> g (* Nothing to visit *)
  | GEnumTag (enum, _) ->
      (trace "visit" (dprintf "visiting global enum %s\n" enum.ename));
      (* Do the values and attributes of the enumerated items *)
      let itemVisit (name, exp, loc) = (name, visitCilExpr vis exp, loc) in
      enum.eitems <- mapNoCopy itemVisit enum.eitems;
      enum.eattr <- visitCilAttributes vis enum.eattr;
      g

  | GCompTag (comp, _) ->
      (trace "visit" (dprintf "visiting global comp %s\n" comp.cname));
      (* Do the types and attirbutes of the fields *)
      let fieldVisit = fun fi -> 
        fi.ftype <- visitCilType vis fi.ftype;
        fi.fattr <- visitCilAttributes vis fi.fattr
      in
      List.iter fieldVisit comp.cfields;
      comp.cattr <- visitCilAttributes vis comp.cattr;
      g

  | GVarDecl(v, l) -> 
      let v' = visitCilVarDecl vis v in
      if v' != v then GVarDecl (v', l) else g
  | GVar (v, inito, l) -> 
      let v' = visitCilVarDecl vis v in
      (match inito.init with
        None -> ()
      | Some i -> let i' = visitCilInit vis i in 
        if i' != i then inito.init <- Some i');

      if v' != v then GVar (v', inito, l) else g

  | GPragma (a, l) -> begin
      match visitCilAttributes vis [a] with
        [a'] -> if a' != a then GPragma (a', l) else g
      | _ -> E.s (E.unimp "visitCilAttributes returns more than one attribute")
  end
  | _ -> g


(** A visitor that does constant folding. If "machdep" is true then we do 
 * machine dependent simplification (e.g., sizeof) *)
class constFoldVisitorClass (machdep: bool) : cilVisitor = object
  inherit nopCilVisitor
      
  method vinst i = 
    match i with 
      (* Skip two functions to which we add Sizeof to the type arguments. 
         See the comments for these above. *)
      Call(_,(Lval (Var vi,NoOffset)),_,_) 
        when ((vi.vname = "__builtin_va_arg") 
              || (vi.vname = "__builtin_types_compatible_p")) ->
          SkipChildren
    | _ -> DoChildren
  method vexpr (e: exp) = 
    (* Do it bottom up *)
    ChangeDoChildrenPost (e, constFold machdep)
        
end
let constFoldVisitor (machdep: bool) = new constFoldVisitorClass machdep

(* Iterate over all globals, including the global initializer *)
let iterGlobals (fl: file)
                (doone: global -> unit) : unit =
  let doone' g = 
      currentLoc := get_globalLoc g;
      doone g
  in
  List.iter doone' fl.globals;
  (match fl.globinit with
    None -> ()
  | Some g -> doone' (GFun(g, locUnknown)))

(* Fold over all globals, including the global initializer *)
let foldGlobals (fl: file) 
                (doone: 'a -> global -> 'a) 
                (acc: 'a) : 'a = 
  let doone' acc g = 
      currentLoc := get_globalLoc g;
      doone acc g
  in
  let acc' = List.fold_left doone' acc fl.globals in
  (match fl.globinit with
    None -> acc'
  | Some g -> doone' acc' (GFun(g, locUnknown)))


(* A visitor for the whole file that does not change the globals *)
let visitCilFileSameGlobals (vis : cilVisitor) (f : file) : unit =
  let fGlob g = visitCilGlobal vis g in
  iterGlobals f (fun g -> 
    match fGlob g with 
      [g'] when g' == g || Util.equals g' g -> () (* Try to do the pointer check first *)
    | gl -> 
        ignore (E.log "You used visitCilFilSameGlobals but the global got changed:\n %a\nchanged to %a\n" d_global g (docList ~sep:line (d_global ())) gl);
        ())

(* Be careful with visiting the whole file because it might be huge. *)
let visitCilFile (vis : cilVisitor) (f : file) : unit =
  let fGlob g = visitCilGlobal vis g in
  (* Scan the globals. Make sure this is tail recursive. *)
  let rec loop (acc: global list) = function
      [] -> f.globals <- List.rev acc
    | g :: restg -> 
        loop ((List.rev (fGlob g)) @ acc) restg
  in
  loop [] f.globals;
  (* the global initializer *)
  (match f.globinit with
    None -> ()
  | Some g -> f.globinit <- Some (visitCilFunction vis g))



(** Create or fetch the global initializer. Tries to put a call to in the the 
 * function with the main_name *)
let getGlobInit ?(main_name="main") (fl: file) = 
  match fl.globinit with 
    Some f -> f
  | None -> begin
      (* Sadly, we cannot use the Filename library because it does not like 
       * function names with multiple . in them *)
      let f = 
        let len = String.length fl.fileName in
        (* Find the last path separator and record the first . that we see, 
        * going backwards *)
        let lastDot = ref len in
        let rec findLastPathSep i = 
          if i < 0 then -1 else
          let c = String.get fl.fileName i in
          if c = '/' || c = '\\' then i
          else begin
            if c = '.' && !lastDot = len then 
              lastDot := i;
            findLastPathSep (i - 1)
          end
        in
        let lastPathSep = findLastPathSep (len - 1) in
        let basenoext = 
          String.sub fl.fileName (lastPathSep + 1) (!lastDot - lastPathSep - 1) 
        in
        emptyFunction 
          (makeValidSymbolName ("__globinit_" ^ basenoext))
      in
      fl.globinit <- Some f;
      (* Now try to add a call to the global initialized at the beginning of 
       * main *)
      let inserted = ref false in
      List.iter 
        (fun g ->
          match g with
            GFun(m, lm) when m.svar.vname = main_name ->
              (* Prepend a prototype to the global initializer *)
              fl.globals <- GVarDecl (f.svar, lm) :: fl.globals;
              m.sbody.bstmts <- 
                 compactStmts (mkStmt (Instr [Call(None, 
                                                   Lval(var f.svar), 
                                                   [], locUnknown)]) 
                               :: m.sbody.bstmts);
              inserted := true;
              if !E.verboseFlag then
                ignore (E.log "Inserted the globinit\n");
              fl.globinitcalled <- true;
          | _ -> ())
        fl.globals;

      if not !inserted then 
        ignore (E.warn "Cannot find %s to add global initializer %s" 
                  main_name f.svar.vname);
      
      f
  end
  

      
(* Fold over all globals, including the global initializer *)
let mapGlobals (fl: file) 
               (doone: global -> global) : unit = 
  fl.globals <- List.map doone fl.globals;
  (match fl.globinit with
    None -> ()
  | Some g -> begin
      match doone (GFun(g, locUnknown)) with
        GFun(g', _) -> fl.globinit <- Some g'
      | _ -> E.s (E.bug "mapGlobals: globinit is not a function")
  end)



let dumpFile (pp: cilPrinter) (out : out_channel) (outfile: string) file =
  printDepth := 99999;  (* We don't want ... in the output *)
  (* If we are in RELEASE mode then we do not print indentation *)

  Pretty.fastMode := true;

  if !E.verboseFlag then 
    ignore (E.log "printing file %s\n" outfile);
  let print x = fprint out 78 x in
  print (text ("/* Generated by CIL v. " ^ cilVersion ^ " */\n" ^
               (* sm: I want to easily tell whether the generated output
                * is with print_CIL_Input or not *)
               "/* print_CIL_Input is " ^ (if !print_CIL_Input then "true" else "false") ^ " */\n\n"));
  iterGlobals file (fun g -> dumpGlobal pp out g);
    
  (* sm: we have to flush the output channel; if we don't then under *)
  (* some circumstances (I haven't figure out exactly when, but it happens *)
  (* more often with big inputs), we get a truncated output file *)
  flush out



(******************
 ******************
 ******************)



(******************** OPTIMIZATIONS *****)
let rec peepHole1 (* Process one statement and possibly replace it *)
                  (doone: instr -> instr list option)
                  (* Scan a block and recurse inside nested blocks *)
                  (ss: stmt list) : unit = 
  let rec doInstrList (il: instr list) : instr list = 
    match il with 
      [] -> []
    | i :: rest -> begin
        match doone i with
          None -> i :: doInstrList rest
        | Some sl -> doInstrList (sl @ rest)
    end
  in
    
  List.iter 
    (fun s -> 
      match s.skind with
        Instr il -> s.skind <- Instr (doInstrList il)
      | If (e, tb, eb, _) -> 
          peepHole1 doone tb.bstmts;
          peepHole1 doone eb.bstmts
      | Switch (e, b, _, _) -> peepHole1 doone b.bstmts
(*
      | Loop (b, l, _, _) -> peepHole1 doone b.bstmts
*)
      | While (_, b, _) -> peepHole1 doone b.bstmts
      | DoWhile (_, b, _) -> peepHole1 doone b.bstmts
      | For (bInit, _, bIter, b, _) ->
	  peepHole1 doone bInit.bstmts;
	  peepHole1 doone bIter.bstmts;
	  peepHole1 doone b.bstmts
      | Block b -> peepHole1 doone b.bstmts
      | TryFinally (b, h, l) -> 
          peepHole1 doone b.bstmts; 
          peepHole1 doone h.bstmts
      | TryExcept (b, (il, e), h, l) -> 
          peepHole1 doone b.bstmts; 
          peepHole1 doone h.bstmts;
          s.skind <- TryExcept(b, (doInstrList il, e), h, l);
      | Return _ | Goto _ | Break _ | Continue _ -> ())
    ss

let rec peepHole2  (* Process two statements and possibly replace them both *)
                   (dotwo: instr * instr -> instr list option)
                   (ss: stmt list) : unit = 
  let rec doInstrList (il: instr list) : instr list = 
    match il with 
      [] -> []
    | [i] -> [i]
    | (i1 :: ((i2 :: rest) as rest2)) -> 
        begin
          match dotwo (i1,i2) with
            None -> i1 :: doInstrList rest2
          | Some sl -> doInstrList (sl @ rest)
        end
  in
  List.iter 
    (fun s -> 
      match s.skind with
        Instr il -> s.skind <- Instr (doInstrList il)
      | If (e, tb, eb, _) -> 
          peepHole2 dotwo tb.bstmts;
          peepHole2 dotwo eb.bstmts
      | Switch (e, b, _, _) -> peepHole2 dotwo b.bstmts
(*
      | Loop (b, l, _, _) -> peepHole2 dotwo b.bstmts
*)
      | While (_, b, _) -> peepHole2 dotwo b.bstmts
      | DoWhile (_, b, _) -> peepHole2 dotwo b.bstmts
      | For (bInit, _, bIter, b, _) ->
	  peepHole2 dotwo bInit.bstmts;
	  peepHole2 dotwo bIter.bstmts;
	  peepHole2 dotwo b.bstmts
      | Block b -> peepHole2 dotwo b.bstmts
      | TryFinally (b, h, l) -> peepHole2 dotwo b.bstmts; 
                                peepHole2 dotwo h.bstmts
      | TryExcept (b, (il, e), h, l) -> 
          peepHole2 dotwo b.bstmts; 
          peepHole2 dotwo h.bstmts;
          s.skind <- TryExcept (b, (doInstrList il, e), h, l)

      | Return _ | Goto _ | Break _ | Continue _ -> ())
    ss




(*** Type signatures ***)

(* Helper class for typeSig: replace any types in attributes with typsigs *)
class typeSigVisitor(typeSigConverter: typ->typsig) = object 
  inherit nopCilVisitor 
  method vattrparam ap =
    match ap with
      | ASizeOf t -> ChangeTo (ASizeOfS (typeSigConverter t))
      | AAlignOf t -> ChangeTo (AAlignOfS (typeSigConverter t))
      | _ -> DoChildren
end

let typeSigAddAttrs a0 t = 
  if a0 == [] then t else
  match t with 
    TSBase t -> TSBase (typeAddAttributes a0 t)
  | TSPtr (ts, a) -> TSPtr (ts, addAttributes a0 a)
  | TSArray (ts, l, a) -> TSArray(ts, l, addAttributes a0 a)
  | TSComp (iss, n, a) -> TSComp (iss, n, addAttributes a0 a)
  | TSEnum (n, a) -> TSEnum (n, addAttributes a0 a)
  | TSFun(ts, tsargs, isva, a) -> TSFun(ts, tsargs, isva, addAttributes a0 a)

(* Compute a type signature.
    Use ~ignoreSign:true to convert all signed integer types to unsigned,
    so that signed and unsigned will compare the same. *)
let rec typeSigWithAttrs ?(ignoreSign=false) doattr t = 
  let typeSig = typeSigWithAttrs ~ignoreSign doattr in
  let attrVisitor = new typeSigVisitor typeSig in
  let doattr al = visitCilAttributes attrVisitor (doattr al) in
  match t with 
  | TInt (ik, al) -> 
      let ik' = if ignoreSign then begin
        match ik with
          | ISChar | IChar -> IUChar
          | IShort -> IUShort
          | IInt -> IUInt
          | ILong -> IULong
          | ILongLong -> IULongLong
          | _ -> ik          
      end else
        ik
      in
      TSBase (TInt (ik', doattr al))
  | TFloat (fk, al) -> TSBase (TFloat (fk, doattr al))
  | TVoid al -> TSBase (TVoid (doattr al))
  | TEnum (enum, a) -> TSEnum (enum.ename, doattr a)
  | TPtr (t, a) -> TSPtr (typeSig t, doattr a)
  | TArray (t,l,a) -> (* We do not want fancy expressions in array lengths. 
                       * So constant fold the lengths *)
      let l' = 
        match l with 
          Some l -> begin 
            match constFold true l with 
              Const(CInt64(i, _, _)) -> Some i
            | e -> E.s (E.bug "Invalid length in array type: %a\n" 
                          (!pd_exp) e)
          end 
        | None -> None
      in 
      TSArray(typeSig t, l', doattr a)

  | TComp (comp, a) -> 
      TSComp (comp.cstruct, comp.cname, doattr (addAttributes comp.cattr a))
  | TFun(rt,args,isva,a) -> 
      TSFun(typeSig rt, 
            List.map (fun (_, atype, _) -> (typeSig atype)) (argsToList args),
            isva, doattr a)
  | TNamed(t, a) -> typeSigAddAttrs (doattr a) (typeSig t.ttype)
  | TBuiltin_va_list al -> TSBase (TBuiltin_va_list (doattr al))      

let typeSig t = 
  typeSigWithAttrs (fun al -> al) t

let _ = pTypeSig := typeSig

(* Remove the attribute from the top-level of the type signature *)
let setTypeSigAttrs (a: attribute list) = function
    TSBase t -> TSBase (setTypeAttrs t a)
  | TSPtr (ts, _) -> TSPtr (ts, a)
  | TSArray (ts, l, _) -> TSArray(ts, l, a)
  | TSComp (iss, n, _) -> TSComp (iss, n, a)
  | TSEnum (n, _) -> TSEnum (n, a)
  | TSFun (ts, tsargs, isva, _) -> TSFun (ts, tsargs, isva, a)


let typeSigAttrs = function
    TSBase t -> typeAttrs t
  | TSPtr (ts, a) -> a
  | TSArray (ts, l, a) -> a
  | TSComp (iss, n, a) -> a
  | TSEnum (n, a) -> a
  | TSFun (ts, tsargs, isva, a) -> a



let dExp: doc -> exp = 
  fun d -> Const(CStr(sprint !lineLength d))

let dInstr: doc -> location -> instr = 
  fun d l -> Asm([], [sprint !lineLength d], [], [], [], l)

let dGlobal: doc -> location -> global = 
  fun d l -> GAsm(sprint !lineLength d, l)

let rec addOffset (toadd: offset) (off: offset) : offset =
  match off with
    NoOffset -> toadd
  | Field(fid', offset) -> Field(fid', addOffset toadd offset)
  | Index(e, offset) -> Index(e, addOffset toadd offset)

 (* Add an offset at the end of an lv *)      
let addOffsetLval toadd (b, off) : lval =
 b, addOffset toadd off

let rec removeOffset (off: offset) : offset * offset = 
  match off with 
    NoOffset -> NoOffset, NoOffset
  | Field(f, NoOffset) -> NoOffset, off
  | Index(i, NoOffset) -> NoOffset, off
  | Field(f, restoff) -> 
      let off', last = removeOffset restoff in
      Field(f, off'), last
  | Index(i, restoff) -> 
      let off', last = removeOffset restoff in
      Index(i, off'), last

let removeOffsetLval ((b, off): lval) : lval * offset = 
  let off', last = removeOffset off in
  (b, off'), last

  (* Make an AddrOf. Given an lval of type T will give back an expression of 
   * type ptr(T)  *)
let mkAddrOf ((b, off) as lval) : exp = 
  (* Never take the address of a register variable *)
  (match lval with
    Var vi, off when vi.vstorage = Register -> vi.vstorage <- NoStorage
  | _ -> ()); 
  match lval with
    Mem e, NoOffset -> e
  | b, Index(z, NoOffset) when isZero z -> StartOf (b, NoOffset)(* array *)
  | _ -> AddrOf lval


let mkAddrOrStartOf (lv: lval) : exp = 
  match unrollType (typeOfLval lv) with 
    TArray _ -> StartOf lv
  | _ -> mkAddrOf lv


  (* Make a Mem, while optimizing AddrOf. The type of the addr must be 
   * TPtr(t) and the type of the resulting lval is t. Note that in CIL the 
   * implicit conversion between a function and a pointer to a function does 
   * not apply. You must do the conversion yourself using AddrOf *)
let mkMem ~(addr: exp) ~(off: offset) : lval =  
  let res = 
    match addr, off with
      AddrOf lv, _ -> addOffsetLval off lv
    | StartOf lv, _ -> (* Must be an array *)
        addOffsetLval (Index(zero, off)) lv 
    | _, _ -> Mem addr, off
  in
(*  ignore (E.log "memof : %a:%a\nresult = %a\n" 
            d_plainexp addr d_plainoffset off d_plainexp res); *)
  res



let splitFunctionType (ftype: typ) 
    : typ * (string * typ * attributes) list option * bool * attributes = 
  match unrollType ftype with 
    TFun (rt, args, isva, a) -> rt, args, isva, a
  | _ -> E.s (bug "splitFunctionType invoked on a non function type %a" 
                d_type ftype)

let splitFunctionTypeVI (fvi: varinfo) 
    : typ * (string * typ * attributes) list option * bool * attributes = 
  match unrollType fvi.vtype with 
    TFun (rt, args, isva, a) -> rt, args, isva, a
  | _ -> E.s (bug "Function %s invoked on a non function type" fvi.vname)

let isArrayType t = 
  match unrollType t with
    TArray _ -> true
  | _ -> false


let rec isConstant = function
  | Const _ -> true
  | UnOp (_, e, _) -> isConstant e
  | BinOp (_, e1, e2, _) -> isConstant e1 && isConstant e2
  | Lval (Var vi, NoOffset) -> 
      (vi.vglob && isArrayType vi.vtype || isFunctionType vi.vtype)
  | Lval _ -> false
  | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ -> true
  | CastE (_, e) -> isConstant e
  | AddrOf (Var vi, off) | StartOf (Var vi, off)
        -> vi.vglob && isConstantOff off
  | AddrOf (Mem e, off) | StartOf(Mem e, off) 
        -> isConstant e && isConstantOff off

and isConstantOff = function
    NoOffset -> true
  | Field(fi, off) -> isConstantOff off
  | Index(e, off) -> isConstant e && isConstantOff off


let getCompField (cinfo:compinfo) (fieldName:string) : fieldinfo =
  (List.find (fun fi -> fi.fname = fieldName) cinfo.cfields)


let rec mkCastT ~(e: exp) ~(oldt: typ) ~(newt: typ) = 
  (* Do not remove old casts because they are conversions !!! *)
  if Util.equals (typeSig oldt) (typeSig newt) then begin
    e
  end else begin
    (* Watch out for constants *)
    match newt, e with 
      TInt(newik, []), Const(CInt64(i, _, _)) -> kinteger64 newik i
    | _ -> CastE(newt,e)
  end

let mkCast ~(e: exp) ~(newt: typ) = 
  mkCastT e (typeOf e) newt

type existsAction = 
    ExistsTrue                          (* We have found it *)
  | ExistsFalse                         (* Stop processing this branch *)
  | ExistsMaybe                         (* This node is not what we are 
                                         * looking for but maybe its 
                                         * successors are *)
let existsType (f: typ -> existsAction) (t: typ) : bool = 
  let memo : (int, unit) H.t = H.create 17 in  (* Memo table *)
  let rec loop t = 
    match f t with 
      ExistsTrue -> true
    | ExistsFalse -> false
    | ExistsMaybe -> 
        (match t with 
          TNamed (t', _) -> loop t'.ttype
        | TComp (c, _) -> loopComp c
        | TArray (t', _, _) -> loop t'
        | TPtr (t', _) -> loop t'
        | TFun (rt, args, _, _) -> 
            (loop rt || List.exists (fun (_, at, _) -> loop at) 
              (argsToList args))
        | _ -> false)
  and loopComp c = 
    if H.mem memo c.ckey then 
      (* We are looping, the answer must be false *)
      false
    else begin
      H.add memo c.ckey ();
      List.exists (fun f -> loop f.ftype) c.cfields
    end
  in
  loop t
          

(* Try to do an increment, with constant folding *)
let increm (e: exp) (i: int) =
  let et = typeOf e in
  let bop = if isPointerType et then PlusPI else PlusA in
  constFold false (BinOp(bop, e, integer i, et))
      
exception LenOfArray
let lenOfArray (eo: exp option) : int = 
  match eo with 
    None -> raise LenOfArray
  | Some e -> begin
      match constFold true e with
      | Const(CInt64(ni, _, _)) when ni >= Int64.zero -> 
          Int64.to_int ni
      | e -> raise LenOfArray
  end
  

(*** Make a initializer for zeroe-ing a data type ***)
let rec makeZeroInit (t: typ) : init = 
  match unrollType t with
    TInt (ik, _) -> SingleInit (Const(CInt64(Int64.zero, ik, None)))
  | TFloat(fk, _) -> SingleInit(Const(CReal(0.0, fk, None)))
  | TEnum _ -> SingleInit zero
  | TComp (comp, _) as t' when comp.cstruct -> 
      let inits = 
        List.fold_right
          (fun f acc -> 
            if f.fname <> missingFieldName then 
              (Field(f, NoOffset), makeZeroInit f.ftype) :: acc
            else
              acc)
          comp.cfields []
      in
      CompoundInit (t', inits)

  | TComp (comp, _) when not comp.cstruct -> 
      let fstfield, rest = 
        match comp.cfields with
          f :: rest -> f, rest
        | [] -> E.s (unimp "Cannot create init for empty union")
      in
      let fieldToInit = 
        if !msvcMode then
          (* ISO C99 [6.7.8.10] says that the first field of the union
             is the one we should initialize. *)
          fstfield
        else begin
          (* gcc initializes the whole union to zero.  So choose the largest
             field, and set that to zero.  Choose the first field if possible.
             MSVC also initializes the whole union, but use the ISO behavior
             for MSVC because it only allows compound initializers to refer
             to the first union field. *)
          let fieldSize f = try bitsSizeOf f.ftype with SizeOfError _ -> 0 in
          let widestField, widestFieldWidth =
            List.fold_left (fun acc thisField ->
                              let widestField, widestFieldWidth = acc in
                              let thisSize = fieldSize thisField in
                              if thisSize > widestFieldWidth then
                                thisField, thisSize
                              else
                                acc)
              (fstfield, fieldSize fstfield)
              rest
          in
          widestField
        end
      in
      CompoundInit(t, [(Field(fieldToInit, NoOffset), 
                        makeZeroInit fieldToInit.ftype)])

  | TArray(bt, Some len, _) as t' -> 
      let n = 
        match constFold true len with
          Const(CInt64(n, _, _)) -> Int64.to_int n
        | _ -> E.s (E.unimp "Cannot understand length of array")
      in
      let initbt = makeZeroInit bt in
      let rec loopElems acc i = 
        if i < 0 then acc
        else loopElems ((Index(integer i, NoOffset), initbt) :: acc) (i - 1) 
      in
      CompoundInit(t', loopElems [] (n - 1))

  | TArray (bt, None, at) as t' ->
      (* Unsized array, allow it and fill it in later 
       * (see cabs2cil.ml, collectInitializer) *)
      CompoundInit (t', [])

  | TPtr _ as t -> SingleInit(CastE(t, zero))
  | x -> E.s (unimp "Cannot initialize type: %a" d_type x)


(**** Fold over the list of initializers in a Compound. In the case of an 
 * array initializer only the initializers present are scanned (a prefix of 
 * all initializers) *)
let foldLeftCompound 
    ~(doinit: offset -> init -> typ -> 'a -> 'a)
    ~(ct: typ) 
    ~(initl: (offset * init) list)
    ~(acc: 'a) : 'a = 
  match unrollType ct with
    TArray(bt, _, _) -> 
      List.fold_left (fun acc (o, i) -> doinit o i bt acc) acc initl

  | TComp (comp, _) -> 
      let getTypeOffset = function
          Field(f, NoOffset) -> f.ftype
        | _ -> E.s (bug "foldLeftCompound: malformed initializer")
      in
      List.fold_left 
        (fun acc (o, i) -> doinit o i (getTypeOffset o) acc) acc initl

  | _ -> E.s (unimp "Type of Compound is not array or struct or union")

(**** Fold over the list of initializers in a Compound. Like foldLeftCompound 
 * but scans even the zero-initializers that are missing at the end of the 
 * array *)
let foldLeftCompoundAll 
    ~(doinit: offset -> init -> typ -> 'a -> 'a)
    ~(ct: typ) 
    ~(initl: (offset * init) list)
    ~(acc: 'a) : 'a = 
  match unrollType ct with
    TArray(bt, leno, _) -> begin
      let part = 
        List.fold_left (fun acc (o, i) -> doinit o i bt acc) acc initl in
      (* See how many more we have to do *)
      match leno with 
        Some lene -> begin
          match constFold true lene with 
            Const(CInt64(i, _, _)) -> 
              let len_array = Int64.to_int i in
              let len_init = List.length initl in
              if len_array > len_init then 
                let zi = makeZeroInit bt in
                let rec loop acc i = 
                  if i >= len_array then acc
                  else 
                    loop (doinit (Index(integer i, NoOffset)) zi bt acc) 
                         (i + 1)
                in
                loop part (len_init + 1)
              else
                part
          | _ -> E.s (unimp "foldLeftCompoundAll: array with initializer and non-constant length\n")
        end
          
      | _ -> E.s (unimp "foldLeftCompoundAll: TArray with initializer and no length")
    end
  | TComp (comp, _) -> 
      let getTypeOffset = function
          Field(f, NoOffset) -> f.ftype
        | _ -> E.s (bug "foldLeftCompound: malformed initializer")
      in
      List.fold_left 
        (fun acc (o, i) -> doinit o i (getTypeOffset o) acc) acc initl

  | _ -> E.s (E.unimp "Type of Compound is not array or struct or union")



let rec isCompleteType t =
  match unrollType t with
  | TArray(t, None, _) -> false
  | TArray(t, Some z, _) when isZero z -> false
  | TComp (comp, _) -> (* Struct or union *)
      List.for_all (fun fi -> isCompleteType fi.ftype) comp.cfields
  | _ -> true


module A = Alpha
  

(** Uniquefy the variable names *)
let uniqueVarNames (f: file) : unit = 
  (* Setup the alpha conversion table for globals *)
  let gAlphaTable: (string, 
                    location A.alphaTableData ref) H.t = H.create 113 in
  (* Keep also track of the global names that we have used. Map them to the 
   * variable ID. We do this only to check that we do not have two globals 
   * with the same name. *)
  let globalNames: (string, int) H.t = H.create 113 in
  (* Scan the file and add the global names to the table *)
  iterGlobals f
    (function
        GVarDecl(vi, l) 
      | GVar(vi, _, l) 
      | GFun({svar = vi}, l) -> 
          (* See if we have used this name already for something else *)
          (try
            let oldid = H.find globalNames vi.vname in
            if oldid <> vi.vid then 
              ignore (warn "The name %s is used for two distinct globals" 
                        vi.vname);
            (* Here if we have used this name already. Go ahead *)
            ()
          with Not_found -> begin
            (* Here if this is the first time we define a name *)
            H.add globalNames vi.vname vi.vid;
            (* And register it *)
            A.registerAlphaName gAlphaTable None vi.vname !currentLoc;
            ()
          end)
      | _ -> ());

  (* Now we must scan the function bodies and rename the locals *)
  iterGlobals f
    (function 
        GFun(fdec, l) -> begin
          currentLoc := l;
          (* Setup an undo list to be able to revert the changes to the 
           * global alpha table *)
          let undolist = ref [] in
          (* Process one local variable *)
          let processLocal (v: varinfo) = 
            let newname, oldloc = 
              A.newAlphaName gAlphaTable (Some undolist) v.vname 
               !currentLoc
            in
            if false && newname <> v.vname then (* Disable this warning *)
              ignore (warn "uniqueVarNames: Changing the name of local %s in %s to %s (due to duplicate at %a)\n"
                        v.vname fdec.svar.vname newname d_loc oldloc);
            v.vname <- newname
          in
          (* Do the formals first *)
          List.iter processLocal fdec.sformals;
          (* Fix the type again *)
          setFormals fdec fdec.sformals;
          (* And now the locals *)
          List.iter processLocal fdec.slocals;
          (* Undo the changes to the global table *)
          A.undoAlphaChanges gAlphaTable !undolist;
          ()
        end
      | _ -> ());
  ()
          

(* A visitor that makes a deep copy of a function body *)
class copyFunctionVisitor (newname: string) = object (self)
  inherit nopCilVisitor

      (* Keep here a maping from locals to their copies *)
  val map : (string, varinfo) H.t = H.create 113 
      (* Keep here a maping from statements to their copies *)
  val stmtmap : (int, stmt) H.t = H.create 113
  val sid = ref 0 (* Will have to assign ids to statements *)
      (* Keep here a list of statements to be patched *)
  val patches : stmt list ref = ref []

  val argid = ref 0

      (* This is the main function *)
  method vfunc (f: fundec) : fundec visitAction = 
    (* We need a map from the old locals/formals to the new ones *)
    H.clear map;
    argid := 0;
     (* Make a copy of the fundec. *)
    let f' = {f with svar = f.svar} in
    let patchfunction (f' : fundec) = 
      (* Change the name. Only this late to allow the visitor to copy the 
       * svar  *)
      f'.svar.vname <- newname;
      let findStmt (i: int) = 
        try H.find stmtmap i 
        with Not_found -> E.s (bug "Cannot find the copy of stmt#%d" i)
      in
      let patchstmt (s: stmt) = 
        match s.skind with
          Goto (sr, l) -> 
            (* Make a copy of the reference *)
            let sr' = ref (findStmt !sr.sid) in
            s.skind <- Goto (sr',l)
        | Switch (e, body, cases, l) -> 
            s.skind <- Switch (e, body, 
                               List.map (fun cs -> findStmt cs.sid) cases, l)
        | _ -> ()
      in
      List.iter patchstmt !patches;
      f'
    in
    patches := [];
    sid := 0;
    H.clear stmtmap;
    ChangeDoChildrenPost (f', patchfunction)
    
      (* We must create a new varinfo for each declaration. Memoize to 
       * maintain sharing *)
  method vvdec (v: varinfo) = 
    (* Some varinfo have empty names. Give them some name *)
    if v.vname = "" then begin
      v.vname <- "arg" ^ string_of_int !argid; incr argid
    end;
    try
      ChangeTo (H.find map v.vname)
    with Not_found -> begin
      let v' = {v with vid = newVID () } in
      H.add map v.vname v';
      ChangeDoChildrenPost (v', fun x -> x)
    end

      (* We must replace references to local variables *)
  method vvrbl (v: varinfo) = 
    if v.vglob then SkipChildren else 
    try
      ChangeTo (H.find map v.vname)
    with Not_found -> 
      E.s (bug "Cannot find the new copy of local variable %s" v.vname)


        (* Replace statements. *)
  method vstmt (s: stmt) : stmt visitAction = 
    s.sid <- !sid; incr sid;
    let s' = {s with sid = s.sid} in
    H.add stmtmap s.sid s'; (* Remember where we copied this *)
    (* if we have a Goto or a Switch remember them to fixup at end *)
    (match s'.skind with
      (Goto _ | Switch _) -> patches := s' :: !patches
    | _ -> ());
    (* Do the children *)
    ChangeDoChildrenPost (s', fun x -> x)

      (* Copy blocks since they are mutable *)
  method vblock (b: block) = 
    ChangeDoChildrenPost ({b with bstmts = b.bstmts}, fun x -> x)


  method vglob _ = E.s (bug "copyFunction should not be used on globals")
end

(* We need a function that copies a CIL function. *)
let copyFunction (f: fundec) (newname: string) : fundec = 
  visitCilFunction (new copyFunctionVisitor(newname)) f
  
(********* Compute the CFG ********)
let sid_counter = ref 0

let new_sid () =
  let id = !sid_counter in
  incr sid_counter;
  id

let statements : stmt list ref = ref [] 
(* Clear all info about the CFG in statements *)  
class clear : cilVisitor = object
  inherit nopCilVisitor
  method vstmt s = begin
    s.sid <- !sid_counter ;
    incr sid_counter ;
    statements := s :: !statements;
    s.succs <- [] ;
    s.preds <- [] ;
    DoChildren
  end
  method vexpr _ = SkipChildren
  method vtype _ = SkipChildren
  method vinst _ = SkipChildren
end

let link source dest = begin
  if not (List.mem dest source.succs) then
    source.succs <- dest :: source.succs ;
  if not (List.mem source dest.preds) then
    dest.preds <- source :: dest.preds 
end
let trylink source dest_option = match dest_option with
  None -> ()
| Some(dest) -> link source dest 


(** Cmopute the successors and predecessors of a block, given a fallthrough *)
let rec succpred_block b fallthrough =
  let rec handle sl = match sl with
    [] -> ()
  | [a] -> succpred_stmt a fallthrough 
  | hd :: ((next :: _) as tl) -> 
      succpred_stmt hd (Some next) ;
      handle tl 
  in handle b.bstmts


and succpred_stmt s fallthrough = 
  match s.skind with
    Instr _ -> trylink s fallthrough
  | Return _ -> ()
  | Goto(dest,l) -> link s !dest
  | Break _  
  | Continue _ 
  | Switch _ ->
    failwith "computeCFGInfo: cannot be called on functions with break, continue or switch statements. Use prepareCFG first to remove them."

  | If(e1,b1,b2,l) -> 
      (match b1.bstmts with
        [] -> trylink s fallthrough
      | hd :: tl -> (link s hd ; succpred_block b1 fallthrough )) ;
      (match b2.bstmts with
        [] -> trylink s fallthrough
      | hd :: tl -> (link s hd ; succpred_block b2 fallthrough ))

(*
  | Loop(b,l,_,_) -> 
      begin match b.bstmts with
        [] -> failwith "computeCFGInfo: empty loop" 
      | hd :: tl -> 
          link s hd ; 
          succpred_block b (Some(hd))
      end
*)

  | While (e, b, l) -> begin match b.bstmts with
                       | [] -> failwith "computeCFGInfo: empty loop" 
	               | hd :: tl -> link s hd ;
                                     succpred_block b (Some(hd))
                       end

  | DoWhile (e, b, l) ->begin match b.bstmts with
                       |  [] -> failwith "computeCFGInfo: empty loop" 
	               | hd :: tl -> link s hd ;
                                     succpred_block b (Some(hd))
                       end

  | For (bInit, e, bIter, b, l) ->
      (match bInit.bstmts with
         |  [] -> failwith "computeCFGInfo: empty loop" 
	 | hd :: tl -> link s hd ;
             succpred_block bInit (Some(hd))) ;
      (match bIter.bstmts with
         |  [] -> failwith "computeCFGInfo: empty loop" 
	 | hd :: tl -> link s hd ;
             succpred_block bIter (Some(hd))) ;
      (match b.bstmts with
         |  [] -> failwith "computeCFGInfo: empty loop" 
	 | hd :: tl -> link s hd ;
             succpred_block b (Some(hd))) ;

  | Block(b) -> begin match b.bstmts with
                  [] -> trylink s fallthrough
                | hd :: tl -> link s hd ;
                    succpred_block b fallthrough
                end
  | TryExcept _ | TryFinally _ -> 
      failwith "computeCFGInfo: structured exception handling not implemented"

(* [weimer] Sun May  5 12:25:24 PDT 2002
 * This code was pulled from ext/switch.ml because it looks like we really
 * want it to be part of CIL. 
 *
 * Here is the magic handling to
 *  (1) replace switch statements with if/goto
 *  (2) remove "break"
 *  (3) remove "default"
 *  (4) remove "continue"
 *)
let is_case_label l = match l with
  | Case _ | Default _ -> true
  | _ -> false

let switch_count = ref (-1) 
let get_switch_count () = 
  switch_count := 1 + !switch_count ;
  !switch_count

let switch_label = ref (-1)

let rec xform_switch_stmt s break_dest cont_dest label_index = begin
  s.labels <- List.map (fun lab -> match lab with
    Label _ -> lab
  | Case(e,l) ->
      let suffix =
	match isInteger e with
	| Some value ->
	    if value < Int64.zero then
	      "neg_" ^ Int64.to_string (Int64.neg value)
	    else
	      Int64.to_string value
	| None ->
	    incr switch_label;
	    "exp_" ^ string_of_int !switch_label
      in
      let str = Pretty.sprint !lineLength 
	  (Pretty.dprintf "switch_%d_%s" label_index suffix) in 
      (Label(str,l,false))
  | Default(l) -> (Label(Printf.sprintf 
                  "switch_%d_default" label_index,l,false))
  ) s.labels ; 
  match s.skind with
  | Instr _ | Return _ | Goto _ -> ()
  | Break(l) -> begin try 
                  s.skind <- Goto(break_dest (),l)
                with e ->
                  ignore (error "prepareCFG: break: %a@!" d_stmt s) ;
                  raise e
                end
  | Continue(l) -> begin try
                  s.skind <- Goto(cont_dest (),l)
                with e ->
                  ignore (error "prepareCFG: continue: %a@!" d_stmt s) ;
                  raise e
                end
  | If(e,b1,b2,l) -> xform_switch_block b1 break_dest cont_dest label_index ;
                     xform_switch_block b2 break_dest cont_dest label_index
  | Switch(e,b,sl,l) -> begin
      (* change 
       * switch (se) {
       *   case 0: s0 ;
       *   case 1: s1 ; break;
       *   ...
       * }
       *
       * into:
       *
       * if (se == 0) goto label_0;
       * else if (se == 1) goto label_1;
       * ...
       * else if (0) { // body_block
       *  label_0: s0;
       *  label_1: s1; goto label_break;
       *  ...
       * } else if (0) { // break_block
       *  label_break: ; // break_stmt
       * } 
       *)
      let i = get_switch_count () in 
      let break_stmt = mkStmt (Instr []) in
      break_stmt.labels <- 
	[Label((Printf.sprintf "switch_%d_break" i),l,false)] ;
      let break_block = mkBlock [ break_stmt ] in
      let body_block = b in 
      let body_if_stmtkind = (If(zero,body_block,break_block,l)) in

      (* The default case, if present, must be used only if *all*
      non-default cases fail [ISO/IEC 9899:1999, §6.8.4.2, ¶5]. As a
      result, we sort the order in which we handle the labels (but not the
      order in which we print out the statements, so fall-through still
      works as expected). *)
      let compare_choices s1 s2 = match s1.labels, s2.labels with
      | (Default(_) :: _), _ -> 1
      | _, (Default(_) :: _) -> -1
      | _, _ -> 0
      in

      let rec handle_choices sl = match sl with
        [] -> body_if_stmtkind
      | stmt_hd :: stmt_tl -> begin
        let rec handle_labels lab_list = begin
          match lab_list with
            [] -> handle_choices stmt_tl 
          | Case(ce,cl) :: lab_tl -> 
              let pred = BinOp(Eq,e,ce,intType) in
              let then_block = mkBlock [ mkStmt (Goto(ref stmt_hd,cl)) ] in
              let else_block = mkBlock [ mkStmt (handle_labels lab_tl) ] in
              If(pred,then_block,else_block,cl)
          | Default(dl) :: lab_tl -> 
              (* ww: before this was 'if (1) goto label', but as Ben points
              out this might confuse someone down the line who doesn't have
              special handling for if(1) into thinking that there are two
              paths here. The simpler 'goto label' is what we want. *) 
              Block(mkBlock [ mkStmt (Goto(ref stmt_hd,dl)) ;
                              mkStmt (handle_labels lab_tl) ])
          | Label(_,_,_) :: lab_tl -> handle_labels lab_tl
        end in
        handle_labels stmt_hd.labels
      end in
      s.skind <- handle_choices (List.sort compare_choices sl) ;
      xform_switch_block b (fun () -> ref break_stmt) cont_dest i 
    end
(*
  | Loop(b,l,_,_) -> 
          let i = get_switch_count () in 
          let break_stmt = mkStmt (Instr []) in
          break_stmt.labels <- 
	    [Label((Printf.sprintf "while_%d_break" i),l,false)] ;
          let cont_stmt = mkStmt (Instr []) in
          cont_stmt.labels <- 
	    [Label((Printf.sprintf "while_%d_continue" i),l,false)] ;
          b.bstmts <- cont_stmt :: b.bstmts ;
          let this_stmt = mkStmt 
            (Loop(b,l,Some(cont_stmt),Some(break_stmt))) in 
          let break_dest () = ref break_stmt in
          let cont_dest () = ref cont_stmt in 
          xform_switch_block b break_dest cont_dest label_index ;
          break_stmt.succs <- s.succs ; 
          let new_block = mkBlock [ this_stmt ; break_stmt ] in
          s.skind <- Block new_block
*)
  | While (e, b, l) ->
          let i = get_switch_count () in 
          let break_stmt = mkStmt (Instr []) in
          break_stmt.labels <- 
	    [Label((Printf.sprintf "while_%d_break" i),l,false)] ;
          let cont_stmt = mkStmt (Instr []) in
          cont_stmt.labels <- 
	    [Label((Printf.sprintf "while_%d_continue" i),l,false)] ;
          b.bstmts <- cont_stmt :: b.bstmts ;
          let this_stmt = mkStmt 
            (While(e,b,l)) in 
          let break_dest () = ref break_stmt in
          let cont_dest () = ref cont_stmt in 
          xform_switch_block b break_dest cont_dest label_index ;
          break_stmt.succs <- s.succs ; 
          let new_block = mkBlock [ this_stmt ; break_stmt ] in
          s.skind <- Block new_block

  | DoWhile (e, b, l) ->
          let i = get_switch_count () in 
          let break_stmt = mkStmt (Instr []) in
          break_stmt.labels <- 
	    [Label((Printf.sprintf "while_%d_break" i),l,false)] ;
          let cont_stmt = mkStmt (Instr []) in
          cont_stmt.labels <- 
	    [Label((Printf.sprintf "while_%d_continue" i),l,false)] ;
          b.bstmts <- cont_stmt :: b.bstmts ;
          let this_stmt = mkStmt 
            (DoWhile(e,b,l)) in 
          let break_dest () = ref break_stmt in
          let cont_dest () = ref cont_stmt in 
          xform_switch_block b break_dest cont_dest label_index ;
          break_stmt.succs <- s.succs ; 
          let new_block = mkBlock [ this_stmt ; break_stmt ] in
          s.skind <- Block new_block

  | For (bInit, e, bIter , b, l) ->
          let i = get_switch_count () in 
          let break_stmt = mkStmt (Instr []) in
          break_stmt.labels <- 
	    [Label((Printf.sprintf "while_%d_break" i),l,false)] ;
          let cont_stmt = mkStmt (Instr []) in
          cont_stmt.labels <- 
	    [Label((Printf.sprintf "while_%d_continue" i),l,false)] ;
          b.bstmts <- cont_stmt :: b.bstmts ;
          let this_stmt = mkStmt 
            (For(bInit,e,bIter,b,l)) in 
          let break_dest () = ref break_stmt in
          let cont_dest () = ref cont_stmt in 
          xform_switch_block b break_dest cont_dest label_index ;
          break_stmt.succs <- s.succs ; 
          let new_block = mkBlock [ this_stmt ; break_stmt ] in
          s.skind <- Block new_block


  | Block(b) -> xform_switch_block b break_dest cont_dest label_index

  | TryExcept _ | TryFinally _ -> 
      failwith "xform_switch_statement: structured exception handling not implemented"

end and xform_switch_block b break_dest cont_dest label_index = 
  try 
    let rec link_succs sl = match sl with
    | [] -> ()
    | hd :: tl -> (if hd.succs = [] then hd.succs <- tl) ; link_succs tl
    in 
    link_succs b.bstmts ;
    List.iter (fun stmt -> 
      xform_switch_stmt stmt break_dest cont_dest label_index) b.bstmts ;
  with e ->
    List.iter (fun stmt -> ignore
      (warn "prepareCFG: %a@!" d_stmt stmt)) b.bstmts ;
    raise e

(* prepare a function for computeCFGInfo by removing break, continue,
 * default and switch statements/labels and replacing them with Ifs and
 * Gotos. *)
let prepareCFG (fd : fundec) : unit =
  xform_switch_block fd.sbody 
      (fun () -> failwith "prepareCFG: break with no enclosing loop") 
      (fun () -> failwith "prepareCFG: continue with no enclosing loop") (-1)

(* make the cfg and return a list of statements *)
let computeCFGInfo (f : fundec) (global_numbering : bool) : unit =
  if not global_numbering then 
    sid_counter := 0 ; 
  statements := [];
  let clear_it = new clear in 
  ignore (visitCilBlock clear_it f.sbody) ;
  f.smaxstmtid <- Some (!sid_counter) ;
  succpred_block f.sbody (None);
  let res = List.rev !statements in
  statements := [];
  f.sallstmts <- res;
  ()

let initCIL () = 
  if not !initCIL_called then begin 
    (* Set the machine *)
    theMachine := if !msvcMode then M.msvc else M.gcc;
    (* Pick type for string literals *)
    stringLiteralType := if !theMachine.M.const_string_literals then
      charConstPtrType
    else
      charPtrType;
    (* Find the right ikind given the size *)
    let findIkind (unsigned: bool) (sz: int) : ikind = 
      (* Test the most common sizes first *)
      if sz = !theMachine.M.sizeof_int then 
        if unsigned then IUInt else IInt 
      else if sz = !theMachine.M.sizeof_long then 
        if unsigned then IULong else ILong
      else if sz = 1 then 
        if unsigned then IUChar else IChar 
      else if sz = !theMachine.M.sizeof_short then
        if unsigned then IUShort else IShort
      else if sz = !theMachine.M.sizeof_longlong then
        if unsigned then IULongLong else ILongLong
      else 
        E.s(E.unimp "initCIL: cannot find the right ikind for size %d\n" sz)
    in      
    upointType := TInt(findIkind true !theMachine.M.sizeof_ptr, []);
    kindOfSizeOf := findIkind true !theMachine.M.sizeof_sizeof;
    typeOfSizeOf := TInt(!kindOfSizeOf, []);
    H.add gccBuiltins "__builtin_memset" 
      (voidPtrType, [ voidPtrType; intType; intType ], false);
    wcharKind := findIkind false !theMachine.M.sizeof_wchar;
    wcharType := TInt(!wcharKind, []);
    char_is_unsigned := !theMachine.M.char_is_unsigned;
    little_endian := !theMachine.M.little_endian;
    underscore_name := !theMachine.M.underscore_name;
    nextGlobalVID := 1;
    nextCompinfoKey := 1;
    initCIL_called := true
  end
    

(* We want to bring all type declarations before the data declarations. This 
 * is needed for code of the following form: 

   int f(); // Prototype without arguments
   typedef int FOO;
   int f(FOO x) { ... }

   In CIL the prototype also lists the type of the argument as being FOO, 
   which is undefined. 

   There is one catch with this scheme. If the type contains an array whose 
   length refers to variables then those variables must be declared before 
   the type *)

let pullTypesForward = true

  
    (* Scan a type and collect the variables that are refered *)
class getVarsInGlobalClass (pacc: varinfo list ref) = object
  inherit nopCilVisitor
  method vvrbl (vi: varinfo) = 
    pacc := vi :: !pacc;
    SkipChildren

  method vglob = function
      GType _ | GCompTag _ -> DoChildren
    | _ -> SkipChildren
      
end

let getVarsInGlobal (g : global) : varinfo list = 
  let pacc : varinfo list ref = ref [] in
  let v : cilVisitor = new getVarsInGlobalClass pacc in
  ignore (visitCilGlobal v g);
  !pacc

let hasPrefix p s = 
  let pl = String.length p in
  (String.length s >= pl) && String.sub s 0 pl = p

let pushGlobal (g: global) 
               ~(types:global list ref)
               ~(variables: global list ref) = 
  if not pullTypesForward then 
    variables := g :: !variables
  else
    begin
      (* Collect a list of variables that are refered from the type. Return 
       * Some if the global should go with the types and None if it should go 
       * to the variables. *)
      let varsintype : (varinfo list * location) option = 
        match g with 
          GType (_, l) | GCompTag (_, l) -> Some (getVarsInGlobal g, l)
        | GEnumTag (_, l) | GPragma (Attr("pack", _), l) 
        | GCompTagDecl (_, l) | GEnumTagDecl (_, l) -> Some ([], l)
          (** Move the warning pragmas early 
        | GPragma(Attr(s, _), l) when hasPrefix "warning" s -> Some ([], l)
          *)
        | _ -> None (* Does not go with the types *)
      in
      match varsintype with 
      None -> variables := g :: !variables
    | Some (vl, loc) -> 
        types := 
           (* insert declarations for referred variables ('vl'), before
            * the type definition 'g' itself *)
           g :: (List.fold_left (fun acc v -> GVarDecl(v, loc) :: acc) 
                                !types vl) 
  end


type formatArg = 
    Fe of exp
  | Feo of exp option  (** For array lengths *)
  | Fu of unop
  | Fb of binop
  | Fk of ikind
  | FE of exp list (** For arguments in a function call *)
  | Ff of (string * typ * attributes) (** For a formal argument *)
  | FF of (string * typ * attributes) list (* For formal argument lists *)
  | Fva of bool (** For the ellipsis in a function type *)
  | Fv of varinfo
  | Fl of lval
  | Flo of lval option (** For the result of a function call *)
  | Fo of offset
  | Fc of compinfo
  | Fi of instr
  | FI of instr list
  | Ft of typ
  | Fd of int
  | Fg of string
  | Fs of stmt
  | FS of stmt list
  | FA of attributes

  | Fp of attrparam
  | FP of attrparam list

  | FX of string

let d_formatarg () = function
    Fe e -> dprintf "Fe(%a)" d_exp e
  | Feo None -> dprintf "Feo(None)"
  | Feo (Some e) -> dprintf "Feo(%a)" d_exp e
  | FE _ -> dprintf "FE()"
  | Fk ik -> dprintf "Fk()"
  | Fva b -> dprintf "Fva(%b)" b
  | Ff (an, _, _) -> dprintf "Ff(%s)" an
  | FF _ -> dprintf "FF(...)"
  | FA _ -> dprintf "FA(...)"
  | Fu uo -> dprintf "Fu()"
  | Fb bo -> dprintf "Fb()"
  | Fv v -> dprintf "Fv(%s)" v.vname
  | Fl l -> dprintf "Fl(%a)" d_lval l
  | Flo None -> dprintf "Flo(None)"
  | Flo (Some l) -> dprintf "Flo(%a)" d_lval l
  | Fo o -> dprintf "Fo"
  | Fc ci -> dprintf "Fc(%s)" ci.cname
  | Fi i -> dprintf "Fi(...)"
  | FI i -> dprintf "FI(...)"
  | Ft t -> dprintf "Ft(%a)" d_type t
  | Fd n -> dprintf "Fd(%d)" n
  | Fg s -> dprintf "Fg(%s)" s
  | Fp _ -> dprintf "Fp(...)" 
  | FP n -> dprintf "FP(...)" 
  | Fs _ -> dprintf "FS"
  | FS _ -> dprintf "FS"

  | FX _ -> dprintf "FX()"


