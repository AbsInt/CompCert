(* MODIF: Loop constructor replaced by 3 constructors: While, DoWhile, For. *)

(*
 *
 * Copyright (c) 2001-2002, 
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
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

(*
 * CIL: An intermediate language for analyzing C programs.
 *
 * George Necula
 *
 *)

(** CIL API Documentation. An html version of this document can be found at 
 * http://manju.cs.berkeley.edu/cil. *)

(** Call this function to perform some initialization. Call if after you have 
 * set {!Cil.msvcMode}.  *)
val initCIL: unit -> unit


(** This are the CIL version numbers. A CIL version is a number of the form 
 * M.m.r (major, minor and release) *)
val cilVersion: string
val cilVersionMajor: int
val cilVersionMinor: int
val cilVersionRevision: int

(** This module defines the abstract syntax of CIL. It also provides utility 
 * functions for traversing the CIL data structures, and pretty-printing 
 * them. The parser for both the GCC and MSVC front-ends can be invoked as 
 * [Frontc.parse: string -> unit ->] {!Cil.file}. This function must be given 
 * the name of a preprocessed C file and will return the top-level data 
 * structure that describes a whole source file. By default the parsing and 
 * elaboration into CIL is done as for GCC source. If you want to use MSVC 
 * source you must set the {!Cil.msvcMode} to [true] and must also invoke the 
 * function [Frontc.setMSVCMode: unit -> unit]. *)


(** {b The Abstract Syntax of CIL} *)


(** The top-level representation of a CIL source file (and the result of the 
 * parsing and elaboration). Its main contents is the list of global 
 * declarations and definitions. You can iterate over the globals in a 
 * {!Cil.file} using the following iterators: {!Cil.mapGlobals}, 
 * {!Cil.iterGlobals} and {!Cil.foldGlobals}. You can also use the 
 * {!Cil.dummyFile} when you need a {!Cil.file} as a placeholder. For each 
 * global item CIL stores the source location where it appears (using the 
 * type {!Cil.location}) *)

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
       * should always be false if there is no global initializer. When you 
       * create a global initialization CIL will try to insert code in main 
       * to call it. This will not happen if your file does not contain a 
       * function called "main" *)
    } 
(** Top-level representation of a C source file *)

and comment = location * string

(** {b Globals}. The main type for representing global declarations and 
 * definitions. A list of these form a CIL file. The order of globals in the 
 * file is generally important. *)

(** A global declaration or definition *)
and global =
  | GType of typeinfo * location    
    (** A typedef. All uses of type names (through the [TNamed] constructor) 
        must be preceded in the file by a definition of the name. The string 
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

(** {b Types}. A C type is represented in CIL using the type {!Cil.typ}. 
 * Among types we differentiate the integral types (with different kinds 
 * denoting the sign and precision), floating point types, enumeration types, 
 * array and pointer types, and function types. Every type is associated with 
 * a list of attributes, which are always kept in sorted order. Use 
 * {!Cil.addAttribute} and {!Cil.addAttributes} to construct list of 
 * attributes. If you want to inspect a type, you should use 
 * {!Cil.unrollType} or {!Cil.unrollTypeDeep} to see through the uses of 
 * named types. *)
(** CIL is configured at build-time with the sizes and alignments of the 
 * underlying compiler (GCC or MSVC). CIL contains functions that can compute 
 * the size of a type (in bits) {!Cil.bitsSizeOf}, the alignment of a type 
 * (in bytes) {!Cil.alignOf_int}, and can convert an offset into a start and 
 * width (both in bits) using the function {!Cil.bitsOffset}. At the moment 
 * these functions do not take into account the [packed] attributes and 
 * pragmas. *)

and typ =
    TVoid of attributes   (** Void type. Also predefined as {!Cil.voidType} *)
  | TInt of ikind * attributes 
     (** An integer type. The kind specifies the sign and width. Several 
      * useful variants are predefined as {!Cil.intType}, {!Cil.uintType}, 
      * {!Cil.longType}, {!Cil.charType}. *)


  | TFloat of fkind * attributes 
     (** A floating-point type. The kind specifies the precision. You can 
      * also use the predefined constant {!Cil.doubleType}. *)

  | TPtr of typ * attributes  
           (** Pointer type. Several useful variants are predefined as 
            * {!Cil.charPtrType}, {!Cil.charConstPtrType} (pointer to a 
            * constant character), {!Cil.voidPtrType}, 
            * {!Cil.intPtrType}  *)

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
           * function's sformals. Use {!Cil.setFormals}, or 
           * {!Cil.setFunctionType}, or {!Cil.makeFormalVar} for this 
           * purpose. *)

  | TNamed of typeinfo * attributes 
          (* The use of a named type. Each such type name must be preceded 
           * in the file by a [GType] global. This is printed as just the 
           * type name. The actual referred type is not printed here and is 
           * carried only to simplify processing. To see through a sequence 
           * of named type references, use {!Cil.unrollType} or 
           * {!Cil.unrollTypeDeep}. The attributes are in addition to those 
           * given when the type name was defined. *)

  | TComp of compinfo * attributes
(** The most delicate issue for C types is that recursion that is possible by 
 * using structures and pointers. To address this issue we have a more 
 * complex representation for structured types (struct and union). Each such 
 * type is represented using the {!Cil.compinfo} type. For each composite 
 * type the {!Cil.compinfo} structure must be declared at top level using 
 * [GCompTag] and all references to it must share the same copy of the 
 * structure. The attributes given are those pertaining to this use of the 
 * type and are in addition to the attributes that were given at the 
 * definition of the type and which are stored in the {!Cil.compinfo}. *)

  | TEnum of enuminfo * attributes
           (** A reference to an enumeration type. All such references must
               share the enuminfo among them and with a [GEnumTag] global that 
               precedes all uses. The attributes refer to this use of the 
               enumeration and are in addition to the attributes of the 
               enumeration itself, which are stored inside the enuminfo  *)

  
  | TBuiltin_va_list of attributes
            (** This is the same as the gcc's type with the same name *)

(**
 There are a number of functions for querying the kind of a type. These are
 {!Cil.isIntegralType}, 
 {!Cil.isArithmeticType}, 
 {!Cil.isPointerType}, 
 {!Cil.isFunctionType}, 
 {!Cil.isArrayType}. 

 There are two easy ways to scan a type. First, you can use the
{!Cil.existsType} to return a boolean answer about a type. This function
is controlled by a user-provided function that is queried for each type that is
used to construct the current type. The function can specify whether to
terminate the scan with a boolean result or to continue the scan for the
nested types. 

 The other method for scanning types is provided by the visitor interface (see
 {!Cil.cilVisitor}).

 If you want to compare types (or to use them as hash-values) then you should
use instead type signatures (represented as {!Cil.typsig}). These
contain the same information as types but canonicalized such that simple Ocaml
structural equality will tell whether two types are equal. Use
{!Cil.typeSig} to compute the signature of a type. If you want to ignore
certain type attributes then use {!Cil.typeSigWithAttrs}. 

*)


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


(** {b Attributes.} *)

and attribute = Attr of string * attrparam list
(** An attribute has a name and some optional parameters. The name should not 
 * start or end with underscore. When CIL parses attribute names it will 
 * strip leading and ending underscores (to ensure that the multitude of GCC 
 * attributes such as const, __const and __const__ all mean the same thing.) *)

(** Attributes are lists sorted by the attribute name. Use the functions 
 * {!Cil.addAttribute} and {!Cil.addAttributes} to insert attributes in an 
 * attribute list and maintain the sortedness. *)
and attributes = attribute list
 
(** The type of parameters of attributes *)
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

(** {b Structures.} The {!Cil.compinfo} describes the definition of a 
 * structure or union type. Each such {!Cil.compinfo} must be defined at the 
 * top-level using the [GCompTag] constructor and must be shared by all 
 * references to this type (using either the [TComp] type constructor or from 
 * the definition of the fields. 

   If all you need is to scan the definition of each 
 * composite type once, you can do that by scanning all top-level [GCompTag]. 

 * Constructing a {!Cil.compinfo} can be tricky since it must contain fields 
 * that might refer to the host {!Cil.compinfo} and furthermore the type of 
 * the field might need to refer to the {!Cil.compinfo} for recursive types. 
 * Use the {!Cil.mkCompInfo} function to create a {!Cil.compinfo}. You can 
 * easily fetch the {!Cil.fieldinfo} for a given field in a structure with 
 * {!Cil.getCompField}. *)

(** The definition of a structure or union type. Use {!Cil.mkCompInfo} to 
 * make one and use {!Cil.copyCompInfo} to copy one (this ensures that a new 
 * key is assigned and that the fields have the right pointers to parents.). *)
and compinfo = {
    mutable cstruct: bool;              
   (** True if struct, False if union *)
    mutable cname: string;              
   (** The name. Always non-empty. Use {!Cil.compFullName} to get the full 
    * name of a comp (along with the struct or union) *)
    mutable ckey: int;                  
    (** A unique integer. This is assigned by {!Cil.mkCompInfo} using a 
     * global variable in the Cil module. Thus two identical structs in two 
     * different files might have different keys. Use {!Cil.copyCompInfo} to 
     * copy structures so that a new key is assigned. *)
    mutable cfields: fieldinfo list;    
    (** Information about the fields. Notice that each fieldinfo has a 
      * pointer back to the host compinfo. This means that you should not 
      * share fieldinfo's between two compinfo's *) 
    mutable cattr:   attributes;        
    (** The attributes that are defined at the same time as the composite 
     * type. These attributes can be supplemented individually at each 
     * reference to this [compinfo] using the [TComp] type constructor. *)
    mutable cdefined: bool;
    (** This boolean flag can be used to distinguish between structures
     that have not been defined and those that have been defined but have
     no fields (such things are allowed in gcc). *)
    mutable creferenced: bool;          
    (** True if used. Initially set to false. *)
  }

(** {b Structure fields.} The {!Cil.fieldinfo} structure is used to describe 
 * a structure or union field. Fields, just like variables, can have 
 * attributes associated with the field itself or associated with the type of 
 * the field (stored along with the type of the field). *)

(** Information about a struct/union field *)
and fieldinfo = { 
    mutable fcomp: compinfo;            
     (** The host structure that contains this field. There can be only one 
      * [compinfo] that contains the field. *)
    mutable fname: string;              
    (** The name of the field. Might be the value of {!Cil.missingFieldName} 
     * in which case it must be a bitfield and is not printed and it does not 
     * participate in initialization *)
    mutable ftype: typ;     
    (** The type *)
    mutable fbitfield: int option;      
    (** If a bitfield then ftype should be an integer type and the width of 
     * the bitfield must be 0 or a positive integer smaller or equal to the 
     * width of the integer type. A field of width 0 is used in C to control 
     * the alignment of fields. *)
    mutable fattr: attributes;          
    (** The attributes for this field (not for its type) *)
    mutable floc: location;
    (** The location where this field is defined *)
}



(** {b Enumerations.} Information about an enumeration. This is shared by all 
 * references to an enumeration. Make sure you have a [GEnumTag] for each of 
 * of these. *)

(** Information about an enumeration *)
and enuminfo = {
    mutable ename: string;              
    (** The name. Always non-empty. *)
    mutable eitems: (string * exp * location) list;
    (** Items with names and values. This list should be non-empty. The item 
     * values must be compile-time constants. *)
    mutable eattr: attributes;         
    (** The attributes that are defined at the same time as the enumeration 
     * type. These attributes can be supplemented individually at each 
     * reference to this [enuminfo] using the [TEnum] type constructor. *)
    mutable ereferenced: bool;         
    (** True if used. Initially set to false*)
}

(** {b Enumerations.} Information about an enumeration. This is shared by all 
 * references to an enumeration. Make sure you have a [GEnumTag] for each of 
 * of these. *)

(** Information about a defined type *)
and typeinfo = {
    mutable tname: string;              
    (** The name. Can be empty only in a [GType] when introducing a composite 
     * or enumeration tag. If empty cannot be referred to from the file *)
    mutable ttype: typ;
    (** The actual type. This includes the attributes that were present in 
     * the typedef *)
    mutable treferenced: bool;         
    (** True if used. Initially set to false*)
}

(** {b Variables.} 
 Each local or global variable is represented by a unique {!Cil.varinfo}
structure. A global {!Cil.varinfo} can be introduced with the [GVarDecl] or
[GVar] or [GFun] globals. A local varinfo can be introduced as part of a
function definition {!Cil.fundec}. 

 All references to a given global or local variable must refer to the same
copy of the [varinfo]. Each [varinfo] has a globally unique identifier that 
can be used to index maps and hashtables (the name can also be used for this 
purpose, except for locals from different functions). This identifier is 
constructor using a global counter.

 It is very important that you construct [varinfo] structures using only one
 of the following functions:
- {!Cil.makeGlobalVar} : to make a global variable
- {!Cil.makeTempVar} : to make a temporary local variable whose name
will be generated so that to avoid conflict with other locals. 
- {!Cil.makeLocalVar} : like {!Cil.makeTempVar} but you can specify the
exact name to be used. 
- {!Cil.copyVarinfo}: make a shallow copy of a varinfo assigning a new name 
and a new unique identifier

 A [varinfo] is also used in a function type to denote the list of formals. 

*)

(** Information about a variable. *)
and varinfo = { 
    mutable vname: string;		
    (** The name of the variable. Cannot be empty. It is primarily your 
     * responsibility to ensure the uniqueness of a variable name. For local 
     * variables {!Cil.makeTempVar} helps you ensure that the name is unique. 
     *)

    mutable vtype: typ;                 
    (** The declared type of the variable. *)

    mutable vattr: attributes;          
    (** A list of attributes associated with the variable.*)
    mutable vstorage: storage;          
    (** The storage-class *)

    mutable vglob: bool;	        
    (** True if this is a global variable*)

    mutable vinline: bool;
    (** Whether this varinfo is for an inline function. *)

    mutable vdecl: location;            
    (** Location of variable declaration. *)

    mutable vid: int;  
    (** A unique integer identifier. This field will be 
     * set for you if you use one of the {!Cil.makeFormalVar}, 
     * {!Cil.makeLocalVar}, {!Cil.makeTempVar}, {!Cil.makeGlobalVar}, or 
     * {!Cil.copyVarinfo}. *)

    mutable vaddrof: bool;              
    (** True if the address of this variable is taken. CIL will set these 
     * flags when it parses C, but you should make sure to set the flag 
     * whenever your transformation create [AddrOf] expression. *)

    mutable vreferenced: bool;          
    (** True if this variable is ever referenced. This is computed by 
     * [removeUnusedVars]. It is safe to just initialize this to False *)
}

(** Storage-class information *)
and storage = 
    NoStorage     (** The default storage. Nothing is printed  *)
  | Static
  | Register
  | Extern                              


(** {b Expressions.} The CIL expression language contains only the side-effect free expressions of
C. They are represented as the type {!Cil.exp}. There are several
interesting aspects of CIL expressions: 

 Integer and floating point constants can carry their textual representation.
This way the integer 15 can be printed as 0xF if that is how it occurred in the
source. 

 CIL uses 64 bits to represent the integer constants and also stores the width
of the integer type. Care must be taken to ensure that the constant is
representable with the given width. Use the functions {!Cil.kinteger},
{!Cil.kinteger64} and {!Cil.integer} to construct constant
expressions. CIL predefines the constants {!Cil.zero},
{!Cil.one} and {!Cil.mone} (for -1). 

 Use the functions {!Cil.isConstant} and {!Cil.isInteger} to test if
an expression is a constant and a constant integer respectively.

 CIL keeps the type of all unary and binary expressions. You can think of that
type qualifying the operator. Furthermore there are different operators for
arithmetic and comparisons on arithmetic types and on pointers. 

 Another unusual aspect of CIL is that the implicit conversion between an
expression of array type and one of pointer type is made explicit, using the
[StartOf] expression constructor (which is not printed). If you apply the
[AddrOf}]constructor to an lvalue of type [T] then you will be getting an
expression of type [TPtr(T)].

 You can find the type of an expression with {!Cil.typeOf}. 

 You can perform constant folding on expressions using the function
{!Cil.constFold}. 
*)

(** Expressions (Side-effect free)*)
and exp =
    Const      of constant              (** Constant *)
  | Lval       of lval                  (** Lvalue *)
  | SizeOf     of typ                   
    (** sizeof(<type>). Has [unsigned int] type (ISO 6.5.3.4). This is not 
     * turned into a constant because some transformations might want to 
     * change types *)

  | SizeOfE    of exp                   
    (** sizeof(<expression>) *)

  | SizeOfStr  of string
    (** sizeof(string_literal). We separate this case out because this is the 
      * only instance in which a string literal should not be treated as 
      * having type pointer to character. *)

  | AlignOf    of typ                   
    (** This corresponds to the GCC __alignof_. Has [unsigned int] type *)
  | AlignOfE   of exp  

                                        
  | UnOp       of unop * exp * typ     
    (** Unary operation. Includes the type of the result. *)

  | BinOp      of binop * exp * exp * typ
    (** Binary operation. Includes the type of the result. The arithmetic 
     * conversions are made explicit for the arguments. *)

  | CastE      of typ * exp            
    (** Use {!Cil.mkCast} to make casts.  *)

  | AddrOf     of lval                 
    (** Always use {!Cil.mkAddrOf} to construct one of these. Apply to an 
     * lvalue of type [T] yields an expression of type [TPtr(T)] *)

  | StartOf    of lval   
    (** Conversion from an array to a pointer to the beginning of the array. 
     * Given an lval of type [TArray(T)] produces an expression of type 
     * [TPtr(T)]. In C this operation is implicit, the [StartOf] operator is 
     * not printed. We have it in CIL because it makes the typing rules 
     * simpler. *)

(** {b Constants.} *)

(** Literal constants *)
and constant =
  | CInt64 of int64 * ikind * string option 
    (** Integer constant. Give the ikind (see ISO9899 6.1.3.2) and the 
     * textual representation, if available. (This allows us to print a 
     * constant as, for example, 0xF instead of 15.) Use {!Cil.integer} or 
     * {!Cil.kinteger} to create these. Watch out for integers that cannot be 
     * represented on 64 bits. OCAML does not give Overflow exceptions. *)
  | CStr of string 
    (* String constant. The escape characters inside the string have been 
     * already interpreted. This constant has pointer to character type! The 
     * only case when you would like a string literal to have an array type 
     * is when it is an argument to sizeof. In that case you should use 
     * SizeOfStr. *)
  | CWStr of int64 list  
    (* Wide character string constant. Note that the local interpretation
     * of such a literal depends on {!Cil.wcharType} and {!Cil.wcharKind}.
     * Such a constant has type pointer to {!Cil.wcharType}. The
     * escape characters in the string have not been "interpreted" in 
     * the sense that L"A\xabcd" remains "A\xabcd" rather than being
     * represented as the wide character list with two elements: 65 and
     * 43981. That "interpretation" depends on the underlying wide
     * character type. *)
  | CChr of char   
    (** Character constant.  This has type int, so use charConstToInt
     * to read the value in case sign-extension is needed. *)
  | CReal of float * fkind * string option 
     (** Floating point constant. Give the fkind (see ISO 6.4.4.2) and also 
      * the textual representation, if available. *)
  | CEnum of exp * string * enuminfo
     (** An enumeration constant with the given value, name, from the given 
      * enuminfo. This is used only if {!Cil.lowerConstants} is true 
      * (default). Use {!Cil.constFoldVisitor} to replace these with integer 
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

  | LAnd                                (** logical and. Unlike other 
                                         * expressions this one does not 
                                         * always evaluate both operands. If 
                                         * you want to use these, you must 
                                         * set {!Cil.useLogicalOperators}. *)
  | LOr                                 (** logical or. Unlike other 
                                         * expressions this one does not 
                                         * always evaluate both operands.  If 
                                         * you want to use these, you must 
                                         * set {!Cil.useLogicalOperators}. *)

(** {b Lvalues.} Lvalues are the sublanguage of expressions that can appear at the left of an assignment or as operand to the address-of operator. 
In C the syntax for lvalues is not always a good indication of the meaning 
of the lvalue. For example the C value
{v  
a[0][1][2]
 v}
 might involve 1, 2 or 3 memory reads when used in an expression context,
depending on the declared type of the variable [a]. If [a] has type [int
\[4\]\[4\]\[4\]] then we have one memory read from somewhere inside the area 
that stores the array [a]. On the other hand if [a] has type [int ***] then
the expression really means [* ( * ( * (a + 0) + 1) + 2)], in which case it is
clear that it involves three separate memory operations. 

An lvalue denotes the contents of a range of memory addresses. This range 
is denoted as a host object along with an offset within the object. The 
host object can be of two kinds: a local or global variable, or an object 
whose address is in a pointer expression. We distinguish the two cases so 
that we can tell quickly whether we are accessing some component of a 
variable directly or we are accessing a memory location through a pointer.
To make it easy to 
tell what an lvalue means CIL represents lvalues as a host object and an
offset (see {!Cil.lval}). The host object (represented as
{!Cil.lhost}) can be a local or global variable or can be the object
pointed-to by a pointer expression. The offset (represented as
{!Cil.offset}) is a sequence of field or array index designators.

 Both the typing rules and the meaning of an lvalue is very precisely
specified in CIL. 

 The following are a few useful function for operating on lvalues:
- {!Cil.mkMem} - makes an lvalue of [Mem] kind. Use this to ensure
that certain equivalent forms of lvalues are canonized. 
For example, [*&x = x]. 
- {!Cil.typeOfLval} - the type of an lvalue
- {!Cil.typeOffset} - the type of an offset, given the type of the
host. 
- {!Cil.addOffset} and {!Cil.addOffsetLval} - extend sequences
of offsets.
- {!Cil.removeOffset} and {!Cil.removeOffsetLval} - shrink sequences
of offsets.

The following equivalences hold {v 
Mem(AddrOf(Mem a, aoff)), off   = Mem a, aoff + off 
Mem(AddrOf(Var v, aoff)), off   = Var v, aoff + off 
AddrOf (Mem a, NoOffset)        = a                 
 v}

*)
(** An lvalue *)
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
  * of the lvalue and changes the denoted type, essentially focusing to some 
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


(** {b Initializers.} 
A special kind of expressions are those that can appear as initializers for
global variables (initialization of local variables is turned into
assignments). The initializers are represented as type {!Cil.init}. You
can create initializers with {!Cil.makeZeroInit} and you can conveniently
scan compound initializers them with {!Cil.foldLeftCompound} or with {!Cil.foldLeftCompoundAll}. 
*)
(** Initializers for global variables. *)
and init = 
  | SingleInit   of exp   (** A single initializer *)
  | CompoundInit   of typ * (offset * init) list
    (** Used only for initializers of structures, unions and arrays. The 
     * offsets are all of the form [Field(f, NoOffset)] or [Index(i, 
     * NoOffset)] and specify the field or the index being initialized. For 
     * structures all fields must have an initializer (except the unnamed 
     * bitfields), in the proper order. This is necessary since the offsets 
     * are not printed. For unions there must be exactly one initializer. If 
     * the initializer is not for the first field then a field designator is 
     * printed, so you better be on GCC since MSVC does not understand this. 
     * For arrays, however, we allow you to give only a prefix of the 
     * initializers. You can scan an initializer list with 
     * {!Cil.foldLeftCompound} or with {!Cil.foldLeftCompoundAll}. *)


(** We want to be able to update an initializer in a global variable, so we 
 * define it as a mutable field *)
and initinfo = {
    mutable init : init option;
  } 

(** {b Function definitions.} 
A function definition is always introduced with a [GFun] constructor at the
top level. All the information about the function is stored into a
{!Cil.fundec}. Some of the information (e.g. its name, type,
storage, attributes) is stored as a {!Cil.varinfo} that is a field of the
[fundec]. To refer to the function from the expression language you must use
the [varinfo]. 

 The function definition contains, in addition to the body, a list of all the
local variables and separately a list of the formals. Both kind of variables
can be referred to in the body of the function. The formals must also be shared
with the formals that appear in the function type. For that reason, to
manipulate formals you should use the provided functions
{!Cil.makeFormalVar} and {!Cil.setFormals} and {!Cil.makeFormalVar}. 
*)
(** Function definitions. *)
and fundec =
    { mutable svar:     varinfo;        
         (** Holds the name and type as a variable, so we can refer to it 
          * easily from the program. All references to this function either 
          * in a function call or in a prototype must point to the same 
          * [varinfo]. *)
      mutable sformals: varinfo list;   
        (** Formals. These must be in the same order and with the same 
         * information as the formal information in the type of the function. 
         * Use {!Cil.setFormals} or 
         * {!Cil.setFunctionType} or {!Cil.makeFormalVar} 
         * to set these formals and ensure that they 
         * are reflected in the function type. Do not make copies of these 
         * because the body refers to them. *)
      mutable slocals: varinfo list;    
        (** Locals. Does NOT include the sformals. Do not make copies of 
         * these because the body refers to them. *)
      mutable smaxid: int;           (** Max local id. Starts at 0. Used for 
                                      * creating the names of new temporary 
                                      * variables. Updated by 
                                      * {!Cil.makeLocalVar} and 
                                      * {!Cil.makeTempVar}. You can also use 
                                      * {!Cil.setMaxId} to set it after you 
                                      * have added the formals and locals. *)
      mutable sbody: block;          (** The function body. *)
      mutable smaxstmtid: int option;  (** max id of a (reachable) statement 
                                        * in this function, if we have 
                                        * computed it. range = 0 ... 
                                        * (smaxstmtid-1). This is computed by 
                                        * {!Cil.computeCFGInfo}. *)
      mutable sallstmts: stmt list;  (** After you call {!Cil.computeCFGInfo} 
                                      * this field is set to contain all 
                                      * statements in the function *)
    }


(** A block is a sequence of statements with the control falling through from 
    one element to the next *)
and block = 
   { mutable battrs: attributes;      (** Attributes for the block *)
     mutable bstmts: stmt list;       (** The statements comprising the block*)
   } 


(** {b Statements}. 
CIL statements are the structural elements that make the CFG. They are 
represented using the type {!Cil.stmt}. Every
statement has a (possibly empty) list of labels. The
{!Cil.stmtkind} field of a statement indicates what kind of statement it 
is.

 Use {!Cil.mkStmt} to make a statement and the fill-in the fields. 

CIL also comes with support for control-flow graphs. The [sid] field in
[stmt] can be used to give unique numbers to statements, and the [succs]
and [preds] fields can be used to maintain a list of successors and
predecessors for every statement. The CFG information is not computed by
default. Instead you must explicitly use the functions
{!Cil.prepareCFG} and {!Cil.computeCFGInfo} to do it.

*)
(** Statements. *)
and stmt = {
    mutable labels: label list;        
    (** Whether the statement starts with some labels, case statements or 
     * default statements. *)

    mutable skind: stmtkind;           
    (** The kind of statement *)

    mutable sid: int;                  
    (** A number (>= 0) that is unique in a function. Filled in only after 
     * the CFG is computed. *)
    mutable succs: stmt list;          
    (** The successor statements. They can always be computed from the skind 
     * and the context in which this statement appears. Filled in only after 
     * the CFG is computed. *)
    mutable preds: stmt list;          
    (** The inverse of the succs function. *)
  } 

(** Labels *)
and label = 
    Label of string * location * bool   
          (** A real label. If the bool is "true", the label is from the 
           * input source program. If the bool is "false", the label was 
           * created by CIL or some other transformation *)
  | Case of exp * location              (** A case statement. This expression 
                                         * is lowered into a constant if 
                                         * {!Cil.lowerConstants} is set to 
                                         * true. *)
  | Default of location                 (** A default statement *)



(** The various kinds of control-flow statements statements *)
and stmtkind = 
  | Instr  of instr list               
  (** A group of instructions that do not contain control flow. Control 
   * implicitly falls through. *)

  | Return of exp option * location     
   (** The return statement. This is a leaf in the CFG. *)

  | Goto of stmt ref * location         
   (** A goto statement. Appears from actual goto's in the code or from 
    * goto's that have been inserted during elaboration. The reference 
    * points to the statement that is the target of the Goto. This means that 
    * you have to update the reference whenever you replace the target 
    * statement. The target statement MUST have at least a label. *)

  | Break of location                   
   (** A break to the end of the nearest enclosing loop or Switch *)

  | Continue of location                
   (** A continue to the start of the nearest enclosing loop *)
  | If of exp * block * block * location 
   (** A conditional. Two successors, the "then" and the "else" branches. 
    * Both branches fall-through to the successor of the If statement. *)

  | Switch of exp * block * (stmt list) * location  
   (** A switch statement. The statements that implement the cases can be 
    * reached through the provided list. For each such target you can find 
    * among its labels what cases it implements. The statements that 
    * implement the cases are somewhere within the provided [block]. *)

(*
  | Loop of block * location * (stmt option) * (stmt option)
    (** A [while(1)] loop. The termination test is implemented in the body of 
     * a loop using a [Break] statement. If prepareCFG has been called,
     * the first stmt option will point to the stmt containing the continue
     * label for this loop and the second will point to the stmt containing
     * the break label for this loop. *)
*)

  | While of exp * block * location
    (** A [while] loop. *)

  | DoWhile of exp * block * location
    (** A [do...while] loop. *)

  | For of block * exp * block * block * location
    (** A [for] loop. *)

  | Block of block                      
    (** Just a block of statements. Use it as a way to keep some block 
     * attributes local *)

    (** On MSVC we support structured exception handling. This is what you 
     * might expect. Control can get into the finally block either from the 
     * end of the body block, or if an exception is thrown. *)
  | TryFinally of block * block * location

    (** On MSVC we support structured exception handling. The try/except 
     * statement is a bit tricky: 
         [__try { blk } 
         __except (e) {
            handler
         }]

         The argument to __except  must be an expression. However, we keep a 
         list of instructions AND an expression in case you need to make 
         function calls. We'll print those as a comma expression. The control 
         can get to the __except expression only if an exception is thrown. 
         After that, depending on the value of the expression the control 
         goes to the handler, propagates the exception, or retries the 
         exception !!!
     *)      
  | TryExcept of block * (instr list * exp) * block * location
  

(** {b Instructions}. 
 An instruction {!Cil.instr} is a statement that has no local
(intraprocedural) control flow. It can be either an assignment,
function call, or an inline assembly instruction. *)

(** Instructions. *)
and instr =
    Set        of lval * exp * location  
   (** An assignment. The type of the expression is guaranteed to be the same 
    * with that of the lvalue *)
  | Call       of lval option * exp * exp list * location
   (** A function call with the (optional) result placed in an lval. It is 
    * possible that the returned type of the function is not identical to 
    * that of the lvalue. In that case a cast is printed. The type of the 
    * actual arguments are identical to those of the declared formals. The 
    * number of arguments is the same as that of the declared formals, except 
    * for vararg functions. This construct is also used to encode a call to 
    * "__builtin_va_arg". In this case the second argument (which should be a 
    * type T) is encoded SizeOf(T) *)

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
    (** There are for storing inline assembly. They follow the GCC 
      * specification: 
{v 
  asm [volatile] ("...template..." "..template.."
                  : "c1" (o1), "c2" (o2), ..., "cN" (oN)
                  : "d1" (i1), "d2" (i2), ..., "dM" (iM)
                  : "r1", "r2", ..., "nL" );
 v}

where the parts are

  - [volatile] (optional): when present, the assembler instruction
    cannot be removed, moved, or otherwise optimized
  - template: a sequence of strings, with %0, %1, %2, etc. in the string to 
    refer to the input and output expressions. I think they're numbered
    consecutively, but the docs don't specify. Each string is printed on 
    a separate line. This is the only part that is present for MSVC inline
    assembly.
  - "ci" (oi): pairs of constraint-string and output-lval; the 
    constraint specifies that the register used must have some
    property, like being a floating-point register; the constraint
    string for outputs also has "=" to indicate it is written, or
    "+" to indicate it is both read and written; 'oi' is the
    name of a C lvalue (probably a variable name) to be used as
    the output destination
  - "dj" (ij): pairs of constraint and input expression; the constraint
    is similar to the "ci"s.  the 'ij' is an arbitrary C expression
    to be loaded into the corresponding register
  - "rk": registers to be regarded as "clobbered" by the instruction;
    "memory" may be specified for arbitrary memory effects

an example (from gcc manual):
{v 
  asm volatile ("movc3 %0,%1,%2"
                : /* no outputs */
                : "g" (from), "g" (to), "g" (count)
                : "r0", "r1", "r2", "r3", "r4", "r5");
 v}
*)

(** Describes a location in a source file. *)
and location = { 
    line: int;		   (** The line number. -1 means "do not know" *)
    file: string;          (** The name of the source file*)
    byte: int;             (** The byte position in the source file *)
}


(** Type signatures. Two types are identical iff they have identical 
 * signatures. These contain the same information as types but canonicalized. 
 * For example, two function types that are identical except for the name of 
 * the formal arguments are given the same signature. Also, [TNamed] 
 * constructors are unrolled. *)
and typsig = 
    TSArray of typsig * int64 option * attribute list
  | TSPtr of typsig * attribute list
  | TSComp of bool * string * attribute list
  | TSFun of typsig * typsig list * bool * attribute list
  | TSEnum of string * attribute list
  | TSBase of typ



(** {b Lowering Options} *)

val lowerConstants: bool ref
    (** Do lower constants (default true) *)

val insertImplicitCasts: bool ref
    (** Do insert implicit casts (default true) *)

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
     * checking is enabled (--check is passed to cilly). Set this to true if 
     * your feature makes any changes for the program. *)
}

(** Comparison function for locations.
 ** Compares first by filename, then line, then byte *)
val compareLoc: location -> location -> int

(** {b Values for manipulating globals} *)

(** Make an empty function *)
val emptyFunction: string -> fundec

(** Update the formals of a [fundec] and make sure that the function type 
    has the same information. Will copy the name as well into the type. *)
val setFormals: fundec -> varinfo list -> unit

(** Set the types of arguments and results as given by the function type 
 * passed as the second argument. Will not copy the names from the function 
 * type to the formals *)
val setFunctionType: fundec -> typ -> unit


(** Set the type of the function and make formal arguments for them *)
val setFunctionTypeMakeFormals: fundec -> typ -> unit

(** Update the smaxid after you have populated with locals and formals 
 * (unless you constructed those using {!Cil.makeLocalVar} or 
 * {!Cil.makeTempVar}. *)
val setMaxId: fundec -> unit

(** A dummy function declaration handy when you need one as a placeholder. It 
 * contains inside a dummy varinfo. *)
val dummyFunDec: fundec

(** A dummy file *)
val dummyFile: file

(** Write a {!Cil.file} in binary form to the filesystem. The file can be
 * read back in later using {!Cil.loadBinaryFile}, possibly saving parsing
 * time. The second argument is the name of the file that should be
 * created. *)
val saveBinaryFile : file -> string -> unit

(** Write a {!Cil.file} in binary form to the filesystem. The file can be
 * read back in later using {!Cil.loadBinaryFile}, possibly saving parsing
 * time. Does not close the channel. *)
val saveBinaryFileChannel : file -> out_channel -> unit

(** Read a {!Cil.file} in binary form from the filesystem. The first
 * argument is the name of a file previously created by
 * {!Cil.saveBinaryFile}. *)
val loadBinaryFile : string -> file 

(** Get the global initializer and create one if it does not already exist. 
 * When it creates a global initializer it attempts to place a call to it in 
 * the main function named by the optional argument (default "main")  *)
val getGlobInit: ?main_name:string -> file -> fundec  

(** Iterate over all globals, including the global initializer *)
val iterGlobals: file -> (global -> unit) -> unit

(** Fold over all globals, including the global initializer *)
val foldGlobals: file -> ('a -> global -> 'a) -> 'a -> 'a

(** Map over all globals, including the global initializer and change things 
    in place *)
val mapGlobals: file -> (global -> global) -> unit

val new_sid : unit -> int

(** Prepare a function for CFG information computation by
  * {!Cil.computeCFGInfo}. This function converts all [Break], [Switch],
  * [Default] and [Continue] {!Cil.stmtkind}s and {!Cil.label}s into [If]s
  * and [Goto]s, giving the function body a very CFG-like character. This
  * function modifies its argument in place. *)
val prepareCFG: fundec -> unit

(** Compute the CFG information for all statements in a fundec and return a 
  * list of the statements. The input fundec cannot have [Break], [Switch], 
  * [Default], or [Continue] {!Cil.stmtkind}s or {!Cil.label}s. Use
  * {!Cil.prepareCFG} to transform them away.  The second argument should
  * be [true] if you wish a global statement number, [false] if you wish a
  * local (per-function) statement numbering. The list of statements is set 
  * in the sallstmts field of a fundec. 
  * 
  * NOTE: unless you want the simpler control-flow graph provided by
  * prepareCFG, or you need the function's smaxstmtid and sallstmt fields
  * filled in, we recommend you use {!Cfg.computeFileCFG} instead of this
  * function to compute control-flow information.
  * {!Cfg.computeFileCFG} is newer and will handle switch, break, and
  * continue correctly.*)
val computeCFGInfo: fundec -> bool -> unit


(** Create a deep copy of a function. There should be no sharing between the 
 * copy and the original function *)
val copyFunction: fundec -> string -> fundec 


(** CIL keeps the types at the beginning of the file and the variables at the 
 * end of the file. This function will take a global and add it to the 
 * corresponding stack. Its operation is actually more complicated because if 
 * the global declares a type that contains references to variables (e.g. in 
 * sizeof in an array length) then it will also add declarations for the 
 * variables to the types stack *)
val pushGlobal: global -> types: global list ref 
                       -> variables: global list ref -> unit

(** An empty statement. Used in pretty printing *)
val invalidStmt: stmt

(** A list of the GCC built-in functions. Maps the name to the result and 
  * argument types, and whether it is vararg *)
val gccBuiltins: (string, typ * typ list * bool) Hashtbl.t


(** A list of the MSVC built-in functions. Maps the name to the result and 
 * argument types, and whether it is vararg *)
val msvcBuiltins: (string, typ * typ list * bool) Hashtbl.t
 
(** {b Values for manipulating initializers} *)


(** Make a initializer for zero-ing a data type *)
val makeZeroInit: typ -> init


(** Fold over the list of initializers in a Compound. [doinit] is called on 
 * every present initializer, even if it is of compound type. In the case of 
 * arrays there might be missing zero-initializers at the end of the list. 
 * These are not scanned. This is much like [List.fold_left] except we also 
 * pass the type of the initializer *)
val foldLeftCompound: 
    doinit: (offset -> init -> typ -> 'a -> 'a) ->
    ct: typ ->
    initl: (offset * init) list ->
    acc: 'a -> 'a


(** Fold over the list of initializers in a Compound, like 
 * {!Cil.foldLeftCompound} but in the case of an array it scans even missing 
 * zero initializers at the end of the array *)
val foldLeftCompoundAll: 
    doinit: (offset -> init -> typ -> 'a -> 'a) ->
    ct: typ ->
    initl: (offset * init) list ->
    acc: 'a -> 'a



(** {b Values for manipulating types} *)

(** void *)
val voidType: typ

(* is the given type "void"? *)
val isVoidType: typ -> bool

(* is the given type "void *"? *)
val isVoidPtrType: typ -> bool

(** int *)
val intType: typ

(** unsigned int *)
val uintType: typ

(** long *)
val longType: typ

(** unsigned long *)
val ulongType: typ

(** char *)
val charType: typ

(** char * *)
val charPtrType: typ

(** wchar_t (depends on architecture) and is set when you call 
 * {!Cil.initCIL}. *)
val wcharKind: ikind ref
val wcharType: typ ref 

(** char const * *)
val charConstPtrType: typ

(** void * *)
val voidPtrType: typ

(** int * *)
val intPtrType: typ

(** unsigned int * *)
val uintPtrType: typ

(** double *)
val doubleType: typ

(* An unsigned integer type that fits pointers. Depends on {!Cil.msvcMode} 
 *  and is set when you call {!Cil.initCIL}. *)
val upointType: typ ref

(* An unsigned integer type that is the type of sizeof. Depends on 
 * {!Cil.msvcMode} and is set when you call {!Cil.initCIL}.  *)
val typeOfSizeOf: typ ref

(** Returns true if and only if the given integer type is signed. *)
val isSigned: ikind -> bool


(** Creates a a (potentially recursive) composite type. The arguments are: 
 * (1) a boolean indicating whether it is a struct or a union, (2) the name 
 * (always non-empty), (3) a function that when given a representation of the 
 * structure type constructs the type of the fields recursive type (the first 
 * argument is only useful when some fields need to refer to the type of the 
 * structure itself), and (4) a list of attributes to be associated with the 
 * composite type. The resulting compinfo has the field "cdefined" only if 
 * the list of fields is non-empty. *)
val mkCompInfo: bool ->      (* whether it is a struct or a union *)
               string ->     (* name of the composite type; cannot be empty *)
               (compinfo -> 
                  (string * typ * int option * attributes * location) list) ->
               (* a function that when given a forward 
                  representation of the structure type constructs the type of 
                  the fields. The function can ignore this argument if not 
                  constructing a recursive type.  *)
               attributes -> compinfo

(** Makes a shallow copy of a {!Cil.compinfo} changing the name and the key.*)
val copyCompInfo: compinfo -> string -> compinfo

(** This is a constant used as the name of an unnamed bitfield. These fields
    do not participate in initialization and their name is not printed. *)
val missingFieldName: string 

(** Get the full name of a comp *)
val compFullName: compinfo -> string

(** Returns true if this is a complete type. 
   This means that sizeof(t) makes sense. 
   Incomplete types are not yet defined 
   structures and empty arrays. *)
val isCompleteType: typ -> bool  

(** Unroll a type until it exposes a non 
 * [TNamed]. Will collect all attributes appearing in [TNamed]!!! *)
val unrollType: typ -> typ  

(** Unroll all the TNamed in a type (even under type constructors such as 
 * [TPtr], [TFun] or [TArray]. Does not unroll the types of fields in [TComp] 
 * types. Will collect all attributes *)
val unrollTypeDeep: typ -> typ 

(** Separate out the storage-modifier name attributes *)
val separateStorageModifiers: attribute list -> attribute list * attribute list

(** True if the argument is an integral type (i.e. integer or enum) *)
val isIntegralType: typ -> bool

(** True if the argument is an arithmetic type (i.e. integer, enum or 
    floating point *)
val isArithmeticType: typ -> bool

(**True if the argument is a pointer type *)
val isPointerType: typ -> bool

(** True if the argument is a function type *)
val isFunctionType: typ -> bool

(** Obtain the argument list ([] if None) *)
val argsToList: (string * typ * attributes) list option 
                  -> (string * typ * attributes) list

(** True if the argument is an array type *)
val isArrayType: typ -> bool

(** Raised when {!Cil.lenOfArray} fails either because the length is [None] 
  * or because it is a non-constant expression *)
exception LenOfArray

(** Call to compute the array length as present in the array type, to an 
  * integer. Raises {!Cil.LenOfArray} if not able to compute the length, such 
  * as when there is no length or the length is not a constant. *)
val lenOfArray: exp option -> int

(** Return a named fieldinfo in compinfo, or raise Not_found *)
val getCompField: compinfo -> string -> fieldinfo


(** A datatype to be used in conjunction with [existsType] *)
type existsAction = 
    ExistsTrue                          (* We have found it *)
  | ExistsFalse                         (* Stop processing this branch *)
  | ExistsMaybe                         (* This node is not what we are 
                                         * looking for but maybe its 
                                         * successors are *)

(** Scans a type by applying the function on all elements. 
    When the function returns ExistsTrue, the scan stops with
    true. When the function returns ExistsFalse then the current branch is not
    scanned anymore. Care is taken to 
    apply the function only once on each composite type, thus avoiding 
    circularity. When the function returns ExistsMaybe then the types that 
    construct the current type are scanned (e.g. the base type for TPtr and 
    TArray, the type of fields for a TComp, etc). *)
val existsType: (typ -> existsAction) -> typ -> bool


(** Given a function type split it into return type, 
 * arguments, is_vararg and attributes. An error is raised if the type is not 
 * a function type *)
val splitFunctionType: 
    typ -> typ * (string * typ * attributes) list option * bool * attributes
(** Same as {!Cil.splitFunctionType} but takes a varinfo. Prints a nicer 
 * error message if the varinfo is not for a function *)
val splitFunctionTypeVI: 
    varinfo -> typ * (string * typ * attributes) list option * bool * attributes


(** {b Type signatures} *)

(** Type signatures. Two types are identical iff they have identical 
 * signatures. These contain the same information as types but canonicalized. 
 * For example, two function types that are identical except for the name of 
 * the formal arguments are given the same signature. Also, [TNamed] 
 * constructors are unrolled. You shoud use [Util.equals] to compare type 
 * signatures because they might still contain circular structures (through 
 * attributes, and sizeof) *)

(** Print a type signature *)
val d_typsig: unit -> typsig -> Pretty.doc

(** Compute a type signature *)
val typeSig: typ -> typsig

(** Like {!Cil.typeSig} but customize the incorporation of attributes.
    Use ~ignoreSign:true to convert all signed integer types to unsigned,
    so that signed and unsigned will compare the same. *)
val typeSigWithAttrs: ?ignoreSign:bool -> (attributes -> attributes) -> typ -> typsig

(** Replace the attributes of a signature (only at top level) *)
val setTypeSigAttrs: attributes -> typsig -> typsig 

(** Get the top-level attributes of a signature *)
val typeSigAttrs: typsig -> attributes

(*********************************************************)
(**  LVALUES *)

(** Make a varinfo. Use this (rarely) to make a raw varinfo. Use other 
 * functions to make locals ({!Cil.makeLocalVar} or {!Cil.makeFormalVar} or 
 * {!Cil.makeTempVar}) and globals ({!Cil.makeGlobalVar}). Note that this 
 * function will assign a new identifier. The first argument specifies 
 * whether the varinfo is for a global. *)
val makeVarinfo: bool -> string -> typ -> varinfo

(** Make a formal variable for a function. Insert it in both the sformals 
    and the type of the function. You can optionally specify where to insert 
    this one. If where = "^" then it is inserted first. If where = "$" then 
    it is inserted last. Otherwise where must be the name of a formal after 
    which to insert this. By default it is inserted at the end. *)
val makeFormalVar: fundec -> ?where:string -> string -> typ -> varinfo

(** Make a local variable and add it to a function's slocals (only if insert = 
    true, which is the default). Make sure you know what you are doing if you 
    set insert=false.  *)
val makeLocalVar: fundec -> ?insert:bool -> string -> typ -> varinfo

(** Make a temporary variable and add it to a function's slocals. The name of 
    the temporary variable will be generated based on the given name hint so 
    that to avoid conflicts with other locals.  *)
val makeTempVar: fundec -> ?name: string -> typ -> varinfo


(** Make a global variable. Your responsibility to make sure that the name 
    is unique *) 
val makeGlobalVar: string -> typ -> varinfo

(** Make a shallow copy of a [varinfo] and assign a new identifier *)
val copyVarinfo: varinfo -> string -> varinfo


(** Generate a new variable ID. This will be different than any variable ID 
 * that is generated by {!Cil.makeLocalVar} and friends *)
val newVID: unit -> int

(** Add an offset at the end of an lvalue. Make sure the type of the lvalue 
 * and the offset are compatible. *)
val addOffsetLval: offset -> lval -> lval 

(** [addOffset o1 o2] adds [o1] to the end of [o2]. *)
val addOffset:     offset -> offset -> offset

(** Remove ONE offset from the end of an lvalue. Returns the lvalue with the 
 * trimmed offset and the final offset. If the final offset is [NoOffset] 
 * then the original [lval] did not have an offset. *)
val removeOffsetLval: lval -> lval * offset

(** Remove ONE offset from the end of an offset sequence. Returns the 
 * trimmed offset and the final offset. If the final offset is [NoOffset] 
 * then the original [lval] did not have an offset. *)
val removeOffset:   offset -> offset * offset

(** Compute the type of an lvalue *)
val typeOfLval: lval -> typ

(** Compute the type of an offset from a base type *)
val typeOffset: typ -> offset -> typ 


(*******************************************************)
(** {b Values for manipulating expressions} *)


(* Construct integer constants *)

(** 0 *)
val zero: exp

(** 1 *)
val one: exp

(** -1 *)
val mone: exp


(** Construct an integer of a given kind, using OCaml's int64 type. If needed 
  * it will truncate the integer to be within the representable range for the 
  * given kind. *)
val kinteger64: ikind -> int64 -> exp

(** Construct an integer of a given kind. Converts the integer to int64 and 
  * then uses kinteger64. This might truncate the value if you use a kind 
  * that cannot represent the given integer. This can only happen for one of 
  * the Char or Short kinds *)
val kinteger: ikind -> int -> exp

(** Construct an integer of kind IInt. You can use this always since the 
    OCaml integers are 31 bits and are guaranteed to fit in an IInt *)
val integer: int -> exp


(** True if the given expression is a (possibly cast'ed) 
    character or an integer constant *)
val isInteger: exp -> int64 option

(** True if the expression is a compile-time constant *)
val isConstant: exp -> bool

(** True if the given expression is a (possibly cast'ed) integer or character 
    constant with value zero *)
val isZero: exp -> bool

(** Given the character c in a (CChr c), sign-extend it to 32 bits.
  (This is the official way of interpreting character constants, according to
  ISO C 6.4.4.4.10, which says that character constants are chars cast to ints)
  Returns CInt64(sign-extened c, IInt, None) *)
val charConstToInt: char -> constant

(** Do constant folding on an expression. If the first argument is true then 
    will also compute compiler-dependent expressions such as sizeof *)    
val constFold: bool -> exp -> exp

(** Do constant folding on a binary operation. The bulk of the work done by 
    [constFold] is done here. If the first argument is true then 
    will also compute compiler-dependent expressions such as sizeof *)
val constFoldBinOp: bool -> binop -> exp -> exp -> typ -> exp

(** Increment an expression. Can be arithmetic or pointer type *) 
val increm: exp -> int -> exp


(** Makes an lvalue out of a given variable *)
val var: varinfo -> lval

(** Make an AddrOf. Given an lvalue of type T will give back an expression of 
    type ptr(T). It optimizes somewhat expressions like "& v" and "& v[0]"  *)
val mkAddrOf: lval -> exp               


(** Like mkAddrOf except if the type of lval is an array then it uses 
    StartOf. This is the right operation for getting a pointer to the start 
    of the storage denoted by lval. *)
val mkAddrOrStartOf: lval -> exp

(** Make a Mem, while optimizing AddrOf. The type of the addr must be 
    TPtr(t) and the type of the resulting lval is t. Note that in CIL the 
    implicit conversion between an array and the pointer to the first 
    element does not apply. You must do the conversion yourself using 
    StartOf *)
val mkMem: addr:exp -> off:offset -> lval

(** Make an expression that is a string constant (of pointer type) *)
val mkString: string -> exp

(** Construct a cast when having the old type of the expression. If the new 
  * type is the same as the old type, then no cast is added. *)
val mkCastT: e:exp -> oldt:typ -> newt:typ -> exp

(** Like {!Cil.mkCastT} but uses typeOf to get [oldt] *)  
val mkCast: e:exp -> newt:typ -> exp 

(** Removes casts from this expression, but ignores casts within
  other expression constructs.  So we delete the (A) and (B) casts from 
  "(A)(B)(x + (C)y)", but leave the (C) cast. *)
val stripCasts: exp -> exp

(** Compute the type of an expression *)
val typeOf: exp -> typ

(** Convert a string representing a C integer literal to an expression. 
 * Handles the prefixes 0x and 0 and the suffixes L, U, UL, LL, ULL *)
val parseInt: string -> exp


(**********************************************)
(** {b Values for manipulating statements} *)

(** Construct a statement, given its kind. Initialize the [sid] field to -1,
    and [labels], [succs] and [preds] to the empty list *)
val mkStmt: stmtkind -> stmt

(** Construct a block with no attributes, given a list of statements *)
val mkBlock: stmt list -> block

(** Construct a statement consisting of just one instruction *)
val mkStmtOneInstr: instr -> stmt

(** Try to compress statements so as to get maximal basic blocks *)
(* use this instead of List.@ because you get fewer basic blocks *)
val compactStmts: stmt list -> stmt list

(** Returns an empty statement (of kind [Instr]) *)
val mkEmptyStmt: unit -> stmt

(** A instr to serve as a placeholder *)
val dummyInstr: instr

(** A statement consisting of just [dummyInstr] *)
val dummyStmt: stmt

(** Make a while loop. Can contain Break or Continue *)
val mkWhile: guard:exp -> body:stmt list -> stmt list

(** Make a for loop for(i=start; i<past; i += incr) \{ ... \}. The body 
    can contain Break but not Continue. Can be used with i a pointer 
    or an integer. Start and done must have the same type but incr 
    must be an integer *)
val mkForIncr:  iter:varinfo -> first:exp -> stopat:exp -> incr:exp 
                 -> body:stmt list -> stmt list

(** Make a for loop for(start; guard; next) \{ ... \}. The body can 
    contain Break but not Continue !!! *) 
val mkFor: start:stmt list -> guard:exp -> next: stmt list -> 
                                       body: stmt list -> stmt list
 


(**************************************************)
(** {b Values for manipulating attributes} *)

(** Various classes of attributes *)
type attributeClass = 
    AttrName of bool 
        (** Attribute of a name. If argument is true and we are on MSVC then 
            the attribute is printed using __declspec as part of the storage 
            specifier  *)
  | AttrFunType of bool 
        (** Attribute of a function type. If argument is true and we are on 
            MSVC then the attribute is printed just before the function name *)
  | AttrType  (** Attribute of a type *)

(** This table contains the mapping of predefined attributes to classes. 
    Extend this table with more attributes as you need. This table is used to 
    determine how to associate attributes with names or types *)
val attributeHash: (string, attributeClass) Hashtbl.t

(** Partition the attributes into classes:name attributes, function type, 
    and type attributes *)
val partitionAttributes:  default:attributeClass -> 
                         attributes -> attribute list * (* AttrName *)
                                       attribute list * (* AttrFunType *)
                                           attribute list   (* AttrType *)

(** Add an attribute. Maintains the attributes in sorted order of the second 
    argument *)
val addAttribute: attribute -> attributes -> attributes
    
(** Add a list of attributes. Maintains the attributes in sorted order. The 
    second argument must be sorted, but not necessarily the first *)
val addAttributes: attribute list -> attributes -> attributes

(** Remove all attributes with the given name. Maintains the attributes in 
    sorted order.  *)
val dropAttribute: string -> attributes -> attributes

(** Remove all attributes with names appearing in the string list.
 *  Maintains the attributes in sorted order *)
val dropAttributes: string list -> attributes -> attributes

(** Retains attributes with the given name *)
val filterAttributes: string -> attributes -> attributes

(** True if the named attribute appears in the attribute list. The list of
    attributes must be sorted.  *)
val hasAttribute: string -> attributes -> bool

(** Returns all the attributes contained in a type. This requires a traversal 
    of the type structure, in case of composite, enumeration and named types *)
val typeAttrs: typ -> attribute list

val setTypeAttrs: typ -> attributes -> typ (* Resets the attributes *)


(** Add some attributes to a type *)
val typeAddAttributes: attribute list -> typ -> typ

(** Remove all attributes with the given names from a type. Note that this
    does not remove attributes from typedef and tag definitions, just from 
    their uses *)
val typeRemoveAttributes: string list -> typ -> typ


(******************
 ******************  VISITOR
 ******************)
(** {b The visitor} *)

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



(** A visitor interface for traversing CIL trees. Create instantiations of 
 * this type by specializing the class {!Cil.nopCilVisitor}. Each of the 
 * specialized visiting functions can also call the [queueInstr] to specify 
 * that some instructions should be inserted before the current instruction 
 * or statement. Use syntax like [self#queueInstr] to call a method
 * associated with the current object. *)
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
    (** Invoked on each expression occurrence. The subtrees are the 
     * subexpressions, the types (for a [Cast] or [SizeOf] expression) or the 
     * variable use. *)

  method vlval: lval -> lval visitAction        
    (** Invoked on each lvalue occurrence *)

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
    (** Control-flow statement. The default [DoChildren] action does not 
     * create a new statement when the components change. Instead it updates 
     * the contents of the original statement. This is done to preserve the 
     * sharing with [Goto] and [Case] statements that point to the original 
     * statement. If you use the [ChangeTo] action then you should take care 
     * of preserving that sharing yourself.  *)

  method vblock: block -> block visitAction     (** Block. *)
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

    (** Add here instructions while visiting to queue them to preceede the 
     * current statement or instruction being processed. Use this method only 
     * when you are visiting an expression that is inside a function body, or 
     * a statement, because otherwise there will no place for the visitor to 
     * place your instructions. *)
  method queueInstr: instr list -> unit

    (** Gets the queue of instructions and resets the queue. This is done 
     * automatically for you when you visit statments. *)
  method unqueueInstr: unit -> instr list

end

(** Default Visitor. Traverses the CIL tree without modifying anything *)
class nopCilVisitor: cilVisitor

(* other cil constructs *)

(** Visit a file. This will will re-cons all globals TWICE (so that it is 
 * tail-recursive). Use {!Cil.visitCilFileSameGlobals} if your visitor will 
 * not change the list of globals.  *)
val visitCilFile: cilVisitor -> file -> unit

(** A visitor for the whole file that does not change the globals (but maybe
 * changes things inside the globals). Use this function instead of
 * {!Cil.visitCilFile} whenever appropriate because it is more efficient for
 * long files. *)
val visitCilFileSameGlobals: cilVisitor -> file -> unit

(** Visit a global *)
val visitCilGlobal: cilVisitor -> global -> global list

(** Visit a function definition *)
val visitCilFunction: cilVisitor -> fundec -> fundec

(* Visit an expression *)
val visitCilExpr: cilVisitor -> exp -> exp

(** Visit an lvalue *)
val visitCilLval: cilVisitor -> lval -> lval

(** Visit an lvalue or recursive offset *)
val visitCilOffset: cilVisitor -> offset -> offset

(** Visit an initializer offset *)
val visitCilInitOffset: cilVisitor -> offset -> offset

(** Visit an instruction *)
val visitCilInstr: cilVisitor -> instr -> instr list

(** Visit a statement *)
val visitCilStmt: cilVisitor -> stmt -> stmt

(** Visit a block *)
val visitCilBlock: cilVisitor -> block -> block

(** Visit a type *)
val visitCilType: cilVisitor -> typ -> typ

(** Visit a variable declaration *)
val visitCilVarDecl: cilVisitor -> varinfo -> varinfo

(** Visit an initializer *)
val visitCilInit: cilVisitor -> init -> init


(** Visit a list of attributes *)
val visitCilAttributes: cilVisitor -> attribute list -> attribute list

(* And some generic visitors. The above are built with these *)


(** {b Utility functions} *)

(** Whether the pretty printer should print output for the MS VC compiler.
   Default is GCC. After you set this function you should call {!Cil.initCIL}. *)
val msvcMode: bool ref               


(** Whether to use the logical operands LAnd and LOr. By default, do not use 
 * them because they are unlike other expressions and do not evaluate both of 
 * their operands *)
val useLogicalOperators: bool ref


(** A visitor that does constant folding. Pass as argument whether you want 
 * machine specific simplifications to be done, or not. *)
val constFoldVisitor: bool -> cilVisitor

(** Styles of printing line directives *)
type lineDirectiveStyle =
  | LineComment
  | LinePreprocessorInput
  | LinePreprocessorOutput

(** How to print line directives *)
val lineDirectiveStyle: lineDirectiveStyle option ref

(** Whether we print something that will only be used as input to our own 
 * parser. In that case we are a bit more liberal in what we print *)
val print_CIL_Input: bool ref

(** Whether to print the CIL as they are, without trying to be smart and 
  * print nicer code. Normally this is false, in which case the pretty 
  * printer will turn the while(1) loops of CIL into nicer loops, will not 
  * print empty "else" blocks, etc. These is one case howewer in which if you 
  * turn this on you will get code that does not compile: if you use varargs 
  * the __builtin_va_arg function will be printed in its internal form. *)
val printCilAsIs: bool ref

(** The length used when wrapping output lines.  Setting this variable to
  * a large integer will prevent wrapping and make #line directives more
  * accurate.
  *)
val lineLength: int ref

(** Return the string 's' if we're printing output for gcc, suppres
 *  it if we're printing for CIL to parse back in.  the purpose is to
 *  hide things from gcc that it complains about, but still be able
 *  to do lossless transformations when CIL is the consumer *)
val forgcc: string -> string

(** {b Debugging support} *)

(** A reference to the current location. If you are careful to set this to 
 * the current location then you can use some built-in logging functions that 
 * will print the location. *)
val currentLoc: location ref

(** A reference to the current global being visited *)
val currentGlobal: global ref 


(** CIL has a fairly easy to use mechanism for printing error messages. This 
 * mechanism is built on top of the pretty-printer mechanism (see 
 * {!Pretty.doc}) and the error-message modules (see {!Errormsg.error}). 

 Here is a typical example for printing a log message: {v 
ignore (Errormsg.log "Expression %a is not positive (at %s:%i)\n"
                        d_exp e loc.file loc.line)
 v}

 and here is an example of how you print a fatal error message that stop the 
* execution: {v 
Errormsg.s (Errormsg.bug "Why am I here?")
 v}

 Notice that you can use C format strings with some extension. The most 
useful extension is "%a" that means to consumer the next two argument from 
the argument list and to apply the first to [unit] and then to the second 
and to print the resulting {!Pretty.doc}. For each major type in CIL there is 
a corresponding function that pretty-prints an element of that type:
*)


(** Pretty-print a location *)
val d_loc: unit -> location -> Pretty.doc

(** Pretty-print the {!Cil.currentLoc} *)
val d_thisloc: unit -> Pretty.doc

(** Pretty-print an integer of a given kind *)
val d_ikind: unit -> ikind -> Pretty.doc

(** Pretty-print a floating-point kind *)
val d_fkind: unit -> fkind -> Pretty.doc

(** Pretty-print storage-class information *)
val d_storage: unit -> storage -> Pretty.doc

(** Pretty-print a constant *)
val d_const: unit -> constant -> Pretty.doc


val derefStarLevel: int
val indexLevel: int
val arrowLevel: int
val addrOfLevel: int
val additiveLevel: int
val comparativeLevel: int
val bitwiseLevel: int

(** Parentheses level. An expression "a op b" is printed parenthesized if its 
 * parentheses level is >= that that of its context. Identifiers have the 
 * lowest level and weakly binding operators (e.g. |) have the largest level. 
 * The correctness criterion is that a smaller level MUST correspond to a 
 * stronger precedence!
 *)
val getParenthLevel: exp -> int

(** A printer interface for CIL trees. Create instantiations of 
 * this type by specializing the class {!Cil.defaultCilPrinterClass}. *)
class type cilPrinter = object
  method pVDecl: unit -> varinfo -> Pretty.doc
    (** Invoked for each variable declaration. Note that variable 
     * declarations are all the [GVar], [GVarDecl], [GFun], all the [varinfo] 
     * in formals of function types, and the formals and locals for function 
     * definitions. *)

  method pVar: varinfo -> Pretty.doc
    (** Invoked on each variable use. *)

  method pLval: unit -> lval -> Pretty.doc
    (** Invoked on each lvalue occurrence *)

  method pOffset: Pretty.doc -> offset -> Pretty.doc
    (** Invoked on each offset occurrence. The second argument is the base. *)

  method pInstr: unit -> instr -> Pretty.doc
    (** Invoked on each instruction occurrence. *)

  method pLabel: unit -> label -> Pretty.doc
    (** Print a label. *)

  method pStmt: unit -> stmt -> Pretty.doc
    (** Control-flow statement. This is used by 
     * {!Cil.printGlobal} and by {!Cil.dumpGlobal}. *)

  method dStmt: out_channel -> int -> stmt -> unit
    (** Dump a control-flow statement to a file with a given indentation. 
     * This is used by {!Cil.dumpGlobal}. *)

  method dBlock: out_channel -> int -> block -> unit
    (** Dump a control-flow block to a file with a given indentation. 
     * This is used by {!Cil.dumpGlobal}. *)

  method pBlock: unit -> block -> Pretty.doc

  method pBlock: unit -> block -> Pretty.doc
    (** Print a block. *)

  method pGlobal: unit -> global -> Pretty.doc
    (** Global (vars, types, etc.). This can be slow and is used only by 
     * {!Cil.printGlobal} but not by {!Cil.dumpGlobal}. *)

  method dGlobal: out_channel -> global -> unit
    (** Dump a global to a file with a given indentation. This is used by 
     * {!Cil.dumpGlobal} *)

  method pFieldDecl: unit -> fieldinfo -> Pretty.doc
    (** A field declaration *)

  method pType: Pretty.doc option -> unit -> typ -> Pretty.doc  
  (* Use of some type in some declaration. The first argument is used to print 
   * the declared element, or is None if we are just printing a type with no 
   * name being declared. Note that for structure/union and enumeration types 
   * the definition of the composite type is not visited. Use [vglob] to 
   * visit it.  *)

  method pAttr: attribute -> Pretty.doc * bool
    (** Attribute. Also return an indication whether this attribute must be 
      * printed inside the __attribute__ list or not. *)
   
  method pAttrParam: unit -> attrparam -> Pretty.doc 
    (** Attribute parameter *)
   
  method pAttrs: unit -> attributes -> Pretty.doc
    (** Attribute lists *)

  method pLineDirective: ?forcefile:bool -> location -> Pretty.doc
    (** Print a line-number. This is assumed to come always on an empty line. 
     * If the forcefile argument is present and is true then the file name 
     * will be printed always. Otherwise the file name is printed only if it 
     * is different from the last time time this function is called. The last 
     * file name is stored in a private field inside the cilPrinter object. *)

  method pStmtKind: stmt -> unit -> stmtkind -> Pretty.doc
    (** Print a statement kind. The code to be printed is given in the
     * {!Cil.stmtkind} argument.  The initial {!Cil.stmt} argument
     * records the statement which follows the one being printed;
     * {!Cil.defaultCilPrinterClass} uses this information to prettify
     * statement printing in certain special cases. *)

  method pExp: unit -> exp -> Pretty.doc
    (** Print expressions *) 

  method pInit: unit -> init -> Pretty.doc
    (** Print initializers. This can be slow and is used by 
     * {!Cil.printGlobal} but not by {!Cil.dumpGlobal}. *)

  method dInit: out_channel -> int -> init -> unit
    (** Dump a global to a file with a given indentation. This is used by 
     * {!Cil.dumpGlobal} *)
end

class defaultCilPrinterClass: cilPrinter
val defaultCilPrinter: cilPrinter

(** These are pretty-printers that will show you more details on the internal 
 * CIL representation, without trying hard to make it look like C *)
class plainCilPrinterClass: cilPrinter
val plainCilPrinter: cilPrinter

(* zra: This is the pretty printer that Maincil will use.
   by default it is set to defaultCilPrinter *)
val printerForMaincil: cilPrinter ref

(* Top-level printing functions *)
(** Print a type given a pretty printer *)
val printType: cilPrinter -> unit -> typ -> Pretty.doc
  
(** Print an expression given a pretty printer *)
val printExp: cilPrinter -> unit -> exp -> Pretty.doc

(** Print an lvalue given a pretty printer *)
val printLval: cilPrinter -> unit -> lval -> Pretty.doc

(** Print a global given a pretty printer *)
val printGlobal: cilPrinter -> unit -> global -> Pretty.doc 

(** Print an attribute given a pretty printer *)
val printAttr: cilPrinter -> unit -> attribute -> Pretty.doc 

(** Print a set of attributes given a pretty printer *)
val printAttrs: cilPrinter -> unit -> attributes -> Pretty.doc 

(** Print an instruction given a pretty printer *)
val printInstr: cilPrinter -> unit -> instr -> Pretty.doc 

(** Print a statement given a pretty printer. This can take very long 
 * (or even overflow the stack) for huge statements. Use {!Cil.dumpStmt} 
 * instead. *)
val printStmt: cilPrinter -> unit -> stmt -> Pretty.doc

(** Print a block given a pretty printer. This can take very long 
 * (or even overflow the stack) for huge block. Use {!Cil.dumpBlock} 
 * instead. *)
val printBlock: cilPrinter -> unit -> block -> Pretty.doc

(** Dump a statement to a file using a given indentation. Use this instead of 
 * {!Cil.printStmt} whenever possible. *)
val dumpStmt: cilPrinter -> out_channel -> int -> stmt -> unit

(** Dump a block to a file using a given indentation. Use this instead of 
 * {!Cil.printBlock} whenever possible. *)
val dumpBlock: cilPrinter -> out_channel -> int -> block -> unit

(** Print an initializer given a pretty printer. This can take very long 
 * (or even overflow the stack) for huge initializers. Use {!Cil.dumpInit} 
 * instead. *)
val printInit: cilPrinter -> unit -> init -> Pretty.doc 

(** Dump an initializer to a file using a given indentation. Use this instead of 
 * {!Cil.printInit} whenever possible. *)
val dumpInit: cilPrinter -> out_channel -> int -> init -> unit

(** Pretty-print a type using {!Cil.defaultCilPrinter} *)
val d_type: unit -> typ -> Pretty.doc

(** Pretty-print an expression using {!Cil.defaultCilPrinter}  *)
val d_exp: unit -> exp -> Pretty.doc

(** Pretty-print an lvalue using {!Cil.defaultCilPrinter}   *)
val d_lval: unit -> lval -> Pretty.doc

(** Pretty-print an offset using {!Cil.defaultCilPrinter}, given the pretty 
 * printing for the base.   *)
val d_offset: Pretty.doc -> unit -> offset -> Pretty.doc

(** Pretty-print an initializer using {!Cil.defaultCilPrinter}.  This can be 
 * extremely slow (or even overflow the stack) for huge initializers. Use 
 * {!Cil.dumpInit} instead. *)
val d_init: unit -> init -> Pretty.doc

(** Pretty-print a binary operator *)
val d_binop: unit -> binop -> Pretty.doc

(** Pretty-print a unary operator *)
val d_unop: unit -> unop -> Pretty.doc

(** Pretty-print an attribute using {!Cil.defaultCilPrinter}  *)
val d_attr: unit -> attribute -> Pretty.doc

(** Pretty-print an argument of an attribute using {!Cil.defaultCilPrinter}  *)
val d_attrparam: unit -> attrparam -> Pretty.doc

(** Pretty-print a list of attributes using {!Cil.defaultCilPrinter}  *)
val d_attrlist: unit -> attributes -> Pretty.doc 

(** Pretty-print an instruction using {!Cil.defaultCilPrinter}   *)
val d_instr: unit -> instr -> Pretty.doc

(** Pretty-print a label using {!Cil.defaultCilPrinter} *)
val d_label: unit -> label -> Pretty.doc

(** Pretty-print a statement using {!Cil.defaultCilPrinter}. This can be 
 * extremely slow (or even overflow the stack) for huge statements. Use 
 * {!Cil.dumpStmt} instead. *)
val d_stmt: unit -> stmt -> Pretty.doc

(** Pretty-print a block using {!Cil.defaultCilPrinter}. This can be 
 * extremely slow (or even overflow the stack) for huge blocks. Use 
 * {!Cil.dumpBlock} instead. *)
val d_block: unit -> block -> Pretty.doc

(** Pretty-print the internal representation of a global using 
 * {!Cil.defaultCilPrinter}. This can be extremely slow (or even overflow the 
 * stack) for huge globals (such as arrays with lots of initializers). Use 
 * {!Cil.dumpGlobal} instead. *)
val d_global: unit -> global -> Pretty.doc


(** Versions of the above pretty printers, that don't print #line directives *)
val dn_exp       : unit -> exp -> Pretty.doc
val dn_lval      : unit -> lval -> Pretty.doc
(* dn_offset is missing because it has a different interface *)
val dn_init      : unit -> init -> Pretty.doc
val dn_type      : unit -> typ -> Pretty.doc
val dn_global    : unit -> global -> Pretty.doc
val dn_attrlist  : unit -> attributes -> Pretty.doc
val dn_attr      : unit -> attribute -> Pretty.doc
val dn_attrparam : unit -> attrparam -> Pretty.doc
val dn_stmt      : unit -> stmt -> Pretty.doc
val dn_instr     : unit -> instr -> Pretty.doc


(** Pretty-print a short description of the global. This is useful for error 
 * messages *)
val d_shortglobal: unit -> global -> Pretty.doc

(** Pretty-print a global. Here you give the channel where the printout
 * should be sent. *)
val dumpGlobal: cilPrinter -> out_channel -> global -> unit

(** Pretty-print an entire file. Here you give the channel where the printout
 * should be sent. *)
val dumpFile: cilPrinter -> out_channel -> string -> file -> unit


(* the following error message producing functions also print a location in 
 * the code. use {!Errormsg.bug} and {!Errormsg.unimp} if you do not want 
 * that *)

(** Like {!Errormsg.bug} except that {!Cil.currentLoc} is also printed *)
val bug: ('a,unit,Pretty.doc) format -> 'a

(** Like {!Errormsg.unimp} except that {!Cil.currentLoc}is also printed *)
val unimp: ('a,unit,Pretty.doc) format -> 'a

(** Like {!Errormsg.error} except that {!Cil.currentLoc} is also printed *)
val error: ('a,unit,Pretty.doc) format -> 'a

(** Like {!Cil.error} except that it explicitly takes a location argument, 
 * instead of using the {!Cil.currentLoc} *)
val errorLoc: location -> ('a,unit,Pretty.doc) format -> 'a  

(** Like {!Errormsg.warn} except that {!Cil.currentLoc} is also printed *)
val warn: ('a,unit,Pretty.doc) format -> 'a


(** Like {!Errormsg.warnOpt} except that {!Cil.currentLoc} is also printed. 
 * This warning is printed only of {!Errormsg.warnFlag} is set. *)
val warnOpt: ('a,unit,Pretty.doc) format -> 'a

(** Like {!Errormsg.warn} except that {!Cil.currentLoc} and context 
    is also printed *)
val warnContext: ('a,unit,Pretty.doc) format -> 'a

(** Like {!Errormsg.warn} except that {!Cil.currentLoc} and context is also 
 * printed. This warning is printed only of {!Errormsg.warnFlag} is set. *)
val warnContextOpt: ('a,unit,Pretty.doc) format -> 'a

(** Like {!Cil.warn} except that it explicitly takes a location argument, 
 * instead of using the {!Cil.currentLoc} *)
val warnLoc: location -> ('a,unit,Pretty.doc) format -> 'a  

(** Sometimes you do not want to see the syntactic sugar that the above 
 * pretty-printing functions add. In that case you can use the following 
 * pretty-printing functions. But note that the output of these functions is 
 * not valid C *)

(** Pretty-print the internal representation of an expression *)
val d_plainexp: unit -> exp -> Pretty.doc

(** Pretty-print the internal representation of an integer *)
val d_plaininit: unit -> init -> Pretty.doc

(** Pretty-print the internal representation of an lvalue *)
val d_plainlval: unit -> lval -> Pretty.doc

(** Pretty-print the internal representation of an lvalue offset 
val d_plainoffset: unit -> offset -> Pretty.doc *)

(** Pretty-print the internal representation of a type *)
val d_plaintype: unit -> typ -> Pretty.doc



(** {b ALPHA conversion} has been moved to the Alpha module. *)


(** Assign unique names to local variables. This might be necessary after you 
 * transformed the code and added or renamed some new variables. Names are 
 * not used by CIL internally, but once you print the file out the compiler 
 * downstream might be confused. You might 
 * have added a new global that happens to have the same name as a local in 
 * some function. Rename the local to ensure that there would never be 
 * confusioin. Or, viceversa, you might have added a local with a name that 
 * conflicts with a global *)
val uniqueVarNames: file -> unit

(** {b Optimization Passes} *)

(** A peephole optimizer that processes two adjacent statements and possibly 
    replaces them both. If some replacement happens, then the new statements 
    are themselves subject to optimization *)
val peepHole2: (instr * instr -> instr list option) -> stmt list -> unit

(** Similar to [peepHole2] except that the optimization window consists of 
    one statement, not two *)
val peepHole1: (instr -> instr list option) -> stmt list -> unit

(** {b Machine dependency} *)

     
(** Raised when one of the bitsSizeOf functions cannot compute the size of a 
 * type. This can happen because the type contains array-length expressions 
 * that we don't know how to compute or because it is a type whose size is 
 * not defined (e.g. TFun or an undefined compinfo). The string is an 
 * explanation of the error *)        
exception SizeOfError of string * typ

(** The size of a type, in bits. Trailing padding is added for structs and 
 * arrays. Raises {!Cil.SizeOfError} when it cannot compute the size. This 
 * function is architecture dependent, so you should only call this after you 
 * call {!Cil.initCIL}. Remember that on GCC sizeof(void) is 1! *)
val bitsSizeOf: typ -> int

(* The size of a type, in bytes. Returns a constant expression or a "sizeof" 
 * expression if it cannot compute the size. This function is architecture 
 * dependent, so you should only call this after you call {!Cil.initCIL}.  *)
val sizeOf: typ -> exp

(** The minimum alignment (in bytes) for a type. This function is 
 * architecture dependent, so you should only call this after you call 
 * {!Cil.initCIL}. *)
val alignOf_int: typ -> int

(** Give a type of a base and an offset, returns the number of bits from the 
 * base address and the width (also expressed in bits) for the subobject 
 * denoted by the offset. Raises {!Cil.SizeOfError} when it cannot compute 
 * the size. This function is architecture dependent, so you should only call 
 * this after you call {!Cil.initCIL}. *)
val bitsOffset: typ -> offset -> int * int


(** Whether "char" is unsigned. Set after you call {!Cil.initCIL} *)
val char_is_unsigned: bool ref

(** Whether the machine is little endian. Set after you call {!Cil.initCIL} *)
val little_endian: bool ref

(** Whether the compiler generates assembly labels by prepending "_" to the 
    identifier. That is, will function foo() have the label "foo", or "_foo"?
    Set after you call {!Cil.initCIL} *)
val underscore_name: bool ref

(** Represents a location that cannot be determined *)
val locUnknown: location

(** Return the location of an instruction *)
val get_instrLoc: instr -> location 

(** Return the location of a global, or locUnknown *)
val get_globalLoc: global -> location 

(** Return the location of a statement, or locUnknown *)
val get_stmtLoc: stmtkind -> location 


(** Generate an {!Cil.exp} to be used in case of errors. *)
val dExp: Pretty.doc -> exp 

(** Generate an {!Cil.instr} to be used in case of errors. *)
val dInstr: Pretty.doc -> location -> instr

(** Generate a {!Cil.global} to be used in case of errors. *)
val dGlobal: Pretty.doc -> location -> global

(** Like map but try not to make a copy of the list *)
val mapNoCopy: ('a -> 'a) -> 'a list -> 'a list

(** Like map but each call can return a list. Try not to make a copy of the 
    list *)
val mapNoCopyList: ('a -> 'a list) -> 'a list -> 'a list

(** sm: return true if the first is a prefix of the second string *)
val startsWith: string -> string -> bool


(** {b An Interpreter for constructing CIL constructs} *)

(** The type of argument for the interpreter *)
type formatArg = 
    Fe of exp
  | Feo of exp option  (** For array lengths *)
  | Fu of unop
  | Fb of binop
  | Fk of ikind
  | FE of exp list (** For arguments in a function call *)
  | Ff of (string * typ * attributes) (** For a formal argument *)
  | FF of (string * typ * attributes) list (** For formal argument lists *)
  | Fva of bool (** For the ellipsis in a function type *)
  | Fv of varinfo
  | Fl of lval
  | Flo of lval option 

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


(** Pretty-prints a format arg *)
val d_formatarg: unit -> formatArg -> Pretty.doc

val lowerConstants: bool ref
 (** Do lower constant expressions into constants (default true) *)
