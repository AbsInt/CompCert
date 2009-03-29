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
(* cprint -- pretty printer of C program from abstract syntax
**
** Project:	FrontC
** File:	cprint.ml
** Version:	2.1e
** Date:	9.1.99
** Author:	Hugues Cassé
**
**	1.0		2.22.99	Hugues Cassé	First version.
**	2.0		3.18.99	Hugues Cassé	Compatible with Frontc 2.1, use of CAML
**									pretty printer.
**	2.1		3.22.99	Hugues Cassé	More efficient custom pretty printer used.
**	2.1a	4.12.99	Hugues Cassé	Correctly handle:
**									char *m, *m, *p; m + (n - p)
**	2.1b	4.15.99	Hugues Cassé	x + (y + z) stays x + (y + z) for
**									keeping computation order.
**	2.1c	7.23.99	Hugues Cassé	Improvement of case and default display.
**	2.1d	8.25.99	Hugues Cassé	Rebuild escape sequences in string and
**									characters.
**	2.1e	9.1.99	Hugues Cassé	Fix, recognize and correctly display '\0'.
*)

(* George Necula: I changed this pretty dramatically since CABS changed *)
open Cabs
open Escape
let version = "Cprint 2.1e 9.1.99 Hugues Cassé"

type loc = { line : int; file : string }

let lu = {line = -1; file = "loc unknown";}
let cabslu = {lineno = -10; 
	      filename = "cabs loc unknown"; 
	      byteno = -10;}

let curLoc = ref cabslu

let msvcMode = ref false

let printLn = ref true
let printLnComment = ref false

let printCounters = ref false
let printComments = ref false

(*
** FrontC Pretty printer
*)
let out = ref stdout
let width = ref 80
let tab = ref 2
let max_indent = ref 60

let line = ref ""
let line_len = ref 0
let current = ref ""
let current_len = ref 0
let spaces = ref 0
let follow = ref 0
let roll = ref 0

let print_tab size =
	for i = 1 to size / 8 do
		output_char !out '\t'
	done;
	for i  = 1 to size mod 8 do
		output_char !out ' '
	done

let flush _ =
	if !line <> "" then begin
		print_tab (!spaces + !follow);
		output_string !out !line;
		line := "";
		line_len := 0
	end

let commit _ =
  if !current <> "" then begin
    if !line = "" then begin
      line := !current;
      line_len := !current_len
    end else begin
      line := (!line ^ " " ^ !current);
      line_len := !line_len + 1 + !current_len
    end;
    current := "";
    current_len := 0
  end


let addline () =
  curLoc := {lineno = !curLoc.lineno+1;
             filename = !curLoc.filename;
             byteno = -1;} (*sfg: can we do better than this?*)
       
       
let new_line _ =
  commit ();
  if !line <> "" then begin
    flush ();
    addline();
    output_char !out '\n'
  end;
  follow := 0
       
let force_new_line _ =
  commit ();
  flush ();
  addline();
  output_char !out '\n';
  follow := 0
       
let indent _ =
  new_line ();
  spaces := !spaces + !tab;
  if !spaces >= !max_indent then begin
    spaces := !tab;
    roll := !roll + 1
  end
      
let indentline _ =
  new_line ();
  if !spaces >= !max_indent then begin
    spaces := !tab;
    roll := !roll + 1
  end
      
let unindent _ =
  new_line ();
  spaces := !spaces - !tab;
  if (!spaces <= 0) && (!roll > 0) then begin
    spaces := ((!max_indent - 1) / !tab) * !tab;
    roll := !roll - 1
  end
      
let space _ = commit ()

let print str =
  current := !current ^ str;
  current_len := !current_len + (String.length str);
  if (!spaces + !follow + !line_len + 1 + !current_len) > !width
  then begin
    if !line_len = 0 then commit ();
    flush ();
    addline();
    output_char !out '\n';
    if !follow = 0 then follow := !tab
  end

(* sm: for some reason I couldn't just call print from frontc.... ? *)
let print_unescaped_string str = print str

let setLoc (l : cabsloc) =
  if !printLn then  
    if (l.lineno <> !curLoc.lineno) || l.filename <> !curLoc.filename then 
      begin
        let oldspaces = !spaces in
        (* sm: below, we had '//#' instead of '#', which means printLnComment was disregarded *)
        if !printLnComment then print "//" else print "#";
        if !msvcMode then print "line";
        print " ";
        print (string_of_int l.lineno);
        if (l.filename <> !curLoc.filename) then begin
          print (" \"" ^ l.filename ^ "\"")
        end;
        spaces := oldspaces;
        new_line();
        curLoc := l
      end



(*
** Useful primitives
*)
let print_list print_sep print_elt lst = 
  let _ = List.fold_left
      (fun com elt ->
	if com then print_sep ();
	print_elt elt;
	true)
      false
      lst in
  ()

let print_commas nl fct lst =
  print_list (fun () -> print ","; if nl then new_line() else space()) fct lst
	
let print_string (s:string) =
  print ("\"" ^ escape_string s ^ "\"")

let print_wstring (s: int64 list ) =
  print ("L\"" ^ escape_wstring s ^ "\"")

(*
** Base Type Printing
*)

let rec print_specifiers (specs: spec_elem list) =
  comprint "specifier(";
  let print_spec_elem = function
      SpecTypedef -> print "typedef "
    | SpecInline -> print "__inline "
    | SpecStorage sto ->
        print (match sto with
          NO_STORAGE -> (comstring "/*no storage*/")
        | AUTO -> "auto "
        | STATIC -> "static "
        | EXTERN -> "extern "
        | REGISTER -> "register ")
    | SpecCV cv -> 
        print (match cv with
        | CV_CONST -> "const "
        | CV_VOLATILE -> "volatile "
        | CV_RESTRICT -> "restrict ")
    | SpecAttr al -> print_attribute al; space ()
    | SpecType bt -> print_type_spec bt
    | SpecPattern name -> print ("@specifier(" ^ name ^ ") ")
  in
  List.iter print_spec_elem specs
  ;comprint ")"


and print_type_spec = function
    Tvoid -> print "void "
  | Tchar -> print "char "
  | Tshort -> print "short "
  | Tint -> print "int "
  | Tlong -> print "long "
  | Tint64 -> print "__int64 "
  | Tfloat -> print "float "
  | Tdouble -> print "double "
  | Tsigned -> print "signed "
  | Tunsigned -> print "unsigned "
  | Tnamed s -> comprint "tnamed"; print s; space ();
  | Tstruct (n, None, _) -> print ("struct " ^ n ^ " ")
  | Tstruct (n, Some flds, extraAttrs) ->
      (print_struct_name_attr "struct" n extraAttrs);
      (print_fields flds)
  | Tunion (n, None, _) -> print ("union " ^ n ^ " ")
  | Tunion (n, Some flds, extraAttrs) ->
      (print_struct_name_attr "union" n extraAttrs);
      (print_fields flds)
  | Tenum (n, None, _) -> print ("enum " ^ n ^ " ")
  | Tenum (n, Some enum_items, extraAttrs) ->
      (print_struct_name_attr "enum" n extraAttrs);
      (print_enum_items enum_items)
  | TtypeofE e -> print "__typeof__("; print_expression e; print ") "
  | TtypeofT (s,d) -> print "__typeof__("; print_onlytype (s, d); print ") "


(* print "struct foo", but with specified keyword and a list of
 * attributes to put between keyword and name *)
and print_struct_name_attr (keyword: string) (name: string) (extraAttrs: attribute list) =
begin
  if extraAttrs = [] then
    print (keyword ^ " " ^ name)
  else begin
    (print (keyword ^ " "));
    (print_attributes extraAttrs);    (* prints a final space *)
    (print name);
  end
end


(* This is the main printer for declarations. It is easy bacause the 
 * declarations are laid out as they need to be printed. *)
and print_decl (n: string) = function
    JUSTBASE -> if n <> "___missing_field_name" then 
                  print n
                else
                  comprint "missing field name"
  | PARENTYPE (al1, d, al2) ->
      print "(";
      print_attributes al1; space ();
      print_decl n d; space ();
      print_attributes al2; print ")"
  | PTR (al, d) ->
      print "* ";
      print_attributes al; space ();
      print_decl n d
  | ARRAY (d, al, e) ->
      print_decl n d;
      print "[";
      print_attributes al;
      if e <> NOTHING then print_expression e;
      print "]"
  | PROTO(d, args, isva) ->
      comprint "proto(";
      print_decl n d;
      print "(";
      print_params args isva;
      print ")";
      comprint ")"


and print_fields (flds : field_group list) =
  if flds = [] then print " { } "
  else begin
    print " {";
    indent ();
    List.iter
      (fun fld -> print_field_group fld; print ";"; new_line ())
      flds;
    unindent ();
    print "} "
  end

and print_enum_items items =
  if items = [] then print " { } "
  else begin
    print " {";
    indent ();
    print_commas
      true
      (fun (id, exp, loc) -> print id;
	if exp = NOTHING then ()
	else begin
	  space ();
	  print "= ";
	  print_expression exp
	end)
      items;
    unindent ();
    print "} ";
  end

  
and print_onlytype (specs, dt) =
  print_specifiers specs;
  print_decl "" dt
    
and print_name ((n, decl, attrs, _) : name) =
  print_decl n decl;
  space ();
  print_attributes attrs

and print_init_name ((n, i) : init_name) =
  print_name n;
  if i <> NO_INIT then begin
    space ();
    print "= ";
    print_init_expression i
  end
            
and print_name_group (specs, names) =
  print_specifiers specs;
  print_commas false print_name names
    
and print_field_group (specs, fields) =
  print_specifiers specs;
  print_commas false print_field fields
    

and print_field (name, widtho) = 
  print_name name;
  (match widtho with 
    None -> ()
  | Some w -> print " : ";  print_expression w)

and print_init_name_group (specs, names) =
  print_specifiers specs;
  print_commas false print_init_name names
    
and print_single_name (specs, name) =
  print_specifiers specs;
  print_name name

and print_params (pars : single_name list) (ell : bool) =
  print_commas false print_single_name pars;
  if ell then print (if pars = [] then "..." else ", ...") else ()
    
and print_old_params pars ell =
  print_commas false (fun id -> print id) pars;
  if ell then print (if pars = [] then "..." else ", ...") else ()
    

(*
** Expression printing
**		Priorities
**		16	variables
**		15	. -> [] call()
**		14  ++, -- (post)
**		13	++ -- (pre) ~ ! - + & *(cast)
**		12	* / %
**		11	+ -
**		10	<< >>
**		9	< <= > >=
**		8	== !=
**		7	&
**		6	^
**		5	|
**		4	&&
**		3	||
**		2	? :
**		1	= ?=
**		0	,				
*)
and get_operator exp =
  match exp with
    NOTHING -> ("", 16)
  | UNARY (op, _) ->
      (match op with
	MINUS -> ("-", 13)
      | PLUS -> ("+", 13)
      | NOT -> ("!", 13)
      | BNOT -> ("~", 13)
      | MEMOF -> ("*", 13)
      | ADDROF -> ("&", 13)
      | PREINCR -> ("++", 13)
      | PREDECR -> ("--", 13)
      | POSINCR -> ("++", 14)
      | POSDECR -> ("--", 14))
  | LABELADDR s -> ("", 16)  (* Like a constant *)
  | BINARY (op, _, _) ->
      (match op with
	MUL -> ("*", 12)
      | DIV -> ("/", 12)
      | MOD -> ("%", 12)
      | ADD -> ("+", 11)
      | SUB -> ("-", 11)
      | SHL -> ("<<", 10)
      | SHR -> (">>", 10)
      | LT -> ("<", 9)
      | LE -> ("<=", 9)
      | GT -> (">", 9)
      | GE -> (">=", 9)
      | EQ -> ("==", 8)
      | NE -> ("!=", 8)
      | BAND -> ("&", 7)
      | XOR -> ("^", 6)
      | BOR -> ("|", 5)
      | AND -> ("&&", 4)
      | OR -> ("||", 3)
      | ASSIGN -> ("=", 1)
      | ADD_ASSIGN -> ("+=", 1)
      | SUB_ASSIGN -> ("-=", 1)
      | MUL_ASSIGN -> ("*=", 1)
      | DIV_ASSIGN -> ("/=", 1)
      | MOD_ASSIGN -> ("%=", 1)
      | BAND_ASSIGN -> ("&=", 1)
      | BOR_ASSIGN -> ("|=", 1)
      | XOR_ASSIGN -> ("^=", 1)
      | SHL_ASSIGN -> ("<<=", 1)
      | SHR_ASSIGN -> (">>=", 1))
  | QUESTION _ -> ("", 2)
  | CAST _ -> ("", 13)
  | CALL _ -> ("", 15)
  | COMMA _ -> ("", 0)
  | CONSTANT _ -> ("", 16)
  | VARIABLE name -> ("", 16)
  | EXPR_SIZEOF exp -> ("", 16)
  | TYPE_SIZEOF _ -> ("", 16)
  | EXPR_ALIGNOF exp -> ("", 16)
  | TYPE_ALIGNOF _ -> ("", 16)
  | INDEX (exp, idx) -> ("", 15)
  | MEMBEROF (exp, fld) -> ("", 15)
  | MEMBEROFPTR (exp, fld) -> ("", 15)
  | GNU_BODY _ -> ("", 17)
  | EXPR_PATTERN _ -> ("", 16)     (* sm: not sure about this *)

and print_comma_exps exps =
  print_commas false print_expression exps
    
and print_init_expression (iexp: init_expression) : unit = 
  match iexp with 
    NO_INIT -> ()
  | SINGLE_INIT e -> print_expression e
  | COMPOUND_INIT  initexps ->
      let doinitexp = function
          NEXT_INIT, e -> print_init_expression e
        | i, e -> 
            let rec doinit = function
                NEXT_INIT -> ()
              | INFIELD_INIT (fn, i) -> print ("." ^ fn); doinit i
              | ATINDEX_INIT (e, i) -> 
                  print "[";
                  print_expression e;
                  print "]";
                  doinit i
              | ATINDEXRANGE_INIT (s, e) -> 
                  print "["; 
                  print_expression s;
                  print " ... ";
                  print_expression e;
                  print "]"
                in
            doinit i; print " = "; 
            print_init_expression e
      in
      print "{";
      print_commas false doinitexp initexps;
      print "}"

and print_expression (exp: expression) = print_expression_level 1 exp

and print_expression_level (lvl: int) (exp : expression) =
  let (txt, lvl') = get_operator exp in
  let _ = if lvl > lvl' then print "(" else () in
  let _ = match exp with
    NOTHING -> ()
  | UNARY (op, exp') ->
      (match op with
	POSINCR | POSDECR ->
	  print_expression_level lvl' exp';
	  print txt
      | _ ->
	  print txt; space (); (* Print the space to avoid --5 *)
	  print_expression_level lvl' exp')
  | LABELADDR l -> print ("&& " ^ l)
  | BINARY (op, exp1, exp2) ->
			(*if (op = SUB) && (lvl <= lvl') then print "(";*)
      print_expression_level lvl' exp1;
      space ();
      print txt;
      space ();
			(*print_expression exp2 (if op = SUB then (lvl' + 1) else lvl');*)
      print_expression_level (lvl' + 1) exp2 
			(*if (op = SUB) && (lvl <= lvl') then print ")"*)
  | QUESTION (exp1, exp2, exp3) ->
      print_expression_level 2 exp1;
      space ();
      print "? ";
      print_expression_level 2 exp2;
      space ();
      print ": ";
      print_expression_level 2 exp3;
  | CAST (typ, iexp) ->
      print "(";
      print_onlytype typ;
      print ")"; 
     (* Always print parentheses. In a small number of cases when we print 
      * constants we don't need them  *)
      (match iexp with
        SINGLE_INIT e -> print_expression_level 15 e
      | COMPOUND_INIT _ -> (* print "("; *) 
          print_init_expression iexp 
          (* ; print ")" *)
      | NO_INIT -> print "<NO_INIT in cast. Should never arise>")

  | CALL (VARIABLE "__builtin_va_arg", [arg; TYPE_SIZEOF (bt, dt)]) -> 
      comprint "variable";
      print "__builtin_va_arg";
      print "(";
      print_expression_level 1 arg;
      print ",";
      print_onlytype (bt, dt);
      print ")"
  | CALL (exp, args) ->
      print_expression_level 16 exp;
      print "(";
      print_comma_exps args;
      print ")"
  | COMMA exps ->
      print_comma_exps exps
  | CONSTANT cst ->
      (match cst with
	CONST_INT i -> print i
      | CONST_FLOAT r -> print r
      | CONST_CHAR c -> print ("'" ^ escape_wstring c ^ "'")
      | CONST_WCHAR c -> print ("L'" ^ escape_wstring c ^ "'")
      | CONST_STRING s -> print_string s
      | CONST_WSTRING ws -> print_wstring ws)
  | VARIABLE name ->
      comprint "variable";
      print name
  | EXPR_SIZEOF exp ->
      print "sizeof(";
      print_expression_level 0 exp;
      print ")"
  | TYPE_SIZEOF (bt,dt) ->
      print "sizeof(";
      print_onlytype (bt, dt);
      print ")"
  | EXPR_ALIGNOF exp ->
      print "__alignof__(";
      print_expression_level 0 exp;
      print ")"
  | TYPE_ALIGNOF (bt,dt) ->
      print "__alignof__(";
      print_onlytype (bt, dt);
      print ")"
  | INDEX (exp, idx) ->
      print_expression_level 16 exp;
      print "[";
      print_expression_level 0 idx;
      print "]"
  | MEMBEROF (exp, fld) ->
      print_expression_level 16 exp;
      print ("." ^ fld)
  | MEMBEROFPTR (exp, fld) ->
      print_expression_level 16 exp;
      print ("->" ^ fld)
  | GNU_BODY (blk) ->
      print "(";
      print_block blk;
      print ")"
  | EXPR_PATTERN (name) ->
      print ("@expr(" ^ name ^ ") ")
  in
  if lvl > lvl' then print ")" else ()
    

(*
** Statement printing
*)
and print_statement stat =
  match stat with
    NOP (loc) ->
      setLoc(loc);
      print ";";
      new_line ()
  | COMPUTATION (exp, loc) ->
      setLoc(loc);
      print_expression exp;
      print ";";
      new_line ()
  | BLOCK (blk, loc) -> print_block blk

  | SEQUENCE (s1, s2, loc) ->
      setLoc(loc);
      print_statement s1;
      print_statement s2;
  | IF (exp, s1, s2, loc) ->
      setLoc(loc);
      print "if(";
      print_expression_level 0 exp;
      print ")";
      print_substatement s1;
      (match s2 with
      | NOP(_) -> ()
      | _ -> begin
          print "else";
          print_substatement s2;
        end)
  | WHILE (exp, stat, loc) ->
      setLoc(loc);
      print "while(";
      print_expression_level 0 exp;
      print ")";
      print_substatement stat
  | DOWHILE (exp, stat, loc) ->
      setLoc(loc);
      print "do";
      print_substatement stat;
      print "while(";
      print_expression_level 0 exp;
      print ");";
      new_line ();
  | FOR (fc1, exp2, exp3, stat, loc) ->
      setLoc(loc);
      print "for(";
      (match fc1 with
        FC_EXP exp1 -> print_expression_level 0 exp1; print ";"
      | FC_DECL dec1 -> print_def dec1);
      space ();
      print_expression_level 0 exp2;
      print ";";
      space ();
      print_expression_level 0 exp3;
      print ")";
      print_substatement stat
  | BREAK (loc)->
      setLoc(loc);
      print "break;"; new_line ()
  | CONTINUE (loc) ->
      setLoc(loc);
      print "continue;"; new_line ()
  | RETURN (exp, loc) ->
      setLoc(loc);
      print "return";
      if exp = NOTHING
      then ()
      else begin
	print " ";
	print_expression_level 1 exp
      end;
      print ";";
      new_line ()
  | SWITCH (exp, stat, loc) ->
      setLoc(loc);
      print "switch(";
      print_expression_level 0 exp;
      print ")";
      print_substatement stat
  | CASE (exp, stat, loc) ->
      setLoc(loc);
      unindent ();
      print "case ";
      print_expression_level 1 exp;
      print ":";
      indent ();
      print_substatement stat
  | CASERANGE (expl, exph, stat, loc) ->
      setLoc(loc);
      unindent ();
      print "case ";
      print_expression expl;
      print " ... ";
      print_expression exph;
      print ":";
      indent ();
      print_substatement stat
  | DEFAULT (stat, loc) ->
      setLoc(loc);
      unindent ();
      print "default :";
      indent ();
      print_substatement stat
  | LABEL (name, stat, loc) ->
      setLoc(loc);
      print (name ^ ":");
      space ();
      print_substatement stat
  | GOTO (name, loc) ->
      setLoc(loc);
      print ("goto " ^ name ^ ";");
      new_line ()
  | COMPGOTO (exp, loc) -> 
      setLoc(loc);
      print ("goto *"); print_expression exp; print ";"; new_line ()
  | DEFINITION d ->
      print_def d
  | ASM (attrs, tlist, details, loc) ->
      setLoc(loc);
      let print_asm_operand (cnstr, e) =
        print_string cnstr; space (); print_expression_level 100 e
      in
      if !msvcMode then begin
        print "__asm {";
        print_list (fun () -> new_line()) print tlist; (* templates *)
        print "};"
      end else begin
        print "__asm__ "; 
        print_attributes attrs;
        print "(";
        print_list (fun () -> new_line()) print_string tlist; (* templates *)
	begin
	  match details with
	  | None -> ()
	  | Some { aoutputs = outs; ainputs = ins; aclobbers = clobs } ->
              print ":"; space ();
              print_commas false print_asm_operand outs;
              if ins <> [] || clobs <> [] then begin
		print ":"; space ();
		print_commas false print_asm_operand ins;
		if clobs <> [] then begin
		  print ":"; space ();
		  print_commas false print_string clobs
		end;
              end
	end;
        print ");"
      end;
      new_line ()
  | TRY_FINALLY (b, h, loc) -> 
      setLoc loc;
      print "__try ";
      print_block b;
      print "__finally ";
      print_block h

  | TRY_EXCEPT (b, e, h, loc) -> 
      setLoc loc;
      print "__try ";
      print_block b;
      print "__except("; print_expression e; print ")";
      print_block h
      
and print_block blk = 
  new_line();
  print "{";
  indent ();
  if blk.blabels <> [] then begin
    print "__label__ ";
    print_commas false print blk.blabels;
    print ";";
    new_line ();
  end;
  if blk.battrs <> [] then begin
    List.iter print_attribute blk.battrs;
    new_line ();
  end;
  List.iter print_statement blk.bstmts;
  unindent ();
  print "}";
  new_line ()
  
and print_substatement stat =
  match stat with
    IF _
  | SEQUENCE _
  | DOWHILE _ ->
      new_line ();
      print "{";
      indent ();
      print_statement stat;
      unindent ();
      print "}";
      new_line ();
  | BLOCK _ ->
      print_statement stat
  | _ ->
      indent ();
      print_statement stat;
      unindent ()


(*
** GCC Attributes
*)
and print_attribute (name,args) = 
  if args = [] then print (
    match name with 
      "restrict" -> "__restrict" 
      (* weimer: Fri Dec  7 17:12:35  2001
       * must not print 'restrict' and the code below does allows some
       * plain 'restrict's to slip though! *)
    | x -> x)
  else begin
    print name;
    print "("; if name = "__attribute__" then print "(";
    (match args with
      [VARIABLE "aconst"] -> print "const"
    | [VARIABLE "restrict"] -> print "__restrict"
    | _ -> print_commas false (fun e -> print_expression e) args);
    print ")"; if name = "__attribute__" then print ")"
  end

(* Print attributes. *)
and print_attributes attrs =
  List.iter (fun a -> print_attribute a; space ()) attrs

(*
** Declaration printing
*)
and print_defs defs =
  let prev = ref false in
  List.iter
    (fun def ->
      (match def with
	DECDEF _ -> prev := false
      | _ ->
	  if not !prev then force_new_line ();
	  prev := true);
      print_def def)
    defs

and print_def def =
  match def with
    FUNDEF (proto, body, loc, _) ->
      comprint "fundef";
      if !printCounters then begin
        try
          let fname =
            match proto with
              (_, (n, _, _, _)) -> n
          in
          print_def (DECDEF (([SpecType Tint],
                              [(fname ^ "__counter", JUSTBASE, [], cabslu),
                                NO_INIT]), loc));
        with Not_found -> print "/* can't print the counter */"
      end;
      setLoc(loc);
      print_single_name proto;
      print_block body;
      force_new_line ();

  | DECDEF (names, loc) ->
      comprint "decdef";
      setLoc(loc);
      print_init_name_group names;
      print ";";
      new_line ()

  | TYPEDEF (names, loc) ->
      comprint "typedef";
      setLoc(loc);
      print_name_group names;
      print ";";
      new_line ();
      force_new_line ()

  | ONLYTYPEDEF (specs, loc) ->
      comprint "onlytypedef";
      setLoc(loc);
      print_specifiers specs;
      print ";";
      new_line ();
      force_new_line ()

  | GLOBASM (asm, loc) ->
      setLoc(loc);
      print "__asm__ (";  print_string asm; print ");";
      new_line ();
      force_new_line ()

  | PRAGMA (a,loc) ->
      setLoc(loc);
      force_new_line ();
      print "#pragma ";
      let oldwidth = !width in
      width := 1000000;  (* Do not wrap pragmas *)
      print_expression a;
      width := oldwidth;
      force_new_line ()

  | LINKAGE (n, loc, dl) -> 
      setLoc (loc);
      force_new_line ();
      print "extern "; print_string n; print_string "  {";
      List.iter print_def dl;
      print_string "}";
      force_new_line ()

  | TRANSFORMER(srcdef, destdeflist, loc) ->
      setLoc(loc);
      print "@transform {";
      force_new_line();
      print "{";
        force_new_line();
        indent ();
        print_def srcdef;
        unindent();
      print "}";
      force_new_line();
      print "to {";
        force_new_line();
        indent();
        List.iter print_def destdeflist;
        unindent();
      print "}";
      force_new_line()

  | EXPRTRANSFORMER(srcexpr, destexpr, loc) ->
      setLoc(loc);
      print "@transformExpr { ";
      print_expression srcexpr;
      print " } to { ";
      print_expression destexpr;
      print " }";
      force_new_line()


(* sm: print a comment if the printComments flag is set *)
and comprint (str : string) : unit =
begin
  if (!printComments) then (
    print "/*";
    print str;
    print "*/ "
  )
  else
    ()
end

(* sm: yield either the given string, or "", depending on printComments *)
and comstring (str : string) : string =
begin
  if (!printComments) then
    str
  else
    ""
end


(*  print abstrac_syntax -> ()
**		Pretty printing the given abstract syntax program.
*)
let printFile (result : out_channel) ((fname, defs) : file) =
  out := result;
  print_defs defs;
  flush ()     (* sm: should do this here *)

let set_tab t = tab := t
let set_width w = width := w

