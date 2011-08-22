(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Pulling side-effects out of expressions *)

(* Assumes: nothing
   Produces: simplified code *)

open C
open Cutil
open Transform

(* Grammar of simplified expressions:
      e ::= EConst cst
          | ESizeof ty
          | EVar id
          | EUnop pure-unop e
          | EBinop pure-binop e e
          | EConditional e e e
          | ECast ty e

   Grammar of statements produced to reflect side-effects in expressions:
      s ::= Sskip
          | Sdo (EBinop Oassign e e)
          | Sdo (EBinop Oassign e (ECall e e* ))
          | Sdo (Ecall e el)
          | Sseq s s
          | Sif e s s
*)

let rec is_simpl_expr e =
  match e.edesc with
  | EConst cst -> true
  | ESizeof ty -> true
  | EVar id -> true
  | EUnop((Ominus|Oplus|Olognot|Onot|Oderef|Oaddrof), e1) ->
      is_simpl_expr e1
  | EBinop((Oadd|Osub|Omul|Odiv|Omod|Oand|Oor|Oxor|Oshl|Oshr|
            Oeq|One|Olt|Ogt|Ole|Oge|Oindex|Ologand|Ologor), e1, e2, _) ->
      is_simpl_expr e1 && is_simpl_expr e2
  | EConditional(e1, e2, e3) ->
      is_simpl_expr e1 && is_simpl_expr e2 && is_simpl_expr e3
  | ECast(ty, e1) ->
      is_simpl_expr e1
  | _ ->
      false

(* "Destination" of a simplified expression *)

type exp_destination =
  | RHS                  (* evaluate as a r-value *)
  | LHS                  (* evaluate as a l-value *)
  | Drop                 (* drop its value, we only need the side-effects *)
  | Set of exp           (* assign it to the given simplified l.h.s. *)

let voidconst = { nullconst with etyp = TVoid [] }

(* Reads from volatile lvalues are also considered as side-effects if
   [volatilize] is true. *)

let volatilize = ref false

(* [simpl_expr loc env e act] returns a pair [s, e'] of
   a statement that performs the side-effects present in [e] and
   a simplified, side-effect-free expression [e'].
   If [act] is [RHS], [e'] evaluates to the same value as [e].
   If [act] is [LHS], [e'] evaluates to the same location as [e].
   If [act] is [Drop], [e'] is not meaningful and must be ignored.
   If [act] is [Set lhs], [s] also performs an assignment
   equivalent to [lhs = e].  [e'] is not meaningful. *)

let simpl_expr loc env e act =

  (* Temporaries should not be [const] because we assign into them,
     and need not be [volatile] because no one else is writing into them.
     As for [restrict] it doesn't make sense anyway. *)

  let new_temp ty =
    Transform.new_temp (erase_attributes_type env ty) in

  let eboolvalof e =
    { edesc = EBinop(One, e, intconst 0L IInt, TInt(IInt, []));
      etyp = TInt(IInt, []) } in

  let sseq s1 s2 = Cutil.sseq loc s1 s2 in

  let sassign e1 e2 =
    { sdesc = Sdo {edesc = EBinop(Oassign, e1, e2, e1.etyp); etyp = e1.etyp}; 
      sloc = loc } in

  let sif e s1 s2 =
    { sdesc = Sif(e, s1, s2); sloc = loc } in

  let is_volatile_read e =
    !volatilize
    && List.mem AVolatile (attributes_of_type env e.etyp)
    && is_lvalue e in

  let lhs_to_rhs e =
    if is_volatile_read e
    then (let t = new_temp e.etyp in (sassign t e, t))
    else (sskip, e) in

  let finish act s e =
    match act with
    | RHS ->
        if is_volatile_read e
        then (let t = new_temp e.etyp in (sseq s (sassign t e), t))
        else (s, e)
    | LHS ->
        (s, e)
    | Drop -> 
        if is_volatile_read e
        then (let t = new_temp e.etyp in (sseq s (sassign t e), voidconst))
        else (s, voidconst)
    | Set lhs ->
        if is_volatile_read e
        then (let t = new_temp e.etyp in
                 (sseq s (sseq (sassign t e) (sassign lhs t)), voidconst))
        else (sseq s (sassign lhs e), voidconst) in

   let rec simpl e act =
    match e.edesc with

    | EConst cst -> 
        finish act sskip e

    | ESizeof ty -> 
        finish act sskip e

    | EVar id ->
        finish act sskip e

    | EUnop(op, e1) ->

        begin match op with

        | Ominus | Oplus | Olognot | Onot | Oderef | Oarrow _ ->
            let (s1, e1') = simpl e1 RHS in
            finish act s1 {edesc = EUnop(op, e1'); etyp = e.etyp}

        | Oaddrof ->
            let (s1, e1') = simpl e1 LHS in
            finish act s1 {edesc = EUnop(op, e1'); etyp = e.etyp}

        | Odot _ ->
            let (s1, e1') = simpl e1 (if act = LHS then LHS else RHS) in
            finish act s1 {edesc = EUnop(op, e1'); etyp = e.etyp}

        | Opreincr | Opredecr ->
            let (s1, e1') = simpl e1 LHS in
            let (s2, e2') = lhs_to_rhs e1' in
            let op' = match op with Opreincr -> Oadd | _ -> Osub in
            let ty = unary_conversion env e.etyp in
            let e3 =
              {edesc = EBinop(op', e2', intconst 1L IInt, ty); etyp = ty} in
            begin match act with
            | Drop ->
                (sseq s1 (sseq s2 (sassign e1' e3)), voidconst)
            | _ ->
                let tmp = new_temp e.etyp in
                finish act (sseq s1 (sseq s2 (sseq (sassign tmp e3)
                                                   (sassign e1' tmp))))
                       tmp
            end

        | Opostincr | Opostdecr ->
            let (s1, e1') = simpl e1 LHS in
            let op' = match op with Opostincr -> Oadd | _ -> Osub in
            let ty = unary_conversion env e.etyp in
            begin match act with
            | Drop ->
                let (s2, e2') = lhs_to_rhs e1' in
                let e3 =
                  {edesc = EBinop(op', e2', intconst 1L IInt, ty); etyp = ty} in
                (sseq s1 (sseq s2 (sassign e1' e3)), voidconst)
            | _ ->
                let tmp = new_temp e.etyp in
                let e3 =
                  {edesc = EBinop(op', tmp, intconst 1L IInt, ty); etyp = ty} in
                finish act (sseq s1 (sseq (sassign tmp e1') (sassign e1' e3))) 
                       tmp
            end

        end

    | EBinop(op, e1, e2, ty) ->

        begin match op with

        | Oadd | Osub | Omul | Odiv | Omod | Oand | Oor | Oxor
        | Oshl | Oshr | Oeq | One | Olt | Ogt | Ole | Oge | Oindex ->
            let (s1, e1') = simpl e1 RHS in
            let (s2, e2') = simpl e2 RHS in
            finish act (sseq s1 s2)
                       {edesc = EBinop(op, e1', e2', ty); etyp = e.etyp}

        | Oassign ->
            if act = Drop && is_simpl_expr e1 then
              simpl e2 (Set e1)
            else begin
              match act with
              | Drop ->
                  let (s1, e1') = simpl e1 LHS in
                  let (s2, e2') = simpl e2 RHS in
                  (sseq s1 (sseq s2 (sassign e1' e2')), voidconst)
              | _ ->
                  let tmp = new_temp e.etyp in
                  let (s1, e1') = simpl e1 LHS in
                  let (s2, e2') = simpl e2 (Set tmp) in
                  finish act (sseq s1 (sseq s2 (sassign e1' tmp)))
                             tmp
            end

        | Oadd_assign | Osub_assign | Omul_assign | Odiv_assign
        | Omod_assign | Oand_assign | Oor_assign  | Oxor_assign
        | Oshl_assign | Oshr_assign ->
            let (s1, e1') = simpl e1 LHS in
            let (s11, e11') = lhs_to_rhs e1' in
            let (s2, e2') = simpl e2 RHS in
            let op' =
              match op with
              | Oadd_assign -> Oadd    | Osub_assign -> Osub
              | Omul_assign -> Omul    | Odiv_assign -> Odiv
              | Omod_assign -> Omod    | Oand_assign -> Oand
              | Oor_assign  -> Oor     | Oxor_assign -> Oxor
              | Oshl_assign -> Oshl    | Oshr_assign -> Oshr
              | _ -> assert false in
            let e3 =
              { edesc = EBinop(op', e11', e2', ty); etyp = ty } in
            begin match act with
            | Drop ->
                (sseq s1 (sseq s11 (sseq s2 (sassign e1' e3))), voidconst)
            | _ ->
                let tmp = new_temp e.etyp in
                finish act (sseq s1 (sseq s11 (sseq s2
                               (sseq (sassign tmp e3) (sassign e1' tmp)))))
                           tmp
            end

        | Ocomma ->
            let (s1, _) = simpl e1 Drop in
            let (s2, e2') = simpl e2 act in
            (sseq s1 s2, e2')

        | Ologand ->
            let (s1, e1') = simpl e1 RHS in
            if is_simpl_expr e2 then begin
              finish act s1
                     {edesc = EBinop(Ologand, e1', e2, ty); etyp = e.etyp}
            end else begin
              match act with
              | Drop ->
                  let (s2, _) = simpl e2 Drop in
                  (sseq s1 (sif e1' s2 sskip), voidconst)
              | RHS | LHS ->  (* LHS should not happen *)
                  let (s2, e2') = simpl e2 RHS in
                  let tmp = new_temp e.etyp in
                  (sseq s1 (sif e1' 
                              (sseq s2 (sassign tmp (eboolvalof e2')))
                              (sassign tmp (intconst 0L IInt))),
                   tmp)
              | Set lv ->
                  let (s2, e2') = simpl e2 RHS in
                  (sseq s1 (sif e1' 
                              (sseq s2 (sassign lv (eboolvalof e2')))
                              (sassign lv (intconst 0L IInt))),
                   voidconst)
            end             

        | Ologor ->
            let (s1, e1') = simpl e1 RHS in
            if is_simpl_expr e2 then begin
              finish act s1
                     {edesc = EBinop(Ologor, e1', e2, ty); etyp = e.etyp}
            end else begin
              match act with
              | Drop ->
                  let (s2, _) = simpl e2 Drop in
                  (sseq s1 (sif e1' sskip s2), voidconst)
              | RHS | LHS ->  (* LHS should not happen *)
                  let (s2, e2') = simpl e2 RHS in
                  let tmp = new_temp e.etyp in
                  (sseq s1 (sif e1' 
                              (sassign tmp (intconst 1L IInt))
                              (sseq s2 (sassign tmp (eboolvalof e2')))),
                   tmp)
              | Set lv ->
                  let (s2, e2') = simpl e2 RHS in
                  (sseq s1 (sif e1' 
                              (sassign lv (intconst 1L IInt))
                              (sseq s2 (sassign lv (eboolvalof e2')))),
                   voidconst)
            end             

        end

    | EConditional(e1, e2, e3) ->
        let (s1, e1') = simpl e1 RHS in
        if is_simpl_expr e2 && is_simpl_expr e3 then begin
          finish act s1 {edesc = EConditional(e1', e2, e3); etyp = e.etyp}
        end else begin
          match act with
          | Drop ->
              let (s2, _) = simpl e2 Drop in
              let (s3, _) = simpl e3 Drop in
              (sseq s1 (sif e1' s2 s3), voidconst)
          | RHS | LHS ->  (* LHS should not happen *)
              let tmp = new_temp e.etyp in
              let (s2, _) = simpl e2 (Set tmp) in
              let (s3, _) = simpl e3 (Set tmp) in
              (sseq s1 (sif e1' s2 s3), tmp)
          | Set lv ->
              let (s2, _) = simpl e2 (Set lv) in
              let (s3, _) = simpl e3 (Set lv) in
              (sseq s1 (sif e1' s2 s3), voidconst)
        end

    | ECast(ty, e1) ->
        if is_void_type env ty then begin
          if act <> Drop then
            Errors.warning "%acast to 'void' in a context expecting a value\n"
                           formatloc loc;
            simpl e1 act
        end else begin
          let (s1, e1') = simpl e1 RHS in
          finish act s1 {edesc = ECast(ty, e1'); etyp = e.etyp}
        end

    | ECall(e1, el) ->
        let (s1, e1') = simpl e1 RHS in
        let (s2, el') = simpl_list el in
        let e2 = { edesc = ECall(e1', el'); etyp = e.etyp } in
        begin match act with
        | Drop ->
            (sseq s1 (sseq s2 {sdesc = Sdo e2; sloc=loc}), voidconst)
        | Set({edesc = EVar _} as lhs) ->
            (* CompCert wants the destination of a call to be a variable,
               not a more complex lhs.  In the latter case, we
               fall through the catch-all case below *)
            (sseq s1 (sseq s2 (sassign lhs e2)), voidconst)
        | _ ->
            let tmp = new_temp e.etyp in
            finish act (sseq s1 (sseq s2 (sassign tmp e2))) tmp
        end

  and simpl_list = function
    | [] -> (sskip, [])
    | e1 :: el ->
        let (s1, e1') = simpl e1 RHS in
        let (s2, el') = simpl_list el in
        (sseq s1 s2, e1' :: el')

  in simpl e act

(* Simplification of an initializer *)

let simpl_initializer loc env i =

  let rec simpl_init = function
  | Init_single e ->
      let (s, e') = simpl_expr loc env e RHS in
      (s, Init_single e)
  | Init_array il ->
      let rec simpl = function
      | [] -> (sskip, [])
      | i1 :: il ->
          let (s1, i1') = simpl_init i1 in
          let (s2, il') = simpl il in
          (sseq loc s1 s2, i1' :: il') in
      let (s, il') = simpl il in
      (s, Init_array il')
  | Init_struct(id, il) ->
      let rec simpl = function
      | [] -> (sskip, [])
      | (f1, i1) :: il ->
          let (s1, i1') = simpl_init i1 in
          let (s2, il') = simpl il in
          (sseq loc s1 s2, (f1, i1') :: il') in
      let (s, il') = simpl il in
      (s, Init_struct(id, il'))
  | Init_union(id, f, i) ->
      let (s, i') = simpl_init i in
      (s, Init_union(id, f, i'))

  in simpl_init i

(* Construct a simplified statement equivalent to [if (e) s1; else s2;].
   Optimizes the case where e contains [&&] or [||] or [?].
   [s1] or [s2] can be duplicated, so use only for small [s1] and [s2]
   that do not define any labels. *)

let rec simpl_if loc env e s1 s2 =
  match e.edesc with
  | EUnop(Olognot, e1) ->
      simpl_if loc env e1 s2 s1
  | EBinop(Ologand, e1, e2, _) ->
      simpl_if loc env e1
        (simpl_if loc env e2 s1 s2)
        s2
  | EBinop(Ologor, e1, e2, _) ->
      simpl_if loc env e1
        s1
        (simpl_if loc env e2 s1 s2)
  | EConditional(e1, e2, e3) ->
      simpl_if loc env e1
        (simpl_if loc env e2 s1 s2)
        (simpl_if loc env e3 s1 s2)
  | _ ->
      let (s, e') = simpl_expr loc env e RHS in
      sseq loc s {sdesc = Sif(e', s1, s2); sloc = loc}

(* Trivial statements for which [simpl_if] is applicable *)

let trivial_stmt s =
  match s.sdesc with
  | Sskip | Scontinue | Sbreak | Sgoto _ -> true
  | _ -> false

(* Construct a simplified statement equivalent to [if (!e) exit; ]. *)

let break_if_false loc env e =
  simpl_if loc env e
           {sdesc = Sskip; sloc = loc}
           {sdesc = Sbreak; sloc = loc}

(* Simplification of a statement *)

let simpl_statement env s =

  let rec simpl_stmt s =
    match s.sdesc with

  | Sskip ->
      s

  | Sdo e ->
      let (s', _) = simpl_expr s.sloc env e Drop in
      s'

  | Sseq(s1, s2) ->
      {sdesc = Sseq(simpl_stmt s1, simpl_stmt s2); sloc = s.sloc}

  | Sif(e, s1, s2) ->
      if trivial_stmt s1 && trivial_stmt s2 then
        simpl_if s.sloc env e (simpl_stmt s1) (simpl_stmt s2)
      else begin
        let (s', e') = simpl_expr s.sloc env e RHS in
        sseq s.sloc s'
          {sdesc = Sif(e', simpl_stmt s1, simpl_stmt s2);
           sloc = s.sloc}
      end

  | Swhile(e, s1) ->
      if is_simpl_expr e then
        {sdesc = Swhile(e, simpl_stmt s1); sloc = s.sloc}
      else
        {sdesc =
           Swhile(intconst 1L IInt,
                  sseq s.sloc (break_if_false s.sloc env e)
                              (simpl_stmt s1));
         sloc = s.sloc}

  | Sdowhile(s1, e) ->
      if is_simpl_expr e then
        {sdesc = Sdowhile(simpl_stmt s1, e); sloc = s.sloc}
      else begin
        let tmp = new_temp (TInt(IInt, [])) in
        let (s', _) = simpl_expr s.sloc env e (Set tmp) in
        let s_init =
          {sdesc = Sdo {edesc = EBinop(Oassign, tmp, intconst 1L IInt, tmp.etyp);
                        etyp = tmp.etyp};
           sloc = s.sloc} in
        {sdesc = Sfor(s_init, tmp, s', simpl_stmt s1); sloc = s.sloc}
      end
(*** Alternate translation that unfortunately puts a "break" in the
     "next" part of a "for", something that is not supported
     by Clight semantics, and has unknown behavior in gcc.
        {sdesc =
           Sfor(sskip, 
                intconst 1L IInt,
                break_if_false s.sloc env e,
                simpl_stmt s1);
         sloc = s.sloc}
***)

  | Sfor(s1, e, s2, s3) ->
      if is_simpl_expr e then
        {sdesc = Sfor(simpl_stmt s1,
                      e,
                      simpl_stmt s2,
                      simpl_stmt s3);
         sloc = s.sloc}
      else
        let (s', e') = simpl_expr s.sloc env e RHS in
        {sdesc = Sfor(sseq s.sloc (simpl_stmt s1) s',
                      e',
                      sseq s.sloc (simpl_stmt s2) s',
                      simpl_stmt s3);
         sloc = s.sloc}

  | Sbreak ->
      s
  | Scontinue ->
      s

  | Sswitch(e, s1) ->
      let (s', e') = simpl_expr s.sloc env e RHS in
      sseq s.sloc s' {sdesc = Sswitch(e', simpl_stmt s1); sloc = s.sloc}

  | Slabeled(lbl, s1) ->
      {sdesc = Slabeled(lbl, simpl_stmt s1); sloc = s.sloc}

  | Sgoto lbl ->
      s

  | Sreturn None ->
      s

  | Sreturn (Some e) ->
      let (s', e') = simpl_expr s.sloc env e RHS in
      sseq s.sloc s' {sdesc = Sreturn(Some e'); sloc = s.sloc}

  | Sblock sl ->
      {sdesc = Sblock(simpl_block sl); sloc = s.sloc}

  | Sdecl d -> assert false

  and simpl_block = function
  | [] -> []
  | ({sdesc = Sdecl(sto, id, ty, None)} as s) :: sl ->
      s :: simpl_block sl
  | ({sdesc = Sdecl(sto, id, ty, Some i)} as s) :: sl ->
      let (s', i') = simpl_initializer s.sloc env i in
      let sl' =
           {sdesc = Sdecl(sto, id, ty, Some i'); sloc = s.sloc}
        :: simpl_block sl in
      if s'.sdesc = Sskip then sl' else s' :: sl'
  | s :: sl ->
      simpl_stmt s :: simpl_block sl

  in simpl_stmt s

(* Simplification of a function definition *)

let simpl_fundef env f =
  reset_temps();
  let body' = simpl_statement env f.fd_body in
  let temps = get_temps() in
  { f with fd_locals = f.fd_locals @ temps; fd_body = body' }

(* Entry point *)

let program ?(volatile = false) p =
  volatilize := volatile;
  Transform.program ~fundef:simpl_fundef p
