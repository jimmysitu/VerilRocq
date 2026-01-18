Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Lib.Lib. Import HMapNotations. Import SZNotations.
Require Import Lang.Analysis Lang.Syntax.

Set Implicit Arguments.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope hmap_scope.

(*! State monad with failures *)

Inductive sf (sty fty: Type) :=
| Sret: sty -> sf sty fty
| Fail: fty -> sf sty fty.
Arguments Sret [_] {_}.
Arguments Fail {_} [_].

Definition liftToSF {sty fty} (os: option sty) (f: fty): sf sty fty :=
  match os with
  | Some s => Sret s
  | None => Fail f
  end.

Declare Scope sf_monad_scope.

Module SFMonadNotations.

  Notation "S <- SF ; CONT" :=
    (match SF with
     | Sret s => (fun S => CONT) s
     | Fail f => Fail f
     end) (at level 84, right associativity): sf_monad_scope.

  Notation "S <- SF <~ AS ; CONT" :=
    (match SF with
     | Sret s => (fun S => CONT) s
     | Fail f => (fun S => CONT) AS
     end) (at level 84, right associativity): sf_monad_scope.

  Notation "S <- SF ~> RET ; CONT" :=
    (match SF with
     | Sret s => (fun S => CONT) s
     | Fail _ => Sret RET
     end) (at level 84, right associativity): sf_monad_scope.

  Notation "OS |> F" :=
    (liftToSF OS F) (at level 83, left associativity): sf_monad_scope.

  Open Scope sf_monad_scope.
End SFMonadNotations.

Include SFMonadNotations.

Section ListMap.
  Context {A S F: Type}.
  Variable (f: A -> sf S F).
  Fixpoint sf_list_map (al: list A): sf (list S) F :=
    match al with
    | nil => Sret nil
    | cons a al' => (o <- f a;
                     ol' <- sf_list_map al';
                     Sret (cons o ol'))
    end.
End ListMap.

Section ListMap2.
  Context {A B S F: Type}.
  Variable (f: A -> B -> sf S F).
  Fixpoint sf_list_map2 (al: list A) (bl: list B) {struct bl}: sf (list S) F :=
    match al with
    | nil => Sret nil
    | cons a al' => match bl with
                    | nil => Sret nil
                    | cons b bl' => (o <- f a b;
                                     ol' <- sf_list_map2 al' bl';
                                     Sret (cons o ol'))
                    end
    end.
End ListMap2.

Section Iterate.
  Context {T A F: Type}.
  Variable fitr: T -> A -> sf A F.

  Fixpoint iterate (ts: list T) (a: A): sf A F :=
    match ts with
    | nil => Sret a
    | cons t ts' => (ta <- fitr t a; iterate ts' ta)
    end.

  Fixpoint iterate_resume (ts: list T) (a: A): sf A F :=
    match ts with
    | nil => Sret a
    | cons t ts' => (ta <- fitr t a <~ a;
                     iterate_resume ts' ta)
    end.

End Iterate.

Section IterateUpd.
  Context {T A B F: Type}.
  Variables (fitr: T -> A -> sf B F)
            (fba: B -> A) (nilb: B)
            (upda: A -> A -> A) (updb: B -> B -> B).

  Fixpoint iterate_update (ts: list T) (a: A): sf B F :=
    match ts with
    | nil => Sret nilb
    | cons t ts' => (tab <- fitr t a;
                     tsab <- iterate_update ts' (upda a (fba tab));
                     Sret (updb tab tsab))
    end.

End IterateUpd.

(*! -- end of State monad with failures *)

Section Semantics.
  Context `{sz_ops}.
  Context `{vid_ops}.
  Context `{array_ops hmap}.

  Definition hfind2 (p: hpath) (h1 h2: hmap): option hmap :=
    match hfind p h1 with
    | Some v => Some v
    | None => hfind p h2
    end.

  Definition Value := hmap.
  Definition State := Value.
  Definition Flops := State.
  Definition Decls := State. (* NOTE: values are all invalid. *)

  Record MTrs :=
    { mtrs_input_vids: list vid_t; (* input declarations *)
      mtrs_output_vids: list vid_t; (* output declarations *)
      mtrs_func: State (* inputs *) -> State (* current flop state *) ->
                 (State * State) (* flop updates for next cycle * outputs *) }.

  Record Func :=
    { func_input_vids: list vid_t; (* input declarations *)
      func_func: State (* inputs *) -> Value (* return value *) }.

  (*! Transition-function definitions *)



  Definition buildFInputState (vids: list vid_t) (args: list Value): State :=
    HMapStr (List.combine vids args).

  Definition evalPriLiteral (p: VPriLiteral): Value :=
    match p with
    | VPriLiteralNumber n =>
        match n with
        | VNumberIntegral intn =>
            match intn with
            | VIntegralBinary osz num =>
                match osz with
                | Some sz => HMapBits #{(binaryZtoZ (Z.to_nat sz) num), sz, false}
                | _ => HMapBits #{(binaryZtoZ sz_int32_nat num), sz_int32, false}
                end
            | VIntegralOctal osz num =>
                match osz with
                | Some sz => HMapBits #{(octalZtoZ (Z.to_nat sz) num), sz, false}
                | _ => HMapBits #{(octalZtoZ sz_int32_nat num), sz_int32, false}
                end
            | VIntegralHex osz num =>
                HMapBits #{num, (match osz with
                                 | Some sz => sz
                                 | _ => sz_int32
                                 end), false}
            | VIntegralDecimal (VDecimalNumberNB num) =>
                (** IEEE Standard 11.8.1 .. Decimal numbers are signed .. *)
                HMapBits #{num, sz_int32, true}
            | VIntegralDecimal (VDecimalNumberB osz num) =>
                (** IEEE Standard 11.8.1 .. Based numbers are unsigned .. *)
                HMapBits #{num, (match osz with
                                 | Some sz => sz
                                 | _ => sz_int32
                                 end), false}
            end
        end
    | VPriLiteralUU VZeros => HMapBits szF0
    | VPriLiteralUU VOnes => HMapBits szF1
    end.

  Definition uniOpFunc (op: VUniOp): SZ -> SZ :=
    match op with
    | VUniPlus => id | VUniMinus => sz_u_minus | VUniNot => sz_u_not
    | VUniNeg => sz_u_neg | VUniAnd => sz_u_and | VUniNand => sz_u_nand
    | VUniOr => sz_u_or | VUniNor => sz_u_nor | VUniXor => sz_u_xor | VUniXnor => sz_u_xnor
    end.

  Definition binOpFunc (op: VBinOp): SZ -> SZ -> SZ :=
    match op with
    | VBinAdd => sz_b_add | VBinSub => sz_b_sub
    | VBinMul => sz_b_mul | VBinDiv => sz_b_div | VBinRem => sz_b_rem
    | VBinEq => sz_b_eq | VBinNEq => sz_b_neq
    | VBinFEq => sz_b_feq | VBinFNEq => sz_b_fneq
    | VBinWEq => sz_b_weq | VBinWNEq => sz_b_wneq
    | VBinLAnd => sz_b_land | VBinLOr => sz_b_lor
    | VBinPow => sz_b_pow
    | VBinLt => sz_b_lt | VBinLe => sz_b_le
    | VBinGt => sz_b_gt | VBinGe => sz_b_ge
    | VBinBAnd => sz_b_and | VBinBOr => sz_b_or
    | VBinBXor => sz_b_xor | VBinBXnor => sz_b_xnor
    | VBinShr => sz_b_shr | VBinShl => sz_b_shl
    | VBinSar => sz_b_sar | VBinSal => sz_b_sal
    end.

  (** Now with failures *)
  Inductive TrsFail :=
  | TrsFatal (* should not happen; need to debug *)
  | TrsUndeclared
  | TrsUndriven
  | TrsNotSupported
  | TrsNotUnfoldable.
  Definition trsOk (sty: Type) := sf sty TrsFail.


  Inductive chain {T: Type} (bot: T) (F: T -> trsOk T) : T -> Prop :=
  | chain_bottom: chain bot F bot
  | chain_step (h: T) (h': T): chain bot F h -> F h = Sret h' -> chain bot F h'.

  Definition LFP {T: Type} (bot: T) F h := (chain bot F h) /\ (F h = Sret h).


  Definition sfind (vid: vid_t) (h: hmap): trsOk hmap :=
    match hfind [HEltVid vid] h with
    | Some v => Sret v
    | None => Fail TrsUndriven
    end.

  Definition TrsFMap (A: Type) := vid_t -> trsOk A.
  Definition fmapEmpty {A}: TrsFMap A := fun _ => Fail TrsUndeclared.
  Local Notation "'[>]'" := fmapEmpty.
  Definition fmapSingle {A} (k: vid_t) (v: A): TrsFMap A :=
    fun vid => if (vid_eq_dec vid k) then Sret v else Fail TrsUndeclared.
  Definition fmapMerge {A} (m1 m2: TrsFMap A): TrsFMap A :=
    fun vid => match m1 vid with
               | Sret v => Sret v
               | Fail _ => m2 vid
               end.

  Definition MTrss := TrsFMap MTrs.
  Definition Funcs := TrsFMap Func.

  (*! Semantics using pre-collected declarations and functions *)

  Section WithDeclsFuncs.
    Variable decls: Decls.
    Variable funcs: Funcs.
    Variable ctxs: State.

    Definition ctxfind (p: hpath): trsOk hmap :=
      hfind p ctxs |> TrsUndriven.

    Section OnCurPos.
      Variable cpos: hpath. (** The current position in terms of modules/regions *)

      Definition declfind (vid: vid_t): trsOk hpath :=
        hpos cpos vid decls |> TrsUndeclared.

      (** [IFW] contains values for inputs, flops, and "wires (including output ones) evaluated so far".
       * It also contains parameter and local values as well.
       * When a variable is declared, it holds the value '0 with a proper type as a type information. *)
      Definition IFW := State.
      Variable ifw: IFW.

      (** New wire values. It will be either updated to [ifw] or reverted
       * based on the success of each module-item level evaluation. *)
      Definition NW := State.

      Section WithUpdates.
        Variable nw: NW.

        Definition wfind (vid: vid_t): trsOk hmap :=
          (pos <- declfind vid;
           hfind2 pos nw ifw |> TrsUndriven).

        Definition getAccessVid (e: @VExpr vid_t): trsOk vid_t :=
          match e with
          | VExprId vid => Sret vid
          | _ => Fail TrsFatal
          end.

        Definition sfbits (v: Value): trsOk SZ := Sret (hbits v).

        Fixpoint evalExpr (e: @VExpr vid_t) {struct e}: trsOk Value :=
          match e with
          | VExprPriLiteral pl => Sret (evalPriLiteral pl)
          | VExprId vid => wfind vid
          | VExprHier pe ce => (pv <- evalExpr pe;
                                cvid <- getAccessVid ce;
                                Sret (haccess pv cvid))
          | VExprPriSelect se ie => (sv <- evalExpr se;
                                     iv <- evalExpr ie;
                                     Sret (hselect sv (hbits iv)))
          | VExprPriSelectConstRange se le re => (sv <- evalExpr se;
                                                  lv <- evalExpr le; li <- sfbits lv;
                                                  rv <- evalExpr re; ri <- sfbits rv;
                                                  Sret (hrange sv li ri))
          | VExprPriConcat es => (vs <- sf_list_map evalExpr es;
                                  Sret (harray vs))
          | VExprPriMultConcat ne ces => (nv <- evalExpr ne; nb <- sfbits nv;
                                          vs <- sf_list_map evalExpr ces;
                                          Sret (harray (List.concat (List.repeat vs (Z.to_nat (zof nb))))))
          | VExprTfCall tfid aes => (func <- funcs tfid;
                                     avs <- sf_list_map (evalExpr) aes;
                                     Sret (func.(func_func) (buildFInputState func.(func_input_vids) avs)))
          | VExprSystemTfCall tf aes =>
              (match tf with
               | VSystemTfSigned => (match aes with
                                     | nil => Fail TrsFatal
                                     | cons ae taes => (av <- evalExpr ae; ab <- sfbits av;
                                                        Sret (HMapBits (sz_signed ab)))
                                     end)
               | VSystemTfUnsigned => (match aes with
                                       | nil => Fail TrsFatal
                                       | cons ae taes => (av <- evalExpr ae; ab <- sfbits av;
                                                          Sret (HMapBits (sz_unsigned ab)))
                                       end)
               end)
          | VExprCast sze e => (szv <- evalExpr sze; sz <- sfbits szv;
                                v <- evalExpr e; b <- sfbits v;
                                Sret (HMapBits (sz_cast_v sz b)))
          | VExprUniOp op e => (v <- evalExpr e; z <- sfbits v;
                                Sret (HMapBits (uniOpFunc op z)))
          | VExprBinOp op le re => (lv <- evalExpr le; lz <- sfbits lv;
                                    rv <- evalExpr re; rz <- sfbits rv;
                                    Sret (HMapBits (binOpFunc op lz rz)))
          | VExprCond ce te fe => (cv <- evalExpr ce;
                                   cvz <- sfbits cv;
                                   ftrs <- evalExpr fe;
                                   ttrs <- evalExpr te;
                                   Sret (if (sz_is_zero cvz) then ftrs else ttrs))
          | VExprInside ie res => (iv <- evalExpr ie; iz <- sfbits iv;
                                   rvs <- sf_list_map (evalExpr) res;
                                   rzs <- sf_list_map sfbits rvs;
                                   Sret (HMapBits #{(if (List.find (fun rz => sz_equiv iz rz) rzs)
                                                     then 1 else 0), 1, false}))
          | _ => Fail TrsNotSupported
          end.

        Fixpoint lvposfind (lv: @VExpr vid_t): trsOk hpath :=
          (* TODO: lvposfind does not support range selects or concatenation lvalues yet
             (e.g. VExprPriSelectConstRange / VExprPriSelectIdxRangeAdd/Sub / VExprPriConcat). *)
          match lv with
          | VExprId vid => (pty <- declfind vid; Sret pty)
          | VExprHier pe ce => (ppty <- lvposfind pe;
                                cvid <- getAccessVid ce;
                                Sret (cons (HEltVid cvid) ppty))
          | VExprPriSelect se ie => (spty <- lvposfind se;
                                     iv <- evalExpr ie; i <- sfbits iv;
                                     Sret (cons (HEltInd i) spty))
          | _ => Fail TrsFatal
          end.

        Definition ctxEval (p: hpath) (e: @VExpr vid_t): trsOk Value :=
          (v <- evalExpr e;
           (* Apply the ctx value only when "assignable," i.e. when [e] is evaluable *)
           cv <- ctxfind p <~ v;
           Sret cv).

        Definition trsVAssignVPos (v: Value) (pty: hpath): trsOk State :=
          Sret (hsingle pty v).

        Definition trsVAssignV (lv: @VExpr vid_t) (v: Value) (pty: hpath): trsOk State :=
          match lv with
          | VExprId vid => trsVAssignVPos v pty
          | VExprHier pe ce => trsVAssignVPos v pty
          | VExprPriSelect se ie => trsVAssignVPos v pty
          | _ => Fail TrsNotSupported
          end.

        Definition trsVAssign (a: @VAssign vid_t): trsOk State :=
          match a with
          | VAssignO lv e => (pty <- lvposfind lv;
                              cv <- ctxEval pty e;
                              trsVAssignV lv cv pty)
          end.

      End WithUpdates.

      Fixpoint trsVAssigns (assigns: @VAssigns vid_t) (nw: NW): trsOk NW :=
        match assigns with
        | VAssignsOne a => trsVAssign nw a
        | VAssignsCons a assigns' =>
            (aa <- trsVAssign nw a;
             naa <- trsVAssigns assigns' (hupds nw aa);
             Sret (hupds aa naa))
        end.

      Definition trsVContAssign (cass: @VContAssign vid_t) (nw: NW): trsOk NW :=
        match cass with
        | VContAssignNet assigns => trsVAssigns assigns nw
        end.

      Definition nfupds (ifl1 ifl2: NW * Flops): NW * Flops :=
        (hupds (fst ifl1) (fst ifl2), hupds (snd ifl1) (snd ifl2)).

      Definition pnfupds (pred: bool) (ifl1 ifl2: NW * Flops): NW * Flops :=
        (phupds pred (fst ifl1) (fst ifl2), phupds pred (snd ifl1) (snd ifl2)).

      Section StatementCase.
        Variable trsf: bool -> @VStatementItem vid_t -> NW -> trsOk (NW * Flops * Value).

        Fixpoint trsVStatementCaseV (isComb: bool)
          (cz: SZ) (css: list (@VCaseItem vid_t VStatementItem)) (nw: NW): trsOk (NW * Flops) :=
          match css with
          | nil => Sret ([], [])
          | cons cs css' => match cs with
                            | VCaseItemCase _ ies st =>
                                (* Assuming each case item value is bits *)
                                (iv <- evalExpr nw ies; iz <- sfbits iv;
                                 ttrs <- trsf isComb st nw;
                                 ftrs <- trsVStatementCaseV isComb cz css' nw;
                                 Sret (pnfupds (sz_equiv cz iz) (fst ttrs) ftrs))
                            | VCaseItemDefault _ st =>
                                (dtrs <- trsf isComb st nw; Sret (fst dtrs))
                            end
          end.
      End StatementCase.

      Definition trsVStatementForInit := trsVAssigns.
      Definition trsVStatementForStep (fstep: VForStep) (nw: NW): trsOk NW :=
        match fstep with
        | VForStepIncOrDec (VIncExpr vid) =>
            Sret (hupdf (cons (HEltVid vid) cpos)
                    (fun v => match v with
                              | HMapBits z => HMapBits (sz_b_add z #{1, 1, true})
                              | _ => v
                              end)
                    nw)
        | VForStepIncOrDec (VDecExpr vid) =>
            Sret (hupdf (cons (HEltVid vid) cpos)
                    (fun v => match v with
                              | HMapBits z => HMapBits (sz_b_sub z #{1, 1, true})
                              | _ => v
                              end)
                    nw)
        | _ => Fail TrsNotSupported
        end.

      Section StatementForLoop.
        Variable trsf: bool -> @VStatementItem vid_t -> NW -> trsOk (NW * Flops * Value).

        Fixpoint trsVStatementForLoopN (magic: nat)
          (isComb: bool) (ce: @VExpr vid_t) (fstep: @VForStep vid_t)
          (st: @VStatementItem vid_t) (nw: NW): trsOk (NW * Flops) :=
          match magic with
          | O => Fail TrsNotUnfoldable
          | S n => (cv <- evalExpr nw ce; cz <- sfbits cv;
                    if (Z.eq_dec (zof cz) 0) then Sret ([], [])
                    else (ifl <- trsf isComb st nw;
                          nnw <- trsVStatementForStep fstep (hupds nw (fst (fst ifl)));
                          nifl <- trsVStatementForLoopN n isComb ce fstep st nnw;
                          Sret (nfupds (fst ifl) nifl)))
          end.

        Definition maxLoop: nat := Nat.pow 2 5.
        Definition trsVStatementForLoop := trsVStatementForLoopN maxLoop.

      End StatementForLoop.

      (** NOTE: return values are the new updates to wires and flops. *)
      Fixpoint trsVStatementItem (isComb: bool) (sti: @VStatementItem vid_t) (nw: NW): trsOk (NW * Flops * Value) :=
        match sti with
        | VStatementItemBlockingAssignNormal lv e => (pty <- lvposfind nw lv;
                                                      cv <- ctxEval nw pty e;
                                                      atrs <- trsVAssignV lv cv pty;
                                                      Sret (if isComb then (atrs, [], []) else ([], atrs, [])))
        | VStatementItemNonblockingAssign lv e => (pty <- lvposfind nw lv;
                                                   cv <- ctxEval nw pty e;
                                                   atrs <- trsVAssignV lv cv pty;
                                                   Sret (if isComb then (atrs, [], []) else ([], atrs, [])))
        | VStatementCase cty ce css => (cv <- evalExpr nw ce; cz <- sfbits cv;
                                        nwf <- trsVStatementCaseV trsVStatementItem isComb cz css nw;
                                        Sret (nwf, []))
        | VStatementCond ce tsti ofsti => (cv <- evalExpr nw ce; cz <- sfbits cv;
                                           ftrs <- (match ofsti with
                                                    | Some (Some fsti) => trsVStatementItem isComb fsti nw
                                                    | _ => Sret ([], [], [])
                                                    end);
                                           ttrs <- (match tsti with
                                                    | Some tsti => trsVStatementItem isComb tsti nw
                                                    | _ => Sret ([], [], [])
                                                    end);
                                           Sret (pnfupds (sz_is_zero cz) (fst ftrs) (fst ttrs), []))
        | VStatementItemReturn re => (rv <- evalExpr nw re; Sret ([], [], rv))
        | VStatementProcTimingControl tc psti => trsVStatementItem isComb psti nw
        | VStatementSeqBlock stis => iterate_update (trsVStatementItem isComb) (fun s => fst (fst s)) ([], [], [])
                                       hupds (fun nfr1 nfr2 => (nfupds (fst nfr1) (fst nfr2), snd nfr2))
                                       stis nw
        | _ => Fail TrsNotSupported
        end.

      Definition trsVNetDeclAssign (pd: @VPackedDims vid_t) (nda: @VNetDeclAssign vid_t): trsOk NW :=
        match nda with
        | VNetDeclAssignOne vid oe => match oe with
                                      | Some e => (cv <- ctxEval [] (cons (HEltVid vid) cpos) e;
                                                   nnw <- trsVAssignV (VExprId vid) cv (cons (HEltVid vid) cpos);
                                                   Sret nnw)
                                      | None => Sret []
                                      end
        end.

      Fixpoint trsVNetDeclAssigns (pd: @VPackedDims vid_t) (ndas: @VNetDeclAssigns vid_t): trsOk NW :=
        match ndas with
        | VNetDeclAssignsOne nda => trsVNetDeclAssign pd nda
        | VNetDeclAssignsCons nda ndas' => (nw <- trsVNetDeclAssign pd nda;
                                            nws <- trsVNetDeclAssigns pd ndas';
                                            Sret (hupds nw nws))
        end.

      Definition trsVVarDeclAssign (dt: @VDataType vid_t) (nda: @VVarDeclAssign vid_t): trsOk NW :=
        match nda with
        | VVarDeclAssignVar vid vd oe =>
            match oe with
            | Some e => (cv <- ctxEval [] (cons (HEltVid vid) cpos) e;
                         nnw <- trsVAssignV (VExprId vid) cv (cons (HEltVid vid) cpos);
                         Sret nnw)
            | None => Sret []
            end
        end.

      Fixpoint trsVVarDeclAssigns (dt: @VDataType vid_t) (ndas: @VVarDeclAssigns vid_t): trsOk NW :=
        match ndas with
        | VVarDeclAssignsOne nda => trsVVarDeclAssign dt nda
        | VVarDeclAssignsCons nda ndas' => (nw <- trsVVarDeclAssign dt nda;
                                            nws <- trsVVarDeclAssigns dt ndas';
                                            Sret (hupds nw nws))
        end.

      Definition trsVParamAssign (dti: @VDataTypeOrImplicit vid_t) (nda: @VParamAssign vid_t): trsOk NW :=
        match nda with
        | VParamAssignOne vid (VConstParamExprMinTypMax e) =>
            (cv <- ctxEval [] (cons (HEltVid vid) cpos) e;
             nnw <- trsVAssignV (VExprId vid) cv (cons (HEltVid vid) cpos);
             Sret nnw)
        end.

      Fixpoint trsVParamAssigns (dti: @VDataTypeOrImplicit vid_t) (ndas: @VParamAssigns vid_t): trsOk NW :=
        match ndas with
        | VParamAssignsOne nda => trsVParamAssign dti nda
        | VParamAssignsCons nda ndas' => (nw <- trsVParamAssign dti nda;
                                          nws <- trsVParamAssigns dti ndas';
                                          Sret (hupds nw nws))
        end.

      Definition trsVPkgGenItemDecl (pgid: @VPkgGenItemDecl vid_t): trsOk NW :=
        match pgid with
        | VPkgGenItemDeclNet (VNetDeclOne nt pd ndas) => trsVNetDeclAssigns pd ndas
        | VPkgGenItemDeclData (VDataDeclVarDecl (VVarDeclOne dt vdas)) => trsVVarDeclAssigns dt vdas
        | VPkgGenItemDeclTask td => Sret []
        | VPkgGenItemDeclFunc fd => Sret []
        | VPkgGenItemDeclParam (VParamDeclData dti pas) => trsVParamAssigns dti pas
        | VPkgGenItemDeclLocalParam (VLocalParamDeclOne dti pas) => trsVParamAssigns dti pas
        end.

      Definition trsVModuleCommonItem (mci: @VModuleCommonItem vid_t): trsOk (NW * Flops) :=
        match mci with
        | VModuleCommonItemDecl (VModuleGenItemDeclPkg pgid) => (nnw <- trsVPkgGenItemDecl pgid;
                                                                 Sret (nnw, []))
        | VModuleCommonItemAssert cca => Sret ([], []) (* Not any part of the trs func *)
        | VModuleCommonItemContAssign cass => (nnw <- trsVContAssign cass [];
                                               Sret (nnw, []))
        | VModuleCommonItemAlways akwd (VStatementO sti) =>
            (nwf <- trsVStatementItem (match akwd with
                                       | VAlwaysComb => true
                                       | _ => false
                                       end) sti [];
             Sret (fst (fst nwf), snd (fst nwf)))
        | _ => Fail TrsNotSupported
        end.

      Definition trsVModuleInsMTrsInput (ivids: list vid_t) (npc: @VNamedPortConn vid_t)
        (inputs: State): trsOk State :=
        match npc with
        | VNamedPortConnI vid => (vty <- List.find (vid_eqb vid) ivids |> TrsUndeclared ~> inputs;
                                  iv <- wfind [] vid ~> inputs;
                                  Sret (hadd [HEltVid vid] iv inputs))
        | VNamedPortConnE vid ie => (vty <- List.find (vid_eqb vid) ivids |> TrsUndeclared ~> inputs;
                                     iv <- evalExpr [] ie ~> inputs;
                                     Sret (hadd [HEltVid vid] iv inputs))
        (* Will be handled separately, after handling all explicit input-port connections *)
        | VNamedPortConnW => Sret inputs
        end.

      Fixpoint trsVModuleInsMTrsInputs (ivids: list vid_t) (npcs: @VNamedPortConns vid_t)
        (inputs: State): trsOk State :=
        match npcs with
        | VNamedPortConnsOne npc => trsVModuleInsMTrsInput ivids npc inputs
        | VNamedPortConnsCons npc npcs' => (ninputs <- trsVModuleInsMTrsInput ivids npc inputs;
                                            trsVModuleInsMTrsInputs ivids npcs' ninputs)
        end.

      Definition trsVModuleInsMTrsOutput (ovids: list vid_t) (npc: @VNamedPortConn vid_t)
        (outputs: State): trsOk NW :=
        match npc with
        | VNamedPortConnI vid => (vty <- List.find (vid_eqb vid) ovids |> TrsUndeclared ~> [];
                                  pty <- lvposfind [] (VExprId vid);
                                  v <- (match ctxfind pty with
                                        | Sret cv => Sret cv
                                        | Fail _ => haccessO outputs vid |> TrsUndriven
                                        end) ~> [];
                                  atrs <- trsVAssignV (VExprId vid) v pty;
                                  Sret atrs)
        | VNamedPortConnE vid (VExprId ovid) => (vty <- List.find (vid_eqb vid) ovids |> TrsUndeclared ~> [];
                                                 pty <- lvposfind [] (VExprId ovid);
                                                 v <- (match ctxfind pty with
                                                       | Sret cv => Sret cv
                                                       | Fail _ => haccessO outputs vid |> TrsUndriven
                                                       end) ~> [];
                                                 atrs <- trsVAssignV (VExprId ovid) v pty;
                                                 Sret atrs)
        | VNamedPortConnE vid oe => (vty <- List.find (vid_eqb vid) ovids |> TrsUndeclared ~> [];
                                     (*pty <- lvposfind [] (VExprId vid);*)
                                     pty <- lvposfind [] oe;
                                     ov <- haccessO outputs vid |> TrsUndriven ~> [];
                                     atrs <- trsVAssignV oe ov pty;
                                     Sret atrs)
        (* Will be handled separately, after handling all explicit output-port connections *)
        | VNamedPortConnW => Sret []
        end.

      Fixpoint trsVModuleInsMTrsOutputs (ovids: list vid_t) (npcs: @VNamedPortConns vid_t)
        (outputs: State): trsOk NW :=
        match npcs with
        | VNamedPortConnsOne npc => trsVModuleInsMTrsOutput ovids npc outputs
        | VNamedPortConnsCons npc npcs' => (nnw <- trsVModuleInsMTrsOutput ovids npc outputs;
                                            nnws <- trsVModuleInsMTrsOutputs ovids npcs' outputs;
                                            Sret (hupds nnw nnws))
        end.

      (** cf. IEEE Standard 23.3.2.4:
       * .. When the implicit .* port connection is mixed in the same instantiation with named port
       * connections, the implicit .* port connection token can be placed anywhere in the port list.
       * The .* token can only appear at most once in the port list. *)
      Definition trsVModuleInsMTrs (mtrs: MTrs)
        (iid: vid_t) (npcs: @VNamedPortConns vid_t): trsOk (NW * Flops) :=
        (inputs <- trsVModuleInsMTrsInputs mtrs.(mtrs_input_vids) npcs [];
         mflops <- hfind (cpos ++ [HEltVid iid]) ifw |> TrsUndeclared;
         let mflo := mtrs.(mtrs_func) inputs mflops in
         outputs <- trsVModuleInsMTrsOutputs mtrs.(mtrs_output_vids) npcs (snd mflo);
         Sret (outputs, hsingle (cons (HEltVid iid) cpos) (fst mflo))).

      Definition trsVModuleIns (mtrss: MTrss)
        (mins: @VModuleIns vid_t): trsOk (NW * Flops) :=
        match mins with
        | VModuleInsOne mid params (VHierInsOne iid (VPortConnsNamed npcs)) =>
            (mtrs <- mtrss mid; trsVModuleInsMTrs mtrs iid npcs)
        end.

      Definition trsVModuleOrGenerateItem (mtrss: MTrss)
        (mgi: @VModuleOrGenerateItem vid_t): trsOk (NW * Flops) :=
        match mgi with
        | VModuleOrGenerateItemIns mins => trsVModuleIns mtrss mins
        | VModuleOrGenerateItemCommon mci => trsVModuleCommonItem mci
        end.

    End OnCurPos.

    Variable mtrss: MTrss.

    Definition IFF := (IFW * Flops)%type.
    Notation "'iff_ifw_' iff" := (fst iff) (at level 0).
    Notation "'iff_flops_' iff" := (snd iff) (at level 0).

    Definition iffupds (iff1 iff2: IFF): IFF :=
      (** NOTE: We use [hupds] instead of [hmergeR] because [hupds] performs a
       * recursive update, whereas [hmergeR] is flat. In a hierarchical design,
       * [hupds] allows updating specific signals within a submodule without
       * overwriting the entire submodule state.
       *)
      (*
      (hmergeR (iff_ifw_ iff1) (iff_ifw_ iff2),
        hmergeR (iff_flops_ iff1) (iff_flops_ iff2)).
      *)
      (hupds (iff_ifw_ iff1) (iff_ifw_ iff2),
        hupds (iff_flops_ iff1) (iff_flops_ iff2)).

    Fixpoint trsVGenerateModuleItem (gmi: @VGenerateModuleItem vid_t) (cpos: hpath)
      (iff: IFF): trsOk IFF :=
      match gmi with
      | VGenerateModuleItemCond ce tgmi ofgmi =>
          (cv <- evalExpr cpos (iff_ifw_ iff) [] ce; cz <- sfbits cv;
           ftrs <- (match ofgmi with
                    | Some fgmi => trsVGenerateModuleItem fgmi cpos iff
                    | _ => Sret iff
                    end);
           ttrs <- trsVGenerateModuleItem tgmi cpos iff;
           Sret (if (sz_is_zero cz) then ftrs else ttrs))
      | VGenerateModuleItemBlock gmis =>
          (** NOTE: it's very important to use [iterate_resume] (instead of [iterate]).
           * We indeed would like to resume iteration if we fail to convert a particular module item to
           * its transition function, especially when the failure is due to yet-undriven signals.
           *)
          iterate_resume (fun gmi => trsVGenerateModuleItem gmi cpos) gmis iff
      | VGenerateModuleItemModule mgi =>
          (niff <- trsVModuleOrGenerateItem cpos (iff_ifw_ iff) mtrss mgi ~> iff;
           Sret (iffupds iff niff))
      end.

    Definition trsVNonPortModuleItem (pnp: @VNonPortModuleItem vid_t)
      (iff: IFF): trsOk IFF :=
      match pnp with
      | VNonPortGeneratedModuleIns (VGeneratedModuleInsO gmi) => trsVGenerateModuleItem gmi nil iff
      | VNonPortModuleOrGenerateItem mgi =>
          (niff <- trsVModuleOrGenerateItem nil (iff_ifw_ iff) mtrss mgi ~> iff;
           Sret (iffupds iff niff))
      end.

    Definition trsVModuleItem (mitem: @VModuleItem vid_t)
      (iff: IFF): trsOk IFF :=
      match mitem with
      | VModuleItemPortDecl pdec => Sret iff
      | VModuleItemNonPort pnp => trsVNonPortModuleItem pnp iff
      end.

    Fixpoint trsVModuleItems (mitems: @VModuleItems vid_t)
      (iff: IFF): trsOk IFF :=
      match mitems with
      | VModuleItemsOne mitem => trsVModuleItem mitem iff
      | VModuleItemsCons mitem mitems' =>
          (niff <- trsVModuleItem mitem iff <~ iff;
           trsVModuleItems mitems' niff)
      end.

    Definition trsVParamDecl (pdecl: @VParamDecl vid_t) (ifw: IFW): trsOk IFW :=
      match pdecl with
      | VParamDeclData dti pas => (nidl <- trsVParamAssigns nil ifw dti pas;
                                   Sret (hmergeL ifw nidl))
      end.

    Fixpoint trsVParamPorts (pports: @VParamPorts vid_t) (ifw: IFW): trsOk IFW :=
      match pports with
      | VParamPortsNil => Sret ifw
      | VParamPortsOne pdecl => trsVParamDecl pdecl ifw
      | VParamPortsCons pdecl spports => (nidl <- trsVParamDecl pdecl ifw;
                                          trsVParamPorts spports nidl)
      end.

    Definition trsVModuleDecl (m: @VModuleDecl vid_t)
      (ifw: IFW): trsOk IFF :=
      match m with
      | VModuleDeclAnsi mn pports pdecls mitems =>
          (pifw <- trsVParamPorts pports ifw;
           trsVModuleItems mitems (pifw, []))
      end.

    Definition trsVModuleDecl_IFF (m: @VModuleDecl vid_t) (iff: IFF) := trsVModuleDecl m (iff_ifw_ iff).

    Fixpoint trsM_iff_rep (m: @VModuleDecl vid_t)
      (iff: IFF) (n: nat): trsOk IFF :=
      match n with
      | O => Sret iff
      | S n' => match trsM_iff_rep m iff n' with
        | Sret niff => trsVModuleDecl_IFF m niff
        | Fail f => Fail f
        end
      end.

    Lemma trsM_iff_rep_is_chain (m: @VModuleDecl vid_t) (n: nat) (iff iff': IFF)
      (REP: trsM_iff_rep m iff n = Sret iff'):
         chain iff (trsVModuleDecl_IFF m) iff'.
    Proof.
      generalize dependent iff'. induction n as [|n']; intros.
      - (* n = 0 *)
        simpl in REP. injection REP as ->. eapply chain_bottom.
      - (* n = S n' *)
        simpl in REP. remember (trsVModuleDecl_IFF m) as F eqn: EQf in *. clear EQf.
        destruct (trsM_iff_rep m iff n') eqn: Hn' in REP. 2: { discriminate REP. }
        eapply chain_step; eauto.
    Qed.


    Definition trsM_IFF (m: @VModuleDecl vid_t)
      (oiff: trsOk IFF): (State * State) (* "updated" flop state * outputs *) :=
      match oiff with
      | Sret iff => let (ins, outs) := getIOIds m in
                    (iff_flops_ iff, hfilter outs (iff_ifw_ iff))
      | Fail _ => ([], [])
      end.

  End WithDeclsFuncs.

  Definition trsNext (flops: State) (uo: State * State) :=
    (hupds flops (fst uo), snd uo).

  Definition trsT (trsF: State -> State -> (State * State)):
    State -> State -> (State * State) :=
    fun ins flops => trsNext flops (trsF ins flops).

  (*! Collect declarations *)

  Section WithCurPos.
    Variable cpos: hpath. (** The current position in terms of modules/regions *)

    Definition declsVNetDeclAssign (pd: @VPackedDims vid_t) (nda: @VNetDeclAssign vid_t): trsOk Decls :=
      match nda with
      | VNetDeclAssignOne vid oe => Sret (hsingle (cons (HEltVid vid) cpos) [])
      end.

    Fixpoint declsVNetDeclAssigns (pd: @VPackedDims vid_t) (ndas: @VNetDeclAssigns vid_t): trsOk Decls :=
      match ndas with
      | VNetDeclAssignsOne nda => declsVNetDeclAssign pd nda
      | VNetDeclAssignsCons nda ndas' => (nwd <- declsVNetDeclAssign pd nda;
                                          nwds <- declsVNetDeclAssigns pd ndas';
                                          Sret (hupds nwd nwds))
      end.

    Definition declsVVarDeclAssign (dt: @VDataType vid_t) (nda: @VVarDeclAssign vid_t): trsOk Decls :=
      match nda with
      | VVarDeclAssignVar vid vd oe => Sret (hsingle (cons (HEltVid vid) cpos) [])
      end.

    Fixpoint declsVVarDeclAssigns (dt: @VDataType vid_t) (ndas: @VVarDeclAssigns vid_t): trsOk Decls :=
      match ndas with
      | VVarDeclAssignsOne nda => declsVVarDeclAssign dt nda
      | VVarDeclAssignsCons nda ndas' => (nwd <- declsVVarDeclAssign dt nda;
                                          nwds <- declsVVarDeclAssigns dt ndas';
                                          Sret (hupds nwd nwds))
      end.

    Definition declsVParamAssign (dti: @VDataTypeOrImplicit vid_t) (nda: @VParamAssign vid_t): trsOk Decls :=
      match nda with
      | VParamAssignOne vid (VConstParamExprMinTypMax e) => Sret (hsingle (cons (HEltVid vid) cpos) [])
      end.

    Fixpoint declsVParamAssigns (dti: @VDataTypeOrImplicit vid_t) (ndas: @VParamAssigns vid_t): trsOk Decls :=
      match ndas with
      | VParamAssignsOne nda => declsVParamAssign dti nda
      | VParamAssignsCons nda ndas' => (nwd <- declsVParamAssign dti nda;
                                        nwds <- declsVParamAssigns dti ndas';
                                        Sret (hupds nwd nwds))
      end.

    Definition declsVPkgGenItemDecl (pgid: @VPkgGenItemDecl vid_t): trsOk Decls :=
      match pgid with
      | VPkgGenItemDeclNet (VNetDeclOne nt pd ndas) => declsVNetDeclAssigns pd ndas
      | VPkgGenItemDeclData (VDataDeclVarDecl (VVarDeclOne dt vdas)) => declsVVarDeclAssigns dt vdas
      | VPkgGenItemDeclTask td => Sret []
      | VPkgGenItemDeclFunc fd => Sret []
      | VPkgGenItemDeclParam (VParamDeclData dti pas) => declsVParamAssigns dti pas
      | VPkgGenItemDeclLocalParam (VLocalParamDeclOne dti pas) => declsVParamAssigns dti pas
      end.

    Definition declsVModuleCommonItem (mci: @VModuleCommonItem vid_t): trsOk Decls :=
      match mci with
      | VModuleCommonItemDecl (VModuleGenItemDeclPkg pgid) => declsVPkgGenItemDecl pgid
      | VModuleCommonItemAssert cca => Sret []
      | VModuleCommonItemContAssign cass => Sret []
      | VModuleCommonItemAlways akwd (VStatementO sti) => Sret []
      | _ => Fail TrsNotSupported
      end.

    Definition declsVModuleOrGenerateItem (mgi: @VModuleOrGenerateItem vid_t): trsOk Decls :=
      match mgi with
      | VModuleOrGenerateItemIns mins => Sret []
      | VModuleOrGenerateItemCommon mci => declsVModuleCommonItem mci
      end.

  End WithCurPos.

  Fixpoint declsVGenerateModuleItem (gmi: @VGenerateModuleItem vid_t) (cpos: hpath)
    (decls: Decls): trsOk Decls :=
    match gmi with
    | VGenerateModuleItemCond ce tgmi ofgmi =>
        (ftrs <- (match ofgmi with
                  | Some fgmi => declsVGenerateModuleItem fgmi cpos decls
                  | _ => Sret decls
                  end);
         ttrs <- declsVGenerateModuleItem tgmi cpos decls;
         Sret (hupds ftrs ttrs))
    | VGenerateModuleItemBlock gmis =>
        (** NOTE: it's very important to use [iterate_resume] (instead of [iterate]).
         * We indeed would like to resume iteration if we fail to convert a particular module item to
         * its transition function, especially when the failure is due to yet-undriven signals.
         *)
        iterate_resume (fun gmi => declsVGenerateModuleItem gmi cpos) gmis decls
    | VGenerateModuleItemModule mgi =>
        (ndecls <- declsVModuleOrGenerateItem cpos mgi ~> decls;
         Sret (hupds decls ndecls))
    end.

  Definition declsVNonPortModuleItem (pnp: @VNonPortModuleItem vid_t)
    (decls: Decls): trsOk Decls :=
    match pnp with
    | VNonPortGeneratedModuleIns (VGeneratedModuleInsO gmi) => declsVGenerateModuleItem gmi nil decls
    | VNonPortModuleOrGenerateItem mgi =>
        (ndecls <- declsVModuleOrGenerateItem nil mgi ~> decls;
         Sret (hupds decls ndecls))
    end.

  Definition declsVModuleItem (mitem: @VModuleItem vid_t)
    (decls: Decls): trsOk Decls :=
    match mitem with
    | VModuleItemPortDecl pdec => Sret decls
    | VModuleItemNonPort pnp => declsVNonPortModuleItem pnp decls
    end.

  Fixpoint declsVModuleItems (mitems: @VModuleItems vid_t)
    (decls: Decls): trsOk Decls :=
    match mitems with
    | VModuleItemsOne mitem => declsVModuleItem mitem decls
    | VModuleItemsCons mitem mitems' =>
        (ndecls <- declsVModuleItem mitem decls <~ decls;
         declsVModuleItems mitems' ndecls)
    end.

  Definition declsVParamDecl (pdecl: @VParamDecl vid_t)
    (decls: Decls): trsOk Decls :=
    match pdecl with
    | VParamDeclData dti pas => (nidl <- declsVParamAssigns nil dti pas;
                                 Sret (hmergeL decls nidl))
    end.

  Fixpoint declsVParamPorts (pports: @VParamPorts vid_t)
    (decls: Decls): trsOk Decls :=
    match pports with
    | VParamPortsNil => Sret decls
    | VParamPortsOne pdecl => declsVParamDecl pdecl decls
    | VParamPortsCons pdecl spports => (nidl <- declsVParamDecl pdecl decls;
                                        declsVParamPorts spports nidl)
    end.

  Definition declsVAnsiPortDecl (pdecl: @VAnsiPortDecl vid_t) (decls: Decls): trsOk Decls :=
    match pdecl with
    | VAnsiPortDeclNet None vid => Sret decls
    | VAnsiPortDeclNet (Some (VNetPortHeaderO opd (VPortTypeO onty pdims))) vid =>
        Sret (hmergeL decls (hsingle (cons (HEltVid vid) nil) []))
    | VAnsiPortDeclVar None vid => Sret decls
    | VAnsiPortDeclVar (Some (VVarPortHeaderO opd dt)) vid =>
        Sret (hmergeL decls (hsingle (cons (HEltVid vid) nil) []))
    end.

  Fixpoint declsVAnsiPortDecls (pdecls: @VAnsiPortDecls vid_t) (decls: Decls): trsOk Decls :=
    match pdecls with
    | VAnsiPortDeclNil => Sret decls
    | VAnsiPortDeclsOne pdecl => declsVAnsiPortDecl pdecl decls
    | VAnsiPortDeclsCons pdecl spdecls => (ndecls <- declsVAnsiPortDecl pdecl decls;
                                           declsVAnsiPortDecls spdecls ndecls)
    end.

  Definition declsVModuleDecl (m: @VModuleDecl vid_t): Decls :=
    match m with
    | VModuleDeclAnsi mn pports pdecls mitems =>
        match (pidl <- declsVParamPorts pports [];
               ndecls <- declsVAnsiPortDecls pdecls pidl;
               declsVModuleItems mitems ndecls) with
        | Sret d => d
        | Fail _ => []
        end
    end.

  (*! Collect functions *)

  Definition declsVParamPortsM (m: @VModuleDecl vid_t): Decls :=
    match m with
    | VModuleDeclAnsi mn pports pdecls mitems =>
        match declsVParamPorts pports [] with
        | Sret pdecls => pdecls
        | Fail _ => []
        end
    end.

  Definition trsVParamPortsM (m: @VModuleDecl vid_t): State :=
    match m with
    | VModuleDeclAnsi mn pports pdecls mitems =>
        match trsVParamPorts [] [>] [] pports [] with
        | Sret params => params
        | Fail _ => []
        end
    end.

  Section WithParams.
    Variables (pdecls: Decls) (params: State).

    Definition funcsVFuncDecl (fd: @VFuncDecl vid_t): Funcs :=
      match fd with
      | VFuncDeclOne dti fid ports (VStatementO sti) =>
          fmapSingle fid {| func_input_vids :=
                             match declsVAnsiPortDecls ports [] with
                             | Sret decls => match decls with
                                             | HMapStr ds => List.map fst ds
                                             | _ => nil
                                             end
                             | Fail _ => nil
                             end;
                           func_func :=
                             fun args =>
                               match (decls <- declsVAnsiPortDecls ports [];
                                      trsVStatementItem (hmergeL pdecls decls) [>] [] nil (hmergeL params args) true sti []) with
                               | Sret nfv => snd nfv
                               | Fail _ => []
                               end |}
      end.

    Definition funcsVPkgGenItemDecl (pgid: @VPkgGenItemDecl vid_t): trsOk Funcs :=
      match pgid with
      | VPkgGenItemDeclNet (VNetDeclOne nt pd ndas) => Sret [>]
      | VPkgGenItemDeclData (VDataDeclVarDecl (VVarDeclOne dt vdas)) => Sret [>]
      | VPkgGenItemDeclTask td => Sret [>]
      | VPkgGenItemDeclFunc fd => Sret (funcsVFuncDecl fd)
      | VPkgGenItemDeclParam (VParamDeclData dti pas) => Sret [>]
      | VPkgGenItemDeclLocalParam (VLocalParamDeclOne dti pas) => Sret [>]
      end.

    Definition funcsVModuleCommonItem (mci: @VModuleCommonItem vid_t): trsOk Funcs :=
      match mci with
      | VModuleCommonItemDecl (VModuleGenItemDeclPkg pgid) => funcsVPkgGenItemDecl pgid
      | VModuleCommonItemAssert cca => Sret [>]
      | VModuleCommonItemContAssign cass => Sret [>]
      | VModuleCommonItemAlways akwd (VStatementO sti) => Sret [>]
      | _ => Fail TrsNotSupported
      end.

    Definition funcsVModuleOrGenerateItem (mgi: @VModuleOrGenerateItem vid_t): trsOk Funcs :=
      match mgi with
      | VModuleOrGenerateItemIns mins => Sret [>]
      | VModuleOrGenerateItemCommon mci => funcsVModuleCommonItem mci
      end.

    Fixpoint funcsVGenerateModuleItem (gmi: @VGenerateModuleItem vid_t)
      (funcs: Funcs): trsOk Funcs :=
      match gmi with
      | VGenerateModuleItemCond ce tgmi ofgmi =>
          (ftrs <- (match ofgmi with
                    | Some fgmi => funcsVGenerateModuleItem fgmi funcs
                    | _ => Sret funcs
                    end);
           ttrs <- funcsVGenerateModuleItem tgmi funcs;
           Sret (fmapMerge ftrs ttrs))
      | VGenerateModuleItemBlock gmis =>
          (** NOTE: it's very important to use [iterate_resume] (instead of [iterate]).
           * We indeed would like to resume iteration if we fail to convert a particular module item to
           * its transition function, especially when the failure is due to yet-undriven signals.
           *)
          iterate_resume (fun gmi => funcsVGenerateModuleItem gmi) gmis funcs
      | VGenerateModuleItemModule mgi =>
          (nfuncs <- funcsVModuleOrGenerateItem mgi ~> funcs;
           Sret (fmapMerge funcs nfuncs))
      end.

    Definition funcsVNonPortModuleItem (pnp: @VNonPortModuleItem vid_t)
      (funcs: Funcs): trsOk Funcs :=
      match pnp with
      | VNonPortGeneratedModuleIns (VGeneratedModuleInsO gmi) => funcsVGenerateModuleItem gmi funcs
      | VNonPortModuleOrGenerateItem mgi =>
          (nfuncs <- funcsVModuleOrGenerateItem mgi ~> funcs;
           Sret (fmapMerge funcs nfuncs))
      end.

    Definition funcsVModuleItem (mitem: @VModuleItem vid_t)
      (funcs: Funcs): trsOk Funcs :=
      match mitem with
      | VModuleItemPortDecl pdec => Sret funcs
      | VModuleItemNonPort pnp => funcsVNonPortModuleItem pnp funcs
      end.

    Fixpoint funcsVModuleItems (mitems: @VModuleItems vid_t)
      (funcs: Funcs): trsOk Funcs :=
      match mitems with
      | VModuleItemsOne mitem => funcsVModuleItem mitem funcs
      | VModuleItemsCons mitem mitems' =>
          (nfuncs <- funcsVModuleItem mitem funcs <~ funcs;
           funcsVModuleItems mitems' nfuncs)
      end.

    Definition funcsVModuleDecl (m: @VModuleDecl vid_t): Funcs :=
      match m with
      | VModuleDeclAnsi mn pports pdecls mitems =>
          match funcsVModuleItems mitems [>] with
          | Sret funcs => funcs
          | Fail _ => [>]
          end
      end.

  End WithParams.

  Section StructuredState.

    Class StructuredState (A : Set) := {
      from_state: State -> trsOk A;
      to_state: A -> State;
    }.

  End StructuredState.

  Section MTrsOf.
    Variable (m: @VModuleDecl vid_t) (funcs: Funcs) (etrs: MTrss).

    Variable (Inputs Flops: Set).
    Context `{StructuredState Inputs} `{StructuredState Flops}.

    Definition decls: Decls := declsVModuleDecl m.
    Definition ctxs: State := [].

    Definition MTrs_rep_n n inputs flops : (State * State) (* (register updates, outputs) *)
      := (trsM_IFF m (trsM_iff_rep decls funcs ctxs etrs m (hupds inputs flops, []) n)).

    Definition format (A: Set) (state: State) `{StructuredState A} :=
      a <- from_state (A := A) state;
      Sret (to_state a).
    Arguments format _ _ {_}.

    Definition is_module_trs (trs:  State (* inputs *) -> State (* current flop state *) ->
                 (State * State) (* flop updates for next cycle * outputs *)) := (
          let F := trsVModuleDecl_IFF decls funcs ctxs etrs m in
          let (_, out_ids) := getIOIds m in
          forall inputs flops upds outs,
          trs inputs flops = (upds, outs) ->
            match (format Inputs inputs, format Flops flops) with
            | (Sret inputs, Sret flops) => (* If the data is formatted successfully, the transition function is defined as a lfp. *)
              exists state, LFP (hupds inputs flops, []) F (state, upds) /\
              hfilter out_ids state = outs
            | _ => (upds, outs) = ([], []) (* If the data cannot be formatted, the transition fails. *)
            end
        ).

    (* Helper function for relating user-defined structured transitions with the semantical state transitions. *)
    Definition to_unstructured_trs {Updates Outputs: Set} (update_to_state: Updates -> State) (output_to_state: Outputs -> State)
      (structured_trs: Inputs -> Flops -> (Updates * Outputs))
        : State -> State -> (State * State) :=
      fun inputs flops =>
        match (from_state (A := Inputs) inputs, from_state (A := Flops) flops) with
        | (Sret inputs, Sret flops) =>
          let uo := (structured_trs inputs flops) in
          (update_to_state (fst uo), output_to_state (snd uo))
        | _ => ([], [])
        end.

    Record MTrsOf: Type :=
      mk_MTrsOf {
        mtrsof_mtrs: MTrs;
        mtrsof_mtrs_input: mtrsof_mtrs.(mtrs_input_vids) = fst (getIOIds m);
        mtrsof_mtrs_output: mtrsof_mtrs.(mtrs_output_vids) = snd (getIOIds m);
        mtrsof_mtrs_func: is_module_trs mtrsof_mtrs.(mtrs_func);
      }.

    #[global] Coercion mtrsof_mtrs : MTrsOf >-> MTrs.

  End MTrsOf.

  #[global] Arguments is_module_trs m funcs etrs (Inputs Flops) {_ _}.
  #[global] Arguments MTrsOf m funcs etrs (Inputs Flops) {_ _}.

End Semantics.
