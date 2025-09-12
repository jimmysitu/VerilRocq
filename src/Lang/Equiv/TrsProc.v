Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Lib.Lib. Import HMapNotations. Import SZNotations.
Require Import Lang.Syntax Lang.Analysis Lang.Semantics. Include SFMonadNotations.
Require Import Coq.micromega.Lia.

Require Import UpdGraph Standard.

Set Implicit Arguments.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope hmap_scope.

Section TrsProc.
  Context `{sz_ops}.
  Context `{vid_ops}.
  Context `{array_ops hmap}.

  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Definition trsProc (proc: Process) (ifw: IFW): trsOk IFF :=
    execEvalEvent decls funcs mtrss ifw (proc_pos proc) (proc_evu proc).

  Fixpoint trsProcs (procs: Processes) (iff: IFF): trsOk IFF :=
    match procs with
    | proc :: tprocs => (niff <- trsProc proc (fst iff) <~ ([], []);
                         trsProcs tprocs (iffupds iff niff))
    | nil => Sret iff
    end.

  Definition ProcWfUpd (proc: Process): Prop :=
    forall ifw niff,
      trsProc proc ifw = Sret niff ->
      HMapStrEmpty (fst niff).

  Definition ProcsWfUpd (procs: Processes): Prop :=
    Forall ProcWfUpd procs.

  Definition ProcsUpdDisj (proc1 proc2: Process): Prop :=
    forall ifw1 niff1,
      trsProc proc1 ifw1 = Sret niff1 ->
      forall ifw2 niff2,
        trsProc proc2 ifw2 = Sret niff2 ->
        HDisj (fst niff1) (fst niff2).

  Definition ProcsWfDet (procs: Processes): Prop :=
    forall n1 n2 proc1 proc2,
      n1 <> n2 ->
      nth_error procs n1 = Some proc1 ->
      nth_error procs n2 = Some proc2 ->
      ProcsUpdDisj proc1 proc2.

  (*! Facts *)

  Lemma ProcsWfUpd_cons_inv:
    forall proc procs,
      ProcsWfUpd (proc :: procs) -> ProcWfUpd proc /\ ProcsWfUpd procs.
  Proof using .
    intros; apply Forall_cons_iff in H3; assumption.
  Qed.

  Lemma ProcsWfDet_cons_inv:
    forall proc procs,
      ProcsWfDet (proc :: procs) ->
      (forall tproc, In tproc procs -> ProcsUpdDisj proc tproc) /\
      ProcsWfDet procs.
  Proof using .
    unfold ProcsWfDet; simpl; intros; split.
    - intros.
      apply In_nth_error in H4; destruct H4 as [n ?].
      apply H3 with (n1:= O) (n2:= S n); auto.
    - intros.
      apply H3 with (n1:= S n1) (n2:= S n2); auto.
  Qed.

  Lemma ProcsWfUpd_app_inv:
    forall procs1 procs2,
      ProcsWfUpd (procs1 ++ procs2) -> ProcsWfUpd procs1 /\ ProcsWfUpd procs2.
  Proof using .
    unfold ProcsWfUpd; intros.
    apply Forall_app; assumption.
  Qed.

  Lemma ProcsWfDet_app_inv:
    forall procs1 procs2,
      ProcsWfDet (procs1 ++ procs2) -> ProcsWfDet procs1 /\ ProcsWfDet procs2.
  Proof using .
    unfold ProcsWfDet; intros.
    split; intros.
    - eapply H3; [eassumption|..].
      + rewrite nth_error_app1; [assumption|].
        apply nth_error_Some; congruence.
      + rewrite nth_error_app1; [assumption|].
        apply nth_error_Some; congruence.
    - apply H3 with (n1:= (n1 + length procs1)%nat) (n2:= (n2 + length procs1)%nat).
      + lia.
      + rewrite nth_error_app2; [|lia].
        rewrite PeanoNat.Nat.add_sub; assumption.
      + rewrite nth_error_app2; [|lia].
        rewrite PeanoNat.Nat.add_sub; assumption.
  Qed.

  Lemma trsProcs_never_fails:
    forall procs iff f, trsProcs procs iff <> Fail f.
  Proof using .
    induction procs; simpl; intros; [discriminate|].
    destruct (trsProc _ _); eapply IHprocs.
  Qed.

  Lemma trsProcs_app:
    forall procs1 procs2 iff,
      trsProcs (procs1 ++ procs2) iff = (niff <- trsProcs procs1 iff <~ iff; trsProcs procs2 niff).
  Proof using .
    induction procs1; simpl; intros; [reflexivity|].
    destruct (trsProc _ _).
    - rewrite IHprocs1.
      destruct (trsProcs _ _) eqn:Ht; [reflexivity|].
      exfalso; eapply trsProcs_never_fails; eassumption.
    - unfold iffupds; simpl.
      rewrite !hmergeR_empty.
      destruct iff; simpl; apply IHprocs1.
  Qed.

  Inductive TrsProcsUpd: Processes -> list State -> Prop :=
  | TrsProcsUpdNil: TrsProcsUpd nil nil
  | TrsProcsUpdFail: forall proc ifw f,
      trsProc proc ifw = Fail f ->
      forall procs upds,
        TrsProcsUpd procs upds ->
        TrsProcsUpd (proc :: procs) ([] :: upds)
  | TrsProcsUpdSret: forall proc ifw uifw uflops,
      trsProc proc ifw = Sret (uifw, uflops) ->
      forall procs upds,
        TrsProcsUpd procs upds ->
        TrsProcsUpd (proc :: procs) (uifw :: upds).

  Lemma TrsProcsUpd_disj_ind:
    forall proc procs
           (Hprocs: forall tproc, In tproc procs -> ProcsUpdDisj proc tproc)
           ifw uifw uflops,
      trsProc proc ifw = Sret (uifw, uflops) ->
      forall upds,
        TrsProcsUpd procs upds ->
        forall upd,
          In upd upds ->
          HDisj uifw upd.
  Proof using .
    induction 3; simpl; intros; [exfalso; auto|..].
    - destruct H6; [subst; red; destruct uifw; auto|].
      eapply IHTrsProcsUpd; [|assumption].
      intros; apply Hprocs; right; assumption.
    - destruct H6.
      + subst.
        specialize (Hprocs _ (or_introl eq_refl)).
        specialize (Hprocs _ _ H3 _ _ H4).
        assumption.
      + apply IHTrsProcsUpd; [|assumption].
        intros; apply Hprocs; right; assumption.
  Qed.

  Lemma TrsProcsUpd_disj:
    forall procs1 procs2 (HprocsD: ProcsWfDet (procs1 ++ procs2))
           upds1,
      TrsProcsUpd procs1 upds1 ->
      forall upds2,
        TrsProcsUpd procs2 upds2 ->
        forall upd1 upd2,
          In upd1 upds1 ->
          In upd2 upds2 ->
          HDisj upd1 upd2.
  Proof using .
    induction 2; simpl; intros; [exfalso; auto|..].
    - destruct H6; [subst; red; auto|].
      eapply IHTrsProcsUpd; try eassumption.
      eapply ProcsWfDet_cons_inv; eassumption.
    - destruct H6.
      + subst uifw.
        eapply TrsProcsUpd_disj_ind with (procs:= procs2); try eassumption.
        simpl in HprocsD; apply ProcsWfDet_cons_inv in HprocsD; destruct HprocsD as [HprocsD _].
        intros; apply HprocsD.
        apply in_or_app; right; assumption.
      + eapply IHTrsProcsUpd; try eassumption.
        eapply ProcsWfDet_cons_inv; eassumption.
  Qed.

  Fixpoint updMerge (upds: list State): State :=
    match upds with
    | nil => []
    | upd :: tupds => hmergeR upd (updMerge tupds)
    end.

  Lemma updMerge_HMapStrEmpty:
    forall upds (Hupds: Forall HMapStrEmpty upds),
      HMapStrEmpty (updMerge upds).
  Proof using .
    induction upds as [|upd upds]; simpl; intros; [auto; fail|].
    inv Hupds.
    apply hmergeR_HMapStrEmpty; auto.
  Qed.

  Lemma updMerge_disj_ind:
    forall upd (Hupd: HMapStrEmpty upd)
           upds (Hupds: Forall HMapStrEmpty upds),
      (forall iupd, In iupd upds -> HDisj upd iupd) ->
      HDisj upd (updMerge upds).
  Proof using .
    induction upds as [|iupd upds]; simpl; intros; [destruct upd; auto; fail|].
    inv Hupds.
    apply HDisj_sym, HDisj_hmergeR_split.
    - assumption.
    - apply HDisj_sym, H3; left; reflexivity.
    - apply updMerge_HMapStrEmpty; assumption.
    - apply HDisj_sym, IHupds; [assumption|].
      intros; apply H3; right; assumption.
    - assumption.
  Qed.

  Lemma updMerge_disj:
    forall upds1 (Hupds1: Forall HMapStrEmpty upds1)
           upds2 (Hupds2: Forall HMapStrEmpty upds2),
      (forall upd1 upd2, In upd1 upds1 -> In upd2 upds2 -> HDisj upd1 upd2) ->
      HDisj (updMerge upds1) (updMerge upds2).
  Proof using .
    induction upds1 as [|upd1 upds1]; simpl; intros; [auto; fail|].
    inv Hupds1.
    apply HDisj_hmergeR_split.
    - assumption.
    - apply updMerge_disj_ind; try assumption.
      intros; apply H3; auto.
    - apply updMerge_HMapStrEmpty; assumption.
    - apply IHupds1; try assumption.
      intros; eapply H3; auto.
    - apply updMerge_HMapStrEmpty; assumption.
  Qed.

  Lemma TrsProcsUpd_HMapStrEmpty:
    forall procs (Hprocs: ProcsWfUpd procs) upds,
      TrsProcsUpd procs upds ->
      Forall HMapStrEmpty upds.
  Proof using .
    induction 2; [constructor|..].
    - constructor; [red; auto|].
      apply IHTrsProcsUpd.
      eapply ProcsWfUpd_cons_inv; eassumption.
    - inv Hprocs.
      constructor.
      + apply H7 in H3; assumption.
      + apply IHTrsProcsUpd; assumption.
  Qed.

  Lemma updMerge_TrsProcsUpd_disj_ind:
    forall proc (Hproc: ProcWfUpd proc) ifw uifw uflops,
      trsProc proc ifw = Sret (uifw, uflops) ->
      forall procs (Hprocs: ProcsWfUpd procs),
        (forall tproc, In tproc procs -> ProcsUpdDisj proc tproc) ->
        forall tupds,
          TrsProcsUpd procs tupds ->
          HDisj uifw (updMerge tupds).
  Proof using .
    intros.
    apply updMerge_disj_ind.
    - specialize (Hproc _ _ H3); assumption.
    - eapply TrsProcsUpd_HMapStrEmpty; eassumption.
    - intros.
      move H3 at bottom.
      induction H5; [elim H6|..].
      + inv H6; [destruct uifw; red; auto|].
        apply ProcsWfUpd_cons_inv in Hprocs; dest.
        apply IHTrsProcsUpd; [assumption| |assumption].
        intros; apply H4; right; assumption.
      + inv H6.
        * specialize (H4 _ (or_introl eq_refl)).
          specialize (H4 _ _ H3 _ _ H5); assumption.
        * apply ProcsWfUpd_cons_inv in Hprocs; dest.
          apply IHTrsProcsUpd; [assumption| |assumption].
          intros; apply H4; right; assumption.
  Qed.

  Lemma trsProcs_TrsProcsUpd:
    forall procs (HprocsU: ProcsWfUpd procs) (HprocsD: ProcsWfDet procs)
           ifw flops nifw nflops,
      trsProcs procs (ifw, flops) = Sret (nifw, nflops) ->
      exists upds,
        TrsProcsUpd procs upds /\
          nifw = hmergeR ifw (updMerge upds) /\
          HMapStrEmpty (updMerge upds).
  Proof using .
    induction procs as [|proc procs]; simpl; intros.
    - inv H3; exists nil; repeat split.
      + constructor.
      + simpl; rewrite hmergeR_empty; reflexivity.

    - apply ProcsWfUpd_cons_inv in HprocsU; dest.
      apply ProcsWfDet_cons_inv in HprocsD; dest.
      destruct (trsProc proc ifw) as [[uifw uflops]|] eqn:Hproc;
        unfold iffupds in *; simpl in *.
      + apply IHprocs in H3; [|assumption..].
        destruct H3 as [tupds ?]; dest; subst.
        exists (uifw :: tupds); repeat split.
        * econstructor; eassumption.
        * simpl; apply hmergeR_assoc.
          { apply H4 in Hproc; assumption. }
          { eapply updMerge_TrsProcsUpd_disj_ind; eassumption. }
        * apply updMerge_HMapStrEmpty; constructor.
          { apply H4 in Hproc; assumption. }
          { eapply TrsProcsUpd_HMapStrEmpty; eassumption. }
      + rewrite !hmergeR_empty in H3.
        apply IHprocs in H3; [|assumption..].
        destruct H3 as [tupds ?]; dest; subst.
        exists ([] :: tupds); repeat split.
        * econstructor; eassumption.
        * simpl; destruct (updMerge tupds); reflexivity.
        * apply updMerge_HMapStrEmpty; constructor.
          { red; auto. }
          { eapply TrsProcsUpd_HMapStrEmpty; eassumption. }
  Qed.

  Lemma trsProcs_upds_disj:
    forall procs1 procs2 (HprocsU: ProcsWfUpd (procs1 ++ procs2))
           (HprocsD: ProcsWfDet (procs1 ++ procs2))
           ifw1 flops1 nifw1 nflops1,
      trsProcs procs1 (ifw1, flops1) = Sret (nifw1, nflops1) ->
      forall ifw2 flops2 nifw2 nflops2,
        trsProcs procs2 (ifw2, flops2) = Sret (nifw2, nflops2) ->
        exists uifw1 uifw2,
          nifw1 = hmergeR ifw1 uifw1 /\ HMapStrEmpty uifw1 /\
            nifw2 = hmergeR ifw2 uifw2 /\ HMapStrEmpty uifw2 /\
            HDisj uifw1 uifw2.
  Proof using .
    intros.
    apply trsProcs_TrsProcsUpd in H3;
      [|apply ProcsWfUpd_app_inv in HprocsU; dest; assumption
      |apply ProcsWfDet_app_inv in HprocsD; dest; assumption].
    apply trsProcs_TrsProcsUpd in H4;
      [|apply ProcsWfUpd_app_inv in HprocsU; dest; assumption
      |apply ProcsWfDet_app_inv in HprocsD; dest; assumption].
    destruct H3 as [upds1 ?].
    destruct H4 as [upds2 ?]; dest.
    do 2 eexists; repeat split; [eassumption..|].
    apply updMerge_disj.
    - eapply TrsProcsUpd_HMapStrEmpty; [|eassumption].
      apply ProcsWfUpd_app_inv in HprocsU; dest; assumption.
    - eapply TrsProcsUpd_HMapStrEmpty; [|eassumption].
      apply ProcsWfUpd_app_inv in HprocsU; dest; assumption.
    - eapply TrsProcsUpd_disj; eassumption.
  Qed.

  Lemma trsProcs_fp_app:
    forall procs1 procs2 (HprocsU: ProcsWfUpd (procs1 ++ procs2))
           (HprocsD: ProcsWfDet (procs1 ++ procs2))
           stf flops nflops,
      trsProcs (procs1 ++ procs2) (stf, flops) = Sret (stf, nflops) ->
      exists nflops1,
        trsProcs procs1 (stf, flops) = Sret (stf, nflops1) /\
          trsProcs procs2 (stf, nflops1) = Sret (stf, nflops).
  Proof using .
    intros.
    rewrite trsProcs_app in H3.
    destruct (trsProcs procs1 (stf, flops)) as [[ist iflops]|] eqn:Hi;
      [|exfalso; eapply trsProcs_never_fails; eassumption].

    eapply trsProcs_upds_disj with (procs1:= procs1) (procs2:= procs2) in Hi; [|eassumption..].
    destruct Hi as [uifw1 [uifw2 ?]]; dest; subst.

    rewrite hmergeR_assoc in H6; [|assumption..].
    apply eq_sym, hmergeR_absorbed_left in H6; [|assumption..].
    rewrite H6 in *.
    eexists; split; [reflexivity|eassumption].
  Qed.

  Lemma trsProcs_fp_ind:
    forall procs (HprocsU: ProcsWfUpd procs)
           (HprocsD: ProcsWfDet procs)
           stf flops nflops,
      trsProcs procs (stf, flops) = Sret (stf, nflops) ->
      forall proc,
        In proc procs ->
        match trsProc proc stf with
        | Sret (pifw, pflops) => hmergeR stf pifw = stf
        | Fail _ => True
        end.
  Proof using .
    intros.
    apply in_split in H4.
    destruct H4 as [procs1 [procs2 ?]]; subst procs.
    eapply trsProcs_fp_app in H3; [|assumption..].
    destruct H3 as [nflops1 [? ?]].
    replace (proc :: procs2) with ([proc] ++ procs2) in H4 by reflexivity.
    eapply trsProcs_fp_app in H4;
      [|apply ProcsWfUpd_app_inv in HprocsU; dest; assumption
      |apply ProcsWfDet_app_inv in HprocsD; dest; assumption].
    destruct H4 as [nflops2 [? ?]].
    simpl in H4.
    destruct (trsProc proc stf) as [[uifw uflops]|]; simpl in *; [|auto; fail].
    inv H4.
    rewrite H7; assumption.
  Qed.

  Inductive TrsProcsRep (procs: Processes): IFW -> IFW -> Flops -> Prop :=
  | TrsProcsNext: forall ifw1 ifwf flops,
      TrsProcsRep procs ifw1 ifwf flops ->
      forall ifw0 flops1,
        trsProcs procs (ifw0, []) = Sret (ifw1, flops1) ->
        TrsProcsRep procs ifw0 ifwf flops
  | TrsProcsFix: forall ifw flops,
      trsProcs procs (ifw, []) = Sret (ifw, flops) ->
      TrsProcsRep procs ifw ifw flops.

  Definition TrsProcsRepProg (procs: Processes): Prop :=
    forall ifw0, exists ifwf flops, TrsProcsRep procs ifw0 ifwf flops.

  Definition TrsProcsRepConst (procs: Processes): Prop :=
    forall ifw0 ifwf0 flops0,
      TrsProcsRep procs ifw0 ifwf0 flops0 ->
      forall ifw1 ifwf1 flops1,
        TrsProcsRep procs ifw1 ifwf1 flops1 ->
        hupds ifwf0 ifwf1 = ifwf1.

  Lemma TrsProcsRep_fix_det:
    forall procs ifw0 flops0,
      trsProcs procs (ifw0, []) = Sret (ifw0, flops0) ->
      forall ifw1 flops1,
        TrsProcsRep procs ifw0 ifw1 flops1 ->
        ifw0 = ifw1 /\ flops0 = flops1.
  Proof using .
    induction 2; intros.
    - rewrite H3 in H5; inv H5.
      apply IHTrsProcsRep; assumption.
    - rewrite H3 in H4; inv H4.
      split; reflexivity.
  Qed.

  Lemma TrsProcsRep_det:
    forall procs init ifw0 flops0,
      TrsProcsRep procs init ifw0 flops0 ->
      forall ifw1 flops1,
        TrsProcsRep procs init ifw1 flops1 ->
        ifw0 = ifw1 /\ flops0 = flops1.
  Proof using .
    induction 1; intros.
    - destruct H5.
      + rewrite H4 in H6; inv H6.
        apply IHTrsProcsRep; assumption.
      + rewrite H4 in H5; inv H5.
        eapply TrsProcsRep_fix_det in H4; [|eassumption].
        dest; subst; split; reflexivity.
    - eapply TrsProcsRep_fix_det; eassumption.
  Qed.

End TrsProc.
