Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Lib.Lib. Import HMapNotations. Import SZNotations.
Require Import Lang.Syntax Lang.Analysis Lang.Semantics. Include SFMonadNotations.

Require Import UpdGraph Standard TrsProc StfUpdGraph StdUpdGraph ProcUpdGraph.

Set Implicit Arguments.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope hmap_scope.

Section StfStd.
  Context `{sz_ops}.
  Context `{vid_ops}.
  Context `{array_ops hmap}.

  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss) (vars: list vid_t)
    (mprocs: Processes). (* Processes from the given module. *)

  Definition procs: Processes := getProcInputClk :: mprocs.

  Definition ipsIns (inputs: InitState): IPS :=
    (inputs, getProcInputClk) :: (List.map (fun mproc => (nil, mproc)) mprocs).

  Fixpoint combineIps (inits: list InitState) (procs: list Process): IPS :=
    match procs with
    | proc :: tprocs => match inits with
                        | init :: tinits => (init, proc) :: (combineIps tinits tprocs)
                        | nil => List.map (fun proc => (nil, proc)) procs
                        end
    | nil => nil
    end.

  Definition ipsFlops (flops: list InitState): IPS :=
    (nil, getProcInputClk) :: (combineIps flops mprocs).

  Definition ipsAll (inputs: InitState) (flops: list InitState): IPS :=
    (inputs, getProcInputClk) :: (combineIps flops mprocs).

  Definition TrsF (ins: InitState) (flops nflops: list InitState): Prop :=
    exists stf, TrsProcsRep decls funcs mtrss procs (initState (ipsAll ins flops)) stf (initState (ipsFlops nflops)).

  Definition StateOf (ins: InitState) (flops: list InitState) (stf: State): Prop :=
    exists nflops, TrsProcsRep decls funcs mtrss procs (initState (ipsAll ins flops)) stf nflops.

  Definition TrsI (st0 st1: State) (inputs: InitState): Prop :=
    ExecTimeSlot decls funcs mtrss procs st0 (inputsR procs inputs) (nilR procs) st1.

  Definition TrsC (st0 st1: State) (flops: list InitState): Prop :=
    ExecTimeSlot decls funcs mtrss procs st0 (flopsR flops) (nilR procs) st1.

  Definition IpsInputsMono :=
    forall ins0 flops ug0 st0,
      EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsAll ins0 flops)) [] ug0 st0 ->
      forall ins1 st1,
        (exists ug1, EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsAll ins1 flops)) [] ug1 st1) <->
          (exists ugi, EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsIns ins1)) st0 ugi st1).

  Definition IpsFlopsMono :=
    forall ins flops0 ug0 st0,
      EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsAll ins flops0)) [] ug0 st0 ->
      forall flops1 st1,
        (exists ug1, EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsAll ins flops1)) [] ug1 st1) <->
          (exists ugi, EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsFlops flops1)) st0 ugi st1).

  Definition IpsTrsVars :=
    forall ins flops st ugf stf,
      EvalUGraphTrs (getUGraph decls funcs mtrss false (ipsAll ins flops)) st ugf stf ->
      forall stu,
        HMapStrKeysWf (hupds stf stu) vars.

  Definition IpsGetUGraphWf :=
    forall ins flops,
      HMapStrEmptyWf (initState (ipsAll ins flops)) /\
      GetUGraphWf decls funcs mtrss (ipsAll ins flops).

  Definition TrsCFlopsConst: Prop :=
    forall ins flops0 stf0,
      StateOf ins flops0 stf0 ->
      forall stf1 flops1,
        TrsC stf0 stf1 flops1 ->
        StateOf ins flops1 stf1 ->
        TrsF ins flops0 flops1.

  Lemma std_ipsIns_procs:
    forall ins, List.map snd (ipsIns ins) = procs.
  Proof using All.
    unfold procs; simpl; intros.
    f_equal.
    clear; induction mprocs; [reflexivity|simpl; congruence].
  Qed.

  Lemma std_ipsFlops_procs:
    forall flops, List.map snd (ipsFlops flops) = procs.
  Proof using All.
    unfold ipsFlops, procs; simpl; intros.
    f_equal.
    generalize dependent flops.
    induction mprocs; intros.
    - destruct flops; reflexivity.
    - destruct flops; simpl.
      + f_equal; clear.
        induction p; [reflexivity|simpl; congruence].
      + congruence.
  Qed.

  Lemma std_ipsAll_procs:
    forall ins flops, List.map snd (ipsAll ins flops) = procs.
  Proof using All.
    unfold ipsAll, procs; simpl; intros.
    f_equal.
    generalize dependent flops.
    induction mprocs; intros.
    - destruct flops; reflexivity.
    - destruct flops; simpl.
      + f_equal; clear.
        induction p; [reflexivity|simpl; congruence].
      + congruence.
  Qed.

  Hypotheses (HstdOk: StdOk decls funcs mtrss procs)
    (HprocsOk: ProcsOk decls funcs mtrss procs)
    (HugOk: UGraphOk decls funcs mtrss).

  Hypotheses (HugIMono: IpsInputsMono) (HugFMono: IpsFlopsMono)
    (HugVars: IpsTrsVars) (HugWf: IpsGetUGraphWf)
    (HflopsC: TrsCFlopsConst).

  Section TrsIEquiv.
    Variable flops: list InitState.
    Hypotheses (Hflops: List.length flops = List.length mprocs).

    Lemma stf_implies_TrsI:
      forall ins0 stf0,
        StateOf ins0 flops stf0 ->
        forall ins1 stf1,
          StateOf ins1 flops stf1 ->
          TrsI stf0 stf1 ins1.
    Proof using All.
      unfold StateOf; intros.
      destruct H3 as [nflops0 ?].
      destruct H4 as [nflops1 ?].

      (** Apply TrsF-to-UGraph *)
      replace procs with (List.map snd (ipsAll ins1 flops)) in H4
          by apply std_ipsAll_procs.
      simple apply TrsProcsRep_imp_EvalUGraphTrs with (stb:= HMapEmpty) in H4.
      all: try (apply HugOk; fail).
      all: try (rewrite std_ipsAll_procs by assumption; apply HprocsOk; fail).
      3: apply HugWf; fail.
      2: (replace (initState (ipsAll ins1 flops)) with (hupds [] (initState (ipsAll ins1 flops))) by reflexivity;
          apply HugOk).
      destruct H4 as [ug1 [? [? ?]]].
      apply HugWf in H4.
      replace (hupds [] stf1) with stf1 in H4 by reflexivity.

      replace procs with (List.map snd (ipsAll ins0 flops)) in H3
          by apply std_ipsAll_procs.
      simple apply TrsProcsRep_imp_EvalUGraphTrs with (stb:= HMapEmpty) in H3.
      all: try (apply HugOk; fail).
      all: try (rewrite std_ipsAll_procs by assumption; apply HprocsOk; fail).
      3: apply HugWf; fail.
      2: (replace (initState (ipsAll ins0 flops)) with (hupds [] (initState (ipsAll ins0 flops))) by reflexivity;
          apply HugOk).
      destruct H3 as [ug0 [? [? ?]]].
      apply HugWf in H3.
      replace (hupds [] stf0) with stf0 in H3 by reflexivity.

      (** Fill the updates gap between [ins1] and [ins1 U flops] *)
      assert (EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsAll ins0 flops)) [] ug0 stf0)
        as Hugi by (repeat split; assumption).
      apply HugIMono in Hugi.
      assert (exists ug1, EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsAll ins1 flops)) [] ug1 stf1)
        as Hmono by (eexists; repeat split; eassumption).
      specialize (Hugi ins1 stf1).
      destruct Hugi as [Hugi _].
      specialize (Hugi Hmono); clear Hmono.
      destruct Hugi as [ugi Hugi].

      (** Apply UGraph-to-TrsI *)
      unfold TrsI.
      replace (inputsR procs ins1) with (initsR (List.map fst (ipsIns ins1))).
      2: { unfold inputsR; simpl.
           f_equal.
           clear; induction mprocs; [reflexivity|simpl; congruence]. }
      replace procs with (List.map snd (ipsIns ins1)).
      2: { simpl; unfold procs.
           f_equal.
           clear; induction mprocs; [reflexivity|simpl; congruence]. }
      eapply EvalUGraphTrs_imp_TrsStdI with (ug2:= ugi).

      all: try (apply HugOk; fail).
      - discriminate.
      - rewrite std_ipsIns_procs; apply HprocsOk.
      - rewrite std_ipsIns_procs; apply HstdOk.
      - replace stf0 with (hupds stf0 []) by apply hupds_empty.
        eapply HugOk; [eassumption|].
        rewrite std_ipsAll_procs, std_ipsIns_procs.
        reflexivity.
      - replace stf0 with (hupds stf0 []) by apply hupds_empty.
        eapply HugVars; eassumption.
      - assumption.
      - rewrite std_ipsIns_procs; apply HstdOk.
    Qed.

    Lemma TrsI_implies_stf:
      forall ins0 stf0,
        StateOf ins0 flops stf0 ->
        forall ins1 stf1,
          TrsI stf0 stf1 ins1 ->
          StateOf ins1 flops stf1.
    Proof using All.
      unfold StateOf; intros.
      destruct H3 as [nflops ?].
      pose proof H3 as Hbase.
      apply HprocsOk in Hbase.

      (** Apply TrsI-to-UGraph *)
      unfold TrsI in H4.
      replace (inputsR procs ins1) with (initsR (List.map fst (ipsIns ins1))) in H4.
      2: { unfold inputsR; simpl.
           f_equal.
           clear; induction mprocs; [reflexivity|simpl; congruence]. }
      replace procs with (List.map snd (ipsIns ins1)) in H4.
      2: { simpl; unfold procs.
           f_equal.
           clear; induction mprocs; [reflexivity|simpl; congruence]. }
      apply TrsStdI_imp_EvalUGraphTrs in H4.
      all: try (apply HugOk; fail).
      all: try rewrite !std_ipsIns_procs; try assumption.
      2: discriminate.
      destruct H4 as [ug1 [? ?]].

      (** Apply TrsF-to-UGraph *)
      replace procs with (List.map snd (ipsAll ins0 flops)) in H3
          by apply std_ipsAll_procs.
      simple apply TrsProcsRep_imp_EvalUGraphTrs with (stb:= HMapEmpty) in H3.
      all: try (apply HugOk; fail).
      all: try (rewrite std_ipsAll_procs by assumption; apply HprocsOk; fail).
      3: apply HugWf.
      destruct H3 as [ug0 [? [? ?]]].
      apply HugWf in H3.
      replace (hupds [] stf0) with stf0 in H3 by reflexivity.

      (** Fill the updates gap between [ins1] and [ins1 U flops] *)
      assert (EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsAll ins0 flops)) [] ug0 stf0)
        as Hugi by (repeat split; assumption).
      apply HugIMono in Hugi.
      assert (exists ugi, EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsIns ins1)) stf0 ugi stf1)
        as Hmono by (eexists; repeat split; try eassumption;
                     eapply HugOk; eassumption).
      specialize (Hugi ins1 stf1).
      destruct Hugi as [_ Hugi].
      specialize (Hugi Hmono); clear Hmono.
      destruct Hugi as [ugi Hugi].
      assert (EvalUGraphTrsFp (getUGraph decls funcs mtrss true (ipsAll ins1 flops))
                (initState (ipsAll ins1 flops)) ugi stf1) as Hugif.
      { destruct Hugi as [? [? ?]].
        repeat split; try assumption.
        apply HugWf in H8; assumption.
      }
      clear Hugi.

      (** Apply UGraph-to-TrsF *)
      replace procs with (List.map snd (ipsAll ins1 flops))
        by apply std_ipsAll_procs.
      eapply EvalUGraphTrs_imp_TrsProcsRep with (stb:= stf0) (ug2:= ugi) in Hugif.
      all: try (apply HugOk; fail).
      all: try rewrite !std_ipsAll_procs in *; try apply HprocsOk; try assumption.
      - destruct Hugif as [tstf [tflops [? ?]]].
        specialize (Hbase _ _ _ H8).
        rewrite Hbase in H9; subst tstf.
        eexists; eassumption.
      - replace (initState (ipsAll ins1 flops)) with (hupds [] (initState (ipsAll ins1 flops))) by reflexivity.
        apply HugOk.
      - apply HugWf.
      - eapply HugOk; [eassumption|].
        rewrite !std_ipsAll_procs.
        reflexivity.
      - eapply HugVars; eassumption.
      - eapply HugOk; eassumption.
      - replace (initState (ipsAll ins0 flops)) with (hupds [] (initState (ipsAll ins0 flops))) by reflexivity.
        apply HugOk.
      - apply HstdOk.
    Qed.

  End TrsIEquiv.

  Section TrsCEquiv.
    Variables (ins: InitState)
      (flops0 flops1: list InitState).
    Hypotheses
      (Hflops0: List.length flops0 = List.length mprocs)
      (Hflops1: List.length flops1 = List.length mprocs).

    Lemma stf_implies_TrsC:
      forall stf0,
        StateOf ins flops0 stf0 ->
        forall stf1,
          StateOf ins flops1 stf1 ->
          TrsF ins flops0 flops1 ->
          TrsC stf0 stf1 flops1.
    Proof using All.
      unfold StateOf, TrsF; intros.
      destruct H3 as [nflops0 ?].
      destruct H4 as [nflops1 ?].
      destruct H5 as [fstf0 ?].
      pose proof (TrsProcsRep_det H3 H5).
      destruct H6; subst fstf0 nflops0.
      clear H5.

      (** Apply TrsF-to-UGraph *)
      replace procs with (List.map snd (ipsAll ins flops1)) in H4
          by apply std_ipsAll_procs.
      simple apply TrsProcsRep_imp_EvalUGraphTrs with (stb:= HMapEmpty) in H4.
      all: try (apply HugOk; fail).
      all: try (rewrite std_ipsAll_procs by assumption; apply HprocsOk; fail).
      3: apply HugWf.
      2: (replace (initState (ipsAll ins flops1)) with (hupds [] (initState (ipsAll ins flops1))) by reflexivity;
          apply HugOk).
      destruct H4 as [ug1 [? [? ?]]].
      apply HugWf in H4.
      replace (hupds [] stf1) with stf1 in H4 by reflexivity.

      replace procs with (List.map snd (ipsAll ins flops0)) in H3
          by apply std_ipsAll_procs.
      simple apply TrsProcsRep_imp_EvalUGraphTrs with (stb:= HMapEmpty) in H3.
      all: try (apply HugOk; fail).
      all: try (rewrite std_ipsAll_procs by assumption; apply HprocsOk; fail).
      3: apply HugWf.
      2: (replace (initState (ipsAll ins flops0)) with (hupds [] (initState (ipsAll ins flops0))) by reflexivity;
          apply HugOk).
      destruct H3 as [ug0 [? [? ?]]].
      apply HugWf in H3.
      replace (hupds [] stf0) with stf0 in H3 by reflexivity.

      (** Fill the updates gap between [flops1] and [ins U flops1] *)
      assert (EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsAll ins flops0)) [] ug0 stf0)
        as Hugi by (repeat split; assumption).
      apply HugFMono in Hugi.
      assert (exists ug1, EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsAll ins flops1)) [] ug1 stf1)
        as Hmono by (eexists; repeat split; eassumption).
      specialize (Hugi flops1 stf1).
      destruct Hugi as [Hugi _].
      specialize (Hugi Hmono); clear Hmono.
      destruct Hugi as [ugi Hugi].

      (** Apply UGraph-to-TrsC *)
      unfold TrsC.
      replace (flopsR flops1) with (initsR (List.map fst (ipsFlops flops1))).
      2: { unfold flopsR; simpl.
           f_equal.
           clear -Hflops1.
           generalize dependent mprocs; clear.
           induction flops1; intros.
           { destruct mprocs; [reflexivity|discriminate]. }
           { destruct mprocs; [discriminate|].
             simpl in Hflops1; inv Hflops1.
             simpl; rewrite IHl by assumption.
             reflexivity.
           }
      }
      replace procs with (List.map snd (ipsFlops flops1)).
      2: { simpl; unfold procs.
           f_equal.
           clear -Hflops1.
           generalize dependent flops1; clear.
           induction mprocs; intros.
           { destruct flops1; [reflexivity|discriminate]. }
           { destruct flops1; [discriminate|].
             simpl in Hflops1; inv Hflops1.
             simpl; rewrite IHp by assumption.
             reflexivity.
           }
      }
      eapply EvalUGraphTrs_imp_TrsStdI with (ug2:= ugi).

      all: try (apply HugOk; fail).
      - discriminate.
      - rewrite std_ipsFlops_procs; apply HprocsOk.
      - rewrite std_ipsFlops_procs; apply HstdOk.
      - replace stf0 with (hupds stf0 []) by apply hupds_empty.
        eapply HugOk; [eassumption|].
        rewrite std_ipsAll_procs, std_ipsFlops_procs.
        reflexivity.
      - replace stf0 with (hupds stf0 []) by apply hupds_empty.
        eapply HugVars; eassumption.
      - assumption.
      - rewrite std_ipsFlops_procs by assumption; apply HstdOk.
    Qed.

    Lemma TrsC_implies_stf:
      forall stf0,
        StateOf ins flops0 stf0 ->
        forall stf1,
          TrsC stf0 stf1 flops1 ->
          StateOf ins flops1 stf1.
    Proof using All.
      unfold StateOf; intros.
      destruct H3 as [nflops ?].
      pose proof H3 as Hbase.
      apply HprocsOk in Hbase.

      (** Apply TrsI-to-UGraph *)
      unfold TrsC in H4.
      replace (flopsR flops1) with (initsR (List.map fst (ipsFlops flops1))) in H4.
      2: { unfold flopsR; simpl.
           f_equal.
           clear -Hflops1.
           generalize dependent mprocs; clear.
           induction flops1; intros.
           { destruct mprocs; [reflexivity|discriminate]. }
           { destruct mprocs; [discriminate|].
             simpl in Hflops1; inv Hflops1.
             simpl; rewrite IHl by assumption.
             reflexivity.
           }
      }
      replace procs with (List.map snd (ipsFlops flops1)) in H4.
      2: { simpl; unfold procs.
           f_equal.
           clear -Hflops1.
           generalize dependent flops1; clear.
           induction mprocs; intros.
           { destruct flops1; [reflexivity|discriminate]. }
           { destruct flops1; [discriminate|].
             simpl in Hflops1; inv Hflops1.
             simpl; rewrite IHp by assumption.
             reflexivity.
           }
      }
      apply TrsStdI_imp_EvalUGraphTrs in H4.
      all: try (apply HugOk; fail).
      all: try rewrite !std_ipsFlops_procs; try assumption.
      2: discriminate.
      destruct H4 as [ug1 [? ?]].

      (** Apply TrsF-to-UGraph *)
      replace procs with (List.map snd (ipsAll ins flops0)) in H3
          by apply std_ipsAll_procs.
      simple apply TrsProcsRep_imp_EvalUGraphTrs with (stb:= HMapEmpty) in H3.
      all: try (apply HugOk; fail).
      all: try (rewrite std_ipsAll_procs by assumption; apply HprocsOk; fail).
      3: apply HugWf.
      destruct H3 as [ug0 [? [? ?]]].
      apply HugWf in H3.
      replace (hupds [] stf0) with stf0 in H3 by reflexivity.

      (** Fill the updates gap between [flops1] and [ins U flops1] *)
      assert (EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsAll ins flops0)) [] ug0 stf0)
        as Hugi by (repeat split; assumption).
      apply HugFMono in Hugi.
      assert (exists ugi, EvalUGraphTrsFp (getUGraph decls funcs mtrss false (ipsFlops flops1)) stf0 ugi stf1)
        as Hmono by (eexists; repeat split; try eassumption;
                     eapply HugOk; eassumption).
      specialize (Hugi flops1 stf1).
      destruct Hugi as [_ Hugi].
      specialize (Hugi Hmono); clear Hmono.
      destruct Hugi as [ugi Hugi].
      assert (EvalUGraphTrsFp (getUGraph decls funcs mtrss true (ipsAll ins flops1))
                (initState (ipsAll ins flops1)) ugi stf1) as Hugif.
      { destruct Hugi as [? [? ?]].
        repeat split; try assumption.
        apply HugWf in H8; assumption.
      }
      clear Hugi.

      (** Apply UGraph-to-TrsF *)
      replace procs with (List.map snd (ipsAll ins flops1))
        by apply std_ipsAll_procs.
      eapply EvalUGraphTrs_imp_TrsProcsRep with (stb:= stf0) (ug2:= ugi) in Hugif.
      all: try (apply HugOk; fail).
      all: try rewrite !std_ipsAll_procs in *; try apply HprocsOk; try assumption.
      - destruct Hugif as [tstf [tflops [? ?]]].
        specialize (Hbase _ _ _ H8).
        rewrite Hbase in H9; subst tstf.
        eexists; eassumption.
      - replace (initState (ipsAll ins flops1)) with (hupds [] (initState (ipsAll ins flops1))) by reflexivity.
        apply HugOk.
      - apply HugWf.
      - eapply HugOk; [eassumption|].
        rewrite !std_ipsAll_procs.
        reflexivity.
      - eapply HugVars; eassumption.
      - eapply HugOk; eassumption.
      - replace (initState (ipsAll ins flops0)) with (hupds [] (initState (ipsAll ins flops0))) by reflexivity.
        apply HugOk.
      - apply HstdOk.
    Qed.

  End TrsCEquiv.

  Variables (ins0 ins1: InitState)
    (flops0 flops1: list InitState).
  Hypotheses
    (Hflops0: List.length flops0 = List.length mprocs)
    (Hflops1: List.length flops1 = List.length mprocs).

  Theorem stf_implies_std:
    forall stf00,
      StateOf ins0 flops0 stf00 ->
      forall stf11,
        StateOf ins1 flops1 stf11 ->
        TrsF ins1 flops0 flops1 ->
        exists stf10, TrsI stf00 stf10 ins1 /\ TrsC stf10 stf11 flops1.
  Proof using All.
    intros.
    pose proof H5 as Hf.
    red in Hf; destruct Hf as [stf10 Hf].
    assert (StateOf ins1 flops0 stf10) as Hs by (eexists; eassumption).
    pose proof Hs as Hs2.
    apply stf_implies_TrsI
      with (ins0:= ins0) (stf0:= stf00) in Hs; [|assumption..].
    apply stf_implies_TrsC
      with (flops0:= flops0) (stf0:= stf10) in H4; [|eassumption..].
    eexists; split; eassumption.
  Qed.

  Theorem std_implies_stf:
    forall stf00,
      StateOf ins0 flops0 stf00 ->
      forall stf10,
        TrsI stf00 stf10 ins1 ->
        forall stf11,
          TrsC stf10 stf11 flops1 ->
          (StateOf ins1 flops1 stf11 /\ TrsF ins1 flops0 flops1).
  Proof using All.
    intros.
    assert (StateOf ins1 flops0 stf10) as Hst0.
    { eapply TrsI_implies_stf in H4; [..|eassumption]; eassumption. }
    assert (StateOf ins1 flops1 stf11) as Hst1.
    { eapply TrsC_implies_stf in H5; [..|eassumption]; eassumption. }
    split; [assumption|].
    eapply HflopsC; eassumption.
  Qed.

  Theorem stf_std_equiv:
    forall stf00,
      StateOf ins0 flops0 stf00 ->
      forall stf11,
        (StateOf ins1 flops1 stf11 /\ TrsF ins1 flops0 flops1) <->
        (exists stf10, TrsI stf00 stf10 ins1 /\ TrsC stf10 stf11 flops1).
  Proof using All.
    intros; split; intros.
    - destruct H4.
      apply stf_implies_std; assumption.
    - destruct H4 as [stf10 [? ?]].
      eapply std_implies_stf; eassumption.
  Qed.

End StfStd.
