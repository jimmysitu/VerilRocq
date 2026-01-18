Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Lib.Lib. Import HMapNotations. Import SZNotations.
Require Import Lang.Syntax Lang.Analysis Lang.Semantics. Include SFMonadNotations.

Require Import UpdGraph Standard ProcUpdGraph TrsProc.

Set Implicit Arguments.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope hmap_scope.

Section Equivalence.
  Context `{sz_ops}.
  Context `{vid_ops}.
  Context `{array_ops hmap}.

  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Lemma UNodeSt_upd_other_no_effect:
    forall ug1 un ug2,
      UGraphUnique (ug1 ++ un :: ug2) ->
      UNodeKeysOk un ->
      forall oun,
        In oun ug1 \/ In oun ug2 ->
        forall ifw,
          HMapStrEmpty ifw ->
          HMapStrEmpty (updf un ifw) ->
          UNodeSt ifw oun ->
          UNodeSt (hupds ifw (updf un ifw)) oun.
  Proof using .
    intros.
    red in H8; dest.
    red; split; [assumption|].
    split; intros.
    - specialize (H9 H11 _ H12); intro Hx; elim H9.
      rewrite hupds_hfind in Hx by assumption.
      destruct (hfind [HEltVid v] ifw).
      + destruct (hfind [HEltVid v] (updf un ifw)); discriminate.
      + reflexivity.
    - specialize (H10 H11 _ H12).
      rewrite hupds_hfind by assumption.
      rewrite H10.
      destruct (hfind [HEltVid v] ifw).
      + destruct (hfind [HEltVid v] (updf un ifw)); discriminate.
      + admit.
    (*
      specialize (H4 ifw); destruct H4; [rewrite H4; reflexivity|].
      destruct H4 as [uvs [? ?]].
      rewrite H4; simpl.
      pose proof (haccessV_Some uvs v) as Hv; destruct Hv as [Hv _].
      destruct (haccessV uvs v); [|reflexivity].
      exfalso.
      specialize (Hv ltac:(discriminate)).
      rewrite <-H13 in Hv.
      destruct H5.
      + eapply UGraphUnique_false_left; [eassumption|..]; eassumption.
      + eapply UGraphUnique_false_right; [eassumption|..]; eassumption.
  Qed.
    *)
  Admitted.

  Lemma UGraphSt_upd:
    forall proc (HprocWf0: ProcWfExecUniq decls funcs mtrss proc)
           (HprocWf1: ProcWfExecSucc decls funcs mtrss proc)
           ifw (Hifw: HMapStrEmptyWf ifw)
           uifw nflops,
      trsProc decls funcs mtrss proc ifw = Sret (uifw, nflops) ->
      forall ug1 un ug2,
        UGraphUnique (ug1 ++ un :: ug2) ->
        UGraphSt ifw (ug1 ++ un :: ug2) ->
        UNodeProc decls funcs mtrss un proc ->
        UGraphSt (hupds ifw uifw)
          (ug1 ++ {| keys := keys un;
                    deps := deps un;
                    updOnce := true;
                    updDone := true;
                    updf := updf un |} :: ug2) /\
          HMapStrEmptyWf (hupds ifw uifw).
  Proof using .
    unfold UNodeProc; intros; dest.
    apply Forall_app in H5; dest; inv H10.
    assert (uifw = updf un ifw) by (rewrite H9, H3; reflexivity); subst uifw.
    pose proof (UNodeKeysOk_HMapStrEmpty H6 ifw) as Huifw.
    split.
    2: { apply HMapStrEmptyWf_hupds; [assumption|].
         specialize (HprocWf0 ifw); rewrite H3 in HprocWf0; assumption.
    }

    apply Forall_app; split; [|constructor].
    - apply Forall_forall; intros oun ?.
      eapply Forall_In in H5; [|eassumption].
      eapply UNodeSt_upd_other_no_effect; try eassumption.
      + left; assumption.
      + apply HMapStrEmptyWf_HMapStrEmpty; assumption.
    - red in H13; dest.
      red; split; [reflexivity|].
      split; intros; [|discriminate].
      rewrite hupds_hfind; [|apply HMapStrEmptyWf_HMapStrEmpty; assumption|assumption].

      (* use [UNodeKeysOk] *)
      specialize (H6 ifw); destruct H6.
      + exfalso.
        specialize (HprocWf1 ifw).
        rewrite H3 in HprocWf1; dest.
        elim H16; assumption.
      + destruct H6 as [uvs [? ?]].
        rewrite H6; simpl in *.
        rewrite H16 in H15.
        apply haccessV_Some in H15.
        destruct (haccessV uvs v).
        { destruct (haccessO ifw v); discriminate. }
        { elim H15; reflexivity. }
    - apply Forall_forall; intros oun ?.
      eapply Forall_In in H14; [|eassumption].
      eapply UNodeSt_upd_other_no_effect; try eassumption.
      + right; assumption.
      + apply HMapStrEmptyWf_HMapStrEmpty; assumption.
  Qed.

  Lemma unode_updated_hupds:
    forall un ifw,
      HMapStrEmptyWf ifw ->
      (forall v, In v (keys un) ->
                 hfind [HEltVid v] ifw = hfind [HEltVid v] (updf un ifw)) ->
      UNodeKeysOk un ->
      keys un <> nil ->
      hupds ifw (updf un ifw) = ifw.
  Proof using .
    unfold UNodeKeysOk; intros.
    specialize (H5 ifw); destruct H5;
      [rewrite H5; apply hupds_empty|].
    destruct H5 as [uvs [? ?]].
    rewrite H5 in *; clear H5.

    destruct ifw; try (exfalso; auto; fail).
    - exfalso.
      destruct (keys un) as [|k ?]; [elim H6; reflexivity|].
      destruct uvs as [|[uk uv] uvs]; [discriminate|].
      simpl in *; inv H7.
      specialize (H4 uk (or_introl eq_refl)).
      rewrite vid_eqb_refl in H4; discriminate.
    - rewrite H7 in H4.
      apply hupds_absorbed; assumption.
  Qed.

  Lemma getNode_Some_In:
    forall ug k un, getNode ug k = Some un -> In un ug /\ In k (keys un).
  Proof using .
    induction ug as [|un ug]; simpl; intros; [discriminate|].
    destruct (existsb _ _) eqn:Hk.
    - inv H3; split.
      + left; reflexivity.
      + apply existsb_exists in Hk; destruct Hk as [uk [? ?]].
        apply vid_eqb_eq in H4; subst uk.
        assumption.
    - specialize (IHug _ _ H3).
      intuition.
  Qed.

  Lemma trsProc_UGraphSt_upd:
    forall proc (Hproc: ProcWf decls funcs mtrss proc)
           ifw uifw nflops,
      trsProc decls funcs mtrss proc ifw = Sret (uifw, nflops) ->
      forall ug,
        UGraphUnique ug ->
        UGraphDepsOk ug ->
        UGraphSt ifw ug ->
        forall un,
          In un ug ->
          UNodeProc decls funcs mtrss un proc ->
          getDepsUpdDone ug (deps un) = true /\
            (deps un = []%list \/ getDepsUpdOnce ug (deps un) = true).
  Proof using .
    intros.
    destruct Hproc as [_ [Hproc _]]; specialize (Hproc ifw).
    rewrite H3 in Hproc; destruct Hproc as [Huifwe Hproc].
    simpl in Huifwe.

    (* reducing [UGraphDepsOk] *)
    eapply Forall_In in H5; [|eassumption].
    red in H5.

    (* reducing [UNodeProc] *)
    red in H8; dest.
    rewrite <-H10 in Hproc.
    clear H8 H9 H10.

    assert (forall dk, In dk (deps un) -> getUpdDone ug dk = true /\ getUpdOnce ug dk = true) as Hdt.
    { intros.
      eapply Forall_In in Hproc; [|eassumption].
      eapply Forall_In in H5; [|eassumption].
      unfold getUpdDone, getUpdOnce; destruct (getNode ug dk) eqn:Hdk; [|elim H5; reflexivity].
      apply getNode_Some_In in Hdk; dest.
      eapply Forall_In in H6; [|eassumption].
      red in H6; dest.
      rewrite H6.
      destruct (updDone u); [split; reflexivity|].
      specialize (H13 eq_refl _ H10).
      elim Hproc; assumption.
    }

    split.
    - rewrite getDepsUpdDone_existsb.
      apply Bool.negb_true_iff.
      apply existsb_false_forall.
      intros.
      specialize (Hdt _ H8); dest.
      rewrite H9; reflexivity.
    - rewrite getDepsUpdOnce_existsb.
      destruct (deps un) as [|dk ds].
      + left; reflexivity.
      + right; apply existsb_exists.
        exists dk; split; [left; reflexivity|].
        specialize (Hdt dk).
        apply Hdt; left; reflexivity.
  Qed.

  Section WithBase.
    Variable (stb: State).

    Lemma trsProc_imp_EvalUGraphTrs:
      forall proc gprocs (Hgprocs: Forall (ProcWf decls funcs mtrss) gprocs),
        In proc gprocs ->
        forall ifw (Hifw: HMapStrEmptyWf ifw) uifw nflops,
          trsProc decls funcs mtrss proc ifw = Sret (uifw, nflops) ->
          forall ug (Hupdf: UpdfSub ug ifw),
            UGraphDepsOk ug ->
            UGraphUnique ug ->
            UGraphProcs decls funcs mtrss ug gprocs ->
            UGraphSt ifw ug ->
            exists nug, EvalUGraphTrs ug (hupds stb ifw) nug (hupds stb (hupds ifw uifw)) /\
                          UGraphDepsOk nug /\
                          UGraphUnique nug /\
                          UGraphProcs decls funcs mtrss nug gprocs /\
                          UGraphSt (hupds ifw uifw) nug /\
                          HMapStrEmptyWf (hupds ifw uifw).
    Proof using .
      intros.
      apply List.in_split in H3; destruct H3 as [procs1 [procs2 ?]]; subst gprocs.
      pose proof H7 as Hup.
      apply Forall2_app_inv_r in H7; destruct H7 as [ug1 [ug2 [? [? ?]]]].
      destruct ug2 as [|un ug2]; inv H7.
      destruct (updDone un) eqn:Huu.

      - assert (hupds ifw uifw = ifw) as Hnupd.
        { replace uifw with (updf un ifw).
          { apply unode_updated_hupds; try assumption.
            { apply Forall_app in Hupdf; destruct Hupdf as [_ Hupdf].
              apply Forall_cons_iff in Hupdf; destruct Hupdf as [Hupdf _].
              apply Hupdf; assumption.
            }
            { apply H13. }
            { apply H13. }
          }
          { red in H13; dest.
            rewrite H11; simpl.
            rewrite H4.
            reflexivity.
          }
        }

        rewrite Hnupd.
        eexists; repeat split; [apply EvalUGraphId; fail|..]; assumption.

      - rewrite Forall_app in Hgprocs; destruct Hgprocs as [Hprocs1 Hprocs2]; inv Hprocs2.
        exists (ug1 ++ {| keys := keys un;
                         deps := deps un;
                         updOnce := true;
                         updDone := true;
                         updf := updf un |} :: ug2);
          repeat split.

        + (* [EvalUGraphTrs] *)
          assert (getDepsUpdDone (ug1 ++ un :: ug2) (deps un) = true) as Hud.
          { eapply trsProc_UGraphSt_upd; try eassumption.
            apply in_or_app; right; left; reflexivity.
          }
          apply EvalUGraphTrs_one.
          econstructor; [reflexivity| | |reflexivity|..].
          * eapply trsProc_UGraphSt_upd; try eassumption.
            apply in_or_app; right; left; reflexivity.
          * assumption.
          * rewrite Hud; reflexivity.
          * assert (updf un (hupds stb ifw) = uifw /\ HMapStrEmpty uifw) as Hupdb.
            { red in H13; dest.
              apply UNodeKeysOk_HMapStrEmpty with (st:= (hupds stb ifw)) in H7.
              rewrite H13 in *.
              red in H10; dest.
              rewrite H17 in *; [|eassumption..].
              split; [reflexivity|assumption].
            }

            destruct Hupdb.
            rewrite H7.
            apply hupds_assoc.
            { apply HMapStrEmptyWf_HMapStrEmpty; assumption. }
            { assumption. }
            { apply Forall_app in H8; dest; inv H12.
              red in H17.
              red in H13; dest.
              specialize (H13 (hupds stb ifw)).
              destruct H13.
              { rewrite H13 in *.
                red; intros.
                destruct ifw; auto.
              }
              { destruct H13 as [uvs [? ?]].
                rewrite H13 in *; rewrite H20 in *.
                red; intros.
                destruct ifw; try (exfalso; auto; fail); auto.
                intros.
                specialize (H14 Huu _ H22).
                simpl in H14.
                eapply haccessV_Some with (vs:= str) (k:= v); [assumption|].
                destruct (haccessV str v); [discriminate|assumption].
              }
            }

        + (* [UGraphDepsOk] *)
          eapply UGraphDepsOk_keys_equiv; [eassumption|..].
          all: rewrite !map_app; simpl; f_equal.

        + (* [UGraphUnique] *)
          eapply UGraphUnique_keys_equiv; [eassumption|].
          rewrite !map_app; simpl; f_equal.

        + (* [UGraphProcs] *)
          apply UGraphProcs_upd; assumption.

        + (* [UGraphSt] *)
          eapply UGraphSt_upd; try eassumption.
          all: apply H10.
        + eapply UGraphSt_upd; try eassumption.
          all: apply H10.
    Qed.

    Hypothesis (Hstb: UGraphBaseMono stb).

    Lemma trsProcs_imp_EvalUGraphTrs_ind:
      forall gprocs (Hgprocs: Forall (ProcWf decls funcs mtrss) gprocs) procs
             (Hpr: exists rprocs, gprocs = rprocs ++ procs)
             ifw (Hifw: HMapStrEmptyWf ifw)
             nifw flops nflops,
        trsProcs decls funcs mtrss procs (ifw, flops) = Sret (nifw, nflops) ->
        forall ug (Hupdf: UpdfSub ug ifw)
               (Hugk: UGraphKeysOk ug)
               (Hugu: UGraphUpdfOk ug),
          UGraphDepsOk ug ->
          UGraphUnique ug ->
          UGraphProcs decls funcs mtrss ug gprocs ->
          UGraphSt ifw ug ->
          exists nug, EvalUGraphTrs ug (hupds stb ifw) nug (hupds stb nifw) /\
                        UGraphDepsOk nug /\
                        UGraphUnique nug /\
                        UGraphProcs decls funcs mtrss nug gprocs /\
                        UGraphSt nifw nug /\
                        HMapStrEmptyWf nifw.
    Proof using All.
      induction procs as [|hproc tprocs]; simpl; intros.
      - inv H3.
        exists ug; repeat split; [|eassumption..].
        constructor.
      - assert (exists rprocs, gprocs = rprocs ++ tprocs) as Hri.
        { destruct Hpr as [rprocs ?]; subst gprocs.
          exists (rprocs ++ [hproc]).
          rewrite <-List.app_assoc; reflexivity.
        }
        specialize (IHtprocs Hri); clear Hri.
        destruct (trsProc decls funcs mtrss hproc ifw) as [[uifw uflops]|] eqn:Hproc;
          unfold iffupds in *; simpl in *.
        + eapply trsProc_imp_EvalUGraphTrs with (gprocs:= gprocs) in Hproc; try eassumption.
          * destruct Hproc as [uug [? [? [? [? [? ?]]]]]].
            assert (UpdfSub uug (hupds ifw uifw)) as Hupdfu.
            { eapply EvalUGraphTrs_UpdfSub; [..|eassumption|].
              all: try assumption.
              apply Hstb; assumption.
            }
            assert (UGraphKeysOk uug) as Hugku by (eapply EvalUGraphTrs_UGraphKeysOk; eassumption).
            assert (UGraphUpdfOk uug) as Huguu by (eapply EvalUGraphTrs_UGraphUpdfOk; eassumption).
            specialize (IHtprocs _ H13 _ _ _ H3 _ Hupdfu Hugku Huguu H9 H10 H11 H12).
            destruct IHtprocs as [nug [? [? [? [? [? ?]]]]]].
            exists nug; repeat split; [|assumption..].
            eapply EvalUGraphTrs_trs; eassumption.
          * dest; subst gprocs; apply in_or_app; right; left; reflexivity.
        + rewrite !hupds_empty in H3.
          eapply IHtprocs; eassumption.
    Qed.

  End WithBase.

  Section WithProcs.
    Variable ips: IPS.

    Local Notation procs := (List.map snd ips).

    Hypotheses (HprocsW: Forall (ProcWf decls funcs mtrss) procs)
      (HprocsU: ProcsWfUpd decls funcs mtrss procs)
      (HprocsD: ProcsWfDet decls funcs mtrss procs).

    Definition UNodeUpdComplFull (ug: ugraph) (un: unode) :=
      unodeUpdCompl ug un = true /\ updOnce un = updDone un.

    Definition UGraphUpdComplFull (ug: ugraph): Prop :=
      Forall (UNodeUpdComplFull ug) ug.

    Lemma fp_UGraphUpdComplFull:
      forall stf (Hstf: HMapStrEmptyWf stf) flops nflops,
        trsProcs decls funcs mtrss procs (stf, flops) = Sret (stf, nflops) ->
        forall ugf,
          UGraphProcs decls funcs mtrss ugf procs ->
          UGraphSt stf ugf ->
          UGraphUpdComplFull ugf.
    Proof using All.
      intros; red.
      apply Forall_forall.
      intros un ?.
      split.
      2: { red in H5; rewrite Forall_forall in H5; specialize (H5 _ H6).
           red in H5; dest; assumption.
      }

      unfold unodeUpdCompl.
      destruct (getDepsUpdDone ugf (deps un)) eqn:Hud; [simpl|reflexivity].
      destruct (updDone un) eqn:Hun; [reflexivity|exfalso].

      pose proof H5 as Hust.
      eapply Forall_In in H5; [|eassumption].
      red in H5; dest.
      specialize (H8 Hun).

      eapply Forall2_In_left in H4; [|eassumption].
      destruct H4 as [proc [? ?]].
      eapply trsProcs_fp_ind in H3; [|eassumption..].
      red in H9; dest.
      specialize (H12 stf).
      specialize (H9 stf).
      eapply Forall_In in HprocsW; [|eassumption].
      destruct HprocsW as [_ [? _]].
      specialize (H13 stf).

      destruct (trsProc decls funcs mtrss proc stf) as [[pifw pflops]|] eqn:Hp.
      - simpl in H12; subst pifw.
        destruct H9.
        + rewrite H9 in H13.
          destruct H13; elim H12; reflexivity.
        + destruct H9 as [uvs [? ?]].
          rewrite H9 in *.
          rewrite H12 in *.
          assert (forall v, hfind [HEltVid v] (hupds stf (HMapStr uvs)) =
                              match hfind [HEltVid v] (HMapStr uvs) with
                              | Some v0 => Some v0
                              | None => hfind [HEltVid v] stf
                              end) as Hmf
            by (apply hupds_hfind; [apply HMapStrEmptyWf_HMapStrEmpty; assumption|red; auto]).
          rewrite H3 in Hmf.
          destruct (map fst uvs) as [|uk uks] eqn:Hku; [elim H10; reflexivity|].
          specialize (H8 uk (or_introl eq_refl)).
          specialize (Hmf uk); rewrite H8 in Hmf.
          destruct uvs as [|[huk huv] uvs]; inv Hku; simpl in *.
          rewrite vid_eqb_refl in Hmf; discriminate.

      - destruct H13 as [dk [? ?]].
        rewrite <-H11 in H13.
        rewrite getDepsUpdDone_existsb in Hud.
        apply Bool.negb_true_iff in Hud.
        rewrite existsb_false_forall in Hud.
        specialize (Hud _ H13).
        apply Bool.negb_false_iff in Hud.
        unfold getUpdDone in Hud.
        destruct (getNode ugf dk) as [dun|] eqn:Hdn; [|discriminate].
        apply getNode_Some_In in Hdn; dest.

        eapply Forall_In in Hust; [|eassumption].
        red in Hust; dest.
        specialize (H18 Hud _ H16).
        elim H18; assumption.
    Qed.

    Lemma TrsProcsRep_imp_EvalUGraphTrs_ind:
      forall inits (Hinits: HMapStrEmptyWf inits) stf flops,
        TrsProcsRep decls funcs mtrss procs inits stf flops ->
        forall iug,
          UpdfSub iug inits ->
          UGraphKeysOk iug ->
          UGraphUpdfOk iug ->
          UGraphDepsOk iug ->
          UGraphUnique iug ->
          UGraphProcs decls funcs mtrss iug procs ->
          UGraphSt inits iug ->
          forall stb (Hstb: UGraphBaseMono stb),
          exists ugf,
            EvalUGraphTrs iug (hupds stb inits) ugf (hupds stb stf) /\
              UGraphUpdComplFull ugf.
    Proof using All.
      induction 2; simpl; intros; subst.
      - eapply trsProcs_imp_EvalUGraphTrs_ind with (gprocs:= procs) in H4; try eassumption.
        + destruct H4 as [nug [? [? [? [? [? ?]]]]]].
          assert (UpdfSub nug ifw1) as Hupdfu.
            { eapply EvalUGraphTrs_UpdfSub; [..|eassumption|].
              all: try assumption.
              apply Hstb; assumption.
            }
            assert (UGraphKeysOk nug) as Hugku by (eapply EvalUGraphTrs_UGraphKeysOk; eassumption).
            assert (UGraphUpdfOk nug) as Huguu by (eapply EvalUGraphTrs_UGraphUpdfOk; eassumption).
          specialize (IHTrsProcsRep H16 _ Hupdfu Hugku Huguu H12 H13 H14 H15 _ Hstb).
          destruct IHTrsProcsRep as [ugf [? ?]].
          eexists; split; [|eassumption].
          eapply EvalUGraphTrs_trs; eassumption.
        + exists nil; reflexivity.
      - exists iug; split; [constructor; fail|].
        eapply fp_UGraphUpdComplFull; eassumption.
    Qed.

    Definition ugMInitsU: ugraph := getUGraph decls funcs mtrss true ips.
    Local Notation initState := (initState ips).

    (** Initial conditions: all proven statically (syntactically) by the given processes. *)
    Hypotheses (Huu: UGraphUnique ugMInitsU)
      (Huk: UGraphKeysOk ugMInitsU)
      (Hud: UGraphDepsOk ugMInitsU)
      (Huf: UGraphUpdfOk ugMInitsU)
      (Hup: UGraphProcs decls funcs mtrss ugMInitsU procs)
      (Hus: UGraphSt initState ugMInitsU)
      (Hufs: UpdfSub ugMInitsU initState)
      (Hku: HMapStrEmptyWf initState).

    Theorem TrsProcsRep_imp_EvalUGraphTrs:
      forall stf flops,
        TrsProcsRep decls funcs mtrss procs initState stf flops ->
        forall stb (Hstb: UGraphBaseMono stb),
        exists ug2,
          EvalUGraphTrsFp ugMInitsU (hupds stb initState) ug2 (hupds stb stf).
    Proof using All.
      intros.
      eapply TrsProcsRep_imp_EvalUGraphTrs_ind with (stb:= stb) in H3;
        try eassumption.
      - destruct H3 as [ugf [? ?]].
        exists ugf; repeat split; try assumption.
        + apply Forall_forall; intros.
          red in H4; rewrite Forall_forall in H4; specialize (H4 _ H5).
          apply H4.
        + apply Forall_forall; intros.
          red in H4; rewrite Forall_forall in H4; specialize (H4 _ H5).
          apply H4.
    Qed.

    (** Additional conditions to ensure the other direction by confluence *)
    Variables (stb: State) (vars: list vid_t).
    Hypotheses (Hstwf: UGraphStWf (hupds stb initState) ugMInitsU)
      (Hvars: HMapStrKeysWf (hupds stb initState) vars)
      (Hum: UGraphBaseMono stb)
      (Hufsb: UpdfSub ugMInitsU (hupds stb initState)).

    Theorem EvalUGraphTrs_imp_TrsProcsRep_rel:
      forall ug2 stbf,
        EvalUGraphTrsFp ugMInitsU (hupds stb initState) ug2 (hupds stb stbf) ->
        forall pstf pflops,
          TrsProcsRep decls funcs mtrss procs initState pstf pflops ->
          hupds stb stbf = hupds stb pstf.
    Proof using All.
      unfold EvalUGraphTrsFp; intros; dest.
      simple apply TrsProcsRep_imp_EvalUGraphTrs with (stb:= stb) in H4; [|assumption].
      destruct H4 as [aug2 [? [? ?]]].
      eapply eval_ugraph_confl_state_eq_ind
        with (ug0:= ugMInitsU) (st0:= hupds stb initState)
             (ug1:= ug2) (ug2:= aug2); try eassumption.
    Qed.

    Theorem EvalUGraphTrs_imp_TrsProcsRep:
      forall pstf,
        hupds stb pstf = pstf ->
        forall ug2,
          EvalUGraphTrsFp ugMInitsU initState ug2 pstf ->
          TrsProcsRepProg decls funcs mtrss procs ->
          exists tstf tflops,
            TrsProcsRep decls funcs mtrss procs initState tstf tflops /\
              hupds stb tstf = pstf.
    Proof using All.
      intros.
      destruct H4 as [? [? ?]].
      eapply Hum in H4.
      specialize (H5 initState).
      destruct H5 as [tstf [pflops ?]].
      pose proof H5.
      eapply EvalUGraphTrs_imp_TrsProcsRep_rel with (stbf:= pstf) in H8.
      - do 2 eexists; split; [eassumption|].
        congruence.
      - repeat split; eassumption.
    Qed.

  End WithProcs.

End Equivalence.
