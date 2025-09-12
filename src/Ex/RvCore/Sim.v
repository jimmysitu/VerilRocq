Require Import Coq.ZArith.BinInt Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.ModuleITree.
Require Import Lang.Lang.

Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms Coq.Classes.DecidableClass.
Require Import Coq.Program.Tactics.
From Coq Require Import Lia.
From ITree Require Import ITree ITreeFacts.
From FreeSim Require Import Tutorial SimGlobalIndex SimGlobalEquiv SimGlobalIndexFacts.
From Paco Require Import paco.
From Ordinal Require Import Ordinal Arithmetic ClassicalOrdinal.

Require Import Ex.RvCore.Common Ex.RvCore.Mem Ex.RvCore.MemSpec Ex.RvCore.Spec Ex.RvCore.Core Ex.RvCore.Frontend Ex.RvCore.FrontendSpec.

Import ListNotations.

#[local] Existing Instance SZ_sz_ops.
#[local] Existing Instance hmap_array_ops.

Definition Inputs := State.
Definition Outputs := State.


Section AbsFuncs.
  Variables (ldvf pcf execf: State -> SZ).

  Section Specification.

    Definition outputValid (o: Outputs): bool :=
      match (pc_commit_vld_v <- sfind pc_commit_vld o;
            Sret pc_commit_vld_v) with
      | Sret pc_commit_vld_v => negb (szIsZero (hbits pc_commit_vld_v))
      | Fail _ => false
      end.
    Definition fixed_input := HMapStr ((rst_n, HMapBits #{1, 1, false}) :: nil).

      Section SpecTree.
        Variable (imem_data: MemData).

        Definition spec_transition: ModuleITree.Transition := trsT (Spec.mtrs_abs_funcs ldvf pcf execf).(mtrs_func).

        Definition spec_initial_state  := Spec.rstS (MemData_to_harr imem_data).

        Definition spec_itree_from_state state :=
          filter_io fixed_input outputValid (module_itree spec_transition state).

        Definition spec_itree := spec_itree_from_state spec_initial_state.
      End SpecTree.

      Section CoreTree.
        Variable (btbf: State -> Z) (imem_data: MemData).

        Definition core_transition: ModuleITree.Transition := trsT ((Core.mtrs_abs_funcs ldvf pcf execf btbf).(mtrs_func)).

        Definition core_initial_state: State := Core.rstS btbf (MemData_to_harr imem_data).

        Definition core_itree_from_state state :=
          filter_io fixed_input outputValid (module_itree core_transition state).
        Definition core_itree := core_itree_from_state core_initial_state.
      End CoreTree.

    Definition core_ok: Prop
      := forall btbf imem_data, spec_itree imem_data ⪸ core_itree btbf imem_data.
  End Specification.

  Section Helpers.
    Variable (imem_data: MemData).
    Import Core.Core Spec.Spec MemSpec.ICacheASpec FrontendSpec.FrontendSpec.

    Definition dmemLdval (wb_ld_ty_sz: SZ) (dmem_resp_sz: SZ): SZ :=
      ldvf (HMapStr ((funct3, HMapBits wb_ld_ty_sz)
                      :: (dmem_resp, HMapBits dmem_resp_sz)
                      :: nil)).


    Inductive pc_prediction_status (e2w_vld: bool) (last_pc: option SZ) (pc_fetch_sz spec_pc_sz: SZ) (token frontend_i: nat): Prop :=
    | pc_prediction_status_normal
        (IND: token = (FrontendSpec.max_ind + frontend_i + (if e2w_vld then 1 else 0) + 2)%nat)
    | pc_prediction_status_mispredicted (* pc misprediction just happened. *)
        (IND: token = (FrontendSpec.max_ind + 1)%nat)
        (FD_IND: frontend_i = FrontendSpec.max_ind%nat)
        (PC: last_pc = None /\ pc_fetch_sz = spec_pc_sz)
        (E2W: e2w_vld = false)
    | pc_prediction_status_recovery (* State during misprediction recovery. Frontend contains the correct pc. *)
        (IND: token = frontend_i)
        (IND_LT_MAX: (frontend_i < FrontendSpec.max_ind)%nat)
        (PC: last_pc = Some spec_pc_sz)
        (E2W: e2w_vld = false).

    Inductive sim (cs: State) (ss: State) (token: nat): Prop :=
    | mkSim
      e2w_vld pc_fetch_sz core_pc_exec_sz rdi_sz rdv_sz wb_ld wb_ld_ty_sz dmem_resp_vld dmem_resp_sz core_dmem_v core_rf frontend_flops
      prev_rf_data prev_e2w_vld prev_wb_ld prev_rdi_sz prev_rdv_sz last_pc frontend_i pc_d2e_vld pc_d2e_sz prev_ld_result_sz
      spec_pc_sz spec_rf spec_dmem_v
      (CS_FORMAT:
        cs = to_state {|Core.e2w_vld_v := #{Z.b2z e2w_vld, 1, false};
                        Core.pc_fetch_v := pc_fetch_sz;
                        Core.pc_exec_v := core_pc_exec_sz;
                        Core.rdi_v := rdi_sz;
                        Core.rdv_v := rdv_sz;
                        Core.wb_ld_v := #{Z.b2z wb_ld, 1, false};
                        Core.wb_ld_ty_v := wb_ld_ty_sz;
                        Core.dcache_a_v := {|
                          DCacheA.dmem_v := MemData_to_harr core_dmem_v;
                          DCacheA.int_resp_vld_v := #{Z.b2z dmem_resp_vld, 1, false};
                          DCacheA.int_resp_v := dmem_resp_sz
                        |};
                        Core.rf_v := MemData_to_harr core_rf;
                        Core.frontend_v := frontend_flops;
                        Core.btb_v := tt;
                        |}
      )
      (SS_FORMAT:  ss = to_state {|
          pc_v := spec_pc_sz;
          rf_v := MemData_to_harr spec_rf;
          icache_v := {| ICache.imem_v := MemData_to_harr imem_data |};
          dcache_v := {| DCache.dmem_v := MemData_to_harr spec_dmem_v |}
        |}
      )
      (INV_FRONTEND: IsFrontendFlops imem_data prev_rf_data prev_e2w_vld prev_wb_ld prev_rdi_sz prev_rdv_sz prev_ld_result_sz last_pc frontend_i pc_d2e_vld pc_d2e_sz frontend_flops)
      (SIM_PC: spec_pc_sz = core_pc_exec_sz)
      (SIM_DMEM: core_dmem_v = spec_dmem_v)
      (SIM_RF:
        let ld_result_sz := dmemLdval wb_ld_ty_sz dmem_resp_sz in
        FrontendSpec.rf_to_be e2w_vld wb_ld rdi_sz rdv_sz ld_result_sz core_rf = spec_rf
      )
      (RD_STALL:
        pc_d2e_vld = true -> e2w_vld = true ->
          let inst_d2e_sz := szCastV #{32,32,true} (MemData_get_with_div4 pc_d2e_sz imem_data) in
          szEquiv (get_rs1_sz inst_d2e_sz) rdi_sz = false /\
          szEquiv (get_rs2_sz inst_d2e_sz) rdi_sz = false
      )
      (PROGRESS: pc_prediction_status e2w_vld last_pc pc_fetch_sz spec_pc_sz token frontend_i)
      (RF_UPD: core_rf = FrontendSpec.rf_to_be prev_e2w_vld prev_wb_ld prev_rdi_sz prev_rdv_sz prev_ld_result_sz prev_rf_data)
      .

    (* eutt helpers. *)
    #[local] Instance euttge_simg {E R}: Proper ((euttge eq) ==> (@euttge (E +' ModSemE.eventE) R R eq) ==> impl) ((⪸)).
    Proof.
      repeat intro. eapply Tutorial.eutt_simg.  1,2: eapply euttge_sub_eutt; eassumption. eauto.
    Qed.

    #[export] Instance gsimg_cong_euttge {E} r1 r2 R0 R1 RR f_src f_tgt :
      Proper ((euttge eq) ==> (euttge eq) ==> flip impl)
        (gpaco7 (_simg (E := E)) (cpn7 (_simg (E:=E))) r1 r2 R0 R1 RR f_src f_tgt).
    Proof.
      repeat intro. guclo euttC_spec. econstructor; eauto.
    Qed.

    #[local] Hint Rewrite @interp_tau : itree.
    #[local] Hint Rewrite @interp_mrec_bind : itree.
    #[local] Hint Rewrite @interp_mrec_trigger : itree.

    #[local] Hint Rewrite @ITreelib.interp_mrec_tau : itree.
    #[local] Hint Rewrite @ITreelib.interp_mrec_ret : itree.

    #[local] Definition simg {E R} := @SimGlobalIndex.simg E R R (fun _ _ => eq).
    #[local] Notation "('⪸)" := (simg) (at level 60).
    (* #[local] Notation "s '[' f_s '⪸ f_t ']' t" := (simg f_s f_t s t) (at level 60). *)

    #[local] Arguments Z.pow_pos : simpl never.
    #[local] Arguments Z.pow : simpl never.
    #[local] Arguments Z.shiftl : simpl never.
    #[local] Arguments Z.mul : simpl never.
    #[local] Arguments szIsZero: simpl never.
    #[local] Arguments szNorm: simpl never.

    #[local] Open Scope Z_scope.

    Lemma MemData_get_rf_to_be_neq rs e2w_vld wb_ld rdi rdv_sz inst_d2e_sz rf:
            (e2w_vld = true -> szEquiv rs rdi = false) ->
            MemData_get rs (rf_to_be e2w_vld wb_ld rdi rdv_sz inst_d2e_sz rf) = MemData_get rs rf.
    Proof.
      intros. unfold rf_to_be.
      destruct e2w_vld; [|reflexivity].
      rewrite MemData_get_update_neq; [reflexivity|]. auto.
    Qed.


    Lemma core_ok_aux src_state tgt_state token btbf:
      sim tgt_state src_state token ->
      simg token 0%nat (spec_itree_from_state src_state) (core_itree_from_state btbf tgt_state).
    Proof.
      unfold core_itree_from_state, spec_itree_from_state, module_itree, filter_io.

      (* Note: we cannot use rec_as_interp since it only guarantees ≈ when we need ≳ *)
      (* We instead unfold the definitions and work directly with interp_mrec. *)
      unfold rec, mrec.

      (* induction using gpaco. *)
      ginit. revert src_state tgt_state token.
      gcofix CIH.
      intros s1 t1 token SIM.
      destruct SIM. subst t1 core_pc_exec_sz core_dmem_v.
      destruct frontend_flops, icache_a_v.

      (* Start with symbolic execution of the target. *)
      (* We first hide the spec tree to prevent uninvented rewrites to the spec. *)
      remember (interp_mrec _ _) as spec eqn: Hspec.

      (* We then unfold core's transition step. *)
      unfold module_itree_body at 2.
      repeat (autorewrite with itree; cbn -[core_transition]).
      remember (module_itree_body (core_transition btbf)) as rec_core eqn: Hrec_core.
      unfold core_transition, fixed_input, trsT, trsNext.
      remember (mtrs_func _ _ _) as core_trs eqn: Hcore_trs.
      cbv [mtrs_func mtrsof_mtrs Core.mtrs_abs_funcs SZ_sz_ops hmap_array_ops] in Hcore_trs.

      set (I := from_state (A := Core.Inputs) _) in Hcore_trs.
      let I' := (eval cbv -[MemData_to_harr Z.b2z] in I) in replace I with I' in Hcore_trs by (cbv -[MemData_to_harr Z.b2z]; reflexivity). clear I.
      set (F := from_state (A := Core.Flops) _) in Hcore_trs.
      let F' := (eval cbv -[MemData_to_harr Z.b2z] in F) in replace F with F' in Hcore_trs by (cbv -[MemData_to_harr Z.b2z]; reflexivity). clear F.

      subst core_trs; cbv [fst snd].

      (* Apply frontend spec. *)
      edestruct frontend_trs_spec with (d2e_rdy_v := sznil) (flush_v := sznil) as (_ & _ & _ & inst_d2e_sz & rsv1_sz & rsv2_sz & -> & -> & D2E_CONSISTENT & _); [exact INV_FRONTEND|reflexivity|].
      edestruct frontend_trs_spec as (frontend_updates' & frontend_req_rdy' & d2e_vld' & inst_d2e_sz' & rsv1_sz' & rsv2_sz' & -> & -> & D2E_CONSISTENT' & Hfrontend);[exact INV_FRONTEND|reflexivity|].

      (* Simplify expressions. *)
      rewrite 2!hbits_hselect_MemData_to_harr.
      unfold szBEq, szBNEq, szUNot, szBLOr, szBLAnd in Hfrontend |- *.
      assert (forall b, szIsZero #{Z.b2z b, 1, false} = negb b) as szIsZero_b2z_wid1.
      { intros. eapply szIsZero_b2z. lia. }
      repeat ((rewrite ?szIsZero_b2z_wid1, ?szIsZero_0, ?szIsZero_1); cbn -[Z.eqb szEquiv]).
      rewrite ?szIsZero_b2z_wid1, ?szIsZero_0, ?szIsZero_1 in Hfrontend.
      simpl_bool.
      progress repeat replace (negb e2w_vld || e2w_vld)%bool with true in Hfrontend|- * by (destruct e2w_vld; reflexivity).
      simpl_bool.

      (* Simplify frontend updates. *)
      match goal with |- context [(frontend, ?S)] => replace S with (update_flops frontend_updates'
                                          {|
                                          Frontend.pc_f2d_v := pc_f2d_v;
                                          Frontend.pc_f2d_vld_v := pc_f2d_vld_v;
                                          Frontend.d2e_vld_v := d2e_vld_v;
                                          Frontend.pc_d2e_v := pc_d2e_v;
                                          Frontend.inst_d2e_v := inst_d2e_v;
                                          Frontend.rsv1_v := rsv1_v;
                                          Frontend.rsv2_v := rsv2_v;
                                          Frontend.icache_a_v :=
                                          {| ICacheA.imem_v := imem_v; ICacheA.int_resp_vld_v := int_resp_vld_v; ICacheA.int_resp_v := int_resp_v |}
                                          |}) by reflexivity end.

      (* Destruct full frontend spec. *)
      edestruct Hfrontend with (d2e_rdy := true) as
              (frontend_flops' & last_pc' & frontend_i' & pc_d2e_vld' & pc_d2e_sz' & FRONTEND_UPD & FRONTEND_INV' & FD_PROGRESS_UPD & RD_STALL').
      1-5: reflexivity.
      { (* RF_UPD *) rewrite RF_UPD. reflexivity. }
      { (* RD_COND *) intros -> ->. destruct D2E_CONSISTENT' as [(-> & -> & ->) _]; [reflexivity|]. apply RD_STALL; reflexivity. }
      rewrite FRONTEND_UPD.

      (* Remember important values. *)
      remember (pc_d2e_vld && szEquiv pc_d2e_sz spec_pc_sz)%bool as exec_ok eqn: Hexec_ok.
      remember (pc_d2e_vld && negb (szEquiv pc_d2e_sz spec_pc_sz))%bool as exec_bad eqn: Hexec_bad.
      match goal with |- context [(Common.e2w_vld, HMapBits #{Z.b2z ?a, _, _})] => remember a as e2w_vld' eqn: He2w_vld' end.
      match goal with |- context [(pc_fetch, HMapBits ?a)] => remember a as pc_fetch_sz' eqn: Hpc_fetch_sz' end.
      (* -- End of transition unfolding. -- *)

      match goal with |- context [Output ?a] => remember a as core_output eqn: Hcore_output end.
      match goal with |- context [call ?a] => remember a as core_state' eqn: Hcore_state' end.
      autorewrite with itree. cbn.


      (* To proceed further, we need to decide on the validness of the core's output. *)
      destruct exec_ok; cycle 1.

      - (* Stall in the exec stage. Core takes a tau step. *)
        subst core_output. cbn. autorewrite with itree; cbn. rewrite szIsZero_0. cbn.
        autorewrite with itree. rewrite unfold_interp_mrec.
        repeat (autorewrite with itree; cbn).

        (* Take a Tau step with FreeSim. *)
        guclo simg_indC_spec. econstructor; [eauto|]. instantiate (1 := 1%nat).

        rewrite <- interp_bind. rewrite <- interp_mrec_bind. rewrite bind_ret_r.

        (* It is enough to prove sim relation preservation & token decreasing. *)
        enough (exists token', sim core_state' s1 token' /\ (token' < token)%nat) as (token' & SIM' & LT).
        { gstep. econstructor 10 with (f_tgt0 := 0%nat).
          - gfinal. left. subst spec; eapply CIH. apply SIM'.
          - apply OrdArith.lt_from_nat, LT.
          - apply OrdArith.lt_from_nat. lia.
        }

        (* Assert progress first to prove pc_prediction_status updates and token decreasing together. *)
        assert (exists token', pc_prediction_status e2w_vld' last_pc' pc_fetch_sz' spec_pc_sz token' frontend_i' /\ (token' < token)%nat) as (token' & PROGRESS' & LT).
        { subst e2w_vld'. simpl. destruct exec_bad.
          - (* exec_bad is true. The pipeline starts misprediction recovery. *)
            destruct FD_PROGRESS_UPD as [-> ->].
            symmetry in Hexec_bad. apply andb_prop in Hexec_bad as [-> NEQ].
            specialize (D2E_CONSISTENT' eq_refl).
            destruct PROGRESS as [-> | -> -> [-> ->] -> | -> _ -> _].
            + eexists _. split.
              * eapply pc_prediction_status_mispredicted; auto.
              * clear. destruct e2w_vld; lia.
            + exfalso. destruct D2E_CONSISTENT' as [_ H]. discriminate H.
            + exfalso. clear -NEQ D2E_CONSISTENT'. destruct D2E_CONSISTENT' as [_ H]. injection H as ->.
              unfold szEquiv in NEQ. rewrite Z.eqb_refl in NEQ. discriminate NEQ.
          - (* exec_bad is false. Since exec_ok and exec_bad is both false, pc_d2e_vld should be false. *)
            assert (pc_d2e_vld = false) as ->.
            { clear -Hexec_bad Hexec_ok. destruct pc_d2e_vld; [|reflexivity]. destruct (szEquiv pc_d2e_sz spec_pc_sz); discriminate. }
            match type of FD_PROGRESS_UPD with (false = true \/ ?a) => assert (FD_PROGRESS_UPD': a) by (destruct FD_PROGRESS_UPD as [H|H]; [discriminate H|exact H]) end.
            clear FD_PROGRESS_UPD. destruct FD_PROGRESS_UPD' as (-> & i'_LE & i'_LT).
            destruct PROGRESS as [-> | -> -> [-> ->] -> | -> i_LT_max -> ->].
            + eexists _. split.
              * eapply pc_prediction_status_normal. reflexivity.
              * clear -i'_LE i'_LT. destruct e2w_vld; lia.
            + eexists _. split.
              * eapply pc_prediction_status_recovery; try reflexivity. apply (i'_LT eq_refl).
              * clear -i'_LE. lia.
            + eexists _. split.
              * eapply pc_prediction_status_recovery; try reflexivity.
                { clear -i'_LT i_LT_max. lia. }
                { clear -i_LT_max. destruct (frontend_i =? max_ind)%nat eqn: H; [exfalso|reflexivity]. apply Nat.eqb_eq in H as ->. lia. }
              * exact (i'_LT eq_refl).
        }


        exists token'. split; [|exact LT]. clear LT.
        (* Prove that `sim` is preserved. *)
        subst core_state' e2w_vld'; econstructor.
        { (* CS_FORMAT *)
          cbv [to_state Core.flops_structured DCacheA.flops_structured].
          do 12 f_equal; instantiate_cond_eq; rewrite ?hbinUArr_MemData; reflexivity. }
        { (* SS_FORMAT  *) exact SS_FORMAT. }
        { (* INV_FRONTEND *) apply FRONTEND_INV'. }
        { (* SIM_PC *) simpl. reflexivity. }
        { (* SIM_DMEM *) simpl. reflexivity. }
        { (* SIM_RF *) rewrite <- SIM_RF. unfold rf_to_be. simpl. destruct e2w_vld, wb_ld; reflexivity. }
        { (* RD_STALL *) simpl. discriminate 2. }
        { (* PROGRESS *) exact PROGRESS'. }
        { (* RF_UPD *) simpl. unfold FrontendSpec.rf_to_be. destruct e2w_vld, wb_ld; try reflexivity. }
      - (* A step in the exec stage. Both trees take a step with the same output value. *)
        assert (pc_d2e_vld = true /\ szEquiv pc_d2e_sz spec_pc_sz = true) as [-> EQ] by (apply Bool.andb_true_eq in Hexec_ok as [<- <-]; auto). clear Hexec_ok.
        specialize (D2E_CONSISTENT' eq_refl) as [(-> & -> & ->) ->].
        specialize (D2E_CONSISTENT eq_refl) as [(-> & -> & ->) _].
        specialize (RD_STALL eq_refl). simpl in RD_STALL.
        unfold szEquiv in EQ. apply Z.eqb_eq in EQ.

        (* Let's now unfold the spec tree. *)
        subst spec.

        unfold module_itree_body at 2.
        remember (module_itree_body spec_transition) as rec_spec eqn: Hspec.
        repeat (autorewrite with itree; cbn -[spec_transition]). rewrite SS_FORMAT.

        unfold spec_transition, trsT, trsNext.
        remember (mtrs_func _ _ _) as spec_trs eqn: Hspec_trs.
        cbv [mtrs_func mtrsof_mtrs Spec.mtrs_abs_funcs SZ_sz_ops hmap_array_ops] in Hspec_trs.

        set (I := from_state (A := Spec.Inputs) _) in Hspec_trs.
        let I' := (eval cbv -[MemData_to_harr Z.b2z] in I) in replace I with I' in Hspec_trs by (cbv -[MemData_to_harr Z.b2z]; reflexivity). clear I.
        set (F := from_state (A := Spec.Flops) _) in Hspec_trs.
        let F' := (eval cbv -[MemData_to_harr Z.b2z] in F) in replace F with F' in Hspec_trs by (cbv -[MemData_to_harr Z.b2z]; reflexivity). clear F.

        subst spec_trs; cbv [fst snd].

        (* Simplify expressions. *)
        subst core_output.
        rewrite !hbits_hselect_MemData_to_harr.
        unfold szBEq, szBNEq, szUNot, szBLOr, szBLAnd.
        repeat ((rewrite ?szIsZero_b2z_wid1, ?szIsZero_0, ?szIsZero_1); cbn -[Z.eqb szEquiv]).
        simpl_bool.

        match goal with |- context [call ?a] => remember a as spec_state' eqn: Hspec_state' end.
        progress repeat (autorewrite with itree; cbn). replace (szIsZero #{1,1,false}) with false by reflexivity. cbn.

        (* It is enough to prove sim relation preservation *)
        enough (exists token', sim core_state' spec_state' token') as (token' & SIM').
        { clear -SIM' CIH.
          guclo simg_indC_spec. econstructor; eauto. intros _ _ _.
          rewrite !unfold_interp_mrec. cbn. rewrite !tau_euttge. repeat (autorewrite with itree; cbn).
          (* We use FreeSim's bind rule for the recursive call. *)
          guclo bindC_spec. econstructor.
          { gstep. econstructor 10.
            { gfinal; left. eapply CIH, SIM'. }
            all: eapply Ord.S_lt. }

          intros. rewrite -> SIM.
          repeat (autorewrite with itree; cbn). guclo simg_indC_spec. econstructor; eauto.
          all: eapply Ord.le_refl.
        }

        subst spec_state'.
        match goal with |- context [(pc, HMapBits ?a)] => remember a as spec_pc_sz' eqn: Hspec_pc_sz' end.
        subst core_state'.
        remember (MemData_get_with_div4 pc_d2e_sz imem_data) as inst_d2e_sz eqn: Hinst_d2e_sz in *.
        replace ((MemData_get (szRange spec_pc_sz _ _) imem_data)) with inst_d2e_sz in *.
        2: { subst inst_d2e_sz. unfold MemData_get_with_div4, szRange. rewrite EQ. reflexivity. }
        rewrite <- RF_UPD.
        replace (szRange (szCastV #{32,32,true} inst_d2e_sz) (szNorm #{19,32,true}) (szNorm #{15,32,_})) with (get_rs1_sz (szCastV #{32,32,true} inst_d2e_sz)) in * by reflexivity.
        replace (szRange (szCastV #{32,32,true} inst_d2e_sz) (szNorm #{24,32,true}) (szNorm #{20,32,_})) with (get_rs2_sz (szCastV #{32,32,true} inst_d2e_sz)) in * by reflexivity.
        simpl in SIM_RF. subst spec_rf.

        replace (MemData_get (get_rs1_sz (szCastV #{32,32,_} inst_d2e_sz)) core_rf) with (match hselectA (MemData_to_harr (rf_to_be e2w_vld wb_ld rdi_sz rdv_sz (dmemLdval wb_ld_ty_sz dmem_resp_sz) core_rf)) (szNorm (get_rs1_sz (szCastV #{32,32,false} inst_d2e_sz))) with
                | HMapBits b => b | _ => sznil end) in *.
        2: { rewrite hbits_hselect_MemData_to_harr. apply MemData_get_rf_to_be_neq. intros H. destruct (RD_STALL H) as [A _]. exact A. }

        replace (MemData_get (get_rs2_sz (szCastV #{32,32,_} inst_d2e_sz)) core_rf) with  (match hselectA (MemData_to_harr (rf_to_be e2w_vld wb_ld rdi_sz rdv_sz (dmemLdval wb_ld_ty_sz dmem_resp_sz) core_rf)) (szNorm (get_rs2_sz (szCastV #{32,32,false} inst_d2e_sz))) with
                | HMapBits b => b | _ => sznil end) in *.
        2: { rewrite hbits_hselect_MemData_to_harr. apply MemData_get_rf_to_be_neq. intros H. destruct (RD_STALL H) as [_ B]. apply B. }

        (* Assert progress first. *)
        assert (exists token', pc_prediction_status e2w_vld' last_pc' pc_fetch_sz' spec_pc_sz' token' frontend_i') as (token' & PROGRESS').
        { eexists _. eapply pc_prediction_status_normal. reflexivity. }

        eexists token'.

        econstructor.
        { (* CS_FORMAT *)
          cbv [to_state Core.flops_structured DCacheA.flops_structured].
          do 12 f_equal; instantiate_cond_eq; rewrite ?hbinUArr_MemData; reflexivity. }
        { (* SS_FORMAT  *) cbv [to_state Spec.flops_structured DCache.flops_structured].
          do 4 f_equal; instantiate_cond_eq; rewrite ?hbinUArr_MemData; reflexivity. }
        { (* INV_FRONTEND *) apply FRONTEND_INV'. }
        { (* SIM_PC *) subst spec_pc_sz'. replace (negb true) with false by reflexivity. clear -RD_STALL.
           repeat f_equal.
          - (* rsv1 *) destruct (szIsZero _); reflexivity.
          (* reflexivity. rewrite hbits_hselect_MemData_to_harr. f_equal.
            rewrite MemData_get_rf_to_be_neq. 2: { intros H. destruct (RD_STALL H) as [A _]. exact A. }
            reflexivity. *)
          - (* rsv2 *)
            destruct (szIsZero _); reflexivity.
         (* [reflexivity|]. rewrite hbits_hselect_MemData_to_harr. f_equal.
            rewrite MemData_get_rf_to_be_neq. 2: { intros H. destruct (RD_STALL H) as [_ B]. exact B. }
            reflexivity. } *) }
        { (* SIM_DMEM *) reflexivity. }
        { (* SIM_RF *) cbn. unfold rf_to_be. subst e2w_vld'.
          remember (szRange (szCastV #{32,32,true} inst_d2e_sz) (szNorm #{6,32,true}) (szNorm #{0,32,true})) as opcode_v_s eqn: Hopcode_v_s.
          dest_if; cycle 1.
          - (* rd_upd = false. *) cbn. destruct e2w_vld, wb_ld; reflexivity.
          - (* rd_upd = true. *)
            cbn. clear. destruct (szEquiv opcode_v_s #{3,7,false}).
            + cbn. repeat (dest_if; try discriminate; try reflexivity).
            + simpl_bool. cbn. destruct e2w_vld; repeat (dest_if; try discriminate; try reflexivity).
        }
        { (* RD_STALL *) subst e2w_vld'. intros -> ->. cbn. apply RD_STALL'; reflexivity. }
        { (* PROGRESS *) exact PROGRESS'. }
        { (* RF_UPD *) clear. unfold rf_to_be. destruct e2w_vld, wb_ld; reflexivity. }
    Qed.

  End Helpers.

  Theorem core_ok': core_ok.
  Proof using All.
    unfold core_ok. intros.
    unfold spec_itree, core_itree.
    remember (core_initial_state _ _ : hmap) as t. remember (spec_initial_state _ : hmap) as s.
    assert (exists tok, sim imem_data t s tok) as [tok Hsim]. {
      subst t s. unfold core_initial_state, spec_initial_state, Core.rstS, Spec.rstS, SZ_sz_ops, hmap_array_ops.
      eexists.
      pose (arr_init := [(0, #{0,32,false})] : MemData).
      econstructor 1 with (core_dmem_v := arr_init) (spec_dmem_v := arr_init) (core_rf := arr_init) (spec_rf := arr_init)
        (prev_e2w_vld := false)
        (frontend_flops := Frontend.Build_Flops _ _ _ _ _ _ _ (ICacheA.Build_Flops _ _ _)).
      - (* CS_FORMAT *) cbv [to_state Core.flops_structured DCacheA.flops_structured Frontend.flops_structured ICacheA.flops_structured].
        repeat f_equal; (first [ instantiate (1 := false); reflexivity | instantiate (1 := true); reflexivity ]).
      - (* SS_FORMAT *) reflexivity.
      - (* INV_FRONTEND *)
        econstructor 1 with (imem_has_buffer := false).
        + econstructor.
          * reflexivity.
          * exact I.
        + f_equal; first [ instantiate (1 := false); reflexivity | instantiate (1 := true); reflexivity ].
        + split; reflexivity.
        + discriminate 1.
        + reflexivity.
        + econstructor; eauto.
      -  (* SIM_PC *) reflexivity.
      - (* SIM_DMEM *) reflexivity.
      - (* SIM_RF *) reflexivity.
      - (* RD_STALL *) discriminate 1.
      - (* PROGRESS *) econstructor; reflexivity.
      - (* RF_UPD *) reflexivity.
      Unshelve.
      all: match goal with
      | |- bool => exact false
      | |- SZ => exact sznil
      end.
    }
    eapply simg_bot_flag_up. eapply core_ok_aux. exact Hsim.
  Qed.

End AbsFuncs.
