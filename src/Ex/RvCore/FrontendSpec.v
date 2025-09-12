From Coq Require Import Lia.
Require Import Coq.ZArith.BinInt Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lib.Lib. Import SZNotations.

Require Import Ex.RvCore.Common Ex.RvCore.MemSpec Ex.RvCore.Frontend.


Module FrontendSpec.
  #[local] Existing Instance SZ_sz_ops.
  #[local] Existing Instance hmap_array_ops.

  Section Defs.
    Import Frontend Mem.ICacheA ICacheASpec.

    Inductive LastPcPosition (pc_f2d_vld pc_d2e_vld: bool) (i: nat) (* A counter representing how far the `last_pc` is from coming out. *) :=
    | LastPcPosition_None
        (VLD: pc_f2d_vld = false /\ pc_d2e_vld = false)
        (IND: i = 2%nat)
    | LastPcPosition_Fetch
        (VLD: pc_f2d_vld = true /\ pc_d2e_vld = false)
        (IND: i = 1%nat)
    | LastPcPosition_Decode
        (VLD: pc_d2e_vld = true)
        (IND: i = 0%nat)
    .

    #[local] Open Scope Z_scope.


    Definition get_rs1_sz inst_sz := szRange inst_sz 19 15.
    Definition get_rs2_sz inst_sz := szRange inst_sz 24 20.
    Definition get_rd_sz inst_sz := szRange inst_sz 11 7.

    Definition rf_to_be (e2w_vld wb_ld: bool) rdi_sz rdv_sz ld_result_sz rf: MemData :=
      if e2w_vld
        then
          let upd := (if wb_ld then ld_result_sz else rdv_sz) in
          MemData_update (szNorm rdi_sz) upd rf
        else rf.

    Definition d2e_consistent (imem_data prev_rf_data: MemData) (prev_e2w_vld prev_wb_ld: bool)
                              prev_rdi_sz prev_rdv_sz pc_d2e_sz inst_d2e_sz rsv1_sz rsv2_sz prev_ld_result_sz :=
      inst_d2e_sz = szCastV #{32,32,true} (MemData_get_with_div4 pc_d2e_sz imem_data) /\
        let next_rf := rf_to_be prev_e2w_vld prev_wb_ld prev_rdi_sz prev_rdv_sz prev_ld_result_sz prev_rf_data in
        let rs1_sz := get_rs1_sz inst_d2e_sz in
        let rs2_sz := get_rs2_sz inst_d2e_sz in
        rsv1_sz = (if szIsZero rs1_sz then #{0, 32, false} else szCastV #{32,32,true} (MemData_get rs1_sz next_rf)) /\
        rsv2_sz = (if szIsZero rs2_sz then #{0, 32, false} else szCastV #{32,32,true} (MemData_get rs2_sz next_rf))
      .


    Inductive IsFrontendFlops (imem_data prev_rf_data: MemData) (prev_e2w_vld prev_wb_ld: bool) (prev_rdi_sz prev_rdv_sz prev_ld_result_sz: SZ)
                              (last_pc: option SZ) (i: nat) (pc_d2e_vld: bool) (pc_d2e_sz: SZ) (flops: Frontend.Flops): Prop :=
    | mkIsFrontendFlops
      (pc_f2d_vld imem_has_buffer: bool)
      imem_buffered_addr_sz pc_f2d_sz (inst_f2d_sz inst_d2e_sz rsv1_sz rsv2_sz: SZ)
      imem_flops
      (* IsICacheAFlops (data: MemData) (has_buffered: bool) (buffered_addr_sz: SZ) buffered_ret_sz (flops: Flops) *)
      (IMEM_FLOPS: IsICacheAFlops imem_data imem_has_buffer imem_buffered_addr_sz inst_f2d_sz imem_flops) (* ICacheA's vld bit is always same as pc_f2d_vld. *)
      (FORMAT:
        flops =
          {| pc_f2d_v := pc_f2d_sz;
            pc_f2d_vld_v := #{Z.b2z pc_f2d_vld, 1, false};
            d2e_vld_v := #{Z.b2z pc_d2e_vld, 1, false};
            pc_d2e_v := pc_d2e_sz;
            inst_d2e_v := inst_d2e_sz;
            rsv1_v := rsv1_sz;
            rsv2_v := rsv2_sz;
            icache_a_v := imem_flops
        |})
      (F2D_PC: imem_has_buffer = pc_f2d_vld /\ imem_buffered_addr_sz = pc_f2d_sz)
      (D2E_CONSISTENT:
        pc_d2e_vld = true ->
        d2e_consistent imem_data prev_rf_data prev_e2w_vld prev_wb_ld prev_rdi_sz prev_rdv_sz pc_d2e_sz inst_d2e_sz rsv1_sz rsv2_sz prev_ld_result_sz)
      (LAST_PC: last_pc = if pc_d2e_vld then Some pc_d2e_sz
                          else if pc_f2d_vld then Some pc_f2d_sz
                          else None)
      (PROGRESS: LastPcPosition pc_f2d_vld pc_d2e_vld i)
      .
  End Defs.

  Section Spec.
    Import Ex.RvCore.Mem Lang.Semantics.
    Import Frontend.
    #[local] Transparent Frontend.trs_structured.
    #[local] Arguments Z.pow_pos : simpl never.
    #[local] Arguments Z.pow : simpl never.
    #[local] Arguments Z.shiftl : simpl never.
    #[local] Arguments Z.mul : simpl never.
    #[local] Arguments Z.eqb: simpl nomatch.
    #[local] Arguments szIsZero: simpl never.

    #[local] Open Scope bool_scope.
    #[local] Open Scope Z_scope.

    Lemma szIsZero_0 : szIsZero #{0, 1, false} = true.
    Proof. reflexivity. Qed.

    Lemma szIsZero_1 : szIsZero #{1, 1, false} = false.
    Proof. reflexivity. Qed.

    Definition update_flops (update: Updates) (flops: Flops): State :=
      (hupds (to_state flops) (update_to_state update)).

    Definition max_ind := 2%nat.

    Lemma frontend_trs_spec (imem_data prev_rf_data: MemData) (prev_e2w_vld prev_wb_ld: bool) (prev_rdi_sz prev_rdv_sz prev_ld_result_sz: SZ) (last_pc: option SZ) (i: nat) pc_d2e_vld pc_d2e_sz flops
                                (rst_n_v: SZ) pc_fetch_v rf_v d2e_rdy_v e2w_vld_v wb_ld_v rdi_sz rdv_sz flush_v
      (INV_FLOPS: IsFrontendFlops imem_data prev_rf_data prev_e2w_vld prev_wb_ld prev_rdi_sz prev_rdv_sz prev_ld_result_sz last_pc i pc_d2e_vld pc_d2e_sz flops)
      (RST: rst_n_v = #{1, 1, false})
      :
        exists (update: Updates) (frontend_req_rdy d2e_vld: bool) (inst_d2e_sz rsv1_sz rsv2_sz: SZ),
          let inputs := {|rst_n_v := rst_n_v;
                          pc_fetch_v := pc_fetch_v;
                          rf_v := rf_v;
                          d2e_rdy_v := d2e_rdy_v;
                          e2w_vld_v := e2w_vld_v;
                          wb_ld_v := wb_ld_v;
                          rdi_v := rdi_sz;
                          rdv_v := rdv_sz;
                          flush_v := flush_v;
                          |}  in
          Frontend.trs_structured inputs flops =
            (update,
            {|frontend_req_rdy_out := #{Z.b2z frontend_req_rdy, 1, false};
              d2e_vld_out := #{Z.b2z d2e_vld, 1, false};
              pc_d2e_out := pc_d2e_sz;
              inst_d2e_out := inst_d2e_sz;
              rsv1_out := rsv1_sz;
              rsv2_out := rsv2_sz;
            |}) /\
            d2e_vld = pc_d2e_vld /\
            (d2e_vld = true -> d2e_consistent imem_data prev_rf_data prev_e2w_vld prev_wb_ld prev_rdi_sz prev_rdv_sz pc_d2e_sz inst_d2e_sz rsv1_sz rsv2_sz prev_ld_result_sz /\
                               last_pc = Some pc_d2e_sz) /\
            (* The full spec below is available if the input is fully provided. *)
            (forall (rf_data: MemData) prev_ld_result_sz' (d2e_rdy e2w_vld wb_ld flush: bool) ,
              rf_v = MemData_to_harr rf_data ->
              d2e_rdy_v = #{Z.b2z d2e_rdy, 1, false} ->
              e2w_vld_v = #{Z.b2z e2w_vld, 1, false} ->
              wb_ld_v = #{Z.b2z wb_ld, 1, false} ->
              flush_v = #{Z.b2z flush, 1, false} ->
              forall (RF_UPD: rf_data = rf_to_be prev_e2w_vld prev_wb_ld prev_rdi_sz prev_rdv_sz prev_ld_result_sz prev_rf_data)
                (RD_COND: d2e_vld = true -> e2w_vld = true ->
                  szEquiv (get_rs1_sz inst_d2e_sz) rdi_sz = false /\
                  szEquiv (get_rs2_sz inst_d2e_sz) rdi_sz = false ),
                exists flops' (last_pc': option SZ) i' pc_d2e_vld' pc_d2e_sz',
                  update_flops update flops = to_state flops' /\
                  IsFrontendFlops imem_data rf_data e2w_vld wb_ld rdi_sz rdv_sz prev_ld_result_sz' last_pc' i' pc_d2e_vld' pc_d2e_sz' flops' /\
                  (if flush then
                    i' = max_ind /\ last_pc' = None
                  else
                    d2e_vld = true \/
                    (last_pc' = if (i =? max_ind)%nat then Some pc_fetch_v else last_pc) /\ (i' <= i)%nat /\ (e2w_vld = false -> (i' < i)%nat)
                  ) /\ (
                    (* For two consequent outputs, the former's rdv does not match with the latter's rs1/rs2. *)
                    d2e_vld = true -> pc_d2e_vld' = true -> d2e_rdy = true ->
                      let inst_d2e_sz' := szCastV #{32,32,true} (MemData_get_with_div4 pc_d2e_sz' imem_data) in
                        szEquiv (get_rs1_sz inst_d2e_sz') (get_rd_sz inst_d2e_sz) = false /\
                        szEquiv (get_rs2_sz inst_d2e_sz') (get_rd_sz inst_d2e_sz) = false
                  )
            ).
    Proof.
      destruct flops, INV_FLOPS. injection FORMAT; repeat intros ->; clear FORMAT. destruct F2D_PC as [-> ->]. subst rst_n_v.
      repeat eexists _. intros inputs; subst inputs.
      repeat ssplit.
      { (* transition *) cbn. reflexivity. }
      { (* d2e_vld *) reflexivity. }
      { (* d2e_consistent *)
        intros ->. split.
        - eapply D2E_CONSISTENT. reflexivity.
        - exact LAST_PC. }
      (* Full spec *)
      intros ??????. do 5 intros ->. intros ??.
      edestruct ICacheASpec.icacheA_trs_spec with (req_vld_sz := sznil) as (_ & _ & _ & _ & -> & -> & -> & _); [exact IMEM_FLOPS|reflexivity|].
      edestruct ICacheASpec.icacheA_trs_spec with (req_vld_sz := sznil) as (_ & _ & _ & _ & -> & -> & -> & _); [exact IMEM_FLOPS|reflexivity|].
      unfold szBEq, szBNEq.
      repeat (rewrite ?szBLOr_b2z, ?szBLAnd_b2z, ?szIsZero_b2z, ?Z.mod_1_l, ?szIsZero_0, ?szIsZero_1 by lia; cbn -[update_flops]).
      rewrite ?Bool.negb_involutive.

      edestruct ICacheASpec.icacheA_trs_spec as (imem_update & imem_req_rdy & t1 & t2 & -> & Ht1 & Ht2 & Hinst_f2d_z & Hcache); [exact IMEM_FLOPS|reflexivity|]; subst t1 t2.
      progress repeat (rewrite ?szBLOr_b2z, ?szBLAnd_b2z, ?szIsZero_b2z, ?Z.mod_1_l, ?szIsZero_0, ?szIsZero_1 by lia; cbn -[update_flops]).
      rewrite !Bool.negb_involutive.

      replace (szRange inst_f2d_sz (szNormS #{19,32,true}) (szNormS #{15,32,_}))
        with (get_rs1_sz inst_f2d_sz) in * by reflexivity. remember (get_rs1_sz inst_f2d_sz) as rs1_sz.
      replace (szRange inst_f2d_sz (szNormS #{24,32,true}) (szNormS #{20,32,_}))
        with (get_rs2_sz inst_f2d_sz) in * by reflexivity. remember (get_rs2_sz inst_f2d_sz) as rs2_sz.
      replace (szRange inst_d2e_sz (szNormS #{11,32,true}) (szNormS #{7,32,_}))
        with (get_rd_sz inst_d2e_sz) in * by reflexivity. remember (get_rd_sz inst_d2e_sz) as rd_d2e_sz.

      remember (pc_d2e_vld && (szEquiv rs1_sz rd_d2e_sz || szEquiv rs2_sz rd_d2e_sz) ||
           e2w_vld && wb_ld && (szEquiv rs1_sz rdi_sz || szEquiv rs2_sz rdi_sz)) as rd_stall eqn: Hrd_stall.
      remember (negb pc_d2e_vld || d2e_rdy) as d2e_avail eqn: Hd2e_avail.
      remember (d2e_avail && negb rd_stall) as f2d_rdy eqn: Hf2d_rdy.
      rewrite andb_diag in *.

      remember (pc_f2d_vld && f2d_rdy) as decode_now eqn: Hdecode_now.
      remember (imem_req_rdy && (negb pc_f2d_vld || f2d_rdy && pc_f2d_vld)) as fetch_now eqn: Hfetch_now.

      (* destruct icache's full spec. *)
      remember (negb pc_f2d_vld || f2d_rdy) as imem_req_vld eqn: Himem_req_vld.
      remember (f2d_rdy && pc_f2d_vld) as imem_resp_rdy eqn: Himem_resp_rdy.
      edestruct Hcache with (req_vld_b := imem_req_vld) (resp_rdy_b := imem_resp_rdy) as
            (imem_has_buffer' & _ & inst_f2d_sz' & imem_flops' & IMEM_UPD & Himem_req_rdy & Himem_has_buffer' & -> & IMEM_INV').
      { subst imem_req_vld imem_resp_rdy. destruct pc_f2d_vld, f2d_rdy; reflexivity. }
      { reflexivity. } { reflexivity. }

      eexists (ltac: (econstructor; shelve) : Flops); repeat eexists _. repeat ssplit.
      { (* update_flops *)
        cbn. replace (hupds _ (ICacheA.update_to_state imem_update)) with (ICacheASpec.update_flops imem_update imem_flops) by reflexivity.
        rewrite IMEM_UPD. reflexivity. }
      { (* INV *)
        assert (fetch_now = imem_req_vld && imem_req_rdy) as H.
        { subst fetch_now. destruct imem_req_rdy; simpl_bool; [|reflexivity].
          subst imem_req_vld imem_resp_rdy. destruct f2d_rdy, pc_f2d_vld; reflexivity. }
        clear Hfetch_now. rename H into Hfetch_now.

        econstructor.
        { (* IMEM_FLOPS *) exact IMEM_INV'. }
        { (* FORMAT *) f_equal.
          - (* pc_f2d_vld *) instantiate_cond_eq; first [ instantiate (1 := false); reflexivity | instantiate (1 := true); reflexivity ].
          - (* d2e_vld_v *) instantiate_cond_eq; first [ instantiate (1 := false); reflexivity | instantiate (1 := true); reflexivity ]. }
        { (* F2D_PC *) ssplit.
          { subst imem_has_buffer'. rewrite <- Hfetch_now.
            destruct flush; [reflexivity|]. destruct fetch_now; [reflexivity|]. cbn. destruct imem_resp_rdy, pc_f2d_vld; reflexivity. }
          { destruct flush; [reflexivity|]. cbn. rewrite <- Hfetch_now. destruct fetch_now; reflexivity. }
        }
        { (* D2E_CONSISTENT *)
          destruct flush; [discriminate 1|]. cbn.

          destruct decode_now.

          2: { cbn.
            destruct (if negb d2e_rdy then pc_d2e_vld else false) eqn: Hd2e_vld'; [intros _|discriminate 1].
            (* Case: The previous d2e token remains in place. *)
            assert (d2e_rdy = false /\ pc_d2e_vld = true) as [-> ->].
            { clear -Hd2e_vld'. destruct d2e_rdy, pc_d2e_vld; auto. }
            clear Hd2e_vld'.
            destruct D2E_CONSISTENT as (-> & -> & ->); [reflexivity|..].
            remember (MemData_get_with_div4 pc_d2e_sz imem_data) as inst_d2e_sz eqn: Hinst_d2e_z.
            rewrite <- RF_UPD.
            unfold d2e_consistent. repeat ssplit.
            - subst inst_d2e_sz. reflexivity.
            - destruct (szIsZero _); [reflexivity|]. unfold rf_to_be. f_equal.
              destruct e2w_vld; [|reflexivity].
              rewrite MemData_get_update_neq; [reflexivity|].
              clear -RD_COND. edestruct RD_COND as [? ?]; [reflexivity..|assumption].
            - destruct (szIsZero _); [reflexivity|]. unfold rf_to_be. f_equal.
              destruct e2w_vld; [|reflexivity].
              rewrite MemData_get_update_neq; [reflexivity|].
              clear -RD_COND. edestruct RD_COND as [? ?]; [reflexivity..|assumption].
          }

          intros _. clear D2E_CONSISTENT.
          assert (pc_f2d_vld = true /\ f2d_rdy = true) as [-> ->]; [|clear Hdecode_now].
          { clear -Hdecode_now. destruct pc_f2d_vld, f2d_rdy; auto. }
          assert (d2e_avail = true /\ rd_stall = false) as [-> ->]; [|clear Hf2d_rdy].
          { clear -Hf2d_rdy. destruct d2e_avail, rd_stall; auto. }
          symmetry in Hrd_stall. apply orb_false_elim in Hrd_stall as [_ NO_WB_STALL].

          subst rs1_sz rs2_sz. cbn -[szEquiv Z.eqb]. unfold d2e_consistent. repeat ssplit.

          - subst inst_f2d_sz. reflexivity.
          - (* rs1 *)
            destruct (szIsZero _); [reflexivity|]. unfold rf_to_be. f_equal.
            destruct ((e2w_vld && negb wb_ld && szEquiv (get_rs1_sz inst_f2d_sz) rdi_sz)) eqn: Hhas_bypass.
            + (* Has bypass *)
              assert (e2w_vld = true /\ wb_ld = false /\ szEquiv (get_rs1_sz inst_f2d_sz) rdi_sz = true) as (-> & -> & EQ).
              { clear -Hhas_bypass. destruct e2w_vld, wb_ld, (szEquiv _ _); auto. }
              cbn. rewrite MemData_get_update_eq; [reflexivity|exact EQ].
            + (* Doesn't have bypass. *)
              cbn. rewrite hbits_hselect_MemData_to_harr.
              destruct e2w_vld; [|reflexivity]. cbn in Hhas_bypass.
              destruct (szEquiv (get_rs1_sz inst_f2d_sz) rdi_sz) eqn: Hrs1_equiv.
              * exfalso. clear -Hhas_bypass NO_WB_STALL. simpl_bool. destruct wb_ld; discriminate.
              * rewrite MemData_get_update_neq; [reflexivity|exact Hrs1_equiv].
          - (* rs2 *)
            destruct (szIsZero _); [reflexivity|]. unfold rf_to_be. f_equal.
            destruct ((e2w_vld && negb wb_ld && szEquiv (get_rs2_sz inst_f2d_sz) rdi_sz)) eqn: Hhas_bypass.
            + (* Has bypass *)
              assert (e2w_vld = true /\ wb_ld = false /\ szEquiv (get_rs2_sz inst_f2d_sz) rdi_sz = true) as (-> & -> & EQ).
              { clear -Hhas_bypass. destruct e2w_vld, wb_ld, (szEquiv _ _); auto. }
              cbn. rewrite MemData_get_update_eq; [reflexivity|exact EQ].
            + (* Doesn't have bypass. *)
              cbn. rewrite hbits_hselect_MemData_to_harr.
              destruct e2w_vld; [|reflexivity]. cbn in Hhas_bypass.
              destruct (szEquiv (get_rs2_sz inst_f2d_sz) rdi_sz) eqn: Hrs2_equiv.
              * exfalso. clear -Hhas_bypass NO_WB_STALL. simpl_bool. destruct wb_ld; discriminate.
              * rewrite MemData_get_update_neq; [reflexivity|exact Hrs2_equiv].
        }
        { (* LAST_PC *) reflexivity. }
        { (* PROGRESS *)
          cbn.
          instantiate (1 := if (if negb flush then if negb decode_now then if negb d2e_rdy then pc_d2e_vld else false else true else false) then _
                            else if (if negb flush then if negb fetch_now then if negb imem_resp_rdy then pc_f2d_vld else false else true else false) then _
                            else _).
          destruct (if negb flush then if negb decode_now then if negb d2e_rdy then pc_d2e_vld else false else true else false).
          { apply LastPcPosition_Decode; reflexivity. }
          destruct (if negb flush then if negb fetch_now then if negb imem_resp_rdy then pc_f2d_vld else false else true else false).
          { apply LastPcPosition_Fetch; eauto. }
          { apply LastPcPosition_None; eauto. } }
        (* End Inv. *)
      }
      { (* Output conditions for progress guarantee *)
        destruct flush. { simpl. auto. }

        destruct PROGRESS.
        { (* last_pc was none. *)
          right. subst decode_now fetch_now imem_req_rdy last_pc. destruct VLD as [-> ->]. rewrite IND.
          progress replace (if negb d2e_rdy then false else false) with false by (destruct d2e_rdy; reflexivity).
          repeat ssplit; try reflexivity; cbn; lia. }
        { (* last_pc was in fetch stage. *)
          right. subst last_pc. destruct VLD as [-> ->]. rewrite IND.
          progress replace (if negb d2e_rdy then false else false) with false by (destruct d2e_rdy; reflexivity).
          repeat ssplit; try reflexivity; cbn.
          - destruct decode_now; cbn.
            + reflexivity.
            + destruct f2d_rdy; [discriminate Hdecode_now|].
              subst fetch_now.
              assert (imem_resp_rdy = false) as ->. { subst imem_resp_rdy. reflexivity. } clear. simpl_bool. cbn. reflexivity.
          - cbn. destruct decode_now; simpl; [lia|]. destruct fetch_now; simpl; [lia|]. destruct imem_resp_rdy; simpl; [|lia].
            exfalso. clear -Hdecode_now Himem_resp_rdy. destruct f2d_rdy; discriminate.
          - cbn. intros ->. subst decode_now f2d_rdy rd_stall d2e_avail. cbn. lia. }
        { (* last_pc was in decode stage. *)
          left. cbn. subst i pc_d2e_vld last_pc. repeat ssplit; reflexivity. }
      }
      { (* Condition for two consequent outputs *)
        intros -> Hd2e_vld' ->. cbn in Hd2e_vld'.
        destruct flush; [discriminate Hd2e_vld'|]. destruct decode_now; [|discriminate Hd2e_vld']. clear Hd2e_vld'. cbn.
        symmetry in Hdecode_now. apply andb_prop in Hdecode_now as [-> ->].
        symmetry in Hf2d_rdy. apply andb_prop in Hf2d_rdy as [-> H]. destruct rd_stall; [discriminate H|].
        subst rs1_sz rs2_sz inst_f2d_sz. clear -Hrd_stall. cbn in Hrd_stall.
        symmetry in Hrd_stall. apply orb_false_elim in Hrd_stall as [NO_EX_STALL _].
        apply orb_false_iff in NO_EX_STALL. exact NO_EX_STALL.
      }
    Qed.

    #[global] Opaque max_ind.
  End Spec.
End FrontendSpec.
