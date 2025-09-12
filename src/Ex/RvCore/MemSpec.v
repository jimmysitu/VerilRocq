Require Import Coq.ZArith.BinInt.
From Coq Require Import Lia.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lib.Lib. Import SZNotations.

Require Import Ex.RvCore.Common.
Require Import Ex.RvCore.Mem.

Import ListNotations.
#[local] Open Scope Z_scope.

#[local] Existing Instance SZ_sz_ops.
#[local] Existing Instance hmap_array_ops.

Definition MemData: Type := list (Z (* address *) * SZ (* value *)).

Definition MemData_to_harr (data: MemData): list (Z * hmap) :=
  List.map (fun x => (fst x, HMapBits (snd x))) data.

Definition MemData_get (addr: SZ) (data: MemData): SZ :=
  match List.find (fun x => szNorm addr =? fst x) data with
  | Some v => snd v
  | None => sznil
  end.

Definition MemData_get_with_div4 (addr: SZ) (data: MemData): SZ :=
  MemData_get (szRange addr 31 2) data.

Fixpoint MemData_merge_1 (mem1 mem2: MemData): MemData :=
match mem1 with
| [] => []
| (addr1, v1) :: mem1' => (addr1, match List.find (fun iv1 => addr1 =? (fst iv1)) mem2 with
                                        | Some iv1 => (snd iv1)
                                        | None => v1
                                        end) ::
                              (MemData_merge_1 mem1' mem2)
end.

Definition MemData_merge_2 (mem1 mem2: MemData): MemData :=
  List.filter (fun iv2 => negb (List.existsb (fun iv1 => (fst iv1 =? fst iv2)) mem1)) mem2.

Definition MemData_merge (mem1 mem2: MemData): MemData :=
  MemData_merge_1 mem1 mem2 ++ MemData_merge_2 mem1 mem2.

Definition MemData_update (i: Z) (v: SZ) (mem: MemData): MemData :=
  MemData_merge mem [(i, v)].

Lemma hbinUArr_MemData (mem: MemData) (i: Z) (v: SZ):
  hbinUArr hupds (MemData_to_harr mem) ([(i, HMapBits v)]) = MemData_to_harr (MemData_update i v mem).
Proof.
  unfold hbinUArr, MemData_to_harr, MemData_update, MemData_merge. rewrite map_app. f_equal.
  - induction mem as [|[i' v'] mem' IH]; [reflexivity|].
    cbn. destruct (i' =? i); f_equal; apply IH.
  - induction mem as [|[i' v'] mem' IH]; [reflexivity|].
    simpl. destruct (i' =? i); [reflexivity|].
    apply IH.
Qed.

Lemma hselect_MemData_to_harr addr data:
  hselectA (MemData_to_harr data) addr =
    match List.find (fun x => addr =? fst x) data with
    | Some v => HMapBits (snd v)
    | None => HMapEmpty
    end.
Proof.
  induction data as [|a l' IH].
  - reflexivity.
  - cbn. destruct (addr =? fst a).
    + reflexivity.
    + apply IH.
Qed.

Lemma hbits_hselect_MemData_to_harr data addr:
    match hselectA (MemData_to_harr data) (szNorm addr)
    with
    | HMapBits b => b
    | _ => sznil
    end = MemData_get addr data.
Proof.
  rewrite hselect_MemData_to_harr. unfold MemData_get. destruct (find _ _); reflexivity.
Qed.

Lemma MemData_get_update_neq i i' v mem:
  szEquiv i i' = false ->
  MemData_get i (MemData_update (szNorm i') v mem) = MemData_get i mem.
Proof.
  intros NEQ.
  rewrite <- hbits_hselect_MemData_to_harr. rewrite <- hbinUArr_MemData.
  rewrite hselectA_single_upd_neq.
  2: { unfold szEquiv in NEQ. intros EQ. rewrite EQ in NEQ.
    rewrite Z.eqb_refl in NEQ. discriminate NEQ. }
  rewrite hbits_hselect_MemData_to_harr. reflexivity.
Qed.

Lemma MemData_get_update_eq i i' v mem:
  szEquiv i i' = true ->
  MemData_get i (MemData_update (szNorm i') v mem) = v.
Proof.
  intros EQ.
  rewrite <- hbits_hselect_MemData_to_harr. rewrite <- hbinUArr_MemData.
  unfold szEquiv in EQ. apply Z.eqb_eq in EQ. rewrite EQ.
  rewrite hselectA_single_upd_bits. reflexivity.
Qed.

Module ICacheASpec.
  Import Lang.Semantics.
  Import Mem.ICacheA.
  Import ListNotations.
  Import HMapNotations.


  Definition update_flops (update: Updates) (flops: Flops): State :=
    hupds (to_state flops) (update_to_state update).

  Inductive IsICacheAFlops (data: MemData) (has_buffered: bool) (buffered_addr_sz: SZ) buffered_ret_sz (flops: Flops): Prop :=
  | mkIsICacheAFlops
      (FORMAT:
        flops = {|imem_v := MemData_to_harr data;
                  int_resp_vld_v := #{Z.b2z has_buffered, 1, false};
                  int_resp_v := buffered_ret_sz |}
      )
      (CONSISTENT: if has_buffered then buffered_ret_sz = szCastV #{32,32,true} (MemData_get_with_div4 buffered_addr_sz data) else True)
  .

  #[local] Transparent ICacheA.trs_structured.
  #[local] Arguments Z.pow_pos : simpl never.
  #[local] Arguments Z.pow : simpl never.
  #[local] Arguments Z.shiftl : simpl never.
  #[local] Arguments Z.mul : simpl never.
  #[local] Arguments szIsZero : simpl never.


  Lemma szIsZero_1 : szIsZero #{1, 1, false} = false.
  Proof. reflexivity. Qed.

  Lemma icacheA_trs_spec (data: MemData) rst_sz req_vld_sz req_sz resp_rdy_sz flush_sz flops has_buffered buffered_addr_sz buffered_ret_sz
    (INV_FLOPS: IsICacheAFlops data has_buffered buffered_addr_sz buffered_ret_sz flops)
    (RST : rst_sz = #{1, 1, false}) :
      exists (update: Updates) (req_rdy resp_vld: bool) resp_sz,
      let inputs := {|
        rst_n_v := rst_sz;
        imem_req_vld_v := req_vld_sz;
        imem_req_v := req_sz;
        imem_resp_rdy_v := resp_rdy_sz;
        flush_v := flush_sz
      |} in
        ICacheA.trs_structured inputs flops =
          (update,
          {|
            imem_req_rdy_v := #{Z.b2z req_rdy, 1, false};
            imem_resp_vld_v := #{Z.b2z resp_vld, 1, false};
            imem_resp_v := resp_sz;
          |}) /\
          resp_vld = has_buffered /\
          resp_sz = buffered_ret_sz /\
          (if (has_buffered) then resp_sz = szCastV #{32,32,true} (MemData_get_with_div4 buffered_addr_sz data) else True) /\
          (* The full spec below is available if the input is fully provided. *)
          (forall req_vld_b resp_rdy_b flush_b,
            req_vld_sz = #{Z.b2z req_vld_b, 1, false} ->
            resp_rdy_sz = #{Z.b2z resp_rdy_b, 1, false} ->
            flush_sz = #{Z.b2z flush_b, 1, false} ->
              exists has_buffered' buffered_addr_sz' buffered_ret_sz' flops',
              update_flops update flops = to_state flops' /\
              req_rdy = (if (has_buffered) then resp_rdy_b else true) /\
              has_buffered' = (if flush_b then false else if (req_vld_b && req_rdy) then true else if (resp_vld && resp_rdy_b) then false else has_buffered) /\
              buffered_addr_sz' = (if flush_b then #{0, 32, false} else if (req_vld_b && req_rdy) then req_sz else buffered_addr_sz) /\
              IsICacheAFlops data has_buffered' buffered_addr_sz' buffered_ret_sz' flops'
          )
  .
  Proof.
    destruct flops. destruct INV_FLOPS. injection FORMAT as -> -> ->. subst rst_sz.
    eexists _, _, _, _. intros ?; subst inputs.
    repeat ssplit.
    { (* Transition *) cbn. reflexivity. }
    { (* resp_vld *) reflexivity. }
    { (* resp_sz *) reflexivity. }
    { (* consistency *) exact CONSISTENT. }
    (* Full spec *)
    intros ??? -> -> ->. eexists _, _, (* buffered_ret_sz' *) (if flush_b then #{0,32,false} else _). eexists (Build_Flops _ _ _). repeat ssplit. 3-4: reflexivity.
    2: { (* req_rdy *) destruct has_buffered, resp_rdy_b; reflexivity. }
    { (* update_flops *) cbn. reflexivity. }
    { (* INV *) constructor.
      - (* FORMAT *) f_equal.
        + (* int_resp_vld_v *) destruct flush_b; [reflexivity|]. destruct has_buffered, resp_rdy_b, req_vld_b; reflexivity.
        + (* int_resp_v *) destruct flush_b; reflexivity.
      - (* CONSISTENT *) destruct flush_b; [exact I|]. cbn.
          unfold MemData_get_with_div4. rewrite hbits_hselect_MemData_to_harr. destruct has_buffered, resp_rdy_b, req_vld_b; try subst buffered_ret_sz ; reflexivity.
    }
  Qed.

End ICacheASpec.
