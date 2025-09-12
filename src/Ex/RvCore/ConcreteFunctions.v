Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.

Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.
Require Import Ex.RvCore.Common Ex.RvCore.Spec Ex.RvCore.Core.

Import SZNotations.
Import ListNotations.


Section WithCtx.
  Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.

  #[local] Ltac ef_equal :=
  eapply f_equal
  || eapply f_equal2
  || eapply f_equal3
  || eapply f_equal4
  || eapply f_equal5.

  #[local] Lemma if_bool_eq {A : Type} (c1 c2 : bool) (then1 else1 then2 else2 : A) :
    c1 = c2 ->
    then1 = then2 ->
    else1 = else2 ->
    (if c1 then then1 else else1) = (if c2 then then2 else else2).
  Proof. intros. subst. reflexivity. Qed.

  #[local] Lemma if_bool_eq_with_f {A B : Type} (c1 c2 : bool) f1 (then1 else1 : A) (then2 else2 : B) :
    c1 = c2 ->
    f1 then1 = then2 ->
    f1 else1 = else2 ->
    f1 (if c1 then then1 else else1) = (if c2 then then2 else else2).
  Proof. intros. subst. destruct c2; reflexivity. Qed.

  #[local] Tactic Notation "auto_instantiate" uconstr(h) :=
    match goal with | |- ?a = ?b =>
      try reflexivity;
      match b with
      (* if b is an if expression, instantiate target with an if expression. *)
      | if _ then _ else _ => eapply if_bool_eq || eapply if_bool_eq_with_f
      | _ =>
        tryif (is_var b) then
          (* if b is a variable, see if the right-hand side can be obtained by haccess. *)
          (instantiate (1 := hbits (haccess h pc)); reflexivity) ||
          (instantiate (1 := hbits (haccess h opcode)); reflexivity) ||
          (instantiate (1 := hbits (haccess h funct3)); reflexivity) ||
          (instantiate (1 := hbits (haccess h funct7)); reflexivity) ||
          (instantiate (1 := hbits (haccess h rsv1)); reflexivity) ||
          (instantiate (1 := hbits (haccess h rsv2)); reflexivity) ||
          (instantiate (1 := hbits (haccess h imm_b)); reflexivity) ||
          (instantiate (1 := hbits (haccess h imm_i)); reflexivity) ||
          (instantiate (1 := hbits (haccess h imm_j)); reflexivity) ||
          (instantiate (1 := hbits (haccess h imm_u)); reflexivity) ||
          (instantiate (1 := hbits (haccess h dmem_resp)); reflexivity)
          (* if it is not a variable, we assume it is a function *)
          else ef_equal
      end
    end.


  Definition ldvf_concrete: { ldvf: State -> SZ |
    forall funct3_v dmem_resp_v,
    let ins := HMapStr [(funct3, HMapBits funct3_v); (dmem_resp, HMapBits dmem_resp_v)] in
    (match (Functions.f get_ld_val) with
    | Sret func => func.(func_func) ins
    | Fail _ => HMapEmpty end) = HMapBits (ldvf ins) }.
  Proof.
    destruct SZ_OPS eqn: Hsz_ops, ARRAY_OPS eqn: Harray_ops.
    match (type of Hsz_ops) with | SZ_OPS = ?a => set (SZ_OPS' := a) end.
    match (type of Harray_ops) with | ARRAY_OPS = ?a => set (ARRAY_OPS' := a) end.
    clear Hsz_ops SZ_OPS ARRAY_OPS Harray_ops.
    eexists _. intros.

    instantiate (1 := fun h => _).
    vm_compute.
    symmetry.
    repeat (auto_instantiate h).
  Defined.

  Definition execf_concrete: { execf: State -> SZ |
    forall pc_v opcode_v funct3_v funct7_v rsv1_v rsv2_v imm_i_v imm_u_v,
    let ins := HMapStr [(pc, HMapBits pc_v); (opcode, HMapBits opcode_v); (funct3, HMapBits funct3_v); (funct7, HMapBits funct7_v); (rsv1, HMapBits rsv1_v);
                (rsv2, HMapBits rsv2_v); (imm_i, HMapBits imm_i_v); (imm_u, HMapBits imm_u_v)] in
    (match (Functions.f get_exec_value) with
    | Sret func => func.(func_func) ins
    | Fail _ => HMapEmpty end) = HMapBits (execf ins) }.
  Proof.
    destruct SZ_OPS eqn: Hsz_ops, ARRAY_OPS eqn: Harray_ops.
    match (type of Hsz_ops) with | SZ_OPS = ?a => set (SZ_OPS' := a) end.
    match (type of Harray_ops) with | ARRAY_OPS = ?a => set (ARRAY_OPS' := a) end.
    clear Hsz_ops SZ_OPS ARRAY_OPS Harray_ops.
    eexists _. intros.

    instantiate (1 := fun h => _).
    vm_compute.
    symmetry.
    repeat (auto_instantiate h).
  Defined.

  Definition pcf_concrete: { pcf: State -> SZ |
    forall pc_v opcode_v funct3_v rsv1_v rsv2_v imm_b_v imm_i_v imm_j_v,
    let ins := HMapStr [(pc, HMapBits pc_v); (opcode, HMapBits opcode_v); (funct3, HMapBits funct3_v); (rsv1, HMapBits rsv1_v);
                (rsv2, HMapBits rsv2_v); (imm_b, HMapBits imm_b_v); (imm_i, HMapBits imm_i_v); (imm_j, HMapBits imm_j_v)] in
    (match (Functions.f get_next_pc) with
    | Sret func => func.(func_func) ins
    | Fail _ => HMapEmpty end) = HMapBits (pcf ins) }.
  Proof.
    destruct SZ_OPS eqn: Hsz_ops, ARRAY_OPS eqn: Harray_ops.
    match (type of Hsz_ops) with | SZ_OPS = ?a => set (SZ_OPS' := a) end.
    match (type of Harray_ops) with | ARRAY_OPS = ?a => set (ARRAY_OPS' := a) end.
    clear Hsz_ops SZ_OPS ARRAY_OPS Harray_ops.
    eexists _. intros.

    instantiate (1 := fun h => _).
    vm_compute.
    symmetry.
    progress repeat match goal with
    | |- context [match ?h with | HMapBits b => b | _ => _ end] =>
    replace (match h with | HMapBits b => b | _ => _ end) with (hbits h) by reflexivity
    end.
    repeat (auto_instantiate h).
  Defined.

End WithCtx.


Import Core.Core.

Lemma core_transition_concrete_eq `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap} ins sf btbf :
  (Core.mtrs_abs_funcs (proj1_sig ldvf_concrete) (proj1_sig pcf_concrete) (proj1_sig execf_concrete) btbf).(mtrs_func) ins sf = (Core.mtrs btbf).(mtrs_func) ins sf.
Proof.
  destruct SZ_OPS eqn: Hsz_ops, ARRAY_OPS eqn: Harray_ops.
  match (type of Hsz_ops) with | SZ_OPS = ?a => set (SZ_OPS' := a) end.
  match (type of Harray_ops) with | ARRAY_OPS = ?a => set (ARRAY_OPS' := a) end.
  clear Hsz_ops SZ_OPS ARRAY_OPS Harray_ops.
  unfold mtrs_func, mtrsof_mtrs.
  pose proof (proj2_sig ldvf_concrete) as Hldvf. cbv -[proj1_sig ldvf_concrete] in Hldvf.
  pose proof (proj2_sig pcf_concrete) as Hpcf. cbv -[proj1_sig pcf_concrete] in Hpcf.
  pose proof (proj2_sig execf_concrete) as Hexecf. cbv -[proj1_sig execf_concrete] in Hexecf.

  cbv [Core.mtrs_abs_funcs Core.mtrs SZ_OPS' ARRAY_OPS'];

  destruct (from_state ins) as [[]|]; [|reflexivity];
  (* [|reflexivity]. *)
  destruct (from_state sf) as [[??????? [] ? [??????? []]]|]; [|reflexivity];
  (* [|reflexivity]. *)
  rewrite <- Hldvf, <- Hpcf, <- Hexecf; reflexivity.
Qed.

Import Spec.Spec.

Lemma spec_transition_concrete_eq `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap} ins sf :
  (Spec.mtrs_abs_funcs (proj1_sig ldvf_concrete) (proj1_sig pcf_concrete) (proj1_sig execf_concrete)).(mtrs_func) ins sf = (Spec.mtrs).(mtrs_func) ins sf.
Proof.
  destruct SZ_OPS eqn: Hsz_ops, ARRAY_OPS eqn: Harray_ops.
  match (type of Hsz_ops) with | SZ_OPS = ?a => set (SZ_OPS' := a) end.
  match (type of Harray_ops) with | ARRAY_OPS = ?a => set (ARRAY_OPS' := a) end.
  clear Hsz_ops SZ_OPS ARRAY_OPS Harray_ops.
  unfold mtrs_func, mtrsof_mtrs.
  pose proof (proj2_sig ldvf_concrete) as Hldvf. cbv -[proj1_sig ldvf_concrete] in Hldvf.
  pose proof (proj2_sig pcf_concrete) as Hpcf. cbv -[proj1_sig pcf_concrete] in Hpcf.
  pose proof (proj2_sig execf_concrete) as Hexecf. cbv -[proj1_sig execf_concrete] in Hexecf.

  cbv [Spec.mtrs_abs_funcs Spec.mtrs SZ_OPS' ARRAY_OPS'];

  destruct (from_state ins) as [[]|]; [|reflexivity];
  destruct (from_state sf) as [[??[][]]|]; [|reflexivity];
  rewrite <- Hldvf, <- Hpcf, <- Hexecf; reflexivity.
Qed.
