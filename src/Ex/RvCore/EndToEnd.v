Require Import Ex.RvCore.FormalSpec Ex.RvCore.Spec Ex.RvCore.Core Ex.RvCore.Common.
Require Ex.RvCore.Sim Ex.RvCore.FormalSim Ex.RvCore.FormalSpec Ex.RvCore.ConcreteFunctions.
Require Import Lang.Lang Lang.ModuleITree Lib.SZ Lib.HMap Lib.Tactics.

From ITree Require Import ITree ITreeFacts.
From FreeSim Require Import Tutorial SimGlobalIndex SimGlobalEquiv SimGlobalIndexFacts Behavior Any.
From Paco Require Import paco.
From Ordinal Require Import Ordinal.

(* Typeclass Instances *)
Require Import riscv.Utility.Words32Naive riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Z_keyed_SortedListMap.
#[local] Existing Instance SZ_sz_ops.
#[local] Existing Instance hmap_array_ops.

Import SZNotations.

(* Axioms *)
Require Import Coq.Logic.FunctionalExtensionality.
Require FreeSim.Axioms. (* For propositional extensionality. *)


Definition outputValid (o: hmap): bool :=
  match (pc_commit_vld_v <- sfind pc_commit_vld o;
        Sret pc_commit_vld_v) with
  | Sret pc_commit_vld_v => negb (szIsZero (hbits pc_commit_vld_v))
  | Fail _ => false
  end.
Definition fixed_input := HMapStr ((rst_n, HMapBits #{1, 1, false}) :: nil).


Section Target.
  Variable (btbf: State -> Z) (initial_imem: list (Z * Z)).

  Definition target_transition: ModuleITree.Transition := trsT ((Core.mtrs btbf).(mtrs_func)).

  Definition target_initial_imem := List.map (fun iv => (fst iv, HMapBits #{snd iv, 32, false})) initial_imem.
  Definition target_initial_state := Core.rstS btbf target_initial_imem.

  Definition target_module_from_state state :=
    filter_io fixed_input outputValid (module_itree target_transition state).
  Definition target_module := target_module_from_state target_initial_state.
End Target.

From FreeSim Require Import ModSem ModSemE.
Notation riscv_ioE := FormalSpec.riscv_ioE.
#[local] Instance CONF : EMSConfig := {| finalize := Some; initial_arg := tt↑ |}.


(* For interpreting the ITrees through FreeSim's notion of traces, we map the `riscv_ioE` events to eventE syscalls. *)
Definition riscvE_handler : (riscv_ioE +' eventE) ~> itree (riscv_ioE +' eventE)
  := (fun _ e => match e with
      | inl1 e =>
        match e with
        | FormalSpec.Output z =>
          trigger (SyscallOut "output_pc" z↑ (fun _ => True)) ;;; 
          Ret tt
        end
      | inr1 o => trigger o
  end).

(* We (1) map riscv_ioE events to eventE syscall events using `riscvE_handler` and (2) change the output type to Any.t. *)
Definition to_syscalls (I : itree (riscv_ioE +' eventE) void) : itree (riscv_ioE +' eventE) Any.t :=
  ITree.map (fun v : void => match v with end)
    (interp riscvE_handler I).

Definition src initial_imem := to_syscalls (FormalSpec.riscv_itree (FormalSpec.formal_initial_imem initial_imem)).
Definition tgt btbf initial_imem := to_syscalls (interp FormalSim.translate_riscv_output (target_module btbf initial_imem)).


(* The proof of the top level specification.
  We first apply FreeSim's adequacy theorem to show end-to-end behavioral refinement from simulation relation.
  We then transitively connect Sim.core_ok and FormalSim.spec_ok to prove the simulation. *)
Theorem core_refine_riscv_formal btbf initial_imem
  (IMEM_OK: List.Forall (fun iv => 0 <= fst iv < 2 ^ 30) initial_imem):
    Beh.of_program (ModSemL.compile_itree (initialize (tgt btbf initial_imem)))
    <1=
    Beh.of_program (ModSemL.compile_itree (initialize (src initial_imem))).
Proof.
  eapply adequacy_global_itree. { reflexivity. }
  
  (* The `ITree.map` and `interp` applied to both side of the `simg` relation can be safely removed.  *)
  unfold src, tgt, to_syscalls, ITree.map.
  ginit. guclo bindC_spec. econstructor; eauto. 2: { intros void_v. destruct void_v. }
  gfinal. right. eapply simg_interp.
  (* Now prove the simulation between riscv itrees. *)
  eapply simg_trans. 1: { eapply FormalSim.spec_ok, IMEM_OK. }
  unfold FormalSim.spec_itree, FormalSim.spec_itree_with_state.
  apply simg_interp.

  assert (target_module btbf initial_imem =
    Sim.core_itree (proj1_sig ConcreteFunctions.ldvf_concrete) (proj1_sig ConcreteFunctions.pcf_concrete) (proj1_sig ConcreteFunctions.execf_concrete)
                    btbf (List.map (fun iv => (fst iv, #{snd iv, 32, false})) initial_imem)) as ->.
  { unfold target_module, target_module_from_state, Sim.core_itree, Sim.core_itree_from_state. do 2progress f_equal.
    - unfold target_transition, Sim.core_transition. progress f_equal.
      extensionality ins. extensionality sf.
      rewrite ConcreteFunctions.core_transition_concrete_eq. reflexivity.
    - unfold target_initial_state, Sim.core_initial_state, MemSpec.MemData_to_harr, target_initial_imem. f_equal.
      rewrite List.map_map. reflexivity.
  }

  assert (FormalSim.spec_itree_raw (FormalSim.spec_initial_state _) =
      Sim.spec_itree (proj1_sig ConcreteFunctions.ldvf_concrete) (proj1_sig ConcreteFunctions.pcf_concrete) (proj1_sig ConcreteFunctions.execf_concrete)
                      (List.map (fun iv => (fst iv, #{snd iv, 32, false})) initial_imem) ) as ->.
  { unfold FormalSim.spec_itree_raw, Sim.spec_itree, Sim.spec_itree_from_state. do 2progress f_equal.
    - unfold FormalSim.spec_concrete_transition, Sim.spec_transition. progress f_equal.
      extensionality ins. extensionality sf.
      rewrite ConcreteFunctions.spec_transition_concrete_eq. reflexivity.
    - unfold FormalSim.spec_initial_state, Sim.spec_initial_state, MemSpec.MemData_to_harr. f_equal.
      rewrite List.map_map. reflexivity.
  }
  apply Sim.core_ok'.
Qed.
