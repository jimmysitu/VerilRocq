From Coq Require Import ZArith.BinInt Lia.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang Lang.ModuleITree.

Require Import Ex.RvCore.Common Ex.RvCore.Mem Ex.RvCore.Spec Ex.RvCore.Sim.
Import Spec.Spec.

Section WithCtx.
  Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.

  Definition spec_concrete_transition: ModuleITree.Transition := trsT (Spec.mtrs).(mtrs_func).

  Record spec_concrete_transition_flops sf1 inp := mk_unfolded {
    next_flops: Spec.Flops;
    outs: ModuleITree.OutputT;
    eq_transition: (to_state next_flops, outs) = spec_concrete_transition inp (to_state sf1);
  }.

End WithCtx.

Definition spec_concrete_transition_flops' `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap} (sf1: Spec.Flops)
            : spec_concrete_transition_flops sf1 Sim.fixed_input.
Proof.
  set (SZ_OPS' := SZ_OPS). destruct SZ_OPS.
  set (ARRAY_OPS' := ARRAY_OPS). destruct ARRAY_OPS.
  destruct sf1 as [?? [][]].
  eapply (mk_unfolded _ _ ({| pc_v := _; rf_v := _; icache_v := {| ICache.imem_v := _ |}; dcache_v := {| DCache.dmem_v := _ |} |}) _).
  unfold spec_concrete_transition, trsT, trsNext.
  set (T := mtrs_func mtrs fixed_input _).
  let T' := (eval cbv in T) in replace T with T' by reflexivity. clear T. cbv [fst snd].
  cbn.

  repeat f_equal.
  all: instantiate_cond_eq.
Defined.

Lemma spec_transition_concrete_unfold `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap} sf1 s2 outs
      (TRS : (s2, outs) = spec_concrete_transition fixed_input (to_state sf1)) :
        let (sf2, outs', _) := spec_concrete_transition_flops' sf1 in
        s2 = to_state sf2 /\
        outs = outs'.
Proof.
  destruct (spec_concrete_transition_flops' sf1) as [sf2 outs' eq_trs].
  rewrite <- TRS in eq_trs. clear TRS. inversion eq_trs. auto.
Qed.
