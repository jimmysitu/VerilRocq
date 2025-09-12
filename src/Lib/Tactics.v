Require Import Lib.SZ.

Ltac instantiate_cond := match goal with
                         | |- context [if ?c then _ else _] =>
                             instantiate (1:= if c then _ else _);
                             let Hc := fresh "Hc" in destruct c eqn:Hc
                         end.
Ltac instantiate_cond_eq := repeat (instantiate_cond; try reflexivity).

Ltac dest_if := match goal with
                | |- context [if ?c then _ else _] =>
                    match c with
                    | context [if _ then _ else _] => fail 1
                    | _ => let Hc := fresh "Hc" in destruct c eqn:Hc
                    end
                end.

Ltac simpl_sz :=
  repeat (rewrite ?szIsZero_szUNot, ?szIsZero_szBLAnd, ?szIsZero_szBLOr, ?szIsZero_szBEq in *;
          try match goal with
            | [H: szIsZero _ = true |- _] => rewrite H
            | [H: szIsZero _ = false |- _] => rewrite H
            end).
Ltac simpl_bool :=
  repeat rewrite ?Bool.andb_true_l, ?Bool.andb_true_r, ?Bool.orb_true_l, ?Bool.orb_true_r,
    ?Bool.andb_false_l, ?Bool.andb_false_r, ?Bool.orb_false_l, ?Bool.orb_false_r,
    ?Bool.negb_true_iff, ?Bool.negb_false_iff, ?Bool.negb_involutive in *.
Ltac simpl_cond :=
  simpl_sz; simpl_bool; simpl in *.

Ltac dest_if_simpl := dest_if; simpl_cond.
