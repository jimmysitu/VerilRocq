Require Import Coq.Bool.Bool Coq.Strings.String Coq.Strings.Ascii
        Coq.Lists.List (* Coq.Vectors.Vector *)
        Coq.Logic.Eqdep Coq.Arith.PeanoNat Coq.micromega.Lia.
Require Export Coq.Logic.ProofIrrelevance.

Set Implicit Arguments.

Definition o2l {A} (oa: option A): list A :=
  match oa with
  | None => nil
  | Some a => cons a nil
  end.

Definition ocons {A} (oa: option A) (l: list A): list A :=
  match oa with
  | None => l
  | Some a => cons a l
  end.

Ltac ssplit :=
  match goal with
  | [ |- _ /\ _] => split
  end.

Ltac nothing := idtac.

Ltac inv H := inversion H; subst; clear H.
Ltac dest :=
  repeat (match goal with
            | H: _ /\ _ |- _ => destruct H
            | H: exists _, _ |- _ => destruct H
          end).
Ltac dest_in :=
  repeat
    match goal with
    | [H: List.In _ _ |- _] => inv H
    end.
Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
    | [ H : context[if ?X then _ else _] |- _ ]=> destruct X
  end.

Ltac is_equal t1 t2 :=
  let Heq := fresh "Heq" in
  assert (Heq: t1 = t2) by reflexivity;
  clear Heq.

Ltac is_pure_const t :=
  tryif is_var t
  then fail
  else lazymatch t with
       | ?t1 ?t2 =>
         tryif is_pure_const t1
         then is_pure_const t2 else fail
       | _ => idtac
       end.

Ltac not_pure_const t :=
  tryif is_var t
  then idtac
  else lazymatch t with
       | ?t1 ?t2 =>
         tryif not_pure_const t1
         then idtac else not_pure_const t2
       | _ => fail
       end.

Ltac collect_of_type_helper ty ls :=
  match goal with
  | [v: ty |- _]
    => lazymatch ls with
       | context[cons v _] => fail
       | _ => collect_of_type_helper ty (cons v ls)
       end
  | _ => ls
  end.
Ltac collect_of_type ty := collect_of_type_helper ty (@nil ty).

Declare Scope monad_scope.
Module MonadNotations.

  Notation "A <- OA ; CONT" :=
    (match OA with
     | Some a => (fun A => CONT) a
     | None => None
     end) (at level 84, right associativity): monad_scope.

  Notation "A <- OA >> RET ; CONT" :=
    (match OA with
     | Some a => (fun A => CONT) a
     | None => Some RET
     end) (at level 84, right associativity): monad_scope.

  Open Scope monad_scope.
End MonadNotations.

(*! Basic facts *)

Lemma find_app:
  forall A (f: A -> bool) al1 al2,
    find f (al1 ++ al2) = match find f al1 with
                          | Some a => Some a
                          | None => find f al2
                          end.
Proof using .
  induction al1; simpl; intros; [reflexivity|].
  destruct (f a); [reflexivity|].
  apply IHal1.
Qed.

Lemma Forall_In:
  forall A (P: A -> Prop) al,
    Forall P al ->
    forall a,
      In a al -> P a.
Proof using .
  intros.
  rewrite Forall_forall in H.
  eauto.
Qed.

Lemma existsb_false_forall:
  forall A (f: A -> bool) al,
    existsb f al = false <->
      forall a, In a al -> f a = false.
Proof using .
  induction al; intros.
  - split; intros; [elim H0; fail|reflexivity].
  - split; intros.
    + apply Bool.orb_false_elim in H; dest.
      destruct H0; subst; [assumption|].
      apply IHal; assumption.
    + apply Bool.orb_false_intro.
      * apply H; left; reflexivity.
      * eapply IHal; intros.
        apply H; right; assumption.
Qed.

Lemma Forall2_In_left:
  forall A B (P: A -> B -> Prop) al bl,
    Forall2 P al bl ->
    forall a,
      In a al ->
      exists b, In b bl /\ P a b.
Proof using.
  induction al; simpl; intros; [exfalso; auto|].
  destruct bl; inv H.
  destruct H0; subst.
  - exists b; split; [|assumption].
    left; reflexivity.
  - specialize (IHal _ H6 _ H); dest.
    eexists; split; [|eassumption].
    right; assumption.
Qed.

Lemma Forall2_In_right:
  forall A B (P: A -> B -> Prop) bl al,
    Forall2 P al bl ->
    forall b,
      In b bl ->
      exists a, In a al /\ P a b.
Proof using.
  induction bl; simpl; intros; [exfalso; auto|].
  destruct al; inv H.
  destruct H0; subst.
  - exists a0; split; [|assumption].
    left; reflexivity.
  - specialize (IHbl _ H6 _ H); dest.
    eexists; split; [|eassumption].
    right; assumption.
Qed.
