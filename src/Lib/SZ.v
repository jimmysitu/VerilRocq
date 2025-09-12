From Coq Require Import Lia ZArith.BinInt ZArith_dec.
#[local] Open Scope Z_scope.

Require Import coqutil.Z.BitOps.

(* Small utils *)

Definition sz_int32: Z := 32.
Definition sz_int32_nat: nat := 32.

Fixpoint binaryZtoZ (sz: nat) (bz: Z): Z :=
  match sz with
  | O => 0
  | S sz' => (binaryZtoZ sz' (Z.div bz 10)) * 2 + (Z.rem bz 10)
  end.

Fixpoint octalZtoZ (sz: nat) (oz: Z): Z :=
  match sz with
  | O => 0
  | S sz' => (octalZtoZ sz' (Z.div oz 10)) * 8 + (Z.rem oz 10)
  end.

Record SZ := { zof: Z; szof: Z; snof: bool }.

Module SZNotations.
  Notation "'#{' ZV , SZV , SNV '}'" :=
    {| zof := ZV; szof := SZV; snof := SNV |} (format "'#{' ZV , SZV , SNV '}'").
End SZNotations.

Import SZNotations.

Definition sznil: SZ := #{0, 0, false}.
Definition szF0: SZ := #{0, 1, true}.
Definition szF1: SZ := #{-1, 1, true}.

Class sz_ops :=
  { sz_zero: SZ;
    sz_is_zero: SZ -> bool;
    sz_norm: SZ -> Z; (* unsigned normalization *)
    sz_eq_str: SZ -> SZ -> bool; (* strict, structural equality *)
    sz_equiv: SZ -> SZ -> bool; (* equality defined in Verilog *)

    sz_select: SZ -> Z (*index*) -> SZ;
    sz_range: SZ -> Z (*msb*) -> Z (*lsb*) -> SZ;

    sz_concat2: SZ -> SZ -> SZ;
    sz_concat: list SZ -> SZ;
    sz_msb: Z (*width*) -> SZ -> SZ;
    sz_lsb: Z (*width*) -> SZ -> SZ;
    sz_signext: Z (*width*) -> SZ -> SZ;
    sz_zeroext: Z (*width*) -> SZ -> SZ;
    sz_cast_v: SZ (*value containing the new width*) -> SZ -> SZ;
    sz_signed: SZ -> SZ;
    sz_unsigned: SZ -> SZ;

    sz_u_minus: SZ -> SZ;
    sz_u_not: SZ -> SZ;
    sz_u_neg: SZ -> SZ;
    sz_u_and: SZ -> SZ;
    sz_u_nand: SZ -> SZ;
    sz_u_or: SZ -> SZ;
    sz_u_nor: SZ -> SZ;
    sz_u_xor: SZ -> SZ;
    sz_u_xnor: SZ -> SZ;

    sz_b_add: SZ -> SZ -> SZ;
    sz_b_sub: SZ -> SZ -> SZ;
    sz_b_mul: SZ -> SZ -> SZ;
    sz_b_div: SZ -> SZ -> SZ;
    sz_b_rem: SZ -> SZ -> SZ;
    sz_b_eq: SZ -> SZ -> SZ;
    sz_b_neq: SZ -> SZ -> SZ;
    sz_b_feq: SZ -> SZ -> SZ;
    sz_b_fneq: SZ -> SZ -> SZ;
    sz_b_weq: SZ -> SZ -> SZ;
    sz_b_wneq: SZ -> SZ -> SZ;
    sz_b_land: SZ -> SZ -> SZ;
    sz_b_lor: SZ -> SZ -> SZ;
    sz_b_pow: SZ -> SZ -> SZ;
    sz_b_lt: SZ -> SZ -> SZ;
    sz_b_le: SZ -> SZ -> SZ;
    sz_b_gt: SZ -> SZ -> SZ;
    sz_b_ge: SZ -> SZ -> SZ;
    sz_b_and: SZ -> SZ -> SZ;
    sz_b_or: SZ -> SZ -> SZ;
    sz_b_xor: SZ -> SZ -> SZ;
    sz_b_xnor: SZ -> SZ -> SZ;
    sz_b_shr: SZ -> SZ -> SZ;
    sz_b_shl: SZ -> SZ -> SZ;
    sz_b_sar: SZ -> SZ -> SZ;
    sz_b_sal: SZ -> SZ -> SZ;
  }.

Definition sz_rep `{sz_ops} (n: nat) (z: SZ): SZ := sz_concat (List.repeat z n).

Definition szNormZ (z: SZ): Z := Z.modulo (zof z) (Z.pow 2 (szof z)).
Definition szNormS (z: SZ): Z :=
  BitOps.signExtend (szof z) (szNormZ z).
Definition szNorm (z: SZ): Z :=
  if snof z then szNormS z else szNormZ z.

Definition szIsZero (sz: SZ): bool := Z.eqb (szNorm sz) 0.
Arguments szIsZero !sz /.


Definition szZeroExt (wid: Z) (z: SZ): SZ :=
  #{szNormZ z, wid, snof z}.
Definition szSignExt (wid: Z) (z: SZ): SZ :=
  #{szNormS z, wid, snof z}.
Arguments szZeroExt wid !z /.
Arguments szSignExt wid !z /.

(** IEEE standard 11.4.5 Equality operators *)
Definition szEquiv (sz1 sz2: SZ): bool :=
  Z.eqb (szNorm sz1) (szNorm sz2).
Arguments szEquiv !sz1 !sz2 /.

(** NOTE: better to evaluate equalities for sizes and signs first, since they usually
 * evaluate to a constant bool. *)
Definition szEqStr (sz1 sz2: SZ): bool :=
  match sz1, sz2 with
  | {| zof := z1; szof := size1; snof := sign1 |},
    {| zof := z2; szof := size2; snof := sign2 |} =>
      (Z.eqb size1 size2) && (Bool.eqb sign1 sign2) && (szEquiv sz1 sz2)
  end.
Arguments szEqStr !sz1 !sz2 /.

Definition szMsb (wid: Z) (z: SZ): SZ :=
  #{Z.div (zof z) (Z.pow 2 wid), wid, snof z}.
Definition szLsb (wid: Z) (z: SZ): SZ :=
  #{Z.modulo (zof z) (Z.pow 2 wid), wid, snof z}.
Arguments szMsb wid !z /.
Arguments szLsb wid !z /.


(** IEEE Standard 11.8.1 .. Concatenate results are unsigned .. *)
Definition szConcat2 (msz lsz: SZ): SZ :=
  {| zof := Z.shiftl (zof msz) (szof lsz) + szNormZ lsz;
    szof := szof msz + szof lsz;
    snof := false |}.
Fixpoint szConcat (szs: list SZ): SZ :=
  match szs with
  | nil => sznil
  | cons sz szs' => szConcat2 sz (szConcat szs')
  end.
Arguments szConcat2 !msz !lsz /.

Definition szCast' (nwid: Z) (nsign: bool) (sz: SZ): SZ :=
  let nsz := if (Z.leb (szof sz) nwid)
             then #{szNorm sz, nwid, snof sz}
             else (* truncation *) szLsb nwid sz in
  #{zof nsz, szof nsz, nsign}.

Definition szCastV (nwid sz: SZ): SZ :=
  if (Z.eqb (zof nwid) (szof sz)) then sz
  else szCast' (zof nwid) (snof sz) sz.
Arguments szCastV !nwid !sz /.

Definition szCastD (new sz: SZ): SZ :=
  if (andb (Z.eqb (szof new) (szof sz)) (Bool.eqb (snof new) (snof sz))) then sz
  else szCast' (szof new) (snof new) sz.

Definition szSigned (sz: SZ): SZ :=
  #{zof sz, szof sz, true}.
Arguments szSigned !sz /.

Definition szUnsigned (sz: SZ): SZ :=
  #{zof sz, szof sz, false}.
Arguments szUnsigned !sz /.


Fixpoint redXor' (sz: nat) (v: Z): bool :=
  match sz with
  | O => Z.testbit v (Z.of_nat sz)
  | S sz' => xorb (Z.testbit v (Z.of_nat sz)) (redXor' sz' v)
  end.
Definition redXor (v: SZ): SZ :=
  #{Z.b2z (redXor' (Z.to_nat (szof v)) (zof v)), 1, false}.
Definition redXnor (v: SZ): SZ :=
  #{Z.b2z (negb (redXor' (Z.to_nat (szof v)) (zof v))), 1, false}.

Definition szUMinus (v: SZ) := #{(-(zof v)), (szof v), (snof v)}.
Definition szUNot (v: SZ) := #{Z.b2z (szIsZero v), 1, false}.
Definition szUNeg (v: SZ) := #{(Z.pow 2 (szof v) -  1 - zof v), (szof v), (snof v)}.
Arguments szUMinus !v /.
Arguments szUNot !v /.
Arguments szUNeg !v /.

Definition szUAnd (v: SZ) :=
  #{Z.b2z (Z.eqb (szNormS v) (-1)), 1, false}.
Definition szUNand (v: SZ) :=
  #{Z.b2z (negb (Z.eqb (szNormS v) (-1))), 1, false}.
Definition szUOr (v: SZ) := #{Z.b2z (negb (szIsZero v)), 1, false}.
Definition szUNor (v: SZ) := #{Z.b2z (szIsZero v), 1, false}.
Definition szUXor (v: SZ) := redXor v.
Definition szUXnor (v: SZ) := redXnor v.
Arguments szUAnd !v /.
Arguments szUNand !v /.
Arguments szUOr !v /.
Arguments szUNor !v /.
Arguments szUXor !v /.
Arguments szUNor !v /.
Arguments szUXnor !v /.

Definition szBin {T} (op: Z -> Z -> T) (lv rv: SZ): T :=
  op (szNorm lv) (szNorm rv).

Definition szBAdd (lv rv: SZ) :=
  #{(szBin Z.add lv rv), (Z.max (szof lv) (szof rv)), (snof lv && snof rv)}.
Definition szBSub (lv rv: SZ) :=
  #{(szBin Z.sub lv rv), (Z.max (szof lv) (szof rv)), (snof lv && snof rv)}.
Definition szBMul (lv rv: SZ) :=
  #{(szBin Z.mul lv rv), (Z.max (szof lv) (szof rv)), (snof lv && snof rv)}.
Definition szBDiv (lv rv: SZ) :=
  #{(szBin Z.div lv rv), (Z.max (szof lv) (szof rv)), (snof lv && snof rv)}.
Definition szBRem (lv rv: SZ) :=
  #{(szBin Z.rem lv rv), (Z.max (szof lv) (szof rv)), (snof lv && snof rv)}.
Arguments szBAdd !lv !rv /.
Arguments szBSub !lv !rv /.
Arguments szBMul !lv !rv /.
Arguments szBDiv !lv !rv /.
Arguments szBRem !lv !rv /.

Definition szBEq (lv rv: SZ) := #{Z.b2z (szEquiv lv rv), 1, false}.
Definition szBNEq (lv rv: SZ) := #{Z.b2z (negb (szEquiv lv rv)), 1, false}.
Definition szBFEq (lv rv: SZ) :=
  (** NOTE: 'x', 'z', and '?' are not supported.. *)
  #{Z.b2z (Z.eqb (zof lv) (zof rv)), 1, false}.
Definition szBFNEq (lv rv: SZ) :=
  #{Z.b2z (negb (Z.eqb (zof lv) (zof rv))), 1, false}.
Definition szBWEq (lv rv: SZ) :=
  #{Z.b2z (Z.eqb (zof lv) (zof rv)), 1, false}.
Definition szBWNEq (lv rv: SZ) :=
  #{Z.b2z (negb (Z.eqb (zof lv) (zof rv))), 1, false}.
Arguments szBEq !lv !rv /.
Arguments szBNEq !lv !rv /.
Arguments szBFEq !lv !rv /.
Arguments szBFNEq !lv !rv /.
Arguments szBWEq !lv !rv /.
Arguments szBWNEq !lv !rv /.

Definition szBLAnd (lv rv: SZ) :=
  #{Z.b2z (andb (negb (szIsZero lv)) (negb (szIsZero rv))), 1, false}.
Definition szBLOr (lv rv: SZ) :=
  #{Z.b2z (orb (negb (szIsZero lv)) (negb (szIsZero rv))), 1, false}.
Arguments szBLAnd !lv !rv /.
Arguments szBLOr !lv !rv /.

Definition szBPow (lv rv: SZ) := #{(szBin Z.pow lv rv), (szof lv), (snof lv && snof rv)}.
Arguments szBPow !lv !rv /.

Definition szBLt (lv rv: SZ) := #{Z.b2z (Z.ltb (szNorm lv) (szNorm rv)), 1, false}.
Definition szBLe (lv rv: SZ) := #{Z.b2z (Z.leb (szNorm lv) (szNorm rv)), 1, false}.
Definition szBGt (lv rv: SZ) := #{Z.b2z (Z.gtb (szNorm lv) (szNorm rv)), 1, false}.
Definition szBGe (lv rv: SZ) := #{Z.b2z (Z.geb (szNorm lv) (szNorm rv)), 1, false}.
Arguments szBLt !lv !rv /.
Arguments szBLe !lv !rv /.
Arguments szBGt !lv !rv /.
Arguments szBGe !lv !rv /.

Definition szBAnd (lv rv: SZ) :=
  let size := Z.max (szof lv) (szof rv) in
  #{(Z.land (szNorm lv mod 2 ^ size) (szNorm rv mod 2 ^ size)), size, false}.
Definition szBOr (lv rv: SZ) :=
  let size := Z.max (szof lv) (szof rv) in
  #{(Z.lor (szNorm lv mod 2 ^ size) (szNorm rv mod 2 ^ size)), size, false}.
Definition szBXor (lv rv: SZ) :=
  let size := Z.max (szof lv) (szof rv) in
  #{(Z.lxor (szNorm lv mod 2 ^ size) (szNorm rv mod 2 ^ size)), size, false}.
Definition szBXnor (lv rv: SZ) :=
  let size := Z.max (szof lv) (szof rv) in
  #{(-(Z.lxor (szNorm lv mod 2 ^ size) (szNorm rv mod 2 ^ size))+1), size, false}.
Arguments szBAnd !lv !rv /.
Arguments szBOr !lv !rv /.
Arguments szBXor !lv !rv /.
Arguments szBXnor !lv !rv /.

Definition szBShr (lv rv: SZ) := #{(Z.shiftr (szNormZ lv) (szNormZ rv)), (szof lv), false}.
Definition szBShl (lv rv: SZ) := #{(Z.shiftl (szNormZ lv) (szNormZ rv)), (szof lv), false}.
Definition szBSar (lv rv: SZ) := #{(Z.shiftr (szNorm lv) (szNormZ rv)), (szof lv), (snof lv)}.
Definition szBSal (lv rv: SZ) := #{(Z.shiftl (szNorm lv) (szNormZ rv)), (szof lv), (snof lv)}.
Arguments szBShr !lv !rv /.
Arguments szBShl !lv !rv /.
Arguments szBSar !lv !rv /.
Arguments szBSal !lv !rv /.

Definition szSelect (b: SZ) (i: Z) := #{(Z.b2z (Z.testbit (szNorm b) i)), 1, false}.
Definition szRange (b: SZ) (s de: Z) := #{(bitSlice (szNorm b) de (s + 1)), (s - de + 1), false}.
Arguments szSelect : simpl never.
Arguments szRange : simpl never.

#[local] Instance SZ_sz_ops: sz_ops :=
  {| sz_zero := sznil;
    sz_is_zero := szIsZero;
    sz_norm := szNorm;
    sz_eq_str := szEqStr;
    sz_equiv := szEquiv;

    sz_select := szSelect;
    sz_range := szRange;

    sz_concat2 := szConcat2;
    sz_concat := szConcat;
    sz_msb := szMsb;
    sz_lsb := szLsb;
    sz_signext := szSignExt;
    sz_zeroext := szZeroExt;
    sz_cast_v := szCastV;
    sz_signed := szSigned;
    sz_unsigned := szUnsigned;

    sz_u_minus := szUMinus;
    sz_u_not := szUNot;
    sz_u_neg := szUNeg;
    sz_u_and := szUAnd;
    sz_u_nand := szUNand;
    sz_u_or := szUOr;
    sz_u_nor := szUNor;
    sz_u_xor := szUXor;
    sz_u_xnor := szUXnor;

    sz_b_add := szBAdd;
    sz_b_sub := szBSub;
    sz_b_mul := szBMul;
    sz_b_div := szBDiv;
    sz_b_rem := szBRem;
    sz_b_eq := szBEq;
    sz_b_neq := szBNEq;
    sz_b_feq := szBFEq;
    sz_b_fneq := szBFNEq;
    sz_b_weq := szBWEq;
    sz_b_wneq := szBWNEq;
    sz_b_land := szBLAnd;
    sz_b_lor := szBLOr;
    sz_b_pow := szBPow;
    sz_b_lt := szBLt;
    sz_b_le := szBLe;
    sz_b_gt := szBGt;
    sz_b_ge := szBGe;
    sz_b_and := szBAnd;
    sz_b_or := szBOr;
    sz_b_xor := szBXor;
    sz_b_xnor := szBXnor;
    sz_b_shr := szBShr;
    sz_b_shl := szBShl;
    sz_b_sar := szBSar;
    sz_b_sal := szBSal;
  |}.

(*! Facts *)

Lemma szIsZero_szUNot: forall sz, szIsZero (szUNot sz) = negb (szIsZero sz).
Proof.
  intros [z s n].
  unfold szIsZero, szUNot; simpl.
  destruct (szNorm #{z,s,n} =? 0); reflexivity.
Qed.

Lemma szIsZero_true_szUNot: forall sz, szIsZero sz = true -> szUNot sz = #{1,1,false}.
Proof.
  intros [z s n] H.
  unfold szIsZero, szUNot in *; simpl in *.
  rewrite H; reflexivity.
Qed.

Lemma szIsZero_false_szUNot: forall sz, szIsZero sz = false -> szUNot sz = #{0,1,false}.
Proof.
  intros [z s n] H.
  unfold szIsZero, szUNot in *; simpl in *.
  rewrite H; reflexivity.
Qed.

Lemma szIsZero_szBLAnd: forall sz1 sz2, szIsZero (szBLAnd sz1 sz2) = orb (szIsZero sz1) (szIsZero sz2).
Proof.
  intros [z1 s1 n1] [z2 s2 n2].
  unfold szIsZero, szBLAnd; simpl.
  destruct (szNorm #{z1,s1,n1} =? 0), (szNorm #{z2,s2,n2} =? 0); reflexivity.
Qed.

Lemma szIsZero_szBLOr: forall sz1 sz2, szIsZero (szBLOr sz1 sz2) = andb (szIsZero sz1) (szIsZero sz2).
Proof.
  intros [z1 s1 n1] [z2 s2 n2].
  unfold szIsZero, szBLOr; simpl.
  destruct (szNorm #{z1,s1,n1} =? 0), (szNorm #{z2,s2,n2} =? 0); reflexivity.
Qed.

Lemma szIsZero_szBEq: forall sz1 sz2, szIsZero (szBEq sz1 sz2) = negb (szEquiv sz1 sz2).
Proof.
  intros [z1 s1 n1] [z2 s2 n2]. simpl.
  destruct (_ =? szNorm _); reflexivity.
Qed.

Lemma szEquiv_szNorm_1: forall sz1 sz2, szEquiv sz1 sz2 = true -> szNorm sz1 = szNorm sz2.
Proof.
  unfold szEquiv; intros.
  apply Z.eqb_eq; assumption.
Qed.

Lemma szEquiv_szNorm_2: forall sz1 sz2, szEquiv sz1 sz2 = false -> szNorm sz1 <> szNorm sz2.
Proof.
  unfold szEquiv; intros.
  apply Z.eqb_neq; assumption.
Qed.

Lemma szIsZero_b2z b wid sn:
  0 < wid -> szIsZero #{Z.b2z b, wid, sn} = negb b.
Proof.
  intros WID_POS.
  assert (szNormZ #{Z.b2z b,wid,sn} = Z.b2z b) as HnormZb.
  { unfold szNormZ. cbn. destruct b; cbn; [|reflexivity].
    rewrite Z.mod_1_l; [auto|]. apply Z.pow_gt_1; lia. }
  unfold szIsZero, szNorm, szNormS. rewrite HnormZb. cbn.
  destruct sn.
  - destruct b; cbn.
    + destruct (Z_lt_dec 1 wid) as [H|H].
      { rewrite signExtend_nop with (l := 1); lia. }
      { assert (wid = 1) as -> by lia. reflexivity. }
    + rewrite signExtend_nop with (l := 0); lia.
  - destruct b; reflexivity.
Qed.

Lemma szBLAnd_b2z b1 b2 wid1 wid2 sn1 sn2:
  0 < wid1 -> 0 < wid2 -> szBLAnd (#{Z.b2z b1, wid1, sn1}) (#{Z.b2z b2, wid2, sn2}) = #{Z.b2z (b1 && b2), 1, false}.
Proof. intros. unfold szBLAnd. rewrite !szIsZero_b2z by lia. destruct b1, b2; reflexivity. Qed.

Lemma szBLOr_b2z b1 b2 wid1 wid2 sn1 sn2:
   0 < wid1 -> 0 < wid2 -> szBLOr (#{Z.b2z b1, wid1, sn1}) (#{Z.b2z b2, wid2, sn2}) = #{Z.b2z (b1 || b2), 1, false}.
Proof. intros. unfold szBLOr. rewrite !szIsZero_b2z by lia. destruct b1, b2; reflexivity. Qed.
