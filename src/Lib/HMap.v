Require Import Coq.Lists.List. Import ListNotations.
Require Import ZArith.BinInt OrderedType.
Require Import Lib.Common Lib.SZ.
Require Import Coq.micromega.Lia.

Set Implicit Arguments.
Scheme Equality for list.

Lemma existsb_In:
  forall {A} (f: A -> bool) a (l: list A),
    In a l ->
    f a = true ->
    existsb f l = true.
Proof.
  induction l; simpl; intros; [exfalso; auto|].
  destruct H; subst.
  - rewrite H0; reflexivity.
  - rewrite IHl by assumption; apply Bool.orb_true_r.
Qed.

Class vid_t_c :=
  { vid_t: Set }.

Class vid_ops `{vid_t_c} :=
  { vid_eq_dec: forall v1 v2: vid_t, {v1 = v2} + {v1 <> v2}
  }.

Section Vid.
  Context `{vid_ops}.

  Definition vid_eqb (v1 v2: vid_t) := if vid_eq_dec v1 v2 then true else false.

  Lemma vid_eqb_refl: forall v, vid_eqb v v = true.
  Proof using .
    unfold vid_eqb; intros.
    destruct (vid_eq_dec v v); [reflexivity|elim n; reflexivity].
  Qed.

  Lemma vid_eqb_eq: forall v1 v2, vid_eqb v1 v2 = true -> v1 = v2.
  Proof using .
    unfold vid_eqb; intros.
    destruct (vid_eq_dec v1 v2); [assumption|discriminate].
  Qed.

  Lemma vid_eqb_not: forall v1 v2, v1 <> v2 -> vid_eqb v1 v2 = false.
  Proof using .
    unfold vid_eqb; intros.
    destruct (vid_eq_dec v1 v2); [elim H1; assumption|reflexivity].
  Qed.

End Vid.

Class array_ops hv :=
  { array_select: list (Z * hv) -> Z (*index*) -> hv;
    array_range: list (Z * hv) -> Z (* msb start *) -> Z (* lsb end *) -> list (Z * hv);
  }.

Section HMap.
  Context `{sz_ops}.
  Context `{vid_ops}.

  (*! Hierarchical finite maps *)

  Inductive hmap :=
  | HMapEmpty
  | HMapBits (b: SZ)
  | HMapArr (vs: list (Z (*index*) * hmap))
  | HMapStr (str: list (vid_t * hmap)).

  Definition is_empty (h: hmap): bool :=
    match h with
    | HMapEmpty => true
    | _ => false
    end.

  Definition is_bits (h: hmap): bool :=
    match h with
    | HMapBits _ => true
    | _ => false
    end.

  Context `{ao: array_ops hmap}.

  Definition hbits (h: hmap): SZ :=
    match h with
    | HMapBits b => b
    | _ => sz_zero
    end.
  Arguments hbits !h: simpl nomatch.

  Definition hbitsO (h: hmap): option SZ :=
    match h with
    | HMapBits b => Some b
    | _ => None
    end.

  Fixpoint hselectA (vs: list (Z * hmap)) (i: Z): hmap :=
    match vs with
    | nil => HMapEmpty
    | cons (hi, h) vs' => if Z.eqb i hi then h else hselectA vs' i
    end.

  Definition hselect (h: hmap) (i: SZ): hmap :=
    match h with
    | HMapBits b => HMapBits (sz_select b (sz_norm i))
    | HMapArr vs => array_select vs (sz_norm i)
    | _ => HMapEmpty
    end.

  Definition hselectO (h: hmap) (i: SZ): option hmap :=
    match h with
    | HMapBits b => Some (HMapBits (sz_select b (sz_norm i)))
    | HMapArr vs => Some (array_select vs (sz_norm i))
    | _ => None
    end.

  Definition hrangeA (vs: list (Z * hmap)) (msbi lsbi: Z): list (Z * hmap) :=
    List.filter (fun iv => andb (Z.leb lsbi (fst iv)) (Z.leb (fst iv) msbi)) vs.

  Definition hrange (h: hmap) (msbi lsbi: SZ): hmap :=
    match h with
    | HMapBits b => HMapBits (sz_range b (sz_norm msbi) (sz_norm lsbi))
    | HMapArr vs => HMapArr (array_range vs (sz_norm msbi) (sz_norm lsbi))
    | _ => HMapEmpty
    end.

  Definition hrangeO (h: hmap) (msbi lsbi: SZ): option hmap :=
    match h with
    | HMapBits b => Some (HMapBits (sz_range b (sz_norm msbi) (sz_norm lsbi)))
    | HMapArr vs => Some (HMapArr (array_range vs (sz_norm msbi) (sz_norm lsbi)))
    | _ => None
    end.

  Definition harr (h: hmap): list (Z * hmap) :=
    match h with
    | HMapArr arr => arr
    | _ => nil
    end.

  Definition hstr (h: hmap): list (vid_t * hmap) :=
    match h with
    | HMapStr str => str
    | _ => nil
    end.

  Fixpoint haccessV (str: list (vid_t * hmap)) (i: vid_t): option hmap :=
    match str with
    | nil => None
    | cons (n, h) str' => if vid_eqb i n then Some h else haccessV str' i
    end.

  Definition haccess (h: hmap) (i: vid_t): hmap :=
    match h with
    | HMapStr str => match haccessV str i with
                     | Some v => v
                     | None => HMapEmpty
                     end
    | _ => HMapEmpty
    end.

  Definition haccessO (h: hmap) (i: vid_t): option hmap :=
    match h with
    | HMapStr str => haccessV str i
    | _ => None
    end.

  Fixpoint hlistArr (n: nat) (hs: list hmap): list (Z * hmap) :=
    match hs with
    | nil => nil
    | cons h hs' => cons (Z.of_nat n, h) (hlistArr (S n) hs')
    end.

  Definition harray (hs: list hmap): hmap :=
    HMapArr (hlistArr O hs).

  (*! Hierarchical paths *)

  Inductive helt :=
  | HEltInd (i: SZ)
  | HEltVid (i: vid_t).

  Definition helt_eqb (e1 e2: helt) :=
    match e1, e2 with
    | HEltInd i1, HEltInd i2 => szEqStr i1 i2
    | HEltVid i1, HEltVid i2 => vid_eqb i1 i2
    | _, _ => false
    end.

  Definition hpath := list helt.

  Definition hpath_eqb (p1 p2: hpath): bool :=
    list_beq helt_eqb p1 p2.

  Definition hpathTop (p: hpath): option vid_t :=
    match p with
    | HEltVid i1 :: _ => Some i1
    | _ => None
    end.

  Definition hmove (h: hmap) (e: helt): option hmap :=
    match e with
    | HEltInd i => hselectO h i
    | HEltVid i => haccessO h i
    end.

  Fixpoint hpos (pre: hpath) (vid: vid_t) (h: hmap): option hpath :=
    match pre with
    | nil => match haccessO h vid with
             | Some _ => Some (cons (HEltVid vid) nil)
             | None => None
             end
    | cons e pre' =>
        match hmove h e with
        | Some sh => match hpos pre' vid sh with
                     | Some fh => Some (cons e fh)
                     | None => match haccessO h vid with
                               | Some _ => Some (cons (HEltVid vid) nil)
                               | None => None
                               end
                     end
        | None => None
        end
    end.

  Fixpoint hfind (p: hpath) (h: hmap): option hmap :=
    match p with
    | nil => Some h
    | cons e p' =>
        match hmove h e with
        | Some sh => hfind p' sh
        | None => None
        end
    end.

  Fixpoint hsingle (p: hpath) (v: hmap): hmap :=
    match p with
    | nil => v
    | cons (HEltInd i) np => hsingle np (HMapArr [(sz_norm i, v)])
    | cons (HEltVid i) np => hsingle np (HMapStr [(i, v)])
    end.

  (** Equivalence w.r.t. indices and fields *)

  Definition HSub (h1 h2: hmap): Prop :=
    forall p, p <> nil -> forall v, hfind p h1 = Some v -> hfind p h2 = Some v.

  Definition HSEquiv (h1 h2: hmap): Prop :=
    HSub h1 h2 /\ HSub h2 h1.

  Definition HDisj (h1 h2: hmap): Prop :=
    match h1, h2 with
    | HMapStr vs1, HMapStr vs2 => forall v, In v (List.map fst vs1) -> In v (List.map fst vs2) -> False
    | _, _ => True
    end.

  (** Iterations *)

  Section HIter.
    Variables (f: hmap -> hmap) (d: hmap).

    Fixpoint hiterArr (hs: list (Z * hmap)) (i: Z) {struct hs}: list (Z * hmap) :=
      match hs with
      | nil => [(i, d)]
      | cons h hs' => if Z.eqb i (fst h)
                      then cons (i, f (snd h)) hs'
                      else cons h (hiterArr hs' i)
      end.

    Fixpoint hiterStr (str: list (vid_t * hmap)) (i: vid_t) {struct str}: list (vid_t * hmap) :=
      match str with
      | nil => [(i, d)]
      | cons vh str' => if vid_eqb i (fst vh)
                        then cons (i, f (snd vh)) str'
                        else cons vh (hiterStr str' i)
      end.

  End HIter.

  (* NOTE: overwrites the value if there is already a value in a given path. *)
  Fixpoint hadd (p: hpath) (v: hmap) (h: hmap): hmap :=
    match p with
    | nil => v
    | cons (HEltInd i) np =>
        match h with
        | HMapEmpty => hsingle p v
        | HMapArr hs => HMapArr (hiterArr (hadd np v) (hsingle np v) hs (sz_norm i))
        | _ => h (* fail to add *)
        end
    | cons (HEltVid i) np =>
        match h with
        | HMapEmpty => hsingle p v
        | HMapStr str => HMapStr (hiterStr (hadd np v) (hsingle np v) str i)
        | _ => h (* fail to add *)
        end
    end.

  Fixpoint hupdf (p: hpath) (uf: hmap -> hmap) (h: hmap): hmap :=
    match p with
    | nil => uf h
    | cons (HEltInd i) np =>
        match h with
        | HMapArr hs => HMapArr (hiterArr (hupdf np uf) (uf HMapEmpty) hs (sz_norm i))
        | _ => h (* fail to update *)
        end
    | cons (HEltVid i) np =>
        match h with
        | HMapStr str => HMapStr (hiterStr (hupdf np uf) (uf HMapEmpty) str i)
        | _ => h (* fail to update *)
        end
    end.

  Section HBinary.
    Variable f: hmap -> hmap -> hmap.

    (** Update-oriented iteration *)

    Fixpoint hbinUArr1 (arr1 arr2: list (Z * hmap)) {struct arr1}: list (Z * hmap) :=
      match arr1 with
      | nil => nil
      | cons (vid1, h1) arr1' => cons (vid1, match List.find (fun vh => Z.eqb vid1 (fst vh)) arr2 with
                                             | Some vh2 => f h1 (snd vh2)
                                             | None => h1
                                             end)
                                   (hbinUArr1 arr1' arr2)
      end.

    Definition hbinUArr2 (arr1 arr2: list (Z * hmap)): list (Z * hmap) :=
      List.filter (fun vh2 => negb (List.existsb (fun vh1 => Z.eqb (fst vh1) (fst vh2)) arr1)) arr2.

    Definition hbinUArr (arr1 arr2: list (Z * hmap)): list (Z * hmap) :=
      hbinUArr1 arr1 arr2 ++ hbinUArr2 arr1 arr2.

    Fixpoint hbinUStr1 (str1 str2: list (vid_t * hmap)) {struct str1}: list (vid_t * hmap) :=
      match str1 with
      | nil => nil
      | cons (vid1, h1) str1' => cons (vid1, match List.find (fun vh => vid_eqb vid1 (fst vh)) str2 with
                                             | Some vh2 => f h1 (snd vh2)
                                             | None => h1
                                             end)
                                   (hbinUStr1 str1' str2)
      end.

    Definition hbinUStr2 (str1 str2: list (vid_t * hmap)): list (vid_t * hmap) :=
      List.filter (fun vh2 => negb (List.existsb (fun vh1 => vid_eqb (fst vh1) (fst vh2)) str1)) str2.

    Definition hbinUStr (str1 str2: list (vid_t * hmap)): list (vid_t * hmap) :=
      hbinUStr1 str1 str2 ++ hbinUStr2 str1 str2.

    (** Function-application-oriented iteration *)

    Fixpoint hbinFArr1 (arr1 arr2: list (Z * hmap)) {struct arr1}: list (Z * hmap) :=
      match arr1 with
      | nil => nil
      | cons (vid1, h1) arr1' => cons (vid1, f h1 (match List.find (fun vh => Z.eqb vid1 (fst vh)) arr2 with
                                                   | Some vh2 => snd vh2
                                                   | None => HMapEmpty
                                                   end))
                                   (hbinFArr1 arr1' arr2)
      end.

    Definition hbinFArr2 (arr1 arr2: list (Z * hmap)): list (Z * hmap) :=
      List.map (fun vh2 => (fst vh2, f HMapEmpty (snd vh2)))
        (List.filter (fun vh2 => negb (List.existsb (fun vh1 => Z.eqb (fst vh1) (fst vh2)) arr1)) arr2).

    Definition hbinFArr (arr1 arr2: list (Z * hmap)): list (Z * hmap) :=
      hbinFArr1 arr1 arr2 ++ hbinFArr2 arr1 arr2.

    Fixpoint hbinFStr1 (str1 str2: list (vid_t * hmap)) {struct str1}: list (vid_t * hmap) :=
      match str1 with
      | nil => nil
      | cons (vid1, h1) str1' => cons (vid1, f h1 (match List.find (fun vh => vid_eqb vid1 (fst vh)) str2 with
                                                   | Some vh2 => snd vh2
                                                   | None => HMapEmpty
                                                   end))
                                   (hbinFStr1 str1' str2)
      end.

    Definition hbinFStr2 (str1 str2: list (vid_t * hmap)): list (vid_t * hmap) :=
      List.map (fun vh2 => (fst vh2, f HMapEmpty (snd vh2)))
        (List.filter (fun vh2 => negb (List.existsb (fun vh1 => vid_eqb (fst vh1) (fst vh2)) str1)) str2).

    Definition hbinFStr (str1 str2: list (vid_t * hmap)): list (vid_t * hmap) :=
      hbinFStr1 str1 str2 ++ hbinFStr2 str1 str2.

  End HBinary.

  Fixpoint hupds (h1 h2: hmap) {struct h1}: hmap :=
    match h1 with
    | HMapEmpty => h2
    | HMapBits b1 => HMapBits (match h2 with
                               | HMapEmpty => b1
                               | HMapBits b2 => b2
                               | HMapArr hs2 => b1
                               | HMapStr _ => b1 (* should not happen *)
                               end)
    | HMapArr hs1 => match h2 with
                     | HMapEmpty => h1
                     | HMapBits b2 => h2 (* overwritten by the right *)
                     | HMapArr hs2 => HMapArr (hbinUArr hupds hs1 hs2)
                     | HMapStr _ => h1 (* should not happen *)
                     end
    | HMapStr str1 => match h2 with
                      | HMapEmpty => h1
                      | HMapBits _ => h2 (* overwritten by the right *)
                      | HMapArr _ => h1 (* should not happen *)
                      | HMapStr str2 => HMapStr (hbinUStr hupds str1 str2)
                      end
    end.

  (* NOTE: predicate non-recursive (flat) updates, assuming the each [hmap] is either [HMapStr] or [HMapEmpty]. *)
  Definition phupdsI (pred: bool) (h1 h2: hmap): hmap := if pred then h1 else h2.
  Definition phupds (pred: bool) (h1 h2: hmap): hmap :=
    match h1, h2 with
    | HMapStr str1, HMapStr str2 => HMapStr (hbinFStr (phupdsI pred) str1 str2)
    | HMapEmpty, HMapStr str2 => HMapStr (hbinFStr (phupdsI pred) nil str2)
    | HMapStr str1, HMapEmpty => HMapStr (hbinFStr (phupdsI pred) str1 nil)
    | _, _ => HMapEmpty
    end.

  (* NOTE: also non-recursive (flat); [h2] cannot overwrite [h1]. *)
  Definition hmergeL (h1 h2: hmap): hmap :=
    match h1, h2 with
    | HMapStr str1, HMapStr str2 => HMapStr (str1 ++ hbinUStr2 str1 str2)
    | HMapEmpty, _ => h2
    | _, _ => h1
    end.

  Definition hmergeR (h1 h2: hmap): hmap :=
    match h1, h2 with
    | HMapStr str1, HMapStr str2 => HMapStr (hbinUStr1 (fun _ h2 => h2) str1 str2 ++ hbinUStr2 str1 str2)
    | _, HMapEmpty => h1
    | _, _ => h2
    end.

  Definition hfilterStr (fl: list vid_t) (str: list (vid_t * hmap)): list (vid_t * hmap) :=
    List.filter (fun vh => if List.existsb (fun fvid => vid_eqb (fst vh) fvid) fl
                           then true else false) str.

  Definition hfilter (fl: list vid_t) (h: hmap): hmap :=
    match h with
    | HMapStr str => HMapStr (hfilterStr fl str)
    | _ => h
    end.

  Definition HMapStrEmpty (h: hmap): Prop :=
    match h with
    | HMapBits _ | HMapArr _ => False
    | _ => True
    end.

  Definition KeysUnique (keys: list vid_t): Prop :=
    forall n1 n2,
      n1 <> n2 ->
      forall k1 k2,
        List.nth_error keys n1 = Some k1 ->
        List.nth_error keys n2 = Some k2 ->
        k1 <> k2.

  Definition HMapStrKeysWf (h: hmap) (keys: list vid_t): Prop :=
    match h with
    | HMapStr str =>
        List.map fst str = keys /\ KeysUnique keys
    | _ => False
    end.

  Definition HMapStrEmptyWf (h: hmap): Prop :=
    match h with
    | HMapStr str => KeysUnique (List.map fst str)
    | HMapEmpty => True
    | _ => False
    end.

  Section Facts.

    Section hmap_ind2.
      Variables (P: hmap -> Prop)
        (f0: P HMapEmpty)
        (f1: forall b, P (HMapBits b))
        (f2: forall hs, Forall (fun sh => P (snd sh)) hs -> P (HMapArr hs))
        (f3: forall hs, Forall (fun sh => P (snd sh)) hs -> P (HMapStr hs)).

      Fixpoint hmap_ind2 (h: hmap): P h :=
        match h with
        | HMapEmpty => f0
        | HMapBits b => f1 b
        | HMapArr hs => f2 (list_ind (fun hs => Forall (fun sh => P (snd sh)) hs)
                              (Forall_nil _)
                              (fun sh _ IH => Forall_cons sh (hmap_ind2 (snd sh)) IH) hs)
        | HMapStr hs => f3 (list_ind (fun hs => Forall (fun sh => P (snd sh)) hs)
                              (Forall_nil _)
                              (fun sh _ IH => Forall_cons sh (hmap_ind2 (snd sh)) IH) hs)
        end.
    End hmap_ind2.

    Lemma hpos_not_nil: forall pre vid h p, hpos pre vid h = Some p -> p <> nil.
    Proof using .
      destruct pre; simpl; intros.
      - destruct (haccessO h vid); [|discriminate].
        inv H2; discriminate.
      - destruct (hmove h0 h); [|discriminate].
        destruct (hpos pre vid h1).
        + inv H2; discriminate.
        + destruct (haccessO h0 vid); [|discriminate].
          inv H2; discriminate.
    Qed.

    Lemma hupds_bits: forall h b, hupds h (HMapBits b) = HMapBits b.
    Proof using . destruct h; reflexivity. Qed.

    Lemma HSub_refl: forall h, HSub h h.
    Proof using . intros; red; intros; assumption. Qed.

    Lemma HSub_trans: forall h1 h2, HSub h1 h2 -> forall h3, HSub h2 h3 -> HSub h1 h3.
    Proof using . unfold HSub; intros; eauto. Qed.

    Lemma hmove_app_1:
      forall he hs1 sh,
        hmove (HMapStr hs1) he = Some sh ->
        forall hs2,
          hmove (HMapStr (hs1 ++ hs2)) he = Some sh.
    Proof using .
      destruct he; simpl; intros; [discriminate|].
      clear -H2.
      induction hs1 as [|[k v] hs]; [discriminate|].
      simpl in *.
      destruct (vid_eqb i k); auto.
    Qed.

    Lemma HSub_HMapStr_app_1:
      forall hs1 hs2, HSub (HMapStr hs1) (HMapStr hs2) ->
                      forall hs3, HSub (HMapStr hs1) (HMapStr (hs2 ++ hs3)).
    Proof using .
      unfold HSub; intros.
      specialize (H2 _ H3 _ H4).
      clear -H2 H3.
      destruct p as [|he p]; [elim H3; reflexivity|].
      simpl in *.
      destruct (hmove (HMapStr hs2) he) eqn:Hmv; [|discriminate].
      erewrite hmove_app_1; eauto.
    Qed.

    Lemma HMapStrEmptyWf_HMapStrEmpty:
      forall h, HMapStrEmptyWf h -> HMapStrEmpty h.
    Proof using .
      destruct h; simpl; intros; auto.
    Qed.

    Lemma haccessV_Some:
      forall vs k, haccessV vs k <> None <-> In k (map fst vs).
    Proof using .
      induction vs as [|[vk vv] vs]; simpl; intros.
      - split; intros; [elim H2; reflexivity|exfalso; auto].
      - destruct (vid_eqb k vk) eqn:Hk.
        + apply vid_eqb_eq in Hk; subst.
          split; intros; [left; reflexivity|discriminate].
        + split; intros; [right; apply IHvs; assumption|].
          destruct H2.
          * subst; rewrite vid_eqb_refl in Hk; discriminate.
          * apply IHvs; assumption.
    Qed.

    Lemma haccessV_app:
      forall vs1 vs2 k, haccessV (vs1 ++ vs2) k = match haccessV vs1 k with
                                                  | Some v => Some v
                                                  | None => haccessV vs2 k
                                                  end.
    Proof using .
      induction vs1 as [|[k1 v1] vs1]; simpl; intros; [reflexivity|].
      destruct (vid_eqb k k1); [reflexivity|].
      apply IHvs1.
    Qed.

    Lemma haccessV_None_hbinUStr2:
      forall vs1 k,
        haccessV vs1 k = None ->
        forall vs2, haccessV (hbinUStr2 vs1 vs2) k = haccessV vs2 k.
    Proof using .
      induction vs2 as [|[k2 v2] vs2]; simpl; intros; [reflexivity|].
      destruct (existsb (fun vh1 => vid_eqb (fst vh1) k2) vs1) eqn:Hex; simpl.
      - destruct (vid_eqb k k2) eqn:Hk; [|assumption].
        apply vid_eqb_eq in Hk; subst k2.
        exfalso; clear -H2 Hex.
        induction vs1 as [|[k1 v1] vs1]; simpl in *; [discriminate|].
        destruct (vid_eqb k k1) eqn:Hk; [discriminate|].
        destruct (vid_eqb k1 k) eqn:Hk1; simpl in *.
        + apply vid_eqb_eq in Hk1; subst k1.
          rewrite vid_eqb_refl in Hk; discriminate.
        + apply IHvs1; assumption.
      - destruct (vid_eqb k k2) eqn:Hk; [reflexivity|assumption].
    Qed.

    Lemma haccessV_hbinUStr1_no_effect:
      forall k uvs,
        ~ In k (map fst uvs) ->
        forall f vs,
          haccessV (hbinUStr1 f vs uvs) k = haccessV vs k.
    Proof using .
      induction vs as [|[hk hv] vs]; simpl; intros; [reflexivity|].
      destruct (vid_eqb k hk) eqn:Hk; [|assumption].
      apply vid_eqb_eq in Hk; subst hk.
      destruct (find _ uvs) as [[fk fh]|] eqn:Hfk; [|reflexivity].
      exfalso.
      apply find_some in Hfk; dest; simpl in *.
      apply vid_eqb_eq in H4; subst fk.
      apply in_map with (f:= fst) in H3.
      elim H2; assumption.
    Qed.

    Lemma haccessV_hbinUStr2_None:
      forall k uvs,
        ~ In k (map fst uvs) ->
        forall vs, haccessV (hbinUStr2 vs uvs) k = None.
    Proof using .
      induction uvs as [|[uk uh] uvs]; simpl; intros; [reflexivity|].
      destruct (existsb _ _) eqn:Hex; simpl.
      - eapply IHuvs.
        intro Hx; elim H2.
        right; assumption.
      - destruct (vid_eqb k uk) eqn:Hk.
        + apply vid_eqb_eq in Hk; subst uk.
          elim H2; left; reflexivity.
        + eapply IHuvs.
          intro Hx; elim H2.
          right; assumption.
    Qed.

    Lemma haccessV_None_existsb:
      forall vs k,
        haccessV vs k = None ->
        existsb (fun vh => vid_eqb (fst vh) k) vs = false.
    Proof using .
      induction vs as [|[vk h] vs]; simpl; intros; [reflexivity|].
      destruct (vid_eqb k vk) eqn:Hk.
      - discriminate.
      - destruct (vid_eqb vk k) eqn:Hvk.
        + apply vid_eqb_eq in Hvk; subst vk.
          rewrite vid_eqb_refl in Hk; discriminate.
        + simpl; apply IHvs; assumption.
    Qed.

    Lemma haccessV_existsb_None:
      forall vs k,
        existsb (fun vh => vid_eqb (fst vh) k) vs = false ->
        haccessV vs k = None.
    Proof using .
      induction vs as [|[vk h] vs]; simpl; intros; [reflexivity|].
      destruct (vid_eqb k vk) eqn:Hk.
      - apply vid_eqb_eq in Hk; subst vk.
        rewrite vid_eqb_refl in H2; discriminate.
      - destruct (vid_eqb vk k) eqn:Hvk.
        + apply vid_eqb_eq in Hvk; subst vk.
          rewrite vid_eqb_refl in Hk; discriminate.
        + simpl; apply IHvs; assumption.
    Qed.

    Lemma haccessV_hbinUStr2_Some_None:
      forall vs uvs k v,
        haccessV (hbinUStr2 vs uvs) k = Some v ->
        haccessV vs k = None.
    Proof using .
      induction uvs as [|[uk uh] uvs]; simpl; intros; [discriminate|].
      destruct (existsb _ _) eqn:Hex; simpl in *; [eauto|].
      destruct (vid_eqb k uk) eqn:Hk; eauto.
      apply vid_eqb_eq in Hk; subst uk.
      apply haccessV_existsb_None; assumption.
    Qed.

    Lemma haccessV_hbinUStr2_Some:
      forall vs uvs k v,
        haccessV (hbinUStr2 vs uvs) k = Some v ->
        haccessV uvs k = Some v.
    Proof using .
      induction uvs as [|[uk uh] uvs]; simpl; intros; [discriminate|].
      destruct (existsb _ _) eqn:Hex; simpl in *.
      - destruct (vid_eqb k uk) eqn:Hk; eauto.
        apply vid_eqb_eq in Hk; subst uk.
        apply haccessV_hbinUStr2_Some_None in H2.
        apply haccessV_None_existsb in H2.
        congruence.
      - destruct (vid_eqb k uk) eqn:Hk; eauto.
    Qed.

    Lemma haccessV_hbinUStr_no_effect:
      forall k uvs,
        ~ In k (map fst uvs) ->
        forall vs,
          haccessV vs k = haccessV (hbinUStr hupds vs uvs) k.
    Proof using .
      unfold hbinUStr; intros.
      rewrite haccessV_app.
      rewrite haccessV_hbinUStr1_no_effect by assumption.
      destruct (haccessV vs k); [reflexivity|].
      rewrite haccessV_hbinUStr2_None by assumption.
      reflexivity.
    Qed.

    Lemma hfind_empty: forall p, p <> [] -> hfind p HMapEmpty = None.
    Proof using .
      intros.
      destruct p; [elim H2; reflexivity|].
      simpl; destruct h; simpl; reflexivity.
    Qed.

    Lemma hupds_empty: forall h, hupds h HMapEmpty = h.
    Proof using .
      destruct h; reflexivity.
    Qed.

    Lemma hmergeL_empty: forall h, hmergeL h HMapEmpty = h.
    Proof using .
      destruct h; reflexivity.
    Qed.

    Lemma hmergeR_empty: forall h, hmergeR h HMapEmpty = h.
    Proof using .
      destruct h; reflexivity.
    Qed.

    Lemma hmergeL_HMapStrEmpty:
      forall h1 h2, HMapStrEmpty h1 -> HMapStrEmpty h2 -> HMapStrEmpty (hmergeL h1 h2).
    Proof using .
      destruct h1; simpl; intros; try assumption.
      destruct h2; auto.
    Qed.

    Lemma hmergeR_HMapStrEmpty:
      forall h1 h2, HMapStrEmpty h1 -> HMapStrEmpty h2 -> HMapStrEmpty (hmergeR h1 h2).
    Proof using .
      destruct h1, h2; simpl; intros; try assumption.
    Qed.

    Lemma hmergeL_HSub: forall h1 h2, HSub h1 (hmergeL h1 h2).
    Proof using .
      induction h1 as [| |hs1|hs1] using hmap_ind2; simpl; intros.
      - red; intros.
        rewrite hfind_empty in H3 by assumption; discriminate.
      - apply HSub_refl.
      - apply HSub_refl.
      - destruct h2 as [| | |str2]; [apply HSub_refl..|].
        apply HSub_HMapStr_app_1.
        apply HSub_refl.
    Qed.

    Lemma hbinUStr1_nil: forall f hs, hbinUStr1 f hs nil = hs.
    Proof using .
      induction hs as [|[vid h] hs]; simpl; intros; [reflexivity|].
      rewrite IHhs; reflexivity.
    Qed.

    Lemma hbinUStr1_app_1:
      forall f hs1 hs2 hs3, hbinUStr1 f (hs1 ++ hs2) hs3 = hbinUStr1 f hs1 hs3 ++ hbinUStr1 f hs2 hs3.
    Proof using .
      induction hs1 as [|[vid1 h1] hs1]; simpl; intros; [reflexivity|].
      rewrite IHhs1; reflexivity.
    Qed.

    Lemma hbinUStr1_app_2:
      forall f hs1 hs2 hs3 (Hhs: forall v, In v (map fst hs2) -> In v (map fst hs3) -> False),
        hbinUStr1 f hs1 (hs2 ++ hs3) = hbinUStr1 f (hbinUStr1 f hs1 hs2) hs3.
    Proof using .
      induction hs1 as [|[vid1 h1] hs1]; simpl; intros; [reflexivity|].
      rewrite IHhs1 by assumption.
      rewrite find_app.
      destruct (find _ hs2) eqn:Hf2; [|reflexivity].
      destruct (find _ hs3) eqn:Hf3; [|reflexivity].
      apply find_some in Hf2, Hf3; dest.
      exfalso.
      apply vid_eqb_eq in H5, H3; subst.
      eapply Hhs.
      - apply in_map; eassumption.
      - rewrite H3; apply in_map; eassumption.
    Qed.

    Lemma hbinUStr2_In:
      forall hs1 hs2 h, In h (hbinUStr2 hs1 hs2) -> In h hs2.
    Proof using .
      induction hs2 as [|[vid2 h2] hs2]; simpl; intros; [assumption|].
      destruct (negb _); simpl in *.
      - destruct H2; auto.
      - right; auto.
    Qed.

    Lemma hbinUStr2_In_not:
      forall hs1 hs2 h, In h (hbinUStr2 hs1 hs2) -> ~ In h hs1.
    Proof using .
      unfold hbinUStr2; intros; intro Hx.
      apply filter_In in H2; dest.
      apply Bool.negb_true_iff in H3.
      replace (existsb (fun vh1 : vid_t * hmap => vid_eqb (fst vh1) (fst h)) hs1) with true in H3; [discriminate|].
      apply eq_sym.
      apply existsb_exists.
      exists h; split; [assumption|].
      apply vid_eqb_refl.
    Qed.

    Lemma hbinUStr2_vids_In_not:
      forall hs1 hs2 v, In v (map fst (hbinUStr2 hs1 hs2)) -> ~ In v (map fst hs1).
    Proof using .
      induction hs2 as [|[vid2 h2] hs2]; simpl; intros; [exfalso; auto|].
      destruct (negb _) eqn:Hn; simpl in *.
      - destruct H2; [|auto; fail].
        subst.
        apply Bool.negb_true_iff in Hn.
        rewrite existsb_false_forall in Hn.
        intro Hx.
        apply in_map_iff in Hx; dest; subst.
        specialize (Hn _ H3).
        rewrite vid_eqb_refl in Hn; discriminate.
      - apply IHhs2; assumption.
    Qed.

    Lemma hbinUStr2_nil:
      forall h, hbinUStr2 nil h = h.
    Proof using .
      unfold hbinUStr2; induction h; simpl; intros; [reflexivity|].
      simpl in IHh; congruence.
    Qed.

    Lemma hbinUStr2_app_1:
      forall h1 h2 h3, hbinUStr2 (h1 ++ h2) h3 = hbinUStr2 h1 (hbinUStr2 h2 h3).
    Proof using .
      induction h3; simpl; intros; [reflexivity|].
      rewrite existsb_app.
      destruct (existsb _ h2); simpl.
      all: destruct (existsb _ _); simpl; congruence.
    Qed.

    Lemma hbinUStr2_app_2:
      forall h1 h2 h3, hbinUStr2 h1 (h2 ++ h3) = hbinUStr2 h1 h2 ++ hbinUStr2 h1 h3.
    Proof using .
      unfold hbinUStr2; intros.
      rewrite <-filter_app; reflexivity.
    Qed.

    Lemma hbinUStr2_existsb_eq:
      forall h1 h2,
        (forall v, existsb (fun vh => vid_eqb (fst vh) v) h1 = existsb (fun vh => vid_eqb (fst vh) v) h2) ->
        forall h, hbinUStr2 h1 h = hbinUStr2 h2 h.
    Proof using .
      induction h; simpl; intros; [reflexivity|].
      rewrite H2, IHh.
      reflexivity.
    Qed.

    Lemma hbinUStr2_nil_1:
      forall vs1 vs2,
        (forall v, In v (map fst vs2) -> haccessV vs1 v <> None) ->
        hbinUStr2 vs1 vs2 = nil.
    Proof using .
      induction vs2 as [|[k2 v2] vs2]; simpl; intros; [reflexivity|].
      destruct (existsb (fun vh1 : vid_t * hmap => vid_eqb (fst vh1) k2) vs1) eqn:Hk2; simpl.
      - apply IHvs2; intros.
        apply H2; right; assumption.
      - exfalso.
        rewrite existsb_false_forall in Hk2.
        specialize (H2 k2 (or_introl eq_refl)); elim H2.
        clear -Hk2; induction vs1 as [|[k1 v1] vs1]; simpl in *; [reflexivity|].
        destruct (vid_eqb k2 k1) eqn:Hk1.
        + apply vid_eqb_eq in Hk1; subst k2.
          specialize (Hk2 (k1, v1) (or_introl eq_refl)); simpl in Hk2.
          rewrite vid_eqb_refl in Hk2; discriminate.
        + apply IHvs1; intros.
          apply Hk2; right; assumption.
    Qed.

    Lemma hbinUStr1_disj:
      forall f hs1 hs2 (Hhs: forall v, In v (map fst hs1) -> In v (map fst hs2) -> False),
        hbinUStr1 f hs1 hs2 = hs1.
    Proof using .
      induction hs1 as [|[vid1 h1] hs1]; simpl; intros; [reflexivity|].
      destruct (find _ hs2) as [[fvid fh]|] eqn:Hhs2.
      - exfalso.
        apply find_some in Hhs2; dest; simpl in *.
        apply vid_eqb_eq in H3; subst fvid.
        eapply Hhs; [left; reflexivity|].
        apply in_map with (f:= fst) in H2; assumption.
      - rewrite IHhs1; [reflexivity|].
        intros; eapply Hhs; [right; eassumption|eassumption].
    Qed.

    Lemma hbinUStr2_disj:
      forall hs1 hs2 (Hhs: forall v, In v (map fst hs1) -> In v (map fst hs2) -> False),
        hbinUStr2 hs1 hs2 = hs2.
    Proof using .
      induction hs2 as [|[vid2 h2] hs2]; simpl; intros; [reflexivity|].
      destruct (existsb _ _) eqn:Hex1; simpl.
      - exfalso.
        apply existsb_exists in Hex1.
        destruct Hex1 as [[evid eh] [? ?]]; simpl in *.
        apply vid_eqb_eq in H3; subst evid.
        eapply Hhs.
        + apply in_map; eassumption.
        + left; reflexivity.
      - rewrite IHhs2; [reflexivity|].
        intros; eapply Hhs; [eassumption|].
        right; assumption.
    Qed.

    Lemma hbinUStr_disj:
      forall f hs1 hs2 (Hhs: forall v, In v (map fst hs1) -> In v (map fst hs2) -> False),
        hbinUStr f hs1 hs2 = hs1 ++ hs2.
    Proof using .
      unfold hbinUStr; intros.
      rewrite hbinUStr1_disj, hbinUStr2_disj by assumption.
      reflexivity.
    Qed.

    Lemma hbinUStr1_vids_eq:
      forall f hs1 hs2,
        List.map fst (hbinUStr1 f hs1 hs2) = List.map fst hs1.
    Proof using .
      induction hs1 as [|[vid1 h1] hs1]; simpl; intros; [reflexivity|].
      rewrite IHhs1; reflexivity.
    Qed.

    Lemma existsb_vid_hbinUStr1_eq:
      forall f tvid hs1 hs2,
        existsb (fun vh => vid_eqb (fst vh) tvid) hs1 =
          existsb (fun vh => vid_eqb (fst vh) tvid) (hbinUStr1 f hs1 hs2).
    Proof using .
      induction hs1 as [|[vid1 h1] hs1]; simpl; intros; [reflexivity|].
      rewrite <-IHhs1.
      reflexivity.
    Qed.

    Lemma haccessV_hbinUStr1_hupds_Some:
      forall vs k,
        haccessV vs k <> None ->
        forall uvs,
          haccessV (hbinUStr1 hupds vs uvs) k <> None.
    Proof using .
      intros.
      apply haccessV_Some in H2.
      apply haccessV_Some.
      induction vs as [|[vk vv] vs]; simpl; intros; [elim H2|].
      destruct H2; simpl in *; [auto; fail|].
      auto.
    Qed.

    Lemma haccessV_hbinUStr_hupds_Some:
      forall vs k,
        haccessV vs k <> None ->
        forall uvs,
          haccessV (hbinUStr hupds vs uvs) k <> None.
    Proof using .
      intros.
      unfold hbinUStr; rewrite haccessV_app.
      destruct (haccessV (hbinUStr1 hupds vs uvs) k) eqn:Hk; [discriminate|].
      eapply haccessV_hbinUStr1_hupds_Some in H2.
      elim H2; eassumption.
    Qed.

    Lemma haccessV_find:
      forall vs k nv,
        match find (fun vh => vid_eqb k (fst vh)) vs with
        | Some vh => snd vh
        | None => nv
        end = match haccessV vs k with
              | Some uh => uh
              | None => nv
              end.
    Proof using .
      induction vs as [|[hk hv] vs]; simpl; intros; [reflexivity|].
      destruct (vid_eqb k hk) eqn:Hk; auto.
    Qed.

    Lemma haccessV_find_Some:
      forall vs k h,
        find (fun vh => vid_eqb k (fst vh)) vs = Some h ->
        k = fst h /\ haccessV vs k = Some (snd h).
    Proof using .
      induction vs as [|[hk hv] vs]; simpl; intros; [discriminate|].
      destruct (vid_eqb k hk) eqn:Hk; auto.
      inv H2; split.
      - apply vid_eqb_eq in Hk; subst; reflexivity.
      - reflexivity.
    Qed.

    Lemma haccessV_In:
      forall vs k, haccessV vs k <> None <-> In k (map fst vs).
    Proof using .
      induction vs as [|[hk hv] vs]; simpl; intros.
      - split; intros; [elim H2; reflexivity|exfalso; assumption].
      - destruct (vid_eqb k hk) eqn:Hk.
        + apply vid_eqb_eq in Hk; subst hk.
          split; intros; [left; reflexivity|discriminate].
        + split; intros.
          * right; apply IHvs; assumption.
          * destruct H2.
            { subst hk; rewrite vid_eqb_refl in Hk; discriminate. }
            { apply IHvs; assumption. }
    Qed.

    Lemma haccessV_hbinUStr1_hmergeR:
      forall vs uvs k,
        haccessV (hbinUStr1 (fun _ h2 => h2) vs uvs) k =
          match haccessV vs k with
          | Some h => match haccessV uvs k with
                      | Some uh => Some uh
                      | None => Some h
                      end
          | None => None
          end.
    Proof using .
      induction vs as [|[hk hv] vs]; simpl; intros; [reflexivity|].
      destruct (vid_eqb k hk) eqn:Hk.
      - apply vid_eqb_eq in Hk; subst hk.
        rewrite haccessV_find.
        destruct (haccessV uvs k); reflexivity.
      - auto.
    Qed.

    Lemma hbinUStr_assoc:
      forall hs1 hs2 hs3 (Hhs: forall v, In v (map fst hs2) -> In v (map fst hs3) -> False),
        hbinUStr hupds hs1 (hs2 ++ hs3) = hbinUStr hupds (hbinUStr hupds hs1 hs2) hs3.
    Proof using .
      intros.
      unfold hbinUStr.
      rewrite !hbinUStr2_app_1.
      rewrite !hbinUStr2_app_2.
      rewrite !hbinUStr1_app_1.
      rewrite !hbinUStr1_app_2 by assumption.
      rewrite <-!app_assoc.
      do 2 f_equal.

      - induction hs2 as [|[vid2 h2] hs2]; simpl; intros; [reflexivity|].
        destruct (negb _) eqn:Hex1; simpl.
        + destruct (find _ _) as [[vid3 h3]|] eqn:Hf3; simpl in *.
          * exfalso.
            apply find_some in Hf3; dest; simpl in *.
            apply vid_eqb_eq in H3; subst vid2.
            eapply Hhs.
            { left; reflexivity. }
            { apply in_map with (f:= fst) in H2; assumption. }
          * rewrite IHhs2 at 1; [reflexivity|].
            intros.
            eapply Hhs; [right; eassumption|].
            assumption.
        + apply IHhs2.
          intros.
          eapply Hhs; [right; eassumption|].
          assumption.

      - induction hs3 as [|[vid3 h3] hs3]; simpl; intros; [reflexivity|].
        destruct (existsb _ hs1) eqn:Hex1; simpl.
        + destruct (existsb _ (hbinUStr2 hs1 hs2)) eqn:Hex2; simpl.
          * eapply IHhs3.
            intros; eapply Hhs; [eassumption|].
            right; assumption.
          * destruct (existsb _ (hbinUStr1 hupds hs1 hs2)) eqn:Hex3; simpl.
            { apply IHhs3.
              intros; eapply Hhs; [eassumption|].
              right; assumption.
            }
            { rewrite <-existsb_vid_hbinUStr1_eq in Hex3; congruence. }

        + destruct (existsb _ (hbinUStr2 hs1 hs2)) eqn:Hex2; simpl.
          * exfalso.
            clear -Hex2 Hhs.
            apply existsb_exists in Hex2.
            destruct Hex2 as [[evid eh] [? ?]]; simpl in *; dest.
            apply vid_eqb_eq in H2; subst evid.
            induction hs2 as [|[vid2 h2] hs2]; simpl in *; [assumption|].
            destruct (existsb _ hs1) eqn:Hex1; simpl in *.
            { eapply IHhs2; eauto. }
            { destruct H.
              { inv H2; eapply Hhs; eauto. }
              { eapply IHhs2; eauto. }
            }
          * destruct (existsb _ (hbinUStr1 hupds hs1 hs2)) eqn:Hex3; simpl.
            { rewrite <-existsb_vid_hbinUStr1_eq in Hex3; congruence. }
            { rewrite IHhs3; [reflexivity|].
              intros; eapply Hhs; [eassumption|].
              right; assumption.
            }
    Qed.

    Lemma HDisj_sym: forall h1 h2, HDisj h1 h2 -> HDisj h2 h1.
    Proof using .
      unfold HDisj; intros.
      destruct h1, h2; eauto.
    Qed.

    Lemma hupds_hmergeL_assoc:
      forall h1 h2 h3,
        HMapStrEmpty h2 ->
        HMapStrEmpty h3 ->
        HDisj h2 h3 ->
        hupds h1 (hmergeL h2 h3) = hupds (hupds h1 h2) h3.
    Proof using .
      destruct h1 as [|b1|hs1|hs1], h2 as [|b2|hs2|hs2], h3 as [|b3|hs3|hs3]; intros; simpl.
      all: try reflexivity.
      all: try (exfalso; auto; fail).
      - rewrite hbinUStr2_disj by assumption.
        rewrite hbinUStr_disj by assumption.
        reflexivity.
      - rewrite <-hbinUStr_assoc by assumption.
        rewrite hbinUStr2_disj by assumption.
        reflexivity.
    Qed.

    Lemma hupds_hmergeR_assoc:
      forall h1 h2 h3,
        HMapStrEmpty h2 ->
        HMapStrEmpty h3 ->
        HDisj h2 h3 ->
        hupds h1 (hmergeR h2 h3) = hupds (hupds h1 h2) h3.
    Proof using .
      destruct h1 as [|b1|hs1|hs1], h2 as [|b2|hs2|hs2], h3 as [|b3|hs3|hs3]; intros; simpl.
      all: try reflexivity.
      all: try (exfalso; auto; fail).
      - rewrite hbinUStr1_disj by assumption.
        rewrite hbinUStr2_disj by assumption.
        rewrite hbinUStr_disj by assumption.
        reflexivity.
      - rewrite <-hbinUStr_assoc by assumption.
        rewrite hbinUStr1_disj by assumption.
        rewrite hbinUStr2_disj by assumption.
        reflexivity.
    Qed.

    Lemma KeysUnique_cons:
      forall key keys,
        KeysUnique (key :: keys) ->
        KeysUnique keys.
    Proof using .
      unfold KeysUnique; intros.
      eapply (H2 (S n1) (S n2)); try assumption.
      congruence.
    Qed.

    Lemma KeysUnique_cons_not_In:
      forall key keys,
        KeysUnique (key :: keys) ->
        ~ In key keys.
    Proof using .
      induction keys as [|ikey keys]; simpl; intros; [auto; fail|].
      intro Hx; destruct Hx.
      - subst ikey.
        specialize (H2 0 1 ltac:(discriminate) _ _ eq_refl eq_refl); simpl in H2.
        elim H2; reflexivity.
      - generalize H3; apply IHkeys.
        red; intros.
        destruct n1, n2.
        + auto; fail.
        + specialize (H2 0 (S (S n2)) ltac:(discriminate) _ _ H5 H6); assumption.
        + specialize (H2 (S (S n1)) 0 ltac:(discriminate) _ _ H5 H6); assumption.
        + specialize (H2 (S (S n1)) (S (S n2)) ltac:(congruence) _ _ H5 H6); assumption.
    Qed.

    Lemma KeysUnique_cons_spec:
      forall keys,
        KeysUnique keys ->
        forall key,
          ~ In key keys ->
          KeysUnique (key :: keys).
    Proof using .
      unfold KeysUnique; intros.
      destruct n1, n2; simpl in *.
      - elim H4; reflexivity.
      - inv H5; intro Hx; subst.
        elim H3.
        eapply nth_error_In; eassumption.
      - inv H6; intro Hx; subst.
        elim H3.
        eapply nth_error_In; eassumption.
      - eapply H2; [|eassumption..].
        lia.
    Qed.

    Lemma KeysUnique_cons_haccessV:
      forall key vs,
        KeysUnique (key :: List.map fst vs) ->
        haccessV vs key = None.
    Proof using .
      induction vs as [|[hk hv] vs]; simpl; intros; [reflexivity|].
      destruct (vid_eqb key hk) eqn:Hk.
      - exfalso.
        apply vid_eqb_eq in Hk; subst hk.
        specialize (H2 0 1 ltac:(discriminate) _ _ eq_refl eq_refl).
        elim H2; reflexivity.
      - apply IHvs.
        red; intros.
        destruct n1, n2.
        + auto; fail.
        + specialize (H2 0 (S (S n2)) ltac:(discriminate) _ _ H4 H5); assumption.
        + specialize (H2 (S (S n1)) 0 ltac:(discriminate) _ _ H4 H5); assumption.
        + specialize (H2 (S (S n1)) (S (S n2)) ltac:(congruence) _ _ H4 H5); assumption.
    Qed.

    Lemma KeysUnique_app:
      forall keys1,
        KeysUnique keys1 ->
        forall keys2,
          KeysUnique keys2 ->
          (forall n1 k1 n2 k2, nth_error keys1 n1 = Some k1 -> nth_error keys2 n2 = Some k2 -> k1 <> k2) ->
          KeysUnique (keys1 ++ keys2).
    Proof using .
      unfold KeysUnique; intros.
      destruct (Compare_dec.le_lt_dec (length keys1) n1), (Compare_dec.le_lt_dec (length keys1) n2).
      - rewrite nth_error_app2 in H6 by assumption.
        rewrite nth_error_app2 in H7 by assumption.
        eapply H3; [|eassumption..].
        lia.
      - rewrite nth_error_app2 in H6 by assumption.
        rewrite nth_error_app1 in H7 by assumption.
        specialize (H4 _ _ _ _ H7 H6); congruence.
      - rewrite nth_error_app1 in H6 by assumption.
        rewrite nth_error_app2 in H7 by assumption.
        specialize (H4 _ _ _ _ H6 H7); congruence.
      - rewrite nth_error_app1 in H6 by assumption.
        rewrite nth_error_app1 in H7 by assumption.
        eapply H2; eassumption.
    Qed.

    Lemma KeysUnique_filter:
      forall keys,
        KeysUnique keys ->
        forall f,
          KeysUnique (List.filter f keys).
    Proof using .
      induction keys; simpl; intros; [assumption|].
      destruct (f a).
      - apply KeysUnique_cons_spec.
        + apply IHkeys.
          eapply KeysUnique_cons; eassumption.
        + intro Hx.
          apply filter_In in Hx; dest.
          eapply KeysUnique_cons_not_In in H2; auto.
      - apply IHkeys.
        eapply KeysUnique_cons; eassumption.
    Qed.

    Lemma KeysUnique_hbinUStr2:
      forall hs1 hs2,
        KeysUnique (List.map fst hs2) ->
        KeysUnique (List.map fst (hbinUStr2 hs1 hs2)).
    Proof using .
      induction hs2; simpl; intros; [assumption|].
      destruct (negb _); simpl.
      - apply KeysUnique_cons_spec.
        + apply IHhs2.
          eapply KeysUnique_cons; eassumption.
        + intro Hx.
          apply in_map_iff in Hx; dest.
          apply hbinUStr2_In in H4.
          apply in_map with (f:= fst) in H4.
          rewrite H3 in H4.
          eapply KeysUnique_cons_not_In in H2; auto.
      - apply IHhs2.
        eapply KeysUnique_cons; eassumption.
    Qed.

    Lemma HMapStrEmptyWf_hmergeR:
      forall h1 h2,
        HMapStrEmptyWf h1 -> HMapStrEmptyWf h2 ->
        HMapStrEmptyWf (hmergeR h1 h2).
    Proof using .
      destruct h1 as [|b1|hs1|hs1], h2 as [|b2|hs2|hs2]; simpl; intros; auto.
      rewrite map_app.
      apply KeysUnique_app.
      - rewrite hbinUStr1_vids_eq; assumption.
      - apply KeysUnique_hbinUStr2; assumption.
      - intros.
        apply nth_error_In in H4, H5.
        intro Hx; subst k2.
        apply hbinUStr2_vids_In_not in H5.
        rewrite hbinUStr1_vids_eq in H4; auto.
    Qed.

    Lemma HMapStrKeysWf_hupds_no_effect:
      forall h keys,
        HMapStrKeysWf h keys ->
        forall uhs,
          (forall v, In v (map fst uhs) -> hfind [HEltVid v] h <> None) ->
          HMapStrKeysWf (hupds h (HMapStr uhs)) keys.
    Proof using .
      unfold HMapStrKeysWf; intros.
      destruct h as [| | |hs]; try (exfalso; auto; fail).
      dest; simpl in *; subst keys.
      split; [|assumption].
      unfold hbinUStr.
      rewrite hbinUStr2_nil_1.
      - rewrite app_nil_r.
        clear; induction hs as [|[hk hh] hs]; simpl; [reflexivity|].
        congruence.
      - intros.
        specialize (H3 _ H2).
        destruct (haccessV hs v); assumption.
    Qed.

    Lemma HMapStrKeysWf_hfind_eq:
      forall keys h1 h2,
        HMapStrKeysWf h1 keys ->
        HMapStrKeysWf h2 keys ->
        (forall v, hfind [HEltVid v] h1 = hfind [HEltVid v] h2) ->
        h1 = h2.
    Proof using .
      destruct h1 as [|b1|hs1|hs1], h2 as [|b2|hs2|hs2]; intros; simpl.
      all: try (exfalso; auto; fail).
      generalize dependent hs2.
      generalize dependent keys.
      induction hs1 as [|[vid1 h1] hs1]; simpl; intros;
        [destruct hs2; [reflexivity|]; dest; subst; discriminate|].
      dest; destruct hs2 as [|[vid2 h2] hs2]; simpl in *;
        [subst; discriminate|].
      destruct keys as [|key keys]; [discriminate|].
      inv H2; inv H3; do 2 f_equal.
      - specialize (H4 key).
        rewrite vid_eqb_refl in H4; inv H4.
        reflexivity.
      - assert (HMapStr hs1 = HMapStr hs2) as Hhs.
        { eapply IHhs1.
          { split; [reflexivity|eapply KeysUnique_cons; eassumption]. }
          { split; [assumption|eapply KeysUnique_cons; eassumption]. }
          { intros; specialize (H4 v).
            destruct (vid_eqb v key) eqn:Hv; [|assumption].
            apply vid_eqb_eq in Hv; subst v.
            rewrite KeysUnique_cons_haccessV by assumption.
            rewrite KeysUnique_cons_haccessV; [reflexivity|].
            rewrite H8; assumption.
          }
        }
        inv Hhs; reflexivity.
    Qed.

    Lemma hfind_hupds_Some:
      forall h v,
        hfind [HEltVid v] h <> None ->
        forall uh (Huh: HMapStrEmpty uh),
          hfind [HEltVid v] (hupds h uh) <> None.
    Proof using .
      destruct h as [|b|hs|hs], uh as [|ub|uhs|uhs]; simpl; intros.
      all: try (exfalso; auto; fail).
      all: try assumption.
      simpl in *.
      unfold hbinUStr.
      rewrite haccessV_app.
      destruct (haccessV (hbinUStr1 _ _ _) _) eqn:Hv; [discriminate|].
      exfalso; eapply haccessV_hbinUStr1_hupds_Some; [|eassumption].
      destruct (haccessV hs v); [discriminate|assumption].
    Qed.

    Lemma hmergeL_assoc:
      forall h1 h2 h3,
        HMapStrEmpty h2 ->
        hmergeL (hmergeL h1 h2) h3 = hmergeL h1 (hmergeL h2 h3).
    Proof using .
      destruct h1 as [|b1|hs1|hs1], h2 as [|b2|hs2|hs2], h3 as [|b3|hs3|hs3]; intros; simpl.
      all: try reflexivity.
      all: try (exfalso; auto; fail).
      f_equal.
      generalize dependent hs3; generalize dependent hs1.
      induction hs2; simpl; intros; [rewrite app_nil_r, hbinUStr2_nil; reflexivity|].
      destruct (existsb _ _) eqn:Hin; simpl.
      - rewrite IHhs2 by auto; f_equal.
        rewrite !hbinUStr2_app_2; f_equal.
        rewrite <-!hbinUStr2_app_1.
        apply hbinUStr2_existsb_eq; clear -Hin; intros.
        replace (hs1 ++ a :: hs2) with (hs1 ++ [a] ++ hs2) by reflexivity.
        rewrite !existsb_app.
        rewrite Bool.orb_assoc; f_equal; simpl.
        destruct (vid_eq_dec (fst a) v); subst; simpl.
        + rewrite Hin; reflexivity.
        + rewrite vid_eqb_not by assumption.
          rewrite !Bool.orb_false_r; reflexivity.
      - rewrite <-app_assoc; f_equal.
        simpl; f_equal.
        rewrite hbinUStr2_app_2; f_equal.
        rewrite <-hbinUStr2_app_1.
        apply hbinUStr2_existsb_eq; clear -Hin; intros.
        replace (hs1 ++ a :: hbinUStr2 hs1 hs2) with (hs1 ++ [a] ++ hbinUStr2 hs1 hs2) by reflexivity.
        replace (hs1 ++ a :: hs2) with (hs1 ++ [a] ++ hs2) by reflexivity.
        rewrite !existsb_app; simpl.
        destruct (vid_eq_dec (fst a) v); subst; simpl.
        + rewrite vid_eqb_refl; reflexivity.
        + rewrite vid_eqb_not by assumption; simpl.
          clear Hin.
          destruct (existsb (fun vh : vid_t * hmap => vid_eqb (fst vh) v) hs1) eqn:Hin; simpl; [reflexivity|].
          destruct (existsb (fun vh : vid_t * hmap => vid_eqb (fst vh) v) (hbinUStr2 hs1 hs2)) eqn:Hin0;
            destruct (existsb (fun vh : vid_t * hmap => vid_eqb (fst vh) v) hs2) eqn:Hin1.
          all: try reflexivity.
          * apply existsb_exists in Hin0.
            destruct Hin0 as [[ve he] [? ?]]; simpl in *.
            apply filter_In in H; destruct H; simpl in *.
            unfold vid_eqb in H2; destruct (vid_eq_dec ve v); [subst|discriminate].
            rewrite existsb_In with (a:= (v, he)) in Hin1; [|assumption|apply vid_eqb_refl].
            discriminate.
          * apply existsb_exists in Hin1.
            destruct Hin1 as [[ve he] [? ?]]; simpl in *.
            unfold vid_eqb in H2; destruct (vid_eq_dec ve v); [subst|discriminate].
            rewrite existsb_In with (a:= (v, he)) in Hin0; [discriminate| |apply vid_eqb_refl].
            apply filter_In; split; [assumption|].
            simpl; rewrite Hin; reflexivity.
    Qed.

    Lemma hmergeR_str_disj:
      forall hs1 hs2,
        HDisj (HMapStr hs1) (HMapStr hs2) ->
        hmergeR (HMapStr hs1) (HMapStr hs2) = HMapStr (hs1 ++ hs2).
    Proof using .
      simpl; intros.
      rewrite <-hbinUStr_disj with (hs1:= hs1) (hs2:= hs2) (f:= fun _ h2 => h2) by assumption.
      reflexivity.
    Qed.

    Lemma hmergeR_assoc:
      forall h1 h2 h3,
        HMapStrEmpty h2 ->
        HDisj h2 h3 ->
        hmergeR (hmergeR h1 h2) h3 = hmergeR h1 (hmergeR h2 h3).
    Proof using .
      destruct h1 as [|b1|hs1|hs1], h2 as [|b2|hs2|hs2], h3 as [|b3|hs3|hs3]; intros.
      all: try reflexivity.
      all: try (exfalso; auto; fail).

      rewrite hmergeR_str_disj with (hs1:= hs2) (hs2:= hs3) by assumption.
      simpl; f_equal.
      rewrite !hbinUStr1_app_1, !hbinUStr2_app_1, !hbinUStr2_app_2.
      rewrite <-app_assoc; f_equal; [apply eq_sym, hbinUStr1_app_2; assumption|].
      f_equal.
      - apply hbinUStr1_disj.
        intros; eapply H3; [|eassumption].
        clear -H4.
        induction hs2 as [|h2 hs2]; simpl in *; [assumption|].
        destruct (negb _).
        + inv H4; [left; reflexivity|].
          right; apply IHhs2; assumption.
        + right; apply IHhs2; assumption.
      - replace (hbinUStr2 (hbinUStr2 hs1 hs2) hs3) with hs3.
        + clear; induction hs3 as [|h3 hs3]; simpl; [reflexivity|].
          replace (existsb (fun vh1 => vid_eqb (fst vh1) (fst h3)) (hbinUStr1 (fun _ h2 => h2) hs1 hs2))
            with (existsb (fun vh1 : vid_t * hmap => vid_eqb (fst vh1) (fst h3)) hs1).
          * destruct (negb _); congruence.
          * pose proof (hbinUStr1_vids_eq (fun _ h2 => h2) hs1 hs2) as Hv.
            clear -Hv.
            induction hs1 as [|[k1 h1] hs1]; simpl in *; [reflexivity|].
            f_equal.
            apply IHhs1; congruence.
        + apply eq_sym, hbinUStr2_disj.
          intros; eapply H3; [|eassumption].
          clear -H4.
          induction hs2 as [|h2 hs2]; simpl in *; [assumption|].
          destruct (negb _).
          * inv H4; [left; reflexivity|].
            right; apply IHhs2; assumption.
          * right; apply IHhs2; assumption.
    Qed.

    Lemma hmergeL_hfind:
      forall h1 h2,
        HMapStrEmpty h1 ->
        HMapStrEmpty h2 ->
        forall v,
          hfind [HEltVid v] (hmergeL h1 h2) = match hfind [HEltVid v] h1 with
                                              | Some v => Some v
                                              | None => hfind [HEltVid v] h2
                                              end.
    Proof using .
      destruct h1; intros; try (exfalso; auto; fail).
      - rewrite hfind_empty by discriminate.
        reflexivity.
      - destruct h2; try (exfalso; auto; fail).
        + rewrite hmergeL_empty.
          destruct (hfind [HEltVid v] (HMapStr str)); [reflexivity|].
          rewrite hfind_empty by discriminate.
          reflexivity.
        + simpl; clear.
          rewrite haccessV_app.
          destruct (haccessV str v) eqn:Hstr; [reflexivity|].
          rewrite haccessV_None_hbinUStr2 by assumption.
          reflexivity.
    Qed.

    Lemma hmergeR_hfind:
      forall h1 h2,
        HMapStrEmpty h1 ->
        HMapStrEmpty h2 ->
        forall v,
          hfind [HEltVid v] (hmergeR h1 h2) = match hfind [HEltVid v] h2 with
                                              | Some v => Some v
                                              | None => hfind [HEltVid v] h1
                                              end.
    Proof using .
      destruct h2; intros; try (exfalso; auto; fail).
      - rewrite hfind_empty by discriminate.
        rewrite hmergeR_empty; reflexivity.
      - destruct h1; try (exfalso; auto; fail).
        + unfold hmergeR.
          destruct (hfind [HEltVid v] (HMapStr str)); [reflexivity|].
          rewrite hfind_empty by discriminate.
          reflexivity.
        + simpl; clear.
          rewrite haccessV_app.
          rewrite haccessV_hbinUStr1_hmergeR.
          destruct (haccessV str0 v) eqn:Hstr0.
          * destruct (haccessV str v) eqn:Hstr; reflexivity.
          * destruct (haccessV (hbinUStr2 str0 str) v) eqn:Hstr2.
            { erewrite haccessV_hbinUStr2_Some by eassumption; reflexivity. }
            { rewrite haccessV_None_hbinUStr2 in Hstr2 by assumption.
              rewrite Hstr2; reflexivity.
            }
    Qed.

    Lemma hbinUStr1_hmergeR_absorbed:
      forall vs uvs,
        (forall vh, In vh vs ->
                    match find (fun uvh => vid_eqb (fst vh) (fst uvh)) uvs with
                    | Some uvh => vh = uvh
                    | _ => True
                    end) ->
        hbinUStr1 (fun _ h2 => h2) vs uvs = vs.
    Proof using .
      induction vs as [|[vk vv] vs]; simpl; intros; [reflexivity|].
      f_equal.
      - f_equal.
        specialize (H2 _ (or_introl eq_refl)); simpl in H2.
        destruct (find _ uvs); [|reflexivity].
        subst p; reflexivity.
      - apply IHvs.
        intros; apply H2.
        right; assumption.
    Qed.

    Lemma haccessV_KeysUnique:
      forall vs,
        KeysUnique (List.map fst vs) ->
        forall v h,
          In (v, h) vs ->
          haccessV vs v = Some h.
    Proof using .
      induction vs as [|[vk vv] vs]; simpl; intros; [exfalso; auto|].
      destruct (vid_eqb v vk) eqn:Hv.
      - apply vid_eqb_eq in Hv; subst vk.
        destruct H3; [inv H3; reflexivity|].
        exfalso.
        apply KeysUnique_cons_not_In in H2.
        apply in_map with (f:= fst) in H3; auto.
      - apply IHvs.
        + eapply KeysUnique_cons; eassumption.
        + destruct H3; [|assumption].
          inv H3.
          rewrite vid_eqb_refl in Hv; discriminate.
    Qed.

    Lemma hmergeR_absorbed:
      forall vs,
        KeysUnique (List.map fst vs) ->
        forall uvs,
          (forall v, In v (map fst uvs) -> hfind [HEltVid v] (HMapStr vs) = hfind [HEltVid v] (HMapStr uvs)) ->
          hmergeR (HMapStr vs) (HMapStr uvs) = HMapStr vs.
    Proof using .
      intros; simpl; f_equal.
      rewrite hbinUStr1_hmergeR_absorbed.
      - rewrite hbinUStr2_nil_1; [apply app_nil_r|].
        simpl in *; intros.
        specialize (H3 _ H4).
        destruct (haccessV vs v) eqn:Hvs, (haccessV uvs v) eqn:Huvs; try discriminate.
        apply haccessV_In in Huvs; [|assumption].
        elim Huvs.

      - intros.
        destruct (find _ uvs) as [[uv uh]|] eqn:Huf; [|auto; fail].
        destruct vh as [v h]; simpl in *.
        apply haccessV_find_Some in Huf; dest; simpl in *; subst uv.
        assert (In v (map fst uvs)) as Hin by (apply haccessV_In; congruence).
        specialize (H3 _ Hin).
        rewrite H6 in H3.
        apply haccessV_KeysUnique in H4; [|assumption].
        rewrite H4 in H3.
        inv H3; reflexivity.
    Qed.

    Lemma hbinUStr2_absorbed_inv:
      forall hs hs1 hs2, hs ++ hbinUStr2 hs1 hs2 = hs1 -> hbinUStr2 hs1 hs2 = nil.
    Proof using .
      intros.
      destruct (hbinUStr2 hs1 hs2) as [|fh2 fhs2] eqn:Hs; [reflexivity|].
      assert (In fh2 hs1) as Hex.
      { subst hs1; apply in_or_app; right; left; reflexivity. }
      exfalso.
      eapply hbinUStr2_In_not; [|eassumption].
      rewrite Hs; left; reflexivity.
    Qed.

    Lemma hbinUStr1_absorbed_inv:
      forall hs1 hs2 hs3,
        (forall v, In v (map fst hs2) -> In v (map fst hs3) -> False) ->
        hbinUStr1 (fun _ h2 => h2) hs1 (hs2 ++ hs3) = hs1 ->
        hbinUStr1 (fun _ h2 => h2) hs1 hs2 = hs1.
    Proof using .
      induction hs1 as [|[vid1 h1] hs1]; simpl; intros; [reflexivity|].
      rewrite find_app in H3.
      destruct (find _ hs2) as [[vid2 h2]|] eqn:Hf2; simpl in *.
      - rewrite IHhs1 with (hs3:= hs3); [|assumption|].
        all: congruence.
      - rewrite IHhs1 with (hs3:= hs3); [|assumption|].
        all: congruence.
    Qed.

    Lemma hmergeR_absorbed_left_str:
      forall hs1 hs2 hs3,
        HDisj (HMapStr hs2) (HMapStr hs3) ->
        hmergeR (HMapStr hs1) (HMapStr (hs2 ++ hs3)) = HMapStr hs1 ->
        hmergeR (HMapStr hs1) (HMapStr hs2) = HMapStr hs1.
    Proof using .
      simpl; intros; f_equal.
      assert (hbinUStr2 hs1 (hs2 ++ hs3) = nil) as Hs2.
      { apply hbinUStr2_absorbed_inv with (hs:= hbinUStr1 (fun _ h2 => h2) hs1 (hs2 ++ hs3)).
        congruence.
      }
      rewrite Hs2, app_nil_r in H3.
      replace (hbinUStr2 hs1 hs2) with (nil (A:= vid_t * hmap)).
      - clear Hs2; rewrite app_nil_r.
        apply hbinUStr1_absorbed_inv with (hs3:= hs3); [assumption|congruence].
      - rewrite hbinUStr2_app_2 in Hs2.
        destruct (hbinUStr2 hs1 hs2); [reflexivity|discriminate].
    Qed.

    Lemma hmergeR_absorbed_left:
      forall h1 h2 h3,
        hmergeR h1 (hmergeR h2 h3) = h1 ->
        HMapStrEmpty h2 -> HMapStrEmpty h3 ->
        HDisj h2 h3 ->
        hmergeR h1 h2 = h1.
    Proof using .
      destruct h1 as [|b1|hs1|hs1], h2 as [|b2|hs2|hs2], h3 as [|b3|hs3|hs3]; intros.
      all: try (exfalso; auto; fail).
      all: try (reflexivity || discriminate || assumption).
      rewrite hmergeR_str_disj in H2 by assumption.
      eapply hmergeR_absorbed_left_str; eassumption.
    Qed.

    Lemma HDisj_hmergeR_split:
      forall h1 h2 h3,
        HMapStrEmpty h1 -> HDisj h1 h3 ->
        HMapStrEmpty h2 -> HDisj h2 h3 ->
        HMapStrEmpty h3 -> HDisj (hmergeR h1 h2) h3.
    Proof using .
      destruct h1 as [|b1|hs1|hs1], h2 as [|b2|hs2|hs2], h3 as [|b3|hs3|hs3]; intros.
      all: auto.
      simpl in *; clear H2 H4 H6.
      intros.
      rewrite map_app in H2.
      apply in_app_or in H2; destruct H2.
      - rewrite hbinUStr1_vids_eq in H2; eauto.
      - eapply H5; [|eassumption].
        clear -H2.
        induction hs2 as [|h2 hs2]; [assumption|].
        simpl in *.
        destruct (negb _).
        + inv H2; [left; reflexivity|right; auto].
        + right; auto.
    Qed.

    Lemma hselectA_single_upd_bits:
      forall h k b,
        hselectA (hbinUArr hupds h ((k, HMapBits b) :: nil)) k = HMapBits b.
    Proof using .
      unfold hbinUArr; simpl; intros.
      destruct (existsb _ _) eqn:Hb; simpl.

      - apply existsb_exists in Hb.
        destruct Hb as [[k' v] [? ?]]; simpl in *.
        apply Z.eqb_eq in H3; subst k'.
        rewrite app_nil_r.

        clear -H2; induction h; [elim H2|].
        destruct H2; subst.
        + simpl; rewrite Z.eqb_refl; simpl.
          apply hupds_bits.
        + destruct a as [ak av]; simpl.
          destruct (Z.eqb k ak) eqn:Ha; simpl; [|auto].
          rewrite Z.eqb_eq in Ha; subst ak.
          rewrite Z.eqb_refl; simpl.
          apply hupds_bits.

      - induction h; simpl; [rewrite Z.eqb_refl; reflexivity|].
        destruct a as [ak av]; simpl in *.
        apply Bool.orb_false_iff in Hb; dest.
        specialize (IHh H3).
        rewrite H2.
        apply Z.eqb_neq in H2.
        destruct (Z.eqb k ak) eqn:Ha; [|assumption].
        apply Z.eqb_eq in Ha; exfalso; auto.
    Qed.

    Lemma hselectA_single_upd_neq:
      forall h k1 k2 v,
        k1 <> k2 ->
        hselectA (hbinUArr hupds h ((k1, v) :: nil)) k2 = hselectA h k2.
    Proof using .
      unfold hbinUArr; simpl; intros.
      destruct (existsb _ _) eqn:Hb; simpl.

      - apply existsb_exists in Hb.
        destruct Hb as [[k' v'] [? ?]]; simpl in *.
        apply Z.eqb_eq in H4; subst k'.
        rewrite app_nil_r.

        clear -H2; induction h; [reflexivity|].
        destruct a as [ak av]; simpl.
        destruct (Z.eqb k2 ak) eqn:Hk2; simpl; [|auto].
        rewrite Z.eqb_eq in Hk2; subst ak.
        destruct (Z.eqb k2 k1) eqn:Hk; [|reflexivity].
        apply Z.eqb_eq in Hk; subst.
        exfalso; auto.

      - induction h; simpl.
        + destruct (Z.eqb k2 k1) eqn:Hk; [|reflexivity].
          apply Z.eqb_eq in Hk; subst.
          exfalso; auto.
        + destruct a as [ak av]; simpl in *.
          apply Bool.orb_false_iff in Hb; dest.
          rewrite H3.
          specialize (IHh H4).
          destruct (Z.eqb k2 ak) eqn:Hk2; [reflexivity|assumption].
    Qed.

  End Facts.

End HMap.

Arguments HMapEmpty {_}.

Declare Scope hmap_scope.

#[global] Delimit Scope hmap_scope with hmap.

Module HMapNotations.
  Notation "'[' ']'" := HMapEmpty: hmap_scope.
End HMapNotations.

#[local] Instance hmap_array_ops `{vid_t_c}: array_ops hmap :=
  { array_select := hselectA;
    array_range := hrangeA
  }.
