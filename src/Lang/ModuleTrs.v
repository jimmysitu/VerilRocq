Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Lib.Lib. Import HMapNotations. Import SZNotations.
Require Import Lang.Analysis Lang.Syntax Lang.Semantics.

Set Implicit Arguments.

Local Open Scope Z_scope.
Local Open Scope hmap_scope.

Section ModuleTrs.
  Context `{sz_ops}.
  Context `{vid_ops}.
  Context `{array_ops hmap}.


  Record ModulePkg :=
    { mpkg_mtrs: MTrs;
      mpkg_rst_vid: vid_t;
      mpkg_rst_neg: bool; (* true if a negative reset *)
    }.

  Import ListNotations.
  Variable (mpkg: ModulePkg).

  Definition mtrs := mpkg.(mpkg_mtrs).

  Definition buildPreReset: State :=
    HMapStr [(mpkg.(mpkg_rst_vid),
      HMapBits #{(if mpkg.(mpkg_rst_neg) then 0 else 1), 1, false})].

  Definition buildReset (empty_inputs initial_flops: State): State :=
    hupds initial_flops (fst (mtrs.(mtrs_func) (hupds empty_inputs buildPreReset) initial_flops)).

End ModuleTrs.
