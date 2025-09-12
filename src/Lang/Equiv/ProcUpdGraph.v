Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.ZArith.BinInt.
Require Import Lib.Lib. Import HMapNotations. Import SZNotations.
Require Import Lang.Syntax Lang.Analysis Lang.Semantics.

Require Import UpdGraph Standard TrsProc.

Set Implicit Arguments.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope hmap_scope.

Section ProcUpdGraph.
  Context `{sz_ops}.
  Context `{vid_ops}.
  Context `{array_ops hmap}.

  Variables (decls: Decls) (funcs: Funcs) (mtrss: MTrss).

  Definition getWritesEvalUnit (initWrites: list vid_t) (cpos: hpath) (evu: EvalUnit): list vid_t :=
    match evu with
    | EvalUnitAlways isComb stmt =>
        if isComb
        then getSLStatementWrites decls cpos stmt
        else initWrites
    | EvalUnitAssign lv e => getSLExpr decls cpos lv
    | EvalUnitModuleIns mins => getWritesModuleIns decls mtrss cpos mins
    | EvalUnitInputClk => initWrites
    end.

  Definition isInit (init: InitState): bool :=
    match init with
    | nil => false
    | _ => true
    end.

  Definition getUNode (initUpd: bool) (init: InitState) (proc: Process): unode :=
    {| keys := getWritesEvalUnit (List.map fst init) (proc_pos proc) (proc_evu proc);
      deps := if isInit init then nil else trig_stv (proc_trig proc);
      updOnce := isInit init && initUpd;
      updDone := isInit init && initUpd;
      updf := fun st => if isInit init
                        then HMapStr init
                        else match trsProc decls funcs mtrss proc st with
                             | Sret u => fst u
                             | Fail _ => []
                             end |}.

  Definition IPS := list (InitState * Process).

  Definition getUGraph (initUpd: bool) (ips: IPS): ugraph :=
    List.map (fun ip => getUNode initUpd (fst ip) (snd ip)) ips.

  Definition initState (ips: IPS): IFW :=
    HMapStr (List.concat (List.map fst ips)).

  Definition GetUGraphWf (ips: IPS) :=
    forall tst ugf stf,
      EvalUGraphTrs (getUGraph true ips) (hupds tst (initState ips)) ugf stf <->
        EvalUGraphTrs (getUGraph false ips) tst ugf stf.

  (*! Well-formedness of processes *)

  Definition ProcWfExecUniq (proc: Process): Prop :=
    forall s, match trsProc decls funcs mtrss proc s with
              | Sret u => HMapStrEmptyWf (fst u)
              | Fail _ => True
              end.

  Definition ProcWfExecSucc (proc: Process): Prop :=
    forall s,
      match trsProc decls funcs mtrss proc s with
      | Sret u => fst u <> [] /\ Forall (fun v => hfind [HEltVid v] s <> None) (trig_stv (proc_trig proc))
      | Fail _ => exists v, In v (trig_stv (proc_trig proc)) /\ hfind [HEltVid v] s = None
      end.

  Definition ProcWfExecSame0 (proc: Process): Prop :=
    forall upds,
      genEvalEvent (EventUpd upds) proc = None ->
      forall s, trsProc decls funcs mtrss proc (hupds s upds) = trsProc decls funcs mtrss proc s.

  Definition ProcWfExecSame1 (proc: Process): Prop :=
    forall s u,
      trsProc decls funcs mtrss proc s = Sret u ->
      forall base,
        trsProc decls funcs mtrss proc (hupds base s) = Sret u.

  Definition ProcWf (proc: Process): Prop :=
    ProcWfExecUniq proc /\ ProcWfExecSucc proc /\ ProcWfExecSame0 proc /\ ProcWfExecSame1 proc.

  Definition ProcsOk (procs: Processes): Prop :=
    Forall ProcWf procs /\
      TrsProcsRepConst decls funcs mtrss procs /\
      TrsProcsRepProg decls funcs mtrss procs /\
      ProcsWfUpd decls funcs mtrss procs /\
      ProcsWfDet decls funcs mtrss procs.

  (*! Well-formedness of ugraphs wrt. associated processes *)

  Definition UNodeProc (un: unode) (proc: Process): Prop :=
    UNodeKeysOk un /\
      keys un <> nil /\
      deps un = trig_stv (proc_trig proc) /\
      (forall st, updf un st = match trsProc decls funcs mtrss proc st with
                               | Sret u => fst u
                               | Fail _ => []
                               end).

  Definition UGraphProcs (ug: ugraph) (procs: Processes): Prop :=
    Forall2 UNodeProc ug procs.

  Definition UGraphIpsWf :=
    forall ips initb,
      UGraphUnique (getUGraph initb ips) /\
        UGraphKeysOk (getUGraph initb ips) /\
        UGraphDepsOk (getUGraph initb ips) /\
        UGraphUpdOk (getUGraph initb ips) /\
        UGraphUpdfOk (getUGraph initb ips) /\
        UGraphSt (initState ips) (getUGraph initb ips) /\
        UGraphCycleFree (getUGraph initb ips) /\
        UGraphStateMono (getUGraph initb ips) /\
        UGraphProcs (getUGraph initb ips) (List.map snd ips).

  Definition UGraphIpsStWf :=
    forall ips0 st ugf stf,
      EvalUGraphTrs (getUGraph false ips0) st ugf stf ->
      forall ips1,
        List.map snd ips0 = List.map snd ips1 ->
        forall stu initb,
          UGraphStWf (hupds stf stu) (getUGraph initb ips1).

  (*! Facts *)

  Lemma UGraphProcs_upd:
    forall ug1 un ug2 procs,
      UGraphProcs (ug1 ++ un :: ug2) procs ->
      forall nupdo nupdd,
        UGraphProcs (ug1 ++ {| keys := keys un;
                              deps := deps un;
                              updOnce := nupdo;
                              updDone := nupdd;
                              updf := updf un |} :: ug2) procs.
  Proof using .
    unfold UGraphProcs; intros.
    apply Forall2_app_inv_l in H3; destruct H3 as [procs1 [procs2 [? [? ?]]]]; subst procs.
    destruct procs2 as [|proc procs2]; inv H4.
    apply Forall2_app; [assumption|].
    constructor; [|assumption].
    assumption.
  Qed.

End ProcUpdGraph.
