Require Import Coq.ZArith.BinInt. Local Open Scope Z_scope.
Require Import Lib.Lib.
Require Import Lang.Syntax.

Set Implicit Arguments.
Local Open Scope list_scope.

Section IOAnalysis.
  Context {vid_t: Set}.

  Definition ioAnsiPortDecl (pdecl: @VAnsiPortDecl vid_t): option vid_t * option vid_t :=
    match pdecl with
    | VAnsiPortDeclNet None vid => (None, None)
    | VAnsiPortDeclNet (Some (VNetPortHeaderO None pty)) vid => (None, None)
    | VAnsiPortDeclNet (Some (VNetPortHeaderO (Some pdir) pty)) vid =>
        match pdir with
        | VPortDirectionInput => (Some vid, None)
        | VPortDirectionOutput => (None, Some vid)
        | _ => (None, None)
        end
    | VAnsiPortDeclVar None vid => (None, None)
    | VAnsiPortDeclVar (Some (VVarPortHeaderO None dt)) vid => (None, None)
    | VAnsiPortDeclVar (Some (VVarPortHeaderO (Some pdir) dt)) vid =>
        match pdir with
        | VPortDirectionInput => (Some vid, None)
        | VPortDirectionOutput => (None, Some vid)
        | _ => (None, None)
        end
    end.

  Fixpoint ioAnsiPortDecls (pdecls: @VAnsiPortDecls vid_t): list vid_t * list vid_t :=
    match pdecls with
    | VAnsiPortDeclNil => (nil, nil)
    | VAnsiPortDeclsOne pdecl => let (oi, oo) := ioAnsiPortDecl pdecl in (o2l oi, o2l oo)
    | VAnsiPortDeclsCons pdecl spdecls => let (ih, oh) := ioAnsiPortDecl pdecl in
                                          let (it, ot) := ioAnsiPortDecls spdecls in
                                          (ocons ih it, ocons oh ot)
    end.

  Fixpoint ioPortIds (pids: @VPortIds vid_t): list vid_t :=
    match pids with
    | VPortIdsOne vid => cons vid nil
    | VPortIdsCons vid spids => cons vid (ioPortIds spids)
    end.

  Definition ioPortDecl (pd: @VPortDecl vid_t): list vid_t * list vid_t :=
    match pd with
    | VPortDeclInputP pty pids => (ioPortIds pids, nil)
    | VPortDeclInputD dty pids => (ioPortIds pids, nil)
    | VPortDeclOutputP pty pids => (nil, ioPortIds pids)
    | VPortDeclOutputD dty pids => (nil, ioPortIds pids)
    | _ => (nil, nil)
    end.

  Definition ioModuleItem (mitem: @VModuleItem vid_t): list vid_t * list vid_t :=
    match mitem with
    | VModuleItemPortDecl pd => ioPortDecl pd
    | VModuleItemNonPort _ => (nil, nil)
    end.

  Fixpoint ioModuleItems (mitems: @VModuleItems vid_t): list vid_t * list vid_t :=
    match mitems with
    | VModuleItemsOne mitem => ioModuleItem mitem
    | VModuleItemsCons mitem mitems' => let (ih, oh) := ioModuleItem mitem in
                                        let (it, ot) := ioModuleItems mitems' in
                                        (ih ++ it, oh ++ ot)
    end.

  Definition getIOIds (m: @VModuleDecl vid_t): list vid_t * list vid_t :=
    match m with
    | VModuleDeclAnsi mn pports pdecls mitems =>
        let (ideclsP, odeclsP) := ioAnsiPortDecls pdecls in
        let (ideclsI, odeclsI) := ioModuleItems mitems in
        (ideclsP ++ ideclsI, odeclsP ++ odeclsI)
    end.

End IOAnalysis.
