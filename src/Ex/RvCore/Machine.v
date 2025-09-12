Require Import riscv.Spec.Machine.
Require Import riscv.Utility.Utility riscv.Utility.Monads.
Import OStateOperations.
Require Import riscv.Utility.MonadNotations.
Require Import coqutil.Map.Interface.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.MkMachineWidth.

#[local] Open Scope Z_scope.
#[local] Open Scope bool_scope.


(*
The RiscvMachine used here is the Minimal version provided by the
original riscv-coq (riscv-coq/src/riscv/Platform/Minimal.v), with a few adjustments.
- The machine has separate instruction and data memory.
- The machine only supports loads and stores with addresses aligned to 4 bytes.
  Accessing unaligned addresses will result in an exception.
  (RISC-V formal semantics allows raising exceptions for unaligned data accesses).
*)


Section Machine.
  Context {width: Z} {word: Interface.word width} {word_ok: word.ok word}.
  Context {Registers: map.map Register word}.
  Context {Mem: map.map word byte}.

  (* A simple RiscvMachine that has separate instruction memory and data memory. *)
  Record RiscvMachine := mkRiscvMachine {
      getRegs: Registers;
      getPc: word;
      getNextPc: word;
      getInstMem: Mem;
      getDataMem: Mem;
    }.

  Definition withRegs: Registers -> RiscvMachine -> RiscvMachine :=
    fun regs2 '(mkRiscvMachine regs1 pc nextPC instMem dataMem) =>
                mkRiscvMachine regs2 pc nextPC instMem dataMem.

  Definition withPc: word -> RiscvMachine -> RiscvMachine :=
    fun pc2 '(mkRiscvMachine regs pc1 nextPC instMem dataMem) =>
              mkRiscvMachine regs pc2 nextPC instMem dataMem.

  Definition withNextPc: word -> RiscvMachine -> RiscvMachine :=
    fun nextPC2 '(mkRiscvMachine regs pc nextPC1 instMem dataMem) =>
                  mkRiscvMachine regs pc nextPC2 instMem dataMem.

  Definition withInstMem: Mem -> RiscvMachine -> RiscvMachine :=
    fun instMem2 '(mkRiscvMachine regs pc nextPC instMem1 dataMem)  =>
                mkRiscvMachine regs pc nextPC instMem2 dataMem.

  Definition withDataMem: Mem -> RiscvMachine -> RiscvMachine :=
    fun dataMem2 '(mkRiscvMachine regs pc nextPC instMem dataMem1)  =>
                mkRiscvMachine regs pc nextPC instMem dataMem2.
End Machine.


Section Riscv.
#[local] Open Scope alu_scope.
Context {width: Z} {BW: Bitwidth width} {word: Interface.word width} {word_ok: word.ok word}.
  Context {Registers: map.map Register word}.
  Context {Mem: map.map word byte}.

  Definition RiscvMachine' := RiscvMachine (width := width).
  Definition update (f: RiscvMachine' -> RiscvMachine'): OState RiscvMachine' unit :=
    m <- get; put (f m).

  Definition fail_if_None {R}(o: option R): OState RiscvMachine' R :=
  match o with
  | Some x => Return x
  | None => fail_hard
  end.

  Definition assert_aligned (addr : word) : OState RiscvMachine' unit :=
    if (Utility.Utility.remu addr (ZToReg 4) /= ZToReg 0)
    then fail_hard
    else Return tt.

  Definition loadN(n: nat)(kind: SourceType)(a: word): OState RiscvMachine' (HList.tuple byte n) :=
    assert_aligned a ;;
    mach <- get;
    dmem <- match kind with
      | Fetch => Return (mach.(getInstMem))
      | Execute => Return (mach.(getDataMem))
      | _ => fail_hard
    end;
    fail_if_None (Memory.load_bytes n dmem a).

  (* We only allow stores to the data memory. *)
  Definition storeN (n: nat) (kind: SourceType) (a: word) (v: HList.tuple byte n) :=
    assert_aligned a ;;
    mach <- get;
    dmem <- match kind with
      | Fetch => Return (mach.(getInstMem))
      | Execute => Return (mach.(getDataMem))
      | _ => fail_hard
    end;
    dmem' <- fail_if_None (Memory.store_bytes n dmem a v);
    update (fun mach => (withDataMem dmem' mach)).


  #[export] Instance IsRiscvProgram: RiscvProgram (OState RiscvMachine') word :=  {
    getRegister reg :=
      if Z.eq_dec reg Register0 then
        Return (ZToReg 0)
      else
        if (0 <? reg) && (reg <? 32) then
          mach <- get;
          match map.get mach.(getRegs) reg with
          | Some v => Return v
          | None => Return (word.of_Z 0)
          end
        else
          fail_hard;

    setRegister reg v :=
      if Z.eq_dec reg Register0 then
        Return tt
      else
        if (0 <? reg) && (reg <? 32) then
          update (fun mach => withRegs (map.put mach.(getRegs) reg v) mach)
        else
          fail_hard;

    getPC := mach <- get; Return mach.(getPc);

    setPC newPC := update (withNextPc newPC);

    loadByte   := loadN 1;
    loadHalf   := loadN 2;
    loadWord   := loadN 4;
    loadDouble := loadN 8;

    storeByte   := storeN 1;
    storeHalf   := storeN 2;
    storeWord   := storeN 4;
    storeDouble := storeN 8;

    makeReservation  addr := fail_hard;
    clearReservation addr := fail_hard;
    checkReservation addr := fail_hard;
    getCSRField f := fail_hard;
    setCSRField f v := fail_hard;
    getPrivMode := fail_hard;
    setPrivMode v := fail_hard;
    fence _ _ := fail_hard;

    endCycleNormal := update (fun m => (withPc m.(getNextPc)
                                        (withNextPc (word.add m.(getNextPc) (word.of_Z 4)) m)));

    (* fail hard if an exception is thrown. *)
    endCycleEarly{A: Type} := fail_hard;
  }.
End Riscv.
