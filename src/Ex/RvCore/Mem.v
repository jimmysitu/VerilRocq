Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.

Require Import Ex.RvCore.Common.

Module ICache.

  Module M.
    Notation "'icache'" := icache (in custom ce_top).
    Import Notations.

    Definition m: @VModuleDecl vid := #[
module icache
  #(parameter integer IADDR_SIZE = 32,
    parameter integer INST_SIZE = 32)
   (input logic                  clk,
    input logic                  rst_n,
    input logic                  imem_req_vld,
    input logic [IADDR_SIZE-1:0] imem_req,
    output logic                 imem_resp_vld,
    output logic [INST_SIZE-1:0] imem_resp);

   localparam integer            ICACHE_SIZE = 2**(IADDR_SIZE-2);

   logic [ICACHE_SIZE-1:0][INST_SIZE-1:0] imem;
   logic [IADDR_SIZE-3:0]                 imem_req_truncated;

   assign imem_req_truncated = imem_req[IADDR_SIZE-1:2];
   assign imem_resp_vld = imem_req_vld;
   assign imem_resp = INST_SIZE '(imem[imem_req_truncated]);

endmodule].

  End M.

  Record Inputs :=
    { rst_n_v: SZ;
      imem_req_vld_v: SZ;
      imem_req_v: SZ;
    }.

  Record Flops :=
    { imem_v: list (Z * Value) }.

  Section AbsOps.
    Context `{sz_ops} `{array_ops hmap}.

    Import ListNotations.
    Import HMapNotations.

    #[export] Instance inputs_structured: StructuredState Inputs := {
      from_state :=
        fun state =>
          rst_n_v <- sfind rst_n state;
          imem_req_vld_v <- sfind imem_req_vld state;
          imem_req_v <- sfind imem_req state;
            Sret {|
              rst_n_v := hbits rst_n_v;
              imem_req_vld_v := hbits imem_req_vld_v;
              imem_req_v := hbits imem_req_v;
            |};
      to_state := fun i => match i with
        | {| rst_n_v := rst_n_v; imem_req_vld_v := imem_req_vld_v; imem_req_v := imem_req_v |} =>
          HMapStr [(rst_n, HMapBits rst_n_v); (imem_req_vld, HMapBits imem_req_vld_v); (imem_req, HMapBits imem_req_v)]
        end;
    }.

    #[export] Instance flops_structured: StructuredState Flops := {
      from_state :=
        fun state =>
          imem_v <- sfind imem state;
            Sret {|
              imem_v := harr imem_v;
            |};
      to_state :=
        fun f =>
          match f with
          | {| imem_v := imem_v |} =>
            HMapStr [(imem, HMapArr imem_v)]
          end;
    }.

    Definition etrs (eid: vid_t): trsOk MTrs := Fail TrsUndeclared.

    Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Flops.
    Proof.
      unshelve epose (trs := _ : MTrs).
      { apply Build_MTrs. 1-2: shelve.
        intros inputs flops.
        destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
        destruct (from_state (A := Flops) flops) as [f_format|]; [| eapply (_, _)].
        destruct i_format, f_format. eapply (_, _). }

      apply mk_MTrsOf with (mtrsof_mtrs := trs).
      1-2: vm_compute; reflexivity.
      red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
      destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *; vm_compute in Htrs; injection Htrs as <- <-.
      2-4: eauto.
      eexists _. split; [split|].
      - eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity.
      - vm_compute. reflexivity.
      - cbv. reflexivity.
    Defined.

  End AbsOps.

End ICache.

Module DCache.

  Module M.
    Notation "'dcache'" := dcache (in custom ce_top).
    Import Notations.

    Definition m: @VModuleDecl vid_t := #[
module dcache
  #(parameter integer ADDR_SIZE = 32,
    parameter integer DATA_SIZE = 32)
   (input logic                  clk,
    input logic                  rst_n,
    input logic                  dmem_req_vld,
    input logic                  dmem_req_ld,
    input logic [ADDR_SIZE-1:0]  dmem_req_ld_addr,
    input logic [ADDR_SIZE-1:0]  dmem_req_st_addr,
    input logic [1:0]            dmem_req_st_ty,
    input logic [DATA_SIZE-1:0]  dmem_req_data,
    output logic                 dmem_resp_vld,
    output logic [DATA_SIZE-1:0] dmem_resp);

   localparam integer            DCACHE_SIZE = 2**(ADDR_SIZE-2);

   logic [DCACHE_SIZE-1:0][DATA_SIZE-1:0] dmem;
   logic [DATA_SIZE-1:0]                  req_data;
   logic [DATA_SIZE-1:0]                  st_read_data;
   logic [ADDR_SIZE-3:0]                  dmem_req_ld_addr_truncated;
   logic [ADDR_SIZE-3:0]                  dmem_req_st_addr_truncated;

   assign dmem_req_ld_addr_truncated = dmem_req_ld_addr[ADDR_SIZE-1:2];
   assign dmem_req_st_addr_truncated = dmem_req_st_addr[ADDR_SIZE-1:2];
   assign req_data = DATA_SIZE '(dmem[dmem_req_ld_addr_truncated]);
   assign st_read_data = DATA_SIZE '(dmem[dmem_req_st_addr_truncated]);
   assign dmem_resp_vld = dmem_req_vld && dmem_req_ld;
   assign dmem_resp = req_data;

   logic [DATA_SIZE-1:0]                  st_data;
   assign st_data = dmem_req_st_ty == 2'b00 ? ((32 '(st_read_data[DATA_SIZE-1:8]) << 8) + dmem_req_data[7:0]) :
                    dmem_req_st_ty == 2'b01 ? ((32 '(st_read_data[DATA_SIZE-1:16]) << 16) + dmem_req_data[15:0]) :
                    dmem_req_st_ty == 2'b10 ? dmem_req_data : 'd0;

   always @(posedge clk) begin
      if (!rst_n) dmem <= {'d0};
      else if (dmem_req_vld && !dmem_req_ld) dmem[dmem_req_st_addr_truncated] <= st_data;
   end

endmodule].

  End M.

  Record Inputs :=
    { rst_n_v: SZ;
      dmem_req_vld_v: SZ;
      dmem_req_ld_v: SZ;
      dmem_req_ld_addr_v: SZ;
      dmem_req_st_addr_v: SZ;
      dmem_req_st_ty_v: SZ;
      dmem_req_data_v: SZ;
    }.

  Record Flops :=
    { dmem_v: list (Z * Value) }.

  Section AbsOps.
    Context `{sz_ops} `{array_ops hmap}.

    Import ListNotations.
    Import HMapNotations.

    #[export] Instance inputs_structured: StructuredState Inputs := {
      from_state :=
        fun state =>
          rst_n_v <- sfind rst_n state;
          dmem_req_vld_v <- sfind dmem_req_vld state;
          dmem_req_ld_v <- sfind dmem_req_ld state;
          dmem_req_ld_addr_v <- sfind dmem_req_ld_addr state;
          dmem_req_st_addr_v <- sfind dmem_req_st_addr state;
          dmem_req_st_ty_v <- sfind dmem_req_st_ty state;
          dmem_req_data_v <- sfind dmem_req_data state;
            Sret {|
              rst_n_v := hbits rst_n_v;
              dmem_req_vld_v := hbits dmem_req_vld_v;
              dmem_req_ld_v := hbits dmem_req_ld_v;
              dmem_req_ld_addr_v := hbits dmem_req_ld_addr_v;
              dmem_req_st_addr_v := hbits dmem_req_st_addr_v;
              dmem_req_st_ty_v := hbits dmem_req_st_ty_v;
              dmem_req_data_v := hbits dmem_req_data_v;
            |};
      to_state := fun i =>
        match i with
          | {| rst_n_v := rst_n_v;
               dmem_req_vld_v := dmem_req_vld_v;
               dmem_req_ld_v := dmem_req_ld_v;
               dmem_req_ld_addr_v := dmem_req_ld_addr_v;
               dmem_req_st_addr_v := dmem_req_st_addr_v;
               dmem_req_st_ty_v := dmem_req_st_ty_v;
               dmem_req_data_v := dmem_req_data_v |} =>
            HMapStr [(rst_n, HMapBits rst_n_v);
                    (dmem_req_vld, HMapBits dmem_req_vld_v);
                    (dmem_req_ld, HMapBits dmem_req_ld_v);
                    (dmem_req_ld_addr, HMapBits dmem_req_ld_addr_v);
                    (dmem_req_st_addr, HMapBits dmem_req_st_addr_v);
                    (dmem_req_st_ty, HMapBits dmem_req_st_ty_v);
                    (dmem_req_data, HMapBits dmem_req_data_v)]
        end;
    }.

    #[export] Instance flops_structured: StructuredState Flops :=
    {
      from_state :=
        fun state =>
          dmem_v <- sfind dmem state;
            Sret {|
              dmem_v := harr dmem_v;
            |};
      to_state :=
        fun f =>
          match f with
          | {| dmem_v := dmem_v |} =>
            HMapStr [(dmem, HMapArr dmem_v)]
          end;
    }.

    Definition etrs (eid: vid_t): trsOk MTrs := Fail TrsUndeclared.

    Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Flops.
    Proof.
      unshelve epose (trs := _ : MTrs).
      { apply Build_MTrs. 1-2: shelve.
        intros inputs flops.
        destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
        destruct (from_state (A := Flops) flops) as [f_format|]; [| eapply (_, _)].
        destruct i_format, f_format. eapply (_, _). }

      apply mk_MTrsOf with (mtrsof_mtrs := trs).
      1-2: vm_compute; reflexivity.
      red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
      destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *; vm_compute in Htrs; injection Htrs as <- <-.
      2-4: eauto.
      eexists. split; [split|].
      - eapply trsM_iff_rep_is_chain with (n := 2%nat). vm_compute. reflexivity.
      - vm_compute. reflexivity.
      - vm_compute. reflexivity.
    Defined.

  End AbsOps.

End DCache.

Module ICacheA.

  Module M.
    Notation "'icache_a'" := icache_a (in custom ce_top).
    Include Notations.

    Definition m: @VModuleDecl vid_t := #[
module icache_a
  #(parameter integer IADDR_SIZE = 32,
    parameter integer INST_SIZE = 32)
   (input logic                  clk,
    input logic                  rst_n,
    input logic                  imem_req_vld,
    input logic [IADDR_SIZE-1:0] imem_req,
    input logic                  flush,
    output logic                 imem_req_rdy,
    input logic                  imem_resp_rdy,
    output logic                 imem_resp_vld,
    output logic [INST_SIZE-1:0] imem_resp);
   localparam integer            ICACHE_SIZE = 2**(IADDR_SIZE-2);
   logic [ICACHE_SIZE-1:0][INST_SIZE-1:0] imem;
   logic                                  int_resp_vld;
   logic [INST_SIZE-1:0]                  int_resp;
   logic [IADDR_SIZE-3:0]                 imem_req_truncated;
   assign imem_req_truncated = imem_req[IADDR_SIZE-1:2];
   assign imem_req_rdy = !int_resp_vld || imem_resp_rdy;
   assign imem_resp_vld = int_resp_vld;
   assign imem_resp = int_resp;
   always @(posedge clk) begin
      if (!rst_n || flush) begin
         int_resp_vld <= 1'b0;
         int_resp <= 'd0;
      end
      else begin
         int_resp_vld <= imem_req_vld || !imem_req_rdy;
         if (imem_req_rdy && imem_req_vld) int_resp <= INST_SIZE '(imem[imem_req_truncated]);
      end
   end
endmodule].

  End M.

  Record Inputs :=
    { rst_n_v: SZ;
      imem_req_vld_v: SZ;
      imem_req_v: SZ;
      imem_resp_rdy_v: SZ;
      flush_v: SZ;
    }.

  Record Flops :=
    { imem_v: list (Z * Value);
      int_resp_vld_v: SZ;
      int_resp_v: SZ }.

  Section AbsOps.
    Context `{sz_ops} `{array_ops hmap}.

    Import ListNotations.
    Import HMapNotations.

    #[export] Instance inputs_structured: StructuredState Inputs := {
      from_state :=
        fun state =>
          rst_n_v <- sfind rst_n state <~ [];
          imem_req_vld_v <- sfind imem_req_vld state <~ [];
          imem_req_v <- sfind imem_req state <~ [];
          imem_resp_rdy_v <- sfind imem_resp_rdy state <~ [];
          flush_v <- sfind flush state <~ [];
            Sret {|
              rst_n_v := hbits rst_n_v;
              imem_req_vld_v := hbits imem_req_vld_v;
              imem_req_v := hbits imem_req_v;
              imem_resp_rdy_v := hbits imem_resp_rdy_v;
              flush_v := hbits flush_v;
            |};
      to_state := fun i =>
        match i with {|
          rst_n_v := rst_n_v;
          imem_req_vld_v := imem_req_vld_v;
          imem_req_v := imem_req_v;
          imem_resp_rdy_v := imem_resp_rdy_v;
          flush_v := flush_v;
          |} =>
            HMapStr [(rst_n, HMapBits rst_n_v);
                    (imem_req_vld, HMapBits imem_req_vld_v);
                    (imem_req, HMapBits imem_req_v);
                    (imem_resp_rdy, HMapBits imem_resp_rdy_v);
                    (flush, HMapBits flush_v)]
        end;
    }.

    #[export] Instance flops_structured: StructuredState Flops := {
      from_state :=
        fun state =>
          imem_v <- sfind imem state;
          int_resp_vld_v <- sfind int_resp_vld state;
          int_resp_v <- sfind int_resp state;
            Sret {|
              imem_v := harr imem_v;
              int_resp_vld_v := hbits int_resp_vld_v;
              int_resp_v := hbits int_resp_v;
            |};
      to_state :=
        fun f =>
          match f with
          | {| imem_v := imem_v;
               int_resp_vld_v := int_resp_vld_v;
               int_resp_v := int_resp_v |} =>
            HMapStr [(imem, HMapArr imem_v);
                    (int_resp_vld, HMapBits int_resp_vld_v);
                    (int_resp, HMapBits int_resp_v)]
          end;
    }.

    Record Outputs := {
      imem_req_rdy_v: SZ;
      imem_resp_vld_v: SZ;
      imem_resp_v: SZ;
    }.

    Definition output_to_state (outputs: Outputs): State
      := HMapStr [(imem_req_rdy, HMapBits outputs.(imem_req_rdy_v));
                  (imem_resp_vld, HMapBits outputs.(imem_resp_vld_v));
                  (imem_resp, HMapBits outputs.(imem_resp_v))].

    Record Updates := {
      int_resp_vld_update: State;
      int_resp_update: State;
    }.

    Definition update_to_state (upds: Updates): State
      := HMapStr [(int_resp_vld, upds.(int_resp_vld_update)); (int_resp, upds.(int_resp_update))].

    Definition etrs (eid: vid_t): trsOk MTrs := Fail TrsUndeclared.

    Definition trs_structured_sigT: {trs: forall (inputs: Inputs) (flops: Flops), (Updates * Outputs) |
      is_module_trs M.m fmapEmpty etrs Inputs Flops (to_unstructured_trs update_to_state output_to_state trs)
    }.
    Proof.
      unshelve epose (trs := _ : Inputs -> Flops -> Updates * Outputs).
      { intros i f. destruct i, f. split; econstructor; eapply _. }
      exists trs.
      red. unfold to_unstructured_trs. intros ???? Htrs. unfold format.
      destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *; vm_compute in Htrs; injection Htrs as <- <-.
      2-4: auto.
      eexists. split; [split|].
      { eapply trsM_iff_rep_is_chain with (n := 1%nat). vm_compute. reflexivity. }
      - vm_compute. reflexivity.
      - vm_compute. reflexivity.
      all: vm_compute; reflexivity.
    Defined.

    Definition trs_structured := proj1_sig trs_structured_sigT.

    Definition mtrs: MTrsOf M.m fmapEmpty etrs Inputs Flops.
    Proof.
      eapply mk_MTrsOf with (mtrsof_mtrs := (Build_MTrs _ _ (to_unstructured_trs _ _ trs_structured))).
      1-2: vm_compute; reflexivity. unfold mtrs_func.
      eapply (proj2_sig trs_structured_sigT).
    Defined.

  #[global] Opaque trs_structured.

  End AbsOps.

End ICacheA.

Module DCacheA.

  Module M.
    Notation "'dcache_a'" := dcache_a (in custom ce_top).
    Include Notations.

    Definition m: @VModuleDecl vid_t := #[
module dcache_a
  #(parameter integer ADDR_SIZE = 32,
    parameter integer DATA_SIZE = 32)
   (input logic                  clk,
    input logic                  rst_n,
    input logic                  dmem_req_vld,
    input logic                  dmem_req_ld,
    input logic [ADDR_SIZE-1:0]  dmem_req_ld_addr,
    input logic [ADDR_SIZE-1:0]  dmem_req_st_addr,
    input logic [1:0]            dmem_req_st_ty,
    input logic [DATA_SIZE-1:0]  dmem_req_data,
    output logic                 dmem_req_rdy,
    input logic                  dmem_resp_rdy,
    output logic                 dmem_resp_vld,
    output logic [DATA_SIZE-1:0] dmem_resp);
   localparam integer            DCACHE_SIZE = 32;
   logic [DCACHE_SIZE-1:0][DATA_SIZE-1:0] dmem;
   logic [DATA_SIZE-1:0]                  req_data;
   logic [DATA_SIZE-1:0]                  st_read_data;
   logic                                  int_resp_vld;
   logic [DATA_SIZE-1:0]                  int_resp;
   logic [ADDR_SIZE-3:0]                  dmem_req_ld_addr_truncated;
   logic [ADDR_SIZE-3:0]                  dmem_req_st_addr_truncated;
   assign dmem_req_ld_addr_truncated = dmem_req_ld_addr[ADDR_SIZE-1:2];
   assign dmem_req_st_addr_truncated = dmem_req_st_addr[ADDR_SIZE-1:2];
   assign req_data = DATA_SIZE '(dmem[dmem_req_ld_addr_truncated]);
   assign st_read_data = DATA_SIZE '(dmem[dmem_req_st_addr_truncated]);
   assign dmem_req_rdy = !int_resp_vld || dmem_resp_rdy;
   assign dmem_resp_vld = int_resp_vld;
   assign dmem_resp = int_resp;
   always @(posedge clk) begin
      if (!rst_n) begin
         int_resp_vld <= 1'b0;
         int_resp <= 'd0;
      end
      else begin
         int_resp_vld <= (dmem_req_vld && dmem_req_ld) || !dmem_req_rdy;
         int_resp <= req_data;
      end
   end
   logic [DATA_SIZE-1:0]                  st_data;
   assign st_data = dmem_req_st_ty == 2'b00 ? ((32 '(st_read_data[DATA_SIZE-1:8]) << 8) + dmem_req_data[7:0]) :
                    dmem_req_st_ty == 2'b01 ? ((32 '(st_read_data[DATA_SIZE-1:16]) << 16) + dmem_req_data[15:0]) :
                    dmem_req_st_ty == 2'b10 ? dmem_req_data : 'd0;
   always @(posedge clk) begin
      if (!rst_n) dmem <= {'d0};
      else if (dmem_req_vld && !dmem_req_ld) dmem[dmem_req_st_addr_truncated] <= st_data;
   end
endmodule].

  End M.

  Record Inputs :=
    { rst_n_v: SZ;
      dmem_req_vld_v: SZ;
      dmem_req_ld_v: SZ;
      dmem_req_ld_addr_v: SZ;
      dmem_req_st_addr_v: SZ;
      dmem_req_st_ty_v: SZ;
      dmem_req_data_v: SZ;
      dmem_resp_rdy_v: SZ;
    }.

  Record Flops :=
    { dmem_v: list (Z * Value);
      int_resp_vld_v: SZ;
      int_resp_v: SZ }.

  Section AbsOps.
    Context `{sz_ops} `{array_ops hmap}.

    Import ListNotations.
    Import HMapNotations.

    #[export] Instance inputs_structured: StructuredState Inputs := {
      from_state :=
        fun state =>
          rst_n_v <- sfind rst_n state;
          dmem_req_vld_v <- sfind dmem_req_vld state <~ [];
          dmem_req_ld_v <- sfind dmem_req_ld state;
          dmem_req_ld_addr_v <- sfind dmem_req_ld_addr state;
          dmem_req_st_addr_v <- sfind dmem_req_st_addr state;
          dmem_req_st_ty_v <- sfind dmem_req_st_ty state;
          dmem_req_data_v <- sfind dmem_req_data state;
          dmem_resp_rdy_v <- sfind dmem_resp_rdy state;
            Sret {|
              rst_n_v := hbits rst_n_v;
              dmem_req_vld_v := hbits dmem_req_vld_v;
              dmem_req_ld_v := hbits dmem_req_ld_v;
              dmem_req_ld_addr_v := hbits dmem_req_ld_addr_v;
              dmem_req_st_addr_v := hbits dmem_req_st_addr_v;
              dmem_req_st_ty_v := hbits dmem_req_st_ty_v;
              dmem_req_data_v := hbits dmem_req_data_v;
              dmem_resp_rdy_v := hbits dmem_resp_rdy_v;
            |};
      to_state := fun i =>
        match i with
          | {| rst_n_v := rst_n_v;
               dmem_req_vld_v := dmem_req_vld_v;
               dmem_req_ld_v := dmem_req_ld_v;
               dmem_req_ld_addr_v := dmem_req_ld_addr_v;
               dmem_req_st_addr_v := dmem_req_st_addr_v;
               dmem_req_st_ty_v := dmem_req_st_ty_v;
               dmem_req_data_v := dmem_req_data_v;
               dmem_resp_rdy_v := dmem_resp_rdy_v |} =>
            HMapStr [(rst_n, HMapBits rst_n_v);
                    (dmem_req_vld, HMapBits dmem_req_vld_v);
                    (dmem_req_ld, HMapBits dmem_req_ld_v);
                    (dmem_req_ld_addr, HMapBits dmem_req_ld_addr_v);
                    (dmem_req_st_addr, HMapBits dmem_req_st_addr_v);
                    (dmem_req_st_ty, HMapBits dmem_req_st_ty_v);
                    (dmem_req_data, HMapBits dmem_req_data_v);
                    (dmem_resp_rdy, HMapBits dmem_resp_rdy_v)]
        end;
    }.

    #[export] Instance flops_structured: StructuredState Flops := {
      from_state :=
        fun state =>
          dmem_v <- sfind dmem state;
          int_resp_vld_v <- sfind int_resp_vld state;
          int_resp_v <- sfind int_resp state;
            Sret {|
              dmem_v := harr dmem_v;
              int_resp_vld_v := hbits int_resp_vld_v;
              int_resp_v := hbits int_resp_v;
            |};
      to_state :=
        fun f =>
          match f with
          | {| dmem_v := dmem_v;
               int_resp_vld_v := int_resp_vld_v;
               int_resp_v := int_resp_v |} =>
            HMapStr [(dmem, HMapArr dmem_v);
                    (int_resp_vld, HMapBits int_resp_vld_v);
                    (int_resp, HMapBits int_resp_v)]
          end;
    }.

    Definition etrs (eid: vid_t): trsOk MTrs := Fail TrsUndeclared.

    Definition mtrs : MTrsOf M.m fmapEmpty etrs Inputs Flops.
    Proof.
      unshelve epose (trs := _ : MTrs).
      { apply Build_MTrs. 1-2: shelve.
        intros inputs flops.
        destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
        destruct (from_state (A := Flops) flops) as [f_format|]; [| eapply (_, _)].
        destruct i_format, f_format. eapply (_, _). }

      apply mk_MTrsOf with (mtrsof_mtrs := trs).
      1-2: vm_compute; reflexivity.
      red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
      destruct (from_state inputs) as [[]|], (from_state flops) as [[]|] in *; vm_compute in Htrs; injection Htrs as <- <-.
      2-4: eauto.
      eexists. split; [split|..].
      { eapply trsM_iff_rep_is_chain with (n := 1%nat). vm_compute. reflexivity. }
      all: vm_compute; reflexivity.
    Defined.

  End AbsOps.

End DCacheA.
