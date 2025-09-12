Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.

Require Import Ex.RvCore.Common Ex.RvCore.Mem.
Import Mem.ICache Mem.DCache.

Module Spec.

  Module M.
    Notation "'spec'" := spec (in custom ce_top).
    Include Notations.

    Definition m: @VModuleDecl vid_t := #[
module spec
  #(parameter integer ADDR_SIZE = 32,
    parameter integer IADDR_SIZE = 32,
    parameter integer RF_SIZE = 32,
    parameter integer DATA_SIZE = 32,
    parameter integer INST_SIZE = 32)
   (input logic                   clk,
    input logic                   rst_n,
    output logic                  pc_commit_vld,
    output logic [IADDR_SIZE-1:0] pc_commit);

   logic [ADDR_SIZE-1:0]          pc;
   logic                          imem_req_vld;
   logic [IADDR_SIZE-1:0]         imem_req;

   assign imem_req_vld = 1'b1;
   assign imem_req = pc;

   logic                          imem_resp_vld;
   logic [INST_SIZE-1:0]          imem_resp;

   icache icache(.clk(clk),
                 .rst_n(rst_n),
                 .imem_req_vld(imem_req_vld),
                 .imem_req(imem_req),
                 .imem_resp_vld(imem_resp_vld),
                 .imem_resp(imem_resp));

   logic [INST_SIZE-1:0] inst_cur;
   assign inst_cur = imem_resp;

   logic [6:0]           opcode;
   logic [4:0]           rs1;
   logic [4:0]           rs2;
   logic [4:0]           rd;
   logic [2:0]           funct3;
   logic [6:0]           funct7;
   logic [11:0]          imm_i;
   logic [11:0]          imm_s;
   logic [12:0]          imm_b;
   logic [19:0]          imm_u;
   logic [20:0]          imm_j;

   assign opcode = inst_cur[6:0];
   assign rs1 = inst_cur[19:15];
   assign rs2 = inst_cur[24:20];
   assign rd = inst_cur[11:7];
   assign funct3 = inst_cur[14:12];
   assign funct7 = inst_cur[31:25];
   assign imm_i = inst_cur[31:20];
   assign imm_s = (12 '(inst_cur[31:25]) << 5) | inst_cur[11:7];
   assign imm_b = 13 '((32 '(inst_cur[31:31]) << 12) | (32 '(inst_cur[30:25]) << 5) | (32 '(inst_cur[11:8]) << 1) | (32 '(inst_cur[7:7]) << 11));
   assign imm_u = inst_cur[31:12];
   assign imm_j = 21 '((32 '(inst_cur[31:31]) << 20) | (32 '(inst_cur[30:21]) << 1) | (32 '(inst_cur[20:20]) << 11) | (32 '(inst_cur[19:12]) << 12));

   logic [RF_SIZE-1:0][DATA_SIZE-1:0] rf;
   logic [DATA_SIZE-1:0]  rsv1, rsv2;
   assign rsv1 = DATA_SIZE '(rs1 ? rf[rs1] : 'd0 );
   assign rsv2 = DATA_SIZE '(rs2 ? rf[rs2] : 'd0 );

   localparam [6:0] op_branch = 7'b1100011;
   localparam [6:0] op_load = 7'b0000011;
   localparam [6:0] op_store = 7'b0100011;
   localparam [6:0] op_system = 7'b1110011;
   localparam [6:0] op_misc = 7'b0001111;

   logic [ADDR_SIZE-1:0] pc_next;
   assign pc_next = get_next_pc(pc, opcode, funct3, rsv1, rsv2, imm_b, imm_i, imm_j);
   assign pc_commit = pc;
   assign pc_commit_vld = 1'b1;

   always @(posedge clk) begin
      if (!rst_n) pc <= 'd0;
      else pc <= pc_next;
   end

   logic                 dmem_req_vld;
   logic                 dmem_req_ld;
   logic [ADDR_SIZE-1:0] dmem_req_ld_addr;
   logic [ADDR_SIZE-1:0] dmem_req_st_addr;
   logic [1:0]           dmem_req_st_ty;
   logic [DATA_SIZE-1:0] dmem_req_data;

   assign dmem_req_vld = opcode == op_load || opcode == op_store;
   assign dmem_req_ld = opcode == op_load;
   assign dmem_req_ld_addr = rsv1 + $signed(imm_i);
   assign dmem_req_st_addr = rsv1 + $signed(imm_s);
   assign dmem_req_st_ty = funct3[1:0];
   assign dmem_req_data = rsv2;

   logic                 dmem_resp_vld;
   logic [DATA_SIZE-1:0] dmem_resp;

   dcache dcache(.clk(clk),
                 .rst_n(rst_n),
                 .dmem_req_vld(dmem_req_vld),
                 .dmem_req_ld(dmem_req_ld),
                 .dmem_req_ld_addr(dmem_req_ld_addr),
                 .dmem_req_st_addr(dmem_req_st_addr),
                 .dmem_req_st_ty(dmem_req_st_ty),
                 .dmem_req_data(dmem_req_data),
                 .dmem_resp_vld(dmem_resp_vld),
                 .dmem_resp(dmem_resp));

   logic [DATA_SIZE-1:0] dmem_resp_ld;
   assign dmem_resp_ld = get_ld_val(funct3, dmem_resp);

   logic rd_upd, rd_upd_by_load;
   assign rd_upd = opcode != op_branch && opcode != op_store && opcode != op_system && opcode != op_misc;
   assign rd_upd_by_load = opcode == op_load;

   logic [DATA_SIZE-1:0] rd_exec_val;
   assign rd_exec_val = get_exec_value(pc, opcode, funct3, funct7, rsv1, rsv2, imm_i, imm_u);

   always @(posedge clk) begin
      if (!rst_n) rf <= {'d0};
      else if (rd_upd) rf[rd] <= rd_upd_by_load ? dmem_resp_ld : rd_exec_val;
   end

endmodule].

  End M.

  Record Inputs :=
    { rst_n_v: SZ }.

  Record Flops :=
    { pc_v: SZ;
      rf_v: list (Z * Value);
      icache_v: ICache.Flops;
      dcache_v: DCache.Flops }.

  Section Helpers.
    Context `{sz_ops} `{array_ops hmap}.
    Variables (ldvf pcf execf: State -> SZ).

    Import ListNotations.
    Import HMapNotations.

    #[export] Instance inputs_structured: StructuredState Inputs := {|
      from_state :=
        fun state =>
          rst_n_v <- sfind rst_n state;
            Sret {| rst_n_v := hbits rst_n_v |};
      to_state := fun i =>
        match i with
        | {| rst_n_v := rst_n_v |} =>
          HMapStr ([(rst_n, HMapBits rst_n_v)])
        end
    |}.


    #[export] Instance flops_structured: StructuredState Flops := {|
      from_state :=
        fun state =>
          pc_v <- sfind pc state;
          rf_v <- sfind rf state;
          icache_s <- sfind icache state;
          icache_v <- from_state (A := ICache.Flops) icache_s;
          dcache_s <- sfind dcache state;
          dcache_v <- from_state (A := DCache.Flops) dcache_s;
          Sret {|
            pc_v := hbits pc_v;
            rf_v := harr rf_v;
            icache_v := icache_v;
            dcache_v := dcache_v
          |};
      to_state := fun f =>
        match f with
        | {|pc_v := pc_v;
            rf_v := rf_v;
            icache_v := icache_v;
            dcache_v := dcache_v |} =>
         HMapStr ([(pc, HMapBits pc_v);
                 (rf, HMapArr rf_v);
                 (icache, to_state icache_v);
                 (dcache, to_state dcache_v)])
        end
    |}.

    Definition etrs (eid: vid_t): trsOk MTrs :=
      match eid with
      | icache => Sret (ICache.mtrs: MTrs)
      | dcache => Sret (DCache.mtrs: MTrs)
      | _ => Fail TrsUndeclared
      end.

  End Helpers.

  Section TrsAbsFuncs.
    Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.
    Variables (ldvf pcf execf: State -> SZ) (btbf: State -> Z).

    Import ListNotations.
    Import HMapNotations.

    Definition mtrs_abs_funcs: MTrsOf M.m (funcs_abs ldvf pcf execf) etrs Inputs Flops.
    Proof.
      destruct SZ_OPS eqn: Hsz_ops, ARRAY_OPS eqn: Harray_ops.
      match (type of Hsz_ops) with | SZ_OPS = ?a => set (SZ_OPS' := a) end.
      match (type of Harray_ops) with | ARRAY_OPS = ?a => set (ARRAY_OPS' := a) end.
      clear Hsz_ops SZ_OPS ARRAY_OPS Harray_ops.

      unshelve epose (trs := _ : MTrs).
      { apply Build_MTrs. 1-2: shelve.
        intros inputs flops.
        destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
        destruct (from_state (A := Flops) flops) as [f_format|]; [| eapply (_, _)].
        destruct i_format, f_format as [??[][]]. eapply (_, _). }

      apply mk_MTrsOf with (mtrsof_mtrs := trs).
      1-2: vm_compute; reflexivity.
      red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
      destruct (from_state inputs) as [[]|], (from_state flops) as [[?? [][]]|] in *; injection Htrs as <- <-.
      2-4: reflexivity.
      eexists. split; [split|].
      { eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity. }
      - vm_compute; reflexivity.
      - cbv. reflexivity.
    Defined.

  End TrsAbsFuncs.

  Section Trs.
    Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.

    Definition mtrs:  MTrsOf M.m Functions.f etrs Inputs Flops.
    Proof.
      destruct SZ_OPS eqn: Hsz_ops, ARRAY_OPS eqn: Harray_ops.
      match (type of Hsz_ops) with | SZ_OPS = ?a => set (SZ_OPS' := a) end.
      match (type of Harray_ops) with | ARRAY_OPS = ?a => set (ARRAY_OPS' := a) end.
      clear Hsz_ops SZ_OPS ARRAY_OPS Harray_ops.

      unshelve epose (trs := _ : MTrs).
      { apply Build_MTrs. 1-2: shelve.
        intros inputs flops.
        destruct (from_state (A := Inputs) inputs) as [i_format|]; [| eapply (_, _)].
        destruct (from_state (A := Flops) flops) as [f_format|]; [| eapply (_, _)].
        destruct i_format, f_format as [??[][]]. eapply (_, _). }

      apply mk_MTrsOf with (mtrsof_mtrs := trs).
      1-2: vm_compute; reflexivity.
      red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
      destruct (from_state inputs) as [[]|], (from_state flops) as [[?? [][]]|] in *; injection Htrs as <- <-.
      2-4: reflexivity.
      eexists. split; [split|].
      { eapply trsM_iff_rep_is_chain with (n := 1%nat). cbv. reflexivity. }
      - vm_compute; reflexivity.
      - cbv. reflexivity.
    Defined.

    Definition pkg: ModulePkg :=
      {| mpkg_mtrs := mtrs;
        mpkg_rst_vid := rst_n;
        mpkg_rst_neg := true |}.
 End Trs.

 Section Reset.
  Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.

  Import ListNotations.

  Definition rstS (initial_imem: list (Z * hmap)): State.
  Proof.
    destruct SZ_OPS eqn: Hsz_ops, ARRAY_OPS eqn: Harray_ops.
    match (type of Hsz_ops) with | SZ_OPS = ?a => set (SZ_OPS' := a) end.
    match (type of Harray_ops) with | ARRAY_OPS = ?a => set (ARRAY_OPS' := a) end.
    clear Hsz_ops SZ_OPS ARRAY_OPS Harray_ops.

    let s := (eval vm_compute in (buildReset pkg
      (to_state {| rst_n_v := sznil |})
      (to_state {|pc_v := sznil;
                  rf_v := [];
                  icache_v := {| imem_v := initial_imem|};
                  dcache_v := {| dmem_v := [] |};
                |}))) in exact s.
  Defined.

 End Reset.

End Spec.
