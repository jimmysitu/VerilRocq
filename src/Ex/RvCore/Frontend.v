Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.

Require Import Ex.RvCore.Common.
Require Import Ex.RvCore.Mem.
Import Mem.ICacheA.

Module Frontend.

  Module M.
    Notation "'frontend'" := frontend (in custom ce_top).
    Import Notations.

    Definition m: @VModuleDecl vid_t := #[
module frontend
  #(parameter integer ADDR_SIZE = 32,
    parameter integer IADDR_SIZE = 32,
    parameter integer RF_SIZE = 32,
    parameter integer DATA_SIZE = 32,
    parameter integer INST_SIZE = 32)
  (input logic                  clk,
    input logic                  rst_n,
    input logic                  flush,
    input logic [ADDR_SIZE-1:0]  pc_fetch,
    input logic [RF_SIZE-1:0][DATA_SIZE-1:0] rf,
    output logic                 frontend_req_rdy,
    input logic                  wb_ld,
    input logic                  e2w_vld,
    input logic [4:0]            rdi,
    input logic [DATA_SIZE-1:0]  rdv,
    output logic                 d2e_vld,
    input logic                  d2e_rdy,
    output logic [ADDR_SIZE-1:0] pc_d2e,
    output logic [INST_SIZE-1:0] inst_d2e,
    output logic [DATA_SIZE-1:0] rsv1,
    output logic [DATA_SIZE-1:0] rsv2);
  logic [ADDR_SIZE-1:0]      pc_f2d;
  logic                      pc_f2d_vld;
  logic                      pc_f2d_rdy;
  logic                      pc_f2d_in_vld;
  logic                      pc_f2d_in_rdy;
  logic                      imem_req_rdy;
  logic                      imem_req_vld;
  logic                      imem_resp_vld;
  logic [INST_SIZE-1:0]      imem_resp;
  logic                      imem_resp_rdy;
  logic                      f2d_vld;
  logic                      f2d_rdy;
  logic                      d2e_avail;
  logic                      decode_now;
  logic [4:0]                rs1, rs2;
  logic [4:0]                rd_d2e;
  logic                      rd_stall;
  logic [INST_SIZE-1:0]      inst_dec;

  (* --- Fetch --- *)
  assign frontend_req_rdy = pc_f2d_in_rdy && imem_req_rdy;
  assign pc_f2d_in_vld = imem_req_rdy;
  assign imem_req_vld = pc_f2d_in_rdy;

  (* pc_f2d register *)
  assign pc_f2d_in_rdy = !pc_f2d_vld || pc_f2d_rdy;

  always @(posedge clk) begin
    if (!rst_n || flush) begin
      pc_f2d <= 'd0;
      pc_f2d_vld  <= 1'b0;
    end
    else if (pc_f2d_in_vld && pc_f2d_in_rdy) begin
      pc_f2d  <= pc_fetch;
      pc_f2d_vld <= 1'b1;
    end
    else if (pc_f2d_rdy) begin
      pc_f2d_vld <= 1'b0;
    end
  end

  (* imem *)
  icache_a icache_a(.clk(clk),
                    .flush(flush),
                    .rst_n(rst_n),
                    .imem_req_rdy(imem_req_rdy),
                    .imem_req_vld(imem_req_vld),
                    .imem_req(pc_fetch),
                    .imem_resp_vld(imem_resp_vld),
                    .imem_resp(imem_resp),
                    .imem_resp_rdy(imem_resp_rdy));

  (* Join *)
  assign pc_f2d_rdy = f2d_rdy && imem_resp_vld;
  assign imem_resp_rdy = f2d_rdy && pc_f2d_vld;
  assign f2d_vld = imem_resp_vld && pc_f2d_vld;

  (* --- End Fetch --- *)

  (* --- Decode --- *)
  (* f2d interface *)
  assign f2d_rdy = d2e_avail && !rd_stall;
  assign decode_now = f2d_vld && f2d_rdy;

  (* Instruction decoding *)
  assign inst_dec = imem_resp;
  assign rs1 = inst_dec[19:15];
  assign rs2 = inst_dec[24:20];
  assign rd_d2e = inst_d2e[11:7];

  (* Check stall condition *)
  assign rd_stall = (d2e_vld && (rs1 == rd_d2e || rs2 == rd_d2e)) ||
                    (e2w_vld && wb_ld && (rs1 == rdi || rs2 == rdi));

  (* d2e register *)
  assign d2e_avail = !d2e_vld || d2e_rdy;

  always @(posedge clk) begin
    if (!rst_n || flush) begin
      d2e_vld <= 1'b0;
      pc_d2e   <= 'd0;
      inst_d2e <= 'd0;
      rsv1 <= 'd0;
      rsv2 <= 'd0;
    end
    else if (decode_now) begin
      d2e_vld <= 1'b1;
      pc_d2e   <= pc_f2d;
      inst_d2e <= inst_dec;
      rsv1 <= DATA_SIZE '(rs1 ? ((e2w_vld && !wb_ld && rs1 == rdi) ? rdv : rf[rs1]) : 'd0 );
      rsv2 <= DATA_SIZE '(rs2 ? ((e2w_vld && !wb_ld && rs2 == rdi) ? rdv : rf[rs2]) : 'd0 );
    end
    else if (d2e_rdy) begin
      d2e_vld <= 1'b0;
    end
  end

  (* --- End Decode --- *)
endmodule].
  End M.

  Record Inputs :=
    { rst_n_v: SZ;
      pc_fetch_v: SZ;
      rf_v: list (Z * Value);
      d2e_rdy_v: SZ;
      e2w_vld_v: SZ;
      wb_ld_v: SZ;
      rdi_v: SZ;
      rdv_v: SZ;
      flush_v: SZ; }.

  Record Flops :=
    { pc_f2d_v: SZ;
      pc_f2d_vld_v: SZ;
      d2e_vld_v: SZ;
      pc_d2e_v: SZ;
      inst_d2e_v: SZ;
      rsv1_v: SZ;
      rsv2_v: SZ;
      icache_a_v: ICacheA.Flops }.

  Section AbsOps.
    Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.

    Import ListNotations.
    Import HMapNotations.

    #[export] Instance inputs_structured: StructuredState Inputs := {|
      from_state :=
        fun state =>
          rst_n_v <- sfind rst_n state;
          pc_fetch_v <- sfind pc_fetch state;
          rf_v <- sfind rf state;
          d2e_rdy_v <- sfind d2e_rdy state <~ [];
          e2w_vld_v <- sfind e2w_vld state;
          wb_ld_v <- sfind wb_ld state;
          rdi_v <- sfind rdi state;
          rdv_v <- sfind rdv state;
          flush_v <- sfind flush state <~ [];
            Sret {|
              rst_n_v := hbits rst_n_v;
              pc_fetch_v := hbits pc_fetch_v;
              rf_v := harr rf_v;
              d2e_rdy_v := hbits d2e_rdy_v;
              e2w_vld_v := hbits e2w_vld_v;
              wb_ld_v := hbits wb_ld_v;
              rdi_v := hbits rdi_v;
              rdv_v := hbits rdv_v;
              flush_v := hbits flush_v;
            |};
      to_state :=
        fun i =>
          match i with
            {| rst_n_v := rst_n_v;
               pc_fetch_v := pc_fetch_v;
               rf_v := rf_v;
               d2e_rdy_v := d2e_rdy_v;
               e2w_vld_v := e2w_vld_v;
               wb_ld_v := wb_ld_v;
               rdi_v := rdi_v;
               rdv_v := rdv_v;
               flush_v := flush_v;|} =>
            HMapStr [(rst_n, HMapBits rst_n_v);
                    (pc_fetch, HMapBits pc_fetch_v);
                    (rf, HMapArr rf_v);
                    (d2e_rdy, HMapBits d2e_rdy_v);
                    (e2w_vld, HMapBits e2w_vld_v);
                    (wb_ld, HMapBits wb_ld_v);
                    (rdi, HMapBits rdi_v);
                    (rdv, HMapBits rdv_v);
                    (flush, HMapBits flush_v)]
          end
    |}.

    #[export] Instance flops_structured: StructuredState Flops := {|
      from_state :=
        fun state =>
          pc_f2d_v <- sfind pc_f2d state;
          pc_f2d_vld_v <- sfind pc_f2d_vld state;
          d2e_vld_v <- sfind d2e_vld state;
          pc_d2e_v <- sfind pc_d2e state;
          inst_d2e_v <- sfind inst_d2e state;
          rsv1_v <- sfind rsv1 state;
          rsv2_v <- sfind rsv2 state;
          icache_a_s <- sfind icache_a state;
          icache_a_v <- from_state (A := ICacheA.Flops) icache_a_s;
            Sret {|
              pc_f2d_v := hbits pc_f2d_v;
              pc_f2d_vld_v := hbits pc_f2d_vld_v;
              d2e_vld_v := hbits d2e_vld_v;
              pc_d2e_v := hbits pc_d2e_v;
              inst_d2e_v := hbits inst_d2e_v;
              rsv1_v := hbits rsv1_v;
              rsv2_v := hbits rsv2_v;
              icache_a_v := icache_a_v
            |};
      to_state :=
        fun f =>
          match f with
            {| pc_f2d_v := pc_f2d_v;
               pc_f2d_vld_v := pc_f2d_vld_v;
               d2e_vld_v := d2e_vld_v;
               pc_d2e_v := pc_d2e_v;
               inst_d2e_v := inst_d2e_v;
               rsv1_v := rsv1_v;
               rsv2_v := rsv2_v;
               icache_a_v := icache_a_v |} =>
            HMapStr [(pc_f2d, HMapBits pc_f2d_v);
                    (pc_f2d_vld, HMapBits pc_f2d_vld_v);
                    (d2e_vld, HMapBits d2e_vld_v);
                    (pc_d2e, HMapBits pc_d2e_v);
                    (inst_d2e, HMapBits inst_d2e_v);
                    (rsv1, HMapBits rsv1_v);
                    (rsv2, HMapBits rsv2_v);
                    (icache_a, to_state icache_a_v)]
          end
    |}.

    Record Outputs := {
      frontend_req_rdy_out: SZ;
      d2e_vld_out: SZ;
      pc_d2e_out: SZ;
      inst_d2e_out: SZ;
      rsv1_out: SZ;
      rsv2_out: SZ;
    }.

    Definition output_to_state (outputs: Outputs): State :=
      HMapStr [(d2e_vld, HMapBits outputs.(d2e_vld_out));
               (pc_d2e, HMapBits outputs.(pc_d2e_out));
               (inst_d2e, HMapBits outputs.(inst_d2e_out));
               (rsv1, HMapBits outputs.(rsv1_out));
               (rsv2, HMapBits outputs.(rsv2_out));
               (frontend_req_rdy, HMapBits outputs.(frontend_req_rdy_out))].

    Record Updates := {
      d2e_vld_update: State;
      pc_d2e_update: State;
      inst_d2e_update: State;
      rsv1_update: State;
      rsv2_update: State;
      icache_a_update: ICacheA.Updates;
      pc_f2d_vld_update: State;
      pc_f2d_update: State;
    }.

    Definition update_to_state (upds: Updates): State :=
      HMapStr [(pc_f2d_vld, upds.(pc_f2d_vld_update));
               (pc_f2d, upds.(pc_f2d_update));
               (icache_a, ICacheA.update_to_state upds.(icache_a_update));
               (d2e_vld, upds.(d2e_vld_update));
               (pc_d2e, upds.(pc_d2e_update));
               (inst_d2e, upds.(inst_d2e_update));
               (rsv1, upds.(rsv1_update));
               (rsv2, upds.(rsv2_update))].

    Definition etrs (eid: vid): trsOk MTrs :=
        match eid with
        | icache_a => Sret (ICacheA.mtrs : MTrs)
        | _ => Fail TrsUndeclared
        end.

  End AbsOps.

  Section Trs.
    Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.

    Import ListNotations.
    Import HMapNotations.

    Definition trs_structured_sigT: {trs: forall (inputs: Inputs) (flops: Flops), (Updates * Outputs) |
      is_module_trs M.m fmapEmpty etrs Inputs Flops (to_unstructured_trs update_to_state output_to_state trs)
    }.
    Proof.
      destruct SZ_OPS eqn: Hsz_ops, ARRAY_OPS eqn: Harray_ops.
      match (type of Hsz_ops) with | SZ_OPS = ?a => set (SZ_OPS' := a) end.
      match (type of Harray_ops) with | ARRAY_OPS = ?a => set (ARRAY_OPS' := a) end.
      clear Hsz_ops SZ_OPS ARRAY_OPS Harray_ops.

      unshelve epose (trs := _ : Inputs -> Flops -> Updates * Outputs).
      { intros i f. destruct i, f. split; econstructor; shelve. }
      exists trs. subst trs.
      red. unfold to_unstructured_trs. intros ???? Htrs. unfold format.
      destruct (from_state inputs) as [[]|], (from_state flops) as [[??????? []]|] in *; cbv in Htrs; injection Htrs as <- <-.
      2-4: auto.
      eexists. split; [split|].
      - eapply trsM_iff_rep_is_chain with (n := 6%nat).
        cbv. (* Note: should not use vm_compute here since it ignores Opaque settings. *)
        reflexivity.
      - vm_compute; reflexivity.
      - cbv; reflexivity.
    Defined.

    Definition trs_structured := proj1_sig trs_structured_sigT.

    Definition mtrs: MTrsOf M.m fmapEmpty etrs Inputs Flops.
    Proof.
      eapply mk_MTrsOf with (mtrsof_mtrs := (Build_MTrs _ _ (to_unstructured_trs _ _ trs_structured))).
      1-2: vm_compute; reflexivity. unfold mtrs_func.
      eapply (proj2_sig trs_structured_sigT).
    Defined.

    #[global] Opaque trs_structured.

  End Trs.

End Frontend.
