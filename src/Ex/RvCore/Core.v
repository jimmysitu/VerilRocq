Require Import Coq.ZArith.BinInt.
Require Import Coq.Lists.List.
Require Import Lib.Lib. Import SZNotations.
Require Import Lang.Lang.

Require Import Ex.RvCore.Common Ex.RvCore.Frontend Ex.RvCore.Mem.
Import Mem.DCacheA Frontend.Frontend.

Module Core.

  Module M.
    Notation "'core'" := core (in custom ce_top).
    Import Common.Notations.

    Definition m: @VModuleDecl vid := #[
      module core
        #(parameter integer ADDR_SIZE = 32,
          parameter integer IADDR_SIZE = 32,
          parameter integer RF_SIZE = 32,
          parameter integer DATA_SIZE = 32,
          parameter integer INST_SIZE = 32)
        (input logic                  clk,
        input logic                  rst_n,
        output logic                 pc_commit_vld,
        output logic [ADDR_SIZE-1:0] pc_commit);

        logic                         d2e_vld, e2w_vld;
        logic                         d2e_rdy;
        logic                         e2w_avail;
        logic                         exec_now, wb_now;
        logic [ADDR_SIZE-1:0] pc_fetch, pc_fetch_next;
        logic [INST_SIZE-1:0]  inst_d2e;
        logic [ADDR_SIZE-1:0]  pc_d2e;
        logic [4:0]            rd_d2e;
        logic [DATA_SIZE-1:0]  rsv1, rsv2;
        logic [RF_SIZE-1:0][DATA_SIZE-1:0] rf;
        logic [6:0]       opcode;
        logic [2:0]       funct3;
        logic [6:0]       funct7;
        logic [11:0]      imm_i;
        logic [11:0]      imm_s;
        logic [12:0]      imm_b;
        logic [19:0]      imm_u;
        logic [20:0]      imm_j;
        logic [ADDR_SIZE-1:0] pc_exec, pc_exec_next;
        logic                 exec_ok, exec_bad, exec_mem;
        logic                 flush;
        logic [4:0]           rdi;
        logic                 rd_upd;
        logic [DATA_SIZE-1:0] rdv, rdv_cal;
        logic                 wb_ld;
        logic [2:0]           wb_ld_ty;
        logic                   frontend_req_rdy;
        logic                   dmem_req_rdy;
        logic                   dmem_req_vld;
        logic                   dmem_req_ld;
        logic [ADDR_SIZE-1:0]   dmem_req_ld_addr;
        logic [ADDR_SIZE-1:0]   dmem_req_st_addr;
        logic [1:0]             dmem_req_st_ty;
        logic [DATA_SIZE-1:0]   dmem_req_data;
        logic                   dmem_resp_vld;
        logic [DATA_SIZE-1:0]   dmem_resp;
        logic                   dmem_resp_rdy;
        logic [DATA_SIZE-1:0]   dmem_resp_ld;

        (* pc prediction *)
        btb btb(.clk(clk),
                .rst_n(rst_n),
                .pc_cur_pred(pc_fetch),
                .pc_next_pred(pc_fetch_next),
                .upd_vld(exec_bad),
                .pc_cur_upd(pc_exec),
                .pc_next_upd(pc_exec_next));


        (* frontend module *)
        frontend frontend (.clk(clk),
                          .rst_n(rst_n),
                          .flush(exec_bad),
                          .pc_fetch(pc_fetch),
                          .rf(rf),
                          .frontend_req_rdy(frontend_req_rdy),
                          .wb_ld(wb_ld),
                          .e2w_vld(e2w_vld),
                          .rdi(rdi),
                          .rdv(rdv),
                          .d2e_vld(d2e_vld),
                          .d2e_rdy(d2e_rdy),
                          .pc_d2e(pc_d2e),
                          .inst_d2e(inst_d2e),
                          .rsv1(rsv1),
                          .rsv2(rsv2)
                          );

        always @(posedge clk) begin
          if (!rst_n) begin
            pc_fetch <= 'd0;
          end
          else if (exec_bad) begin
            pc_fetch <= pc_exec;
          end
          else if (frontend_req_rdy) begin
            pc_fetch <= pc_fetch_next;
          end
        end

        assign d2e_rdy = e2w_avail && (!exec_mem || dmem_req_rdy);
        assign exec_now = d2e_vld && d2e_rdy;
        assign e2w_avail = !e2w_vld || wb_now;
        assign wb_now = e2w_vld;

        always @(posedge clk) begin
          if (!rst_n) begin e2w_vld <= 1'b0; end
          else begin
            e2w_vld <= (exec_ok && rd_upd) || !e2w_avail;
          end
        end

        localparam [6:0]  op_branch = 7'b1100011;
        localparam [6:0]  op_load = 7'b0000011;
        localparam [6:0]  op_store = 7'b0100011;
        localparam [6:0]  op_system = 7'b1110011;
        localparam [6:0]  op_misc = 7'b0001111;

        assign rd_d2e = inst_d2e[11:7];
        assign opcode = inst_d2e[6:0];
        assign funct3 = inst_d2e[14:12];
        assign funct7 = inst_d2e[31:25];
        assign imm_i = inst_d2e[31:20];
        assign imm_s = (12 '(inst_d2e[31:25]) << 5) | inst_d2e[11:7];
        assign imm_b = 13 '((32 '(inst_d2e[31:31]) << 12) | (32 '(inst_d2e[30:25]) << 5) | (32 '(inst_d2e[11:8]) << 1) | (32 '(inst_d2e[7:7]) << 11));
        assign imm_u = inst_d2e[31:12];
        assign imm_j = 21 '((32 '(inst_d2e[31:31]) << 20) | (32 '(inst_d2e[30:21]) << 1) | (32 '(inst_d2e[20:20]) << 11) | (32 '(inst_d2e[19:12]) << 12));
        assign exec_ok = exec_now && pc_d2e == pc_exec;
        assign exec_bad = exec_now && pc_d2e != pc_exec;

        assign pc_exec_next = get_next_pc(pc_exec, opcode, funct3, rsv1, rsv2, imm_b, imm_i, imm_j);
        always @(posedge clk) begin
          if (!rst_n) pc_exec <= 'd0;
          else if (exec_ok) pc_exec <= pc_exec_next;
        end
        assign exec_mem = opcode == op_load || opcode == op_store;
        assign dmem_req_vld = exec_ok && exec_mem;
        assign dmem_req_ld = opcode == op_load;
        assign dmem_req_ld_addr = rsv1 + $signed(imm_i);
        assign dmem_req_st_addr = rsv1 + $signed(imm_s);
        assign dmem_req_st_ty = funct3[1:0];
        assign dmem_req_data = rsv2;
        assign rd_upd = opcode != op_branch && opcode != op_store && opcode != op_system && opcode != op_misc;
        assign rdv_cal = get_exec_value(pc_exec, opcode, funct3, funct7, rsv1, rsv2, imm_i, imm_u);
        always @(posedge clk) begin
          if (!rst_n) begin
            rdi <= 'd0;
            rdv <= 'd0;
            wb_ld <= 1'b0;
            wb_ld_ty <= 3'b0;
          end
          else if (exec_ok && rd_upd) begin
            rdi <= rd_d2e;
            rdv <= rdv_cal;
            wb_ld <= dmem_req_vld && dmem_req_ld;
            wb_ld_ty <= funct3;
          end
        end
        assign pc_commit_vld = exec_ok;
        assign pc_commit = pc_exec;
        assign dmem_resp_rdy = 1'b1;
        dcache_a dcache_a(.clk(clk),
                          .rst_n(rst_n),
                          .dmem_req_rdy(dmem_req_rdy),
                          .dmem_req_vld(dmem_req_vld),
                          .dmem_req_ld(dmem_req_ld),
                          .dmem_req_ld_addr(dmem_req_ld_addr),
                          .dmem_req_st_addr(dmem_req_st_addr),
                          .dmem_req_st_ty(dmem_req_st_ty),
                          .dmem_req_data(dmem_req_data),
                          .dmem_resp_vld(dmem_resp_vld),
                          .dmem_resp(dmem_resp),
                          .dmem_resp_rdy(dmem_resp_rdy));
        assign dmem_resp_ld = get_ld_val(wb_ld_ty, dmem_resp);
        always @(posedge clk) begin
          if (!rst_n) rf <= {'d0};
          else if (e2w_vld) rf[rdi] <= wb_ld ? dmem_resp_ld : rdv;
        end
      endmodule
    ].

  End M.

  Record Inputs :=
    { rst_n_v: SZ }.

  Record Flops :=
    { e2w_vld_v: SZ;
      pc_fetch_v: SZ;
      pc_exec_v: SZ;
      rdi_v: SZ;
      rdv_v: SZ;
      wb_ld_v: SZ;
      wb_ld_ty_v: SZ;
      dcache_a_v: DCacheA.Flops;
      rf_v: list (Z * Value);
      frontend_v: Frontend.Flops;
      btb_v: unit }.

  Section Helpers.
    Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.
    Variables (btbf: State -> Z).


    Import ListNotations.
    Import HMapNotations.

    #[export] Instance inputs_structured: StructuredState Inputs := {|
      from_state :=
        fun state =>
          rst_n_v <- sfind rst_n state;
            Sret {|
              rst_n_v := hbits rst_n_v
            |};
      to_state := fun i =>
        match i with
        | {| rst_n_v := rst_n_v |} =>
          HMapStr [(rst_n, HMapBits rst_n_v)]
        end
    |}.


    #[export] Instance flops_structured: StructuredState Flops := {|
      from_state :=
        fun state =>
          e2w_vld_v <- sfind e2w_vld state;
          pc_fetch_v <- sfind pc_fetch state;
          pc_exec_v <- sfind pc_exec state;
          rdi_v <- sfind rdi state;
          rdv_v <- sfind rdv state;
          wb_ld_v <- sfind wb_ld state;
          wb_ld_ty_v <- sfind wb_ld_ty state;
          dcache_a_s <- sfind dcache_a state;
          dcache_a_v <- from_state (A := DCacheA.Flops) dcache_a_s;
          rf_v <- sfind rf state;
          frontend_s <- sfind frontend state;
          frontend_v <- from_state (A := Frontend.Flops) frontend_s;
            Sret {|
              e2w_vld_v := hbits e2w_vld_v;
              pc_fetch_v := hbits pc_fetch_v;
              pc_exec_v := hbits pc_exec_v;
              rdi_v := hbits rdi_v;
              rdv_v := hbits rdv_v;
              wb_ld_v := hbits wb_ld_v;
              wb_ld_ty_v := hbits wb_ld_ty_v;
              dcache_a_v := dcache_a_v;
              rf_v := harr rf_v;
              frontend_v := frontend_v;
              btb_v := tt;
            |};
      to_state :=
        fun f =>
          match f with
          | {| e2w_vld_v := e2w_vld_v;
               pc_fetch_v := pc_fetch_v;
               pc_exec_v := pc_exec_v;
               rdi_v := rdi_v;
               rdv_v := rdv_v;
               wb_ld_v := wb_ld_v;
               wb_ld_ty_v := wb_ld_ty_v;
               dcache_a_v := dcache_a_v;
               rf_v := rf_v;
               frontend_v := frontend_v;
               |} =>
            HMapStr [(e2w_vld, HMapBits e2w_vld_v);
                    (pc_fetch, HMapBits pc_fetch_v);
                    (pc_exec, HMapBits pc_exec_v);
                    (rdi, HMapBits rdi_v);
                    (rdv, HMapBits rdv_v);
                    (wb_ld, HMapBits wb_ld_v);
                    (wb_ld_ty, HMapBits wb_ld_ty_v);
                    (dcache_a, to_state dcache_a_v);
                    (rf, HMapArr rf_v);
                    (frontend, to_state frontend_v);
                    (btb, [])]
          end
    |}.

    Definition etrs (eid: vid): trsOk MTrs :=
    match eid with
    | frontend => Sret (Frontend.mtrs : MTrs)
    | dcache_a => Sret (DCacheA.mtrs : MTrs)
    | btb => Sret {| mtrs_input_vids := clk :: rst_n :: nil;
                    mtrs_output_vids := pc_next_pred :: nil;
                    mtrs_func := fun ins flops => ([], HMapStr ((pc_next_pred, HMapBits #{btbf flops, 32, false}) :: nil))
                  |}
    | _ => Fail TrsUndeclared
    end.

  End Helpers.

  Section TrsAbsFuncs.
    Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.
    Variables (ldvf pcf execf: State -> SZ) (btbf: State -> Z).

    Import ListNotations.
    Import HMapNotations.

    Definition mtrs_abs_funcs : MTrsOf M.m (funcs_abs ldvf pcf execf) (etrs btbf) Inputs Flops.
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
        destruct i_format, f_format as [??????? [] ? [??????? []]]. eapply (_, _). }

      apply mk_MTrsOf with (mtrsof_mtrs := trs).
      1-2: vm_compute; reflexivity.
      red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
      destruct (from_state inputs) as [[]|], (from_state flops) as [[??????? [] ? [??????? []]]|] in *; vm_compute in Htrs; injection Htrs as <- <-.
      2-4: reflexivity.
      eexists. split; [split|].
      { eapply trsM_iff_rep_is_chain with (n := 4%nat). cbv. reflexivity. }
      - vm_compute; reflexivity.
      - cbv. reflexivity.
    Defined.

  End TrsAbsFuncs.

  Section Trs.
    Context `{SZ_OPS: sz_ops} `{ARRAY_OPS: array_ops hmap}.
    Variables (btbf: State -> Z).

    Import ListNotations.
    Import HMapNotations.

    Definition mtrs : MTrsOf M.m Functions.f (etrs btbf) Inputs Flops.
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
        destruct i_format, f_format as [??????? [] ? [??????? []]]. eapply (_, _). }

      apply mk_MTrsOf with (mtrsof_mtrs := trs).
      1-2: vm_compute; reflexivity.
      red. intros ???? Htrs. subst trs. unfold mtrs_func in Htrs. unfold format.
      destruct (from_state inputs) as [[]|], (from_state flops) as [[??????? [] ? [??????? []]]|] in *; vm_compute in Htrs; injection Htrs as <- <-.
      2-4: reflexivity.
      eexists. split; [split|].
      { eapply trsM_iff_rep_is_chain with (n := 4%nat). cbv. reflexivity. }
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
    Variables (btbf: State -> Z).

    Definition rstS (initial_imem: list (Z * hmap)): State.
    Proof.
      destruct SZ_OPS eqn: Hsz_ops, ARRAY_OPS eqn: Harray_ops.
      match (type of Hsz_ops) with | SZ_OPS = ?a => set (SZ_OPS' := a) end.
      match (type of Harray_ops) with | ARRAY_OPS = ?a => set (ARRAY_OPS' := a) end.
      clear Hsz_ops SZ_OPS ARRAY_OPS Harray_ops.
      let s := (eval vm_compute in (buildReset (pkg btbf)
        (to_state {| rst_n_v := sznil |})
        (to_state {|e2w_vld_v := sznil;
                    pc_fetch_v := sznil;
                    pc_exec_v := sznil;
                    rdi_v := sznil;
                    rdv_v := sznil;
                    wb_ld_v := sznil;
                    wb_ld_ty_v := sznil;
                    dcache_a_v := {|
                      DCacheA.dmem_v := nil;
                      DCacheA.int_resp_vld_v := sznil;
                      DCacheA.int_resp_v := sznil
                    |};
                    rf_v := nil;
                    frontend_v := {|
                      pc_f2d_v := sznil;
                      pc_f2d_vld_v := sznil;
                      d2e_vld_v := sznil;
                      pc_d2e_v := sznil;
                      inst_d2e_v := sznil;
                      rsv1_v := sznil;
                      rsv2_v := sznil;
                      icache_a_v := {|
                        ICacheA.imem_v := initial_imem;
                        ICacheA.int_resp_vld_v := sznil;
                        ICacheA.int_resp_v := sznil
                      |}
                    |};
                    btb_v := tt;
                  |}))) in exact s.
    Defined.


  End Reset.

End Core.
