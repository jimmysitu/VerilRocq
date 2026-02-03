Require Import Coq.ZArith.BinInt.
Require Import Lib.Lib. Import SZNotations. Import HMapNotations.
Require Import Lang.Lang.

Local Open Scope hmap_scope.

Inductive vid :=
| clk | rst_n

| spec
| ADDR_SIZE | IADDR_SIZE | RF_SIZE | DATA_SIZE | INST_SIZE
| step | pc_commit_vld | pc_commit
| imem_req_vld | imem_req | imem_req_truncated | imem_resp_vld | imem_resp
| dmem_req_vld | dmem_req_ld | dmem_req_ld_addr | dmem_req_ld_addr_truncated | dmem_resp_vld | dmem_resp
| dmem_req_st_ty | dmem_req_data | dmem_req_st_addr | dmem_req_st_addr_truncated
| pc | inst | inst_cur
| opcode | rs1 | rs2 | rd | funct3 | funct7 | imm_i | imm_s | imm_b | imm_u | imm_j
| rf | rsv1 | rsv2 | rd_stall
| op_reg_reg | op_reg_imm | op_lui | op_auipc | op_branch | op_jal | op_jalr | op_load | op_store | op_system | op_misc
| funct3_add_sub | funct3_sll | funct3_slt | funct3_sltu | funct3_xor | funct3_srl_sra | funct3_or | funct3_and
| funct7_add | funct7_sub | funct7_srl | funct7_sra
| funct3_beq | funct3_bne | funct3_blt | funct3_bge | funct3_bltu | funct3_bgeu
| funct3_lb | funct3_lh | funct3_lw | funct3_lbu | funct3_lhu | funct3_sb | funct3_sh | funct3_sw
| pc_next | dmem_resp_ld
| rd_upd | rd_upd_by_load | rd_exec_val
| get_ld_val | get_next_pc | get_exec_value

| frontend
| frontend_req_rdy
| imem_req_rdy | imem_resp_rdy
| f2d_vld | f2d_rdy
| pc_f2d | pc_f2d_vld | pc_f2d_rdy
| pc_f2d_in_vld | pc_f2d_in_rdy

| core
| dmem_req_rdy | dmem_resp_rdy
| d2e_vld | d2e_rdy | e2w_vld | d2e_avail | e2w_avail
| decode_now | exec_now | wb_now
| pc_fetch | pc_fetch_next
| btb_upd_vld | btb_upd_pc_cur | btb_upd_pc_next
| inst_dec | inst_d2e | pc_d2e | rd_d2e
| pc_exec | pc_exec_next | exec_ok | exec_bad | exec_mem | flush
| rdi | rdv | rdv_cal
| wb_mem | wb_ld | wb_ld_ty

| btb
| pc_cur_pred | pc_next_pred | upd_vld | pc_cur_upd | pc_next_upd

| icache
| ICACHE_SIZE | imem

| dcache
| DCACHE_SIZE | dmem
| req_data | st_data | st_read_data

| icache_a | u_icache_a
| int_resp_vld | int_resp

| dcache_a

| functions.

Definition vid_vid_eq_dec: forall (v1 v2: vid), {v1 = v2} + {v1 <> v2} := ltac:(decide equality).

#[global] Instance vid_vid_t_c: vid_t_c :=
  {| vid_t := vid |}.

#[global] Instance vid_vid_ops: vid_ops :=
  {| vid_eq_dec := vid_vid_eq_dec |}.

Definition get_ld_val_f_abs (f: State -> SZ): Func :=
  {| func_input_vids := funct3 :: dmem_resp :: nil;
    func_func := fun i => HMapBits (f i) |}.

Definition next_pc_f_abs (f: State -> SZ): Func :=
  {| func_input_vids := pc :: opcode :: funct3 :: rsv1 :: rsv2 :: imm_b :: imm_i :: imm_j :: nil;
    func_func := fun i => HMapBits (f i) |}.

Definition exec_value_f_abs (f: State -> SZ): Func :=
  {| func_input_vids := pc :: opcode :: funct3 :: funct7 :: rsv1 :: rsv2 :: imm_i :: imm_u :: nil;
    func_func := fun i => HMapBits (f i) |}.

Definition funcs_abs (ldvf pcf execf: State -> SZ): Funcs :=
  fun fid => match fid with
             | get_ld_val => Sret (get_ld_val_f_abs ldvf)
             | get_next_pc => Sret (next_pc_f_abs pcf)
             | get_exec_value => Sret (exec_value_f_abs execf)
             | _ => Fail TrsUndeclared
             end.

Module Notations.

  Notation "'.clk'" := clk (in custom ce_portconnid).
  Notation "'.rst_n'" := rst_n (in custom ce_portconnid).

  (* frontend ports *)
  Notation "'.frontend_req_rdy'" := frontend_req_rdy (in custom ce_portconnid).
  Notation "'.pc_fetch'" := pc_fetch (in custom ce_portconnid).
  Notation "'.rf'" := rf (in custom ce_portconnid).
  Notation "'.e2w_vld'" := e2w_vld (in custom ce_portconnid).
  Notation "'.wb_ld'" := wb_ld (in custom ce_portconnid).
  Notation "'.rdi'" := rdi (in custom ce_portconnid).
  Notation "'.rdv'" := rdv (in custom ce_portconnid).
  Notation "'.d2e_vld'" := d2e_vld (in custom ce_portconnid).
  Notation "'.d2e_rdy'" := d2e_rdy (in custom ce_portconnid).
  Notation "'.pc_d2e'" := pc_d2e (in custom ce_portconnid).
  Notation "'.inst_d2e'" := inst_d2e (in custom ce_portconnid).
  Notation "'.rsv1'" := rsv1 (in custom ce_portconnid).
  Notation "'.rsv2'" := rsv2 (in custom ce_portconnid).
  Notation "'.flush'" := flush (in custom ce_portconnid).

  (* btb ports *)
  Notation "'.pc_cur_pred'" := pc_cur_pred (in custom ce_portconnid).
  Notation "'.pc_next_pred'" := pc_next_pred (in custom ce_portconnid).
  Notation "'.upd_vld'" := upd_vld (in custom ce_portconnid).
  Notation "'.pc_cur_upd'" := pc_cur_upd (in custom ce_portconnid).
  Notation "'.pc_next_upd'" := pc_next_upd (in custom ce_portconnid).

  (* icache ports *)
  Notation "'.imem_req_vld'" := imem_req_vld (in custom ce_portconnid).
  Notation "'.imem_req'" := imem_req (in custom ce_portconnid).
  Notation "'.imem_resp_vld'" := imem_resp_vld (in custom ce_portconnid).
  Notation "'.imem_resp'" := imem_resp (in custom ce_portconnid).

  (* dcache ports *)
  Notation "'.dmem_req_vld'" := dmem_req_vld (in custom ce_portconnid).
  Notation "'.dmem_req_ld'" := dmem_req_ld (in custom ce_portconnid).
  Notation "'.dmem_req_ld_addr'" := dmem_req_ld_addr (in custom ce_portconnid).
  Notation "'.dmem_req_st_addr'" := dmem_req_st_addr (in custom ce_portconnid).
  Notation "'.dmem_req_st_ty'" := dmem_req_st_ty (in custom ce_portconnid).
  Notation "'.dmem_req_data'" := dmem_req_data (in custom ce_portconnid).
  Notation "'.dmem_resp_vld'" := dmem_resp_vld (in custom ce_portconnid).
  Notation "'.dmem_resp'" := dmem_resp (in custom ce_portconnid).

  (* icache_a ports *)
  Notation "'.imem_req_rdy'" := imem_req_rdy (in custom ce_portconnid).
  Notation "'.imem_resp_rdy'" := imem_resp_rdy (in custom ce_portconnid).

  (* dcache_a ports *)
  Notation "'.dmem_req_rdy'" := dmem_req_rdy (in custom ce_portconnid).
  Notation "'.dmem_resp_rdy'" := dmem_resp_rdy (in custom ce_portconnid).

  (* module instances *)
  Notation "'btb'" := btb (in custom ce_expr).
  Notation "'icache'" := icache (in custom ce_expr).
  Notation "'dcache'" := dcache (in custom ce_expr).
  Notation "'icache_a'" := icache_a (in custom ce_expr).
  Notation "'u_icache_a'" := u_icache_a (in custom ce_expr).
  Notation "'dcache_a'" := dcache_a (in custom ce_expr).

  Notation "'ADDR_SIZE'" := ADDR_SIZE (in custom ce_expr).
  Notation "'IADDR_SIZE'" := IADDR_SIZE (in custom ce_expr).
  Notation "'RF_SIZE'" := RF_SIZE (in custom ce_expr).
  Notation "'DATA_SIZE'" := DATA_SIZE (in custom ce_expr).
  Notation "'INST_SIZE'" := INST_SIZE (in custom ce_expr).
  Notation "'clk'" := clk (in custom ce_expr).
  Notation "'rst_n'" := rst_n (in custom ce_expr).
  Notation "'step'" := step (in custom ce_expr).
  Notation "'pc_commit_vld'" := pc_commit_vld (in custom ce_expr).
  Notation "'pc_commit'" := pc_commit (in custom ce_expr).
  Notation "'imem_req_vld'" := imem_req_vld (in custom ce_expr).
  Notation "'imem_req'" := imem_req (in custom ce_expr).
  Notation "'imem_req_truncated'" := imem_req_truncated (in custom ce_expr).
  Notation "'imem_resp_vld'" := imem_resp_vld (in custom ce_expr).
  Notation "'imem_resp'" := imem_resp (in custom ce_expr).
  Notation "'dmem_req_vld'" := dmem_req_vld (in custom ce_expr).
  Notation "'dmem_req_ld'" := dmem_req_ld (in custom ce_expr).
  Notation "'dmem_req_ld_addr'" := dmem_req_ld_addr (in custom ce_expr).
  Notation "'dmem_req_ld_addr_truncated'" := dmem_req_ld_addr_truncated (in custom ce_expr).
  Notation "'dmem_req_st_addr'" := dmem_req_st_addr (in custom ce_expr).
  Notation "'dmem_req_st_addr_truncated'" := dmem_req_st_addr_truncated (in custom ce_expr).
  Notation "'dmem_req_st_ty'" := dmem_req_st_ty (in custom ce_expr).
  Notation "'dmem_req_data'" := dmem_req_data (in custom ce_expr).
  Notation "'dmem_resp_vld'" := dmem_resp_vld (in custom ce_expr).
  Notation "'dmem_resp'" := dmem_resp (in custom ce_expr).
  Notation "'pc'" := pc (in custom ce_expr).
  Notation "'inst'" := inst (in custom ce_expr).
  Notation "'inst_cur'" := inst_cur (in custom ce_expr).
  Notation "'opcode'" := opcode (in custom ce_expr).
  Notation "'rs1'" := rs1 (in custom ce_expr).
  Notation "'rs2'" := rs2 (in custom ce_expr).
  Notation "'rd'" := rd (in custom ce_expr).
  Notation "'funct3'" := funct3 (in custom ce_expr).
  Notation "'funct7'" := funct7 (in custom ce_expr).
  Notation "'imm_i'" := imm_i (in custom ce_expr).
  Notation "'imm_s'" := imm_s (in custom ce_expr).
  Notation "'imm_b'" := imm_b (in custom ce_expr).
  Notation "'imm_u'" := imm_u (in custom ce_expr).
  Notation "'imm_j'" := imm_j (in custom ce_expr).
  Notation "'rf'" := rf (in custom ce_expr).
  Notation "'rsv1'" := rsv1 (in custom ce_expr).
  Notation "'rsv2'" := rsv2 (in custom ce_expr).
  Notation "'rd_stall'" := rd_stall (in custom ce_expr).
  Notation "'op_reg_reg'" := op_reg_reg (in custom ce_expr).
  Notation "'op_reg_imm'" := op_reg_imm (in custom ce_expr).
  Notation "'op_lui'" := op_lui (in custom ce_expr).
  Notation "'op_auipc'" := op_auipc (in custom ce_expr).
  Notation "'op_branch'" := op_branch (in custom ce_expr).
  Notation "'op_jal'" := op_jal (in custom ce_expr).
  Notation "'op_jalr'" := op_jalr (in custom ce_expr).
  Notation "'op_load'" := op_load (in custom ce_expr).
  Notation "'op_store'" := op_store (in custom ce_expr).
  Notation "'op_system'" := op_system (in custom ce_expr).
  Notation "'op_misc'" := op_misc (in custom ce_expr).
  Notation "'funct3_add_sub'" := funct3_add_sub (in custom ce_expr).
  Notation "'funct3_sll'" := funct3_sll (in custom ce_expr).
  Notation "'funct3_slt'" := funct3_slt (in custom ce_expr).
  Notation "'funct3_sltu'" := funct3_sltu (in custom ce_expr).
  Notation "'funct3_xor'" := funct3_xor (in custom ce_expr).
  Notation "'funct3_srl_sra'" := funct3_srl_sra (in custom ce_expr).
  Notation "'funct3_or'" := funct3_or (in custom ce_expr).
  Notation "'funct3_and'" := funct3_and (in custom ce_expr).
  Notation "'funct7_add'" := funct7_add (in custom ce_expr).
  Notation "'funct7_sub'" := funct7_sub (in custom ce_expr).
  Notation "'funct7_srl'" := funct7_srl (in custom ce_expr).
  Notation "'funct7_sra'" := funct7_sra (in custom ce_expr).
  Notation "'funct3_beq'" := funct3_beq (in custom ce_expr).
  Notation "'funct3_bne'" := funct3_bne (in custom ce_expr).
  Notation "'funct3_blt'" := funct3_blt (in custom ce_expr).
  Notation "'funct3_bge'" := funct3_bge (in custom ce_expr).
  Notation "'funct3_bltu'" := funct3_bltu (in custom ce_expr).
  Notation "'funct3_bgeu'" := funct3_bgeu (in custom ce_expr).
  Notation "'funct3_lb'" := funct3_lb (in custom ce_expr).
  Notation "'funct3_lh'" := funct3_lh (in custom ce_expr).
  Notation "'funct3_lw'" := funct3_lw (in custom ce_expr).
  Notation "'funct3_lbu'" := funct3_lbu (in custom ce_expr).
  Notation "'funct3_lhu'" := funct3_lhu (in custom ce_expr).
  Notation "'funct3_sb'" := funct3_sb (in custom ce_expr).
  Notation "'funct3_sh'" := funct3_sh (in custom ce_expr).
  Notation "'funct3_sw'" := funct3_sw (in custom ce_expr).
  Notation "'pc_next'" := pc_next (in custom ce_expr).
  Notation "'dmem_resp_ld'" := dmem_resp_ld (in custom ce_expr).
  Notation "'rd_upd'" := rd_upd (in custom ce_expr).
  Notation "'rd_upd_by_load'" := rd_upd_by_load (in custom ce_expr).
  Notation "'rd_exec_val'" := rd_exec_val (in custom ce_expr).
  Notation "'get_ld_val'" := get_ld_val (in custom ce_expr).
  Notation "'get_next_pc'" := get_next_pc (in custom ce_expr).
  Notation "'get_exec_value'" := get_exec_value (in custom ce_expr).

  Notation "'imem_req_rdy'" := imem_req_rdy (in custom ce_expr).
  Notation "'imem_resp_rdy'" := imem_resp_rdy (in custom ce_expr).
  Notation "'dmem_req_rdy'" := dmem_req_rdy (in custom ce_expr).
  Notation "'dmem_resp_rdy'" := dmem_resp_rdy (in custom ce_expr).

  Notation "'d2e_vld'" := d2e_vld (in custom ce_expr).
  Notation "'d2e_rdy'" := d2e_rdy (in custom ce_expr).
  Notation "'e2w_vld'" := e2w_vld (in custom ce_expr).
  Notation "'d2e_avail'" := d2e_avail (in custom ce_expr).
  Notation "'e2w_avail'" := e2w_avail (in custom ce_expr).
  Notation "'decode_now'" := decode_now (in custom ce_expr).
  Notation "'exec_now'" := exec_now (in custom ce_expr).
  Notation "'wb_now'" := wb_now (in custom ce_expr).
  Notation "'pc_fetch'" := pc_fetch (in custom ce_expr).
  Notation "'pc_fetch_next'" := pc_fetch_next (in custom ce_expr).
  Notation "'btb_upd_vld'" := btb_upd_vld (in custom ce_expr).
  Notation "'btb_upd_pc_cur'" := btb_upd_pc_cur (in custom ce_expr).
  Notation "'btb_upd_pc_next'" := btb_upd_pc_next (in custom ce_expr).
  Notation "'f2d_vld'" := f2d_vld (in custom ce_expr).
  Notation "'pc_f2d'" := pc_f2d (in custom ce_expr).
  Notation "'inst_dec'" := inst_dec (in custom ce_expr).
  Notation "'inst_d2e'" := inst_d2e (in custom ce_expr).
  Notation "'pc_d2e'" := pc_d2e (in custom ce_expr).
  Notation "'rd_d2e'" := rd_d2e (in custom ce_expr).
  Notation "'pc_exec'" := pc_exec (in custom ce_expr).
  Notation "'pc_exec_next'" := pc_exec_next (in custom ce_expr).
  Notation "'exec_ok'" := exec_ok (in custom ce_expr).
  Notation "'exec_bad'" := exec_bad (in custom ce_expr).
  Notation "'exec_mem'" := exec_mem (in custom ce_expr).
  Notation "'flush'" := flush (in custom ce_expr).
  Notation "'rdi'" := rdi (in custom ce_expr).
  Notation "'rdv'" := rdv (in custom ce_expr).
  Notation "'rdv_cal'" := rdv_cal (in custom ce_expr).
  Notation "'wb_mem'" := wb_mem (in custom ce_expr).
  Notation "'wb_ld'" := wb_ld (in custom ce_expr).
  Notation "'wb_ld_ty'" := wb_ld_ty (in custom ce_expr).

  Notation "'ICACHE_SIZE'" := ICACHE_SIZE (in custom ce_expr).
  Notation "'imem'" := imem (in custom ce_expr).

  Notation "'DCACHE_SIZE'" := DCACHE_SIZE (in custom ce_expr).
  Notation "'dmem'" := dmem (in custom ce_expr).
  Notation "'req_data'" := req_data (in custom ce_expr).
  Notation "'st_data'" := st_data (in custom ce_expr).
  Notation "'st_read_data'" := st_read_data (in custom ce_expr).

  Notation "'int_resp_vld'" := int_resp_vld (in custom ce_expr).
  Notation "'int_resp'" := int_resp (in custom ce_expr).


  Notation "'frontend'" := frontend (in custom ce_expr).
  Notation "'frontend_req_rdy'" := frontend_req_rdy (in custom ce_expr).
  Notation "'f2d_rdy'" := f2d_rdy (in custom ce_expr).
  Notation "'pc_f2d_vld'" := pc_f2d_vld (in custom ce_expr).
  Notation "'pc_f2d_rdy'" := pc_f2d_rdy (in custom ce_expr).
  Notation "'pc_f2d_in_vld'" := pc_f2d_in_vld (in custom ce_expr).
  Notation "'pc_f2d_in_rdy'" := pc_f2d_in_rdy (in custom ce_expr).
End Notations.

Definition VExprIdvid := @VExprId vid.
Coercion VExprIdvid: vid >-> VExpr.
Definition VPortIdsOnevid := @VPortIdsOne vid.
Coercion VPortIdsOnevid: vid >-> VPortIds.

Module Functions.

  Module M.
    Notation "'functions'" := functions (in custom ce_top).
    Include Notations.

    Definition m: @VModuleDecl vid_t := #[
module functions
  #(parameter integer ADDR_SIZE = 32,
    parameter integer DATA_SIZE = 32,
    parameter [6:0] op_reg_reg = 7'b0110011,
    parameter [6:0] op_reg_imm = 7'b0010011,
    parameter [6:0] op_lui = 7'b0110111,
    parameter [6:0] op_auipc = 7'b0010111,
    parameter [6:0] op_branch = 7'b1100011,
    parameter [6:0] op_jal = 7'b1101111,
    parameter [6:0] op_jalr = 7'b1100111,
    parameter [6:0] op_load = 7'b0000011,
    parameter [6:0] op_store = 7'b0100011,
    parameter [2:0] funct3_add_sub = 3'b000,
    parameter [2:0] funct3_sll = 3'b001,
    parameter [2:0] funct3_slt = 3'b010,
    parameter [2:0] funct3_sltu = 3'b011,
    parameter [2:0] funct3_xor = 3'b100,
    parameter [2:0] funct3_srl_sra = 3'b101,
    parameter [2:0] funct3_or = 3'b110,
    parameter [2:0] funct3_and = 3'b111,
    parameter [6:0] funct7_add = 7'b0000000,
    parameter [6:0] funct7_sub = 7'b0100000,
    parameter [6:0] funct7_srl = 7'b0000000,
    parameter [6:0] funct7_sra = 7'b0100000,
    parameter [2:0] funct3_beq = 3'b000,
    parameter [2:0] funct3_bne = 3'b001,
    parameter [2:0] funct3_blt = 3'b100,
    parameter [2:0] funct3_bge = 3'b101,
    parameter [2:0] funct3_bltu = 3'b110,
    parameter [2:0] funct3_bgeu = 3'b111,
    parameter [2:0] funct3_lb = 3'b000,
    parameter [2:0] funct3_lh = 3'b001,
    parameter [2:0] funct3_lw = 3'b010,
    parameter [2:0] funct3_lbu = 3'b100,
    parameter [2:0] funct3_lhu = 3'b101,
    parameter [2:0] funct3_sb = 3'b000,
    parameter [2:0] funct3_sh = 3'b001,
    parameter [2:0] funct3_sw = 3'b010)
   (input logic clk,
    input logic rst_n);

function [DATA_SIZE-1:0] get_ld_val (input logic [2:0]           funct3,
                                     input logic [DATA_SIZE-1:0] dmem_resp);
  return (funct3 == funct3_lb ?  $unsigned(DATA_SIZE '($signed(dmem_resp[7:0]))) :
          funct3 == funct3_lh ?  $unsigned(DATA_SIZE '($signed(dmem_resp[15:0]))) :
          funct3 == funct3_lw ? dmem_resp :
          funct3 == funct3_lbu ? DATA_SIZE '(dmem_resp[7:0]) :
          funct3 == funct3_lhu ? DATA_SIZE '(dmem_resp[15:0]) : 'd0);
endfunction

function [ADDR_SIZE-1:0] get_next_pc (input logic [ADDR_SIZE-1:0] pc,
                                      input logic [6:0]           opcode,
                                      input logic [2:0]           funct3,
                                      input logic [DATA_SIZE-1:0] rsv1,
                                      input logic [DATA_SIZE-1:0] rsv2,
                                      input logic [12:0]          imm_b,
                                      input logic [11:0]          imm_i,
                                      input logic [20:0]          imm_j);
  return (opcode == op_branch ? pc + (funct3 == funct3_beq && rsv1 == rsv2 ||
                                      funct3 == funct3_bne && rsv1 != rsv2 ||
                                      funct3 == funct3_blt && $signed(rsv1) < $signed(rsv2) ||
                                      funct3 == funct3_bge && $signed(rsv1) >= $signed(rsv2) ||
                                      funct3 == funct3_bltu && rsv1 < rsv2 ||
                                      funct3 == funct3_bgeu && rsv1 >= rsv2 ? $signed(imm_b) : 'd4) :
          opcode == op_jal ? pc + $signed(imm_j) :
          opcode == op_jalr ? (rsv1 + $signed(imm_i)) & (~ 'd1) : pc + 'd4);
endfunction

function [DATA_SIZE-1:0] get_exec_value (input logic [ADDR_SIZE-1:0] pc,
                                         input logic [6:0]           opcode,
                                         input logic [2:0]           funct3,
                                         input logic [6:0]           funct7,
                                         input logic [DATA_SIZE-1:0] rsv1,
                                         input logic [DATA_SIZE-1:0] rsv2,
                                         input logic [11:0]          imm_i,
                                         input logic [19:0]          imm_u);
  return (opcode == op_reg_reg ? (funct3 == funct3_add_sub ? (funct7 == funct7_add ? rsv1 + rsv2 :
                                                              funct7 == funct7_sub ? rsv1 - rsv2 : 'd0) :
                                  funct3 == funct3_sll ? rsv1 << 5 '(rsv2) :
                                  funct3 == funct3_slt ? ($signed(rsv1) < $signed(rsv2) ? 'd1 : 'd0) :
                                  funct3 == funct3_sltu ? (rsv1 < rsv2 ? 'd1 : 'd0) :
                                  funct3 == funct3_xor ? rsv1 ^ rsv2 :
                                  funct3 == funct3_srl_sra ? (funct7 == funct7_srl ? rsv1 >> 5 '(rsv2) :
                                                              funct7 == funct7_sra ? $unsigned( $signed(rsv1) >>> 5 '(rsv2)) : 'd0) :
                                  funct3 == funct3_or ? rsv1 | rsv2 :
                                  funct3 == funct3_and ? rsv1 & rsv2 : 'd0) :
          opcode == op_reg_imm ? (funct3 == funct3_add_sub ? rsv1 + $signed(imm_i) :
                                  funct3 == funct3_sll ? rsv1 << imm_i[4:0] :
                                  funct3 == funct3_slt ? ($signed(rsv1) < $signed(imm_i) ? 'd1 : 'd0) :
                                  funct3 == funct3_sltu ? (rsv1 < $unsigned(32 '($signed(imm_i))) ? 'd1 : 'd0) :
                                  funct3 == funct3_xor ? rsv1 ^ $signed(imm_i) :
                                  funct3 == funct3_srl_sra ? (funct7 == funct7_srl ? rsv1 >> imm_i[4:0] :
                                                              funct7 == funct7_sra ? $unsigned( $signed(rsv1) >>> imm_i[4:0]) : 'd0) :
                                  funct3 == funct3_or ? rsv1 | $signed(imm_i) :
                                  funct3 == funct3_and ? rsv1 & $signed(imm_i) : 'd0) :
          opcode == op_lui ? (32 '(imm_u) << 12) :
          opcode == op_auipc ? pc + (32 '(imm_u) << 12) :
          opcode == op_jal ? pc + 'd4 :
          opcode == op_jalr ? pc + 'd4 : 'd0);
endfunction

endmodule].

  End M.
  Section AbsOps.
    Context `{sz_ops} `{array_ops hmap}.

    Definition pdecls: Decls :=
      ltac:(let s := eval vm_compute in (declsVParamPortsM M.m) in exact s).
    Definition params: State :=
      ltac:(let s := eval vm_compute in (trsVParamPortsM M.m) in exact s).

    Definition f: Funcs := funcsVModuleDecl pdecls params M.m.

  End AbsOps.

End Functions.
