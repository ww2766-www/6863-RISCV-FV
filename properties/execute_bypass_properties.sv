module execute_bypass_properties #(
  parameter int DATA_WIDTH = 32,
  parameter int ADDRESS_BITS = 20
)(
  input  logic                    clock,
  input  logic                    reset,
  input  logic                    stall,

  input  logic [2:0]              ALU_Operation,
  input  logic [6:0]              funct7,
  input  logic [2:0]              funct3,
  input  logic [ADDRESS_BITS-1:0] PC,
  input  logic [1:0]              ALU_ASrc,
  input  logic                    ALU_BSrc,
  input  logic                    branch_op,
  input  logic [DATA_WIDTH-1:0]   regRead_1,
  input  logic [DATA_WIDTH-1:0]   regRead_2,
  input  logic [DATA_WIDTH-1:0]   extend,

  input  logic [DATA_WIDTH-1:0]   ALU_result,
  input  logic                    zero,
  input  logic                    branch,
  input  logic [ADDRESS_BITS-1:0] JALR_target
);

  default clocking cb @(posedge clock); endclocking

  // 1) branch_op gating: if branch_op=0 then branch must be 0
  a_branch_gated: assert property (@(posedge clock) disable iff (reset)
    (!branch_op) |-> (!branch)
  ) else $error("[EXEC_SVA] branch should be 0 when branch_op=0");

  // 2) JALR_target alignment: always even (LSB=0)
  a_jalr_aligned: assert property (@(posedge clock) disable iff (reset)
    (JALR_target[0] == 1'b0)
  ) else $error("[EXEC_SVA] JALR_target must be aligned (LSB=0)");

  // 3) Stall behavior proxy check:
  // RTL uses old_stall to hold JALR_target; equivalent observable behavior:
  // if stall was 1 in previous cycle, JALR_target should stay same this cycle
  a_jalr_holds_after_stall: assert property (@(posedge clock) disable iff (reset)
    $past(stall) |-> (JALR_target == $past(JALR_target))
  ) else $error("[EXEC_SVA] JALR_target should hold after stall");

endmodule

