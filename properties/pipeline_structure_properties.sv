//============================================================
// pipeline_structure_properties.sv  (FULL, NO $past/$stable, JASPER-SAFE)
//
// Checks:
//  A) HOLD on stall: IF/ID, ID/EX, EX/MEM must not change when stalled.
//     - Two variants to diagnose stall timing:
//         * HOLD_ON_STALL    : uses stall directly
//         * HOLD_ON_STALL_D  : uses 1-cycle delayed stall (stall_d)
//  B) MAP when output changes: if a pipeline reg updates, it must load
//     the previous stage value from the previous cycle (prev_* bundle).
//
// Notes:
//  - MEM/WB (MU_WB) has no stall port in your RTL, so we do not require
//    MEM/WB to hold on stall; we only check mapping when it updates.
//============================================================

module pipeline_structure_properties #(
    parameter int DATA_WIDTH   = 32,
    parameter int ADDRESS_BITS = 12
)(
    input  logic                    clock,
    input  logic                    reset,
    input  logic                    stall,

    // IF/ID boundary
    input  logic [DATA_WIDTH-1:0]   instruction_fetch,
    input  logic [DATA_WIDTH-1:0]   instruction_decode,
    input  logic [ADDRESS_BITS-1:0] inst_PC_fetch,
    input  logic [ADDRESS_BITS-1:0] inst_PC_decode,

    // ID/EX boundary
    input  logic [DATA_WIDTH-1:0]   instruction_execute,
    input  logic [ADDRESS_BITS-1:0] PC_execute,

    input  logic [6:0]              opcode_decode,
    input  logic [2:0]              funct3_decode,
    input  logic [6:0]              funct7_decode,
    input  logic [4:0]              rd_decode,
    input  logic [DATA_WIDTH-1:0]   rs1_data_decode,
    input  logic [DATA_WIDTH-1:0]   rs2_data_decode,
    input  logic [DATA_WIDTH-1:0]   extend_imm_decode,
    input  logic                    memRead_decode,
    input  logic                    memWrite_decode,
    input  logic                    regWrite_decode,
    input  logic [1:0]              next_PC_select_decode,

    input  logic [6:0]              opcode_execute,
    input  logic [2:0]              funct3_execute,
    input  logic [6:0]              funct7_execute,
    input  logic [4:0]              rd_execute,
    input  logic [DATA_WIDTH-1:0]   rs1_data_execute,
    input  logic [DATA_WIDTH-1:0]   rs2_data_execute,
    input  logic [DATA_WIDTH-1:0]   extend_imm_execute,
    input  logic                    memRead_execute,
    input  logic                    memWrite_execute,
    input  logic                    regWrite_execute,
    input  logic [1:0]              next_PC_select_execute,

    // EX/MEM boundary
    input  logic [DATA_WIDTH-1:0]   instruction_memory,
    input  logic [DATA_WIDTH-1:0]   ALU_result_execute,
    input  logic [DATA_WIDTH-1:0]   ALU_result_memory,
    input  logic [DATA_WIDTH-1:0]   rs2_data_memory,
    input  logic [4:0]              rd_memory,
    input  logic                    memRead_memory,
    input  logic                    memWrite_memory,
    input  logic                    regWrite_memory,
    input  logic [1:0]              next_PC_select_memory,

    // MEM/WB boundary
    input  logic [DATA_WIDTH-1:0]   instruction_writeback,
    input  logic [DATA_WIDTH-1:0]   ALU_result_writeback,
    input  logic [DATA_WIDTH-1:0]   memory_data_memory,
    input  logic [DATA_WIDTH-1:0]   memory_data_writeback,
    input  logic [4:0]              rd_writeback,
    input  logic                    memRead_writeback,
    input  logic                    regWrite_writeback
);

`define KNOWN(x) (!$isunknown(x))

    // ------------------------------------------------------------
    // Guards / diagnostic signals
    // ------------------------------------------------------------
    logic past_valid;
    logic stall_d;

    always_ff @(posedge clock) begin
        if (reset) begin
            past_valid <= 1'b0;
            stall_d    <= 1'b0;
        end else begin
            past_valid <= 1'b1;
            stall_d    <= stall;
        end
    end

    // ------------------------------------------------------------
    // Bundle widths
    // ------------------------------------------------------------
    localparam int IFID_BW = DATA_WIDTH + ADDRESS_BITS;

    localparam int ID_BW = DATA_WIDTH + ADDRESS_BITS
                         + 7 + 3 + 7 + 5
                         + DATA_WIDTH + DATA_WIDTH + DATA_WIDTH
                         + 1 + 1 + 1 + 2;

    localparam int EX_BW = DATA_WIDTH     // instruction
                         + DATA_WIDTH     // ALU_result
                         + DATA_WIDTH     // store_data (rs2)
                         + 5              // rd
                         + 1 + 1 + 1      // memRead/memWrite/regWrite
                         + 2;             // next_PC_select

    localparam int MEM_BW = DATA_WIDTH    // instruction
                          + DATA_WIDTH    // ALU_result
                          + DATA_WIDTH    // load_data
                          + 5             // rd
                          + 1             // memRead
                          + 1;            // regWrite

    // ------------------------------------------------------------
    // Current-cycle bundles
    // ------------------------------------------------------------
    wire [IFID_BW-1:0] ifid_bundle_now = {instruction_decode, inst_PC_decode};
    wire [IFID_BW-1:0] if_bundle_now   = {instruction_fetch,  inst_PC_fetch};

    wire [ID_BW-1:0] id_bundle_now = {
        instruction_decode,
        inst_PC_decode,
        opcode_decode, funct3_decode, funct7_decode,
        rd_decode,
        rs1_data_decode, rs2_data_decode, extend_imm_decode,
        memRead_decode, memWrite_decode, regWrite_decode,
        next_PC_select_decode
    };

    wire [ID_BW-1:0] idex_bundle_now = {
        instruction_execute,
        PC_execute,
        opcode_execute, funct3_execute, funct7_execute,
        rd_execute,
        rs1_data_execute, rs2_data_execute, extend_imm_execute,
        memRead_execute, memWrite_execute, regWrite_execute,
        next_PC_select_execute
    };

    wire [EX_BW-1:0] ex_bundle_now = {
        instruction_execute,
        ALU_result_execute,
        rs2_data_execute,
        rd_execute,
        memRead_execute, memWrite_execute, regWrite_execute,
        next_PC_select_execute
    };

    wire [EX_BW-1:0] exmem_bundle_now = {
        instruction_memory,
        ALU_result_memory,
        rs2_data_memory,
        rd_memory,
        memRead_memory, memWrite_memory, regWrite_memory,
        next_PC_select_memory
    };

    wire [MEM_BW-1:0] mem_bundle_now = {
        instruction_memory,
        ALU_result_memory,
        memory_data_memory,
        rd_memory,
        memRead_memory,
        regWrite_memory
    };

    wire [MEM_BW-1:0] memwb_bundle_now = {
        instruction_writeback,
        ALU_result_writeback,
        memory_data_writeback,
        rd_writeback,
        memRead_writeback,
        regWrite_writeback
    };

    // ------------------------------------------------------------
    // Previous-cycle bundles (explicit regs, wave-visible)
    // ------------------------------------------------------------
    logic [IFID_BW-1:0] prev_if_bundle;
    logic [IFID_BW-1:0] prev_ifid_bundle;

    logic [ID_BW-1:0]   prev_id_bundle;
    logic [ID_BW-1:0]   prev_idex_bundle;

    logic [EX_BW-1:0]   prev_ex_bundle;
    logic [EX_BW-1:0]   prev_exmem_bundle;

    logic [MEM_BW-1:0]  prev_mem_bundle;
    logic [MEM_BW-1:0]  prev_memwb_bundle;

    always_ff @(posedge clock) begin
        if (reset) begin
            prev_if_bundle    <= '0;
            prev_ifid_bundle  <= '0;
            prev_id_bundle    <= '0;
            prev_idex_bundle  <= '0;
            prev_ex_bundle    <= '0;
            prev_exmem_bundle <= '0;
            prev_mem_bundle   <= '0;
            prev_memwb_bundle <= '0;
        end else begin
            prev_if_bundle    <= if_bundle_now;
            prev_ifid_bundle  <= ifid_bundle_now;
            prev_id_bundle    <= id_bundle_now;
            prev_idex_bundle  <= idex_bundle_now;
            prev_ex_bundle    <= ex_bundle_now;
            prev_exmem_bundle <= exmem_bundle_now;
            prev_mem_bundle   <= mem_bundle_now;
            prev_memwb_bundle <= memwb_bundle_now;
        end
    end

    // ============================================================
    // A) HOLD properties
    // ============================================================

    // IF/ID hold on stall
    property p_hold_ifid_on_stall;
        @(posedge clock) disable iff (reset)
            past_valid && stall &&
            `KNOWN(ifid_bundle_now) && `KNOWN(prev_ifid_bundle)
            |-> (ifid_bundle_now === prev_ifid_bundle);
    endproperty
    ASSERT_HOLD_IF_ID_ON_STALL: assert property (p_hold_ifid_on_stall)
        else $error("ASSERT_HOLD_IF_ID_ON_STALL: IF/ID changed while stall==1");

    // IF/ID hold on stall_d (diagnostic)
    property p_hold_ifid_on_stall_d;
        @(posedge clock) disable iff (reset)
            past_valid && stall_d &&
            `KNOWN(ifid_bundle_now) && `KNOWN(prev_ifid_bundle)
            |-> (ifid_bundle_now === prev_ifid_bundle);
    endproperty
    ASSERT_HOLD_IF_ID_ON_STALL_D: assert property (p_hold_ifid_on_stall_d)
        else $error("ASSERT_HOLD_IF_ID_ON_STALL_D: IF/ID changed while stall_d==1");

    // ID/EX hold on stall
    property p_hold_idex_on_stall;
        @(posedge clock) disable iff (reset)
            past_valid && stall &&
            `KNOWN(idex_bundle_now) && `KNOWN(prev_idex_bundle)
            |-> (idex_bundle_now === prev_idex_bundle);
    endproperty
    ASSERT_HOLD_ID_EX_ON_STALL: assert property (p_hold_idex_on_stall)
        else $error("ASSERT_HOLD_ID_EX_ON_STALL: ID/EX changed while stall==1");

    // EX/MEM hold on stall
    property p_hold_exmem_on_stall;
        @(posedge clock) disable iff (reset)
            past_valid && stall &&
            `KNOWN(exmem_bundle_now) && `KNOWN(prev_exmem_bundle)
            |-> (exmem_bundle_now === prev_exmem_bundle);
    endproperty
    ASSERT_HOLD_EX_MEM_ON_STALL: assert property (p_hold_exmem_on_stall)
        else $error("ASSERT_HOLD_EX_MEM_ON_STALL: EX/MEM changed while stall==1");

    // ============================================================
    // B) MAP properties (when output updates, it must load prev input)
    // ============================================================

    // IF -> IF/ID
    property p_map_if_to_ifid_when_changes;
        @(posedge clock) disable iff (reset)
            past_valid &&
            `KNOWN(ifid_bundle_now) && `KNOWN(prev_ifid_bundle) && `KNOWN(prev_if_bundle) &&
            (ifid_bundle_now !== prev_ifid_bundle)
            |-> (ifid_bundle_now === prev_if_bundle);
    endproperty
    ASSERT_MAP_IF_TO_IFID: assert property (p_map_if_to_ifid_when_changes)
        else $error("ASSERT_MAP_IF_TO_IFID: IF/ID updated but != prev(IF)");

    // ID -> ID/EX
    property p_map_id_to_idex_when_changes;
        @(posedge clock) disable iff (reset)
            past_valid &&
            `KNOWN(idex_bundle_now) && `KNOWN(prev_idex_bundle) && `KNOWN(prev_id_bundle) &&
            (idex_bundle_now !== prev_idex_bundle)
            |-> (idex_bundle_now === prev_id_bundle);
    endproperty
    ASSERT_MAP_ID_TO_IDEX: assert property (p_map_id_to_idex_when_changes)
        else $error("ASSERT_MAP_ID_TO_IDEX: ID/EX updated but != prev(ID)");

    // EX -> EX/MEM
    property p_map_ex_to_exmem_when_changes;
        @(posedge clock) disable iff (reset)
            past_valid &&
            `KNOWN(exmem_bundle_now) && `KNOWN(prev_exmem_bundle) && `KNOWN(prev_ex_bundle) &&
            (exmem_bundle_now !== prev_exmem_bundle)
            |-> (exmem_bundle_now === prev_ex_bundle);
    endproperty
    ASSERT_MAP_EX_TO_EXMEM: assert property (p_map_ex_to_exmem_when_changes)
        else $error("ASSERT_MAP_EX_TO_EXMEM: EX/MEM updated but != prev(EX)");

    // MEM -> MEM/WB (no stall hold; just mapping when WB updates)
    property p_map_mem_to_memwb_when_changes;
        @(posedge clock) disable iff (reset)
            past_valid &&
            `KNOWN(memwb_bundle_now) && `KNOWN(prev_memwb_bundle) && `KNOWN(prev_mem_bundle) &&
            (memwb_bundle_now !== prev_memwb_bundle)
            |-> (memwb_bundle_now === prev_mem_bundle);
    endproperty
    ASSERT_MAP_MEM_TO_MEMWB: assert property (p_map_mem_to_memwb_when_changes)
        else $error("ASSERT_MAP_MEM_TO_MEMWB: MEM/WB updated but != prev(MEM)");

    // ============================================================
    // C) Coverage (named)
    // ============================================================

    COVER_PAST_VALID: cover property (@(posedge clock) disable iff (reset) past_valid);

    COVER_STALL:       cover property (@(posedge clock) disable iff (reset) past_valid && stall);
    COVER_STALL_D:     cover property (@(posedge clock) disable iff (reset) past_valid && stall_d);

    COVER_IFID_UPD:    cover property (@(posedge clock) disable iff (reset)
                        past_valid && `KNOWN(ifid_bundle_now) && `KNOWN(prev_ifid_bundle) &&
                        (ifid_bundle_now !== prev_ifid_bundle));

    COVER_IDEX_UPD:    cover property (@(posedge clock) disable iff (reset)
                        past_valid && `KNOWN(idex_bundle_now) && `KNOWN(prev_idex_bundle) &&
                        (idex_bundle_now !== prev_idex_bundle));

    COVER_EXMEM_UPD:   cover property (@(posedge clock) disable iff (reset)
                        past_valid && `KNOWN(exmem_bundle_now) && `KNOWN(prev_exmem_bundle) &&
                        (exmem_bundle_now !== prev_exmem_bundle));

    COVER_MEMWB_UPD:   cover property (@(posedge clock) disable iff (reset)
                        past_valid && `KNOWN(memwb_bundle_now) && `KNOWN(prev_memwb_bundle) &&
                        (memwb_bundle_now !== prev_memwb_bundle));

    // Best-effort flow cover: IF bundle flows to WB after 4 cycles with no stall
    // (Uses explicit prev chain instead of $past)
    logic [IFID_BW-1:0] if_bundle_d1, if_bundle_d2, if_bundle_d3, if_bundle_d4;
    always_ff @(posedge clock) begin
        if (reset) begin
            if_bundle_d1 <= '0;
            if_bundle_d2 <= '0;
            if_bundle_d3 <= '0;
            if_bundle_d4 <= '0;
        end else begin
            if_bundle_d1 <= if_bundle_now;
            if_bundle_d2 <= if_bundle_d1;
            if_bundle_d3 <= if_bundle_d2;
            if_bundle_d4 <= if_bundle_d3;
        end
    end

    // Compare only instruction field for demo, since WB bundle differs in width.
    // Here: instruction_writeback equals instruction_fetch delayed 4 cycles.
    COVER_FLOW_IF_TO_WB_4CYC_NO_STALL: cover property (@(posedge clock) disable iff (reset)
        past_valid &&
        (!stall) ##1 (!stall) ##1 (!stall) ##1 (!stall) &&
        `KNOWN(instruction_writeback) && `KNOWN(if_bundle_d4[IFID_BW-1:ADDRESS_BITS]) &&
        (instruction_writeback === if_bundle_d4[IFID_BW-1:ADDRESS_BITS])
    );

endmodule

