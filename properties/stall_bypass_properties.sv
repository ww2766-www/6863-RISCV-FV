// 验证stall_and_bypass_control_unit仅在load-use冲突时插入气泡，并保持旁路优先级正确
module stall_bypass_properties (
    input logic        clock,
    input logic [4:0]  rs1,
    input logic [4:0]  rs2,
    input logic        regwrite_execute,
    input logic        regwrite_memory,
    input logic        regwrite_writeback,
    input logic [4:0]  rd_execute,
    input logic [4:0]  rd_memory,
    input logic [4:0]  rd_writeback,
    input logic [6:0]  opcode_execute,
    input logic [1:0]  rs1_data_bypass,
    input logic [1:0]  rs2_data_bypass,
    input logic        stall_needed
);

    localparam logic [6:0] LOAD_OPCODE = 7'b0000011;

    logic load_in_execute;
    logic rs1_hazard_execute;
    logic rs1_hazard_memory;
    logic rs1_hazard_writeback;
    logic rs2_hazard_execute;
    logic rs2_hazard_memory;
    logic rs2_hazard_writeback;

    assign load_in_execute      = (opcode_execute == LOAD_OPCODE);
    assign rs1_hazard_execute   = (rs1 == rd_execute)   && regwrite_execute;
    assign rs1_hazard_memory    = (rs1 == rd_memory)    && regwrite_memory;
    assign rs1_hazard_writeback = (rs1 == rd_writeback) && regwrite_writeback;
    assign rs2_hazard_execute   = (rs2 == rd_execute)   && regwrite_execute;
    assign rs2_hazard_memory    = (rs2 == rd_memory)    && regwrite_memory;
    assign rs2_hazard_writeback = (rs2 == rd_writeback) && regwrite_writeback;

    // 确保输入信号无X/Z，加快形式收敛
    property no_unknown_inputs;
        @(posedge clock)
            !$isunknown({rs1, rs2, rd_execute, rd_memory, rd_writeback,
                         regwrite_execute, regwrite_memory, regwrite_writeback,
                         opcode_execute, rs1_data_bypass, rs2_data_bypass, stall_needed});
    endproperty
    assume property (no_unknown_inputs);

    // 断言：stall_needed只能由load-use冲突触发
    property stall_only_on_load_use;
        @(posedge clock)
            stall_needed |->
                (load_in_execute &&
                 ((rs1_hazard_execute && rs1 != 5'd0) ||
                  (rs2_hazard_execute && rs2 != 5'd0)));
    endproperty
    assert property (stall_only_on_load_use);

    // 断言：一旦需要插入气泡，旁路选择必须回到00防止不稳定数据
    property stall_blocks_bypass_mux;
        @(posedge clock)
            stall_needed |-> (rs1_data_bypass == 2'b00 && rs2_data_bypass == 2'b00);
    endproperty
    assert property (stall_blocks_bypass_mux);

    // 断言：execute段命中rs1且未stall时必须选择01旁路
    property rs1_execute_forwarding;
        @(posedge clock)
            (!stall_needed && rs1_hazard_execute) |-> rs1_data_bypass == 2'b01;
    endproperty
    assert property (rs1_execute_forwarding);

    // 断言：execute段命中rs2且未stall时必须选择01旁路
    property rs2_execute_forwarding;
        @(posedge clock)
            (!stall_needed && rs2_hazard_execute) |-> rs2_data_bypass == 2'b01;
    endproperty
    assert property (rs2_execute_forwarding);

    // 断言：访存段命中rs1且执行段未命中时选择10旁路
    property rs1_memory_forwarding;
        @(posedge clock)
            (!stall_needed && !rs1_hazard_execute && rs1_hazard_memory) |-> rs1_data_bypass == 2'b10;
    endproperty
    assert property (rs1_memory_forwarding);

    // 断言：访存段命中rs2且执行段未命中时选择10旁路
    property rs2_memory_forwarding;
        @(posedge clock)
            (!stall_needed && !rs2_hazard_execute && rs2_hazard_memory) |-> rs2_data_bypass == 2'b10;
    endproperty
    assert property (rs2_memory_forwarding);

    // 断言：只有写回段命中rs1时才选择11旁路
    property rs1_writeback_forwarding;
        @(posedge clock)
            (!stall_needed && !rs1_hazard_execute && !rs1_hazard_memory && rs1_hazard_writeback)
            |-> rs1_data_bypass == 2'b11;
    endproperty
    assert property (rs1_writeback_forwarding);

    // 断言：只有写回段命中rs2时才选择11旁路
    property rs2_writeback_forwarding;
        @(posedge clock)
            (!stall_needed && !rs2_hazard_execute && !rs2_hazard_memory && rs2_hazard_writeback)
            |-> rs2_data_bypass == 2'b11;
    endproperty
    assert property (rs2_writeback_forwarding);

    // 覆盖：观察各旁路路径与气泡是否可达
    cover property (@(posedge clock) !stall_needed && rs1_hazard_execute
                    && rs1_data_bypass == 2'b01);
    cover property (@(posedge clock) !stall_needed && !rs1_hazard_execute && rs1_hazard_memory
                    && rs1_data_bypass == 2'b10);
    cover property (@(posedge clock) !stall_needed && !rs1_hazard_execute && !rs1_hazard_memory
                    && rs1_hazard_writeback && rs1_data_bypass == 2'b11);
    cover property (@(posedge clock) stall_needed);

endmodule
