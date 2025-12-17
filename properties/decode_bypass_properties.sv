// 验证decode阶段旁路多路复用器输出与选择信号一致，确保取到正确的执行/访存/写回数据
module decode_bypass_properties #(
    parameter DATA_WIDTH = 32
) (
    input  logic               clock,
    input  logic               reset,
    input  logic [1:0]         rs1_data_bypass,
    input  logic [1:0]         rs2_data_bypass,
    input  logic [DATA_WIDTH-1:0] rs1_data,
    input  logic [DATA_WIDTH-1:0] rs2_data,
    input  logic [DATA_WIDTH-1:0] ALU_result_execute,
    input  logic [DATA_WIDTH-1:0] ALU_result_memory,
    input  logic [DATA_WIDTH-1:0] ALU_result_writeback
);

    // 假设：decode相关输入无X/Z
    property no_unknown_decode_inputs;
        @(posedge clock) disable iff (reset)
            !$isunknown({rs1_data_bypass, rs2_data_bypass,
                         rs1_data, rs2_data,
                         ALU_result_execute, ALU_result_memory, ALU_result_writeback});
    endproperty
    assume property (no_unknown_decode_inputs);

    // 断言：rs1选择01时必须输出执行段结果
    property rs1_selects_execute;
        @(posedge clock) disable iff (reset)
            (rs1_data_bypass == 2'b01) |-> rs1_data == ALU_result_execute;
    endproperty
    assert property (rs1_selects_execute);

    // 断言：rs1选择10时必须输出访存段结果
    property rs1_selects_memory;
        @(posedge clock) disable iff (reset)
            (rs1_data_bypass == 2'b10) |-> rs1_data == ALU_result_memory;
    endproperty
    assert property (rs1_selects_memory);

    // 断言：rs1选择11时必须输出写回段结果
    property rs1_selects_writeback;
        @(posedge clock) disable iff (reset)
            (rs1_data_bypass == 2'b11) |-> rs1_data == ALU_result_writeback;
    endproperty
    assert property (rs1_selects_writeback);

    // 断言：rs2选择01时必须输出执行段结果
    property rs2_selects_execute;
        @(posedge clock) disable iff (reset)
            (rs2_data_bypass == 2'b01) |-> rs2_data == ALU_result_execute;
    endproperty
    assert property (rs2_selects_execute);

    // 断言：rs2选择10时必须输出访存段结果
    property rs2_selects_memory;
        @(posedge clock) disable iff (reset)
            (rs2_data_bypass == 2'b10) |-> rs2_data == ALU_result_memory;
    endproperty
    assert property (rs2_selects_memory);

    // 断言：rs2选择11时必须输出写回段结果
    property rs2_selects_writeback;
        @(posedge clock) disable iff (reset)
            (rs2_data_bypass == 2'b11) |-> rs2_data == ALU_result_writeback;
    endproperty
    assert property (rs2_selects_writeback);

    // 覆盖：每条旁路路径都能被激活，便于观察
    cover property (@(posedge clock) disable iff (reset)
                    rs1_data_bypass == 2'b01 && rs1_data == ALU_result_execute);
    cover property (@(posedge clock) disable iff (reset)
                    rs1_data_bypass == 2'b10 && rs1_data == ALU_result_memory);
    cover property (@(posedge clock) disable iff (reset)
                    rs2_data_bypass == 2'b11 && rs2_data == ALU_result_writeback);

endmodule
