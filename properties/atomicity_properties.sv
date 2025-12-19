// 验证内存阶段的load指令以原子方式写回：读取的数据在下一拍完整写入寄存器
module atomicity_properties #(
    parameter DATA_WIDTH   = 32
) (
    input  logic                 clock,
    input  logic                 reset,
    input  logic                 memRead_memory,
    input  logic                 regWrite_memory,
    input  logic [4:0]           rd_memory,
    input  logic [DATA_WIDTH-1:0] memory_data_memory,
    input  logic                 memRead_writeback,
    input  logic                 regWrite_writeback,
    input  logic [4:0]           rd_writeback,
    input  logic [DATA_WIDTH-1:0] write_data_writeback
);

    // 假设信号无X/Z以免干扰证明
    property no_unknown_atomic_inputs;
        @(posedge clock) disable iff (reset)
            !$isunknown({memRead_memory, regWrite_memory, rd_memory,
                         memory_data_memory, memRead_writeback,
                         regWrite_writeback, rd_writeback, write_data_writeback});
    endproperty
    assume property (no_unknown_atomic_inputs);

    // load指令必须以一次写回完成，写回数据等于内存阶段捕获的数据
    property load_atomic_writeback;
        @(posedge clock) disable iff (reset)
            (memRead_memory && regWrite_memory && rd_memory != 5'd0)
            |=> (memRead_writeback && regWrite_writeback &&
                 rd_writeback == $past(rd_memory) &&
                 write_data_writeback == $past(memory_data_memory));
    endproperty
    assert property (load_atomic_writeback);

    // 覆盖：观察至少一次load原子写回
    cover property (@(posedge clock) disable iff (reset)
                    memRead_memory && regWrite_memory && rd_memory != 5'd0);

endmodule
