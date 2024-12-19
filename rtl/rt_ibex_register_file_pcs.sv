// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V register file
 *
 * Register file with 31 or 15x 32 bit wide registers. Register 0 is fixed to 0.
 * This register file is based on flip flops. Use this register file when
 * targeting FPGA synthesis or Verilator simulation.
 */
module rt_ibex_register_file_pcs import ibex_pkg::*; #(
  parameter bit          RV32E         = 0,
  parameter int unsigned DataWidth     = 32,
  parameter pcs_e        PCSType       = MemoryPCS,
  parameter int unsigned IrqLevelWidth = 8
) (
  // Clock and Reset
  input  logic                 clk_i,
  input  logic                 rst_ni,
  input  logic                 test_en_i,

  // Hardware Context Stack
  input  logic [IrqLevelWidth-1:0] irq_level_i,
  input  logic irq_ack_i,
  input  logic irq_exit_i,

  // Exposed CSRs
  input  logic [31:0] mepc_i,
  input  logic [31:0] mcause_i,
  output logic [31:0] mepc_o,
  output logic [31:0] mcause_o,
  output logic        pcs_restore_done_o,
  input  logic        next_mret_i,

  //Read port R1
  input  logic [4:0]           raddr_a_i,
  output logic [DataWidth-1:0] rdata_a_o,

  //Read port R2
  input  logic [4:0]           raddr_b_i,
  output logic [DataWidth-1:0] rdata_b_o,

  // Write port W1
  input  logic [4:0]           waddr_a_i,
  input  logic [DataWidth-1:0] wdata_a_i,
  input  logic                 we_a_i
);

  localparam int unsigned AddrWidth = RV32E ? 4 : 5;
  localparam int unsigned NumWords  = 2**AddrWidth;
  localparam logic [DataWidth-1:0] WordZeroVal = '0;

  localparam int unsigned NrSavedCsrs = 2; // mepc, mcause
  localparam int unsigned AbiNrSavedRegisters = (RV32E) ? 7 : 16;
  localparam int unsigned NrSavedRegs = NrSavedCsrs + AbiNrSavedRegisters;

  logic [DataWidth-1:0] rf_reg_restore [NumWords];
  logic [DataWidth-1:0] rf_reg [NumWords];
  logic [NumWords-1:0] we_a_dec;

  logic [NrSavedRegs-1:0][DataWidth-1:0] store_data;
  logic [NrSavedRegs-1:0][DataWidth-1:0] restore_data;
  logic restore_en;

  if ( PCSType == MemoryPCS ) begin : gen_memory_impl
    rt_ibex_pcs_memory #(
      .NrSavedRegs   (NrSavedRegs),
      .DataWidth     (DataWidth),
      .IrqLevelWidth (IrqLevelWidth)
    ) i_pcs_memory (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .irq_level_i   (irq_level_i),
      .irq_ack_i     (irq_ack_i),
      .irq_exit_i    (irq_exit_i),
      .store_data_i  (store_data),
      .restore_data_o(restore_data),
      .restore_en_o  (restore_en),
      .next_mret_i   (next_mret_i)
    );
  end else if ( PCSType == ShiftRegPCS ) begin : gen_shift_reg_impl
    rt_ibex_pcs_lifo #(
      .NrSavedRegs   (NrSavedRegs),
      .DataWidth     (DataWidth),
      .IrqLevelWidth (IrqLevelWidth)
    ) i_pcs_shiftreg (
      .clk_i         (clk_i),
      .rst_ni        (rst_ni),
      .irq_level_i   (irq_level_i),
      .irq_ack_i     (irq_ack_i),
      .irq_exit_i    (irq_exit_i),
      .store_data_i  (store_data),
      .restore_data_o(restore_data),
      .restore_en_o  (restore_en),
      .next_mret_i   (next_mret_i)
    );
  end


  always_ff @(posedge clk_i or negedge rst_ni) begin : signal_done
    if(!rst_ni) begin
      pcs_restore_done_o       <= 1'b0;
    end else begin
      pcs_restore_done_o       <= restore_en;
    end
  end


  always_comb begin : we_a_decoder
    for (int unsigned i = 0; i < NumWords; i++) begin
      we_a_dec[i] = (waddr_a_i == 5'(i)) ? we_a_i : 1'b0;
    end
  end

  // No flops for R0 as it's hard-wired to 0
  for (genvar i = 1; i < NumWords; i++) begin : g_rf_flops
    logic [DataWidth-1:0] rf_reg_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rf_reg_q <= WordZeroVal;
      end else if (restore_en) begin
        rf_reg_q <= rf_reg_restore[i]; //'x;
      end else if (we_a_dec[i]) begin
        rf_reg_q <= wdata_a_i;
      end
    end

    assign rf_reg[i] = rf_reg_q;
  end

  always_comb begin : reg_packing

    // store CSR as the base of packed word
    store_data[0] = mepc_i;
    store_data[1] = mcause_i;

    mepc_o   = restore_data[0];
    mcause_o = restore_data[1];

    rf_reg_restore = rf_reg;

    if (RV32E) begin : rve_regs
      for (int i = 2; i < 9; i++) begin
        store_data[i] = rf_reg[get_abi_idx(i, RV32E)];
        rf_reg_restore[get_reg_idx(i, RV32E)] = restore_data[i];
      end
    end else begin : rvi_regs
      for (int i = 2; i < 18; i++) begin
        store_data[i] = rf_reg[get_abi_idx(i, RV32E)];
        rf_reg_restore[get_reg_idx(i, RV32E)] = restore_data[i];
      end
    end

  end

  // R0 tied to zero
  assign rf_reg[0] = WordZeroVal;

  if (RV32E) begin :g_rv32e_regfile
    assign rdata_a_o = rf_reg[raddr_a_i[3:0]];
    assign rdata_b_o = rf_reg[raddr_b_i[3:0]];
  end else begin : g_rv32i_regfile
    assign rdata_a_o = rf_reg[raddr_a_i];
    assign rdata_b_o = rf_reg[raddr_b_i];
  end

// Helper functions to map sparcely placed ABI registers
// https://github.com/riscvarchive/riscv-eabi-spec/blob/master/EABI.adoc#5-eabi-interrupt-handler-context-save

function automatic int get_abi_idx(int reg_idx, bit eabi);
  int result = 0;

  if(eabi) begin
    case (reg_idx)
      2: result = 1;  //  x1 : ra
      3: result = 5;  //  x5 : t0
      4: result = 10; // x10 : a0
      5: result = 11; // x11 : a1
      6: result = 12; // x12 : a2
      7: result = 13; // x13 : a3
      8: result = 15; // x15 : t1
      default: result = 0;
    endcase
  end else begin
    case (reg_idx)
      2: result = 1;  //  x1 : ra
      3: result = 5;  //  x5 : t0
      4: result = 6;  //  x6 : t1
      5: result = 7;  //  x7 : t2
      6: result = 10; // x10 : a0
      7: result = 11; // x11 : a1
      8: result = 12; // x12 : a2
      9: result = 13; // x13 : a3
      10:result = 14; // x14 : a4
      11:result = 15; // x15 : a5
      12:result = 16; // x16 : a6
      13:result = 17; // x17 : a7
      14:result = 28; // x28 : t3
      15:result = 29; // x29 : t4
      16:result = 30; // x30 : t5
      17:result = 31; // x31 : t6
      default: result = 0;
    endcase
  end

  return result;
endfunction

function automatic int get_reg_idx(int abi_idx, bit eabi);
  int result = 0;

  if(eabi) begin
    case (abi_idx)
      2: result =  1 ; //  x1 : ra
      3: result =  5 ; //  x5 : t0
      4: result =  10; // x10 : a0
      5: result =  11; // x11 : a1
      6: result =  12; // x12 : a2
      7: result =  13; // x13 : a3
      8: result =  15; // x15 : t1
      default: result = 0;
    endcase
  end else begin
    case (abi_idx)
      2 : result = 1  ; //  x1 : ra
      3 : result = 5  ; //  x5 : t0
      4 : result = 6  ; //  x6 : t1
      5 : result = 7  ; //  x7 : t2
      6 : result = 10 ; // x10 : a0
      7 : result = 11 ; // x11 : a1
      8 : result = 12 ; // x12 : a2
      9 : result = 13 ; // x13 : a3
      10: result = 14 ; // x14 : a4
      11: result = 15 ; // x15 : a5
      12: result = 16 ; // x16 : a6
      13: result = 17 ; // x17 : a7
      14: result = 28 ; // x28 : t3
      15: result = 29 ; // x29 : t4
      16: result = 30 ; // x30 : t5
      17: result = 31 ; // x31 : t6
      default: result = 0;
    endcase
  end

  return result;
endfunction

endmodule


