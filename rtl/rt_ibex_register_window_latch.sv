// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V register file
 *
 * Register file with 31 or 15x 32 bit wide registers. Register 0 is fixed to 0.
 * This register file is based on latches and is thus smaller than the flip-flop
 * based RF. It requires a target technology-specific clock gating cell. Use this
 * register file when targeting ASIC synthesis or event-based simulators.
 */
module rt_ibex_register_window_latch #(
  parameter bit                   RV32E             = 0,
  parameter int unsigned          DataWidth         = 32,
  parameter bit                   DummyInstructions = 0,
  parameter bit                   WrenCheck         = 0,
  parameter bit                   RdataMuxCheck     = 0,
  parameter logic [DataWidth-1:0] WordZeroVal       = '0,
  parameter int unsigned          NumRegisterWindows = 4,
  parameter int unsigned          WindowSize        = 7
) (
  // Clock and Reset
  input  logic                 clk_i,
  input  logic                 rst_ni,

  input  logic                 test_en_i,
  input  logic                 dummy_instr_id_i,
  input  logic                 dummy_instr_wb_i,

  //Read port R1
  input  logic [4:0]           raddr_a_i,
  output logic [DataWidth-1:0] rdata_a_o,

  //Read port R2
  input  logic [4:0]           raddr_b_i,
  output logic [DataWidth-1:0] rdata_b_o,

  // Write port W1
  input  logic [4:0]           waddr_a_i,
  input  logic [DataWidth-1:0] wdata_a_i,
  input  logic                 we_a_i,

  // This indicates whether spurious WE or non-one-hot encoded raddr are detected.
  output logic                 err_o,

  input  logic                 increment_ptr_i,
  input  logic                 decrement_ptr_i,
  output logic                 window_full_o,
  input  logic [31:0]          mcause_i,
  input  logic [31:0]          mepc_i,
  output logic [31:0]          mcause_o,
  output logic [31:0]          mepc_o,

  input  logic                 save_csr_i
);

  //localparam int unsigned ADDR_WIDTH = RV32E ? 4 : 5;
  localparam int unsigned BASE_WINDOW_SIZE = RV32E ? 16 : 32;
  localparam int unsigned NUM_WORDS   = BASE_WINDOW_SIZE + NumRegisterWindows * WindowSize;
  localparam int unsigned ADDR_WIDTH  = $clog2(NUM_WORDS);
  localparam int unsigned AUX_ADDR_WIDTH = $clog2(NumRegisterWindows);


  logic [DataWidth-1:0] mem[NUM_WORDS];
  logic [2*32-1:0] aux_mem[NumRegisterWindows];

  logic [NUM_WORDS-1:0] waddr_onehot_a;
  logic [NumRegisterWindows-1:0] aux_waddr_onehot_a;
  logic [2*32-1:0]      aux_mem_q;

  logic oh_raddr_a_err, oh_raddr_b_err, oh_we_err;

  logic [NUM_WORDS-1:1] mem_clocks;
  logic [NumRegisterWindows-1:0] aux_mem_clocks;

  logic [DataWidth-1:0] wdata_a_q;

  // internal addresses
  logic [ADDR_WIDTH-1:0] raddr_a_int, raddr_b_int, waddr_a_int;

  logic [ADDR_WIDTH-1:0] window_ptr;
  logic [AUX_ADDR_WIDTH-1:0] aux_ptr;

  logic [$clog2(WindowSize)-1:0] offset_ra, offset_rb, offset_w;
  logic [ADDR_WIDTH-1:0] windowed_raddr_a, windowed_raddr_b, windowed_waddr;

  logic  offset_sel;
  logic  is_eabi_ra, is_eabi_rb, is_eabi_w;
  logic  window_full;


  assign window_full_o  = window_full;

  assign window_full    = window_ptr == ((NumRegisterWindows-1) * WindowSize);

  always_comb begin
    is_eabi_ra = 1'b1;
    case (raddr_a_i)
      1:  offset_ra = 0; //  x1 : ra
      5:  offset_ra = 1; //  x5 : t0
      10: offset_ra = 2; // x10 : a0
      11: offset_ra = 3; // x11 : a1
      12: offset_ra = 4; // x12 : a2
      13: offset_ra = 5; // x13 : a3
      15: offset_ra = 6; // x15 : t1
      default: begin
        offset_ra = 0;
        is_eabi_ra = 1'b0;
      end
    endcase
  end


  always_comb begin
    is_eabi_rb = 1'b1;
    case (raddr_b_i)
      1:  offset_rb = 0;  //  x1 : ra
      5:  offset_rb = 1;  //  x5 : t0
      10: offset_rb = 2; // x10 : a0
      11: offset_rb = 3; // x11 : a1
      12: offset_rb = 4; // x12 : a2
      13: offset_rb = 5; // x13 : a3
      15: offset_rb = 6; // x15 : t1
      default: begin
        offset_rb = 0;
        is_eabi_rb = 1'b0;
      end
    endcase
  end


  always_comb begin
    is_eabi_w = 1'b1;
    case (waddr_a_i)
      1:  offset_w = 0;  //  x1 : ra
      5:  offset_w = 1;  //  x5 : t0
      10: offset_w = 2; // x10 : a0
      11: offset_w = 3; // x11 : a1
      12: offset_w = 4; // x12 : a2
      13: offset_w = 5; // x13 : a3
      15: offset_w = 6; // x15 : t1
      default: begin
        offset_w = 0;
        is_eabi_w = 1'b0;
      end
    endcase
  end

  assign windowed_raddr_a = (BASE_WINDOW_SIZE - WindowSize) + window_ptr + offset_ra;
  assign windowed_raddr_b = (BASE_WINDOW_SIZE - WindowSize) + window_ptr + offset_rb;
  assign windowed_waddr   = (BASE_WINDOW_SIZE - WindowSize) + window_ptr + offset_w;

  assign offset_sel  = (window_ptr != 0);

  assign raddr_a_int = (offset_sel && is_eabi_ra) ? windowed_raddr_a : {'0, raddr_a_i[4:0]};
  assign raddr_b_int = (offset_sel && is_eabi_rb) ? windowed_raddr_b : {'0, raddr_b_i[4:0]};
  assign waddr_a_int = (offset_sel && is_eabi_w)  ? windowed_waddr   : {'0, waddr_a_i[4:0]};

  logic clk_int;

  assign err_o = oh_raddr_a_err || oh_raddr_b_err || oh_we_err;


  always_ff @(posedge clk_i or negedge rst_ni) begin : window_ptr_
    if (!rst_ni) begin
      window_ptr   <= '0;
    end else begin
      if (increment_ptr_i) begin
        if(!(window_ptr == NUM_WORDS-WindowSize)) begin  // window_pointer is NOT pointing to the last window
          window_ptr <= window_ptr + WindowSize;
        end
      end

      if(decrement_ptr_i) begin
        window_ptr <= window_ptr - WindowSize;
      end
    end
  end


  always_ff @(posedge clk_i or negedge rst_ni) begin : aux_ptr_
    if (!rst_ni) begin
      aux_ptr   <= '0;
    end else begin
      if (increment_ptr_i) begin
        if(!(aux_ptr == NumRegisterWindows-1)) begin  // window_pointer is NOT pointing to the last window
          aux_ptr <= aux_ptr + 1;
        end
      end

      if(decrement_ptr_i) begin
        aux_ptr <= aux_ptr - 1;
      end
    end
  end





  //////////
  // READ //
  //////////
  if (RdataMuxCheck) begin : gen_rdata_mux_check
    // Encode raddr_a/b into one-hot encoded signals.
    logic [NUM_WORDS-1:0] raddr_onehot_a, raddr_onehot_b;
    logic [NUM_WORDS-1:0] raddr_onehot_a_buf, raddr_onehot_b_buf;
    prim_onehot_enc #(
      .OneHotWidth(NUM_WORDS)
    ) u_prim_onehot_enc_raddr_a (
      .in_i  (raddr_a_int),
      .en_i  (1'b1),
      .out_o (raddr_onehot_a)
    );

    prim_onehot_enc #(
      .OneHotWidth(NUM_WORDS)
    ) u_prim_onehot_enc_raddr_b (
      .in_i  (raddr_b_int),
      .en_i  (1'b1),
      .out_o (raddr_onehot_b)
    );

    // Buffer the one-hot encoded signals so that the checkers
    // are not optimized.
    prim_buf #(
      .Width(NUM_WORDS)
    ) u_prim_buf_raddr_a (
      .in_i(raddr_onehot_a),
      .out_o(raddr_onehot_a_buf)
    );

    prim_buf #(
      .Width(NUM_WORDS)
    ) u_prim_buf_raddr_b (
      .in_i(raddr_onehot_b),
      .out_o(raddr_onehot_b_buf)
    );

    // SEC_CM: DATA_REG_SW.GLITCH_DETECT
    // Check the one-hot encoded signals for glitches.
    prim_onehot_check #(
      .AddrWidth(ADDR_WIDTH),
      .OneHotWidth(NUM_WORDS),
      .AddrCheck(1),
      // When AddrCheck=1 also EnableCheck needs to be 1.
      .EnableCheck(1)
    ) u_prim_onehot_check_raddr_a (
      .clk_i,
      .rst_ni,
      .oh_i   (raddr_onehot_a_buf),
      .addr_i (raddr_b_int),
      // Set enable=1 as address is always valid.
      .en_i   (1'b1),
      .err_o  (oh_raddr_a_err)
    );

    prim_onehot_check #(
      .AddrWidth(ADDR_WIDTH),
      .OneHotWidth(NUM_WORDS),
      .AddrCheck(1),
      // When AddrCheck=1 also EnableCheck needs to be 1.
      .EnableCheck(1)
    ) u_prim_onehot_check_raddr_b (
      .clk_i,
      .rst_ni,
      .oh_i   (raddr_onehot_b_buf),
      .addr_i (raddr_b_int),
      // Set enable=1 as address is always valid.
      .en_i   (1'b1),
      .err_o  (oh_raddr_b_err)
    );

    // MUX register to rdata_a/b_o according to raddr_a/b_onehot.
    prim_onehot_mux  #(
      .Width(DataWidth),
      .Inputs(NUM_WORDS)
    ) u_rdata_a_mux (
      .clk_i,
      .rst_ni,
      .in_i  (mem),
      .sel_i (raddr_onehot_a),
      .out_o (rdata_a_o)
    );

    prim_onehot_mux  #(
      .Width(DataWidth),
      .Inputs(NUM_WORDS)
    ) u_rdata_b_mux (
      .clk_i,
      .rst_ni,
      .in_i  (mem),
      .sel_i (raddr_onehot_b),
      .out_o (rdata_b_o)
    );
  end else begin : gen_no_rdata_mux_check
    assign rdata_a_o = mem[raddr_a_int];
    assign rdata_b_o = mem[raddr_b_int];
    assign oh_raddr_a_err = 1'b0;
    assign oh_raddr_b_err = 1'b0;

    assign aux_mem_q = aux_mem[aux_ptr];
    assign mcause_o  = aux_mem_q[63:32];
    assign mepc_o    = aux_mem_q[31:0];
  end

  ///////////
  // WRITE //
  ///////////
  // Global clock gating
  prim_clock_gating cg_we_global (
      .clk_i     ( clk_i     ),
      .en_i      ( we_a_i || save_csr_i   ),
      .test_en_i ( test_en_i ),
      .clk_o     ( clk_int   )
  );



  // Sample input data
  // Use clk_int here, since otherwise we don't want to write anything anyway.
  always_ff @(posedge clk_int or negedge rst_ni) begin : sample_wdata
    if (!rst_ni) begin
      wdata_a_q   <= WordZeroVal;
    end else begin
      if (we_a_i) begin
        wdata_a_q <= wdata_a_i;
      end
    end
  end

  // Write address decoding
  always_comb begin : wad
    for (int i = 0; i < NUM_WORDS; i++) begin : wad_word_iter
      if (we_a_i && (waddr_a_int == ADDR_WIDTH'(i))) begin
        waddr_onehot_a[i] = 1'b1;
      end else begin
        waddr_onehot_a[i] = 1'b0;
      end
    end
  end


  always_comb begin : aux_wad
    for (int i = 0; i < NumRegisterWindows; i++) begin : aux_wad_word_iter
      if (save_csr_i && (aux_ptr == AUX_ADDR_WIDTH'(i))) begin
        aux_waddr_onehot_a[i] = 1'b1;
      end else begin
        aux_waddr_onehot_a[i] = 1'b0;
      end
    end
  end

  // SEC_CM: DATA_REG_SW.GLITCH_DETECT
  // This checks for spurious WE strobes on the regfile.
  if (WrenCheck) begin : gen_wren_check
    // Buffer the decoded write enable bits so that the checker
    // is not optimized into the address decoding logic.
    logic [NUM_WORDS-1:0] waddr_onehot_a_buf;
    prim_buf #(
      .Width(NUM_WORDS)
    ) u_prim_buf (
      .in_i(waddr_onehot_a),
      .out_o(waddr_onehot_a_buf)
    );

    prim_onehot_check #(
      .AddrWidth(ADDR_WIDTH),
      .AddrCheck(1),
      .EnableCheck(1)
    ) u_prim_onehot_check (
      .clk_i,
      .rst_ni,
      .oh_i(waddr_onehot_a_buf),
      .addr_i(waddr_a_i),
      .en_i(we_a_i),
      .err_o(oh_we_err)
    );
  end else begin : gen_no_wren_check
    logic unused_strobe;
    assign unused_strobe = waddr_onehot_a[0]; // this is never read from in this case
    assign oh_we_err = 1'b0;
  end

  // Individual clock gating (if integrated clock-gating cells are available)
  for (genvar x = 1; x < NUM_WORDS; x++) begin : gen_cg_word_iter
    prim_clock_gating cg_i (
        .clk_i     ( clk_int           ),
        .en_i      ( waddr_onehot_a[x] ),
        .test_en_i ( test_en_i         ),
        .clk_o     ( mem_clocks[x]     )
    );
  end

  // Individual clock gating (if integrated clock-gating cells are available)
  for (genvar x = 0; x < NumRegisterWindows; x++) begin : gen_aux_cg_word_iter
    prim_clock_gating aux_cg_i (
        .clk_i     ( clk_int           ),
        .en_i      ( aux_waddr_onehot_a[x] ),
        .test_en_i ( test_en_i         ),
        .clk_o     ( aux_mem_clocks[x]     )
    );
  end

  // Actual write operation:
  // Generate the sequential process for the NUM_WORDS words of the memory.
  // The process is synchronized with the clocks mem_clocks[i], i = 1, ..., NUM_WORDS-1.
  for (genvar i = 1; i < NUM_WORDS; i++) begin : g_rf_latches
    always_latch begin
      if (mem_clocks[i]) begin
        mem[i] = wdata_a_q;
      end
    end
  end



  for (genvar i = 0; i < NumRegisterWindows; i++) begin : g_auxrf_latches
    always_latch begin
      if (aux_mem_clocks[i]) begin
        aux_mem[i] = {mcause_i, mepc_i};
      end
    end
  end

  // With dummy instructions enabled, R0 behaves as a real register but will always return 0 for
  // real instructions.
  if (DummyInstructions) begin : g_dummy_r0
    // SEC_CM: CTRL_FLOW.UNPREDICTABLE
    logic                 we_r0_dummy;
    logic                 r0_clock;
    logic [DataWidth-1:0] mem_r0;

    // Write enable for dummy R0 register (waddr_a_i will always be 0 for dummy instructions)
    assign we_r0_dummy = we_a_i & dummy_instr_wb_i;

    // R0 clock gate
    prim_clock_gating cg_i (
        .clk_i     ( clk_int     ),
        .en_i      ( we_r0_dummy ),
        .test_en_i ( test_en_i   ),
        .clk_o     ( r0_clock    )
    );

    always_latch begin : latch_wdata
      if (r0_clock) begin
        mem_r0 = wdata_a_q;
      end
    end

    // Output the dummy data for dummy instructions, otherwise R0 reads as zero
    assign mem[0] = dummy_instr_id_i ? mem_r0 : WordZeroVal;

  end else begin : g_normal_r0
    logic unused_dummy_instr;
    assign unused_dummy_instr = dummy_instr_id_i ^ dummy_instr_wb_i;

    assign mem[0] = WordZeroVal;
  end

//`ifdef VERILATOR
//  initial begin
//    $display("Latch-based register file not supported for Verilator simulation");
//    $fatal;
//  end
//`endif

endmodule
