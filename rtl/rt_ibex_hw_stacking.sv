// SoC-Hub

/**
 * Hardware stacking unit for RT-IBEX
**/



module rt_ibex_hw_stacking import ibex_pkg::*; #(
) (
    input logic            rst_ni,
    input logic            clk_i,


    input logic            start_i,
    input logic            ack_i,
    input hw_stacking_mode_t mode_i,
    input logic            instr_first_cycle_i,
    input logic            instr_valid_clear_i,
    input logic            id_in_ready_i,


    output logic           instr_valid_o,
    output logic [31:0]    instr_rdata_o,
    output logic [15:0]    instr_rdata_c_o,
    output logic           instr_is_compressed_o,
    output logic           done_o,
    output logic           id_mux_ctrl_o,
    output logic [1:0]     lsu_data_select_o,
    output logic           mcause_pending_o,
    output logic           csr_fast_lsu_o,
    output logic           csr_select_o
);



logic [31:0] instr_rdata;
logic [31:0] mem_instr;
logic [31:0] instr_rdata_c;
logic        instr_is_compressed;
logic        instr_valid;
logic        done;
logic        id_mux_ctrl;
logic [1:0]  instr_sel;

load_sp_t    load_instr;
store_sp_t   store_instr;

logic [4:0]  src_dest;
logic [3:0]  immediate;
logic [1:0]  lsu_data_select;
logic        mcause_pending;
logic        csr_fast_lsu;
logic        csr_select;



enum logic [3:0] {RESET,
                  ALLOC_STACK,
                  X1,
                  X5,
                  X10,
                  X11,
                  X12,
                  X13,
                  X15,
                  MEPC,
                  MCAUSE,
                  DONE
                  } hws_fsm_cs, hws_fsm_ns;



// assign instr_rdata_c_o              = instr_rdata_c;
// assign instr_is_compressed_o        = instr_is_compressed;


assign load_instr.base              = 5'h02;      // SP
assign load_instr.func3             = 3'h2;
assign load_instr.dest              = src_dest;
assign load_instr.imm               = {6'h00, immediate, 2'h0};   // 4-byte aligned
assign load_instr.opcode            = OPCODE_LOAD;


assign store_instr.imm              = {6'h00, immediate[3]};
assign store_instr.base             = 5'h02;      // SP
assign store_instr.func3            = 3'h2;
assign store_instr.src              = src_dest;
assign store_instr.imm2             = {immediate[2:0], 2'h0};   // 4-byte aligned
assign store_instr.opcode           = OPCODE_STORE;


assign mem_instr                    = (mode_i == SAVE) ? store_instr : load_instr;


always_comb begin
  unique case(instr_sel)
    2'b01   : instr_rdata = Alloc_stack_instr;
    2'b10   : instr_rdata = Dealloc_stack_instr;
    default : instr_rdata = mem_instr;
  endcase
end


/// Selecting destination and source registers for load and stores instructions...
/// executed during HW context save/restore
always_comb begin
  unique case (hws_fsm_ns)
    RESET:       src_dest =  5'h0E;
    ALLOC_STACK: src_dest =  5'h0E;
    X1:          src_dest =  5'h01;
    X5:          src_dest =  5'h05;
    X10:         src_dest =  5'h0A;
    X11:         src_dest =  5'h0B;
    X12:         src_dest =  5'h0C;
    X13:         src_dest =  5'h0D;
    X15:         src_dest =  5'h0F;
    MEPC:        src_dest =  5'h0F;
    MCAUSE:      src_dest =  5'h0F;
    default:     src_dest =  5'h0F;
  endcase // case (hws_fsm_ns)
end


always_comb begin
    // Default values
    done                   = 1'b0;
    instr_valid            = 1'b0;
    instr_is_compressed    = 1'b0;
    immediate              = 4'h0;
    id_mux_ctrl            = 1'b0;
    instr_sel              = 2'b00;
    lsu_data_select        = 2'b00;
    mcause_pending         = 1'b0;
    csr_fast_lsu           = 1'b0;
    csr_select             = 1'b0;

    hws_fsm_ns             = hws_fsm_cs;

    unique case (hws_fsm_cs)
      RESET: begin
        if(start_i) begin
          if(mode_i == SAVE) begin
            hws_fsm_ns         = ALLOC_STACK;
          end else begin
            hws_fsm_ns         = X1;
            instr_valid        = 1'b1;

            id_mux_ctrl        = 1'b1;
          end
        end
      end

      ALLOC_STACK: begin
        // Depending on the current mode, a stack of size 9-words is allocated or deallocated

        instr_valid        = 1'b1;   // validate the injected instruction to the ID-stage
        id_mux_ctrl        = 1'b1;   // switch the control/instruction paths in the ID-stage


        if(mode_i == SAVE) begin
          instr_sel          = 2'b01;
        end else begin
          instr_sel          = 2'b10;
        end


        if(id_in_ready_i) begin
          if(mode_i == SAVE) begin
            instr_sel     = 2'b00;
            hws_fsm_ns    = X1;

          end else begin
            done = 1'b1;
            hws_fsm_ns    = DONE;
          end
        end
      end

      X1: begin
        instr_valid        = 1'b1;
        id_mux_ctrl        = 1'b1;
        immediate          = 4'h0;

        if(id_in_ready_i) begin
          immediate          = 4'h1;

          hws_fsm_ns    = X5;
        end
      end

      X5: begin
        instr_valid        = 1'b1;
        id_mux_ctrl        = 1'b1;
        immediate          = 4'h1;

        if(id_in_ready_i) begin
          immediate          = 4'h2;

          hws_fsm_ns    = X10;
        end
      end

      X10: begin
        instr_valid        = 1'b1;
        id_mux_ctrl        = 1'b1;
        immediate          = 4'h2;


        if(id_in_ready_i) begin
          immediate          = 4'h3;

          hws_fsm_ns    = X11;
        end
      end

      X11: begin
        instr_valid        = 1'b1;
        id_mux_ctrl        = 1'b1;
        immediate          = 4'h3;


        if(id_in_ready_i) begin
          immediate          = 4'h4;

          hws_fsm_ns    = X12;
        end
      end

      X12: begin
        instr_valid        = 1'b1;
        id_mux_ctrl        = 1'b1;
        immediate          = 4'h4;

        if(id_in_ready_i) begin
          immediate          = 4'h5;

          hws_fsm_ns    = X13;
        end
      end

      X13: begin
        instr_valid        = 1'b1;
        id_mux_ctrl        = 1'b1;
        immediate          = 4'h5;

        if(id_in_ready_i) begin
          immediate          = 4'h6;

          hws_fsm_ns    = X15;
        end
      end

      X15: begin
        instr_valid        = 1'b1;
        id_mux_ctrl        = 1'b1;
        immediate          = 4'h6;

        if(id_in_ready_i) begin
          immediate          = 4'h7;
          lsu_data_select    = 2'b01;

          hws_fsm_ns    = MEPC;
        end
      end

      MEPC: begin
        instr_valid        = 1'b1;
        id_mux_ctrl        = 1'b1;
        immediate          = 4'h7;
        mcause_pending     = 1'b0;
        lsu_data_select    = 2'b01;

        csr_fast_lsu       = 1'b1;
        csr_select         = 1'b0;

        if(id_in_ready_i) begin
          lsu_data_select    = 2'b10;
          immediate          = 4'h8;

          hws_fsm_ns    = MCAUSE;
        end
      end

      MCAUSE: begin
        instr_valid        = 1'b1;
        id_mux_ctrl        = 1'b1;
        immediate          = 4'h8;
        lsu_data_select    = 2'b10;
        mcause_pending     = 1'b1;

        csr_fast_lsu       = 1'b1;
        csr_select         = 1'b1;

        if(id_in_ready_i) begin
          if(mode_i == RESTORE) begin
            hws_fsm_ns = ALLOC_STACK;
          end else begin
            done          = 1'b1;

            hws_fsm_ns = DONE;
          end
        end
      end

      DONE: begin

        done               = 1'b1;

        if(ack_i) begin
          hws_fsm_ns       = RESET;
        end
      end

      default:
        hws_fsm_ns  = RESET;
    endcase
end



// update registers
always_ff @(posedge clk_i or negedge rst_ni) begin : update_regs
    if (!rst_ni) begin
        hws_fsm_cs             <= RESET;

    end else begin
        hws_fsm_cs             <= hws_fsm_ns;

    end
end



always_ff @(posedge clk_i or negedge rst_ni) begin : update_dest_src
    if (!rst_ni) begin
        done_o                <= 1'b0;
        instr_valid_o         <= 1'b0;
        instr_rdata_o         <= instr_rdata;
        id_mux_ctrl_o         <= 1'b0;
        instr_is_compressed_o <= 1'b0;

        lsu_data_select_o     <= 2'b00;
        mcause_pending_o      <= 1'b0;

    end else begin

        /// The outputs of hw_stacking have to be registered to avoid
        /// comb loops with ibex_controller
        done_o                <= done;
        instr_valid_o         <= instr_valid;
        instr_rdata_o         <= instr_rdata;
        id_mux_ctrl_o         <= id_mux_ctrl;
        instr_is_compressed_o <= instr_is_compressed;

        lsu_data_select_o     <= lsu_data_select;
        mcause_pending_o      <= mcause_pending;

        csr_fast_lsu_o        <= csr_fast_lsu;
        csr_select_o          <= csr_select;
    end
end

endmodule

