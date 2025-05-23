module rt_ibex_pcs_lifo_latch #(
  parameter int unsigned NrSavedRegs   = 9,
  parameter int unsigned DataWidth     = 32,
  parameter int unsigned IrqLevelWidth = 8
)(
  input  logic clk_i,
  input  logic rst_ni,

  input  logic [IrqLevelWidth-1:0] irq_level_i,
  input  logic irq_ack_i,
  input  logic irq_exit_i,

  input  logic [NrSavedRegs-1:0][DataWidth-1:0] store_data_i,
  output logic [NrSavedRegs-1:0][DataWidth-1:0] restore_data_o,
  output logic restore_en_o,
  input  logic next_mret_i
);

localparam int unsigned MemWidth = (NrSavedRegs * DataWidth);
localparam int unsigned MemDepth = (IrqLevelWidth);

// Control FSM
typedef enum logic [2:0] {
  IDLE,
  STORE,
  RESTORE,
  RETURN_RESTORE
} state_t;

state_t curr_state, next_state;

logic [MemWidth-1:0] store_data, restore_data;
logic req, we;

logic [MemWidth-1:0] shift_reg_d [MemDepth];
logic [MemWidth-1:0] shift_reg_q [MemDepth];

always_ff @(posedge clk_i or negedge rst_ni) begin : state_reg
  if (~rst_ni) begin
    curr_state <= IDLE;
  end else begin
    curr_state <= next_state;
  end
end

always_comb begin : packing_logic
  for (int i = 0; i < NrSavedRegs; i++) begin
    store_data[(DataWidth*(i)) +: DataWidth] = store_data_i[i];
    restore_data_o[i] = restore_data[(DataWidth*(i)) +: DataWidth];
  end
end

always_comb begin : ctrl_fsm

  next_state   = IDLE;
  req          = '0;
  we           = '0;
  restore_en_o = '0;

  unique case (curr_state)
    IDLE: begin
      if (irq_ack_i) begin
        next_state = STORE;
      end else if (next_mret_i) begin
        req = 1;
        next_state = RESTORE;
      end
    end
    STORE: begin
      we   = 1;
      req  = 0;
      next_state   = IDLE;
    end
    RESTORE: begin
      req  = 1;
      next_state = RETURN_RESTORE;
    end
    RETURN_RESTORE: begin
      req = 1;
      restore_en_o = 1;
      next_state   = IDLE;
    end
    default:begin
      next_state   = IDLE;
      req          = '0;
      we           = '0;
      restore_en_o = '0;
    end
  endcase

end

assign latch_en = req || we;

for (genvar ii=0; ii < MemDepth; ii++) begin : g_shift_reg

  always_latch begin
    if(latch_en) begin   // Store
      shift_reg_q[ii] <= shift_reg_d[ii];
    end
    // if (req) begin  // Restore
    //     if (ii == MemDepth-1) begin
    //       shift_reg_d[ii] <= '0;
    //     end else begin
    //       shift_reg_d[ii] <= shift_reg_q[ii+1];
    //     end
    // end
  end

  always_comb begin : d_select
    if(we) begin   // Store
      if (ii == 0) begin
        shift_reg_d[ii] = store_data;
      end else begin
        shift_reg_d[ii] = shift_reg_q[ii-1];
      end
    end else begin  // Restore
      if (ii == MemDepth-1) begin
        shift_reg_d[ii] = '0;
      end else begin
        shift_reg_d[ii] = shift_reg_q[ii+1];
      end
    end
  end
end
//     case (curr_state)
//       STORE: begin
//         if (ii == 0) begin
//           shift_reg_d[ii] = store_data;
//         end else begin
//           shift_reg_d[ii] = shift_reg_q[ii-1];
//         end
//       end
//       RESTORE: begin
//         if (ii == MemDepth-1) begin
//           shift_reg_d[ii] = '0;
//         end else begin
//           shift_reg_d[ii] = shift_reg_q[ii+1];
//         end
//       end
//       default:;
//     endcase
//   end

// end : g_shift_reg

assign restore_data = shift_reg_q[0];

endmodule : rt_ibex_pcs_lifo_latch
