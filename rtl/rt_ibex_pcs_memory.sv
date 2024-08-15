module rt_ibex_pcs_memory #(
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
    RETURN_STORE,
    RETURN_RESTORE
  } state_t;

  state_t curr_state, next_state;

  logic [MemWidth-1:0] store_data, restore_data;
  logic [IrqLevelWidth-1:0] addr, addr_r;
  logic req, we;

  always_ff @(posedge clk_i or negedge rst_ni) begin : state_reg
    if (~rst_ni) begin
      curr_state <= IDLE;
      addr_r     <= '0;
    end else begin
      curr_state <= next_state;
      addr_r     <= addr;
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
    addr         = addr_r;
    restore_en_o = '0;

    case (curr_state)
      IDLE: begin
        if (irq_ack_i) begin
          next_state = STORE;
        end else if (next_mret_i) begin
          req = 1;
          next_state = RESTORE;
          addr = addr - 1;
        end
      end
      STORE: begin
        we   = 1;
        req  = 1;
        next_state = RETURN_STORE;
      end
      RESTORE: begin
        req  = 1;
        next_state = RETURN_RESTORE;
      end
      RETURN_STORE: begin
        addr = addr + 1;
        req = 1;
      end
      RETURN_RESTORE: begin
        req = 1;
        restore_en_o = 1;
      end
      default:begin
      end
    endcase

  end

  sram #(
    .DATA_WIDTH (MemWidth),
    .NUM_WORDS  (MemDepth)
  ) i_sram (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .req_i   (req),
    .we_i    (we),
    .addr_i  (addr_r),
    .wdata_i (store_data),
    .be_i    ('1),
    .rdata_o (restore_data)
  );



endmodule : rt_ibex_pcs_memory
