//enumeration for the state machine
typedef enum logic [4:0] {
    IDLE = 5'b00001,
    ALBL = 5'b00010,
    ALBH = 5'b00100,
    AHBL = 5'b01000,
    AHBH = 5'b10000} mul_states_e;

//module interface (entity)
module mul_prop(
    
  //interface  
  clk,              reset_n, 
  stall,            first_operand_i, 
  second_operand_i, signed_mode_i, 
  enable_i,         mul_low_i, 
  single_cycle_i,   hold_o,    
  result_o,

  // internals
  mul_state,        next_state
);

//module inputs (:in)
input clk, reset_n, stall;
input [31:0] first_operand_i, second_operand_i;
input [1:0]  signed_mode_i;
input enable_i, mul_low_i, single_cycle_i;

//module outputs (:out)
input hold_o;
input [31:0] result_o;

//internal signals
input mul_states_e mul_state, next_state;