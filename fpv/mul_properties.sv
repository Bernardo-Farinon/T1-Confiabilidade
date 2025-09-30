module mul_prop (
    input logic        clk,
    input logic        reset_n,
    input logic        stall,
    input logic [31:0] first_operand_i,
    input logic [31:0] second_operand_i,
    input logic [1:0]  signed_mode_i,
    input logic        enable_i,
    input logic        mul_low_i,
    input logic        single_cycle_i,
    input logic        hold_o,
    input logic [31:0] result_o,

    //internals
    input logic [4:0] mul_state,
    input logic [4:0] next_state,
    input logic last_cycle,
    input logic should_stall,
    input logic [16:0] op_a,
    input logic [16:0] op_al,
    input logic [16:0] op_ah,
    input logic [16:0] op_b,
    input logic [16:0] op_bl,
    input logic [16:0] op_bh,
    input logic [34:0] accum,
    input logic [34:0] mac_result,
    input logic [34:0] mac_result_partial,
    input logic [15:0] mac_result_r,
    input logic signed_mult
);

default clocking @(posedge clk); endclocking
default disable iff (!reset_n);

localparam IDLE = 5'b00001;
localparam ALBL = 5'b00010;
localparam ALBH = 5'b00100;
localparam AHBL = 5'b01000;
localparam AHBH = 5'b10000;

// estado IDLE permanece quando enable_i e 0
property p_idle_stable;
    (mul_state == IDLE) && !enable_i && !stall |=> (mul_state == IDLE);
endproperty
a_idle_stable: assert property (p_idle_stable);

// ytransicao de IDLE para ALBL quando enable_i e 1
property p_idle_to_albl;
    (mul_state == IDLE) && enable_i && !stall |=> (mul_state == ALBL);
endproperty
a_idle_to_albl: assert property (p_idle_to_albl);

// ALBL -> IDLE single cycle 
property p_albl_to_idle_single;
    (mul_state == ALBL) && single_cycle_i && !stall |=> (mul_state == IDLE);
endproperty
a_albl_to_idle_single: assert property (p_albl_to_idle_single);

// ALBL -> ALBH multi cycle
property p_albl_to_albh_multi;
    (mul_state == ALBL) && !single_cycle_i && !stall |=> (mul_state == ALBH);
endproperty
a_albl_to_albh_multi: assert property (p_albl_to_albh_multi);

//  ALBH -> AHBL 
property p_albh_to_ahbl;
    (mul_state == ALBH) && !stall |=> (mul_state == AHBL);
endproperty
a_albh_to_ahbl: assert property (p_albh_to_ahbl);

// AHBL -> IDLE quando mul_low_i e 1
property p_ahbl_to_idle_low;
    (mul_state == AHBL) && mul_low_i && !stall |=> (mul_state == IDLE);
endproperty
a_ahbl_to_idle_low: assert property (p_ahbl_to_idle_low);

// AHBL -> AHBH quando mul_low_i e 0
property p_ahbl_to_ahbh_high;
    (mul_state == AHBL) && !mul_low_i && !stall |=> (mul_state == AHBH);
endproperty
a_ahbl_to_ahbh_high: assert property (p_ahbl_to_ahbh_high);

// AHBH -> IDLE
property p_ahbh_to_idle;
    (mul_state == AHBH) && !stall |=> (mul_state == IDLE);
endproperty
a_ahbh_to_idle: assert property (p_ahbh_to_idle);

// hold_o ativo durante operacoes
property p_hold_active;
    enable_i && (mul_state != IDLE) && !last_cycle |-> hold_o;
endproperty
a_hold_active: assert property (p_hold_active);

// hold_o desativado no lastcycle
property p_hold_inactive;
    last_cycle |-> !hold_o;
endproperty
a_hold_inactive: assert property (p_hold_inactive);

// Stall impede transicao
property p_stall_prevents;
    stall && last_cycle |=> (mul_state == $past(mul_state));
endproperty
a_stall_prevents: assert property (p_stall_prevents);

// Acumulador zerado no IDLE
property p_accumulator_reset;
    (mul_state == IDLE) && !stall |=> (accum == 35'b0);
endproperty
a_accumulator_reset: assert property (p_accumulator_reset);

// Estados validos
property p_valid_states;
    mul_state inside {IDLE, ALBL, ALBH, AHBL, AHBH};
endproperty
a_valid_states: assert property (p_valid_states);

//Resultado estavel
property p_result_stable;
    !hold_o && (mul_state == IDLE) |=> $stable(result_o);
endproperty
a_result_stable: assert property (p_result_stable);

// Next state logico
property p_next_state_coherent;
    !stall |=> (mul_state == $past(next_state));
endproperty
a_next_state_coherent: assert property (p_next_state_coherent);

// fsm progride quando nao em stall 
property p_fsm_progresses;
    (mul_state != IDLE) && !stall && !last_cycle |=> (mul_state != $past(mul_state));
endproperty
a_fsm_progresses: assert property (p_fsm_progresses);

// estados apenas um ativo
property p_mutually_exclusive;
    $onehot0(mul_state);
endproperty
a_mutually_exclusive: assert property (p_mutually_exclusive);

endmodule