module mul_properties (
    input logic clk,
    input logic reset_n,
    input logic stall,
    input logic [31:0] first_operand_i,
    input logic [31:0] second_operand_i,
    input logic [1:0] signed_mode_i,
    input logic enable_i,
    input logic mul_low_i,
    input logic single_cycle_i,
    input logic hold_o,
    input logic [31:0] result_o
);

    // Importar o tipo de estado do multiplicador
    import RS5_pkg::*;

    // Property 1: Reset assíncrono funciona corretamente
    property reset_property;
        @(posedge clk) disable iff (!reset_n)
        !reset_n |-> ##1 (dut.mul_state == RS5_pkg::ALBL);
    endproperty
    assert_reset: assert property (reset_property);

    // Property 2: Estado IDLE permanece quando enable_i é 0
    property idle_stable;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state == RS5_pkg::IDLE) && !enable_i && !stall |=> (dut.mul_state == RS5_pkg::IDLE);
    endproperty
    assert_idle_stable: assert property (idle_stable);

    // Property 3: Transição de IDLE para ALBL quando enable_i é ativado
    property idle_to_albl;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state == RS5_pkg::IDLE) && enable_i && !stall |=> (dut.mul_state == RS5_pkg::ALBL);
    endproperty
    assert_idle_to_albl: assert property (idle_to_albl);

    // Property 4: Transição de ALBL para IDLE em single-cycle
    property albl_to_idle_single_cycle;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state == RS5_pkg::ALBL) && single_cycle_i && !stall |=> (dut.mul_state == RS5_pkg::IDLE);
    endproperty
    assert_albl_to_idle_single: assert property (albl_to_idle_single_cycle);

    // Property 5: Transição de ALBL para ALBH em multi-cycle
    property albl_to_albh_multi_cycle;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state == RS5_pkg::ALBL) && !single_cycle_i && !stall |=> (dut.mul_state == RS5_pkg::ALBH);
    endproperty
    assert_albl_to_albh: assert property (albl_to_albh_multi_cycle);

    // Property 6: Transição de ALBH para AHBL
    property albh_to_ahbl;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state == RS5_pkg::ALBH) && !stall |=> (dut.mul_state == RS5_pkg::AHBL);
    endproperty
    assert_albh_to_ahbl: assert property (albh_to_ahbl);

    // Property 7: Transição de AHBL para IDLE quando mul_low_i é 1
    property ahbl_to_idle_low;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state == RS5_pkg::AHBL) && mul_low_i && !stall |=> (dut.mul_state == RS5_pkg::IDLE);
    endproperty
    assert_ahbl_to_idle_low: assert property (ahbl_to_idle_low);

    // Property 8: Transição de AHBL para AHBH quando mul_low_i é 0
    property ahbl_to_ahbh_high;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state == RS5_pkg::AHBL) && !mul_low_i && !stall |=> (dut.mul_state == RS5_pkg::AHBH);
    endproperty
    assert_ahbl_to_ahbh: assert property (ahbl_to_ahbh_high);

    // Property 9: Transição de AHBH para IDLE
    property ahbh_to_idle;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state == RS5_pkg::AHBH) && !stall |=> (dut.mul_state == RS5_pkg::IDLE);
    endproperty
    assert_ahbh_to_idle: assert property (ahbh_to_idle);

    // Property 10: hold_o é ativado durante operações multi-ciclo
    property hold_active_during_operation;
        @(posedge clk) disable iff (!reset_n)
        enable_i && (dut.mul_state != RS5_pkg::IDLE) && !dut.last_cycle |-> hold_o;
    endproperty
    assert_hold_active: assert property (hold_active_during_operation);

    // Property 11: hold_o é desativado no último ciclo
    property hold_inactive_last_cycle;
        @(posedge clk) disable iff (!reset_n)
        dut.last_cycle |-> !hold_o;
    endproperty
    assert_hold_inactive: assert property (hold_inactive_last_cycle);

    // Property 12: Stall impede transição de estado
    property stall_prevents_state_change;
        @(posedge clk) disable iff (!reset_n)
        stall && dut.last_cycle |=> (dut.mul_state == $past(dut.mul_state));
    endproperty
    assert_stall_prevents_change: assert property (stall_prevents_state_change);

    // Property 13: Operandos são capturados corretamente no estado IDLE
    property operands_captured_idle;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state == RS5_pkg::IDLE) && enable_i && !stall |=> (dut.op_a == dut.op_al);
    endproperty
    assert_operands_captured: assert property (operands_captured_idle);

    // Property 14: Operando A é atualizado no estado ALBH
    property operand_a_updated_albh;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state == RS5_pkg::ALBH) && !stall |=> (dut.op_a == dut.op_ah);
    endproperty
    assert_operand_a_updated: assert property (operand_a_updated_albh);

    // Property 15: Acumulador é zerado no estado IDLE
    property accumulator_reset_idle;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state == RS5_pkg::IDLE) && !stall |=> (dut.accum == 35'b0);
    endproperty
    assert_accumulator_reset: assert property (accumulator_reset_idle);

    // Property 16: Máquina de estados sempre retorna para IDLE
    property always_returns_to_idle;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state inside {RS5_pkg::ALBL, RS5_pkg::ALBH, RS5_pkg::AHBL, RS5_pkg::AHBH}) 
        && !stall |-> s_eventually (dut.mul_state == RS5_pkg::IDLE);
    endproperty
    assert_returns_to_idle: assert property (always_returns_to_idle);

    // Property 17: Estados válidos da FSM
    property valid_states;
        @(posedge clk) disable iff (!reset_n)
        dut.mul_state inside {RS5_pkg::IDLE, RS5_pkg::ALBL, RS5_pkg::ALBH, 
                             RS5_pkg::AHBL, RS5_pkg::AHBH};
    endproperty
    assert_valid_states: assert property (valid_states);

    // Property 18: Sem deadlock na FSM
    property no_deadlock;
        @(posedge clk) disable iff (!reset_n)
        (dut.mul_state != RS5_pkg::IDLE) && !stall |-> ##[1:10] (dut.mul_state == RS5_pkg::IDLE);
    endproperty
    assert_no_deadlock: assert property (no_deadlock);

    // Property 19: Resultado é estável quando hold_o é 0
    property result_stable_when_not_hold;
        @(posedge clk) disable iff (!reset_n)
        !hold_o |=> $stable(result_o);
    endproperty
    assert_result_stable: assert property (result_stable_when_not_hold);

    // Property 20: Interface de entrada estável durante hold
    property inputs_stable_during_hold;
        @(posedge clk) disable iff (!reset_n)
        hold_o |=> $stable({first_operand_i, second_operand_i, signed_mode_i, 
                           mul_low_i, single_cycle_i});
    endproperty
    assert_inputs_stable: assert property (inputs_stable_during_hold);

endmodule