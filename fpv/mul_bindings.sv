module mul_bind_top;

  bind mul mul_prop mul_bind (
    .clk                (clk),
    .reset_n            (reset_n),
    .stall              (stall),
    .first_operand_i    (first_operand_i),
    .second_operand_i   (second_operand_i),
    .signed_mode_i      (signed_mode_i),
    .enable_i           (enable_i),
    .mul_low_i          (mul_low_i),
    .single_cycle_i     (single_cycle_i),
    .hold_o             (hold_o),
    .result_o           (result_o),

    // internals 
    .mul_state          (mul_state),
    .next_state         (next_state),
    .last_cycle         (last_cycle),
    .should_stall       (should_stall),
    .op_a               (op_a),
    .op_al              (op_al),
    .op_ah              (op_ah),
    .op_b               (op_b),
    .op_bl              (op_bl),
    .op_bh              (op_bh),
    .accum              (accum),
    .mac_result         (mac_result),
    .mac_result_partial (mac_result_partial),
    .mac_result_r       (mac_result_r),
    .signed_mult        (signed_mult)
  );

endmodule