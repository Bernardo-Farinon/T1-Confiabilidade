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
    .next_state         (next_state)
  );

endmodule
