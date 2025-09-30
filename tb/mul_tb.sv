`timescale 1ns/1ps

module mul_tb;
    logic clk;
    logic reset_n;
    logic stall;
    logic [31:0] first_operand_i;
    logic [31:0] second_operand_i;
    logic [1:0] signed_mode_i;
    logic enable_i;
    logic mul_low_i;
    logic single_cycle_i;

    logic hold_o;
    logic [31:0] result_o;

    mul dut (
        .clk(clk),
        .reset_n(reset_n),
        .stall(stall),
        .first_operand_i(first_operand_i),
        .second_operand_i(second_operand_i),
        .signed_mode_i(signed_mode_i),
        .enable_i(enable_i),
        .mul_low_i(mul_low_i),
        .single_cycle_i(single_cycle_i),
        .hold_o(hold_o),
        .result_o(result_o)
    );

    initial clk = 0;
    always #5 clk = ~clk;

    initial begin
        reset_n = 0;
        enable_i = 0;
        stall = 0;
        mul_low_i = 0;
        single_cycle_i = 0;
        first_operand_i = 0;
        second_operand_i = 0;
        signed_mode_i = 0;
        #20;
        reset_n = 1;
        #10;
    end

    task automatic wait_for_completion();
        int timeout = 0;
        while (hold_o && timeout < 100) begin
            @(posedge clk);
            timeout++;
        end
        if (timeout >= 100) begin
            $error("Timeout waiting for multiplication completion");
        end
    endtask

    task automatic test_multiplier(
        input [31:0] a,
        input [31:0] b,
        input [1:0] mode,
        input bit get_low_result,
        input bit single_cycle
    );
        logic [63:0] expected_full;
        logic [31:0] expected;
        logic [31:0] captured_result;
        string mode_str;
        int timeout;

        case(mode)
            2'b00: begin 
                expected_full = a * b;
                mode_str = "unsigned*unsigned";
            end
            2'b01: begin 
                expected_full = $signed(a) * b;
                mode_str = "signed*unsigned";
            end
            2'b10: begin 
                expected_full = a * $signed(b);
                mode_str = "unsigned*signed";
            end
            2'b11: begin 
                expected_full = $signed(a) * $signed(b);
                mode_str = "signed*signed";
            end
        endcase

        expected = get_low_result ? expected_full[31:0] : expected_full[63:32];

        $display("\n=== Starting test: %s, a=%0d, b=%0d, low=%0b, single_cycle=%0b ===",
                 mode_str, a, b, get_low_result, single_cycle);
        $display("Expected result: %h", expected);

        first_operand_i = a;
        second_operand_i = b;
        signed_mode_i = mode;
        mul_low_i = get_low_result;
        single_cycle_i = single_cycle;

        @(posedge clk);
        enable_i = 1;
        @(posedge clk);
        enable_i = 0;

        if (single_cycle) begin
            // single cycle aguarda ALBL com timeout
            timeout = 0;
            while (dut.mul_state != 5'b00010 && timeout < 50) begin // ALBL = 5'b00010
                @(posedge clk);
                timeout++;
            end
            if (timeout >= 50) begin
                $error("timeout waiting for ALBL state");
            end
            captured_result = result_o;
            $display("single cycle ALBL: %h", captured_result);
        end else begin
            wait_for_completion();
            @(posedge clk);
            captured_result = result_o;
            $display("multi cycle result: %h", captured_result);
        end

        assert (captured_result === expected) else begin
            $error("FAIL: Expected=%0h, Got=%0h", expected, captured_result);
        end

        $display(">>> TEST RESULT: %s", (captured_result === expected) ? "PASS" : "FAIL");
        #10;
    endtask

    initial begin
        $display("=== inicio teste ===");
        
       @(posedge reset_n);
        @(posedge clk);
        #10;

        $display("\n=== single cycle ===");
        test_multiplier( 1,   1, 2'b00, 1, 1);   // 1*1=1
        test_multiplier( 2,   3, 2'b00, 1, 1);   // 2*3=6
        test_multiplier( 0, 100, 2'b00, 1, 1);   // 0*100=0
        test_multiplier(255, 255, 2'b00, 1, 1);  // 255*255=65025
        test_multiplier( 5,   5, 2'b11, 1, 1);   // 5*5=25 signed
        test_multiplier( 1,   1, 2'b11, 1, 1);   // 1*1=1 signed

        $display("\n=== multi cycle ===");
        test_multiplier(10,  3, 2'b00, 1, 0);    // 10*3=30
        test_multiplier(15, 20, 2'b00, 0, 0);    // 15*20 high=0
        test_multiplier(50, 50, 2'b00, 0, 0);    // 50*50 high=0
        test_multiplier(1000,1000,2'b00,1,0);    // 1000*1000=1000000
        test_multiplier( 5,  -5, 2'b11,1,0);     // 5*-5=-25 signed
        test_multiplier(-7,   8, 2'b11,1,0);     // -7*8=-56 signed
        test_multiplier(-4,  -4, 2'b11,1,0);     // -4*-4=16 signed
        test_multiplier(32767,32767,2'b11,1,0);  // 32767*32767=1073676289 signed
        test_multiplier(65535,65535,2'b00,1,0);  // 65535*65535=4294836225
        test_multiplier(10,   3, 2'b01,1,0);     // signed*unsigned
        test_multiplier(10,   3, 2'b10,1,0);     // unsigned*signed
        test_multiplier( 0,   0, 2'b11,1,0);     // 0*0 signed
        test_multiplier( 1,  -1, 2'b11,1,0);     // 1*-1 signed

        $display("\n=== testes completos ===");
        $finish;
    end

endmodule