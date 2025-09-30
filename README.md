
# Trabalho T1 - Verificação de Multiplicador

## Descrição
Este projeto implementa a verificação formal (FPV) e baseada em simulação de um multiplicador RISC-V.

## Resultados da Simulação

### Testbench - 20 Casos de Teste
```bash
 === single cycle ===
 
 === Starting test: unsigned*unsigned, a=1, b=1, low=1, single_cycle=1 ===
 Expected result: 00000001
 ** Error: timeout waiting for ALBL state
    Time: 545 ns  Scope: mul_tb.test_multiplier File: ../tb/mul_tb.sv Line: 116
 single cycle ALBL: 00000000
 ** Error: FAIL: Expected=1, Got=0
    Time: 545 ns  Scope: mul_tb.test_multiplier File: ../tb/mul_tb.sv Line: 128
 >>> TEST RESULT: FAIL
 
 === Starting test: unsigned*unsigned, a=2, b=3, low=1, single_cycle=1 ===
 Expected result: 00000006
 single cycle ALBL: 00000006
 >>> TEST RESULT: PASS
 
 === Starting test: unsigned*unsigned, a=0, b=100, low=1, single_cycle=1 ===
 Expected result: 00000000
 single cycle ALBL: 00000000
 >>> TEST RESULT: PASS
 
 === Starting test: unsigned*unsigned, a=255, b=255, low=1, single_cycle=1 ===
 Expected result: 0000fe01
 single cycle ALBL: 0000fe01
 >>> TEST RESULT: PASS
 
 === Starting test: signed*signed, a=5, b=5, low=1, single_cycle=1 ===
 Expected result: 00000019
 single cycle ALBL: 00000019
 >>> TEST RESULT: PASS
 
 === Starting test: signed*signed, a=1, b=1, low=1, single_cycle=1 ===
 Expected result: 00000001
 single cycle ALBL: 00000001
 >>> TEST RESULT: PASS


 === multi cycle ===
 
 === Starting test: unsigned*unsigned, a=10, b=3, low=1, single_cycle=0 ===
 Expected result: 0000001e
 multi cycle result: 0000001e
 >>> TEST RESULT: PASS
 
 === Starting test: unsigned*unsigned, a=15, b=20, low=0, single_cycle=0 ===
 Expected result: 00000000
 multi cycle result: 00000000
 >>> TEST RESULT: PASS
 
 === Starting test: unsigned*unsigned, a=50, b=50, low=0, single_cycle=0 ===
 Expected result: 00000000
 multi cycle result: 00000000
 >>> TEST RESULT: PASS
 
 === Starting test: unsigned*unsigned, a=1000, b=1000, low=1, single_cycle=0 ===
 Expected result: 000f4240
 multi cycle result: 000f4240
 >>> TEST RESULT: PASS
 
 === Starting test: signed*signed, a=5, b=4294967291, low=1, single_cycle=0 ===
 Expected result: ffffffe7
 multi cycle result: ffffffe7
 >>> TEST RESULT: PASS
 
 === Starting test: signed*signed, a=4294967289, b=8, low=1, single_cycle=0 ===
 Expected result: ffffffc8
 multi cycle result: 0007ffc8
 ** Error: FAIL: Expected=ffffffc8, Got=7ffc8
    Time: 925 ns  Scope: mul_tb.test_multiplier File: ../tb/mul_tb.sv Line: 128
 >>> TEST RESULT: FAIL
 
 === Starting test: signed*signed, a=4294967292, b=4294967292, low=1, single_cycle=0 ===
 Expected result: 00000010
 multi cycle result: fffc0010
 ** Error: FAIL: Expected=10, Got=fffc0010
    Time: 965 ns  Scope: mul_tb.test_multiplier File: ../tb/mul_tb.sv Line: 128
 >>> TEST RESULT: FAIL
 
 === Starting test: signed*signed, a=32767, b=32767, low=1, single_cycle=0 ===
 Expected result: 3fff0001
 multi cycle result: 3fff0001
 >>> TEST RESULT: PASS
 
 === Starting test: unsigned*unsigned, a=65535, b=65535, low=1, single_cycle=0 ===
 Expected result: fffe0001
 multi cycle result: fffe0001
 >>> TEST RESULT: PASS
 
 === Starting test: signed*unsigned, a=10, b=3, low=1, single_cycle=0 ===
 Expected result: 0000001e
 multi cycle result: 0000001e
 >>> TEST RESULT: PASS
 
 === Starting test: unsigned*signed, a=10, b=3, low=1, single_cycle=0 ===
 Expected result: 0000001e
 multi cycle result: 0000001e
 >>> TEST RESULT: PASS
 
 === Starting test: signed*signed, a=0, b=0, low=1, single_cycle=0 ===
 Expected result: 00000000
 multi cycle result: 00000000
 >>> TEST RESULT: PASS
 
 === Starting test: signed*signed, a=1, b=4294967295, low=1, single_cycle=0 ===
 Expected result: ffffffff
 multi cycle result: ffffffff
 >>> TEST RESULT: PASS

 === testes completos ===
 ** Note: $finish    : ../tb/mul_tb.sv(166)
    Time: 1215 ns  Iteration: 0  Instance: /mul_tb

### Como Executar
```bash
cd scripts
vsim -do run_questa.do