# Script QuestaSim - Executar simulação completa

# Compilar arquivos
vlog -sv rtl/RS5_pkg.sv
vlog -sv rtl/mul.sv  
vlog -sv tb/mul_tb.sv

# Carregar design
vsim work.mul_tb

# Executar simulação completa
run -all