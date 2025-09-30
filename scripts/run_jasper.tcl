# Script para Verificação Formal jasper

# Carregar arquivos de design
read_file -type systemverilog ../rtl/RS5_pkg.sv
read_file -type systemverilog ../rtl/mul.sv

# Carregar propriedades FPV
read_file -type systemverilog ../fpv/mul_properties.sv
read_file -type systemverilog ../fpv/mul_binding.sv

# Configurar top module
set_top mul

# Configurar clock e reset
clock clk
reset !reset_n

# Compilar design
compile

# Verificar todas as propriedades
check_prove -all

# Gerar relatório
report -type status
report -type proof