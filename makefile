BUILD_DIR = work

all: sim

compile:
	@echo "=== COMPILANDO RS5_pkg ==="
	vlog -sv -work $(BUILD_DIR) rtl/RS5_pkg.sv
	@echo "=== COMPILANDO mul ==="
	vlog -sv -work $(BUILD_DIR) rtl/mul.sv
	@echo "=== COMPILANDO mul_tb ==="
	vlog -sv -work $(BUILD_DIR) tb/mul_tb.sv

sim: compile
	@echo "=== INICIANDO SIMULAÇÃO ==="
	vsim -c -do "run -all; quit" -lib $(BUILD_DIR) mul_tb

clean:
	rm -rf $(BUILD_DIR) transcript vsim.wlf

debug:
	vsim -lib $(BUILD_DIR) mul_tb

.PHONY: all compile sim clean debug