clear -all

# analyze -sv
analyze -sv ./rtl/RS5_pkg.sv
analyze -sv ./rtl/mul.sv

# Analyze property files
analyze -sv ./fpv/mul_properties.sv
analyze -sv ./fpv/mul_bindings.sv

# elaborate the design, point to the design top level
elaborate -top {mul}

# Set up Clocks and Resets
clock clk -factor 1 -phase 1
reset -expression {reset_n == 0}

# get designs statistics
get_design_info

prove -all

# Report proof results
report