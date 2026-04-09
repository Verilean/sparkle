#==============================================================================
# Sparkle → Alveo U280 Physical Constraints (STUB)
#
# Placeholder constraint file. Not usable as-is. The real version will
# populate pin assignments, clock groups, and false-path declarations
# as described in:
#
#   UG1120 UltraScale+ Integrated Block for PCIe (§ XDC templates)
#   UG1393 Vitis Application Acceleration Development Flow
#   The Xilinx U280 XDC template shipped under:
#     <Vivado install>/data/boards/board_parts/xilinx.com/au280/1.2/
#
# See fpga/U280/README.md for the roadmap that must be completed before
# this file has any real content.
#==============================================================================

# ------------------------------------------------------------------------
# Reference clock — 156.25 MHz from the USER_SI570 oscillator (GTYP quad)
# ------------------------------------------------------------------------
# set_property PACKAGE_PIN BJ43 [get_ports refclk_p]
# set_property PACKAGE_PIN BJ44 [get_ports refclk_n]
# create_clock -period 6.400 -name refclk [get_ports refclk_p]

# ------------------------------------------------------------------------
# PCIe Gen4 x16 (Quad-based, Vivado IP wizard handles the low-level pins;
# we only need user-facing sideband).
# ------------------------------------------------------------------------
# set_property PACKAGE_PIN BF41 [get_ports pcie_perstn]
# set_property IOSTANDARD  LVCMOS18 [get_ports pcie_perstn]

# ------------------------------------------------------------------------
# HBM (two stacks). The HBM IP wizard generates the low-level XDC.
# We only override clock associations here.
# ------------------------------------------------------------------------
# create_clock -period 2.222 -name hbm_ref_clk [get_pins hbm_ref_clk_bufg/O]
# set_clock_groups -asynchronous \
#     -group [get_clocks refclk]           \
#     -group [get_clocks hbm_ref_clk]

# ------------------------------------------------------------------------
# UART bring-up (pmod0 or schematic-specific; TBD once shell is chosen)
# ------------------------------------------------------------------------
# set_property PACKAGE_PIN ___ [get_ports uart_tx]
# set_property IOSTANDARD LVCMOS18 [get_ports uart_tx]

# ------------------------------------------------------------------------
# LEDs (user status indicators)
# ------------------------------------------------------------------------
# set_property PACKAGE_PIN BC21 [get_ports {led[0]}]
# set_property PACKAGE_PIN BC22 [get_ports {led[1]}]
# set_property PACKAGE_PIN BB21 [get_ports {led[2]}]
# set_property IOSTANDARD LVCMOS18 [get_ports {led[*]}]

# ------------------------------------------------------------------------
# False paths (CDC between PCIe, HBM, and SoC clocks)
# ------------------------------------------------------------------------
# set_false_path -from [get_clocks pcie_user_clk] -to [get_clocks soc_clk]
# set_false_path -from [get_clocks soc_clk]       -to [get_clocks pcie_user_clk]
