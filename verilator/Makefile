# ============================================================================
# Verilator Simulation Makefile for Sparkle RV32I SoC
#
# Prerequisites:
#   macOS:  brew install verilator
#   Ubuntu: sudo apt install verilator
#
# Usage:
#   make                  # Build verilator simulation
#   make run              # Run with default firmware
#   make run CYCLES=50000 # Run with custom cycle count
#   make run HEX=path.hex # Run with custom firmware
#   make clean            # Clean build artifacts
# ============================================================================

VERILATOR ?= verilator
VERILATOR_FLAGS = --cc --exe --build -j 0 \
    --trace \
    -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-UNUSEDSIGNAL \
    -Wno-CASEINCOMPLETE -Wno-UNOPTFLAT \
    --top-module rv32i_soc

SV_SRC = rv32i_soc.sv
TB_SRC = tb_soc.cpp

OBJ_DIR = obj_dir
SIM_BIN = $(OBJ_DIR)/Vrv32i_soc

# Default simulation parameters
CYCLES ?= 100000
HEX ?= ../firmware/firmware.hex

.PHONY: all build run clean wave

all: build

build: $(SIM_BIN)

$(SIM_BIN): $(SV_SRC) $(TB_SRC)
	$(VERILATOR) $(VERILATOR_FLAGS) $(SV_SRC) $(TB_SRC)

run: $(SIM_BIN)
	$(SIM_BIN) $(HEX) $(CYCLES)

wave: run
	@echo "VCD trace written to sim_trace.vcd"
	@echo "Open with: gtkwave sim_trace.vcd"

clean:
	rm -rf $(OBJ_DIR) sim_trace.vcd
