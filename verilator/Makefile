# ============================================================================
# Verilator Simulation Makefile for Sparkle RV32I SoC
#
# Prerequisites:
#   macOS:  brew install verilator
#   Ubuntu: sudo apt install verilator
#
# Usage:
#   make                  # Build verilator simulation (uses generated SV)
#   make generate         # Generate SV from Lean (lake build)
#   make run              # Run with default firmware
#   make run CYCLES=50000 # Run with custom cycle count
#   make run HEX=path.hex # Run with custom firmware
#   make clean            # Clean build artifacts
#   make build-handwritten # Build with hand-written SV (reference)
# ============================================================================

VERILATOR ?= verilator
VERILATOR_FLAGS = --cc --exe --build -j 0 \
    --trace \
    -Wno-WIDTHEXPAND -Wno-WIDTHTRUNC -Wno-UNUSEDSIGNAL \
    -Wno-CASEINCOMPLETE -Wno-UNOPTFLAT \
    --top-module rv32i_soc

SV_SRC = generated_soc.sv rv32i_soc_wrapper.sv
TB_SRC = tb_soc.cpp

OBJ_DIR = obj_dir
SIM_BIN = $(OBJ_DIR)/Vrv32i_soc

# Default simulation parameters
CYCLES ?= 100000
HEX ?= ../firmware/firmware.hex

# CppSim settings
CPPSIM_CXX ?= clang++
CPPSIM_FLAGS = -std=c++17 -O3 -march=native -DNDEBUG
CPPSIM_BIN = cppsim_soc

.PHONY: all build generate run clean wave build-handwritten \
        generate-cppsim build-cppsim run-cppsim benchmark \
        build-jit run-jit bench

all: build

generate:
	cd .. && lake build IP.RV32.SoCVerilog

build: generate $(SIM_BIN)

$(SIM_BIN): $(SV_SRC) $(TB_SRC)
	$(VERILATOR) $(VERILATOR_FLAGS) -CFLAGS -DTRACE_INTERNAL_SIGNALS $(SV_SRC) $(TB_SRC)

build-handwritten:
	$(VERILATOR) $(VERILATOR_FLAGS) rv32i_soc.sv tb_soc_minimal.cpp

run: $(SIM_BIN)
	$(SIM_BIN) $(HEX) $(CYCLES)

wave: run
	@echo "VCD trace written to sim_trace.vcd"
	@echo "Open with: gtkwave sim_trace.vcd"

# CppSim targets
generate-cppsim:
	cd .. && lake build IP.RV32.SoCVerilog

build-cppsim: generate-cppsim
	$(CPPSIM_CXX) $(CPPSIM_FLAGS) -o $(CPPSIM_BIN) tb_cppsim.cpp

run-cppsim: build-cppsim
	./$(CPPSIM_BIN) $(HEX) $(CYCLES)

benchmark: $(SIM_BIN) build-cppsim
	@echo "=== Verilator ===" && time ./$(SIM_BIN) $(HEX) $(CYCLES)
	@echo "=== CppSim ===" && time ./$(CPPSIM_BIN) $(HEX) $(CYCLES)

# JIT targets
build-jit: generate
	$(CPPSIM_CXX) -shared -fPIC -O2 -std=c++17 -o generated_soc_jit.dylib generated_soc_jit.cpp

run-jit: build-jit
	cd .. && lake exe rv32-jit-test verilator/generated_soc_jit.cpp $(HEX) 5000

# Unified benchmark: Verilator vs JIT side-by-side
bench: verilator_bench jit_bench build-jit
	./bench.sh $(CYCLES) $(HEX)

verilator_bench: $(SIM_BIN) tb_verilator_bench.cpp
	$(CPPSIM_CXX) -O2 -std=c++17 -o verilator_bench tb_verilator_bench.cpp \
		$$(find obj_dir -name '*.o' ! -name 'tb_soc*') \
		-I$(OBJ_DIR) \
		-I$$($(VERILATOR) --getenv VERILATOR_ROOT)/include \
		-I$$($(VERILATOR) --getenv VERILATOR_ROOT)/include/vltstd \
		$$($(VERILATOR) --getenv VERILATOR_ROOT)/include/verilated.cpp \
		$$($(VERILATOR) --getenv VERILATOR_ROOT)/include/verilated_vcd_c.cpp \
		$$($(VERILATOR) --getenv VERILATOR_ROOT)/include/verilated_threads.cpp

jit_bench: tb_jit_bench.cpp
	$(CPPSIM_CXX) -O2 -std=c++17 -o jit_bench tb_jit_bench.cpp -ldl

clean:
	rm -rf $(OBJ_DIR) sim_trace.vcd $(CPPSIM_BIN) *.dylib verilator_bench jit_bench
