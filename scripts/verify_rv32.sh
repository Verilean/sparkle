#!/bin/bash
# verify_rv32.sh — Unified RV32I Signal DSL verification
#
# Runs both Lean4-native simulation and Verilog generation/simulation.
#
# Usage:
#   ./scripts/verify_rv32.sh                    # full pipeline
#   ./scripts/verify_rv32.sh --lean-only        # skip iverilog
#   ./scripts/verify_rv32.sh --verilog-only     # skip Lean4 sim

set -e

LEAN_ONLY=false
VERILOG_ONLY=false

for arg in "$@"; do
  case "$arg" in
    --lean-only) LEAN_ONLY=true ;;
    --verilog-only) VERILOG_ONLY=true ;;
  esac
done

echo "=== RV32I Signal DSL Verification ==="

# 1. Build Lean4 project (always needed)
echo ""
echo "--- Step 1: Building Lean4 project ---"
lake build Examples.RV32

if [ "$VERILOG_ONLY" = false ]; then
  # 2. Run Lean4 simulation (fast, using Signal.atTime with firmware)
  echo ""
  echo "--- Step 2: Running Lean4 simulation ---"
  if [ -f "firmware/firmware.hex" ]; then
    lake env lean --run Tests/RV32/SimTest.lean firmware/firmware.hex 1000
  else
    echo "No firmware found, running with empty IMEM (100 cycles)..."
    lake env lean --run Tests/RV32/SimTest.lean
  fi
fi

if [ "$LEAN_ONLY" = false ]; then
  # 3. Generate Verilog from CircuitM (Signal DSL Verilog is generated at compile time)
  echo ""
  echo "--- Step 3: Generating Verilog ---"
  lake env lean --run Tests/RV32/VerilogDump.lean

  # 4. Run iverilog simulation (optional, requires iverilog)
  if command -v iverilog &> /dev/null; then
    echo ""
    echo "--- Step 4: Running iverilog simulation ---"
    if [ -f "hw/sim/tb_rv32.v" ]; then
      mkdir -p hw/sim
      iverilog -g2012 -o hw/sim/rv32i_sim hw/gen/rv32i_soc.sv hw/sim/tb_rv32.v
      if [ -f "firmware/firmware.hex" ]; then
        vvp hw/sim/rv32i_sim +firmware=firmware/firmware.hex
      else
        vvp hw/sim/rv32i_sim
      fi
    else
      echo "No testbench found at hw/sim/tb_rv32.v, skipping iverilog"
    fi
  else
    echo ""
    echo "--- Step 4: Skipping iverilog (not installed) ---"
  fi
fi

echo ""
echo "=== Verification Complete ==="
