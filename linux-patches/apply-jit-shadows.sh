#!/usr/bin/env bash
# Re-applies JIT shadow members to verilator/generated_soc_jit.cpp after regen.
# Run after `lake build IP.RV32.SoCVerilog` regenerates the file.
set -euo pipefail
cd "$(dirname "$0")/.."

JIT=verilator/generated_soc_jit.cpp

# Already applied?
if grep -q "_shadow_idex_imm = _gen_idex_imm" "$JIT"; then
  echo "Shadows already applied (full+IFID+MMU+AMO+rdata+TLB+wdata+imm)."
  exit 0
fi

# 1. Class member declarations
python3 - <<'PY'
import re
path = "verilator/generated_soc_jit.cpp"
with open(path) as f: src = f.read()
shadow_block = '''
    // SPARKLE-DEBUG shadows
    uint32_t _shadow_idex_pc = 0;
    uint8_t _shadow_stall = 0;
    uint8_t _shadow_squash = 0;
    uint8_t _shadow_ifetchStall = 0;
    uint8_t _shadow_idex_regWrite = 0;
    uint8_t _shadow_idex_rd = 0;
    uint32_t _shadow_alu_result = 0;
    uint8_t _shadow_dmem_we = 0;
    uint32_t _shadow_dmem_write_addr = 0;
    uint32_t _shadow_dmem_write_data = 0;
    uint32_t _shadow_effectiveAddr_ex = 0;
    uint32_t _shadow_fetchPC = 0;
    uint32_t _shadow_ifid_pc = 0;
    uint32_t _shadow_ifid_inst = 0;
    uint8_t _shadow_stallDelay = 0;
    uint8_t _shadow_freezeIDEX = 0;
    uint32_t _shadow_pcReg = 0;
    uint8_t _shadow_mmuState = 0;
    uint8_t _shadow_ptwState = 0;
    uint8_t _shadow_dTLBMiss = 0;
    uint8_t _shadow_anyTLBHit = 0;
    uint8_t _shadow_isMMUFault = 0;
    uint32_t _shadow_dMissPC = 0;
    uint32_t _shadow_dMissVaddr = 0;
    uint8_t _shadow_dMissIsStore = 0;
    uint8_t _shadow_pendingWriteEn = 0;
    uint8_t _shadow_exwb_isAMO = 0;
    uint8_t _shadow_idex_isAMO = 0;
    uint8_t _shadow_exwb_isAMOrw = 0;
    uint32_t _shadow_dmem_rdata = 0;
    uint32_t _shadow_dmem_read_addr = 0;
    uint32_t _shadow_tlb0VPN = 0;
    uint32_t _shadow_tlb0PPN = 0;
    uint8_t _shadow_tlb0Valid = 0;
    uint8_t _shadow_tlb0Mega = 0;
    uint32_t _shadow_tlb1VPN = 0;
    uint32_t _shadow_tlb1PPN = 0;
    uint8_t _shadow_tlb1Valid = 0;
    uint8_t _shadow_tlb1Mega = 0;
    uint32_t _shadow_tlb2VPN = 0;
    uint32_t _shadow_tlb2PPN = 0;
    uint8_t _shadow_tlb2Valid = 0;
    uint8_t _shadow_tlb2Mega = 0;
    uint32_t _shadow_tlb3VPN = 0;
    uint32_t _shadow_tlb3PPN = 0;
    uint8_t _shadow_tlb3Valid = 0;
    uint8_t _shadow_tlb3Mega = 0;
    uint32_t _shadow_idex_imm = 0;
    uint32_t _shadow_alu_a = 0;
    uint32_t _shadow_alu_b = 0;
    uint8_t _shadow_idex_aluSrcB = 0;
    uint32_t _shadow_idex_rs1Val = 0;
    uint32_t _shadow_ex_rs1 = 0;
    uint8_t _shadow_fwd_rs1_match = 0;
    uint32_t _shadow_mipSoftReg = 0;
    uint32_t _shadow_sieReg = 0;
    uint32_t _shadow_mstatusReg = 0;
    uint8_t _shadow_privMode = 0;
    uint32_t _shadow_mipValue = 0;
    uint8_t _shadow_sTimerInt = 0;
    uint32_t _shadow_midelegReg = 0;
    // Internal wires'''
src = src.replace("\n    // Internal wires", shadow_block, 1)

# 2. Shadow assignments after squash computation
import re
pattern = re.compile(r"(        _gen_squash = \([^;]+\);)")
shadow_block = '''
        _shadow_idex_pc = _gen_idex_pc;
        _shadow_stall = _gen_stall;
        _shadow_squash = _gen_squash;
        _shadow_ifetchStall = (_gen_ifetchTLBMiss & (!_gen_ifetchFaultPending));
        _shadow_alu_result = _gen_alu_result;
        _shadow_idex_regWrite = _gen_idex_regWrite;
        _shadow_idex_rd = _gen_idex_rd;
        _shadow_dmem_we = _gen_dmem_we;
        _shadow_dmem_write_addr = _gen_actual_dmem_write_addr;
        _shadow_dmem_write_data = _gen_ex_rs2_approx;
        _shadow_effectiveAddr_ex = _gen_effectiveAddr;
        _shadow_fetchPC = _gen_fetchPC_1;
        _shadow_ifid_pc = _gen_ifid_pc;
        _shadow_ifid_inst = _gen_ifid_inst_in;
        _shadow_stallDelay = _gen_stallDelay;
        _shadow_freezeIDEX = _gen_freezeIDEX;
        _shadow_pcReg = _gen_pcReg;
        _shadow_mmuState = _gen_mmuStateReg;
        _shadow_ptwState = _gen_ptwStateReg;
        _shadow_dTLBMiss = _gen_dTLBMiss;
        _shadow_anyTLBHit = _gen_anyTLBHit;
        _shadow_isMMUFault = _gen_isMMUFault;
        _shadow_dMissPC = _gen_dMissPC;
        _shadow_dMissVaddr = _gen_dMissVaddr;
        _shadow_dMissIsStore = _gen_dMissIsStore;
        _shadow_pendingWriteEn = _gen_pendingWriteEn;
        _shadow_exwb_isAMO = _gen_exwb_isAMO;
        _shadow_idex_isAMO = _gen_idex_isAMO;
        _shadow_exwb_isAMOrw = _gen_exwb_isAMOrw;
        _shadow_dmem_rdata = _gen_dmem_rdata;
        _shadow_dmem_read_addr = _gen_dmem_read_addr;
        _shadow_tlb0VPN = _gen_tlb0VPN;
        _shadow_tlb0PPN = _gen_tlb0PPN;
        _shadow_tlb0Valid = _gen_tlb0Valid;
        _shadow_tlb0Mega = _gen_tlb0Mega;
        _shadow_tlb1VPN = _gen_tlb1VPN;
        _shadow_tlb1PPN = _gen_tlb1PPN;
        _shadow_tlb1Valid = _gen_tlb1Valid;
        _shadow_tlb1Mega = _gen_tlb1Mega;
        _shadow_tlb2VPN = _gen_tlb2VPN;
        _shadow_tlb2PPN = _gen_tlb2PPN;
        _shadow_tlb2Valid = _gen_tlb2Valid;
        _shadow_tlb2Mega = _gen_tlb2Mega;
        _shadow_tlb3VPN = _gen_tlb3VPN;
        _shadow_tlb3PPN = _gen_tlb3PPN;
        _shadow_tlb3Valid = _gen_tlb3Valid;
        _shadow_tlb3Mega = _gen_tlb3Mega;
        _shadow_idex_imm = _gen_idex_imm;
        _shadow_alu_a = _gen_alu_a;
        _shadow_alu_b = _gen_alu_b;
        _shadow_idex_aluSrcB = _gen_idex_aluSrcB;
        _shadow_idex_rs1Val = _gen_idex_rs1Val;
        _shadow_ex_rs1 = _gen_ex_rs1;
        _shadow_fwd_rs1_match = _gen_fwd_rs1_match;
        _shadow_mipSoftReg = _gen_mipSoftReg;
        _shadow_sieReg = _gen_sieReg;
        _shadow_mstatusReg = _gen_mstatusReg;
        _shadow_privMode = _gen_privMode;
        _shadow_mipValue = _gen_mipValue;
        _shadow_sTimerInt = _gen_sTimerIntEnabled;
        _shadow_midelegReg = _gen_midelegReg;'''
src = pattern.sub(lambda m: m.group(1) + shadow_block, src)

# 3. jit_get_wire — robust replacement: rewrite the whole switch body
# Find the block: from `case 20: return ... _gen_trapCause` to the next `}` after `return 0;`
import re
get_wire_block_pattern = re.compile(
    r"(            case 20: return \(uint64_t\)s->_gen_trapCause;\n            case 21: return \(uint64_t\)s->_gen_uartValidBV;\n)"
    r"(?:.*?\n)*?"  # any intermediate lines (already-applied shadows)
    r"(    \}\n    return 0;\n\})",
    re.MULTILINE
)
get_wire_replacement = (
    "            case 20: return (uint64_t)s->_gen_trapCause;\n"
    "            case 21: return (uint64_t)s->_gen_uartValidBV;\n"
    "            case 22: return (uint64_t)s->_shadow_idex_pc;\n"
    "            case 23: return (uint64_t)s->_shadow_stall;\n"
    "            case 24: return (uint64_t)s->_shadow_squash;\n"
    "            case 25: return (uint64_t)s->_shadow_ifetchStall;\n"
    "            case 26: return (uint64_t)s->_shadow_alu_result;\n"
    "            case 27: return (uint64_t)s->_shadow_idex_regWrite;\n"
    "            case 28: return (uint64_t)s->_shadow_idex_rd;\n"
    "            case 29: return (uint64_t)s->_gen_exwb_rd;\n"
    "            case 30: return (uint64_t)s->_shadow_dmem_we;\n"
    "            case 31: return (uint64_t)s->_shadow_dmem_write_addr;\n"
    "            case 32: return (uint64_t)s->_shadow_effectiveAddr_ex;\n"
    "            case 33: return (uint64_t)s->_shadow_fetchPC;\n"
    "            case 34: return (uint64_t)s->_shadow_ifid_pc;\n"
    "            case 35: return (uint64_t)s->_shadow_ifid_inst;\n"
    "            case 36: return (uint64_t)s->_shadow_stallDelay;\n"
    "            case 37: return (uint64_t)s->_shadow_freezeIDEX;\n"
    "            case 38: return (uint64_t)s->_shadow_pcReg;\n"
    "            case 39: return (uint64_t)s->_shadow_mmuState;\n"
    "            case 40: return (uint64_t)s->_shadow_ptwState;\n"
    "            case 41: return (uint64_t)s->_shadow_dTLBMiss;\n"
    "            case 42: return (uint64_t)s->_shadow_anyTLBHit;\n"
    "            case 43: return (uint64_t)s->_shadow_isMMUFault;\n"
    "            case 44: return (uint64_t)s->_shadow_dMissPC;\n"
    "            case 45: return (uint64_t)s->_shadow_dMissVaddr;\n"
    "            case 46: return (uint64_t)s->_shadow_dMissIsStore;\n"
    "            case 47: return (uint64_t)s->_shadow_pendingWriteEn;\n"
    "            case 48: return (uint64_t)s->_shadow_exwb_isAMO;\n"
    "            case 49: return (uint64_t)s->_shadow_idex_isAMO;\n"
    "            case 50: return (uint64_t)s->_shadow_exwb_isAMOrw;\n"
    "            case 51: return (uint64_t)s->_shadow_dmem_rdata;\n"
    "            case 52: return (uint64_t)s->_shadow_dmem_read_addr;\n"
    "            case 53: return (uint64_t)s->_shadow_tlb0VPN;\n"
    "            case 54: return (uint64_t)s->_shadow_tlb0PPN;\n"
    "            case 55: return (uint64_t)s->_shadow_tlb0Valid;\n"
    "            case 56: return (uint64_t)s->_shadow_tlb0Mega;\n"
    "            case 57: return (uint64_t)s->_shadow_tlb1VPN;\n"
    "            case 58: return (uint64_t)s->_shadow_tlb1PPN;\n"
    "            case 59: return (uint64_t)s->_shadow_tlb1Valid;\n"
    "            case 60: return (uint64_t)s->_shadow_tlb1Mega;\n"
    "            case 61: return (uint64_t)s->_shadow_tlb2VPN;\n"
    "            case 62: return (uint64_t)s->_shadow_tlb2PPN;\n"
    "            case 63: return (uint64_t)s->_shadow_tlb2Valid;\n"
    "            case 64: return (uint64_t)s->_shadow_tlb2Mega;\n"
    "            case 65: return (uint64_t)s->_shadow_tlb3VPN;\n"
    "            case 66: return (uint64_t)s->_shadow_tlb3PPN;\n"
    "            case 67: return (uint64_t)s->_shadow_tlb3Valid;\n"
    "            case 68: return (uint64_t)s->_shadow_tlb3Mega;\n"
    "            case 69: return (uint64_t)s->_shadow_dmem_write_data;\n"
    "            case 70: return (uint64_t)s->_shadow_idex_imm;\n"
    "            case 71: return (uint64_t)s->_shadow_alu_a;\n"
    "            case 72: return (uint64_t)s->_shadow_alu_b;\n"
    "            case 73: return (uint64_t)s->_shadow_idex_aluSrcB;\n"
    "            case 74: return (uint64_t)s->_shadow_idex_rs1Val;\n"
    "            case 75: return (uint64_t)s->_shadow_ex_rs1;\n"
    "            case 76: return (uint64_t)s->_shadow_fwd_rs1_match;\n"
    "            case 77: return (uint64_t)s->_shadow_mipSoftReg;\n"
    "            case 78: return (uint64_t)s->_shadow_sieReg;\n"
    "            case 79: return (uint64_t)s->_shadow_mstatusReg;\n"
    "            case 80: return (uint64_t)s->_shadow_privMode;\n"
    "            case 81: return (uint64_t)s->_shadow_mipValue;\n"
    "            case 82: return (uint64_t)s->_shadow_sTimerInt;\n"
    "            case 83: return (uint64_t)s->_shadow_midelegReg;\n"
    "    }\n"
    "    return 0;\n"
    "}"
)
src = get_wire_block_pattern.sub(get_wire_replacement, src, count=1)

# 4. jit_wire_name — robust regex replacement
name_block_pattern = re.compile(
    r"(            case 20: return \"_gen_trapCause\";\n            case 21: return \"_gen_uartValidBV\";\n)"
    r"(?:.*?\n)*?"
    r"(    \}\n    return \"\";\n\})",
    re.MULTILINE
)
name_replacement = (
    "            case 20: return \"_gen_trapCause\";\n"
    "            case 21: return \"_gen_uartValidBV\";\n"
    "            case 22: return \"_shadow_idex_pc\";\n"
    "            case 23: return \"_shadow_stall\";\n"
    "            case 24: return \"_shadow_squash\";\n"
    "            case 25: return \"_shadow_ifetchStall\";\n"
    "            case 26: return \"_shadow_alu_result\";\n"
    "            case 27: return \"_shadow_idex_regWrite\";\n"
    "            case 28: return \"_shadow_idex_rd\";\n"
    "            case 29: return \"_gen_exwb_rd\";\n"
    "            case 30: return \"_shadow_dmem_we\";\n"
    "            case 31: return \"_shadow_dmem_write_addr\";\n"
    "            case 32: return \"_shadow_effectiveAddr_ex\";\n"
    "            case 33: return \"_shadow_fetchPC\";\n"
    "            case 34: return \"_shadow_ifid_pc\";\n"
    "            case 35: return \"_shadow_ifid_inst\";\n"
    "            case 36: return \"_shadow_stallDelay\";\n"
    "            case 37: return \"_shadow_freezeIDEX\";\n"
    "            case 38: return \"_shadow_pcReg\";\n"
    "            case 39: return \"_shadow_mmuState\";\n"
    "            case 40: return \"_shadow_ptwState\";\n"
    "            case 41: return \"_shadow_dTLBMiss\";\n"
    "            case 42: return \"_shadow_anyTLBHit\";\n"
    "            case 43: return \"_shadow_isMMUFault\";\n"
    "            case 44: return \"_shadow_dMissPC\";\n"
    "            case 45: return \"_shadow_dMissVaddr\";\n"
    "            case 46: return \"_shadow_dMissIsStore\";\n"
    "            case 47: return \"_shadow_pendingWriteEn\";\n"
    "            case 48: return \"_shadow_exwb_isAMO\";\n"
    "            case 49: return \"_shadow_idex_isAMO\";\n"
    "            case 50: return \"_shadow_exwb_isAMOrw\";\n"
    "            case 51: return \"_shadow_dmem_rdata\";\n"
    "            case 52: return \"_shadow_dmem_read_addr\";\n"
    "            case 53: return \"_shadow_tlb0VPN\";\n"
    "            case 54: return \"_shadow_tlb0PPN\";\n"
    "            case 55: return \"_shadow_tlb0Valid\";\n"
    "            case 56: return \"_shadow_tlb0Mega\";\n"
    "            case 57: return \"_shadow_tlb1VPN\";\n"
    "            case 58: return \"_shadow_tlb1PPN\";\n"
    "            case 59: return \"_shadow_tlb1Valid\";\n"
    "            case 60: return \"_shadow_tlb1Mega\";\n"
    "            case 61: return \"_shadow_tlb2VPN\";\n"
    "            case 62: return \"_shadow_tlb2PPN\";\n"
    "            case 63: return \"_shadow_tlb2Valid\";\n"
    "            case 64: return \"_shadow_tlb2Mega\";\n"
    "            case 65: return \"_shadow_tlb3VPN\";\n"
    "            case 66: return \"_shadow_tlb3PPN\";\n"
    "            case 67: return \"_shadow_tlb3Valid\";\n"
    "            case 68: return \"_shadow_tlb3Mega\";\n"
    "            case 69: return \"_shadow_dmem_write_data\";\n"
    "            case 70: return \"_shadow_idex_imm\";\n"
    "            case 71: return \"_shadow_alu_a\";\n"
    "            case 72: return \"_shadow_alu_b\";\n"
    "            case 73: return \"_shadow_idex_aluSrcB\";\n"
    "            case 74: return \"_shadow_idex_rs1Val\";\n"
    "            case 75: return \"_shadow_ex_rs1\";\n"
    "            case 76: return \"_shadow_fwd_rs1_match\";\n"
    "            case 77: return \"_shadow_mipSoftReg\";\n"
    "            case 78: return \"_shadow_sieReg\";\n"
    "            case 79: return \"_shadow_mstatusReg\";\n"
    "            case 80: return \"_shadow_privMode\";\n"
    "            case 81: return \"_shadow_mipValue\";\n"
    "            case 82: return \"_shadow_sTimerInt\";\n"
    "            case 83: return \"_shadow_midelegReg\";\n"
    "    }\n"
    "    return \"\";\n"
    "}"
)
src = name_block_pattern.sub(name_replacement, src, count=1)

# 5. jit_num_wires — replace any prior count
src = re.sub(r"uint32_t jit_num_wires\(\)    \{ return \d+; \}",
             "uint32_t jit_num_wires()    { return 84; }", src)

with open(path, "w") as f: f.write(src)
print("Applied shadows (with IFID/fetchPC).")
PY
