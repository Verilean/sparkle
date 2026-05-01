#!/usr/bin/env bash
# Re-applies JIT shadow members to verilator/generated_soc_jit.cpp after regen.
# Run after `lake build IP.RV32.SoCVerilog` regenerates the file.
set -euo pipefail
cd "$(dirname "$0")/.."

JIT=verilator/generated_soc_jit.cpp

# Already applied?
if grep -q "_shadow_idex_pc = _gen_idex_pc" "$JIT"; then
  echo "Shadows already applied (full)."
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
        _shadow_idex_rd = _gen_idex_rd;'''
src = pattern.sub(lambda m: m.group(1) + shadow_block, src)

# 3. jit_get_wire — add cases 22-29 before final `}`
get_wire_old = '''            case 20: return (uint64_t)s->_gen_trapCause;
            case 21: return (uint64_t)s->_gen_uartValidBV;
    }
    return 0;
}'''
get_wire_new = '''            case 20: return (uint64_t)s->_gen_trapCause;
            case 21: return (uint64_t)s->_gen_uartValidBV;
            case 22: return (uint64_t)s->_shadow_idex_pc;
            case 23: return (uint64_t)s->_shadow_stall;
            case 24: return (uint64_t)s->_shadow_squash;
            case 25: return (uint64_t)s->_shadow_ifetchStall;
            case 26: return (uint64_t)s->_shadow_alu_result;
            case 27: return (uint64_t)s->_shadow_idex_regWrite;
            case 28: return (uint64_t)s->_shadow_idex_rd;
            case 29: return (uint64_t)s->_gen_exwb_rd;
    }
    return 0;
}'''
src = src.replace(get_wire_old, get_wire_new)

# 4. jit_wire_name
name_old = '''            case 20: return "_gen_trapCause";
            case 21: return "_gen_uartValidBV";
    }
    return "";
}'''
name_new = '''            case 20: return "_gen_trapCause";
            case 21: return "_gen_uartValidBV";
            case 22: return "_shadow_idex_pc";
            case 23: return "_shadow_stall";
            case 24: return "_shadow_squash";
            case 25: return "_shadow_ifetchStall";
            case 26: return "_shadow_alu_result";
            case 27: return "_shadow_idex_regWrite";
            case 28: return "_shadow_idex_rd";
            case 29: return "_gen_exwb_rd";
    }
    return "";
}'''
src = src.replace(name_old, name_new)

# 5. jit_num_wires
src = src.replace("uint32_t jit_num_wires()    { return 22; }", "uint32_t jit_num_wires()    { return 30; }")

with open(path, "w") as f: f.write(src)
print("Applied shadows.")
PY
