#!/usr/bin/env python3
"""
Generate N-core LiteX SoC.

For Verilator: module hierarchy (sim_core + wrapper with N instances)
For Sparkle: flat single module with N copies of all signals (prefixed)
"""

import re
import sys
import os

def gen_verilator(n_cores, input_v, output_v):
    """Verilator version: module hierarchy with sub-module instances."""
    with open(input_v) as f:
        single = f.read()
    single_renamed = single.replace("module sim (", "module sim_core (")
    single_renamed = single_renamed.replace("module sim(", "module sim_core(")

    wrapper = f"`timescale 1ns / 1ps\n{single_renamed}\n"
    # All UART ports are real I/O — prevents dead code elimination
    # Plus: shared bus signals that create inter-core dependencies
    ports = ["input sys_clk"]
    for i in range(n_cores):
        ports += [f"input [7:0] serial_sink_data_{i}",
                  f"output serial_sink_ready_{i}",
                  f"input serial_sink_valid_{i}",
                  f"output [7:0] serial_source_data_{i}",
                  f"input serial_source_ready_{i}",
                  f"output serial_source_valid_{i}"]
    # Shared bus output (aggregated from all cores)
    ports += [f"output [7:0] shared_bus_data"]
    wrapper += f"module sim_{n_cores}core(\n    " + ",\n    ".join(ports) + "\n);\n"

    # Shared bus: each core's UART output is OR'd together, then fed back
    # as sink data to all cores. This creates a true data dependency loop
    # where every core's output affects every other core's input.
    wrapper += f"""
    // Shared bus: aggregate all cores' UART output → feed back as input
    // This forces all cores to be evaluated every cycle (no dead code)
    wire [7:0] bus_data;
"""
    # OR all serial_source_data together
    or_chain = " | ".join(f"serial_source_data_{i}" for i in range(n_cores))
    wrapper += f"    assign bus_data = {or_chain};\n"
    wrapper += f"    assign shared_bus_data = bus_data;\n\n"

    for i in range(n_cores):
        # Each core receives: its own serial_sink_data XOR'd with shared bus
        # This creates a feedback loop: core output → bus → other core input
        wrapper += f"""
    wire [7:0] core{i}_sink_data;
    assign core{i}_sink_data = serial_sink_data_{i} ^ bus_data;
    sim_core core{i}(
        .serial_sink_data(core{i}_sink_data),
        .serial_sink_ready(serial_sink_ready_{i}),
        .serial_sink_valid(serial_sink_valid_{i} | (|bus_data)),
        .serial_source_data(serial_source_data_{i}),
        .serial_source_ready(serial_source_ready_{i}),
        .serial_source_valid(serial_source_valid_{i}),
        .sys_clk(sys_clk)
    );
"""
    wrapper += "endmodule\n"
    with open(output_v, 'w') as f:
        f.write(wrapper)
    return os.path.getsize(output_v)


def gen_sparkle(n_cores, input_v, output_v):
    """Sparkle version: flat module with prefixed signal copies."""
    with open(input_v) as f:
        single = f.read()

    # Extract body between module sim(...); and endmodule
    m = re.search(r'module sim\s*\([^)]*\);(.*?)endmodule', single, re.DOTALL)
    if not m:
        print("ERROR: module sim not found")
        return 0
    body = m.group(1)

    # Remove input/output declarations from body (wrapper handles these)
    body = re.sub(r'^\s*(input|output)\s+.*?;\s*$', '', body, flags=re.MULTILINE)

    # Collect ALL identifiers used in the body (conservative: any word token)
    # that are NOT Verilog keywords
    keywords = {'wire', 'reg', 'input', 'output', 'assign', 'always', 'begin',
                'end', 'if', 'else', 'case', 'endcase', 'default', 'posedge',
                'negedge', 'or', 'and', 'not', 'module', 'endmodule', 'for',
                'integer', 'parameter', 'localparam', 'initial', 'signed',
                'generate', 'genvar', 'function', 'endfunction', 'task'}

    # Find declared signal names (reg/wire + arrays)
    declared = set()
    for match in re.finditer(r'(?:reg|wire)\s+(?:signed\s+)?(?:\[[^\]]+\]\s+)?(\w+)', body):
        n = match.group(1)
        if n not in keywords:
            declared.add(n)

    wrapper = f"// {n_cores}-core LiteX PicoRV32 SoC (flat)\n"
    wrapper += f"module sim_{n_cores}core(\n    input sys_clk\n);\n"

    for i in range(n_cores):
        cb = body
        sorted_names = sorted(declared, key=len, reverse=True)
        for name in sorted_names:
            cb = re.sub(r'\b' + re.escape(name) + r'\b', f'c{i}_{name}', cb)
        wrapper += f"\n// ===== Core {i} =====\n{cb}\n"

    wrapper += "endmodule\n"
    with open(output_v, 'w') as f:
        f.write(wrapper)
    return os.path.getsize(output_v)


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    base = os.path.dirname(os.path.abspath(__file__))
    input_v = os.path.join(base, "litex_sim_minimal.v")

    sz1 = gen_verilator(n, input_v, os.path.join(base, f"litex_{n}core.v"))
    sz2 = gen_sparkle(n, input_v, os.path.join(base, f"litex_{n}core_flat.v"))
    print(f"{n}-core: verilator={sz1}B, sparkle_flat={sz2}B")
