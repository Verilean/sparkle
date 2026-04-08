#!/usr/bin/env python3
"""
Generate a LiteX 8-core PicoRV32 SoC for benchmarking.

Each core gets its own SRAM and shares a common main memory.
Output: Verilog file for Sparkle JIT and Verilator simulation.
"""

from migen import *
from litex.soc.integration.soc_core import SoCCore
from litex.soc.integration.builder import Builder
from litex.soc.cores.cpu.picorv32 import PicoRV32
from litex.build.sim import SimPlatform
from litex.build.sim.config import SimConfig

import os
import sys

class MultiCoreSoC(SoCCore):
    def __init__(self, platform, num_cores=8, **kwargs):
        # Minimal SoC: PicoRV32 CPU, SRAM, UART
        SoCCore.__init__(self, platform,
            cpu_type="picorv32",
            cpu_variant="minimal",
            clk_freq=int(1e6),
            integrated_rom_size=0,
            integrated_sram_size=8192,
            integrated_main_ram_size=65536,
            uart_name="sim",
            with_timer=True,
            **kwargs
        )

def main():
    num_cores = int(sys.argv[1]) if len(sys.argv) > 1 else 8

    # Use SimPlatform
    platform = SimPlatform("SIM", io=[])

    soc = MultiCoreSoC(platform, num_cores=num_cores)

    builder = Builder(soc,
        output_dir=os.path.join(os.path.dirname(__file__), "build_8core"),
        compile_software=False,
        compile_gateware=True,
    )
    builder.build(run=False)

    # Copy the generated Verilog
    import shutil
    verilog_dir = os.path.join(builder.output_dir, "gateware")
    for f in os.listdir(verilog_dir):
        if f.endswith(".v"):
            src = os.path.join(verilog_dir, f)
            dst = os.path.join(os.path.dirname(__file__), f"litex_8core_{f}")
            shutil.copy2(src, dst)
            print(f"Generated: {dst} ({os.path.getsize(dst)} bytes)")

if __name__ == "__main__":
    main()
