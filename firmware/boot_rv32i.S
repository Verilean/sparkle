# ============================================================================
# RV32I Bare-metal Boot Code (no CSR/IRQ)
#
# Minimal startup for PicoRV32 default config (RV32I only).
# ============================================================================

    .section .text.init, "ax"
    .global _start
    .type _start, @function

_start:
    # 1. Set stack pointer to top of data memory (64KB)
    lui   sp, %hi(_stack_top)
    addi  sp, sp, %lo(_stack_top)

    # 2. Clear BSS section
    lui   t0, %hi(__bss_start)
    addi  t0, t0, %lo(__bss_start)
    lui   t1, %hi(__bss_end)
    addi  t1, t1, %lo(__bss_end)
.bss_clear:
    bge   t0, t1, .bss_done
    sw    zero, 0(t0)
    addi  t0, t0, 4
    j     .bss_clear
.bss_done:

    # 3. Set global pointer
    .option push
    .option norelax
    lui   gp, %hi(__global_pointer$)
    addi  gp, gp, %lo(__global_pointer$)
    .option pop

    # 4. Call main
    jal   ra, main

    # 5. Halt: write return code to UART and spin
    lui   t0, 0x10000          # UART base = 0x10000000
    sw    a0, 0(t0)            # Write main's return value

_halt:
    j     _halt

    .size _start, . - _start
