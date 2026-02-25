# ============================================================================
# RV32I Bare-metal Boot Code
#
# Minimal startup: set stack pointer, clear BSS, jump to main.
# Targets the Sparkle-generated RV32I SoC.
#
# Memory map:
#   IMEM: 0x00000000 - 0x00003FFF  (16KB instruction memory)
#   DMEM: 0x00000000 - 0x0000FFFF  (64KB data memory, separate bus)
#   CLINT: 0x02000000              (timer, software interrupt)
#   UART:  0x10000000              (TX-only console)
# ============================================================================

    .section .text.init, "ax"
    .global _start
    .type _start, @function

_start:
    # -----------------------------------------------------------
    # 0. Set mtvec to trap handler (direct mode)
    # -----------------------------------------------------------
    la    t0, _trap_handler
    csrw  mtvec, t0

    # -----------------------------------------------------------
    # 1. Set stack pointer to top of data memory (64KB)
    # -----------------------------------------------------------
    lui   sp, %hi(_stack_top)
    addi  sp, sp, %lo(_stack_top)

    # -----------------------------------------------------------
    # 2. Clear BSS section
    # -----------------------------------------------------------
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

    # -----------------------------------------------------------
    # 3. Set global pointer (optional, for relaxation)
    # -----------------------------------------------------------
    .option push
    .option norelax
    lui   gp, %hi(__global_pointer$)
    addi  gp, gp, %lo(__global_pointer$)
    .option pop

    # -----------------------------------------------------------
    # 4. Call main
    # -----------------------------------------------------------
    jal   ra, main

    # -----------------------------------------------------------
    # 5. Halt: infinite loop after main returns
    #    Write return code to a test-result address first.
    # -----------------------------------------------------------
    lui   t0, 0x10000          # UART base = 0x10000000
    sw    a0, 0(t0)            # Write main's return value to UART

_halt:
    j     _halt                # Spin forever

    .size _start, . - _start

# ============================================================================
# Trap handler
#
# Minimal handler: saves context via mscratch, reads mcause,
# adjusts mepc for ECALL, records trap cause, returns via MRET.
# ============================================================================
    .global _trap_handler
    .type _trap_handler, @function
    .balign 4

_trap_handler:
    # Save t0 to mscratch, t1 to stack
    csrw  mscratch, t0
    addi  sp, sp, -8
    sw    t1, 0(sp)

    # Read mcause to determine trap type
    csrr  t0, mcause

    # For ECALL (cause=11): increment mepc by 4 to skip ecall instruction
    li    t1, 11
    bne   t0, t1, _trap_not_ecall
    csrr  t0, mepc
    addi  t0, t0, 4
    csrw  mepc, t0
_trap_not_ecall:

    # For timer interrupt (cause=0x80000007): clear by setting mtimecmp high
    csrr  t0, mcause
    li    t1, 0x80000007
    bne   t0, t1, _trap_not_timer
    # Set mtimecmp to max value to clear the interrupt
    li    t1, 0x02004004       # CLINT_MTIMECMP_HI
    li    t0, 0x7FFFFFFF
    sw    t0, 0(t1)
_trap_not_timer:

    # Store mcause to global variable for test verification
    csrr  t0, mcause
    la    t1, _trap_cause
    sw    t0, 0(t1)

    # Restore t1 from stack, t0 from mscratch
    lw    t1, 0(sp)
    addi  sp, sp, 8
    csrr  t0, mscratch
    mret

    .size _trap_handler, . - _trap_handler

# ============================================================================
# Trap cause storage (in BSS)
# ============================================================================
    .section .bss
    .global _trap_cause
    .balign 4
_trap_cause:
    .word 0
