/* Stage-1 bootloader for Sparkle SoC
 *
 * Loaded into IMEM (address 0x00000000). Runs in M-mode with the MMU
 * off. The Sparkle SoC has separate IMEM (instruction-only) and
 * DMEM/DRAM (data) memories — code can be fetched from IMEM but data
 * loads (lw/lbu/etc.) cannot read it. So we cannot embed strings or
 * tables here; everything has to be encoded as immediates in the
 * instruction stream.
 *
 * Before handing off to OpenSBI we run a small BitNet self-test:
 * push 8 Q16.16 activations through the peripheral and emit each
 * input/output/want triple plus PASS/FAIL over UART. This is the
 * earliest possible point we can observe the BitNet token stream
 * end-to-end through the CPU pipeline; it doesn't depend on Linux
 * boot, slab init, driver probe, or console_init succeeding.
 *
 * UART output:
 *
 *     BITNET v1a SELFTEST
 *     in=<8hex> out=<8hex> want=<8hex> [PASS|FAIL]
 *     ... (8 vectors total)
 *     BITNET PASS  (or BITNET FAIL)
 *
 * After the self-test, the CPU sets up OpenSBI's a0/a1 boot convention
 * and jumps to 0x80000000 to continue normal boot.
 */

#ifndef DTB_ADDR
#define DTB_ADDR 0x81F00000
#endif

#define UART_TX     0x10000000
#define BITNET_IN   0x40000004
#define BITNET_OUT  0x40000008

/* Macro: emit one ASCII byte via UART_TX. Clobbers t0, t1.
 * (UART_TX address re-loaded inside in case caller's t0 changed.) */
.macro PUTC ch
    li   t0, UART_TX
    li   t1, \ch
    sw   t1, 0(t0)
.endm

/* Macro: emit a 4-char tag like "in=" via 4 PUTCs, no string fetch needed. */

    .section .text.init, "ax"
    .global _start
_start:
    /* Initialize sp to top of DRAM (32 MB @ 0x80000000-0x82000000).
     * We pick 0x81EFFF00: well below the DTB at 0x81F00000 and well
     * above the kernel image at 0x80400000-0x81C00000. Without this,
     * sp == 0 on reset and stack writes/reads target PA 0xFFFFFFF0,
     * which the bus drops, causing run_vector's saved ra to read
     * back as zero and the next ret to jump to PC=0 (= boot.hex
     * restart, infinite "BITNET v1a SELFTEST" loop). */
    li   sp, 0x81EFFF00
    li   s8, 0                    /* overall fail flag */

    /* "\nBITNET v1a SELFTEST\n" */
    PUTC '\n'
    PUTC 'B'
    PUTC 'I'
    PUTC 'T'
    PUTC 'N'
    PUTC 'E'
    PUTC 'T'
    PUTC ' '
    PUTC 'v'
    PUTC '1'
    PUTC 'a'
    PUTC ' '
    PUTC 'S'
    PUTC 'E'
    PUTC 'L'
    PUTC 'F'
    PUTC 'T'
    PUTC 'E'
    PUTC 'S'
    PUTC 'T'
    PUTC '\n'

    /* Run 8 vectors with inline (input, expected) immediates. */
    li   s2, 0x00010000
    li   s3, 0x00410000
    jal  ra, run_vector

    li   s2, 0x00020000
    li   s3, 0x02020000
    jal  ra, run_vector

    li   s2, 0x00030000
    li   s3, 0x06C30000
    jal  ra, run_vector

    li   s2, 0x00040000
    li   s3, 0x10040000
    jal  ra, run_vector

    li   s2, 0x00080000
    li   s3, 0x80080000
    jal  ra, run_vector

    li   s2, 0x00000100
    li   s3, 0x00000100
    jal  ra, run_vector

    li   s2, 0x12345678
    li   s3, 0x5AD1BC9A
    jal  ra, run_vector

    li   s2, 0x00000000
    li   s3, 0x00000000
    jal  ra, run_vector

    /* "BITNET PASS\n" or "BITNET FAIL\n" depending on s8. */
    PUTC 'B'
    PUTC 'I'
    PUTC 'T'
    PUTC 'N'
    PUTC 'E'
    PUTC 'T'
    PUTC ' '
    bnez s8, fail_total
    PUTC 'P'
    PUTC 'A'
    PUTC 'S'
    PUTC 'S'
    j    end_selftest
fail_total:
    PUTC 'F'
    PUTC 'A'
    PUTC 'I'
    PUTC 'L'
end_selftest:
    PUTC '\n'
    PUTC '\n'

    /* Hand off to OpenSBI */
    li   a0, 0
    li   a1, DTB_ADDR
    lui  t0, 0x80000
    jr   t0
_halt:
    j    _halt

/* run_vector: drive (s2 = input) through BitNet, compare against (s3 = want),
 * emit "  in=0x<hex> out=0x<hex> want=0x<hex> [PASS|FAIL]\n". Sets s8=1 on
 * mismatch. Uses s4 to hold the read-back result; ra is preserved by caller. */
run_vector:
    addi sp, sp, -16
    sw   ra, 12(sp)

    /* Drive peripheral.  Several nops between sw and lw to give the
     * 4-stage pipeline time to commit the store before the load issues
     * its EX-stage address. Without this padding the load can race the
     * store-update of aiInputReg and read back the previous cycle's
     * BitNet output (effectively the input we just wrote, since the
     * register update is one cycle behind). */
    li   t0, BITNET_IN
    sw   s2, 0(t0)
    nop
    nop
    nop
    nop
    li   t0, BITNET_OUT
    lw   s4, 0(t0)

    /* "  in=0x" */
    PUTC ' '
    PUTC ' '
    PUTC 'i'
    PUTC 'n'
    PUTC '='
    PUTC '0'
    PUTC 'x'
    mv   t2, s2
    jal  ra, puthex32

    /* " out=0x" */
    PUTC ' '
    PUTC 'o'
    PUTC 'u'
    PUTC 't'
    PUTC '='
    PUTC '0'
    PUTC 'x'
    mv   t2, s4
    jal  ra, puthex32

    /* " want=0x" */
    PUTC ' '
    PUTC 'w'
    PUTC 'a'
    PUTC 'n'
    PUTC 't'
    PUTC '='
    PUTC '0'
    PUTC 'x'
    mv   t2, s3
    jal  ra, puthex32

    /* " PASS\n" or " FAIL\n" */
    PUTC ' '
    bne  s4, s3, vec_fail
    PUTC 'P'
    PUTC 'A'
    PUTC 'S'
    PUTC 'S'
    j    vec_done
vec_fail:
    li   s8, 1
    PUTC 'F'
    PUTC 'A'
    PUTC 'I'
    PUTC 'L'
vec_done:
    PUTC '\n'

    lw   ra, 12(sp)
    addi sp, sp, 16
    ret

/* puthex32: print register t2 as 8 lowercase hex digits via UART_TX.
 * Uses s7 as temp loop counter so we don't clobber the caller's t-regs. */
puthex32:
    li   s7, 8
puthex_loop:
    li   t0, UART_TX
    srli t1, t2, 28
    andi t1, t1, 0xf
    li   t4, 10
    blt  t1, t4, puthex_skip_alpha
    addi t1, t1, 0x27         /* 'a'-'0'-10 */
puthex_skip_alpha:
    addi t1, t1, 0x30         /* '0' */
    sw   t1, 0(t0)
    slli t2, t2, 4
    addi s7, s7, -1
    bnez s7, puthex_loop
    ret
