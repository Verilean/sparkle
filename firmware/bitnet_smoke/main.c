/* ============================================================================
 * BitNet SoC Smoke Test — Level 1a "Hello World" for CPU + NN IP cohabitation
 *
 * This firmware exercises the BitNet MMIO peripheral on the Sparkle picorv32
 * SoC. It writes four activations to the BitNet input register, reads four
 * results from the BitNet output register, and reports PASS/FAIL via UART.
 *
 * Memory map (from IP/RV32/SoC.lean + IP/RV32/BitNetPeripheral.lean):
 *
 *   0x10000000  W   UART TX (one 32-bit word at a time)
 *   0x40000000  R/W AI status register (unused by v1a, always returns 0)
 *   0x40000004  W   BitNet input latch (write-only)
 *   0x40000008  R   BitNet output (combinational of current input latch)
 *
 * Level 1a BitNet kernel: a 4-input ternary BitLinear with all-+1 weights.
 * Mathematically, this reduces to:
 *
 *     output = input + input + input + input  =  4 * input
 *
 * The firmware asserts this identity for four test inputs. A mismatch means
 * either (a) the MMIO wiring is wrong, (b) the BitNet peripheral diverged
 * from the "4*x" spec, or (c) the picorv32 store→load pipeline gap is too
 * short for the BitNet combinational path to settle (unlikely — picorv32 is
 * multi-cycle so sw/lw pairs are separated by many clocks).
 *
 * UART protocol (matches Tests/SVParser/ParserTest.lean Test 11 style):
 *
 *   0xB17E0001  start marker
 *   <input[0]>  first test input
 *   <output[0]> BitNet result for input[0]
 *   ...
 *   0xCAFE0000  global PASS marker (emitted only if every assertion held)
 *   0xDEADDEAD  global FAIL marker (emitted otherwise)
 *   0xB17E0002  end marker
 * ============================================================================ */

#define UART_TX         (*(volatile unsigned int *)0x10000000)
#define BITNET_INPUT    (*(volatile unsigned int *)0x40000004)
#define BITNET_OUTPUT   (*(volatile unsigned int *)0x40000008)

static void put(unsigned int v) { UART_TX = v; }

int main(void) {
    const unsigned int inputs[4] = {
        0x00010000u,   /* Q16.16 = 1.0  → expected output = 4.0 = 0x00040000 */
        0x00020000u,   /* 2.0           → expected 8.0  = 0x00080000 */
        0x00030000u,   /* 3.0           → expected 12.0 = 0x000C0000 */
        0x00040000u,   /* 4.0           → expected 16.0 = 0x00100000 */
    };

    put(0xB17E0001u);

    int ok = 1;
    for (int i = 0; i < 4; i++) {
        BITNET_INPUT = inputs[i];
        /* picorv32 is multi-cycle; the sw → lw sequence naturally leaves
         * several cycles for the BitNet combinational output to settle.
         * If we ever see stale data, add `asm volatile("nop" ::: "memory")`
         * between the write and the read. */
        unsigned int got = BITNET_OUTPUT;
        unsigned int want = inputs[i] << 2;  /* 4 * input */
        put(inputs[i]);
        put(got);
        if (got != want) ok = 0;
    }

    put(ok ? 0xCAFE0000u : 0xDEADDEADu);
    put(0xB17E0002u);
    while (1) { /* spin */ }
}
