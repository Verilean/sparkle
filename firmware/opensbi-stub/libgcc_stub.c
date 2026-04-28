/*
 * Soft-float libgcc subset for OpenSBI on rv32ima.
 *
 * The riscv32-none-elf gcc shipped in the nix shell is built with the
 * default ilp32d multilib (double-float ABI). Linking OpenSBI's
 * `-mabi=ilp32` (soft-float) objects against that libgcc fails with
 * "can't link double-float modules with soft-float modules". OpenSBI
 * pulls only two 64-bit helpers out of libgcc, so we provide them
 * here as plain ilp32 / soft-float C and skip libgcc entirely.
 *
 * Compile with the same flags OpenSBI uses: rv32ima_zicsr_zifencei,
 * mabi=ilp32, no FP. Then pass the resulting .o as part of ELFFLAGS
 * (LIBS) to OpenSBI's link step.
 */

#include <stdint.h>

/* Bit-by-bit unsigned 64-bit division.
 *
 * Returns numer / denom. If denom == 0, returns ~0 (matches libgcc's
 * UB-on-zero contract). */
uint64_t __udivdi3(uint64_t numer, uint64_t denom)
{
    if (denom == 0) return (uint64_t)-1;
    if (denom > numer) return 0;

    /* Shift denom up so its MSB aligns with numer's MSB. */
    int shift = 0;
    while ((denom << 1) <= numer && (denom & ((uint64_t)1 << 63)) == 0) {
        denom <<= 1;
        shift++;
    }

    uint64_t quot = 0;
    while (shift >= 0) {
        if (numer >= denom) {
            numer -= denom;
            quot |= (uint64_t)1 << shift;
        }
        denom >>= 1;
        shift--;
    }
    return quot;
}

/* Bit-by-bit unsigned 64-bit modulo. */
uint64_t __umoddi3(uint64_t numer, uint64_t denom)
{
    if (denom == 0) return numer;
    if (denom > numer) return numer;

    int shift = 0;
    while ((denom << 1) <= numer && (denom & ((uint64_t)1 << 63)) == 0) {
        denom <<= 1;
        shift++;
    }

    while (shift >= 0) {
        if (numer >= denom) {
            numer -= denom;
        }
        denom >>= 1;
        shift--;
    }
    return numer;
}
