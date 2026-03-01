/* Stage-1 bootloader for Sparkle SoC
 *
 * Loaded into IMEM (address 0x00000000).
 * Sets up OpenSBI boot convention:
 *   a0 = hartid (0)
 *   a1 = DTB address (0x80F00000)
 * Then jumps to OpenSBI at 0x80000000 (DRAM).
 */

#ifndef DTB_ADDR
#define DTB_ADDR 0x80F00000
#endif

    .section .text.init, "ax"
    .global _start
_start:
    li   a0, 0              /* hartid = 0 */
    li   a1, DTB_ADDR       /* a1 = DTB address */
    lui  t0, 0x80000        /* t0 = 0x80000000 (OpenSBI entry) */
    jr   t0                 /* jump to DRAM */
_halt:
    j    _halt
