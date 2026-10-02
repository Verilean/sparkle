/* LiteX PicoRV32 SoC (Tests/SVParser/fixtures/litex_sim_minimal.v):
 * ROM 0x00000000 (128 KB), SRAM 0x01000000 (8 KB), main_ram 0x40000000
 * (64 KB), CSR 0x82000000.  Reset vector 0; the stack is the SRAM. */
.section .text.init
.global _start
_start:
    li sp, 0x01002000
    j main
