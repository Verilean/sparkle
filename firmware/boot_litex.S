/* LiteX PicoRV32 boot code — minimal startup */
.section .text.init
.global _start

_start:
    /* Set stack pointer to top of main_ram (64KB) */
    li sp, 0x10000
    /* Jump to C main */
    j main
