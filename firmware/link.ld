/* ============================================================================
 * RV32I Bare-metal Linker Script
 *
 * Memory map for the Sparkle-generated RV32I SoC:
 *   IMEM: Instruction memory (Harvard, accessed via PC)
 *   DMEM: Data memory (Harvard, accessed via load/store)
 *
 * The RISC-V toolchain sees a unified address space.
 * We place code at 0x00000000 (→ IMEM) and data at 0x00010000 (→ DMEM).
 * The SoC's bus decoder routes load/store addresses to DMEM (truncated).
 * ============================================================================ */

OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
    /* Instruction memory: 16KB (4096 x 32-bit words) */
    IMEM (rx)  : ORIGIN = 0x00000000, LENGTH = 16K

    /* Data memory: 64KB (16384 x 32-bit words) */
    /* Offset to avoid linker overlap with IMEM region */
    DMEM (rw)  : ORIGIN = 0x00010000, LENGTH = 64K
}

SECTIONS
{
    /* ---- Code (loaded into IMEM via $readmemh) ---- */
    .text : ALIGN(4)
    {
        *(.text.init)       /* Boot code first */
        *(.text .text.*)
    } > IMEM

    .rodata : ALIGN(4)
    {
        *(.rodata .rodata.*)
        *(.srodata .srodata.*)
    } > IMEM

    /* ---- Data (loaded into DMEM or initialized at runtime) ---- */
    .data : ALIGN(4)
    {
        __data_start = .;
        *(.data .data.*)
        *(.sdata .sdata.*)

        /* Global pointer: middle of small-data region for ±2KB access */
        . = ALIGN(16);
        __global_pointer$ = . + 0x800;
        __data_end = .;
    } > DMEM

    .bss (NOLOAD) : ALIGN(4)
    {
        __bss_start = .;
        *(.bss .bss.*)
        *(.sbss .sbss.*)
        *(COMMON)
        . = ALIGN(4);
        __bss_end = .;
    } > DMEM

    /* Stack at top of DMEM */
    _stack_top = ORIGIN(DMEM) + LENGTH(DMEM);   /* 0x00020000 */

    /* Discard unwanted sections */
    /DISCARD/ :
    {
        *(.comment)
        *(.note*)
        *(.eh_frame*)
    }
}
