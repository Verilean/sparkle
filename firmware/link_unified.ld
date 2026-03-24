/* ============================================================================
 * Linker Script for unified 64KB memory SoC
 *
 * Single memory region: code at bottom, data/BSS after, stack at top.
 * mem_addr[15:2] maps to memory[0:16383] (64KB as 32-bit words).
 * ============================================================================ */

OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x00000000, LENGTH = 64K
}

SECTIONS
{
    .text : ALIGN(4)
    {
        *(.text.init)
        *(.text .text.*)
    } > RAM

    .rodata : ALIGN(4)
    {
        *(.rodata .rodata.*)
        *(.srodata .srodata.*)
    } > RAM

    .data : ALIGN(4)
    {
        __data_start = .;
        *(.data .data.*)
        *(.sdata .sdata.*)
        . = ALIGN(16);
        __global_pointer$ = . + 0x800;
        __data_end = .;
    } > RAM

    .bss (NOLOAD) : ALIGN(4)
    {
        __bss_start = .;
        *(.bss .bss.*)
        *(.sbss .sbss.*)
        *(COMMON)
        . = ALIGN(4);
        __bss_end = .;
    } > RAM

    /* Stack at top of 64KB RAM */
    _stack_top = ORIGIN(RAM) + LENGTH(RAM);   /* 0x00010000 */

    /DISCARD/ :
    {
        *(.comment)
        *(.note*)
        *(.eh_frame*)
    }
}
