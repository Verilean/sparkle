/* LiteX PicoRV32 SoC linker script
 * Code and data in main_ram at 0x00000000 */
OUTPUT_ARCH("riscv")
ENTRY(_start)

MEMORY {
    RAM (rwx) : ORIGIN = 0x00000000, LENGTH = 64K
}

SECTIONS {
    .text : ALIGN(4) {
        *(.text.init)
        *(.text .text.*)
        *(.rodata .rodata.*)
    } > RAM

    .data : ALIGN(4) {
        *(.data .data.*)
        *(.sdata .sdata.*)
    } > RAM

    .bss (NOLOAD) : ALIGN(4) {
        *(.bss .bss.*)
        *(.sbss .sbss.*)
    } > RAM

    _stack_top = ORIGIN(RAM) + LENGTH(RAM);
}
