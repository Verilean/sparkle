OUTPUT_ARCH("riscv")
ENTRY(_start)
MEMORY { ROM (rx) : ORIGIN = 0x00000000, LENGTH = 128K }
SECTIONS {
    .text : ALIGN(4) { *(.text.init) *(.text .text.*) *(.rodata .rodata.*) *(.srodata .srodata.*) } > ROM
    /DISCARD/ : { *(.comment) *(.riscv.attributes) *(.note.*) *(.eh_frame) }
}
