# ============================================================================
# BitNet SoC Smoke Test Firmware — Level 1a
#
# Minimal RV32I firmware that exercises the BitNet MMIO peripheral on the
# Sparkle picorv32 SoC and reports PASS/FAIL via UART.
#
# Inherits cross-compiler auto-detection from ../Makefile. Build:
#
#     make -C firmware/bitnet_smoke
#
# Produces firmware.hex which is loaded by
# Tests/Integration/BitNetSoCTest.lean.
# ============================================================================

# Auto-detect cross-compiler prefix (same probe as ../Makefile)
ifneq ($(shell which riscv64-unknown-elf-gcc 2>/dev/null),)
    CROSS ?= riscv64-unknown-elf-
else ifneq ($(shell which riscv64-elf-gcc 2>/dev/null),)
    CROSS ?= riscv64-elf-
else ifneq ($(shell which riscv32-unknown-elf-gcc 2>/dev/null),)
    CROSS ?= riscv32-unknown-elf-
else ifneq ($(shell which riscv32-none-elf-gcc 2>/dev/null),)
    CROSS ?= riscv32-none-elf-
else
    CROSS ?= riscv64-unknown-elf-
endif

CC      = $(CROSS)gcc
AS      = $(CROSS)gcc
LD      = $(CROSS)gcc
OBJCOPY = $(CROSS)objcopy
OBJDUMP = $(CROSS)objdump

ARCH    = -march=rv32i_zicsr -mabi=ilp32

CFLAGS  = $(ARCH) -O2 -Wall -Wextra \
           -ffreestanding -nostdlib -nostartfiles \
           -fno-builtin -fno-exceptions \
           -ffunction-sections -fdata-sections

ASFLAGS = $(ARCH) -c

# Reuse the parent linker script and boot file rather than duplicating them.
LDFLAGS = $(ARCH) -nostdlib -nostartfiles \
           -Wl,--gc-sections \
           -Wl,-T,../link.ld \
           -Wl,-Map=firmware.map

TARGET  = firmware

.PHONY: all clean

all: $(TARGET).hex $(TARGET).dump

$(TARGET).elf: boot.o main.o
	$(LD) $(LDFLAGS) -o $@ $^

main.o: main.c
	$(CC) $(CFLAGS) -c -o $@ $<

boot.o: ../boot.S
	$(AS) $(ASFLAGS) -o $@ $<

$(TARGET).bin: $(TARGET).elf
	$(OBJCOPY) -O binary $< $@

$(TARGET).hex: $(TARGET).bin
	python3 ../bin2hex.py $< $@

$(TARGET).dump: $(TARGET).elf
	$(OBJDUMP) -d -M no-aliases $< > $@

clean:
	rm -f *.o *.elf *.bin *.hex *.map *.dump
