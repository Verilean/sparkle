# ============================================================================
# RV32I Bare-metal Firmware Makefile
#
# Cross-compiles C firmware for the Sparkle-generated RV32I SoC.
#
# Prerequisites:
#   macOS:  brew install riscv64-elf-gcc
#   Ubuntu: sudo apt install gcc-riscv64-unknown-elf
#   Arch:   sudo pacman -S riscv64-elf-gcc
#
# If your toolchain has a different prefix, override CROSS:
#   make CROSS=riscv32-unknown-elf-
# ============================================================================

# Auto-detect cross-compiler prefix
ifneq ($(shell which riscv64-unknown-elf-gcc 2>/dev/null),)
    CROSS ?= riscv64-unknown-elf-
else ifneq ($(shell which riscv64-elf-gcc 2>/dev/null),)
    CROSS ?= riscv64-elf-
else ifneq ($(shell which riscv32-unknown-elf-gcc 2>/dev/null),)
    CROSS ?= riscv32-unknown-elf-
else
    CROSS ?= riscv64-unknown-elf-
endif

CC      = $(CROSS)gcc
AS      = $(CROSS)gcc
LD      = $(CROSS)gcc
OBJCOPY = $(CROSS)objcopy
OBJDUMP = $(CROSS)objdump
SIZE    = $(CROSS)size

# ---------- Flags ----------
ARCH    = -march=rv32i_zicsr -mabi=ilp32

CFLAGS  = $(ARCH) -O2 -Wall -Wextra \
           -ffreestanding -nostdlib -nostartfiles \
           -fno-builtin -fno-exceptions \
           -ffunction-sections -fdata-sections

ASFLAGS = $(ARCH) -c

LDFLAGS = $(ARCH) -nostdlib -nostartfiles \
           -Wl,--gc-sections \
           -Wl,-T,link.ld \
           -Wl,-Map=firmware.map

# ---------- Sources ----------
TARGET  = firmware
SRCS_C  = main.c
SRCS_S  = boot.S
OBJS    = $(SRCS_S:.S=.o) $(SRCS_C:.c=.o)

# ---------- Targets ----------
.PHONY: all clean hex dump info

all: $(TARGET).hex $(TARGET).dump

# Link
$(TARGET).elf: $(OBJS)
	$(LD) $(LDFLAGS) -o $@ $^

# Compile C
%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<

# Assemble
%.o: %.S
	$(AS) $(ASFLAGS) -o $@ $<

# Binary
$(TARGET).bin: $(TARGET).elf
	$(OBJCOPY) -O binary $< $@

# Hex file for $readmemh (32-bit words, one per line)
$(TARGET).hex: $(TARGET).bin
	python3 bin2hex.py $< $@

# Disassembly (for debugging)
$(TARGET).dump: $(TARGET).elf
	$(OBJDUMP) -d -M no-aliases $< > $@

dump: $(TARGET).dump
	@cat $<

# Print section sizes
info: $(TARGET).elf
	$(SIZE) $<

hex: $(TARGET).hex
	@echo "Generated $(TARGET).hex ($$(wc -l < $(TARGET).hex) words)"

clean:
	rm -f *.o *.elf *.bin *.hex *.map *.dump
