# Build the libgcc stub used by OpenSBI to bypass the missing
# soft-float multilib in the nix-shell rv32 toolchain.
#
# Output: libgcc_stub.a — passed to OpenSBI's link step via ELFFLAGS.

CROSS  ?= riscv32-none-elf-
CC      = $(CROSS)gcc
AR      = $(CROSS)ar

CFLAGS = -march=rv32ima_zicsr_zifencei -mabi=ilp32 -mcmodel=medany \
         -nostdlib -ffreestanding -fno-builtin -O2 -Wall -Werror

.PHONY: all clean
all: libgcc_stub.a

libgcc_stub.o: libgcc_stub.c
	$(CC) $(CFLAGS) -c -o $@ $<

libgcc_stub.a: libgcc_stub.o
	$(AR) rcs $@ $<

clean:
	rm -f libgcc_stub.o libgcc_stub.a
