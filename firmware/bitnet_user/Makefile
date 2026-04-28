#
# Build the BitNet userspace test as a static rv32 init binary, then
# wrap it in a cpio.gz that the Linux kernel can use as
# CONFIG_INITRAMFS_SOURCE.
#
# Outputs:
#   init             — static rv32 ELF (the binary that runs as PID 1)
#   initramfs.cpio   — uncompressed cpio archive containing /init + /dev
#   initramfs.cpio.gz (gzipped — what the kernel ultimately consumes)
#
# We use the bare-metal riscv32 cross compiler that already ships in
# shell.nix (pkgsCross.riscv32-embedded). The binary is freestanding —
# all syscalls are issued via inline `ecall`, so there is no libc.

CROSS  ?= riscv32-none-elf-
CC      = $(CROSS)gcc
OBJCOPY = $(CROSS)objcopy
LINUX_DIR ?= /tmp/linux

CFLAGS = -march=rv32ima -mabi=ilp32 -nostdlib -nostartfiles \
         -ffreestanding -fno-builtin -O2 -Wall -Werror -static \
         -Wl,-e,_start

.PHONY: all clean install
all: initramfs.cpio.gz

init: main.c
	$(CC) $(CFLAGS) -o $@ $<

#
# initramfs layout:
#   /init             (the test binary)
#   /dev              (mountpoint for devtmpfs — kernel populates it)
#
# /dev/bitnet0 is created automatically by misc_register at probe time
# once devtmpfs is mounted; we don't need a static device node here.
#
initramfs.cpio: init
	rm -rf staging
	mkdir -p staging/dev
	cp init staging/init
	chmod +x staging/init
	# Reproducible cpio: list files in stable order, no timestamps.
	(cd staging && find . -mindepth 1 -printf '%P\n' | LC_ALL=C sort \
	  | cpio -o -H newc --reproducible --quiet) > $@

initramfs.cpio.gz: initramfs.cpio
	gzip -9 -c -n $< > $@

#
# Install the cpio.gz into the Linux build directory and force-enable
# initramfs autoload. Called from firmware/opensbi/setup.sh.
#
install: initramfs.cpio.gz
	@if [ ! -d "$(LINUX_DIR)" ]; then \
		echo "ERROR: LINUX_DIR=$(LINUX_DIR) not found" >&2; exit 1; fi
	cp initramfs.cpio.gz $(LINUX_DIR)/usr/initramfs.cpio.gz
	$(LINUX_DIR)/scripts/config --file $(LINUX_DIR)/.config \
	    --enable CONFIG_BLK_DEV_INITRD \
	    --enable CONFIG_INITRAMFS_FORCE \
	    --set-str CONFIG_INITRAMFS_SOURCE 'usr/initramfs.cpio.gz' \
	    --enable CONFIG_DEVTMPFS \
	    --enable CONFIG_DEVTMPFS_MOUNT
	@echo "Installed initramfs into $(LINUX_DIR)"

clean:
	rm -rf init staging initramfs.cpio initramfs.cpio.gz
