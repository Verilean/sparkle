CROSS    ?= riscv64-elf-
DTB_ADDR  = 0x80F00000

all: boot.hex sparkle-soc.dtb

boot.hex: boot.S
	$(CROSS)gcc -march=rv32ima -mabi=ilp32 -nostdlib -Ttext=0 \
		-DDTB_ADDR=$(DTB_ADDR) -o boot.elf $<
	$(CROSS)objcopy -O binary boot.elf boot.bin
	python3 ../bin2hex.py boot.bin boot.hex

sparkle-soc.dtb: ../sparkle-soc.dts
	dtc -I dts -O dtb -o $@ $<

clean:
	rm -f *.o *.elf *.bin *.hex *.dtb

.PHONY: all clean
