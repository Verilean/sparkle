# Small RV32I program for the PicoRV32 round-trip check: arithmetic,
# shifts, branches, a loop, word/half/byte stores and loads, a call, then
# `ebreak` (PicoRV32 traps and the testbench stops).
    .section .text
    .globl _start
_start:
    li   sp, 0x800            # stack / data area inside the 4 KiB RAM
    li   a0, 0
    li   t0, 1
    li   t1, 11
loop:                         # a0 = 1 + 2 + … + 10 = 55
    add  a0, a0, t0
    addi t0, t0, 1
    bne  t0, t1, loop
    sw   a0, 0(sp)            # 0x800: 55
    slli a1, a0, 5            # 1760
    srli a2, a1, 3            # 220
    xor  a3, a1, a2
    sw   a3, 4(sp)
    li   a4, -1234
    srai a5, a4, 2            # arithmetic shift of a negative value
    sw   a5, 8(sp)
    sltu a6, a4, a0
    slt  a7, a4, a0
    sb   a6, 12(sp)
    sb   a7, 13(sp)
    sh   a1, 14(sp)
    lw   t2, 12(sp)           # read the bytes/half back as one word
    lbu  t3, 13(sp)
    lh   t4, 14(sp)
    add  t5, t2, t3
    add  t5, t5, t4
    sw   t5, 16(sp)
    jal  ra, fib
    sw   a0, 20(sp)           # fib(12) = 144
    ebreak
fib:                          # iterative Fibonacci, n = 12
    li   t0, 12
    li   a0, 0
    li   a1, 1
1:  add  a2, a0, a1
    mv   a0, a1
    mv   a1, a2
    addi t0, t0, -1
    bnez t0, 1b
    ret
