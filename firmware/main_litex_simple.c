/*
 * LiteX PicoRV32 SoC — Simple Timer Test (no function calls, no stack)
 * Directly writes to CSR registers to set timer, then halts.
 */

#define TIMER_LOAD      (*(volatile unsigned int *)(0x82001000))
#define TIMER_RELOAD    (*(volatile unsigned int *)(0x82001004))
#define TIMER_EN        (*(volatile unsigned int *)(0x82001008))
#define TIMER_UPDATE    (*(volatile unsigned int *)(0x8200100C))
#define TIMER_VALUE     (*(volatile unsigned int *)(0x82001010))

void _start(void) __attribute__((naked, section(".text.init")));
void _start(void) {
    /* Set timer: load=100000, reload=100000, enable=1 */
    asm volatile(
        "li a0, 0x82001000\n"   /* TIMER_LOAD */
        "li a1, 100000\n"
        "sw a1, 0(a0)\n"        /* TIMER_LOAD = 100000 */
        "sw a1, 4(a0)\n"        /* TIMER_RELOAD = 100000 */
        "li a2, 1\n"
        "sw a2, 8(a0)\n"        /* TIMER_EN = 1 */
        /* Halt loop */
        "1: j 1b\n"
    );
}
