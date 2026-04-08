/*
 * LiteX PicoRV32 SoC — Timer Test Firmware
 *
 * Sets up the LiteX timer with a countdown value, enables it,
 * then enters an idle loop. Used to test the timer oracle skip.
 *
 * Memory map:
 *   0x00000000: main_ram (code + data)
 *   0x82000000: CSR base
 *   0x82001000: timer0 CSR bank
 *   0x82001800: UART CSR bank
 */

#define CSR_BASE        0x82000000
#define TIMER_BASE      (CSR_BASE + 0x1000)
#define UART_BASE       (CSR_BASE + 0x1800)

/* Timer CSR registers (word-addressed, each 4 bytes) */
#define TIMER_LOAD      (*(volatile unsigned int *)(TIMER_BASE + 0x00))
#define TIMER_RELOAD    (*(volatile unsigned int *)(TIMER_BASE + 0x04))
#define TIMER_EN        (*(volatile unsigned int *)(TIMER_BASE + 0x08))
#define TIMER_UPDATE    (*(volatile unsigned int *)(TIMER_BASE + 0x0C))
#define TIMER_VALUE     (*(volatile unsigned int *)(TIMER_BASE + 0x10))
#define TIMER_EV_STATUS (*(volatile unsigned int *)(TIMER_BASE + 0x14))
#define TIMER_EV_PENDING (*(volatile unsigned int *)(TIMER_BASE + 0x18))
#define TIMER_EV_ENABLE (*(volatile unsigned int *)(TIMER_BASE + 0x1C))

/* UART CSR registers */
#define UART_RXTX       (*(volatile unsigned int *)(UART_BASE + 0x00))
#define UART_TXFULL     (*(volatile unsigned int *)(UART_BASE + 0x04))
#define UART_RXEMPTY    (*(volatile unsigned int *)(UART_BASE + 0x08))

static void uart_putc(char c) {
    while (UART_TXFULL);
    UART_RXTX = c;
}

static void uart_puts(const char *s) {
    while (*s) uart_putc(*s++);
}

static void uart_puthex(unsigned int val) {
    const char hex[] = "0123456789abcdef";
    for (int i = 28; i >= 0; i -= 4)
        uart_putc(hex[(val >> i) & 0xf]);
}

void main(void) {
    /* Announce start */
    uart_puts("TIMER_TEST\n");

    /* Setup timer: load = 100000, reload = 100000, enable */
    TIMER_LOAD = 100000;
    TIMER_RELOAD = 100000;
    TIMER_EN = 1;

    /* Print initial timer value */
    TIMER_UPDATE = 1;  /* latch current value */
    uart_puts("T0=");
    uart_puthex(TIMER_VALUE);
    uart_putc('\n');

    /* Wait for timer to count down (idle loop) */
    for (volatile int i = 0; i < 200; i++) {
        /* Busy wait — the timer oracle should skip these cycles */
        asm volatile("nop");
    }

    /* Read timer again */
    TIMER_UPDATE = 1;
    uart_puts("T1=");
    uart_puthex(TIMER_VALUE);
    uart_putc('\n');

    /* Signal completion */
    uart_puts("DONE\n");

    /* Halt */
    while (1) asm volatile("nop");
}
