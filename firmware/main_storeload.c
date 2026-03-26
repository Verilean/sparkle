#define UART_TX (*(volatile unsigned int *)0x10000000)
static void uart_putword(unsigned int val) { UART_TX = val; }

int main(void) {
    uart_putword(0xDEAD0001);

    /* Test: store large values to stack, load back, output via UART */
    volatile unsigned int a = 12345;
    volatile unsigned int b = 6789;
    volatile unsigned int c = 0xDEADBEEF;
    volatile unsigned int d = 0x12345678;

    uart_putword(a);  /* Expected: 12345 = 0x3039 */
    uart_putword(b);  /* Expected: 6789 = 0x1A85 */
    uart_putword(c);  /* Expected: 0xDEADBEEF */
    uart_putword(d);  /* Expected: 0x12345678 */

    if (a == 12345 && b == 6789 && c == 0xDEADBEEFu && d == 0x12345678u)
        uart_putword(0xCAFE0000);
    else
        uart_putword(0xDEADDEAD);
    return 0;
}
