#define UART_TX (*(volatile unsigned int *)0x10000000)
static void uart_putword(unsigned int val) { UART_TX = val; }

int main(void) {
    volatile unsigned int a = 7;
    volatile unsigned int b = 6;
    unsigned int r = a * b;
    uart_putword(0xDEAD0001);
    uart_putword(r);           /* Expected: 42 */

    volatile unsigned int c = 100;
    volatile unsigned int d = 100;
    unsigned int r2 = c * d;
    uart_putword(r2);          /* Expected: 10000 */

    volatile unsigned int e = 12345;
    volatile unsigned int f = 6789;
    unsigned int r3 = e * f;
    uart_putword(r3);          /* Expected: 83810205 = 0x4FEC4BD */

    if (r == 42 && r2 == 10000 && r3 == 83810205u)
        uart_putword(0xCAFE0000);
    else
        uart_putword(0xDEADDEAD);
    return 0;
}
