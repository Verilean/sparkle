/* ============================================================================
 * Bare-metal RV32IM Test Firmware (M-extension: MUL/DIV/REM)
 *
 * Runs on PicoRV32 with ENABLE_MUL=1, ENABLE_DIV=1.
 * Outputs results via UART (0x10000000) as raw 32-bit words.
 * ============================================================================ */

#define UART_TX     (*(volatile unsigned int *)0x10000000)

static void uart_putword(unsigned int val) {
    UART_TX = val;
}

/* ---------- Test 1: MUL ---------- */

static unsigned int test_mul(void) {
    unsigned int pass = 1;
    unsigned int r;

    r = 7 * 6;
    uart_putword(r);  /* Expected: 42 */
    pass &= (r == 42);

    r = 0 * 12345;
    uart_putword(r);  /* Expected: 0 */
    pass &= (r == 0);

    r = 256 * 256;
    uart_putword(r);  /* Expected: 65536 */
    pass &= (r == 65536);

    r = 0xFFFF * 0xFFFF;
    uart_putword(r);  /* Expected: 0xFFFE0001 */
    pass &= (r == 0xFFFE0001u);

    return pass;
}

/* ---------- Test 2: DIV / REM ---------- */

static unsigned int test_div(void) {
    unsigned int pass = 1;
    unsigned int r;

    r = 42 / 6;
    uart_putword(r);  /* Expected: 7 */
    pass &= (r == 7);

    r = 42 % 6;
    uart_putword(r);  /* Expected: 0 */
    pass &= (r == 0);

    r = 100 / 7;
    uart_putword(r);  /* Expected: 14 */
    pass &= (r == 14);

    r = 100 % 7;
    uart_putword(r);  /* Expected: 2 */
    pass &= (r == 2);

    return pass;
}

/* ---------- Test 3: Signed MUL/DIV ---------- */

static unsigned int test_signed(void) {
    unsigned int pass = 1;
    int r;

    r = (-7) * 6;
    uart_putword((unsigned int)r);  /* Expected: -42 = 0xFFFFFFD6 */
    pass &= (r == -42);

    r = (-100) / 7;
    uart_putword((unsigned int)r);  /* Expected: -14 = 0xFFFFFFF2 */
    pass &= (r == -14);

    r = (-100) % 7;
    uart_putword((unsigned int)r);  /* Expected: -2 = 0xFFFFFFFE */
    pass &= (r == -2);

    return pass;
}

/* ---------- Test 4: Combined — factorial ---------- */

static unsigned int test_factorial(void) {
    unsigned int n = 10;
    unsigned int fact = 1;
    unsigned int i;

    for (i = 2; i <= n; i++) {
        fact = fact * i;
    }

    uart_putword(fact);  /* Expected: 3628800 = 0x375F00 */
    return (fact == 3628800) ? 1 : 0;
}

/* ---------- Main ---------- */

int main(void) {
    unsigned int pass = 1;

    /* Test suite start marker */
    uart_putword(0xDEAD0001);

    /* Test 1: MUL */
    uart_putword(0xAAAA0001);
    pass &= test_mul();

    /* Test 2: DIV/REM */
    uart_putword(0xAAAA0002);
    pass &= test_div();

    /* Test 3: Signed MUL/DIV */
    uart_putword(0xAAAA0003);
    pass &= test_signed();

    /* Test 4: Factorial */
    uart_putword(0xAAAA0004);
    pass &= test_factorial();

    /* Final result marker */
    if (pass) {
        uart_putword(0xCAFE0000);  /* ALL TESTS PASSED */
    } else {
        uart_putword(0xDEADDEAD);  /* SOME TESTS FAILED */
    }

    return pass ? 0 : 1;
}
