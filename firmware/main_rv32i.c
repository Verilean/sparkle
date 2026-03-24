/* ============================================================================
 * Bare-metal RV32I Test Firmware (RV32I-only subset)
 *
 * Runs on PicoRV32 with default parameters (no M/A/CSR extensions).
 * Outputs results via UART (0x10000000) as raw 32-bit words.
 * ============================================================================ */

#define UART_TX     (*(volatile unsigned int *)0x10000000)

static void uart_putword(unsigned int val) {
    UART_TX = val;
}

/* ---------- Test 1: Fibonacci Sequence ---------- */

static unsigned int test_fibonacci(void) {
    unsigned int a = 0, b = 1;
    unsigned int i;
    unsigned int last = 0;

    for (i = 0; i < 10; i++) {
        uart_putword(a);
        last = a;
        unsigned int next = a + b;
        a = b;
        b = next;
    }

    /* Expected: 0,1,1,2,3,5,8,13,21,34 → last = 34 */
    return last;
}

/* ---------- Test 2: Array Sum ---------- */

static unsigned int test_array_sum(void) {
    volatile unsigned int arr[8];
    unsigned int i;

    arr[0] = 10;  arr[1] = 20;  arr[2] = 30;  arr[3] = 40;
    arr[4] = 50;  arr[5] = 60;  arr[6] = 70;  arr[7] = 80;

    unsigned int sum = 0;
    for (i = 0; i < 8; i++) {
        sum += arr[i];
    }

    uart_putword(sum);  /* Expected: 360 = 0x168 */
    return sum;
}

/* ---------- Test 3: Bubble Sort ---------- */

static unsigned int test_sort(void) {
    volatile unsigned int data[6];
    unsigned int i, j, tmp;

    data[0] = 42;  data[1] = 17;  data[2] = 99;
    data[3] = 3;   data[4] = 55;  data[5] = 8;

    for (i = 0; i < 6; i++) {
        for (j = 0; j < 5 - i; j++) {
            if (data[j] > data[j + 1]) {
                tmp = data[j];
                data[j] = data[j + 1];
                data[j + 1] = tmp;
            }
        }
    }

    /* Output sorted: 3,8,17,42,55,99 */
    unsigned int checksum = 0;
    for (i = 0; i < 6; i++) {
        uart_putword(data[i]);
        checksum ^= data[i];
    }

    return checksum;
}

/* ---------- Test 4: GCD (Euclid) ---------- */

static unsigned int gcd(unsigned int a, unsigned int b) {
    while (a != b) {
        if (a > b)
            a = a - b;
        else
            b = b - a;
    }
    return a;
}

static unsigned int test_gcd(void) {
    unsigned int r1 = gcd(48, 18);   /* Expected: 6 */
    unsigned int r2 = gcd(100, 75);  /* Expected: 25 */
    unsigned int r3 = gcd(17, 13);   /* Expected: 1 */

    uart_putword(r1);
    uart_putword(r2);
    uart_putword(r3);

    return r1 + r2 + r3;  /* 6+25+1 = 32 */
}

/* ---------- Main ---------- */

int main(void) {
    unsigned int pass = 1;
    unsigned int result;

    /* Test suite start marker */
    uart_putword(0xDEAD0001);

    /* Test 1: Fibonacci */
    uart_putword(0xAAAA0001);
    result = test_fibonacci();
    pass &= (result == 34);

    /* Test 2: Array sum */
    uart_putword(0xAAAA0002);
    result = test_array_sum();
    pass &= (result == 360);

    /* Test 3: Bubble sort */
    uart_putword(0xAAAA0003);
    result = test_sort();

    /* Test 4: GCD */
    uart_putword(0xAAAA0004);
    result = test_gcd();
    pass &= (result == 32);

    /* Final result marker */
    if (pass) {
        uart_putword(0xCAFE0000);  /* ALL TESTS PASSED */
    } else {
        uart_putword(0xDEADDEAD);  /* SOME TESTS FAILED */
    }

    return pass ? 0 : 1;
}
