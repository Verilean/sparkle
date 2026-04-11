/* ============================================================================
 * Bare-metal RV32I Test Firmware
 *
 * Runs on the Sparkle-generated RV32I SoC.
 * Outputs results via UART (0x10000000) as raw 32-bit words.
 * The Verilog testbench monitors UART writes to verify correctness.
 * ============================================================================ */

#define UART_TX     (*(volatile unsigned int *)0x10000000)

/* ---------- Minimal UART output ---------- */

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

    /* Expected sequence: 0,1,1,2,3,5,8,13,21,34 */
    return last;  /* fib(9) = 34 */
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
    /* Subtraction-based Euclid — no division needed (RV32I has no M ext) */
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

/* ---------- Test 5: CSR Read/Write ---------- */

static unsigned int test_csr(void) {
    unsigned int val;
    unsigned int pass = 1;

    /* Write mtvec, read back */
    asm volatile("csrw mtvec, %0" :: "r"(0x100));
    asm volatile("csrr %0, mtvec" : "=r"(val));
    if (val != 0x100) pass = 0;

    /* Test CSRRSI (immediate variant) — set MIE bit (bit 3) */
    asm volatile("csrsi mstatus, 0x8");
    asm volatile("csrr %0, mstatus" : "=r"(val));
    if (!(val & 0x8)) pass = 0;

    /* Clear MIE bit back */
    asm volatile("csrci mstatus, 0x8");

    /* Test read-only CSR (mhartid should be 0) */
    asm volatile("csrr %0, mhartid" : "=r"(val));
    if (val != 0) pass = 0;

    /* Always restore mtvec to trap handler (even on failure) */
    extern void _trap_handler(void);
    asm volatile("csrw mtvec, %0" :: "r"(&_trap_handler));

    return pass;
}

/* ---------- Test 6: ECALL Trap Entry/Return ---------- */

extern volatile unsigned int _trap_cause;

static unsigned int test_ecall(void) {
    _trap_cause = 0xFFFFFFFF;
    asm volatile("ecall");
    /* After MRET, execution should continue here */
    /* _trap_cause should be 11 (ECALL from M-mode) */
    return (_trap_cause == 11) ? 1 : 0;
}

/* ---------- Test 7: Timer Interrupt ---------- */

#define CLINT_MTIMECMP_LO  (*(volatile unsigned int *)0x02004000)
#define CLINT_MTIMECMP_HI  (*(volatile unsigned int *)0x02004004)
#define CLINT_MTIME_LO     (*(volatile unsigned int *)0x0200BFF8)

static unsigned int test_timer(void) {
    /* Set mtimecmp to current mtime + small delta */
    unsigned int now = CLINT_MTIME_LO;
    CLINT_MTIMECMP_HI = 0;
    CLINT_MTIMECMP_LO = now + 100;

    /* Enable timer interrupt: mie.MTIE (bit 7) */
    asm volatile("csrs mie, %0" :: "r"(1 << 7));
    /* Enable global interrupts: mstatus.MIE (bit 3) */
    asm volatile("csrsi mstatus, 0x8");

    /* Wait for interrupt */
    for (volatile int i = 0; i < 200; i++) {}

    /* Disable interrupts */
    asm volatile("csrci mstatus, 0x8");

    /* Check if timer interrupt was taken (mcause = 0x80000007) */
    return (_trap_cause == 0x80000007) ? 1 : 0;
}

/* ---------- Test 8: M-extension (MUL/DIV/REM) ---------- */

static unsigned int test_mext(void) {
    unsigned int pass = 1;

    /* MUL: 7 * 13 = 91 */
    unsigned int mul_r = 7u * 13u;
    uart_putword(mul_r);           /* Expected: 91 = 0x5B */
    pass &= (mul_r == 91);

    /* MUL signed: -3 * 5 = -15 */
    int smul_r = (-3) * 5;
    uart_putword((unsigned int)smul_r);  /* Expected: 0xFFFFFFF1 (-15) */
    pass &= (smul_r == -15);

    /* DIV: 100 / 7 = 14 */
    unsigned int div_r = 100u / 7u;
    uart_putword(div_r);           /* Expected: 14 = 0x0E */
    pass &= (div_r == 14);

    /* DIV signed: -100 / 7 = -14 (truncated toward zero) */
    int sdiv_r = (-100) / 7;
    uart_putword((unsigned int)sdiv_r);  /* Expected: 0xFFFFFFF2 (-14) */
    pass &= (sdiv_r == -14);

    /* REM: 100 % 7 = 2 */
    unsigned int rem_r = 100u % 7u;
    uart_putword(rem_r);           /* Expected: 2 */
    pass &= (rem_r == 2);

    /* REM signed: -100 % 7 = -2 */
    int srem_r = (-100) % 7;
    uart_putword((unsigned int)srem_r);  /* Expected: 0xFFFFFFFE (-2) */
    pass &= (srem_r == -2);

    return pass;
}

/* ---------- Test 9: BitNet MMIO ---------- */

#define AI_STATUS  (*(volatile unsigned int *)0x40000000)
#define AI_INPUT   (*(volatile unsigned int *)0x40000004)
#define AI_OUTPUT  (*(volatile unsigned int *)0x40000008)

static unsigned int test_bitnet_mmio(void) {
    AI_STATUS = 1;
    unsigned int status = AI_STATUS;
    uart_putword(status);           /* Expected: 1 */
    if (status != 1) return 0;

    unsigned int output = AI_OUTPUT;
    uart_putword(output);           /* Expected: 0 (bitNetPeripheral(0) = 0) */
    if (output != 0) return 0;

    return 1;
}

/* ---------- Test 10: A-extension (Atomics) ---------- */

static unsigned int test_atomics(void) {
    volatile unsigned int shared = 100;
    unsigned int old;

    /* LR.W / SC.W: load-reserved, store-conditional */
    asm volatile(
        "lr.w %0, (%1)\n"
        : "=r"(old) : "r"(&shared) : "memory"
    );
    uart_putword(old);  /* Expected: 100 = 0x64 */
    if (old != 100) return 0;

    unsigned int sc_result;
    asm volatile(
        "sc.w %0, %1, (%2)\n"
        : "=r"(sc_result) : "r"(200u), "r"(&shared) : "memory"
    );
    uart_putword(sc_result);  /* Expected: 0 (success) */
    if (sc_result != 0) return 0;
    uart_putword(shared);     /* Expected: 200 = 0xC8 */
    if (shared != 200) return 0;

    /* AMOSWAP: swap value atomically */
    asm volatile(
        "amoswap.w %0, %1, (%2)\n"
        : "=r"(old) : "r"(999u), "r"(&shared) : "memory"
    );
    uart_putword(old);     /* Expected: 200 = 0xC8 (old value) */
    if (old != 200) return 0;
    uart_putword(shared);  /* Expected: 999 = 0x3E7 */
    if (shared != 999) return 0;

    /* AMOADD: atomic add */
    asm volatile(
        "amoadd.w %0, %1, (%2)\n"
        : "=r"(old) : "r"(1u), "r"(&shared) : "memory"
    );
    uart_putword(old);     /* Expected: 999 = 0x3E7 (old value) */
    if (old != 999) return 0;
    uart_putword(shared);  /* Expected: 1000 = 0x3E8 */
    if (shared != 1000) return 0;

    return 1;
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

    /* Test 5: M-extension */
    uart_putword(0xAAAA0005);
    result = test_mext();
    pass &= result;

    /* Test 6: BitNet MMIO */
    uart_putword(0xAAAA0006);
    result = test_bitnet_mmio();
    pass &= result;

    /* Test 7: A-extension (Atomics) — moved before trap tests */
    uart_putword(0xAAAA0007);
    result = test_atomics();
    pass &= result;

    /* Test 8: CSR Read/Write */
    uart_putword(0xAAAA0008);
    result = test_csr();
    pass &= result;

    /* Test 9: ECALL Trap */
    uart_putword(0xAAAA0009);
    result = test_ecall();
    pass &= result;

    /* Test 10: Timer Interrupt */
    uart_putword(0xAAAA000A);
    result = test_timer();
    pass &= result;

    /* Final result marker */
    if (pass) {
        uart_putword(0xCAFE0000);  /* ALL TESTS PASSED */
    } else {
        uart_putword(0xDEADDEAD);  /* SOME TESTS FAILED */
    }

    return pass ? 0 : 1;
}
