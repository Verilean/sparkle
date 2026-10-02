/* Workload for the simulator instruction-count gate and the
 * JIT-vs-Verilator co-simulation (bench/gate/run.sh).
 *
 * The LiteX benchmark used to run with an empty ROM: PicoRV32 fetched
 * 0x00000000, trapped after 18 cycles, and the 10M measured cycles were
 * an idle SoC.  This keeps the CPU, the bus, both RAMs, the timer and
 * the UART busy, and prints a checksum per round so that a simulator
 * that computes anything differently shows it on the serial output.
 *
 * No .data/.bss: every variable lives in registers, on the stack (SRAM)
 * or at a fixed main_ram address, so the image is ROM-only.            */

#define REG(a) (*(volatile unsigned int *)(a))
#define UART_RXTX    REG(0x82001800)
#define UART_TXFULL  REG(0x82001804)
#define TIMER_LOAD   REG(0x82001000)
#define TIMER_RELOAD REG(0x82001004)
#define TIMER_EN     REG(0x82001008)
#define TIMER_UPDATE REG(0x8200100c)
#define TIMER_VALUE  REG(0x82001010)

#define RAM   ((unsigned int  *)0x40000000)
#define RAMB  ((unsigned char *)0x40000000)
#define RAMH  ((unsigned short*)0x40000000)
#define N 64

static void put(unsigned c) { while (UART_TXFULL) ; UART_RXTX = c; }

static void puthex(unsigned v) {
    for (int i = 28; i >= 0; i -= 4) {
        unsigned d = (v >> i) & 15;
        put(d < 10 ? '0' + d : 'a' + d - 10);
    }
}

static unsigned mix(unsigned h, unsigned v) {
    h ^= v;
    h = (h << 5) | (h >> 27);
    return h * 0x9e3779b1u + 0x7f4a7c15u;
}

void main(void) {
    unsigned seed = 0x12345678u, sum = 0;
    TIMER_LOAD = 0; TIMER_RELOAD = 1000; TIMER_EN = 1;
    for (unsigned round = 0;; round++) {
        /* word stores + LCG (mul) */
        for (int i = 0; i < N; i++) {
            seed = seed * 1664525u + 1013904223u;
            RAM[i] = seed ^ (seed >> 13);
        }
        /* insertion sort: loads, stores, data-dependent branches */
        for (int i = 1; i < N; i++) {
            unsigned k = RAM[i]; int j = i - 1;
            while (j >= 0 && RAM[j] > k) { RAM[j + 1] = RAM[j]; j--; }
            RAM[j + 1] = k;
        }
        /* byte and half-word lanes (the byte-enable RAM path) */
        for (int i = 0; i < N; i++) {
            RAMB[4 * N + i] = (unsigned char)(RAM[i] >> ((i & 3) * 8));
            RAMH[4 * N + N / 2 + i] = (unsigned short)(RAM[i] >> ((i & 1) * 16));
        }
        /* divide / remainder / signed shifts */
        for (int i = 0; i < N; i += 4) {
            unsigned a = RAM[i], b = (RAM[i + 1] >> 20) | 1;
            sum = mix(sum, a / b);
            sum = mix(sum, a % b);
            sum = mix(sum, (unsigned)((int)a >> (i & 31)));
            sum = mix(sum, (unsigned)(((int)a) / (int)(b | 3)));
        }
        for (int i = 0; i < 2 * N; i++) sum = mix(sum, RAM[N + i]);
        TIMER_UPDATE = 1;
        sum = mix(sum, TIMER_VALUE);
        puthex(round); put(' '); puthex(sum); put('\n');
    }
}
