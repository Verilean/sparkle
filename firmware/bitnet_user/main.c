/*
 * BitNet v1a Linux userspace smoke test.
 *
 * This binary runs as PID 1 (/init) inside the kernel's initramfs and
 * exercises the sparkle-bitnet driver against the same 8 golden vectors
 * used by Tests/Integration/BitNetSoCTest.lean. On success it writes
 * "BITNET PASS\n" to stdout (UART via /dev/console); on any mismatch it
 * writes "BITNET FAIL: ...\n" and halts.
 *
 * The binary is freestanding — the rv32 Linux cross-toolchain has no
 * rv32 multilib in the nix shell, so we use the bare-metal
 * `riscv32-none-elf-gcc` plus inline `ecall` Linux syscalls. This is
 * fine because we need only:
 *   open(2), read(2), write(2), close(2), exit_group(2), reboot(2)
 *
 * Linux-on-RV32 syscall numbers are the architecture-independent set
 * defined in include/uapi/asm-generic/unistd.h.
 */

#define SYS_close       57
#define SYS_openat      56
#define SYS_read        63
#define SYS_write       64
#define SYS_exit_group  94
#define SYS_reboot      142

#define O_RDWR          02
#define AT_FDCWD        (-100)

#define LINUX_REBOOT_MAGIC1   0xfee1deadu
#define LINUX_REBOOT_MAGIC2   672274793u
#define LINUX_REBOOT_CMD_HALT 0xcdef0123u

typedef unsigned int   uint32_t;
typedef int            int32_t;
typedef unsigned long  size_t;
typedef long           ssize_t;

static inline long syscall1(long n, long x0) {
    register long a7 __asm__("a7") = n;
    register long a0 __asm__("a0") = x0;
    __asm__ volatile ("ecall" : "+r"(a0) : "r"(a7) : "memory");
    return a0;
}

static inline long syscall3(long n, long x0, long x1, long x2) {
    register long a7 __asm__("a7") = n;
    register long a0 __asm__("a0") = x0;
    register long a1 __asm__("a1") = x1;
    register long a2 __asm__("a2") = x2;
    __asm__ volatile ("ecall" : "+r"(a0) : "r"(a7), "r"(a1), "r"(a2) : "memory");
    return a0;
}

static inline long syscall4(long n, long x0, long x1, long x2, long x3) {
    register long a7 __asm__("a7") = n;
    register long a0 __asm__("a0") = x0;
    register long a1 __asm__("a1") = x1;
    register long a2 __asm__("a2") = x2;
    register long a3 __asm__("a3") = x3;
    __asm__ volatile ("ecall" : "+r"(a0)
                              : "r"(a7), "r"(a1), "r"(a2), "r"(a3)
                              : "memory");
    return a0;
}

static int sys_openat(int dirfd, const char *path, int flags) {
    return (int)syscall4(SYS_openat, dirfd, (long)path, flags, 0);
}
static ssize_t sys_write(int fd, const void *buf, size_t n) {
    return syscall3(SYS_write, fd, (long)buf, n);
}
static ssize_t sys_read(int fd, void *buf, size_t n) {
    return syscall3(SYS_read, fd, (long)buf, n);
}
static int sys_close(int fd) {
    return (int)syscall1(SYS_close, fd);
}
static void sys_exit_group(int code) __attribute__((noreturn));
static void sys_exit_group(int code) {
    syscall1(SYS_exit_group, code);
    for (;;) { /* unreachable */ }
}

static size_t cstr_len(const char *s) {
    size_t n = 0;
    while (s[n]) n++;
    return n;
}

static void puts_raw(const char *s) {
    /* fd 1 = stdout. The kernel hooks /dev/console to UART. */
    sys_write(1, s, cstr_len(s));
}

/* Golden vectors copied verbatim from Tests/Integration/BitNetSoCTest.lean
 * lines 43-51. The Q16.16 input → expected output mapping.
 *
 * NOTE: this is the FULL FFN pipeline output (BitLinear→Scale→ReLU²→
 * ElemMul→BitLinear→Scale→Residual), not the "4*input" linear identity
 * suggested by the older bitnet_smoke firmware. See the BitNetSoCTest
 * comment block for why these 8 specific values are the source of truth.
 */
static const uint32_t cases[][2] = {
    {0x00010000u, 0x00410000u},
    {0x00020000u, 0x02020000u},
    {0x00030000u, 0x06C30000u},
    {0x00040000u, 0x10040000u},
    {0x00080000u, 0x80080000u},
    {0x00000100u, 0x00000100u},
    {0x12345678u, 0x5AD1BC9Au},
    {0x00000000u, 0x00000000u},
};
#define N_CASES (sizeof(cases) / sizeof(cases[0]))

static void hex8(uint32_t v, char out[9]) {
    static const char d[] = "0123456789abcdef";
    for (int i = 7; i >= 0; i--) {
        out[i] = d[v & 0xF];
        v >>= 4;
    }
    out[8] = 0;
}

void _start(void) __attribute__((noreturn));
void _start(void) {
    puts_raw("BITNET TEST: opening /dev/bitnet0\n");

    int fd = sys_openat(AT_FDCWD, "/dev/bitnet0", O_RDWR);
    if (fd < 0) {
        puts_raw("BITNET FAIL: open /dev/bitnet0\n");
        sys_exit_group(1);
    }

    int ok = 1;
    for (size_t i = 0; i < N_CASES; i++) {
        uint32_t in   = cases[i][0];
        uint32_t want = cases[i][1];
        if (sys_write(fd, &in, 4) != 4) {
            puts_raw("BITNET FAIL: write\n");
            ok = 0; break;
        }
        uint32_t got = 0;
        if (sys_read(fd, &got, 4) != 4) {
            puts_raw("BITNET FAIL: read\n");
            ok = 0; break;
        }
        char buf[64];
        char *p = buf;
        for (const char *s = "  in=0x"; *s; s++) *p++ = *s;
        char hx[9]; hex8(in, hx); for (int k = 0; k < 8; k++) *p++ = hx[k];
        for (const char *s = " out=0x"; *s; s++) *p++ = *s;
        hex8(got, hx); for (int k = 0; k < 8; k++) *p++ = hx[k];
        for (const char *s = " want=0x"; *s; s++) *p++ = *s;
        hex8(want, hx); for (int k = 0; k < 8; k++) *p++ = hx[k];
        *p++ = '\n'; *p = 0;
        puts_raw(buf);
        if (got != want) ok = 0;
    }
    sys_close(fd);

    puts_raw(ok ? "BITNET PASS\n" : "BITNET FAIL: mismatch\n");

    /* As PID 1, returning would panic the kernel ("Attempted to kill init!").
     * Halt cleanly so the test harness can scrape UART without races. */
    syscall4(SYS_reboot, (long)LINUX_REBOOT_MAGIC1,
             (long)LINUX_REBOOT_MAGIC2,
             (long)LINUX_REBOOT_CMD_HALT, 0);

    /* Reboot returned (shouldn't happen as PID 1) — spin so we keep
     * holding the CPU and the harness can capture the marker. */
    for (;;) { __asm__ volatile ("wfi"); }
}
