#!/usr/bin/env python3
"""
Host driver for the Sparkle k-on-chip secp256k1 signer on the Tang Nano 20k
(IP/Crypto/EcdsaSignSmall.lean via signZDemo, fpga/tangNano20k/sign_z_demo_top.v).

Protocol: host sends 32 bytes z (big-endian); the device derives the nonce k on
its own die via RFC-6979 with the BAKED key d = 12345 and replies 64 bytes r‖s.
Nothing secret ever crosses the wire — d is baked, k never leaves the chip.

Dependency-free: pure-Python secp256k1 verify + a raw-termios serial port, so it
runs on stock Python 3 with no `pip install`.

  ./sign_z.py --selftest                 # no hardware; pure-Python sanity
  ./sign_z.py --port /dev/ttyUSB1        # sign z=123456789 on the board, verify
  ./sign_z.py --port /dev/ttyUSB1 --z 9  # sign an arbitrary z
"""
import argparse, os, sys, time

# --- secp256k1 (pure Python) — matches IP/Crypto/Secp256k1ECDSA -------------
P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
DEMO_KEY = 12345          # the key baked into the bitstream

def inv_mod(a, m): return pow(a % m, m - 2, m)

def pt_add(p1, p2):
    if p1 is None: return p2
    if p2 is None: return p1
    x1, y1 = p1; x2, y2 = p2
    if x1 == x2 and (y1 + y2) % P == 0: return None
    lam = (3*x1*x1) * inv_mod(2*y1, P) % P if p1 == p2 else (y2-y1) * inv_mod(x2-x1, P) % P
    x3 = (lam*lam - x1 - x2) % P
    return (x3, (lam*(x1-x3) - y1) % P)

def pt_mul(k, pt):
    r = None
    while k:
        if k & 1: r = pt_add(r, pt)
        pt = pt_add(pt, pt); k >>= 1
    return r

def ecdsa_verify(Q, z, r, s):
    if not (0 < r < N and 0 < s < N): return False
    w = inv_mod(s, N)
    X = pt_add(pt_mul(z*w % N, (GX, GY)), pt_mul(r*w % N, Q))
    return X is not None and X[0] % N == r

def derive_pubkey(d): return pt_mul(d, (GX, GY))

# --- raw serial (no pyserial): 115200 8N1 via termios -----------------------
def open_port(path, baud=115200, read_timeout_ds=100):
    import termios
    fd = os.open(path, os.O_RDWR | os.O_NOCTTY)
    attrs = termios.tcgetattr(fd)
    iflag, oflag, cflag, lflag, ispeed, ospeed, cc = attrs
    spd = getattr(termios, f"B{baud}")
    cflag = (cflag | termios.CLOCAL | termios.CREAD) & ~termios.CSIZE
    cflag |= termios.CS8
    cflag &= ~(termios.PARENB | termios.CSTOPB | termios.CRTSCTS)
    iflag &= ~(termios.IXON | termios.IXOFF | termios.IXANY | termios.INLCR |
               termios.ICRNL | termios.IGNCR | termios.ISTRIP | termios.INPCK | termios.BRKINT)
    oflag &= ~termios.OPOST
    lflag &= ~(termios.ICANON | termios.ECHO | termios.ECHOE | termios.ISIG | termios.IEXTEN)
    cc = list(cc); cc[termios.VMIN] = 0; cc[termios.VTIME] = read_timeout_ds  # deciseconds
    termios.tcsetattr(fd, termios.TCSANOW, [iflag, oflag, cflag, lflag, spd, spd, cc])
    # Enable the host→FPGA direction: the Tang Nano 20k's on-board BL616 UART
    # bridge only forwards host→FPGA (FPGA RX, pin 70) after DTR/RTS are PULSED
    # through several transitions (a static level isn't enough).  Without this
    # the device receives nothing and never replies.
    import fcntl, array
    TIOCMGET, TIOCMSET, DTR, RTS = 0x5415, 0x5418, 0x002, 0x004
    def setlines(dtr, rts):
        b = array.array('i', [0]); fcntl.ioctl(fd, TIOCMGET, b, True)
        v = b[0]; v = (v | DTR) if dtr else (v & ~DTR); v = (v | RTS) if rts else (v & ~RTS)
        fcntl.ioctl(fd, TIOCMSET, array.array('i', [v]))
    for d, r in [(1, 1), (0, 0), (1, 0), (0, 1), (1, 1)]:
        setlines(d, r); time.sleep(0.03)
    time.sleep(0.1)
    termios.tcflush(fd, termios.TCIOFLUSH)
    return fd

def read_exact(fd, n, tries=200):
    buf = b""
    while len(buf) < n and tries > 0:
        chunk = os.read(fd, n - len(buf))
        if chunk: buf += chunk
        else: tries -= 1
    return buf

def _pulse_lines(fd):
    """Pulse DTR/RTS through transitions to (re-)enable host→FPGA on the BL616."""
    import fcntl, array
    TIOCMGET, TIOCMSET, DTR, RTS = 0x5415, 0x5418, 0x002, 0x004
    for d, r in [(1, 1), (0, 0), (1, 0), (0, 1), (1, 1)]:
        b = array.array('i', [0]); fcntl.ioctl(fd, TIOCMGET, b, True)
        v = b[0]; v = (v | DTR) if d else (v & ~DTR); v = (v | RTS) if r else (v & ~RTS)
        fcntl.ioctl(fd, TIOCMSET, array.array('i', [v])); time.sleep(0.02)
    time.sleep(0.08)

SYNC = b"\xA5\x5A"          # response frame marker
ST_OK = 0x01               # status byte: signature ready

def _parse_frame(buf, z, Q):
    """Find a [A5 5A][status][r 32B][s 32B] frame in buf whose r,s verify."""
    i = 0
    while True:
        j = buf.find(SYNC, i)
        if j < 0 or j + 2 + 1 + 64 > len(buf):
            return None
        status = buf[j + 2]
        r = int.from_bytes(buf[j+3:j+35], "big")
        s = int.from_bytes(buf[j+35:j+67], "big")
        if status == ST_OK and ecdsa_verify(Q, z, r, s):
            return r, s
        i = j + 1          # false marker inside data — resync past it

def sign_on_device(port, z, attempts=12):
    """Send z, read back the framed response [A5 5A][status][r][s].  The BL616 FTDI
    channel won't read while a write is in flight, so each attempt writes z on a
    SEPARATE fd (pulse DTR/RTS to enable host→FPGA, send 32-byte z, close), then
    reads the repeated response frame on a FRESH fd and parses on the A5 5A marker.
    Retries because the bridge host→FPGA enable is flaky."""
    import termios
    os.system(f"stty -F {port} 115200 raw -echo 2>/dev/null")
    Q = derive_pubkey(DEMO_KEY)
    for _ in range(attempts):
        fw = os.open(port, os.O_RDWR | os.O_NONBLOCK)
        _pulse_lines(fw)
        termios.tcflush(fw, termios.TCIOFLUSH)
        os.write(fw, z.to_bytes(32, "big"))
        time.sleep(0.5)                 # on-chip sign completes, frames start
        os.close(fw)                    # release the write side before reading
        fr = os.open(port, os.O_RDONLY | os.O_NONBLOCK)
        try:
            buf = b""; t0 = time.time()
            while time.time() - t0 < 1.2 and len(buf) < 512:
                try:
                    chunk = os.read(fr, 256)
                except BlockingIOError:
                    chunk = b""
                if chunk:
                    buf += chunk
                    got = _parse_frame(buf, z, Q)
                    if got: return got
                else:
                    time.sleep(0.002)
        finally:
            os.close(fr)
    raise IOError("no valid response frame from the device (all attempts)")

# --- entry points -----------------------------------------------------------
def selftest():
    # A device-independent sanity: sign z with a known k in pure Python, verify.
    d, k, z = DEMO_KEY, 0x1234567890ABCDEF1234567890ABCDEF, 123456789
    R = pt_mul(k, (GX, GY)); r = R[0] % N
    s = inv_mod(k, N) * ((z + r*d) % N) % N
    Q = derive_pubkey(d)
    ok = ecdsa_verify(Q, z, r, s)
    print(f"pubkey Q.x = 0x{Q[0]:064x}")
    print(f"sample r   = 0x{r:064x}")
    print("selftest:", "OK" if ok else "FAIL")
    return 0 if ok else 1

def run(port, z):
    print(f"→ sending z = {z} (0x{z:064x}) to {port}")
    r, s = sign_on_device(port, z)
    Q = derive_pubkey(DEMO_KEY)
    good = ecdsa_verify(Q, z, r, s)
    print(f"← r = 0x{r:064x}")
    print(f"← s = 0x{s:064x}")
    print(f"signature verifies against Q = {DEMO_KEY}·G : {'YES ✓' if good else 'NO ✗'}")
    return 0 if good else 1

def main():
    ap = argparse.ArgumentParser(description="Drive the Sparkle k-on-chip secp256k1 signer.")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--port", help="serial port, e.g. /dev/ttyUSB1")
    ap.add_argument("--z", default="123456789", help="hash z (decimal or 0x-hex)")
    a = ap.parse_args()
    if a.selftest: return selftest()
    if not a.port: ap.error("need --port (or --selftest)")
    z = int(a.z, 0)
    return run(a.port, z)

if __name__ == "__main__":
    sys.exit(main())
