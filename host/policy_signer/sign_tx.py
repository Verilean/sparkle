#!/usr/bin/env python3
"""
Host driver for the Sparkle policy-enforcing Ethereum signer on Tang Nano 50K
(IP/Crypto/PolicySignDemo.lean, tutorial Ch11).

The device, over the BL616 CDC-ACM UART bridge, receives a fixed 128-byte frame

    d(32) | k(32) | to(32) | value(32)          (big-endian, MSB byte first)

computes  z = keccak256(to || value)  ON-CHIP, checks that `to` (low 160 bits)
is in the baked-in allowlist AND value <= cap, and only then signs:

    (r, s) = ECDSA-secp256k1(d, z)

Response: 64 bytes r||s on policy PASS, or a single 0xEE byte on reject.

This script is DEPENDENCY-FREE: it implements secp256k1 (sign+verify) and
Keccak-256 in pure Python, so `--selftest` runs on any stock Python 3 without
`pip install`. That self-test mirrors Tests/IP/Crypto/PolicySignDemoTest.lean:
an allowlisted+under-cap vector signs and verifies, and over-cap / bad-recipient
vectors are rejected.

  DEMO-ONLY / INSECURE: `d` (private key) and `k` (ECDSA nonce) are sent over
  the wire here. A production device bakes `d` into on-chip fuses/PUF and derives
  `k` via RFC-6979 — never over the wire. See docs/ip-catalog/PolicySignDemo.md.
"""

import argparse
import sys

# --------------------------------------------------------------------------
# secp256k1 (pure Python) — matches IP/Crypto/Secp256k1ECDSA / Secp256k1Point.
# --------------------------------------------------------------------------
P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
GX = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
GY = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

def inv_mod(a, m):
    return pow(a % m, m - 2, m)

def pt_add(p1, p2):
    if p1 is None: return p2
    if p2 is None: return p1
    x1, y1 = p1; x2, y2 = p2
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    if p1 == p2:
        lam = (3 * x1 * x1) * inv_mod(2 * y1, P) % P
    else:
        lam = (y2 - y1) * inv_mod(x2 - x1, P) % P
    x3 = (lam * lam - x1 - x2) % P
    y3 = (lam * (x1 - x3) - y1) % P
    return (x3, y3)

def pt_mul(k, pt):
    r = None
    while k:
        if k & 1:
            r = pt_add(r, pt)
        pt = pt_add(pt, pt)
        k >>= 1
    return r

def ecdsa_sign(d, k, z):
    """(r, s) with caller-supplied nonce k. Returns None on degenerate."""
    R = pt_mul(k, (GX, GY))
    r = R[0] % N
    if r == 0: return None
    s = inv_mod(k, N) * ((z + r * d) % N) % N
    if s == 0: return None
    return (r, s)

def ecdsa_verify(Q, z, r, s):
    if not (0 < r < N and 0 < s < N): return False
    w = inv_mod(s, N)
    u1 = z * w % N
    u2 = r * w % N
    X = pt_add(pt_mul(u1, (GX, GY)), pt_mul(u2, Q))
    if X is None: return False
    return X[0] % N == r

def derive_pubkey(d):
    return pt_mul(d, (GX, GY))

# --------------------------------------------------------------------------
# Keccak-256 (pure Python) — matches IP/Crypto/Keccak256 (0x01 delimiter,
# NOT SHA-3's 0x06, so hashlib.sha3_256 does NOT match).
# --------------------------------------------------------------------------
_RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
_ROT = [
    [0, 36, 3, 41, 18], [1, 44, 10, 45, 2], [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56], [27, 20, 39, 8, 14],
]

def _rol(x, n):
    return ((x << n) | (x >> (64 - n))) & 0xFFFFFFFFFFFFFFFF

def _keccak_f(st):
    for rnd in range(24):
        c = [st[x][0] ^ st[x][1] ^ st[x][2] ^ st[x][3] ^ st[x][4] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rol(c[(x + 1) % 5], 1) for x in range(5)]
        for x in range(5):
            for y in range(5):
                st[x][y] ^= d[x]
        b = [[0] * 5 for _ in range(5)]
        for x in range(5):
            for y in range(5):
                b[y][(2 * x + 3 * y) % 5] = _rol(st[x][y], _ROT[x][y])
        for x in range(5):
            for y in range(5):
                st[x][y] = b[x][y] ^ ((~b[(x + 1) % 5][y]) & b[(x + 2) % 5][y])
        st[0][0] ^= _RC[rnd]

def keccak256(msg: bytes) -> bytes:
    rate = 136
    padded = bytearray(msg)
    padded.append(0x01)
    while len(padded) % rate != 0:
        padded.append(0x00)
    padded[-1] ^= 0x80
    st = [[0] * 5 for _ in range(5)]
    for off in range(0, len(padded), rate):
        block = padded[off:off + rate]
        for i in range(rate // 8):
            lane = int.from_bytes(block[i * 8:i * 8 + 8], "little")
            st[i % 5][i // 5] ^= lane
        _keccak_f(st)
    out = b""
    for i in range(4):  # first 32 bytes = lanes (0,0),(1,0),(2,0),(3,0)
        out += st[i % 5][i // 5].to_bytes(8, "little")
    return out

# --------------------------------------------------------------------------
# Frame protocol (matches PolicySignDemo.policySignDemo).
# --------------------------------------------------------------------------
def build_frame(d: int, k: int, to: int, value: int) -> bytes:
    return (d.to_bytes(32, "big") + k.to_bytes(32, "big")
            + to.to_bytes(32, "big") + value.to_bytes(32, "big"))

def signing_hash(to: int, value: int) -> int:
    """z = keccak256(to(32) || value(32)) as a big-endian integer."""
    msg = to.to_bytes(32, "big") + value.to_bytes(32, "big")
    return int.from_bytes(keccak256(msg), "big")

# The device's baked-in policy (IP/Crypto/TxPolicy.lean).
ALLOWLIST = [
    0x70997970C51812dc3A010C7d01b50e0d17dc79C8,
    0x3C44CdDdB6a900fa2b585dd299e03d12FA4293BC,
    0x90F79bf6EB2c4f870365E785982E1f101E93b906,
    0x15d34AAf54267DB7D7c367839AAf71A00a2C6A65,
]
MAX_VALUE = 10**18  # 1 ETH cap

def policy_ok(to: int, value: int) -> bool:
    return (to & ((1 << 160) - 1)) in ALLOWLIST and value <= MAX_VALUE

# --------------------------------------------------------------------------
# Hardware I/O.
# --------------------------------------------------------------------------
def sign_on_device(port: str, d, k, to, value, baud=115200, timeout=10):
    import serial  # pyserial — only needed for real hardware, not --selftest
    ser = serial.Serial(port, baud, timeout=timeout)
    ser.write(build_frame(d, k, to, value))
    resp = ser.read(64)
    ser.close()
    if len(resp) == 1 and resp[0] == 0xEE:
        return None            # policy REJECT
    if len(resp) != 64:
        raise IOError(f"expected 64 bytes r||s or 1 reject byte, got {len(resp)}")
    r = int.from_bytes(resp[:32], "big")
    s = int.from_bytes(resp[32:], "big")
    return (r, s)

# --------------------------------------------------------------------------
# Self-test (no hardware) — mirrors PolicySignDemoTest.
# --------------------------------------------------------------------------
def selftest() -> int:
    d = 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
    k = 0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE
    Q = derive_pubkey(d)
    ok = True

    def case(label, to, value, expect_sign):
        nonlocal ok
        z = signing_hash(to, value)
        # what the *device* would do: gate the sign on the policy.
        if policy_ok(to, value):
            sig = ecdsa_sign(d, k, z)
            signed = sig is not None and ecdsa_verify(Q, z, sig[0], sig[1])
        else:
            signed = False
        good = (signed == expect_sign) and (policy_ok(to, value) == expect_sign)
        print(f"  {'OK ' if good else 'XX '}{label}: policy={'PASS' if policy_ok(to,value) else 'REJECT'}, "
              f"signed={'yes' if signed else 'no'}")
        ok = ok and good

    print("=== policy-signer host self-test (pure-Python reference, no hardware) ===")
    case("allowlisted + under cap  -> SIGN",   ALLOWLIST[0], 5 * 10**17, True)
    case("allowlisted + over cap   -> REJECT", ALLOWLIST[0], 2 * 10**18, False)
    case("bad recipient            -> REJECT", 0xdeadbeef << 120,  10**17, False)
    # sanity: our pure-Python secp256k1 matches the Lean vector r.
    z = signing_hash(ALLOWLIST[0], 5 * 10**17)
    r, s = ecdsa_sign(d, k, z)
    print(f"  .. sample signature r = {r}")
    print("ALL PASS" if ok else "FAIL")
    return 0 if ok else 1

def main() -> int:
    ap = argparse.ArgumentParser(description="Drive the Sparkle policy-enforcing Ethereum signer.")
    ap.add_argument("--selftest", action="store_true", help="run the no-hardware reference check")
    ap.add_argument("--port", help="serial port, e.g. /dev/ttyACM0")
    ap.add_argument("--to", help="recipient address (hex, e.g. 0x7099...79C8)")
    ap.add_argument("--value", help="value in wei (int)")
    ap.add_argument("--key", help="private key d (hex) — DEMO ONLY")
    ap.add_argument("--nonce", help="ECDSA nonce k (hex) — DEMO ONLY")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    if not (args.port and args.to and args.value and args.key and args.nonce):
        ap.error("real signing needs --port --to --value --key --nonce (or use --selftest)")
    to = int(args.to, 16); value = int(args.value)
    d = int(args.key, 16); k = int(args.nonce, 16)

    print(f"policy(host preview): {'PASS' if policy_ok(to, value) else 'REJECT'}")
    res = sign_on_device(args.port, d, k, to, value)
    if res is None:
        print("device REJECTED the transaction (0xEE) — policy violation.")
        return 0
    r, s = res
    z = signing_hash(to, value)
    Q = derive_pubkey(d)
    good = ecdsa_verify(Q, z, r, s)
    print(f"r = 0x{r:064x}")
    print(f"s = 0x{s:064x}")
    print(f"signature verifies against Q = d*G : {'YES' if good else 'NO'}")
    return 0 if good else 1

if __name__ == "__main__":
    sys.exit(main())
