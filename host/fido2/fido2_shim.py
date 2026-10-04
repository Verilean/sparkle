#!/usr/bin/env python3
"""
FIDO2 getAssertion host shim for the Sparkle Tang Nano fido2Demo top (M3).

Sends a fixed 133-byte frame (d ‖ authData ‖ clientDataHash ‖ k) to the
FPGA over the CDC-ACM serial port and reads back the 64-byte raw ECDSA
signature r‖s, then DER-encodes and verifies it.

Wire framing is a documented M3 simplification (see README.md); a full
CTAPHID/CBOR bridge to python-fido2's custom transport is future work.
"""
import argparse, struct, hashlib, sys

# NIST P-256 parameters.
P  = 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
N  = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
A  = P - 3
B  = 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
GX = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
GY = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

def inv(a, m): return pow(a, m - 2, m)
def pt_add(p, q):
    if p is None: return q
    if q is None: return p
    (x1,y1),(x2,y2) = p,q
    if x1==x2 and (y1+y2)%P==0: return None
    if p==q: m=(3*x1*x1+A)*inv(2*y1,P)%P
    else:    m=(y2-y1)*inv(x2-x1,P)%P
    x3=(m*m-x1-x2)%P; y3=(m*(x1-x3)-y1)%P
    return (x3,y3)
def pt_mul(k, p):
    r=None
    while k:
        if k&1: r=pt_add(r,p)
        p=pt_add(p,p); k>>=1
    return r

def be(n, w): return n.to_bytes(w, 'big')

def build_frame(d, authData, clientDataHash, k):
    assert len(authData)==37 and len(clientDataHash)==32
    return be(d,32) + authData + clientDataHash + be(k,32)

def der_sig(r, s):
    def enc_int(x):
        b = x.to_bytes((x.bit_length()+7)//8 or 1, 'big')
        if b[0] & 0x80: b = b'\x00' + b
        return b'\x02' + bytes([len(b)]) + b
    inner = enc_int(r) + enc_int(s)
    return b'\x30' + bytes([len(inner)]) + inner

def verify(qx, qy, z, r, s):
    if not (0 < r < N and 0 < s < N): return False
    w=inv(s,N); u1=z*w%N; u2=r*w%N
    pt=pt_add(pt_mul(u1,(GX,GY)), pt_mul(u2,(qx,qy)))
    return pt is not None and pt[0]%N==r

def run(port, d, k, rp_id, client_data_hash):
    rp_hash = hashlib.sha256(rp_id.encode()).digest()
    authData = rp_hash + bytes([0x05]) + struct.pack('>I', 1)   # flags UP+UV, signCount 1
    frame = build_frame(d, authData, client_data_hash, k)
    z = int.from_bytes(hashlib.sha256(authData + client_data_hash).digest(), 'big')
    qx, qy = pt_mul(d, (GX, GY))
    if port:
        import serial
        ser = serial.Serial(port, 115200, timeout=5)
        ser.write(frame)
        rs = ser.read(64)
        if len(rs) != 64: print("timeout / short read", len(rs)); return 1
        r = int.from_bytes(rs[:32], 'big'); s = int.from_bytes(rs[32:], 'big')
        print("HW signature r=%x s=%x" % (r, s))
    else:
        # self-test: compute the reference signature (fixed k) in software.
        kg = pt_mul(k, (GX, GY)); r = kg[0] % N
        s = inv(k, N) * ((z + r*d) % N) % N
        print("SW reference r=%x s=%x" % (r, s))
    ok = verify(qx, qy, z, r, s)
    print("DER:", der_sig(r, s).hex())
    print("verify:", ok)
    return 0 if ok else 1

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", default=None, help="CDC-ACM serial port (omit for --selftest)")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args()
    D = 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
    K = 0x9E56F509196784D963D1C0A401510EE7ADA3DCC5DEE04B154BF61AF1D5A6DECE
    CDH = bytes([0xAB]) * 32
    sys.exit(run(None if args.selftest else args.port, D, K, "example.com", CDH))
