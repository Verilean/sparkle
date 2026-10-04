#!/usr/bin/env python3
"""
Sign a real EIP-1559 Ethereum transaction with the Sparkle secp256k1 signer
(baked key d=12345, on-chip RFC-6979 nonce) and broadcast it to a local node.

The device signs the 32-byte tx hash z and returns r‖s.  This host tool builds
the tx, gets (r,s) either from the FPGA over UART or from a byte-identical
pure-Python RFC-6979 reference (--ref), normalizes to low-s (EIP-2), recovers the
y-parity, assembles the signed raw tx, broadcasts it, and confirms the transfer.

  ./eth_sign_tx.py --ref                      # sign with the reference (no board)
  ./eth_sign_tx.py --rs <r_hex> <s_hex>       # sign with an FPGA-produced r,s
"""
import argparse, hmac, hashlib, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "policy_signer"))
sys.path.insert(0, os.path.dirname(__file__))
from sign_tx import (eip1559_preimage, eip1559_signed, keccak256, rpc,
                     eth_address, _ecrecover_addr)
from sign_z import N, GX, GY, pt_mul, inv_mod, derive_pubkey

DEMO_KEY = 12345

def rfc6979_k(x, z, n, qlen=256):
    """Device-matching RFC-6979 (SHA-256, secp256k1). z is the 256-bit hash."""
    def bits2int(b):
        i = int.from_bytes(b, 'big'); blen = len(b) * 8
        return i >> (blen - qlen) if blen > qlen else i
    def int2octets(v): return v.to_bytes(32, 'big')
    def bits2octets(b):
        z1 = bits2int(b); z2 = z1 - n
        return int2octets(z2 if z2 >= 0 else z1)
    h1 = z.to_bytes(32, 'big'); xo = int2octets(x); ho = bits2octets(h1)
    V = b'\x01' * 32; K = b'\x00' * 32
    K = hmac.new(K, V + b'\x00' + xo + ho, hashlib.sha256).digest(); V = hmac.new(K, V, hashlib.sha256).digest()
    K = hmac.new(K, V + b'\x01' + xo + ho, hashlib.sha256).digest(); V = hmac.new(K, V, hashlib.sha256).digest()
    while True:
        T = b''
        while len(T) * 8 < qlen:
            V = hmac.new(K, V, hashlib.sha256).digest(); T += V
        k = bits2int(T)
        if 1 <= k < n: return k
        K = hmac.new(K, V + b'\x00', hashlib.sha256).digest(); V = hmac.new(K, V, hashlib.sha256).digest()

def ref_sign(d, z):
    k = rfc6979_k(d, z, N)
    R = pt_mul(k, (GX, GY)); r = R[0] % N
    s = inv_mod(k, N) * ((z + r * d) % N) % N
    return r, s

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rpc", default="http://localhost:8545")
    ap.add_argument("--ref", action="store_true", help="sign with pure-Python RFC-6979 (byte-identical to the FPGA)")
    ap.add_argument("--rs", nargs=2, metavar=("R","S"), help="use an FPGA-produced r,s (hex)")
    ap.add_argument("--port", help="sign on the FPGA over this UART port (e.g. /dev/ttyUSB1)")
    ap.add_argument("--to", default="0x70997970C51812dc3A010C7d01b50e0d17dc79C8")
    ap.add_argument("--value", default=str(10**18), help="wei")
    ap.add_argument("--chain-id", type=int, default=31337)
    a = ap.parse_args()

    d = DEMO_KEY
    frm = eth_address(derive_pubkey(d))
    to = int(a.to, 16); value = int(a.value)
    max_prio, max_fee, gas = 10**9, 2*10**9, 21000
    nonce = int(rpc(a.rpc, "eth_getTransactionCount", [f"0x{frm:040x}", "latest"]), 16)
    pre = eip1559_preimage(a.chain_id, nonce, max_prio, max_fee, gas, to, value)
    z = int.from_bytes(keccak256(pre), "big")
    print(f"from   0x{frm:040x}")
    print(f"to     0x{to:040x}   value {value/1e18} ETH   nonce {nonce}")
    print(f"z      {hex(z)}")

    if a.port:
        from sign_z import sign_on_device
        print(f"signing on FPGA over {a.port} …")
        r, s = sign_on_device(a.port, z)
        print("signature: from the FPGA (over UART)")
    elif a.rs:
        r, s = int(a.rs[0], 16), int(a.rs[1], 16)
        print("signature: from FPGA r,s")
    else:
        r, s = ref_sign(d, z)
        print("signature: pure-Python RFC-6979 (byte-identical to FPGA)")
    print(f"r      {hex(r)}")
    print(f"s      {hex(s)}")

    # EIP-2 low-s: if s > n/2, s = n-s and flip parity.
    want = eth_address(derive_pubkey(d))
    def parity_for(r, s):
        for yp in (0, 1):
            if _ecrecover_addr(z, r, s, yp) == want:
                return yp
        return None
    if s > N // 2:
        yp0 = parity_for(r, s); s = N - s
        y_parity = 1 - yp0 if yp0 is not None else parity_for(r, s)
        print("  (normalized to low-s)")
    else:
        y_parity = parity_for(r, s)
    assert y_parity is not None, "could not recover signer — bad signature"
    assert _ecrecover_addr(z, r, s, y_parity) == want, "ecrecover != signer address"
    print(f"y_parity {y_parity}   (ecrecover -> 0x{want:040x} ✓)")

    raw = eip1559_signed(a.chain_id, nonce, max_prio, max_fee, gas, to, value, y_parity, r, s)
    raw_hex = "0x" + raw.hex()
    bal_before = int(rpc(a.rpc, "eth_getBalance", [f"0x{to:040x}", "latest"]), 16)
    txh = rpc(a.rpc, "eth_sendRawTransaction", [raw_hex])
    print(f"broadcast tx {txh}")
    import time
    receipt = None
    for _ in range(50):
        receipt = rpc(a.rpc, "eth_getTransactionReceipt", [txh])
        if receipt: break
        time.sleep(0.1)
    status = receipt and receipt.get("status")
    bal_after = int(rpc(a.rpc, "eth_getBalance", [f"0x{to:040x}", "latest"]), 16)
    print(f"receipt status {status}  (0x1 = success)")
    print(f"recipient balance {bal_before/1e18:.4f} -> {bal_after/1e18:.4f} ETH  (+{(bal_after-bal_before)/1e18})")
    return 0 if status == "0x1" else 1

if __name__ == "__main__":
    sys.exit(main())
