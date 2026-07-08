/-
  IP.Crypto.Rfc6979HW — deterministic ECDSA nonce (RFC 6979) for secp256k1 +
  SHA-256, driving the shared HMAC-SHA256 core.  The private key `d` is a
  compile-time constant (baked into the bitstream), which makes every HMAC
  message block either `V ‖ const` or `dLo8 ‖ zmodn ‖ const` — no runtime bit
  slicing.  Golden model: `IP/Crypto/Rfc6979.rfc6979`.

  Sequence (RFC 6979 §3.2, qlen = 256):
    K = HMAC(K, V‖00‖dz) ; V = HMAC(K, V)
    K = HMAC(K, V‖01‖dz) ; V = HMAC(K, V)
    loop: V = HMAC(K, V) ; if 1≤V<n return V
          else K = HMAC(K, V‖00) ; V = HMAC(K, V)
-/
import Sparkle
import IP.Crypto.HMACSHA256HW
import IP.Crypto.Proof.Secp256k1ECDSA

namespace Sparkle.IP.Crypto.Rfc6979HW

open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.HMACSHA256HW (hmacSha256 HmacOut pad256)

/-- Curve order n as a 256-bit constant. -/
def nBv : BitVec 256 := BitVec.ofNat 256 Sparkle.IP.Crypto.Secp256k1ECDSA.n

/-- `@[hardware_module]` wrapper so the FSM can project the HMAC outputs. -/
@[hardware_module] def wHmac {dom : DomainConfig}
    (start : Signal dom Bool) (key : Signal dom (BitVec 256))
    (blk1 blk2 : Signal dom (BitVec 512)) (threeBlk : Signal dom Bool) : HmacOut dom :=
  hmacSha256 start key blk1 blk2 threeBlk

structure NonceOut (dom : DomainConfig) where
  k    : Signal dom (BitVec 256)
  done : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (NonceOut dom) dom := ⟨⟩

/-- RFC 6979 deterministic nonce `k` for hash `z`, with baked key `dKey`. -/
def rfc6979HW {dom : DomainConfig}
    (dKey : BitVec 256) (start : Signal dom Bool) (z : Signal dom (BitVec 256)) :
    NonceOut dom :=
  -- Constants derived from the baked key at elaboration (computed OUTSIDE the
  -- `circuit do` — a Nat `let` inside it confuses hardware-type inference).
  let dN := dKey.toNat
  let dHi248 := (dN >>> 8) &&& ((1 <<< 248) - 1)   -- d bytes 0..30 (high 248 bits)
  let dLo8   := dN &&& 0xFF                         -- d byte 31 (low 8 bits)
  let tail00 := (BitVec.ofNat 256 dHi248)                     -- V‖00‖dz block1 tail = 0x00‖dHi
  let tail01 := (BitVec.ofNat 256 ((1 <<< 248) ||| dHi248))   -- V‖01‖dz block1 tail = 0x01‖dHi
  let tailV  := (pad256 : BitVec 256)                         -- V (32B): 0x80‖0…‖len768
  let tailV0 := (BitVec.ofNat 256 ((0x80 <<< 240) ||| 776))  -- V‖00 (33B): 0x00‖0x80‖0…‖len776
  let tail1288 := (BitVec.ofNat 248 ((0x80 <<< 240) ||| 1288))  -- blk2 tail: 0x80‖0×22‖len1288
  let dLo8bv := (BitVec.ofNat 8 dLo8)
  circuit do
    -- State: 0 idle · (1,2)A · (3,4)B1 · (5,6)C · (7,8)B2 · (9,10)Bcand · 11 check
    --        12 done · (13,14)D · (15,16)Bretry
    let stR ← Signal.reg (0#5)
    let kR  ← Signal.reg (0#256)
    let vR  ← Signal.reg (0#256)
    let znR ← Signal.reg (0#256)          -- z mod n, latched on start
    let doneR ← Signal.reg false
    let st := (stR : Signal dom (BitVec 5))
    let vSig := (vR : Signal dom (BitVec 256))
    let znSig := (znR : Signal dom (BitVec 256))

    -- z mod n = z - n if z ≥ n else z  (z < 2^256 < 2n).
    let zGe := ((fun z' => BitVec.ule nBv z') <$> z : Signal dom Bool)
    let zmodn := (Signal.mux zGe ((· - ·) <$> z <*> (Signal.pure nBv : Signal dom (BitVec 256))) z : Signal dom (BitVec 256))

    -- HMAC config keyed on the PHASE (issue+wait pair), so it stays stable for
    -- the ~270 cycles the HMAC runs (NOT on the 1-cycle issue state — that would
    -- drop threeBlk/tailC to their defaults mid-run, skipping block2 = zmodn).
    let phaseA := ((· || ·) <$> (st === 1#5) <*> (st === 2#5) : Signal dom Bool)
    let phaseC := ((· || ·) <$> (st === 5#5) <*> (st === 6#5) : Signal dom Bool)
    let phaseD := ((· || ·) <$> (st === 13#5) <*> (st === 14#5) : Signal dom Bool)
    let tailC :=
      (Signal.mux phaseA (Signal.pure tail00)
        (Signal.mux phaseC (Signal.pure tail01)
          (Signal.mux phaseD (Signal.pure tailV0)
            (Signal.pure tailV))) : Signal dom (BitVec 256))
    let blk1 := ((· ++ ·) <$> vSig <*> tailC : Signal dom (BitVec 512))
    let blk2 := ((· ++ ·) <$> ((· ++ ·) <$> (Signal.pure dLo8bv : Signal dom (BitVec 8)) <*> znSig)
                          <*> (Signal.pure tail1288 : Signal dom (BitVec 248)) : Signal dom (BitVec 512))
    let threeBlk := ((· || ·) <$> phaseA <*> phaseC : Signal dom Bool)

    -- issue pulse: the ISSUE states 1,3,5,7,9,13,15 (start each HMAC once).
    let isIssue := ((· || ·) <$>
        ((· || ·) <$> ((· || ·) <$> (st === 1#5) <*> (st === 3#5)) <*> ((· || ·) <$> (st === 5#5) <*> (st === 7#5)))
        <*> ((· || ·) <$> (st === 9#5) <*> ((· || ·) <$> (st === 13#5) <*> (st === 15#5))) : Signal dom Bool)
    let hm := wHmac isIssue (kR : Signal dom (BitVec 256)) blk1 blk2 threeBlk
    let hmDone := hm.done

    -- captures: K after A/C/D ; V after any B.
    let capK := ((· && ·) <$> ((· || ·) <$> ((· || ·) <$> (st === 2#5) <*> (st === 6#5)) <*> (st === 14#5)) <*> hmDone : Signal dom Bool)
    let capV := ((· && ·) <$> ((· || ·) <$> ((· || ·) <$> (st === 4#5) <*> (st === 8#5)) <*> ((· || ·) <$> (st === 10#5) <*> (st === 16#5))) <*> hmDone : Signal dom Bool)
    -- K = 0x00…00 on start, else latch HMAC result on capK.
    kR <~ Signal.mux start (Signal.pure 0#256)
            (Signal.mux capK hm.hmac (kR : Signal dom (BitVec 256)))
    -- V = 0x01…01 on start, else latch HMAC result on capV.
    vR <~ Signal.mux start (Signal.pure (BitVec.ofNat 256 0x0101010101010101010101010101010101010101010101010101010101010101))
            (Signal.mux capV hm.hmac vSig)
    znR <~ Signal.mux start zmodn znSig

    -- candidate validity at state 11: 1 ≤ V < n.  (Use `0 < V` for V≠0 —
    -- `!(V == 0)` in a map-lambda mis-lowers to a wide bitwise `~V`.)
    let vNonzero := ((fun v => BitVec.ult (0#256) v) <$> vSig : Signal dom Bool)
    let vLtN := ((BitVec.ult · ·) <$> vSig <*> (Signal.pure nBv : Signal dom (BitVec 256)) : Signal dom Bool)
    let vValid := ((· && ·) <$> vNonzero <*> vLtN : Signal dom Bool)

    doneR <~ ((· && ·) <$> (st === 11#5) <*> vValid)

    -- next state.
    let inc := ((· + ·) <$> st <*> (Signal.pure 1#5 : Signal dom (BitVec 5)) : Signal dom (BitVec 5))
    let advOnDone := (Signal.mux hmDone inc st : Signal dom (BitVec 5))
    let stNext :=
      Signal.mux (st === 0#5) (Signal.mux start (Signal.pure 1#5 : Signal dom (BitVec 5)) (Signal.pure 0#5))
      -- check state: valid → done(12→idle) ; invalid → retry(13)
      <| Signal.mux (st === 11#5) (Signal.mux vValid (Signal.pure 12#5 : Signal dom (BitVec 5)) (Signal.pure 13#5))
      <| Signal.mux (st === 12#5) (Signal.pure 0#5 : Signal dom (BitVec 5))
      -- retry Bretry-wait (16) → back to candidate (9)
      <| Signal.mux (st === 16#5) (Signal.mux hmDone (Signal.pure 9#5 : Signal dom (BitVec 5)) (Signal.pure 16#5))
        (Signal.mux isIssue inc advOnDone)     -- issue +1 ; other waits advance on done
    stR <~ stNext

    -- force K to 0 on start (before the first HMAC).
    -- Done via a mux that beats the capture (capK is false in idle).
    return ({ k := (vR : Signal dom (BitVec 256)), done := (doneR : Signal dom Bool) } : NonceOut dom)

end Sparkle.IP.Crypto.Rfc6979HW
