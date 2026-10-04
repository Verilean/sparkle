/-
  IP.Crypto.HMACSHA256HW — HMAC-SHA256 for a 32-byte key and a 32-byte message,
  built on the re-initializable `SHA256.sha256Block` core.

  HMAC(K,m) = SHA256(opad ‖ SHA256(ipad ‖ m)), with a 32-byte K (< block size,
  so no key hashing).  ipad = (K‖0…0) ⊕ 0x36…, opad = (K‖0…0) ⊕ 0x5c….  Both
  inner and outer are exactly 2 padded 512-bit blocks.  Golden model:
  `IP/Crypto/Rfc6979.hmacSha256` on a 32-byte message.
-/
import Sparkle
import IP.Crypto.SHA256

namespace Sparkle.IP.Crypto.HMACSHA256HW

open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IP.Crypto.SHA256 (sha256Block SHA256Out)

/-- 0x36 repeated 32 times. -/
def c36 : BitVec 256 := BitVec.ofNat 256 0x3636363636363636363636363636363636363636363636363636363636363636
/-- 0x5c repeated 32 times. -/
def c5c : BitVec 256 := BitVec.ofNat 256 0x5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c5c
/-- 0x36 repeated 64 times (full ipad constant). -/
def c36_512 : BitVec 512 := (c36 ++ c36)
/-- 0x5c repeated 64 times (full opad constant). -/
def c5c_512 : BitVec 512 := (c5c ++ c5c)
/-- SHA-256 padding tail for a 96-byte total message (one 32-byte data half in
    the 2nd block): 0x80, 23 zero bytes, then the 64-bit length 768 bits. -/
def pad256 : BitVec 256 := BitVec.ofNat 256 0x8000000000000000000000000000000000000000000000000000000000000300

/-- `@[hardware_module]` wrapper so the FSM can project the core's outputs. -/
@[hardware_module] def wSha {dom : DomainConfig}
    (start : Signal dom Bool) (blockIn : Signal dom (BitVec 512))
    (first : Signal dom Bool) : SHA256Out dom :=
  sha256Block start blockIn first

structure HmacOut (dom : DomainConfig) where
  hmac : Signal dom (BitVec 256)
  done : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (HmacOut dom) dom := ⟨⟩

/-- General HMAC-SHA256 with a 32-byte `key` and a message given as ONE or TWO
    already-padded 512-bit inner blocks (`blk1`, `blk2`; `blk2` used iff
    `threeBlk`).  The caller pads the message; this drives the ipad/opad + two
    SHA passes.  Covers all RFC-6979 message lengths (32/33 B → `threeBlk=false`,
    97 B → `threeBlk=true`).  Pulse `start`; `done` pulses with `hmac` valid. -/
def hmacSha256 {dom : DomainConfig}
    (start : Signal dom Bool) (key : Signal dom (BitVec 256))
    (blk1 blk2 : Signal dom (BitVec 512)) (threeBlk : Signal dom Bool) : HmacOut dom :=
  circuit do
    -- 0 idle · 1/2 iB0(ipad) · 3/4 iB1 · 5/6 iB2(opt) · 7/8 oB0(opad) · 9/10 oB1(→hmac)
    let stR ← Signal.reg (0#5)
    let innerR ← Signal.reg (0#256)
    let hmacR ← Signal.reg (0#256)
    let doneR ← Signal.reg false
    let st := (stR : Signal dom (BitVec 5))
    let innerSig := (innerR : Signal dom (BitVec 256))
    let padS := (Signal.pure pad256 : Signal dom (BitVec 256))
    let keyPad := (key ++ (Signal.pure (0#256) : Signal dom (BitVec 256)) : Signal dom (BitVec 512))
    -- ipad/opad as a single 512-bit XOR (not concat-of-256-bit-xor).
    let ipadBlk := (keyPad ^^^ (Signal.pure c36_512 : Signal dom (BitVec 512)) : Signal dom (BitVec 512))
    let opadBlk := (keyPad ^^^ (Signal.pure c5c_512 : Signal dom (BitVec 512)) : Signal dom (BitVec 512))
    let outerBlk := (innerSig ++ padS : Signal dom (BitVec 512))

    let isIssue := ((· || ·) <$> (((st === 1#5) ||| (st === 3#5)) ||| (st === 5#5))
                             <*> ((st === 7#5) ||| (st === 9#5)) : Signal dom Bool)
    let shaFirst := ((st === 1#5) ||| (st === 7#5) : Signal dom Bool)
    let shaBlk :=
      (Signal.mux (st === 1#5) ipadBlk
        (Signal.mux (st === 3#5) blk1
          (Signal.mux (st === 5#5) blk2
            (Signal.mux (st === 7#5) opadBlk outerBlk))) : Signal dom (BitVec 512))

    let sha := wSha isIssue shaBlk shaFirst
    let shaDone := sha.done

    -- capture inner: after iB1 when 2-block, after iB2 when 3-block.
    let capInner2 := (((st === 4#5) &&& (~~~threeBlk)) &&& shaDone : Signal dom Bool)
    let capInner3 := ((st === 6#5) &&& shaDone : Signal dom Bool)
    innerR <~ Signal.mux (capInner2 ||| capInner3) sha.hash innerSig
    hmacR <~ Signal.mux ((st === 10#5) &&& shaDone) sha.hash (hmacR : Signal dom (BitVec 256))
    doneR <~ ((st === 10#5) &&& shaDone)

    -- next state.
    let inc := (st + (Signal.pure 1#5 : Signal dom (BitVec 5)) : Signal dom (BitVec 5))
    -- from iB1-wait(4): →5 if threeBlk else →7 ; from iB2-wait(6): →7.
    let after4 := (Signal.mux threeBlk (Signal.pure 5#5 : Signal dom (BitVec 5)) (Signal.pure 7#5) : Signal dom (BitVec 5))
    let stNext :=
      Signal.mux (st === 0#5) (Signal.mux start (Signal.pure 1#5 : Signal dom (BitVec 5)) (Signal.pure 0#5))
      <| Signal.mux (st === 10#5) (Signal.mux shaDone (Signal.pure 0#5 : Signal dom (BitVec 5)) (Signal.pure 10#5))
      <| Signal.mux (st === 4#5) (Signal.mux shaDone after4 (Signal.pure 4#5))
      <| Signal.mux (st === 6#5) (Signal.mux shaDone (Signal.pure 7#5 : Signal dom (BitVec 5)) (Signal.pure 6#5))
        (Signal.mux isIssue inc (Signal.mux shaDone inc st))   -- issue +1 ; other waits advance on done
    stR <~ stNext

    return ({ hmac := (hmacR : Signal dom (BitVec 256)), done := (doneR : Signal dom Bool) } : HmacOut dom)

end Sparkle.IP.Crypto.HMACSHA256HW
