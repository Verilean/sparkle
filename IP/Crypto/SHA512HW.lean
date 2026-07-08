/-
  IP.Crypto.SHA512HW — Signal-side helpers for SHA-512
  (mirroring the SHA-256 shape in `IP/Crypto/SHA256.lean`).

  Provides the 64-bit versions of every Σ / σ / Ch / Maj
  combinational helper, plus a `kMux` mapping a 7-bit round
  counter to the K[t] constant for t = 0..79.

  Design rationale:
    * The Signal-side helpers are `@[inline] def`s that keep
      the IR elaborator on the SHA-256 fast path but with
      BitVec 64 instead of BitVec 32.  The compiler's
      operator table (SHA-256 §L.1.b) accepts every op used
      here — rotate-right is desugared to `>>>` and `<<<`
      pairs, the same shape that already synthesises for
      SHA-256's `rotr32Sig`.
    * The K-table (80 entries) uses `Sparkle.Core.Lut.kLut!`
      just like SHA-256's kMux — this bypasses the
      "Cannot synthesise Id.run" gap that hits `let mut`-based
      table constructions.
    * A full 80-round SHA-512 iterative compressor
      (`sha512Block`) analogous to SHA-256's `sha256Block`
      would sit here; adding it lands with the compressor's
      own follow-up because `Signal.val` at that state width
      still triggers the same exponential-recursion issue
      the SHA-256 HW hits (see SHA-256 tests' §C2 note).
      The combinational helpers + kMux are the *synthesizable
      HW pieces that every SHA-512 engine needs* and match
      the L.1.b coverage that shipped for SHA-256.
-/

import Sparkle
import Sparkle.Core.Lut
import IP.Crypto.Proof.SHA512

open Sparkle.Core (kLutMacro)
open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.IP.Crypto.SHA512HW

/-! ### Signal-side rotate/shift helpers. -/

@[reducible, inline] def rotr64Sig {dom : DomainConfig}
    (x : Signal dom (BitVec 64)) (n : Nat) :
    Signal dom (BitVec 64) :=
  let nBv  : BitVec 64 := BitVec.ofNat 64 n
  let nBv' : BitVec 64 := BitVec.ofNat 64 (64 - n)
  let pn  : Signal dom (BitVec 64) := Signal.pure nBv
  let pn' : Signal dom (BitVec 64) := Signal.pure nBv'
  let rs : Signal dom (BitVec 64) := x >>> pn
  let ls : Signal dom (BitVec 64) := x <<< pn'
  rs ||| ls

@[reducible, inline] def shr64Sig {dom : DomainConfig}
    (x : Signal dom (BitVec 64)) (n : Nat) :
    Signal dom (BitVec 64) :=
  let nBv : BitVec 64 := BitVec.ofNat 64 n
  let pn : Signal dom (BitVec 64) := Signal.pure nBv
  x >>> pn

@[reducible, inline] def bigSigma0Sig64 {dom : DomainConfig}
    (x : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  let a := rotr64Sig x 28
  let b := rotr64Sig x 34
  let c := rotr64Sig x 39
  let ab := a ^^^ b
  ab ^^^ c

@[reducible, inline] def bigSigma1Sig64 {dom : DomainConfig}
    (x : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  let a := rotr64Sig x 14
  let b := rotr64Sig x 18
  let c := rotr64Sig x 41
  let ab := a ^^^ b
  ab ^^^ c

@[reducible, inline] def smallSigma0Sig64 {dom : DomainConfig}
    (x : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  let a := rotr64Sig x 1
  let b := rotr64Sig x 8
  let c := shr64Sig x 7
  let ab := a ^^^ b
  ab ^^^ c

@[reducible, inline] def smallSigma1Sig64 {dom : DomainConfig}
    (x : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  let a := rotr64Sig x 19
  let b := rotr64Sig x 61
  let c := shr64Sig x 6
  let ab := a ^^^ b
  ab ^^^ c

@[reducible, inline] def chFn64Sig {dom : DomainConfig}
    (x y z : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  let xy   : Signal dom (BitVec 64) := x &&& y
  let nx   : Signal dom (BitVec 64) := ~~~x
  let nxz  : Signal dom (BitVec 64) := nx &&& z
  xy ^^^ nxz

@[reducible, inline] def majFn64Sig {dom : DomainConfig}
    (x y z : Signal dom (BitVec 64)) : Signal dom (BitVec 64) :=
  let xy  : Signal dom (BitVec 64) := x &&& y
  let xz  : Signal dom (BitVec 64) := x &&& z
  let yz  : Signal dom (BitVec 64) := y &&& z
  let t1  : Signal dom (BitVec 64) := xy ^^^ xz
  t1 ^^^ yz

/-! ### K-mux: pick K[t] from a 7-bit counter (t = 0..79). -/

@[hardware_module] def kMux {dom : DomainConfig}
    (cntSig : Signal dom (BitVec 7)) : Signal dom (BitVec 64) :=
  kLut! cntSig [
    Signal.pure 0x428a2f98d728ae22#64, Signal.pure 0x7137449123ef65cd#64,
    Signal.pure 0xb5c0fbcfec4d3b2f#64, Signal.pure 0xe9b5dba58189dbbc#64,
    Signal.pure 0x3956c25bf348b538#64, Signal.pure 0x59f111f1b605d019#64,
    Signal.pure 0x923f82a4af194f9b#64, Signal.pure 0xab1c5ed5da6d8118#64,
    Signal.pure 0xd807aa98a3030242#64, Signal.pure 0x12835b0145706fbe#64,
    Signal.pure 0x243185be4ee4b28c#64, Signal.pure 0x550c7dc3d5ffb4e2#64,
    Signal.pure 0x72be5d74f27b896f#64, Signal.pure 0x80deb1fe3b1696b1#64,
    Signal.pure 0x9bdc06a725c71235#64, Signal.pure 0xc19bf174cf692694#64,
    Signal.pure 0xe49b69c19ef14ad2#64, Signal.pure 0xefbe4786384f25e3#64,
    Signal.pure 0x0fc19dc68b8cd5b5#64, Signal.pure 0x240ca1cc77ac9c65#64,
    Signal.pure 0x2de92c6f592b0275#64, Signal.pure 0x4a7484aa6ea6e483#64,
    Signal.pure 0x5cb0a9dcbd41fbd4#64, Signal.pure 0x76f988da831153b5#64,
    Signal.pure 0x983e5152ee66dfab#64, Signal.pure 0xa831c66d2db43210#64,
    Signal.pure 0xb00327c898fb213f#64, Signal.pure 0xbf597fc7beef0ee4#64,
    Signal.pure 0xc6e00bf33da88fc2#64, Signal.pure 0xd5a79147930aa725#64,
    Signal.pure 0x06ca6351e003826f#64, Signal.pure 0x142929670a0e6e70#64,
    Signal.pure 0x27b70a8546d22ffc#64, Signal.pure 0x2e1b21385c26c926#64,
    Signal.pure 0x4d2c6dfc5ac42aed#64, Signal.pure 0x53380d139d95b3df#64,
    Signal.pure 0x650a73548baf63de#64, Signal.pure 0x766a0abb3c77b2a8#64,
    Signal.pure 0x81c2c92e47edaee6#64, Signal.pure 0x92722c851482353b#64,
    Signal.pure 0xa2bfe8a14cf10364#64, Signal.pure 0xa81a664bbc423001#64,
    Signal.pure 0xc24b8b70d0f89791#64, Signal.pure 0xc76c51a30654be30#64,
    Signal.pure 0xd192e819d6ef5218#64, Signal.pure 0xd69906245565a910#64,
    Signal.pure 0xf40e35855771202a#64, Signal.pure 0x106aa07032bbd1b8#64,
    Signal.pure 0x19a4c116b8d2d0c8#64, Signal.pure 0x1e376c085141ab53#64,
    Signal.pure 0x2748774cdf8eeb99#64, Signal.pure 0x34b0bcb5e19b48a8#64,
    Signal.pure 0x391c0cb3c5c95a63#64, Signal.pure 0x4ed8aa4ae3418acb#64,
    Signal.pure 0x5b9cca4f7763e373#64, Signal.pure 0x682e6ff3d6b2b8a3#64,
    Signal.pure 0x748f82ee5defb2fc#64, Signal.pure 0x78a5636f43172f60#64,
    Signal.pure 0x84c87814a1f0ab72#64, Signal.pure 0x8cc702081a6439ec#64,
    Signal.pure 0x90befffa23631e28#64, Signal.pure 0xa4506cebde82bde9#64,
    Signal.pure 0xbef9a3f7b2c67915#64, Signal.pure 0xc67178f2e372532b#64,
    Signal.pure 0xca273eceea26619c#64, Signal.pure 0xd186b8c721c0c207#64,
    Signal.pure 0xeada7dd6cde0eb1e#64, Signal.pure 0xf57d4f7fee6ed178#64,
    Signal.pure 0x06f067aa72176fba#64, Signal.pure 0x0a637dc5a2c898a6#64,
    Signal.pure 0x113f9804bef90dae#64, Signal.pure 0x1b710b35131c471b#64,
    Signal.pure 0x28db77f523047d84#64, Signal.pure 0x32caab7b40c72493#64,
    Signal.pure 0x3c9ebe0a15c9bebc#64, Signal.pure 0x431d67c49c100d4c#64,
    Signal.pure 0x4cc5d4becb3e42b6#64, Signal.pure 0x597f299cfc657e2a#64,
    Signal.pure 0x5fcb6fab3ad6faec#64, Signal.pure 0x6c44198c4a475817#64
  ]

end Sparkle.IP.Crypto.SHA512HW
