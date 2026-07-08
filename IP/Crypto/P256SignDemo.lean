/-
  IP.Crypto.P256SignDemo — P-256 ECDSA signer CORE, the drop-in
  analogue of `EcdsaSignDemo.signCore` on NIST P-256.

  `p256SignCore (start) (d k z) : SignCoreOut{rOut,sOut,done}` wires
  the P-256 sub-engines (field mul, Jacobian point-op a=-3, scalar-mul
  ladder, generic Fermat mod-inverse `ModInvHW` reused as-is, mod-n
  mul, sign orchestrator) with every start/done handshake closed by a
  1-cycle feedback register — identical composition to the secp256k1
  signer, only the curve engines differ.  The UART demo top is M3.
-/
import Sparkle
import IP.Crypto.Proof.P256Field
import IP.Crypto.Proof.P256ECDSA
import IP.Crypto.Proof.P256PointJac
import IP.Crypto.P256FieldHW
import IP.Crypto.P256PointOpHW
import IP.Crypto.P256ScalarMulHW
import IP.Crypto.ModInvHW
import IP.Crypto.P256OrderHW
import IP.Crypto.P256ECDSAHW

namespace Sparkle.IP.Crypto.P256SignDemo

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Crypto.P256FieldHW (mulHW MulOut)
open Sparkle.IP.Crypto.P256PointOpHW (pointOpHW PointOpOut)
open Sparkle.IP.Crypto.P256ScalarMulHW (scalarMulHW ScalarMulOut)
open Sparkle.IP.Crypto.ModInvHW (modInvHW ModInvOut)
open Sparkle.IP.Crypto.P256OrderHW (mulModNHW)
open Sparkle.IP.Crypto.P256ECDSAHW (signHW SignOut)

@[hardware_module] def wMul {dom : DomainConfig}
    (start : Signal dom Bool) (aIn bIn : Signal dom (BitVec 256)) : MulOut dom :=
  mulHW start aIn bIn

@[hardware_module] def wMulN {dom : DomainConfig}
    (start : Signal dom Bool) (aIn bIn : Signal dom (BitVec 256)) :
    Sparkle.IP.Crypto.P256OrderHW.MulOut dom :=
  mulModNHW start aIn bIn

@[hardware_module] def wPointOp {dom : DomainConfig}
    (start opDouble : Signal dom Bool)
    (x1 y1 z1 x2 y2 z2 : Signal dom (BitVec 256))
    (mulResult : Signal dom (BitVec 256)) (mulDone : Signal dom Bool) : PointOpOut dom :=
  pointOpHW start opDouble x1 y1 z1 x2 y2 z2 mulResult mulDone

@[hardware_module] def wScalarMul {dom : DomainConfig}
    (start : Signal dom Bool) (k : Signal dom (BitVec 256))
    (px py pz : Signal dom (BitVec 256))
    (poResX poResY poResZ : Signal dom (BitVec 256))
    (poResDone : Signal dom Bool) : ScalarMulOut dom :=
  scalarMulHW start k px py pz poResX poResY poResZ poResDone

@[hardware_module] def wInv {dom : DomainConfig}
    (start : Signal dom Bool) (aIn expBits : Signal dom (BitVec 256))
    (mulResult : Signal dom (BitVec 256)) (mulDone : Signal dom Bool) : ModInvOut dom :=
  modInvHW start aIn expBits mulResult mulDone

@[hardware_module] def wSign {dom : DomainConfig}
    (start : Signal dom Bool)
    (d k z : Signal dom (BitVec 256))
    (smX smY smZ : Signal dom (BitVec 256)) (smDone : Signal dom Bool)
    (pRes : Signal dom (BitVec 256)) (pDone : Signal dom Bool)
    (nRes : Signal dom (BitVec 256)) (nDone : Signal dom Bool) : SignOut dom :=
  signHW start d k z smX smY smZ smDone pRes pDone nRes nDone

/-! ## Signer core — all handshakes closed. -/

/-- Base-point / curve constants as 256-bit literals. -/
def gX : BitVec 256 := BitVec.ofNat 256 Sparkle.IP.Crypto.P256PointJac.baseX
def gY : BitVec 256 := BitVec.ofNat 256 Sparkle.IP.Crypto.P256PointJac.baseY
def one256 : BitVec 256 := 1#256

/-- Signature-core output. -/
structure SignCoreOut (dom : DomainConfig) where
  /-- Signature component r (valid at `done`). -/
  rOut : Signal dom (BitVec 256)
  /-- Signature component s (valid at `done`). -/
  sOut : Signal dom (BitVec 256)
  /-- Pulses when (r, s) is ready. -/
  done : Signal dom Bool

instance {dom : DomainConfig} :
    Sparkle.Core.HasDomain (SignCoreOut dom) dom := ⟨⟩

/-- The ECDSA signer with every sub-engine wired and every start/done
    handshake closed by a 1-cycle feedback register.

    Engines instantiated:
      * `smMul`  — field mul for the scalar-mul point-op
      * `po`     — Jacobian point-op (double/add) for k·G
      * `sm`     — scalar-mul ladder (drives `po`)
      * `pMul`   — mod-p field mul (feeds the mod-p inverse AND the
                   signer's direct mod-p multiplies)
      * `pInv`   — mod-p Fermat inverse (drives `pMul`)
      * `nMul`   — mod-n mul (feeds the mod-n inverse AND the direct
                   mod-n multiplies)
      * `nInv`   — mod-n Fermat inverse (drives `nMul`)
      * `sign`   — the sign orchestrator (drives sm / mod-p / mod-n)

    The mod-p engine the signer drives can be EITHER an inverse
    (`pInvStart`) or a plain multiply (`pMulStart`); we route the
    inverse to `pInv` and the multiply to `pMul` and mux the result /
    done from whichever the signer triggered.  Same for mod-n. -/
def p256SignCore {dom : DomainConfig}
    (start : Signal dom Bool)
    (d k z : Signal dom (BitVec 256)) : SignCoreOut dom :=
  circuit do
    -- ===== feedback registers (all 1-cycle delayed) =====
    -- scalar-mul point-op ↔ field-mul
    let smMulResR ← Signal.reg (0#256)
    let smMulDoneR ← Signal.reg false
    -- point-op → scalar-mul
    let poXR ← Signal.reg (0#256)
    let poYR ← Signal.reg (0#256)
    let poZR ← Signal.reg (0#256)
    let poDoneR ← Signal.reg false
    -- scalar-mul → sign
    let smXR ← Signal.reg (0#256)
    let smYR ← Signal.reg (0#256)
    let smZR ← Signal.reg (0#256)
    let smDoneR ← Signal.reg false
    -- mod-p mul feedback (into pInv and into sign)
    let pMulResR ← Signal.reg (0#256)
    let pMulDoneR ← Signal.reg false
    -- mod-p engine result → sign
    let pResR ← Signal.reg (0#256)
    let pDoneR ← Signal.reg false
    -- "the signer issued a DIRECT mod-p multiply and is awaiting it"
    -- (distinguishes the signer's multiply from the inverse's internal
    -- squarings, which share the same pMul engine).
    let pDirR ← Signal.reg false
    -- mod-n mul feedback (into nInv and into sign)
    let nMulResR ← Signal.reg (0#256)
    let nMulDoneR ← Signal.reg false
    -- mod-n engine result → sign
    let nResR ← Signal.reg (0#256)
    let nDoneR ← Signal.reg false
    let nDirR ← Signal.reg false

    let smMulResSig := (smMulResR : Signal dom (BitVec 256))
    let smMulDoneSig := (smMulDoneR : Signal dom Bool)
    let poXSig := (poXR : Signal dom (BitVec 256))
    let poYSig := (poYR : Signal dom (BitVec 256))
    let poZSig := (poZR : Signal dom (BitVec 256))
    let poDoneSig := (poDoneR : Signal dom Bool)
    let smXSig := (smXR : Signal dom (BitVec 256))
    let smYSig := (smYR : Signal dom (BitVec 256))
    let smZSig := (smZR : Signal dom (BitVec 256))
    let smDoneSig := (smDoneR : Signal dom Bool)
    let pMulResSig := (pMulResR : Signal dom (BitVec 256))
    let pMulDoneSig := (pMulDoneR : Signal dom Bool)
    let pResSig := (pResR : Signal dom (BitVec 256))
    let pDoneSig := (pDoneR : Signal dom Bool)
    let pDirSig := (pDirR : Signal dom Bool)
    let nMulResSig := (nMulResR : Signal dom (BitVec 256))
    let nMulDoneSig := (nMulDoneR : Signal dom Bool)
    let nResSig := (nResR : Signal dom (BitVec 256))
    let nDoneSig := (nDoneR : Signal dom Bool)
    let nDirSig := (nDirR : Signal dom Bool)

    -- ===== the sign orchestrator =====
    let gXSig := (Signal.pure gX : Signal dom (BitVec 256))
    let gYSig := (Signal.pure gY : Signal dom (BitVec 256))
    let gZSig := (Signal.pure one256 : Signal dom (BitVec 256))
    let sign := wSign start d k z smXSig smYSig smZSig smDoneSig
                  pResSig pDoneSig nResSig nDoneSig

    -- ===== scalar-mul + its point-op + field-mul =====
    let sm := wScalarMul sign.smStart sign.smK gXSig gYSig gZSig
                poXSig poYSig poZSig poDoneSig
    let po := wPointOp sm.poStart sm.poOpDouble
                sm.poX1 sm.poY1 sm.poZ1 sm.poX2 sm.poY2 sm.poZ2
                smMulResSig smMulDoneSig
    let smMul := wMul po.mulStart po.mulA po.mulB

    -- ===== mod-p inverse-or-multiply engine =====
    -- `pInv` drives its OWN internal field-mul port; but we give the
    -- inverse and the signer's direct multiply a SHARED `pMul` engine,
    -- muxing the start/operands by which one is active.
    let pInv := wInv sign.pInvStart sign.pA sign.pExp pMulResSig pMulDoneSig
    -- pMul serves either the inverse's internal multiply (pInv.mulStart)
    -- or the signer's direct mod-p multiply (sign.pMulStart).
    let pMulStart := (pInv.mulStart ||| sign.pMulStart : Signal dom Bool)
    let pMulA := (Signal.mux sign.pMulStart sign.pA pInv.mulA : Signal dom (BitVec 256))
    let pMulB := (Signal.mux sign.pMulStart sign.pB pInv.mulB : Signal dom (BitVec 256))
    let pMul := wMul pMulStart pMulA pMulB

    -- ===== mod-n inverse-or-multiply engine =====
    let nInv := wInv sign.nInvStart sign.nA sign.nExp nMulResSig nMulDoneSig
    let nMulStart := (nInv.mulStart ||| sign.nMulStart : Signal dom Bool)
    let nMulA := (Signal.mux sign.nMulStart sign.nA nInv.mulA : Signal dom (BitVec 256))
    let nMulB := (Signal.mux sign.nMulStart sign.nB nInv.mulB : Signal dom (BitVec 256))
    let nMul := wMulN nMulStart nMulA nMulB

    -- ===== close all feedback loops =====
    smMulResR <~ smMul.result
    smMulDoneR <~ smMul.done
    poXR <~ po.xOut
    poYR <~ po.yOut
    poZR <~ po.zOut
    poDoneR <~ po.done
    smXR <~ sm.xOut
    smYR <~ sm.yOut
    smZR <~ sm.zOut
    smDoneR <~ sm.done
    -- mod-p: the shared pMul result feeds both the inverse's internal
    -- multiply AND the signer's `pRes`; done likewise.  For the signer,
    -- `pRes/pDone` = inverse result when an inverse ran, else the mul.
    pMulResR <~ pMul.result
    pMulDoneR <~ pMul.done
    -- `pDir` tracks a pending signer DIRECT multiply: set when the
    -- signer issues one, cleared when pMul completes it.
    let pDirSet := sign.pMulStart
    let pMulFinish := (pDirSig &&& pMul.done : Signal dom Bool)
    pDirR <~ Signal.mux pDirSet (Signal.pure true : Signal dom Bool)
              (Signal.mux pMul.done (Signal.pure false : Signal dom Bool) pDirSig)
    -- Signer's mod-p result: the direct multiply result when a direct
    -- multiply just finished, else the inverse result.
    pResR <~ Signal.mux pMulFinish pMul.result
              (Signal.mux pInv.done pInv.result pResSig)
    -- Signer's mod-p done pulses when EITHER the inverse finished OR the
    -- signer's own direct multiply finished (NOT the inverse's internal
    -- squarings — those are gated out by pDir).
    pDoneR <~ (pInv.done ||| pMulFinish)
    -- mod-n (same structure):
    nMulResR <~ nMul.result
    nMulDoneR <~ nMul.done
    let nDirSet := sign.nMulStart
    let nMulFinish := (nDirSig &&& nMul.done : Signal dom Bool)
    nDirR <~ Signal.mux nDirSet (Signal.pure true : Signal dom Bool)
              (Signal.mux nMul.done (Signal.pure false : Signal dom Bool) nDirSig)
    nResR <~ Signal.mux nMulFinish nMul.result
              (Signal.mux nInv.done nInv.result nResSig)
    nDoneR <~ (nInv.done ||| nMulFinish)

    return ({ rOut := sign.rOut
            , sOut := sign.sOut
            , done := sign.done
            } : SignCoreOut dom)

end Sparkle.IP.Crypto.P256SignDemo
