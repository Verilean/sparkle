/-
  Layer 2 of Chapter 12: transport the ℝ controller equation to Q15.16 with
  `retype`, and check that the transported equation is the one Sparkle's
  datapath actually computes.

  The system is the SAME PID loop the chapter runs on throughout — the
  closed loop of §12.1.1, whose ℝ Lyapunov certificate is §12.1.3
  (`proofs/SparkleProofs/Control/PIDDesign.lean`).  Nothing new is
  introduced here; this file only carries that already-proved equation
  down to fixed point.

  ## The failure this exists to prevent

  The usual practice is to write the fixed-point version of a control law by
  hand, next to the ℝ version.  That creates two sources of truth, and they
  drift: a gain rounded differently, a `-` that became saturating on one side
  only, a shift in the wrong direction.  Simulating the RTL does not find it,
  because the RTL is being compared against itself — the ℝ model, the thing
  that was actually *proved* stable, is never in the loop.

  So don't write it.  Derive it.  `retype` replaces `ℝ` throughout a
  definition and substitutes the corresponding operations, so `nextX1Q` below
  is a Q15.16 function nobody typed.

  ## Why `Int./` and not `Int.tdiv`

  `FixQ.Mul` floors (`Int./` rounds toward −∞).  That is not a free choice: it
  has to match `Sparkle.IP.Control.FixedPoint.mulQ`, which is
  `BitVec.extractLsb' 16` on a sign-extended product — an ARITHMETIC right
  shift, which also floors.  Had either side truncated instead, the two would
  agree on every positive product and disagree on every negative one, which is
  exactly the kind of bug that survives a test suite built from positive
  fixtures.  `Tests/` checks the agreement on sign-crossing cases; see
  `docs/tutorial/md/Ch12_ControlPrecision.md` §12.2.2.

  ## The seam, again

  The toolchain split that used to force this separation is gone — root,
  `proofs/` and this package are all on v4.32.1.  What remains is packaging:
  this is still its own Lake package with its own mathlib, so the ℝ model is
  duplicated here rather than imported.  Folding it into `proofs/` is the
  pending follow-up.  Until then the duplication is kept honest by the
  `#guard`s below, which re-derive the constants `proofs/` commits to.

  What this file does NOT do: prove `∀ a b, (mulQ a b).toInt = (a.toInt *
  b.toInt) / 2^16`.  That is a `BitVec` lemma, it belongs on the Sparkle side
  of the toolchain seam, and `bv_decide` should reach it at this width.  Until
  it exists, the transport is checked on cases, and the chapter says so.
-/

import Retype
import Mathlib.Data.Real.Basic

namespace RetypeLab.FixedPointTransport

/-! ### The fixed-point target type

Q15.16 on `Int`: the stored integer is `value · 2^16`.  Deliberately `Int`
rather than `BitVec 32` — the transport is about the *equation*, and keeping
overflow out of it lets the wrap-around question be asked separately (it is
Sparkle's `satAdd`/`clampSym`, and §12.4's clamp discussion). -/

structure FixQ where
  n : Int
deriving Repr, DecidableEq

namespace FixQ

/-- 2^16.  The scale is baked in rather than a parameter so `#eval` below
    prints numbers a reader can check by hand. -/
def scale : Int := 65536

/-- Interpret back into ℚ-as-a-pair, for the `#guard`s. -/
def toNum (a : FixQ) : Int := a.n

instance : OfNat FixQ 0 := ⟨⟨0⟩⟩
instance : OfNat FixQ 1 := ⟨⟨scale⟩⟩
instance : OfNat FixQ 2 := ⟨⟨2 * scale⟩⟩
instance : OfNat FixQ 4 := ⟨⟨4 * scale⟩⟩
instance : OfNat FixQ 8 := ⟨⟨8 * scale⟩⟩
instance : OfNat FixQ 9 := ⟨⟨9 * scale⟩⟩
instance : OfNat FixQ 10 := ⟨⟨10 * scale⟩⟩

instance : Add FixQ := ⟨fun a b => ⟨a.n + b.n⟩⟩
instance : Sub FixQ := ⟨fun a b => ⟨a.n - b.n⟩⟩
instance : Neg FixQ := ⟨fun a => ⟨-a.n⟩⟩

/-- Floors, to match `extractLsb' 16` on a sign-extended product.  See header. -/
instance : Mul FixQ := ⟨fun a b => ⟨(a.n * b.n) / scale⟩⟩
instance : Div FixQ := ⟨fun a b => ⟨(a.n * scale) / b.n⟩⟩

end FixQ

declare_retype RealToFixQ : Real => FixQ

/-! ### The ℝ model — the closed loop of §12.1.1

Duplicated from `proofs/SparkleProofs/Control/PIDDesign.lean`, kept
definitionally identical so the transported version is a faithful image of
what the proofs talk about.  These are the three lines §12.1.3 displays:

    x⁺ = 0.6625·x + 0.1·I − 0.0125·p        (0.6625 = pa − pb·(Kp+Ki+Kd))
    I⁺ = −0.25·x + I
    p⁺ = −x
-/

/-- PID gains (§12.1.1). -/
noncomputable def Kp : ℝ := 2
noncomputable def Ki : ℝ := 1 / 4
noncomputable def Kd : ℝ := 1 / 8

/-- Plant pole and input gain: `x⁺ = pa·x + pb·u`. -/
noncomputable def pa : ℝ := 9 / 10
noncomputable def pb : ℝ := 1 / 10

/-- Plant state. -/
noncomputable def nextX (x I p : ℝ) : ℝ :=
  (pa - pb * (Kp + Ki + Kd)) * x + pb * I - pb * Kd * p

/-- Integrator. -/
noncomputable def nextI (x I _p : ℝ) : ℝ := I - Ki * x

/-- Previous-error register. -/
noncomputable def nextP (x _I _p : ℝ) : ℝ := -x

/-! ### The transport

`retype_def` generates the Q15.16 counterpart; the `attribute` line is what
makes `nextX1`'s *references* to `dt`/`k1` follow the transport instead of
staying at type ℝ (without it the elaborator reports `dt has type ℝ but is
expected to have type FixQ`). -/

retype_def KpQ := Kp using Real => FixQ
retype_def KiQ := Ki using Real => FixQ
retype_def KdQ := Kd using Real => FixQ
retype_def paQ := pa using Real => FixQ
retype_def pbQ := pb using Real => FixQ

attribute [retype RealToFixQ] Kp Ki Kd pa pb

retype_def nextXQ := nextX using Real => FixQ
retype_def nextIQ := nextI using Real => FixQ
retype_def nextPQ := nextP using Real => FixQ

/-! ### Checks

The gains first — each is the ℝ value times 2^16, and each is checkable by
hand against §12.1.1:

    Kp = 2      → 2·65536      = 131072
    Ki = 1/4    → 65536/4      = 16384
    Kd = 1/8    → 65536/8      = 8192
    pa = 9/10   → 0.9·65536    = 58982.4  → 58982
-/

#guard KpQ.toNum == 131072
#guard KiQ.toNum == 16384
#guard KdQ.toNum == 8192
#guard paQ.toNum == 58982

/-! Then the transported closed loop, at `x = 1, I = 0, p = 0`.  §12.1.3
displays the coefficient 0.6625, and 43419/65536 = 0.66250 — so the
transported equation reproduces the number the ℝ proof is about, with no
coefficient transcribed by hand.

This is the check the whole section exists for. -/

#guard (nextXQ ⟨65536⟩ ⟨0⟩ ⟨0⟩).toNum == 43419      -- 0.66250 = 0.6625 ✓

-- The other two rows of the same step: I⁺ = −Ki·x = −0.25, p⁺ = −x = −1.
#guard (nextIQ ⟨65536⟩ ⟨0⟩ ⟨0⟩).toNum == -16384
#guard (nextPQ ⟨65536⟩ ⟨0⟩ ⟨0⟩).toNum == -65536

-- The integrator channel is exact here (Ki = 1/4 is a power of two, so
-- nothing is lost); the plant channel is not (0.9 is not dyadic).  That
-- asymmetry is why §12.4 has to bound the error rather than dismiss it.
#guard (nextIQ ⟨4 * 65536⟩ ⟨0⟩ ⟨0⟩).toNum == -65536

/-! ### The floor is not a rounding footnote

Sign-crossing products are where a truncating implementation would diverge
from this one.  `(-1) * 1` in Q15.16 is `(-65536 · 65536)/65536 = -65536`
exactly, but a product that does not divide evenly floors DOWN on the
negative side rather than toward zero: -/

#guard ((⟨-1⟩ : FixQ) * ⟨1⟩).n == -1        -- (-1·1)/65536 = -1/65536 → -1, not 0

-- The same magnitude on the positive side goes to 0.  A truncating divide
-- would give 0 for both, which is the asymmetry `mulQ_error` relies on
-- NOT having: its error bound is one-sided precisely because both signs floor.
#guard ((⟨1⟩ : FixQ) * ⟨1⟩).n == 0

end RetypeLab.FixedPointTransport
