/-
  Layer 2 of Chapter 12: transport the ℝ controller equation to Q15.16 with
  `retype`, and check that the transported equation is the one Sparkle's
  datapath actually computes.

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

  retype pins Lean v4.32.0; Sparkle and `proofs/` are on v4.28.0, so this
  package cannot import either and the ℝ model is duplicated here — the same
  tradeoff `Falsify.lean` documents at length.  The duplication is kept
  honest by `#guard`s below that re-derive the constants `proofs/` commits to.

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
instance : OfNat FixQ 16 := ⟨⟨16 * scale⟩⟩
instance : OfNat FixQ 10000 := ⟨⟨10000 * scale⟩⟩
instance : OfNat FixQ 6180 := ⟨⟨6180 * scale⟩⟩
instance : OfNat FixQ 12600 := ⟨⟨12600 * scale⟩⟩

instance : Add FixQ := ⟨fun a b => ⟨a.n + b.n⟩⟩
instance : Sub FixQ := ⟨fun a b => ⟨a.n - b.n⟩⟩
instance : Neg FixQ := ⟨fun a => ⟨-a.n⟩⟩

/-- Floors, to match `extractLsb' 16` on a sign-extended product.  See header. -/
instance : Mul FixQ := ⟨fun a b => ⟨(a.n * b.n) / scale⟩⟩
instance : Div FixQ := ⟨fun a b => ⟨(a.n * scale) / b.n⟩⟩

end FixQ

declare_retype RealToFixQ : Real => FixQ

/-! ### The ℝ model

Duplicated from `proofs/SparkleProofs/Control/EstimatorDesign.lean` (the
fixed-gain Kalman observer), kept definitionally identical so the transported
version is a faithful image of what the proofs talk about. -/

noncomputable def dt : ℝ := 1 / 16
noncomputable def k1 : ℝ := 6180 / 10000
noncomputable def k2 : ℝ := 12600 / 10000

/-- One observer step, position channel: `x1⁺ = x1 + dt·x2 + k1·(y − x1)`. -/
noncomputable def nextX1 (x1 x2 y : ℝ) : ℝ := x1 + dt * x2 + k1 * (y - x1)

/-- Velocity channel: `x2⁺ = x2 + dt·u + k2·(y − x1)`. -/
noncomputable def nextX2 (x1 x2 y u : ℝ) : ℝ := x2 + dt * u + k2 * (y - x1)

/-! ### The transport

`retype_def` generates the Q15.16 counterpart; the `attribute` line is what
makes `nextX1`'s *references* to `dt`/`k1` follow the transport instead of
staying at type ℝ (without it the elaborator reports `dt has type ℝ but is
expected to have type FixQ`). -/

retype_def dtQ := dt using Real => FixQ
retype_def k1Q := k1 using Real => FixQ
retype_def k2Q := k2 using Real => FixQ

attribute [retype RealToFixQ] dt k1 k2

retype_def nextX1Q := nextX1 using Real => FixQ
retype_def nextX2Q := nextX2 using Real => FixQ

/-! ### Checks

The constants first — each is the ℝ value times 2^16, floored, and each is
checkable by hand:

    dt = 1/16       → 65536/16      = 4096
    k1 = 0.6180     → 0.6180·65536  = 40501.2…  → 40501
    k2 = 1.2600     → 1.2600·65536  = 82575.4…  → 82575
-/

#guard dtQ.toNum == 4096
#guard k1Q.toNum == 40501
#guard k2Q.toNum == 82575

/-! Then the transported equation.  With `x1 = 1, x2 = 0, y = 0` the ℝ
equation gives `1 + 0 − 0.6180·1 = 0.3820`, and 25035/65536 = 0.38200…

This is the check that matters: the transported function agrees with the
function it was derived from, and no human transcribed a coefficient. -/

#guard (nextX1Q ⟨65536⟩ ⟨0⟩ ⟨0⟩).toNum == 25035

-- `y = x1` kills the innovation, leaving pure integration `x1 + dt·x2`.
-- With `x2 = 1`: `1 + 1/16 = 1.0625` → 69632.
#guard (nextX1Q ⟨65536⟩ ⟨65536⟩ ⟨65536⟩).toNum == 69632

-- Velocity channel, `u = 0`, `y = 0`, `x1 = 1`: `x2 − k2 = 0 − 1.26`.
#guard (nextX2Q ⟨65536⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩).toNum == -82575

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
