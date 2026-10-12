import Tools.ShippingLegacySemWalk2

/-! # Handler walks, 3: `handleLoop`, `handleBitVecOps`

Same method as walks 1 and 2 (`plain_none` elaborated on four handlers
there): for a head whose NAME fails every test of the handler, the handler
returns `none` from the same builder state. No arm is entered.

**Expected elaborated shapes** (not observed; join points inlined by
`dsimp only`):

* `Rec.handleLoop tr e name args hint named` =
  `if (name == ``HWVector.get && decide (args.size ≥ 2)) = true then ARM₁
   else if (name.toString.endsWith ".memoize" && decide (args.size ≥ 1)) = true
   then ARM₂ (falls through in one sub-case)
   else if (name.toString.endsWith ".loop" && decide (args.size ≥ 1)) = true
   then ARM₃ else pure none`.
* `Rec.handleBitVecOps tr e name args hint named` = six arms in sequence, the
  guards being `name == ``BitVec.extractLsb' && …`,
  `(name == ``BitVec.zeroExtend || name == ``BitVec.setWidth) && …`,
  `(name == ``BitVec.shiftLeft || … ``BitVec.ushiftRight || … ``BitVec.sshiftRight) && …`,
  `(name == ``BitVec.append || (name == ``HAppend.hAppend && canonicalMethodInst name args)) && …`,
  `name == ``BEq.beq && … && !canonicalMethodInst name args` (falls through
  when the instance is not a `BEq.mk`), and
  `isPrimitive name && (…)`; then `pure none`. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- **`handleLoop` on a head that is not `HWVector.get` and whose name ends in
neither `.memoize` nor `.loop`.** -/
theorem handleLoop_none {tr : TranslateFn} {e : Lean.Expr} {name : Name}
    {args : Array Lean.Expr} {hint : String} {named : Bool} {ctx : CompilerState}
    {s : CircuitState}
    (hget : (name == ``Sparkle.Core.Vector.HWVector.get) = false)
    (hmemo : name.toString.endsWith ".memoize" = false)
    (hloop : name.toString.endsWith ".loop" = false) :
    Ensures (Rec.handleLoop tr e name args hint named) ctx s
      (fun r t => r = none ∧ t = s) := by
  unfold Rec.handleLoop
  try dsimp only
  plain_none

/-- The names `handleBitVecOps` tests, failing. -/
structure NotBitVecOp (name : Name) : Prop where
  extract : (name == ``BitVec.extractLsb') = false
  zeroExtend : (name == ``BitVec.zeroExtend) = false
  setWidth : (name == ``BitVec.setWidth) = false
  shiftLeft : (name == ``BitVec.shiftLeft) = false
  ushiftRight : (name == ``BitVec.ushiftRight) = false
  sshiftRight : (name == ``BitVec.sshiftRight) = false
  append : (name == ``BitVec.append) = false
  hAppend : (name == ``HAppend.hAppend) = false
  beq : (name == ``BEq.beq) = false
  primitive : isPrimitive name = false

/-- **`handleBitVecOps` on a head that is none of its names and not a
primitive.** -/
theorem handleBitVecOps_none {tr : TranslateFn} {e : Lean.Expr} {name : Name}
    {args : Array Lean.Expr} {hint : String} {named : Bool} {ctx : CompilerState}
    {s : CircuitState} (hn : NotBitVecOp name) :
    Ensures (Rec.handleBitVecOps tr e name args hint named) ctx s
      (fun r t => r = none ∧ t = s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hn
  unfold Rec.handleBitVecOps
  try dsimp only
  -- `plain_none` made no progress here (first build): the third arm has an
  -- `if` on the name inside an expression, which `split` picks. The name
  -- tests are rewritten explicitly instead; every guard becomes `false`.
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    Bool.false_and, Bool.and_false, Bool.false_or, Bool.or_false, Bool.or_self,
    Bool.not_false, Bool.false_eq_true, eq_self, if_false, if_true]
  exact Ensures.pure ⟨rfl, rfl⟩

end Tools.ShippingLegacySem
