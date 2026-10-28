import Tools.Prototype.NormNodeRangeLetOk

/-! # Unit LC16: a kernel-visible model of `machBoolMap`; `BoolMapRange` reduced to ONE correspondence lemma

BUILT (unit LC16): b1-b4 exit 1 (my proof errors), b5 exit 0 (this file). Test: Tests/Compiler/BoolMapModelAgreeTest.lean, t1 exit 0.
No sorry / axiom / native_decide.

Helper chosen: `machBoolMap` (Elab.lean), the simpler of the two: its only recursion is on a pattern subterm (`!`), and its
only callee besides total helpers is `machLiftScalarN`.
MODEL `boolMapModel lift dom`: the text of `machBoolMap` with the two calls `machLiftScalarN senv dom [(wa, a)] ·` replaced by
a PARAMETER `lift`. It is a structural (total, fuel-free) definition, so the kernel has its equations; an adequacy lemma
`exec = some r ↔ ∃ fuel, F fuel = some r` is not needed (the definition is structural; there is no fuel).
Proving the model does NOT discharge `BoolMapRange`: it is REPLACED by the correspondence lemma `BoolMapCorr` (not proved).
PROVED: `boolMapModel_ok`: for every `lift` that keeps `LetOk 0` (given a `LetOk 0` operand), the model keeps `LetOk 0`;
`boolMapRange_of`; `machineShapeN_lets''_noBM`.
PREMISE (named, NOT proved, the ONLY new one): `BoolMapCorr senv`: whenever the shipped `partial def machBoolMap` returns
`some r`, the model at `lift := machLiftScalarN senv dom [(wa, a)]` returns `some r`. Nothing else is new.
REMAINING (from LC15, unchanged): `LiftScalarRange senv` for `machLiftScalarN` (a `partial def`, recursive and calling
`machLiftConst`, `senv.natOf`, ...). That callee is why the model is parametric in `lift`: `machBoolMap` calls the partial
`machLiftScalarN`, so the model is not closed; a single-lemma reduction is possible only because `LiftScalarRange` is ALREADY a
premise of LC15's theorems (it is used, not added). Partial/extern callees of `machBoolMap` itself: `machLiftScalarN` (partial) only;
`machBits?` is total, `Expr.isAppOf`, `inlNatLit`, `mkApp*` are total. -/
namespace Tools.Prototype.BoolMapModelLetOk
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
  Tools.Prototype.NormNodeRangeLetOk

/-- `machBoolMap` with its lifting function a parameter (total, structural). -/
def boolMapModel (lift : Lean.Expr → Option (Nat × Lean.Expr)) (dom : Lean.Expr) : Lean.Expr → Option Lean.Expr
  | .app (.const c _) x =>
    if c == ``Bool.not || c == ``not then do
      let x' ← boolMapModel lift dom x
      some (mkApp3 (.const ``Complement.complement [.zero])
        (mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom (.const ``Bool []))
        (mkApp (.const ``Sparkle.Core.Signal.instComplementSignalBool []) dom) x')
    else none
  | .app (.app (.app (.app (.const ``BEq.beq _) ty) inst) x) y => do
    let w ← machBits? ty
    unless inst.isAppOf ``instBEqOfDecidableEq do none
    let (wx, x') ← lift x
    let (wy, y') ← lift y
    if wx != w || wy != w then none else
    some (mkApp5 (.const ``Sparkle.Core.Signal.Signal.beq []) ty dom
      (mkApp2 (.const ``instBEqOfDecidableEq [.zero]) ty
        (mkApp (.const ``instDecidableEqBitVec []) (inlNatLit w))) x' y')
  | _ => none

theorem boolMapModel_ok (lift : Lean.Expr → Option (Nat × Lean.Expr)) {dom : Lean.Expr}
    (hd : LetOk 0 dom = true)
    (hl : ∀ x w r, LetOk 0 x = true → lift x = some (w, r) → LetOk 0 r = true) :
    ∀ (body r : Lean.Expr), LetOk 0 body = true → boolMapModel lift dom body = some r → LetOk 0 r = true := by
  intro body
  induction body with
  | app f x ihf ihx =>
    intro r hb h
    unfold boolMapModel at h
    split at h
    · rename_i c us x0 heq
      obtain ⟨rfl, rfl⟩ := Expr.app.inj heq
      split at h
      · simp only [bind, Option.bind_eq_some_iff] at h
        obtain ⟨x', hx', hr⟩ := h
        have := Option.some.inj hr
        subst this
        have hx : LetOk 0 x = true := by simpa [LetOk] using hb
        have := ihx x' hx hx'
        simp [LetOk, hd, this]
      · cases h
    · rename_i us ty inst a b heq
      obtain ⟨h1, h2⟩ := Expr.app.inj heq
      subst h1
      subst h2
      -- the operands are now `a` (first) and `x` (second)
      simp only [LetOk, Bool.and_eq_true] at hb
      obtain ⟨⟨⟨⟨-, hty⟩, hi⟩, hxa⟩, hxb⟩ := hb
      cases hw : machBits? ty with
      | none => simp [hw] at h
      | some w =>
        by_cases hinst : inst.isAppOf ``instBEqOfDecidableEq = true
        · cases hla : lift a with
          | none => simp [hw, hinst, hla] at h
          | some pa =>
            obtain ⟨wx, x'⟩ := pa
            cases hlb : lift x with
            | none => simp [hw, hinst, hla, hlb] at h
            | some pb =>
              obtain ⟨wy, y'⟩ := pb
              simp [hw, hinst, hla, hlb] at h
              obtain ⟨-, rfl⟩ := h
              have h1 := hl a wx x' hxa hla
              have h2 := hl x wy y' hxb hlb
              simp [mkApp5, mkApp4, mkApp3, mkApp2, mkApp, LetOk, letOk_natLit, hty, hd, h1, h2]
        · simp [hw, hinst] at h
    · cases h
  | _ => intro r _ h; simp [boolMapModel] at h

/-- PREMISE (named, NOT proved; the ONLY new one): the shipped `partial def machBoolMap` returns only what the model, at the
compiler's own lifting function `machLiftScalarN senv dom [(wa, a)]`, returns. (One direction, `exec = some r → model = some r`,
is all the `LetOk 0` argument needs.) The two function bodies are the same text; no kernel equation for `machBoolMap` exists. -/
def BoolMapCorr (senv : StructEnv) : Prop :=
  ∀ (dom a : Lean.Expr) (wa : Nat) (body r : Lean.Expr),
    machBoolMap senv dom a wa body = some r →
      boolMapModel (machLiftScalarN senv dom [(wa, a)]) dom body = some r

/-- `BoolMapRange` from `LiftScalarRange` (an LC15 premise, unchanged) and the ONE correspondence lemma `BoolMapCorr`. -/
theorem boolMapRange_of {senv : StructEnv} (hl : LiftScalarRange senv) (hc : BoolMapCorr senv) : BoolMapRange senv := by
  intro dom a wa body r hd ha hb h
  exact boolMapModel_ok (machLiftScalarN senv dom [(wa, a)]) hd
    (fun x w r' hx hr => hl dom [(wa, a)] x w r' hd (by simpa using ha) hx hr) body r hb (hc dom a wa body r h)

/-- `machineShapeN_lets''_noNode` with `BoolMapRange` replaced by `BoolMapCorr`. -/
theorem machineShapeN_lets''_noBM {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange)
    (hinst1 : Inst1Range) (hsig : SigTyRange senv) (hz : ZeroLitAgrees)
    (hraw : RawNodeRange senv) (hls : LiftScalarRange senv) (hbc : BoolMapCorr senv)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (hstart : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p →
      execNorm senv p.e = some en → StartDomOk senv (shapeMid senv p en))
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp :=
  machineShapeN_lets''_noNode hroot hlift hinst1 hsig hz hraw hls (boolMapRange_of hls hbc) hpe hstart h

#print axioms boolMapModel_ok
#print axioms boolMapRange_of
#print axioms machineShapeN_lets''_noBM

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_lets''_noBM
  ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ZeroLitAgrees", "RawNodeRange", "LiftScalarRange",
    "BoolMapCorr", "Eq", "StartDomOk", "Eq"])

end Tools.Prototype.BoolMapModelLetOk
