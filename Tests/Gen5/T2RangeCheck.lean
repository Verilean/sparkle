import Tools.ShippingGen5T2Range
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in g5tr2-e57eb431 (clean, exit 0, 739 jobs; TYPE 9, MUTANT 13, AXIOMS 11 standard). No sorry / axiom / native_decide.

/-! # T2-SRCRANGE / T2-RANGE / T2-UNIQ checks (Tools/ShippingGen5T2Range.lean)

Design source: scripts/gen5/DGEN_FREEZE.md §7 (rev2.1 at `par/gen5-t2` 59889446, rev2.2 review notes). The expected
statements below are the §7 texts (§7.1 `Pkg.src_range`, §7.2 `CallOutWidthAt` and the two bridges, §7.3
`outRange_of_bitWidth` / `callOutRange_of_widths`, §7.4 `callField_unique_of_ok`) and the two collapse lemmas of §7.4,
written independently and compared mechanically (`Tests.Gen3.ExpectedType.checkExpected`); each has at least one
mutant written to change its meaning that must be rejected (`checkMutant`). A rejection is a signature / defeq
rejection, not a semantic counterexample. Then axioms.

`callOutRange_of_widths` is CONDITIONAL on `houtTy` and `CallOutWidthAt` (explicit inputs); nothing here supplies
them. -/

namespace Tests.Gen5.T2RangeCheck
open Tools.ShippingGen2
open Tests.Gen3.ExpectedType
open Sparkle.Core.Domain

section Expected
open Sparkle.Core Sparkle.Core.Signal

/-! ## T2-SRCRANGE -/

def ExpectedSrcRange : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (k' : Nat) (o : Sparkle.IR.Machine.OutField)
    (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → (q.src i bools bits)[k']? = some f →
    ∀ τ, f τ < 2 ^ o.width

/-- Mutant: bounded by the field's offset instead of its width. -/
def MutSrcRangeLo : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (k' : Nat) (o : Sparkle.IR.Machine.OutField)
    (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → (q.src i bools bits)[k']? = some f →
    ∀ τ, f τ < 2 ^ o.lo

/-- Mutant: the source output at the NEXT index. -/
def MutSrcRangeShift : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (k' : Nat) (o : Sparkle.IR.Machine.OutField)
    (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → (q.src i bools bits)[k' + 1]? = some f →
    ∀ τ, f τ < 2 ^ o.width

/-! ## T2-RANGE -/

def ExpectedOutRangeOfBitWidth : Prop :=
  ∀ (κ : Sparkle.Compiler.Elab.MixedGateBinder) (f : Nat → Nat)
    (h : ∀ τ, f τ < 2 ^ (Tools.ShippingMachineEntry.kindTy κ).bitWidth), OutRange κ f

/-- Mutant: one bit wider. -/
def MutOutRangeOfBitWidthSucc : Prop :=
  ∀ (κ : Sparkle.Compiler.Elab.MixedGateBinder) (f : Nat → Nat)
    (h : ∀ τ, f τ < 2 ^ ((Tools.ShippingMachineEntry.kindTy κ).bitWidth + 1)), OutRange κ f

def ExpectedCallOutWidthAt {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o → CallField p q k o →
    (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
      some o.ty.bitWidth

/-- Mutant: the binder at `p.kD` (call offset dropped). -/
def MutCallOutWidthAtNoK {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o → CallField p q k o →
    (p.d.shape.binders[p.kD]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
      some o.ty.bitWidth

def ExpectedCallOutRangeOfWidths : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hW : CallOutWidthAt p q k), CallOutRange p q k hk

/-- Mutant: without the callee's `houtTy` row. -/
def MutCallOutRangeOfWidthsNoOutTy : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hW : CallOutWidthAt p q k), CallOutRange p q k hk

/-- Mutant: `houtTy` on the PARENT instead of the callee. -/
def MutCallOutRangeOfWidthsParentTy : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hW : CallOutWidthAt p q k), CallOutRange p q k hk

def ExpectedCallOutWidthAtOfOneOut : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hq : P (p.d.shape.insts[k]).1 = some q) (h1 : p.d.shape.instFields = [])
    (hW : OneOutWidth P p k), CallOutWidthAt p q k

/-- Mutant: without `instFields = []`. -/
def MutCallOutWidthAtOfOneOutNoH1 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hq : P (p.d.shape.insts[k]).1 = some q)
    (hW : OneOutWidth P p k), CallOutWidthAt p q k

def ExpectedCallOutWidthAtOfKidW : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (O : Tools.ShippingChildInvA.RefLawsAOps
      Tools.ShippingChildFresh.MkRefd mref cref) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hG : p.d.shape.instFields ≠ []) {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y)
    (hout : y.1.outputs = q.d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)))
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallOutWidthAt p q k

/-- Mutant: without `hout` (the served child's outputs are `q`'s layout outputs). -/
def MutCallOutWidthAtOfKidWNoHout : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (O : Tools.ShippingChildInvA.RefLawsAOps
      Tools.ShippingChildFresh.MkRefd mref cref) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hG : p.d.shape.instFields ≠ []) {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y)
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallOutWidthAt p q k

/-- Mutant: `hy` dropped (no served child for call `k`). -/
def MutCallOutWidthAtOfKidWNoHy : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (O : Tools.ShippingChildInvA.RefLawsAOps
      Tools.ShippingChildFresh.MkRefd mref cref) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hG : p.d.shape.instFields ≠ []) {y : Tools.ShippingChildInv.Res}
    (hout : y.1.outputs = q.d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)))
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth),
    CallOutWidthAt p q k

/-! ## T2-UNIQ -/

def ExpectedCallFieldUniqueOfOk : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) {k₁ k₂ : Nat}
    {o₁ o₂ : Sparkle.IR.Machine.OutField}
    (h₁ : q.d.shape.layout.outs[k₁]? = some o₁) (h₂ : q.d.shape.layout.outs[k₂]? = some o₂)
    (hc₁ : CallField p q k o₁) (hc₂ : CallField p q k o₂), k₁ = k₂ ∧ o₁ = o₂

/-- Mutant: the two selections at DIFFERENT calls (`k` and `k + 1`); not claimed (§7.4 (a)). -/
def MutCallFieldUniqueTwoCalls : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) {k₁ k₂ : Nat}
    {o₁ o₂ : Sparkle.IR.Machine.OutField}
    (h₁ : q.d.shape.layout.outs[k₁]? = some o₁) (h₂ : q.d.shape.layout.outs[k₂]? = some o₂)
    (hc₁ : CallField p q k o₁) (hc₂ : CallField p q (k + 1) o₂), k₁ = k₂ ∧ o₁ = o₂

def ExpectedGenExtAtCallIffSelected : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o),
    GenExtAtCall p q k hk ↔
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
        ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
          q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o ∧
          (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f ∧
          SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
            (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f

/-- Mutant: without T2-FIELD's per-`i` selection. -/
def MutGenExtAtCallIffNoField : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length),
    GenExtAtCall p q k hk ↔
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
        ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
          q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o ∧
          (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f ∧
          SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
            (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f

/-- Mutant: the selection taken ONCE, outside `∀ i` (a witness taken out before `intro i`). -/
def MutGenExtAtCallIffFieldOutside : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField),
      q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o),
    GenExtAtCall p q k hk ↔
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
        ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
          q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o ∧
          (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f ∧
          SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
            (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f

def ExpectedCallOutRangeIffSelected : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o),
    CallOutRange p q k hk ↔
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
        ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
          q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o ∧
          (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f ∧
          OutRange (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f

/-- Mutant: the range at the NEXT call's binder kind. -/
def MutCallOutRangeIffShift : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o),
    CallOutRange p q k hk ↔
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
        ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
          q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o ∧
          (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f ∧
          OutRange (((p.d.bsIn.drop p.kD)[k + 1]?.map (·.2)).getD .domain) f

end Expected

/-! ## Mechanical comparison -/

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``Pkg.src_range ``ExpectedSrcRange
  checkExpected ``outRange_of_bitWidth ``ExpectedOutRangeOfBitWidth
  checkExpected ``CallOutWidthAt ``ExpectedCallOutWidthAt
  checkExpected ``callOutRange_of_widths ``ExpectedCallOutRangeOfWidths
  checkExpected ``callOutWidthAt_of_oneOut ``ExpectedCallOutWidthAtOfOneOut
  checkExpected ``callOutWidthAt_of_kidW ``ExpectedCallOutWidthAtOfKidW
  checkExpected ``callField_unique_of_ok ``ExpectedCallFieldUniqueOfOk
  checkExpected ``genExtAtCall_iff_selected ``ExpectedGenExtAtCallIffSelected
  checkExpected ``callOutRange_iff_selected ``ExpectedCallOutRangeIffSelected
  checkMutant ``Pkg.src_range ``MutSrcRangeLo
  checkMutant ``Pkg.src_range ``MutSrcRangeShift
  checkMutant ``outRange_of_bitWidth ``MutOutRangeOfBitWidthSucc
  checkMutant ``CallOutWidthAt ``MutCallOutWidthAtNoK
  checkMutant ``callOutRange_of_widths ``MutCallOutRangeOfWidthsNoOutTy
  checkMutant ``callOutRange_of_widths ``MutCallOutRangeOfWidthsParentTy
  checkMutant ``callOutWidthAt_of_oneOut ``MutCallOutWidthAtOfOneOutNoH1
  checkMutant ``callOutWidthAt_of_kidW ``MutCallOutWidthAtOfKidWNoHout
  checkMutant ``callOutWidthAt_of_kidW ``MutCallOutWidthAtOfKidWNoHy
  checkMutant ``callField_unique_of_ok ``MutCallFieldUniqueTwoCalls
  checkMutant ``genExtAtCall_iff_selected ``MutGenExtAtCallIffNoField
  checkMutant ``genExtAtCall_iff_selected ``MutGenExtAtCallIffFieldOutside
  checkMutant ``callOutRange_iff_selected ``MutCallOutRangeIffShift

/-! ## Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``Pkg.src_range, ``t2r_srcRange_gen, ``t2r_srcRange_loop, ``t2r_srcRange_comb,
      ``outRange_of_bitWidth, ``callOutRange_of_widths, ``callOutWidthAt_of_oneOut, ``callOutWidthAt_of_kidW,
      ``callField_unique_of_ok, ``genExtAtCall_iff_selected, ``callOutRange_iff_selected] do
    checkAxioms n

#print axioms Pkg.src_range
#print axioms callOutRange_of_widths
#print axioms callField_unique_of_ok

end Tests.Gen5.T2RangeCheck
