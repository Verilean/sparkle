import Tools.ShippingGen5T2Dec
import Tests.Gen3.ExpectedType
import Tests.Compiler.ShippingMachineLinkedTest
set_option autoImplicit false
-- NOT BUILT: written without running lake/lean (design-to-code unit). Intended: no sorry / axiom / native_decide.

/-! # T2-DEC checks (issue `sparkle-gen5-t2-tie`, T2-DEC part; Tools/ShippingGen5T2Dec.lean)

Design source: scripts/gen5/T2COVER_FREEZE.md §0 and scripts/gen5/M5_INDEP_STUDIES.md §A.3 (`par/gen5-t2` c398021c).
Design-to-code only; not the FG.

1. **Expected types.** `decA`, `decB`, `CallOutF` (their bodies, parameter by parameter), `letTie_dec`, the three
   dispatch equations, (1) `hPointG_iff_callOutG`, (2) `hPointG_iff_callOutDec` and (3) `hPointAt_iff_callOutDec` are
   compared MECHANICALLY (`Tests.Gen3.ExpectedType.checkExpected`) against independent `Expected…` statements written
   from the design text. Meaning-changing MUTANTS must FAIL (`checkMutant`): decoding with the PARENT's port list,
   the old group-only name conjunct in `CallOutF`, the call-output position without the `kD` offset, `LetTie` against
   the parent as callee, `pkgBsC` without `take`, (1) one-way and with the callee/parent swapped, (2) without `hP`,
   one-way, and on the parent's families, (3) without `hG`.
2. **Data control** (data only; it supplies NO `CallOutF`/`HPointG` and no run): one-output parent `callerL` →
   `pickByteH` under the concrete assignment `PL` (fixtures as Tests/Gen2/DataBridgeCheck.lean and
   Tests/Gen3/ArityCheck.lean, copied, not imported). `hP` is decided, so (2) and `letTie_dec` apply to EVERY package
   with `callerL`'s data; `CallField` reads the one-output branch; (3)'s `hG` is refuted on this parent (the reason
   (2), not (3), is the T2-DEC statement).
3. Axioms: `checkAxioms` (standard only) and `#print axioms`. -/

namespace Tests.Gen5.T2DecCheck
open Tools.ShippingGen2
open Tests.Gen3.ExpectedType
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest
open Sparkle.Core.Domain

/-! ## 1. Expected statements and mutants -/

section Expected
open Sparkle.Core Sparkle.Core.Signal

noncomputable def ExpectedDecA {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) : ArgFamB ι dom :=
  fun i bools bits => Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD)
    (Tools.ShippingMachineCallsLinkedT.valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1)

noncomputable def ExpectedDecB {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) : ArgFamV ι dom :=
  fun i bools bits => Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD)
    (Tools.ShippingMachineCallsLinkedT.valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1)

/-- Mutant: decoded with the PARENT's port list. -/
noncomputable def MutDecAParent {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) : ArgFamB ι dom :=
  fun i bools bits => Tools.ShippingMachineChild.boolsOf (D := dom i) (p.d.bsIn.take p.kD)
    (Tools.ShippingMachineCallsLinkedT.valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1)

/-- Mutant: decoded with the PARENT's port list. -/
noncomputable def MutDecBParent {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) : ArgFamV ι dom :=
  fun i bools bits => Tools.ShippingMachineChild.bitsOf (D := dom i) (p.d.bsIn.take p.kD)
    (Tools.ShippingMachineCallsLinkedT.valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1)

def ExpectedCallOutF {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (A : ArgFamB ι dom)
    (B : ArgFamV ι dom) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
      q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o ∧
      (q.src i (A i bools bits) (B i bools bits))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (p.extBS i bools bits r).val τ)
          (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

/-- Mutant: the old group-only name conjunct (this is `CallOut`, which misses one-output parents). -/
def MutCallOutFOldName {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (A : ArgFamB ι dom)
    (B : ArgFamV ι dom) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
      q.d.shape.layout.outs[k']? = some o ∧ o.name = p.d.shape.instFields.getD k "" ∧
      (q.src i (A i bools bits) (B i bools bits))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (p.extBS i bools bits r).val τ)
          (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

/-- Mutant: the call-output position without the `kD` offset. -/
def MutCallOutFNoOffset {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (A : ArgFamB ι dom)
    (B : ArgFamV ι dom) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
      q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o ∧
      (q.src i (A i bools bits) (B i bools bits))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (p.extBS i bools bits r).val τ)
          (fun r n => (p.extS i bools bits r n).val τ)
          k (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

def ExpectedLetTieDec : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length),
    LetTie p q k hk (decA p q k hk) (decB p q k hk)

/-- Mutant: the parent as the callee of the tie. -/
def MutLetTieParent : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length),
    LetTie p p k hk (decA p q k hk) (decB p q k hk)

def ExpectedPkgBsCOf : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {P : Pkgs ι dom} {c : Lean.Name} {q : Pkg ι dom} (hP : P c = some q),
    pkgBsC P c = q.d.bsIn.take q.kD

/-- Mutant: the whole binder list (no `take`). -/
def MutPkgBsCOfAll : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {P : Pkgs ι dom} {c : Lean.Name} {q : Pkg ι dom} (hP : P c = some q),
    pkgBsC P c = q.d.bsIn

def ExpectedPkgOutsCOf : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {P : Pkgs ι dom} {c : Lean.Name} {q : Pkg ι dom} (hP : P c = some q),
    pkgOutsC P c = q.d.shape.layout.outs

def ExpectedPkgSrcOf : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {P : Pkgs ι dom} {c : Lean.Name} {q : Pkg ι dom} (hP : P c = some q) (i : ι)
    (A : Nat → Signal (dom i) Bool) (B : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    pkgSrc P i c A B = q.src i A B

def ExpectedG1 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat),
    HPointG P p q k ↔ CallOutG P p q k

/-- Mutant: one direction only. -/
def MutG1OneWay : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat),
    HPointG P p q k → CallOutG P p q k

/-- Mutant: parent and callee swapped on the right. -/
def MutG1Swap : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat),
    HPointG P p q k ↔ CallOutG P q p k

def ExpectedDec : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]'hk).1 = some q),
    HPointG P p q k ↔ CallOutF p q k (decA p q k hk) (decB p q k hk)

/-- Mutant: no `hP`. -/
def MutDecNoHP : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length),
    HPointG P p q k ↔ CallOutF p q k (decA p q k hk) (decB p q k hk)

/-- Mutant: one direction only (sufficiency, as `hPointAt_of_ties`). -/
def MutDecOneWay : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]'hk).1 = some q),
    CallOutF p q k (decA p q k hk) (decB p q k hk) → HPointG P p q k

/-- Mutant: the families decoded with the parent as callee. -/
def MutDecParentFam : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]'hk).1 = some q),
    HPointG P p q k ↔ CallOutF p q k (decA p p k hk) (decB p p k hk)

def ExpectedGroup : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hG : p.d.shape.instFields ≠ []),
    Tools.ShippingQuadHPoint.HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k ↔
      CallOut p q k (decA p q k hk) (decB p q k hk)

/-- Mutant: no `hG` (would claim the group text for one-output parents). -/
def MutGroupNoHG : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]'hk).1 = some q),
    Tools.ShippingQuadHPoint.HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k ↔
      CallOut p q k (decA p q k hk) (decB p q k hk)

end Expected

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``decA ``ExpectedDecA
  checkExpected ``decB ``ExpectedDecB
  checkExpected ``CallOutF ``ExpectedCallOutF
  checkExpected ``letTie_dec ``ExpectedLetTieDec
  checkExpected ``pkgBsC_of ``ExpectedPkgBsCOf
  checkExpected ``pkgOutsC_of ``ExpectedPkgOutsCOf
  checkExpected ``pkgSrc_of ``ExpectedPkgSrcOf
  checkExpected ``hPointG_iff_callOutG ``ExpectedG1
  checkExpected ``hPointG_iff_callOutDec ``ExpectedDec
  checkExpected ``hPointAt_iff_callOutDec ``ExpectedGroup
  checkMutant ``decA ``MutDecAParent
  checkMutant ``decB ``MutDecBParent
  checkMutant ``CallOutF ``MutCallOutFOldName
  checkMutant ``CallOutF ``MutCallOutFNoOffset
  checkMutant ``letTie_dec ``MutLetTieParent
  checkMutant ``pkgBsC_of ``MutPkgBsCOfAll
  checkMutant ``hPointG_iff_callOutG ``MutG1OneWay
  checkMutant ``hPointG_iff_callOutG ``MutG1Swap
  checkMutant ``hPointG_iff_callOutDec ``MutDecNoHP
  checkMutant ``hPointG_iff_callOutDec ``MutDecOneWay
  checkMutant ``hPointG_iff_callOutDec ``MutDecParentFam
  checkMutant ``hPointAt_iff_callOutDec ``MutGroupNoHG
  -- harness sanity: a mutant is also distinct from its expected statement
  checkMutant ``ExpectedDec ``MutDecNoHP

/-! ## 2. Data control: one-output `callerL` → `pickByteH` (fixtures copied, not imported) -/

abbrev U := fun _ : Unit => defaultDomain

/-- `pickByteH`'s comb package (as Tests/Gen2/DataBridgeCheck.lean `pbhC`). -/
noncomputable def pbhC : CombPkg Unit U :=
  { decl := ``pickByteH, d := pickByteH.machineData, kD := pickByteH.machineData.bsIn.length,
    inits := pickByteH.machineInits, src := pickByteH.machineSource,
    facts := ⟨pickByteH.machine_ok, pickByteH.machine_body, pickByteH.machine_inits, pickByteH.machine_next,
      pickByteH.machine_result⟩ }

noncomputable abbrev pbhPkg : Pkg Unit U := .comb pbhC

/-- A concrete assignment: `pickByteH` ↦ its comb package, everything else ↦ none. -/
noncomputable def PL : Pkgs Unit U := fun c => if c == ``pickByteH then some pbhPkg else none

theorem pickByteH_beq : ((``pickByteH : Lean.Name) == ``pickByteH) = true := by
  first | decide | rfl

theorem PL_pbh : PL ``pickByteH = some pbhPkg := by
  show (if ((``pickByteH : Lean.Name) == ``pickByteH) = true then some pbhPkg else none) = some pbhPkg
  rw [if_pos pickByteH_beq]

set_option maxRecDepth 100000

theorem callerL_hk : 0 < callerL.machineData.shape.insts.length := by
  first | decide | decide +kernel

theorem callerL_noFields : callerL.machineData.shape.instFields = [] := by
  first | rfl | decide | decide +kernel

theorem callerL_inst0 : (callerL.machineData.shape.insts[0]'callerL_hk).1 = ``pickByteH := by
  first | decide | decide +kernel

theorem hk0 (p : Pkg Unit U) (hp : p.d = callerL.machineData) : 0 < p.d.shape.insts.length := by
  rw [hp]; exact callerL_hk

theorem insts0_name (p : Pkg Unit U) (hp : p.d = callerL.machineData) :
    (p.d.shape.insts[0]'(hk0 p hp)).1 = ``pickByteH := by
  have key : ∀ (d : Tools.ShippingMachineAuto.MachineData) (hd : d = callerL.machineData)
      (h : 0 < d.shape.insts.length), (d.shape.insts[0]'h).1 = ``pickByteH := by
    intro d hd h
    subst hd
    exact callerL_inst0
  exact key p.d hp (hk0 p hp)

/-- `hP` of (2) at `callerL`'s call 0 under `PL`, for every package with `callerL`'s data (decided). -/
theorem callerL_hP (p : Pkg Unit U) (hp : p.d = callerL.machineData) :
    PL (p.d.shape.insts[0]'(hk0 p hp)).1 = some pbhPkg := by
  rw [insts0_name p hp]; exact PL_pbh

/-- **Positive (application of (2))**: on a one-output parent, `HPointG` is `CallOutF` on the decoded families. -/
theorem callerL_dec (p : Pkg Unit U) (hp : p.d = callerL.machineData) :
    HPointG PL p pbhPkg 0 ↔ CallOutF p pbhPkg 0 (decA p pbhPkg 0 (hk0 p hp)) (decB p pbhPkg 0 (hk0 p hp)) :=
  hPointG_iff_callOutDec PL p pbhPkg 0 (hk0 p hp) (callerL_hP p hp)

/-- **Positive**: t2 on `callerL`'s call 0 (by definition). -/
theorem callerL_letTie (p : Pkg Unit U) (hp : p.d = callerL.machineData) :
    LetTie p pbhPkg 0 (hk0 p hp) (decA p pbhPkg 0 (hk0 p hp)) (decB p pbhPkg 0 (hk0 p hp)) :=
  letTie_dec p pbhPkg 0 (hk0 p hp)

/-- **Positive**: `CallOutF`'s selection on this parent is the one-output branch. -/
theorem callerL_callField (p : Pkg Unit U) (hp : p.d = callerL.machineData) (o : Sparkle.IR.Machine.OutField) :
    CallField p pbhPkg 0 o ↔ pbhPkg.d.shape.layout.outs = [o] :=
  callField_one (by rw [hp]; exact callerL_noFields)

/-- **Negative for (3)**: the group premise `hG` is false on this parent, so (3) does not apply; (2) does. -/
theorem callerL_not_group (p : Pkg Unit U) (hp : p.d = callerL.machineData) :
    ¬ (p.d.shape.instFields ≠ []) :=
  fun h => h (by rw [hp]; exact callerL_noFields)

/-! ## 3. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``decA, ``decB, ``CallOutF, ``letTie_dec, ``pkgBsC_of, ``pkgOutsC_of, ``pkgSrc_of,
      ``hPointG_iff_callOutG, ``hPointG_iff_callOutDec, ``hPointAt_iff_callOutDec,
      ``PL_pbh, ``callerL_hk, ``callerL_noFields, ``callerL_inst0, ``hk0, ``insts0_name, ``callerL_hP,
      ``callerL_dec, ``callerL_letTie, ``callerL_callField, ``callerL_not_group] do
    checkAxioms n

#print axioms hPointG_iff_callOutG
#print axioms hPointG_iff_callOutDec
#print axioms hPointAt_iff_callOutDec
#print axioms letTie_dec
#print axioms callerL_dec
#print axioms callerL_not_group

end Tests.Gen5.T2DecCheck
