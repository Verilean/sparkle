import Tools.ShippingGen5T2Tie
import Tests.Gen3.ExpectedType
import Tests.Compiler.ShippingMachineLinkedTest
set_option autoImplicit false
-- NOT BUILT: written without running lake/lean (issue `sparkle-gen5-t2-tie`). Unverified until the coordinator's
-- build. No sorry / axiom / native_decide.

/-! # T2-POSENC / T2-FIELD / T2-TIE / T2-STEP checks (issue `sparkle-gen5-t2-tie`; Tools/ShippingGen5T2Tie.lean)

Design source: scripts/gen5/T2COVER_FREEZE.md rev2 §1, §3, §5 and scripts/gen5/DGEN_FREEZE.md rev2 (`par/gen5-t2`
c398021c). Design-to-code only. The T2-TIE / T2-STEP statements are CONDITIONAL on named D-GEN / M3 hypotheses
(`hDG_SEM`, `hDG_SEM_range`, `hDG_GENP`, `hDG_CLOSINGRUN`, `hDG_PKGASSIGN`, `hG_DATA_CALL_*`, `hG_MEMCALLS`); nothing
here supplies them. Not the FG; DG-HPOINT and the final closure audit remain.

1. **Expected types** (mechanical, `Tests.Gen3.ExpectedType.checkExpected`) against independent `Expected…`
   statements, and **mutants** that must be rejected (`checkMutant`; signature / defeq rejections, not all semantic
   counterexamples). The pattern-matching definitions `SigAt` / `OutRange` are checked by their equations (`Iff.rfl`).
2. **Controls**: (a) T2-POSENC on a concrete `extendBits` chain (a placement at another position is skipped) and a
   NEGATIVE control (an out-of-range stream is NOT decoded back: the range row is necessary); (b) T2-FIELD data on the
   one-output parent `callerL` → `pickByteH` (fixtures copied from Tests/Gen5/T2DecCheck.lean, not imported): the
   callee has one output, so `CallField`'s witnesses exist statically, and `FieldRowAt` reads its one-output branch;
   (c) an application of `hPointG_of_callTie` at `callerL`'s call 0 under `PL` (CONDITIONAL on a `CallTie` argument;
   no tie is supplied).
3. Axioms. -/

namespace Tests.Gen5.T2TieCheck
open Tools.ShippingGen2
open Tests.Gen3.ExpectedType
open Sparkle.Tests.Compiler.ShippingMachineLinkedTest
open Sparkle.Core.Domain

section Expected
open Sparkle.Core Sparkle.Core.Signal

/-! ## 1a. T2-POSENC -/

theorem sigAt_bits_iff {D : DomainConfig} (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (pos w : Nat) (f : Nat → Nat) :
    SigAt bools bits pos (.bits w) f ↔ ∀ τ, (bits pos w).val τ = BitVec.ofNat w (f τ) := Iff.rfl

theorem sigAt_bool_iff {D : DomainConfig} (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (pos : Nat) (f : Nat → Nat) :
    SigAt bools bits pos .bool f ↔ ∀ τ, (bools pos).val τ = (f τ != 0) := Iff.rfl

theorem sigAt_domain_iff {D : DomainConfig} (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (pos : Nat) (f : Nat → Nat) :
    SigAt bools bits pos .domain f ↔ False := Iff.rfl

theorem outRange_bits_iff (w : Nat) (f : Nat → Nat) : OutRange (.bits w) f ↔ ∀ τ, f τ < 2 ^ w := Iff.rfl
theorem outRange_bool_iff (f : Nat → Nat) : OutRange .bool f ↔ ∀ τ, f τ < 2 := Iff.rfl

def ExpectedPosEncOfSigAt : Prop :=
  ∀ {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (pos : Nat) (κ : Sparkle.Compiler.Elab.MixedGateBinder) (f : Nat → Nat)
    (hs : SigAt bools bits pos κ f) (hr : OutRange κ f),
    ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (bools r).val τ) (fun r n => (bits r n).val τ) pos κ = f τ

/-- Mutant: no range row. -/
def MutPosEncNoRange : Prop :=
  ∀ {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (pos : Nat) (κ : Sparkle.Compiler.Elab.MixedGateBinder) (f : Nat → Nat)
    (hs : SigAt bools bits pos κ f),
    ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (bools r).val τ) (fun r n => (bits r n).val τ) pos κ = f τ

/-- Mutant: decoded at the next position. -/
def MutPosEncShift : Prop :=
  ∀ {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (pos : Nat) (κ : Sparkle.Compiler.Elab.MixedGateBinder) (f : Nat → Nat)
    (hs : SigAt bools bits pos κ f) (hr : OutRange κ f),
    ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (bools r).val τ) (fun r n => (bits r n).val τ) (pos + 1) κ = f τ

def ExpectedExtendBitsSelf : Prop :=
  ∀ {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (pos w : Nat) (f : Nat → Nat),
    SigAt bools (Tools.ShippingMachineAuto.extendBits bits pos w ⟨fun τ => BitVec.ofNat w (f τ)⟩) pos (.bits w) f

def ExpectedExtendBitsNe : Prop :=
  ∀ {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    {pos pos' w : Nat} (sig : Signal D (BitVec w)) (h : pos ≠ pos') (κ : Sparkle.Compiler.Elab.MixedGateBinder)
    (f : Nat → Nat),
    SigAt bools (Tools.ShippingMachineAuto.extendBits bits pos' w sig) pos κ f ↔ SigAt bools bits pos κ f

/-- Mutant: no `pos ≠ pos'` (false at `pos = pos'`). -/
def MutExtendBitsNeNoH : Prop :=
  ∀ {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    {pos pos' w : Nat} (sig : Signal D (BitVec w)) (κ : Sparkle.Compiler.Elab.MixedGateBinder)
    (f : Nat → Nat),
    SigAt bools (Tools.ShippingMachineAuto.extendBits bits pos' w sig) pos κ f ↔ SigAt bools bits pos κ f

def ExpectedExtendBoolsNe : Prop :=
  ∀ {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    {pos pos' : Nat} (sig : Signal D Bool) (h : pos ≠ pos') (κ : Sparkle.Compiler.Elab.MixedGateBinder)
    (f : Nat → Nat),
    SigAt (Tools.ShippingMachineCausal.extendBools bools pos' sig) bits pos κ f ↔ SigAt bools bits pos κ f

def ExpectedPosEncCallPos : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (k : Nat) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (f : Nat → Nat)
    (hs : SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
      (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f)
    (hr : OutRange (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f),
    ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (p.extBS i bools bits r).val τ)
      (fun r n => (p.extS i bools bits r n).val τ)
      (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

/-- Mutant: the call position without the `kD` offset. -/
def MutPosEncCallPosNoOffset : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (k : Nat) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (f : Nat → Nat)
    (hs : SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
      (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f)
    (hr : OutRange (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f),
    ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (p.extBS i bools bits r).val τ)
      (fun r n => (p.extS i bools bits r n).val τ)
      k (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

/-! ## 1b. T2-FIELD -/

def ExpectedFieldRowAt {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (k : Nat)
    (mc : Sparkle.IR.AST.Module) : Prop :=
  if p.d.shape.instFields = [] then ∃ outP, mc.outputs = [outP]
  else p.d.shape.instFields.getD k "" ∈ mc.outputs.map (·.name)

/-- Mutant: the rev0 `∨` form (accepts a several-output module through either branch). -/
def MutFieldRowAtOr {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (k : Nat)
    (mc : Sparkle.IR.AST.Module) : Prop :=
  (∃ outP, mc.outputs = [outP]) ∨ p.d.shape.instFields.getD k "" ∈ mc.outputs.map (·.name)

def ExpectedCallFieldOfOutputs : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (mc : Sparkle.IR.AST.Module)
    (hout : mc.outputs = q.d.shape.layout.outs.map (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)))
    (hrow : FieldRowAt p k mc),
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o

/-- Mutant: no output-shape premise (the child's `ChildShips` is what supplies it). -/
def MutCallFieldOfOutputsNoOut : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (mc : Sparkle.IR.AST.Module)
    (hrow : FieldRowAt p k mc),
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o

def ExpectedCallFieldAt : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (c : Lean.Name) (r : Tools.ShippingChildInv.Res) (hS : ShipsRes L P c r) (hq : P c = some q)
    (dsn : Sparkle.IR.AST.Design)
    (hDc : ∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g)
    (hmc : Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1)
    (hrow : FieldRowAt p k r.1) (i : ι),
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o

/-- Mutant: without the served child's `ShipsRes` (the children's IH). -/
def MutCallFieldAtNoShips : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (c : Lean.Name) (r : Tools.ShippingChildInv.Res) (hq : P c = some q)
    (dsn : Sparkle.IR.AST.Design)
    (hDc : ∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g)
    (hmc : Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1)
    (hrow : FieldRowAt p k r.1) (i : ι),
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o

/-- Mutant: `i`-free (would need `Nonempty ι`, which is NOT added). -/
def MutCallFieldAtNoI : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (c : Lean.Name) (r : Tools.ShippingChildInv.Res) (hS : ShipsRes L P c r) (hq : P c = some q)
    (dsn : Sparkle.IR.AST.Design)
    (hDc : ∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g)
    (hmc : Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1)
    (hrow : FieldRowAt p k r.1),
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o

/-! ## 1c. T2-TIE (conditional) -/

def ExpectedCallTie {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) : Prop :=
  LetTie p q k hk (decA p q k hk) (Tools.ShippingGen2.decB p q k hk) ∧
    CallOutF p q k (decA p q k hk) (Tools.ShippingGen2.decB p q k hk)

/-- Mutant: the parent's own families (decoded as if the parent were the callee). -/
def MutCallTieParentFam {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) : Prop :=
  LetTie p q k hk (decA p p k hk) (Tools.ShippingGen2.decB p p k hk) ∧
    CallOutF p q k (decA p p k hk) (Tools.ShippingGen2.decB p p k hk)

/-- Mutant: `CallOutF` only (no t2). -/
def MutCallTieNoLet {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) : Prop :=
  CallOutF p q k (decA p q k hk) (Tools.ShippingGen2.decB p q k hk)

def ExpectedGenExtAtCall {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → CallField p q k o →
    (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f →
    SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
      (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f

/-- Mutant: the callee's source on the RAW parent inputs instead of the decoded families. -/
def MutGenExtAtCallRaw {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → CallField p q k o →
    (q.src i bools bits)[k']? = some f →
    SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
      (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f

def ExpectedCallOutRange {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → CallField p q k o →
    (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f →
    OutRange (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f

def ExpectedCallTieOfDgen : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o)
    (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

/-- Mutant: without the range row. -/
def MutCallTieOfDgenNoRange : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o)
    (hDG_SEM : GenExtAtCall p q k hk),
    CallTie p q k hk

/-- Mutant: without the field. -/
def MutCallTieOfDgenNoField : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

def ExpectedCallTieOfServed : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

/-- Mutant: without the field row in the served block. -/
def MutCallTieOfServedNoRow : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1)
    (hDG_SEM : GenExtAtCall p q k hk) (hDG_SEM_range : CallOutRange p q k hk),
    CallTie p q k hk

def ExpectedHPointGOfCallTie : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]'hk).1 = some q) (hT : CallTie p q k hk),
    HPointG P p q k

/-- Mutant: without `hP`. -/
def MutHPointGOfCallTieNoHP : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hT : CallTie p q k hk),
    HPointG P p q k

/-! ## 1d. T2-STEP (conditional) -/

def ExpectedCallDecOfCallTie : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : CallTie p q k hk)
    (hG_DATA_CALL_co : p.d.callsOk p.kD = true)
    (hG_DATA_CALL_slots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hG_DATA_CALL_args : callArgsOkAt p.d p.kD k q.portWidths = true)
    (hG_DATA_CALL_len : (p.d.shape.insts[k]'hk).2.1.length = q.ports.length),
    CallDec p q k

/-- Mutant: without `hnone` (memory entries are not ordinary calls). -/
def MutCallDecOfCallTieNoNone : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length)
    (hP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hT : CallTie p q k hk)
    (hG_DATA_CALL_co : p.d.callsOk p.kD = true)
    (hG_DATA_CALL_slots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hG_DATA_CALL_args : callArgsOkAt p.d p.kD k q.portWidths = true)
    (hG_DATA_CALL_len : (p.d.shape.insts[k]'hk).2.1.length = q.ports.length),
    CallDec p q k

def ExpectedStepDecOfTies : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom)
    (hDG_PKGASSIGN : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∃ q, P (p.d.shape.insts[k]).1 = some q)
    (hT2_TIE : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q, P (p.d.shape.insts[k]).1 = some q → CallTie p q k hk)
    (hG_DATA_CALL_co : p.d.callsOk p.kD = true)
    (hG_DATA_CALL_slots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hG_DATA_CALL_args : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q, P (p.d.shape.insts[k]).1 = some q →
        callArgsOkAt p.d p.kD k q.portWidths = true ∧ (p.d.shape.insts[k]).2.1.length = q.ports.length)
    (hG_MEMCALLS : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? ≠ none →
      MemDec p k (p.d.shape.insts[k]).1),
    ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k

/-- Mutant: every entry an ordinary call (no `MemDec` branch, no `hG_MEMCALLS`). -/
def MutStepDecAllOrd : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom)
    (hDG_PKGASSIGN : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∃ q, P (p.d.shape.insts[k]).1 = some q)
    (hT2_TIE : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q, P (p.d.shape.insts[k]).1 = some q → CallTie p q k hk)
    (hG_DATA_CALL_co : p.d.callsOk p.kD = true)
    (hG_DATA_CALL_slots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hG_DATA_CALL_args : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q, P (p.d.shape.insts[k]).1 = some q →
        callArgsOkAt p.d p.kD k q.portWidths = true ∧ (p.d.shape.insts[k]).2.1.length = q.ports.length),
    ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k

/-- Mutant: without the callee assignment (`hDG_PKGASSIGN`). -/
def MutStepDecNoAssign : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom)
    (hT2_TIE : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q, P (p.d.shape.insts[k]).1 = some q → CallTie p q k hk)
    (hG_DATA_CALL_co : p.d.callsOk p.kD = true)
    (hG_DATA_CALL_slots : p.d.ss.length = p.d.shape.layout.slots.length)
    (hG_DATA_CALL_args : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? = none →
      ∀ q, P (p.d.shape.insts[k]).1 = some q →
        callArgsOkAt p.d p.kD k q.portWidths = true ∧ (p.d.shape.insts[k]).2.1.length = q.ports.length)
    (hG_MEMCALLS : ∀ k (hk : k < p.d.shape.insts.length), (p.d.shape.instOrigins.getD k .ord).child? ≠ none →
      MemDec p k (p.d.shape.insts[k]).1),
    ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k

end Expected

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``posEnc_of_sigAt ``ExpectedPosEncOfSigAt
  checkExpected ``sigAt_extendBits_self ``ExpectedExtendBitsSelf
  checkExpected ``sigAt_extendBits_ne ``ExpectedExtendBitsNe
  checkExpected ``sigAt_extendBools_ne ``ExpectedExtendBoolsNe
  checkExpected ``posEnc_callPos ``ExpectedPosEncCallPos
  checkExpected ``FieldRowAt ``ExpectedFieldRowAt
  checkExpected ``callField_of_outputs ``ExpectedCallFieldOfOutputs
  checkExpected ``callField_at ``ExpectedCallFieldAt
  checkExpected ``CallTie ``ExpectedCallTie
  checkExpected ``GenExtAtCall ``ExpectedGenExtAtCall
  checkExpected ``CallOutRange ``ExpectedCallOutRange
  checkExpected ``callTie_of_dgen ``ExpectedCallTieOfDgen
  checkExpected ``callTie_of_served ``ExpectedCallTieOfServed
  checkExpected ``hPointG_of_callTie ``ExpectedHPointGOfCallTie
  checkExpected ``callDec_of_callTie ``ExpectedCallDecOfCallTie
  checkExpected ``stepDec_of_ties ``ExpectedStepDecOfTies
  checkMutant ``posEnc_of_sigAt ``MutPosEncNoRange
  checkMutant ``posEnc_of_sigAt ``MutPosEncShift
  checkMutant ``sigAt_extendBits_ne ``MutExtendBitsNeNoH
  checkMutant ``posEnc_callPos ``MutPosEncCallPosNoOffset
  checkMutant ``FieldRowAt ``MutFieldRowAtOr
  checkMutant ``callField_of_outputs ``MutCallFieldOfOutputsNoOut
  checkMutant ``callField_at ``MutCallFieldAtNoShips
  checkMutant ``callField_at ``MutCallFieldAtNoI
  checkMutant ``CallTie ``MutCallTieParentFam
  checkMutant ``CallTie ``MutCallTieNoLet
  checkMutant ``GenExtAtCall ``MutGenExtAtCallRaw
  checkMutant ``callTie_of_dgen ``MutCallTieOfDgenNoRange
  checkMutant ``callTie_of_dgen ``MutCallTieOfDgenNoField
  checkMutant ``callTie_of_served ``MutCallTieOfServedNoRow
  checkMutant ``hPointG_of_callTie ``MutHPointGOfCallTieNoHP
  checkMutant ``callDec_of_callTie ``MutCallDecOfCallTieNoNone
  checkMutant ``stepDec_of_ties ``MutStepDecAllOrd
  checkMutant ``stepDec_of_ties ``MutStepDecNoAssign
  -- harness sanity: a mutant is also distinct from its expected statement
  checkMutant ``ExpectedStepDecOfTies ``MutStepDecAllOrd

/-! ## 2a. T2-POSENC controls (concrete `extendBits` chain on `defaultDomain`) -/

section PosEncControl
open Sparkle.Core Sparkle.Core.Signal

/-- **Positive**: a call result placed at position 3 (width 8), then another placement at position 5, decodes back
at 3 to its in-range stream. -/
theorem posEnc_chain_control (bools : Nat → Signal defaultDomain Bool)
    (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n)) (sig5 : Signal defaultDomain (BitVec 4)) :
    ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (bools r).val τ)
      (fun r n => (Tools.ShippingMachineAuto.extendBits
        (Tools.ShippingMachineAuto.extendBits bits 3 8 ⟨fun τ => BitVec.ofNat 8 ((fun t => t % 256) τ)⟩)
        5 4 sig5 r n).val τ) 3 (.bits 8) = (fun t => t % 256) τ := by
  have hs : SigAt bools (Tools.ShippingMachineAuto.extendBits
      (Tools.ShippingMachineAuto.extendBits bits 3 8 ⟨fun τ => BitVec.ofNat 8 ((fun t => t % 256) τ)⟩)
      5 4 sig5) 3 (.bits 8) (fun t => t % 256) :=
    (sigAt_extendBits_ne bools _ sig5 (by decide) (.bits 8) (fun t => t % 256)).mpr
      (sigAt_extendBits_self bools bits 3 8 (fun t => t % 256))
  have hr : OutRange (.bits 8) (fun t => t % 256) := by
    intro τ
    show τ % 256 < 256
    exact Nat.mod_lt τ (by decide)
  exact posEnc_of_sigAt bools _ 3 (.bits 8) (fun t => t % 256) hs hr

/-- **Negative**: an out-of-range stream (`256` at width 8) is NOT decoded back; the range row is necessary. -/
theorem posEnc_range_needed (bools : Nat → Signal defaultDomain Bool)
    (bits : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n)) :
    ¬ ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (bools r).val τ)
      (fun r n => (Tools.ShippingMachineAuto.extendBits bits 3 8
        ⟨fun τ => BitVec.ofNat 8 ((fun _ => 256) τ)⟩ r n).val τ) 3 (.bits 8) = 256 := by
  intro h
  have h0 := h 0
  have e : (Tools.ShippingMachineAuto.extendBits bits 3 8
      ⟨fun τ => BitVec.ofNat 8 ((fun _ => 256) τ)⟩ 3 8).val 0 = BitVec.ofNat 8 ((fun _ => 256) 0) :=
    sigAt_extendBits_self bools bits 3 8 (fun _ => 256) 0
  have h1 : ((Tools.ShippingMachineAuto.extendBits bits 3 8
      ⟨fun τ => BitVec.ofNat 8 ((fun _ => 256) τ)⟩ 3 8).val 0).toNat = 256 := h0
  rw [e] at h1
  exact absurd h1 (by decide)

end PosEncControl

/-! ## 2b. T2-FIELD data control: one-output `callerL` → `pickByteH` (fixtures copied from T2DecCheck) -/

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

theorem callerL_hP (p : Pkg Unit U) (hp : p.d = callerL.machineData) :
    PL (p.d.shape.insts[0]'(hk0 p hp)).1 = some pbhPkg := by
  rw [insts0_name p hp]; exact PL_pbh

/-- `pickByteH` has exactly one layout output (decided). -/
theorem pbh_outs_len : pbhPkg.d.shape.layout.outs.length = 1 := by
  first | decide | decide +kernel | rfl

theorem single_of_length_one {α : Type} : ∀ (L : List α), L.length = 1 → ∃ a, L = [a]
  | [], h => by simp only [List.length_nil] at h; omega
  | [a], _ => ⟨a, rfl⟩
  | _ :: _ :: _, h => by simp only [List.length_cons] at h; omega

/-- **Positive (static data)**: on `callerL`'s call 0, `CallField`'s witnesses exist for the callee `pickByteH`
(one-output branch, `k' = 0`). Static only: no run, no `ChildShips`. -/
theorem callerL_pbh_field (p : Pkg Unit U) (hp : p.d = callerL.machineData) :
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), pbhPkg.d.shape.layout.outs[k']? = some o ∧
      CallField p pbhPkg 0 o := by
  obtain ⟨o, ho⟩ := single_of_length_one _ pbh_outs_len
  exact ⟨0, o, by rw [ho] <;> rfl,
    (callField_one (p := p) (q := pbhPkg) (k := 0) (o := o) (by rw [hp]; exact callerL_noFields)).mpr ho⟩

/-- **Positive**: on `callerL`, the field row is the one-output branch. -/
theorem callerL_fieldRow (p : Pkg Unit U) (hp : p.d = callerL.machineData) (mc : Sparkle.IR.AST.Module) :
    FieldRowAt p 0 mc ↔ ∃ outP, mc.outputs = [outP] := by
  have h1 : p.d.shape.instFields = [] := by rw [hp]; exact callerL_noFields
  unfold FieldRowAt
  rw [if_pos h1]

/-! ## 2c. Conditional application at `callerL`'s call 0 -/

/-- **Application (CONDITIONAL on a `CallTie` argument; none is supplied)**: a tie at `callerL`'s call 0 gives
`HPointG` under `PL`. -/
theorem callerL_hPoint_of_tie (p : Pkg Unit U) (hp : p.d = callerL.machineData)
    (hT : CallTie p pbhPkg 0 (hk0 p hp)) : HPointG PL p pbhPkg 0 :=
  hPointG_of_callTie PL p pbhPkg 0 (hk0 p hp) (callerL_hP p hp) hT

/-! ## 3. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``posEnc_of_sigAt, ``sigAt_extendBits_self, ``sigAt_extendBools_self, ``sigAt_extendBits_ne,
      ``sigAt_extendBools_ne, ``posEnc_callPos, ``childRunN_outputs, ``fieldRow_one_of_callStmt,
      ``callField_of_outputs, ``callField_at, ``callTie_of_dgen, ``callTie_of_served, ``hPointG_of_callTie,
      ``callDec_of_callTie, ``stepDec_of_ties,
      ``sigAt_bits_iff, ``sigAt_bool_iff, ``sigAt_domain_iff, ``outRange_bits_iff, ``outRange_bool_iff,
      ``posEnc_chain_control, ``posEnc_range_needed, ``pbh_outs_len, ``callerL_pbh_field, ``callerL_fieldRow,
      ``callerL_hPoint_of_tie] do
    checkAxioms n

#print axioms callTie_of_served
#print axioms stepDec_of_ties
#print axioms posEnc_chain_control
#print axioms posEnc_range_needed
#print axioms callerL_pbh_field

end Tests.Gen5.T2TieCheck
