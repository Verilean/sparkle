import Tools.ShippingGen5DataOfComplete
import Tests.Gen5.DataOfCheck
import Tests.Gen3.ExpectedType
set_option autoImplicit false
set_option linter.unusedVariables false
-- NOT BUILT by an issue-linked clean build (agent build only; the clean build is the coder's). No sorry / axiom / native_decide.
-- (G6 checks for Tools/ShippingGen5DataOfComplete.lean; scripts/gen5/DG_G6_COMPLETE_FREEZE.md.)

/-! # G6 `dataOfFrom_complete_of_quote` checks

1. TYPE: statements against independently written `Prop`s (written from the freeze md, not copied from the Lean statements).
2. MUTANT: dropped hypotheses / changed conjuncts are rejected by the SAME comparison (signature / defeq rejections, NOT semantic counterexamples).
3. Value closure by the common `Tests.Gen5.DataOfCheck.reach` (unknown names fail), with positive and negative controls. 4. Axioms.
Not checked: that any `d` satisfying the hypotheses exists (G8 / G9), that `dataOfAt` is `some` on a run. -/

namespace Tests.Gen5.DataOfCompleteCheck
open Lean Meta
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineCommand
open Tools.ShippingMachineEntry Tools.ShippingReaderInputs Tools.ShippingReaderMachine
open Tools.ShippingGen5DataOfPure Tools.ShippingGen5DataOf Tools.ShippingGen5ReadKinds
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Sparkle.Compiler.Elab Sparkle.IR.Machine
open Tests.Gen3.ExpectedType

/-! ## 1. Expected types, 2. mutant statements -/

def ExpComplete : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutDropFront : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutDropShape : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutDropOk : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutDropB : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutDropV : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutDropW : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutDropQ : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutDropLvl : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutDropSs : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutDropLs : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutDropOuts : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets),
    dataOfFrom lvl E senv shape tin fl = some d

def MutLvlGe : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : lvl shape.body ≤ liftDepth d.packed) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutSlotsLets : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.lets) (hls : d.ls.length = shape.layout.slots.length) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutOutsBits : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (.bits o.width) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def MutConclNone : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = none

def MutConclOtherNIn : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posB 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    (dataOfFrom lvl E senv shape tin fl).map (·.nIn) = some (d.nIn + 1)

def MutBposSwap : Prop :=
  ∀ (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData},
    ∀ (hfront : dataOfFront E senv shape tin fl = some (d.nIn, d.dom)) (hshape : d.shape = shape) (hok : d.ok = true) (hb : d.bposL = posV 0 (kindsOf d)) (hv : d.vposL = posV 0 (kindsOf d)) (hw : d.vwL = widV (kindsOf d)) (hq : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed) (hlvl : liftDepth d.packed ≤ lvl shape.body) (hss : d.ss.length = shape.layout.slots.length) (hls : d.ls.length = shape.layout.lets) (houts : Zip₂ (fun (o : OutField) (t : Σ s : SType, Term s) => sortOf (outKind o) = some t.1)
      shape.layout.outs d.outs),
    dataOfFrom lvl E senv shape tin fl = some d

def ExpSplitLetsPack : Prop :=
  ∀ (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c)),
    splitLets fs.length (packLets fs core) = some (fs, ⟨c, core⟩)

def ExpSplitFieldsPack : Prop :=
  ∀ (fs : List (Σ w : Nat, Term (.bits w))) (h : 0 < fs.length), splitFields fs.length (packAll fs) = some fs

def ExpUnFieldToField : Prop :=
  ∀ {k : MixedGateBinder} {s : SType} (t : Term s) (h : sortOf k = some s), unField k (toField s t) = some ⟨s, t⟩

def ExpTypedFields : Prop :=
  ∀ {ks : List MixedGateBinder} {ts : List (Σ s : SType, Term s)},
    ∀ (h : Zip₂ (fun k t => sortOf k = some t.1) ks ts),
    typedFields ks (ts.map fun t => toField t.1 t.2) = some ts

def ExpAnyTermsSorts : Prop :=
  ∀ {ss : List SType} (ts : Terms ss), (anyTerms ts).map (·.1) = ss

def ExpAnyTermsHeq : Prop :=
  ∀ {ss : List SType} (ts : Terms ss), HEq (termsOfAny (anyTerms ts)) ts

def MutSplitLetsLen : Prop :=
  ∀ (fs : List (Σ w : Nat, Term (.bits w))) {c : Nat} (core : Term (.bits c)),
    splitLets (fs.length + 1) (packLets fs core) = some (fs, ⟨c, core⟩)

def MutSplitFieldsNoPos : Prop :=
  ∀ (fs : List (Σ w : Nat, Term (.bits w))), splitFields fs.length (packAll fs) = some fs

def MutUnFieldNoSort : Prop :=
  ∀ {k : MixedGateBinder} {s : SType} (t : Term s), unField k (toField s t) = some ⟨s, t⟩

def MutTypedFieldsRev : Prop :=
  ∀ {ks : List MixedGateBinder} {ts : List (Σ s : SType, Term s)},
    Zip₂ (fun k t => sortOf k = some t.1) ks ts →
    typedFields ks (ts.map fun t => toField t.1 t.2) = some ts.reverse

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``dataOfFrom_complete_of_quote ``ExpComplete
  checkExpected ``splitLets_pack ``ExpSplitLetsPack
  checkExpected ``splitFields_pack ``ExpSplitFieldsPack
  checkExpected ``unField_toField ``ExpUnFieldToField
  checkExpected ``typedFields_of_quote_fields ``ExpTypedFields
  checkExpected ``anyTerms_sorts ``ExpAnyTermsSorts
  checkExpected ``anyTerms_heq ``ExpAnyTermsHeq
  logInfo m!"G6 COMPLETE TYPE: 7 theorems checked against independent Props"

run_cmd Lean.Elab.Command.liftTermElabM do
  let tm : List (Name × Name) := [(``dataOfFrom_complete_of_quote, ``MutDropFront), (``dataOfFrom_complete_of_quote, ``MutDropShape), (``dataOfFrom_complete_of_quote, ``MutDropOk), (``dataOfFrom_complete_of_quote, ``MutDropB), (``dataOfFrom_complete_of_quote, ``MutDropV), (``dataOfFrom_complete_of_quote, ``MutDropW), (``dataOfFrom_complete_of_quote, ``MutDropQ), (``dataOfFrom_complete_of_quote, ``MutDropLvl), (``dataOfFrom_complete_of_quote, ``MutDropSs), (``dataOfFrom_complete_of_quote, ``MutDropLs), (``dataOfFrom_complete_of_quote, ``MutDropOuts), (``dataOfFrom_complete_of_quote, ``MutLvlGe), (``dataOfFrom_complete_of_quote, ``MutSlotsLets), (``dataOfFrom_complete_of_quote, ``MutOutsBits), (``dataOfFrom_complete_of_quote, ``MutConclNone), (``dataOfFrom_complete_of_quote, ``MutConclOtherNIn), (``dataOfFrom_complete_of_quote, ``MutBposSwap), (``splitLets_pack, ``MutSplitLetsLen), (``splitFields_pack, ``MutSplitFieldsNoPos), (``unField_toField, ``MutUnFieldNoSort), (``typedFields_of_quote_fields, ``MutTypedFieldsRev)]
  for (t, m) in tm do checkMutant t m
  logInfo m!"G6 COMPLETE COUNTS: TYPE 7 theorems; MUTANT {tm.length} total (main 17, aux 4), each one well-typed change rejected by signature/defeq comparison, NOT a semantic counterexample; includes one dropped-hypothesis mutant per hypothesis (hfront hshape hok hb hv hw hq hlvl hss hls houts)."

/-! ## 3. Value closure -/

open Tests.Gen5.DataOfCheck in
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  unless badProj (.proj `Tools.ShippingGen2.T1Hyp 3 (.bvar 0)) do throwError "G6 AUDIT FAILED: raw T1Hyp proj missed"
  let F := `Tests.Gen5.DataOfFixture
  for (c, bad) in [(F ++ `badDec, true), (F ++ `badNDCases, true), (F ++ `badEqual, true), (F ++ `unrelated, false)] do
    let r ← reach c
    if bad && r.hit.isNone then throwError "G6 AUDIT FAILED: detector misses {c}"
    if !bad && r.hit.isSome then throwError "G6 AUDIT FAILED: detector flags {c}"
    logInfo m!"G6 CONTROL {c}: {toString r.hit}"
  for c in [``dataOfFrom_complete_of_quote, ``splitLets_pack, ``splitFields_pack, ``unField_toField,
      ``typedFields_of_quote_fields, ``anyTerms_sorts, ``anyTerms_heq, ``dataOfTail_complete, ``mkData_eta] do
    let r ← reach c
    if let some p := r.hit then throwError "G6 AUDIT FAILED {c}: forbidden use via {p}"
    logInfo m!"G6 REACH {c}: no T1Hyp / T1HypND / Expr.equal / Expr.eqv / ofReduceBool; visited {r.visited}, body-less {r.noBody}, opaque {r.opaques} {r.opaqueNames}"

/-! ## 4. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let ns : List Name := [``dataOfFrom_complete_of_quote, ``splitLets_pack, ``splitFields_pack, ``unField_toField,
      ``typedFields_of_quote_fields, ``anyTerms_sorts, ``anyTerms_heq, ``dataOfTail_complete, ``mkData_eta]
  for n in ns do checkAxioms n
  logInfo m!"G6 COMPLETE AXIOMS OK: {ns.length} roots, standard axioms only"

end Tests.Gen5.DataOfCompleteCheck
