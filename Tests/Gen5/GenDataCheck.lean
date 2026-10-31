import Tools.ShippingGen5SemGenData
import Tests.Gen5.SemFactsCheck
set_option autoImplicit false
-- NOT BUILT HERE (U8 check, scripts/gen5/DG_SEM_FREEZE_P8.md §3.2; incremental Pod build of this tree at d8ddd8f2: Tests.Gen5.GenDataCheck exit 0 (719 jobs); clean build is the coder's). No sorry/axiom/native_decide.
/-! # DG-SEM U8 check (Tools/ShippingGen5SemGenData.lean), plan of freeze §3.2 (after R1)

* (a) THEOREMS (5): type against an independent `Exp*` (`checkExpected`/`cmpTele`).
* (b) DEFINITIONS `DataOfSound`, `GenData.toIn`, `GenData.genSem`: VALUE comparison `checkValue` (`Expr.eqv` of `ConstantInfo.value?`
      against an independently written `Exp*` def, plus `Expr.eqv` of the types); never type alone. eqv failure is never an automatic pass:
      mutants that are defeq but not eqv are reported as "eqv-rejected, defeq-equal".
* (c) STRUCTURE `GenData`: constructor telescope (parameters, then fields `d wf hshape hdata`: names, order, binder info, dependent types)
      against `ExpGenDataMk`, plus `getStructureFields` and the result type.
* MUTANT — well-typed single changes, rejected by signature / value / telescope comparison: NOT a semantic counterexample.
* AXIOMS / CLOSURE / REACH — as in `Tests/Gen5/SemKitInvCheck.lean`; fixtures live only inside `withoutModifyingEnv`. -/
namespace Tests.Gen5.SemGenDataCheck
open Lean Meta Elab
open Tools.ShippingGen5Sem Tests.Gen3.ExpectedType Tests.Gen5.SemGenCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineAuto Tools.ShippingMachineDenote
open Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingMachineSource Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge

/-! ## Expected: theorems (type route) -/
def ExpToInD : Prop := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    {E : ConstantInfo} {senv : StructEnv} (g : GenData dataOf E senv), (g.toIn hs).d = g.d
def ExpEqVia : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E senv),
    GenData.genSem hs Q X g =
      genSemVia (fun E => GenData dataOf E senv) (fun {E} g => GenData.toIn hs g) Q X g
def ExpEvidence : Prop := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    (senv : StructEnv) (E : ConstantInfo) (g : GenData dataOf E senv),
    machineShape? false [] E senv = some g.d.shape ∧ dataOf E senv g.d.shape = some g.d

/-! ## Mutants: theorem route -/
def MutEqViaQ : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E senv),
    GenData.genSem hs Q X g =
      genSemVia (fun E => GenData dataOf E senv) (fun {E} g => GenData.toIn hs g) (fun _ => none) X g
def MutEvidenceNone : Prop := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    (senv : StructEnv) (E : ConstantInfo) (g : GenData dataOf E senv),
    machineShape? false [] E senv = some g.d.shape ∧ dataOf E senv g.d.shape = none

/-! ## Expected: definitions (value route), written from the sentences of freeze §3.1 -/
def ExpDataOfSound (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss)) : Prop :=
  ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
    dataOf E senv s = some d →
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true
def ExpToIn {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    {E : ConstantInfo} {senv : StructEnv} (g : GenData dataOf E senv) : GenIn :=
  ⟨g.d, g.wf, initsOf g.d, (hs E senv g.d.shape g.d g.hdata).2.1,
    (hs E senv g.d.shape g.d g.hdata).2.2.1, (hs E senv g.d.shape g.d g.hdata).2.2.2⟩
noncomputable def ExpGenSem {ι : Type} {dom : ι → DomainConfig} {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} {senv : StructEnv}
    (g : GenData dataOf E senv) : SemPkg ι dom :=
  genSemI Q X (GenData.toIn hs g)

/-! ## Mutants: value route (each one well-typed change; same type as the real declaration) -/
def MutDOSOk (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss)) : Prop :=
  ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
    dataOf E senv s = some d →
    d.shape = s ∧ d.ok = false ∧
    d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true
def MutDOSNoShape (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss)) : Prop :=
  ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
    dataOf E senv s = some d →
    True ∧ d.ok = true ∧
    d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true
def MutDOSInit (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss)) : Prop :=
  ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
    dataOf E senv s = some d →
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = false
/- Not counted: proof-position variants of `ok` (`id`, `Eq.mp rfl`, a `have` block) elaborate to a term Expr.eqv to the real one once the
   auxiliary `_proof_N` lemmas are inlined, so they are not mutants of the value. -/
/-- different `inits` term of the right type: `initsOf` of the shape-rebuilt data (well-typed, not defeq). -/
def MutToInInits {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    {E : ConstantInfo} {senv : StructEnv} (g : GenData dataOf E senv) : GenIn :=
  ⟨g.d, g.wf, initsOf { g.d with nIn := g.d.nIn }, (hs E senv g.d.shape g.d g.hdata).2.1,
    (hs E senv g.d.shape g.d g.hdata).2.2.1, (hs E senv g.d.shape g.d g.hdata).2.2.2⟩
noncomputable def MutGenSemQ {ι : Type} {dom : ι → DomainConfig} {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} {senv : StructEnv}
    (g : GenData dataOf E senv) : SemPkg ι dom :=
  genSemI (fun _ => none) X (GenData.toIn hs g)
noncomputable def MutGenSemX {ι : Type} {dom : ι → DomainConfig} {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} {senv : StructEnv}
    (g : GenData dataOf E senv) : SemPkg ι dom :=
  genSemI Q Name.anonymous (GenData.toIn hs g)

/-! ## Expected / mutants: `GenData.mk` telescope (parameters are implicit in the constructor) -/
def ExpGenDataMk : Type := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} {E : ConstantInfo} {senv : StructEnv}
    (d : MachineData) (wf : GenWF d = true) (hshape : machineShape? false [] E senv = some d.shape) (hdata : dataOf E senv d.shape = some d),
    GenData dataOf E senv

def MutGD_noWf : Type := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} {E : ConstantInfo} {senv : StructEnv}
    (d : MachineData) (hshape : machineShape? false [] E senv = some d.shape) (hdata : dataOf E senv d.shape = some d),
    GenData dataOf E senv

def MutGD_noShape : Type := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} {E : ConstantInfo} {senv : StructEnv}
    (d : MachineData) (wf : GenWF d = true) (hdata : dataOf E senv d.shape = some d),
    GenData dataOf E senv

def MutGD_noData : Type := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} {E : ConstantInfo} {senv : StructEnv}
    (d : MachineData) (wf : GenWF d = true) (hshape : machineShape? false [] E senv = some d.shape),
    GenData dataOf E senv

def MutGD_dataShapeShift : Type := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} {E : ConstantInfo} {senv : StructEnv}
    (d : MachineData) (wf : GenWF d = true) (hshape : machineShape? false [] E senv = some d.shape) (hdata : dataOf E senv { d.shape with instFields := ["x"] } = some d),
    GenData dataOf E senv

def MutGD_shapeNone : Type := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} {E : ConstantInfo} {senv : StructEnv}
    (d : MachineData) (wf : GenWF d = true) (hshape : machineShape? false [] E senv = none) (hdata : dataOf E senv d.shape = some d),
    GenData dataOf E senv

def MutGD_wfFalse : Type := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} {E : ConstantInfo} {senv : StructEnv}
    (d : MachineData) (wf : GenWF d = false) (hshape : machineShape? false [] E senv = some d.shape) (hdata : dataOf E senv d.shape = some d),
    GenData dataOf E senv

def MutGD_reorder : Type := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} {E : ConstantInfo} {senv : StructEnv}
    (d : MachineData) (hshape : machineShape? false [] E senv = some d.shape) (wf : GenWF d = true) (hdata : dataOf E senv d.shape = some d),
    GenData dataOf E senv

def MutGD_fieldName : Type := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} {E : ConstantInfo} {senv : StructEnv}
    (d : MachineData) (wf' : GenWF d = true) (hshape : machineShape? false [] E senv = some d.shape) (hdata : dataOf E senv d.shape = some d),
    GenData dataOf E senv

def MutGD_inlineFlag : Type := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} {E : ConstantInfo} {senv : StructEnv}
    (d : MachineData) (wf : GenWF d = true) (hshape : machineShape? true [] E senv = some d.shape) (hdata : dataOf E senv d.shape = some d),
    GenData dataOf E senv

def MutGD_binderInfo : Type := ∀ {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} (E : ConstantInfo) {senv : StructEnv}
    (d : MachineData) (wf : GenWF d = true) (hshape : machineShape? false [] E senv = some d.shape) (hdata : dataOf E senv d.shape = some d),
    GenData dataOf E senv

def MutGD_paramOrder : Type := ∀ {E : ConstantInfo} {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData} {senv : StructEnv}
    (d : MachineData) (wf : GenWF d = true) (hshape : machineShape? false [] E senv = some d.shape) (hdata : dataOf E senv d.shape = some d),
    GenData dataOf E senv

def ExpHunfGD : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), Acc R X ∧
        (∀ k ∈ ordC gd.d, R ((gd.d.shape.insts[k]).1) X) ∧ s = GenData.genSem hs G X gd),
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y

def ExpAllGD : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), Acc R X ∧
        (∀ k ∈ ordC gd.d, R ((gd.d.shape.insts[k]).1) X) ∧ s = GenData.genSem hs G X gd),
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s

/-! ## Theorem mutants (type route) -/
def MutEdgeFlipGD : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), Acc R X ∧
        (∀ k ∈ ordC gd.d, R X ((gd.d.shape.insts[k]).1)) ∧ s = GenData.genSem hs G X gd),
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y

def MutHmemNeGD : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? ≠ none)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), Acc R X ∧
        (∀ k ∈ ordC gd.d, R ((gd.d.shape.insts[k]).1) X) ∧ s = GenData.genSem hs G X gd),
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y

def MutHinvEqEmptyGD : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), Acc R X ∧
        (∀ k ∈ ordC gd.d, R ((gd.d.shape.insts[k]).1) X) ∧ s = GenData.genSem hs (fun _ => none) X gd),
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y

def MutConclEdgeGD : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), Acc R X ∧
        (∀ k ∈ ordC gd.d, R ((gd.d.shape.insts[k]).1) X) ∧ s = GenData.genSem hs G X gd),
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R Y ((g.d.shape.insts[k]).1)

def MutAllNoAccGD : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), True ∧
        (∀ k ∈ ordC gd.d, R ((gd.d.shape.insts[k]).1) X) ∧ s = GenData.genSem hs G X gd),
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s

def MutAllSrcGD : Prop := ∀ {ι : Type} {dom : ι → DomainConfig}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), Acc R X ∧
        (∀ k ∈ ordC gd.d, R ((gd.d.shape.insts[k]).1) X) ∧ s = GenData.genSem hs G X gd),
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → SrcCausal s


/-! ## Comparers -/
/-- The elaborator abstracts proof subterms into per-declaration auxiliary lemmas `<decl>._proof_N`; these are inlined (their values
substituted, recursively) so that the PROOF TERMS of the two sides are what is compared, not the auxiliary names. -/
def inlineProofs (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun x => do
    if let .const n ls := x.getAppFn then
      if let .str _ s := n then
        if s.startsWith "_proof_" then
          let ci ← getConstInfo n
          let v? : Option Expr := match ci with
            | .thmInfo t => some t.value
            | .defnInfo t => some t.value
            | _ => none
          if let some v := v? then
            return .visit ((v.instantiateLevelParams ci.levelParams ls).beta x.getAppArgs)
          throwError "GEN5 GENDATA CHECK FAILED: auxiliary lemma {n} has no value"
    return .continue)
/-- VALUE comparison: `Expr.eqv` of the types and of `ConstantInfo.value?` (auxiliary `_proof_N` lemmas inlined). Missing value or non-eqv ⇒ throws (no automatic pass). -/
def valueEqv (real exp : Name) : MetaM (Bool × Bool × Expr × Expr) := do
  let cr ← getConstInfo real
  let ce ← getConstInfo exp
  unless cr.levelParams.length == ce.levelParams.length do throwError "GEN5 GENDATA CHECK FAILED {real}: universe parameters differ from {exp}"
  let some vr := cr.value? | throwError "GEN5 GENDATA CHECK FAILED {real}: no value"
  let some ve := ce.value? | throwError "GEN5 GENDATA CHECK FAILED {exp}: no value"
  let ve := ve.instantiateLevelParams ce.levelParams (cr.levelParams.map mkLevelParam)
  let te := ce.type.instantiateLevelParams ce.levelParams (cr.levelParams.map mkLevelParam)
  let vr ← inlineProofs vr
  let ve ← inlineProofs ve
  pure (cr.type.eqv te, vr.eqv ve, vr, ve)
def checkValue (real exp : Name) : MetaM Unit := do
  let (tok, vok, vr, ve) ← valueEqv real exp
  unless tok do throwError "GEN5 GENDATA CHECK FAILED {real}: type not Expr.eqv to {exp}"
  unless vok do
    let d ← withoutModifyingState (isDefEq vr ve)
    throwError "GEN5 GENDATA CHECK FAILED {real}: value not Expr.eqv to {exp} ({if d then "defeq only" else "not defeq"}):{indentExpr vr}\nexpected{indentExpr ve}"
  logInfo m!"GEN5 GENDATA VALUE OK {real} against {exp} (types eqv, values eqv)"
/-- A value mutant must be rejected (type or value not eqv); returns whether the rejected mutant is nevertheless defeq to the real value. -/
def checkValueMutant (real mt : Name) : MetaM Bool := do
  let (tok, vok, vr, ve) ← valueEqv real mt
  if tok && vok then throwError "GEN5 GENDATA MUTANT ACCEPTED: {mt} is Expr.eqv to {real}"
  let d ← withoutModifyingState (do try isDefEq vr ve catch _ => pure false)
  logInfo m!"GEN5 GENDATA VALUE MUTANT REJECTED {mt} (against {real}; {if tok then "type eqv, value differs" else "type differs"}; {if d then "defeq-equal" else "not defeq"})"
  pure d

def ctorType (n : Name) : MetaM Expr := do return (← getConstInfo n).type
def checkCtorTele (ctor exp : Name) : MetaM Unit := do
  cmpTele s!"{ctor}" (← ctorType ctor) (← stmtOf exp)
  logInfo m!"GEN5 GENDATA CTOR OK {ctor} telescope (names, order, binder info, dependent types) against {exp}"
def checkCtorMutant (ctor mt : Name) : MetaM Unit := do
  let a ← ctorType ctor
  let e ← stmtOf mt
  let accepted ← withoutModifyingState do
    try cmpTele s!"{ctor} vs {mt}" a e; pure true catch _ => pure false
  if accepted then throwError "GEN5 GENDATA MUTANT ACCEPTED: {mt} matches the {ctor} telescope"
  logInfo m!"GEN5 GENDATA CTOR MUTANT REJECTED {mt}"

/-! ## Run -/
run_cmd Lean.Elab.Command.liftTermElabM do
  -- (a) theorems
  checkExpected ``genData_toIn_d ``ExpToInD
  checkExpected ``genData_genSem_eq_via ``ExpEqVia
  checkExpected ``genData_evidence ``ExpEvidence
  checkExpected ``hunf_of_genData ``ExpHunfGD
  checkExpected ``factsOf_all_of_genDataInv ``ExpAllGD
  logInfo m!"GEN5 GENDATA TYPE OK 5 theorems against ExpToInD, ExpEqVia, ExpEvidence, ExpHunfGD, ExpAllGD"
  -- (b) definitions by value
  checkValue ``DataOfSound ``ExpDataOfSound
  checkValue ``GenData.toIn ``ExpToIn
  checkValue ``GenData.genSem ``ExpGenSem
  logInfo m!"GEN5 GENDATA VALUE OK 3 definitions (DataOfSound, GenData.toIn, GenData.genSem) by Expr.eqv of values and types"
  -- (c) structure GenData
  checkCtorTele ``GenData.mk ``ExpGenDataMk
  let fs := getStructureFields (← getEnv) ``GenData
  unless fs == #[`d, `wf, `hshape, `hdata] do throwError "GEN5 GENDATA CHECK FAILED: GenData fields are {fs}"
  logInfo m!"GEN5 GENDATA STRUCT OK: GenData fields {fs}, constructor telescope matched"
  -- (e) positive controls: the value/ctor comparers accept the real declaration (so mutant rejection is not a vacuous failure), reject unknown names
  let t1 ← (do checkValue `Tests.Gen5.SemGenDataCheck.NoSuchConstant ``ExpToIn; pure false) <|> pure true
  unless t1 do throwError "GEN5 GENDATA CONTROL FAILED: checkValue on an unknown constant did not throw"
  let t2 ← (do checkCtorTele `Tests.Gen5.SemGenDataCheck.NoSuchCtor ``ExpGenDataMk; pure false) <|> pure true
  unless t2 do throwError "GEN5 GENDATA CONTROL FAILED: checkCtorTele on an unknown constant did not throw"
  logInfo m!"GEN5 GENDATA CONTROLS OK: comparers accept the real declarations and throw on unknown constants"

run_cmd Lean.Elab.Command.liftTermElabM do
  -- theorem mutants (type route)
  let tm : List (Name × Name) :=
    [(``genData_genSem_eq_via, ``MutEqViaQ),
     (``genData_evidence, ``MutEvidenceNone),
     (``hunf_of_genData, ``MutEdgeFlipGD),
     (``hunf_of_genData, ``MutHmemNeGD),
     (``hunf_of_genData, ``MutHinvEqEmptyGD),
     (``hunf_of_genData, ``MutConclEdgeGD),
     (``factsOf_all_of_genDataInv, ``MutAllNoAccGD),
     (``factsOf_all_of_genDataInv, ``MutAllSrcGD)]
  for (t, m) in tm do checkMutant t m
  -- value mutants (definitions)
  let vm : List (Name × Name) :=
    [(``DataOfSound, ``MutDOSOk), (``DataOfSound, ``MutDOSNoShape), (``DataOfSound, ``MutDOSInit),
     (``GenData.toIn, ``MutToInInits),
     (``GenData.genSem, ``MutGenSemQ), (``GenData.genSem, ``MutGenSemX)]
  let mut defeqOnly : List Name := []
  for (r, m) in vm do
    if ← checkValueMutant r m then defeqOnly := defeqOnly ++ [m]
  -- GenData constructor-telescope mutants
  let cm : List Name :=
    [``MutGD_noWf, ``MutGD_noShape, ``MutGD_noData, ``MutGD_dataShapeShift, ``MutGD_shapeNone, ``MutGD_wfFalse,
     ``MutGD_reorder, ``MutGD_fieldName, ``MutGD_inlineFlag, ``MutGD_binderInfo, ``MutGD_paramOrder]
  for m in cm do checkCtorMutant ``GenData.mk m
  logInfo m!"GEN5 GENDATA COUNTS: TYPE 5 theorems; MUTANT {tm.length + vm.length + cm.length} total = theorem {tm.length} + value {vm.length} + GenData telescope {cm.length}; \
    required controls present: wf dropped (MutGD_noWf), hshape dropped (MutGD_noShape), hdata shape shifted by a MachineShape-typed term (MutGD_dataShapeShift), DataOfSound ok flipped (MutDOSOk, value route); \
    eqv-rejected but defeq-equal (reported, not auto-passed; MutToInInits is the eta-rebuilt `inits` argument): {defeqOnly}; \
    each is one well-typed change, signature/value/telescope rejection, NOT a semantic counterexample. Unused extra hypotheses (weaker) and ill-typed proposals are not counted."

run_cmd Lean.Elab.Command.liftTermElabM do
  let ns : List Name := [``genData_toIn_d, ``genData_genSem_eq_via, ``genData_evidence, ``hunf_of_genData, ``factsOf_all_of_genDataInv,
    ``DataOfSound, ``GenData.toIn, ``GenData.genSem, ``GenData]
  for n in ns do checkAxioms n
  logInfo m!"GEN5 GENDATA AXIOMS OK: {ns.length} roots, standard axioms only"

run_cmd Lean.Elab.Command.liftTermElabM do
  let roots : List Name := [``genData_toIn_d, ``genData_genSem_eq_via, ``genData_evidence, ``hunf_of_genData, ``factsOf_all_of_genDataInv,
    ``DataOfSound, ``GenData.toIn, ``GenData.genSem, ``GenData]
  let c ← closureRun roots
  let f := forbiddenIn c
  unless f.isEmpty do throwError "GEN5 GENDATA CLOSURE FAILED: forbidden constants {f}"
  let t1 ← (do let _ ← closureRun [`Tests.Gen5.SemGenDataCheck.NoSuchConstant]; pure false) <|> pure true
  unless t1 do throwError "GEN5 GENDATA CONTROL FAILED: unknown root did not throw"
  for r in [``Lean.ofReduceBool, ``sorryAx] do
    let f ← detect [r]
    unless f.contains r do throwError "GEN5 GENDATA CONTROL FAILED: forbidden root {r} not flagged (got {f})"
  Tests.Gen5.SemExtCheck.withFixtures fun r3 r4 rc mv mt hv4 => do
    let env ← getEnv
    let t3 ← (do let _ ← closureRun [r3]; pure false) <|> pure true
    unless t3 do throwError "GEN5 GENDATA CONTROL FAILED: unknown helper value did not throw"
    let (_, c3) ← (closureOf env r3).run {}
    unless c3.missing == #[mv] do throwError "GEN5 GENDATA CONTROL FAILED: helper-value case reported {c3.missing}, intended {mv}"
    let t4 ← (do let _ ← closureRun [r4]; pure false) <|> pure true
    unless t4 do throwError "GEN5 GENDATA CONTROL FAILED: unknown helper type did not throw"
    let (_, c4) ← (closureOf env r4).run {}
    unless c4.missing == #[mt] do throwError "GEN5 GENDATA CONTROL FAILED: helper-type case reported {c4.missing}, intended {mt}"
    unless c4.seen.contains hv4 do throwError "GEN5 GENDATA CONTROL FAILED: helper-type path does not pass through Hv4"
    let cc ← closureRun [rc]
    unless cc.missing.isEmpty && (forbiddenIn cc).isEmpty do throwError "GEN5 GENDATA CONTROL FAILED: clean fixture flagged"
  logInfo m!"GEN5 GENDATA CLOSURE OK: {c.seen.toList.length} constants over {roots.length} roots, no forbidden constant; controls: unknown root throws, \
    2 forbidden roots flagged, unknown helper VALUE names Mv, unknown helper TYPE names Mt via Hv4, clean fixture passes (fixtures inside withoutModifyingEnv)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let reach (root : Name) (need : List Name) : MetaM Nat := do
    let c ← closureRun [root]
    for n in need do
      unless c.seen.contains n do throwError "GEN5 GENDATA REACH FAILED: {root} does not reach {n}"
    pure need.length
  let a ← reach ``hunf_of_genData [``hunf_of_kitInv, ``genData_genSem_eq_via, ``genData_toIn_d]
  let b ← reach ``factsOf_all_of_genDataInv [``factsOf_all_of_kitInv]
  let c ← reach ``GenData.toIn [``DataOfSound]
  logInfo m!"GEN5 GENDATA REACH OK: {a + b + c} required constants reached over 3 roots"

#print axioms factsOf_all_of_genDataInv

end Tests.Gen5.SemGenDataCheck
