import Tools.ShippingGen5SemKitInv
set_option autoImplicit false
-- NOT BUILT HERE (U8, scripts/gen5/DG_SEM_FREEZE_P8.md §3.1; clean issue-linked build smu21v-d0a8cf66 exit 0 (719 jobs, dirty=false), approved at d0a8cf66 by the reviewer. defeq-only (syntactically different from the independent Expected, accepted by isDefEq): binder 10 (`hinv`) and the conclusion of `hunf_of_genData`, and binder 10 (`hinv`) of `factsOf_all_of_genDataInv`. No sorry/axiom/native_decide.
/-! # DG-SEM U8 (scripts/gen5/DG_SEM_FREEZE_P8.md §3.1): `GenData`, `GenData.toIn`, `GenData.genSem`
and `hsem` / `hd` / evidence as theorems.

`DataOfSound dataOf initsOf` is a hypothesis of each theorem, not a law. No value of `GenData` is constructed here; nothing here
supplies the real `dataOf`/`initsOf`, `GenWF` for a run, the kit's `hmem`/`hinv`, a run, M5 or FG. -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineRef (reads)
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Sparkle.Compiler.MachInstOrigin

variable {ι : Type} {dom : ι → DomainConfig}

def DataOfSound (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (initsOf : (d : MachineData) → HList (tys d.ss)) : Prop :=
  ∀ (E : ConstantInfo) (senv : StructEnv) (s : MachineShape) (d : MachineData),
    dataOf E senv s = some d →
    d.shape = s ∧ d.ok = true ∧
    d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
    d.initOk (initsOf d) = true

structure GenData (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData)
    (E : ConstantInfo) (senv : StructEnv) where
  d      : MachineData
  wf     : GenWF d = true
  hshape : machineShape? false [] E senv = some d.shape
  hdata  : dataOf E senv d.shape = some d

def GenData.toIn {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    {E : ConstantInfo} {senv : StructEnv} (g : GenData dataOf E senv) : GenIn :=
  ⟨g.d, g.wf, initsOf g.d, (hs E senv g.d.shape g.d g.hdata).2.1,
    (hs E senv g.d.shape g.d g.hdata).2.2.1, (hs E senv g.d.shape g.d g.hdata).2.2.2⟩

noncomputable def GenData.genSem {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} {senv : StructEnv}
    (g : GenData dataOf E senv) : SemPkg ι dom :=
  genSemI Q X (g.toIn hs)

theorem genData_toIn_d {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    {E : ConstantInfo} {senv : StructEnv} (g : GenData dataOf E senv) :
    (g.toIn hs).d = g.d := rfl

theorem genData_genSem_eq_via {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E senv) :
    GenData.genSem hs Q X g =
      genSemVia (fun E => GenData dataOf E senv) (fun {E} g => GenData.toIn hs g) Q X g := rfl

theorem genData_evidence {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    (senv : StructEnv) (E : ConstantInfo) (g : GenData dataOf E senv) :
    machineShape? false [] E senv = some g.d.shape ∧ dataOf E senv g.d.shape = some g.d :=
  ⟨g.hshape, g.hdata⟩

theorem hunf_of_genData {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), Acc R X ∧
        (∀ k ∈ ordC gd.d, R ((gd.d.shape.insts[k]).1) X) ∧ s = GenData.genSem hs G X gd) :
    ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y :=
  hunf_of_kitInv (fun E => GenData dataOf E senv) (fun {E} g => GenData.toIn hs g) (fun {E} g => g.d) ordC
    (fun Q X {E} g => GenData.genSem hs Q X g) R G
    (fun Q X E g => genData_genSem_eq_via hs senv Q X g) (fun {E} g => genData_toIn_d hs g) hmem hinv

theorem factsOf_all_of_genDataInv {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) (senv : StructEnv)
    (ordC : (d : MachineData) → List (Fin d.shape.insts.length))
    (hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
      k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
    (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hinv : ∀ (X : Name) (s : SemPkg ι dom), G X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E senv), Acc R X ∧
        (∀ k ∈ ordC gd.d, R ((gd.d.shape.insts[k]).1) X) ∧ s = GenData.genSem hs G X gd) :
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s :=
  factsOf_all_of_kitInv (fun E => GenData dataOf E senv) (fun {E} g => GenData.toIn hs g) (fun {E} g => g.d) ordC
    (fun Q X {E} g => GenData.genSem hs Q X g) R G
    (fun Q X E g => genData_genSem_eq_via hs senv Q X g) (fun {E} g => genData_toIn_d hs g) hmem hinv

end Tools.ShippingGen5Sem
