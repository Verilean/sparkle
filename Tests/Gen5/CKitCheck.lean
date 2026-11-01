import Tools.ShippingGen5AccGenDataKit
import Tests.Gen5.AccCheck
-- proof-accept target (CKIT): types (isDefEq to the freeze), Prop-hypothesis list of factsOf_genS_assembled'' (only `hs`) and mutants. Axioms / sorry / closure / forbidden names
-- are checked independently by the proof-accept checker (proof/ckit-manifest.json); no axiom/closure check here.
-- NOT BUILT HERE (scripts/gen5/CKIT_FREEZE.md at 7c8fdff7). Expected statements are written by hand from the freeze text (§4), not from the implementation. Mutants are rejected by signature/defeq comparison, not semantic counterexamples. No axiom/native_decide in this file (the skeleton bodies are sorry; the candidate fills them).

/-! # CKIT checks (Tools/ShippingGen5AccGenDataKit.lean)

TYPE: `checkExpected` of the five roots against statements copied from the freeze (§4).
HYP: the Prop-typed binders of `factsOf_genS_assembled''` are exactly `hs` (no `hev`/`hloc`/`hdecl`/`hd`).
MUTANT: signature / defeq rejection only. -/
namespace Tests.Gen5.CKitCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingMachineAuto (MachineData)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine Sparkle.IR.Semantics
open Tools.ShippingMachineDenote Tools.ShippingMachineSource

section Expected

def ExpEvidence : Prop := ∀ {env₀ : Environment} (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData),
    GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀

def ExpDecl : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).decl = X

def ExpD : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).d = g.d

def ExpLocal : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees₀ g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      GenData.genSem hs Q X g = GenData.genSem hs Q' X g

def ExpAssembled : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀))),
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem
        (genData_gdEvidence dataOf) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs)) X = some s →
      FactsOf s
end Expected

section Mutants

-- evidence: `dataOf` replaced by the constant-none function in the GDEvidence head
def MutEvDataOf : Prop := ∀ {env₀ : Environment} (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData),
    GDEvidence (fun _ _ _ => none) (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀

-- decl: conclusion `= X` replaced by `= Name.anonymous`
def MutDeclAnon : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).decl = Name.anonymous

-- d: conclusion `= g.d` replaced by a reflexive statement
def MutDRefl : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).d = (GenData.genSem hs Q X g).d

-- local: premise dropped
def MutLocalNoPre : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      
      GenData.genSem hs Q X g = GenData.genSem hs Q' X g

-- local: conclusion `Q'` replaced by `Q`
def MutLocalQ : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf),
    ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees₀ g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      GenData.genSem hs Q X g = GenData.genSem hs Q X g

-- assembled'': conclusion `Acc` instead of `FactsOf s`
def MutAsmConcl : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀))),
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem
        (genData_gdEvidence dataOf) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs)) X = some s →
      Acc (@CallRel ι dom env₀ (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem
        (genData_gdEvidence dataOf) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs))) X

-- assembled'': an extra hypothesis put back
def MutAsmExtraHyp : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀)))
    (hextra : ∀ Y : Name, Y = Y),
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem
        (genData_gdEvidence dataOf) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs)) X = some s →
      FactsOf s

-- assembled'': `s` fixed to be any `SemPkg` fact (quantifier over `genData₀` removed, conclusion unconditional)
def MutAsmFewHyp : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀))),
    ∀ (X : Name) (s : SemPkg ι dom), FactsOf s

end Mutants

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``genData_gdEvidence ``ExpEvidence
  checkExpected ``genData_genSem_decl ``ExpDecl
  checkExpected ``genData_genSem_d ``ExpD
  checkExpected ``genData_genSem_local ``ExpLocal
  checkExpected ``factsOf_genS_assembled'' ``ExpAssembled
  logInfo m!"CKIT TYPE OK 5 theorems against ExpEvidence, ExpDecl, ExpD, ExpLocal, ExpAssembled"

run_cmd Lean.Elab.Command.liftTermElabM do
  let ci ← getConstInfo ``factsOf_genS_assembled''
  let hyps ← forallTelescope ci.type fun xs _ => do
    let mut acc : List Name := []
    for x in xs do
      let t ← inferType x
      if (← isProp t) && !(← x.fvarId!.getUserName).hasMacroScopes then acc := acc ++ [(← x.fvarId!.getUserName)]
    pure acc
  let want : List Name := [`hs]
  unless hyps == want do throwError "CKIT HYP FAILED: Prop binders of factsOf_genS_assembled'' are {hyps}, expected exactly {want}"
  logInfo m!"CKIT HYP OK: Prop-typed binders are exactly {want} (C.SM-1); no hev/hloc/hdecl/hd (C.AC-2 / C.AC-3)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let tm : List (Name × Name) :=
    [(``genData_gdEvidence, ``MutEvDataOf),
     (``genData_genSem_decl, ``MutDeclAnon),
     (``genData_genSem_d, ``MutDRefl),
     (``genData_genSem_local, ``MutLocalNoPre),
     (``genData_genSem_local, ``MutLocalQ),
     (``factsOf_genS_assembled'', ``MutAsmConcl),
     (``factsOf_genS_assembled'', ``MutAsmExtraHyp),
     (``factsOf_genS_assembled'', ``MutAsmFewHyp)]
  for (t, m) in tm do checkMutant t m
  logInfo m!"CKIT MUTANT REJECTED {tm.length} total, each rejected by signature/defeq comparison, NOT a semantic counterexample"

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo m!"CKIT COUNTS: TYPE 5 / MUTANT 8"

end Tests.Gen5.CKitCheck
