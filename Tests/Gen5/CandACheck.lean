import Tools.ShippingGen5AccSemJoin
import Tests.Gen5.AccCheck
-- proof-accept target: types (isDefEq to the freeze), HYP binder check and mutants. Axioms / sorry / closure / forbidden names
-- (incl. hacc_of_top_runs) are checked independently by the proof-accept checker (proof/canda-manifest.json); `#print axioms` is display only.
-- NOT BUILT HERE (candidate A check, scripts/gen5/CANDA_FREEZE.md at eab9da5d). Expected statements are written from the freeze text, not from the implementation. Mutants are rejected by signature/defeq comparison, not semantic counterexamples. No sorry/axiom/native_decide.

/-! # Candidate A checks (Tools/ShippingGen5AccSemJoin.lean)

TYPE: `checkExpected` of 3 theorems against statements copied from the freeze (§2.1-§2.3).
HYP: the explicit Prop-typed binders of `factsOf_genS_assembled` are exactly `hs hev hloc hdecl hd hinv` (existing rows C.SM-1 / C.AC-2 / C.AC-3 / C.SM-3); no `hacc` / `hmem` binder.
MUTANT: signature / defeq rejection only. AXIOMS: standard three. CLOSURE: explicit-value walker of `AccCheck`, with its walker controls. -/
namespace Tests.Gen5.CandACheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingMachineAuto (MachineData)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine Sparkle.IR.Semantics
open Tools.ShippingMachineDenote Tools.ShippingMachineSource

section Expected

def ExpHaccGenS : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀),
    ∀ (Y : Name) (s : SemPkg ι dom), genS K Y = some s → Acc (CallRel K) Y

def ExpOrdEq : Prop := ∀ (d : MachineData), ordCallees d = ordCallees₀ d

def ExpAssembled : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀)))
    (hev : GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees₀ g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      GenData.genSem hs Q X g = GenData.genSem hs Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).d = g.d)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E (structEnv env₀)),
        Acc (CallRel (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd)) X ∧
        (∀ k ∈ ordCallees₀ gd.d, CallRel (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) ((gd.d.shape.insts[k]).1) X) ∧
        s = GenData.genSem hs (genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd)) X gd),
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) X = some s → FactsOf s
end Expected

section Mutants
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

-- hacc_genS: conclusion about the package declaration instead of `Y`
def MutHaccDecl : Prop := ∀ (K : AssignKit ι dom env₀),
    ∀ (Y : Name) (s : SemPkg ι dom), genS K Y = some s → Acc (CallRel K) s.decl
-- hacc_genS: hypothesis `genS K Y = none`
def MutHaccNone : Prop := ∀ (K : AssignKit ι dom env₀),
    ∀ (Y : Name) (s : SemPkg ι dom), genS K Y = none → Acc (CallRel K) Y
-- hacc_genS: kit argument dropped to a second kit for the relation
def MutHaccTwoKits : Prop := ∀ (K K' : AssignKit ι dom env₀),
    ∀ (Y : Name) (s : SemPkg ι dom), genS K Y = some s → Acc (CallRel K') Y
-- ordCallees_eq_ordCallees₀: reversed sides
def MutOrdSymm : Prop := ∀ (d : MachineData), ordCallees₀ d = ordCallees d
-- ordCallees_eq_ordCallees₀: one side replaced by the empty list
def MutOrdNil : Prop := ∀ (d : MachineData), ordCallees d = ([] : List (Fin d.shape.insts.length))
-- ordCallees_eq_ordCallees₀: equality weakened to a membership statement of one direction (different statement)
def MutOrdSubset : Prop := ∀ (d : MachineData), ∀ k, k ∈ ordCallees d → k ∈ ordCallees₀ d

noncomputable def KitAsm {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀)))
    (hev : GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees₀ g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      GenData.genSem hs Q X g = GenData.genSem hs Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).d = g.d) : AssignKit ι dom env₀ :=
  mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
    (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd

-- assembled: conclusion replaced by `Acc` (hacc_genS's conclusion), not `FactsOf s`
def MutAsmConcl : Prop := ∀
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀)))
    (hev : GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees₀ g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      GenData.genSem hs Q X g = GenData.genSem hs Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).d = g.d)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom),
      genS (KitAsm hs genData₀ hev hloc hdecl hd) X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E (structEnv env₀)),
        Acc (CallRel (KitAsm hs genData₀ hev hloc hdecl hd)) X ∧
        (∀ k ∈ ordCallees₀ gd.d, CallRel (KitAsm hs genData₀ hev hloc hdecl hd) ((gd.d.shape.insts[k]).1) X) ∧
        s = GenData.genSem hs (genS (KitAsm hs genData₀ hev hloc hdecl hd)) X gd),
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (KitAsm hs genData₀ hev hloc hdecl hd) X = some s → Acc (CallRel (KitAsm hs genData₀ hev hloc hdecl hd)) X

-- assembled: an extra `hacc` hypothesis (the discharged C.SM-4 row put back)
def MutAsmExtraHacc : Prop := ∀
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀)))
    (hev : GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees₀ g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      GenData.genSem hs Q X g = GenData.genSem hs Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).d = g.d)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom),
      genS (KitAsm hs genData₀ hev hloc hdecl hd) X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E (structEnv env₀)),
        Acc (CallRel (KitAsm hs genData₀ hev hloc hdecl hd)) X ∧
        (∀ k ∈ ordCallees₀ gd.d, CallRel (KitAsm hs genData₀ hev hloc hdecl hd) ((gd.d.shape.insts[k]).1) X) ∧
        s = GenData.genSem hs (genS (KitAsm hs genData₀ hev hloc hdecl hd)) X gd)
    (hacc : ∀ (Y : Name) (s : SemPkg ι dom), genS (KitAsm hs genData₀ hev hloc hdecl hd) Y = some s →
      Acc (CallRel (KitAsm hs genData₀ hev hloc hdecl hd)) Y),
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (KitAsm hs genData₀ hev hloc hdecl hd) X = some s → FactsOf s

-- assembled: `hinv` dropped
def MutAsmNoHinv : Prop := ∀
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀)))
    (hev : GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees₀ g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      GenData.genSem hs Q X g = GenData.genSem hs Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).d = g.d),
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (KitAsm hs genData₀ hev hloc hdecl hd) X = some s → FactsOf s
end Mutants

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``hacc_genS ``ExpHaccGenS
  checkExpected ``ordCallees_eq_ordCallees₀ ``ExpOrdEq
  checkExpected ``factsOf_genS_assembled ``ExpAssembled
  logInfo m!"CANDA TYPE OK 3 theorems against ExpHaccGenS, ExpOrdEq, ExpAssembled"

run_cmd Lean.Elab.Command.liftTermElabM do
  let ci ← getConstInfo ``factsOf_genS_assembled
  let hyps ← forallTelescope ci.type fun xs _ => do
    let mut acc : List Name := []
    for x in xs do
      let t ← inferType x
      if (← isProp t) && !(← x.fvarId!.getUserName).hasMacroScopes then acc := acc ++ [(← x.fvarId!.getUserName)]
    pure acc
  let want : List Name := [`hs, `hev, `hloc, `hdecl, `hd, `hinv]
  unless hyps == want do throwError "CANDA HYP FAILED: Prop binders of factsOf_genS_assembled are {hyps}, expected exactly {want}"
  logInfo m!"CANDA HYP OK: Prop-typed binders are exactly {want} (existing rows C.SM-1 / C.AC-2 / C.AC-3 / C.SM-3); no hacc / hmem binder"

run_cmd Lean.Elab.Command.liftTermElabM do
  let tm : List (Name × Name) :=
    [(``hacc_genS, ``MutHaccDecl),
     (``hacc_genS, ``MutHaccNone),
     (``hacc_genS, ``MutHaccTwoKits),
     (``ordCallees_eq_ordCallees₀, ``MutOrdSymm),
     (``ordCallees_eq_ordCallees₀, ``MutOrdNil),
     (``ordCallees_eq_ordCallees₀, ``MutOrdSubset),
     (``factsOf_genS_assembled, ``MutAsmConcl),
     (``factsOf_genS_assembled, ``MutAsmExtraHacc),
     (``factsOf_genS_assembled, ``MutAsmNoHinv)]
  for (t, m) in tm do checkMutant t m
  logInfo m!"CANDA MUTANT REJECTED {tm.length} total, each rejected by signature/defeq comparison, NOT a semantic counterexample"

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo m!"CANDA COUNTS: TYPE 3 / MUTANT 9"

#print axioms hacc_genS
#print axioms ordCallees_eq_ordCallees₀
#print axioms factsOf_genS_assembled

end Tests.Gen5.CandACheck
