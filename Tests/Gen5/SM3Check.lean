import Tools.ShippingGen5AccHinv
import Tests.Gen5.AccCheck
-- proof-accept target (SM3): types (isDefEq to the freeze), Prop-hypothesis list (no `hinv`) and mutants. Axioms / sorry / closure / forbidden names
-- are checked independently by the proof-accept checker (proof/sm3-manifest.json); `#print axioms` is display only.
-- NOT BUILT HERE (scripts/gen5/SM3_FREEZE.md at c31cd300). Expected statements are written by hand from the freeze text, not from the implementation. Mutants are rejected by signature/defeq comparison, not semantic counterexamples. No sorry/axiom/native_decide in this file.

/-! # SM3 checks (Tools/ShippingGen5AccHinv.lean)

TYPE: `checkExpected` of `hinv_genS` and `factsOf_genS_assembled'` against statements copied from the freeze (§2).
HYP: the Prop-typed binders of `factsOf_genS_assembled'` are exactly `hs hev hloc hdecl hd` (C.SM-1 / C.AC-2 / C.AC-3); no `hinv` binder (C.SM-3).
MUTANT: signature / defeq rejection only. AXIOMS: `#print axioms` display only. -/
namespace Tests.Gen5.SM3Check
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem Tools.ShippingGen2 Tests.Gen3.ExpectedType
open Tools.ShippingMachineAuto (MachineData)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine Sparkle.IR.Semantics
open Tools.ShippingMachineDenote Tools.ShippingMachineSource

section Expected

def ExpHinv : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
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
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E (structEnv env₀)),
        Acc (CallRel (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd)) X ∧
        (∀ k ∈ ordCallees₀ gd.d, CallRel (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) ((gd.d.shape.insts[k]).1) X) ∧
        s = GenData.genSem hs (genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd)) X gd

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
      (GenData.genSem hs Q X g).d = g.d),
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) X = some s → FactsOf s
end Expected

section Mutants
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

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

-- hinv_genS: `Acc` conjunct dropped
def MutHinvNoAcc : Prop := ∀
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
      genS (KitAsm hs genData₀ hev hloc hdecl hd) X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E (structEnv env₀)),
        (∀ k ∈ ordCallees₀ gd.d, CallRel (KitAsm hs genData₀ hev hloc hdecl hd) ((gd.d.shape.insts[k]).1) X) ∧
        s = GenData.genSem hs (genS (KitAsm hs genData₀ hev hloc hdecl hd)) X gd

-- hinv_genS: hypothesis `genS … X = none`
def MutHinvNone : Prop := ∀
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
      genS (KitAsm hs genData₀ hev hloc hdecl hd) X = none →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E (structEnv env₀)),
        Acc (CallRel (KitAsm hs genData₀ hev hloc hdecl hd)) X ∧
        (∀ k ∈ ordCallees₀ gd.d, CallRel (KitAsm hs genData₀ hev hloc hdecl hd) ((gd.d.shape.insts[k]).1) X) ∧
        s = GenData.genSem hs (genS (KitAsm hs genData₀ hev hloc hdecl hd)) X gd

-- hinv_genS: callee edge direction flipped (`CallRel X callee`)
def MutHinvFlip : Prop := ∀
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
      genS (KitAsm hs genData₀ hev hloc hdecl hd) X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E (structEnv env₀)),
        Acc (CallRel (KitAsm hs genData₀ hev hloc hdecl hd)) X ∧
        (∀ k ∈ ordCallees₀ gd.d, CallRel (KitAsm hs genData₀ hev hloc hdecl hd) X ((gd.d.shape.insts[k]).1)) ∧
        s = GenData.genSem hs (genS (KitAsm hs genData₀ hev hloc hdecl hd)) X gd

-- hinv_genS: the genSem equation replaced by `Q := fun _ => none`
def MutHinvQnone : Prop := ∀
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
      genS (KitAsm hs genData₀ hev hloc hdecl hd) X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E (structEnv env₀)),
        Acc (CallRel (KitAsm hs genData₀ hev hloc hdecl hd)) X ∧
        (∀ k ∈ ordCallees₀ gd.d, CallRel (KitAsm hs genData₀ hev hloc hdecl hd) ((gd.d.shape.insts[k]).1) X) ∧
        s = GenData.genSem hs (fun _ => none) X gd

-- assembled': conclusion `Acc` instead of `FactsOf s`
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
      (GenData.genSem hs Q X g).d = g.d),
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (KitAsm hs genData₀ hev hloc hdecl hd) X = some s → Acc (CallRel (KitAsm hs genData₀ hev hloc hdecl hd)) X

-- assembled': the removed `hinv` hypothesis put back
def MutAsmWithHinv : Prop := ∀
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
      genS (KitAsm hs genData₀ hev hloc hdecl hd) X = some s → FactsOf s

-- assembled': quantified over `hs`/`genData₀` only, `hev`/`hloc`/`hdecl`/`hd` removed
def MutAsmFewHyp : Prop := ∀
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀)))
    (X : Name) (s : SemPkg ι dom), FactsOf s
end Mutants

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``hinv_genS ``ExpHinv
  checkExpected ``factsOf_genS_assembled' ``ExpAssembled
  logInfo m!"SM3 TYPE OK 2 theorems against ExpHinv, ExpAssembled"

run_cmd Lean.Elab.Command.liftTermElabM do
  let ci ← getConstInfo ``factsOf_genS_assembled'
  let hyps ← forallTelescope ci.type fun xs _ => do
    let mut acc : List Name := []
    for x in xs do
      let t ← inferType x
      if (← isProp t) && !(← x.fvarId!.getUserName).hasMacroScopes then acc := acc ++ [(← x.fvarId!.getUserName)]
    pure acc
  let want : List Name := [`hs, `hev, `hloc, `hdecl, `hd]
  unless hyps == want do throwError "SM3 HYP FAILED: Prop binders of factsOf_genS_assembled' are {hyps}, expected exactly {want}"
  logInfo m!"SM3 HYP OK: Prop-typed binders are exactly {want} (C.SM-1 / C.AC-2 / C.AC-3); no hinv binder (C.SM-3)"

run_cmd Lean.Elab.Command.liftTermElabM do
  let tm : List (Name × Name) :=
    [(``hinv_genS, ``MutHinvNoAcc),
     (``hinv_genS, ``MutHinvNone),
     (``hinv_genS, ``MutHinvFlip),
     (``hinv_genS, ``MutHinvQnone),
     (``factsOf_genS_assembled', ``MutAsmConcl),
     (``factsOf_genS_assembled', ``MutAsmWithHinv),
     (``factsOf_genS_assembled', ``MutAsmFewHyp)]
  for (t, m) in tm do checkMutant t m
  logInfo m!"SM3 MUTANT REJECTED {tm.length} total, each rejected by signature/defeq comparison, NOT a semantic counterexample"

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo m!"SM3 COUNTS: TYPE 2 / MUTANT 7"

#print axioms hinv_genS
#print axioms factsOf_genS_assembled'

end Tests.Gen5.SM3Check
