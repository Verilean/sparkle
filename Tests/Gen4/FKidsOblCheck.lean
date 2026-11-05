import Tools.ShippingGen4FKidsObl
import Tools.ShippingGen2Defs
import Tools.ShippingGen5T1ND
set_option autoImplicit false
-- FKIDS OBLIGATION CHECK: audit of `fKidsObl_params_core`, `fKidsObl_params`, `fKidsObl_noGuard` (FKIDS_FREEZE.md §7.9), each verified separately. NameNoTop has no theorem (decided not provable); N5 is its negative control.

/-! # Audit of the obligation theorems

1. TYPE: the theorem's type equals `Expected.memoHit` (the frozen text, written separately), STRUCTURALLY (`Expr.eqv`) and by `isDefEq`.
2. MUTANT: signature rejections only (NOT semantic counterexamples), by `Expr.eqv` AND `isDefEq`; and a negative control for the structural comparison.
3. AXIOMS: only propext / Classical.choice / Quot.sound.
4. CLOSURE: no `Laws` / `T1Hyp` / `T1HypND` in the closure (positive controls: the detector flags `T1Hyp`, `T1HypND`).
5. HYPOTHESES: in the theorem TYPE the only named assumptions are `MemoFamily` and `MsgMvK`. -/

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Sparkle.Compiler.Elab
open Tools.ShippingGen4FKids Tools.ShippingGen4FKidsDepth Tools.ShippingGen4FKidsObl

namespace Tests.Gen4.FKidsOblCheck

namespace Expected

def paramsCore : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName θ true true) mctx mref cctx cref w (M0, D0) w' →
    (M0.parameters.map (·.name)).Nodup ∧ ∀ p ∈ M0.parameters, p.name ∈ θ.map Prod.fst

def params : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    (M'.parameters.map (·.name)).Nodup ∧ ∀ p ∈ M'.parameters, p.name ∈ θ.map Prod.fst

def noGuard : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ x ∈ D'.modules, x.parameters = []

end Expected

namespace Mutant

/-- P1: no `MsgMvK`. -/
def P1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName θ true true) mctx mref cctx cref w (M0, D0) w' →
    (M0.parameters.map (·.name)).Nodup ∧ ∀ p ∈ M0.parameters, p.name ∈ θ.map Prod.fst

/-- P2: Nodup dropped. -/
def P2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName θ true true) mctx mref cctx cref w (M0, D0) w' →
    ∀ p ∈ M0.parameters, p.name ∈ θ.map Prod.fst

/-- P3: membership in θ dropped. -/
def P3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName θ true true) mctx mref cctx cref w (M0, D0) w' →
    (M0.parameters.map (·.name)).Nodup

/-- P4: no start-world hypothesis. -/
def P4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design},
    RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName θ true true) mctx mref cctx cref w (M0, D0) w' →
    (M0.parameters.map (·.name)).Nodup ∧ ∀ p ∈ M0.parameters, p.name ∈ θ.map Prod.fst

/-- P5: the non-symbolic entry. -/
def P5 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName θ false true) mctx mref cctx cref w (M0, D0) w' →
    (M0.parameters.map (·.name)).Nodup ∧ ∀ p ∈ M0.parameters, p.name ∈ θ.map Prod.fst

/-- P6: the top module is claimed parameter free. -/
def P6 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M0 : Sparkle.IR.AST.Module} {D0 : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalCoreWith Tools.ShippingGen4ParamEntry.Tsyn declName θ true true) mctx mref cctx cref w (M0, D0) w' →
    M0.parameters = []

/-- Q1: no `MsgMvK`. -/
def Q1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    (M'.parameters.map (·.name)).Nodup ∧ ∀ p ∈ M'.parameters, p.name ∈ θ.map Prod.fst

/-- Q2: Nodup dropped. -/
def Q2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ p ∈ M'.parameters, p.name ∈ θ.map Prod.fst

/-- Q3: membership dropped. -/
def Q3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    (M'.parameters.map (·.name)).Nodup

/-- Q4: no start-world hypothesis. -/
def Q4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    (M'.parameters.map (·.name)).Nodup ∧ ∀ p ∈ M'.parameters, p.name ∈ θ.map Prod.fst

/-- Q5: Nodup on the design's modules instead of the top. -/
def Q5 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ x ∈ D'.modules, (x.parameters.map (·.name)).Nodup ∧ ∀ p ∈ x.parameters, p.name ∈ θ.map Prod.fst

/-- N1: no `MsgMvK`. -/
def N1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ x ∈ D'.modules, x.parameters = []

/-- N2: the name guard (the frozen `fKids` conclusion; weaker, so it must be told apart). -/
def N2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ x ∈ D'.modules, x.name ≠ M'.name → x.parameters = []

/-- N3: no start-world hypothesis. -/
def N3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ x ∈ D'.modules, x.parameters = []

/-- N4: the top is claimed parameter free too. -/
def N4 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ x ∈ D'.modules, x.parameters = [] ∧ M'.parameters = []

/-- N5: the top-name collision is claimed absent (NameNoTop, the unprovable obligation). -/
def N5 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref}, Tools.Assume.MemoFamily.MemoFamily O →
    Tools.ShippingGen4KWalkDiag.MsgMvK O →
    ∀ {mctx : Meta.Context} {cctx : Core.Context}, AdmCtx O.quiet mctx cctx →
    ∀ {declName : Name} {θ : List (String × Nat)} {w w' : Void IO.RealWorld}
      {M' : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design},
    Tools.ShippingGen4KWalkDepth.KWD O (fun _ _ => True) 0 w →
    RunsTo (synthesizeCombinationalWithParameters declName θ) mctx mref cctx cref w (M', D') w' →
    ∀ x ∈ D'.modules, x.parameters = [] ∧ ∀ x ∈ D'.modules, x.name ≠ M'.name

end Mutant

private partial def closure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then closure env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | none => closure env rest seen
    | some ci =>
      let body : List Name := match ci with
        | .thmInfo v => v.value.getUsedConstants.toList
        | .defnInfo v => v.value.getUsedConstants.toList
        | _ => []
      closure env (ci.type.getUsedConstants.toList ++ body ++ rest) seen

private def forbidden : List Name :=
  [`Tools.ShippingGen2.Laws, `Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND]

private def closureBad (n : Name) : CoreM (List Name) := do
  let seen := closure (← getEnv) [n] {}
  return seen.toList.filter fun m => forbidden.any fun f => f.isPrefixOf m

private def checkOne (t : Name) (expName : Name) (muts : List Name) : TermElabM String := do
  let pre := `Tests.Gen4.FKidsOblCheck
  let ti ← getConstInfo t
  let expC ← getConstInfo (pre ++ `Expected ++ expName)
  let some expV := expC.value? | throwError "Expected.{expName} has no value"
  let structural := Expr.eqv ti.type expV
  unless structural do throwError "TYPE mismatch (structural) for {t}"
  unless ← isDefEq ti.type (mkConst (pre ++ `Expected ++ expName)) do throwError "TYPE mismatch (isDefEq) for {t}"
  let mut rej : Nat := 0
  let mut structRej : Nat := 0
  for m in muts do
    let mc ← getConstInfo (pre ++ `Mutant ++ m)
    if ← isDefEq ti.type (mkConst (pre ++ `Mutant ++ m)) then throwError "mutant {m} NOT rejected"
    rej := rej + 1
    let some mv := mc.value? | throwError "{m} has no value"
    if Expr.eqv ti.type mv then throwError "mutant {m} NOT rejected structurally"
    structRej := structRej + 1
  let axs ← collectAxioms t
  let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
  unless bad.isEmpty do throwError "{t}: axioms {bad}"
  let badC ← closureBad t
  unless badC.isEmpty do throwError "{t}: forbidden constants {badC}"
  let hypNames : List Name :=
    [`Tools.ShippingGen4KWalkEntry.LogMvK, `Tools.ShippingGen4FKidsEntry.LogMvKS, `Tools.ShippingGen4FKidsFallback.LegacyImplKS,
     `Tools.ShippingGen4FKidsHelpers.PpMvKS, `Tools.ShippingGen4KWalkDiag.MsgMvK, `Tools.ShippingGen4FKidsFallback.LegacyCachedKS,
     `Tools.ShippingGen4FKidsFallback.ChildEntryKS, `Tools.Assume.MemoFamily.MemoFamily,
     `Tools.ShippingLegacySemTelescopeN.LamTelescopeN]
  let inType := hypNames.filter ti.type.getUsedConstants.contains
  unless inType == [`Tools.ShippingGen4KWalkDiag.MsgMvK, `Tools.Assume.MemoFamily.MemoFamily] ||
      inType == [`Tools.Assume.MemoFamily.MemoFamily, `Tools.ShippingGen4KWalkDiag.MsgMvK] do
    throwError "hypotheses in type {inType}, expected exactly MsgMvK and MemoFamily"
  return s!"{t}: TYPE isDefEq ok / structural(Expr.eqv) {structural} / MUTANT {rej}/{muts.length} isDefEq-rejected, {structRej}/{muts.length} structurally rejected (signature rejections, not semantic counterexamples) / AXIOMS standard-only / CLOSURE clean / HYPOTHESES in type {inType}"

elab "#fkidsobl_check" : command => liftTermElabM do
  let r1 ← checkOne `Tools.ShippingGen4FKidsObl.fKidsObl_params_core `paramsCore [`P1, `P2, `P3, `P4, `P5, `P6]
  let r2 ← checkOne `Tools.ShippingGen4FKidsObl.fKidsObl_params `params [`Q1, `Q2, `Q3, `Q4, `Q5]
  let r3 ← checkOne `Tools.ShippingGen4FKidsObl.fKidsObl_noGuard `noGuard [`N1, `N2, `N3, `N4, `N5]
  for c in [`Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND] do
    let b ← closureBad c
    if b.isEmpty then throwError "closure detector MISSED {c}"
  logInfo m!"FKIDS OBLIGATION CHECK (3 theorems, verified separately; closure detector positive controls ok):\n{r1}\n{r2}\n{r3}"

#fkidsobl_check

end Tests.Gen4.FKidsOblCheck
