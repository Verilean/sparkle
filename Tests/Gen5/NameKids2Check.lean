import Tools.ShippingGen5NameKids2
import Tests.Gen5.NameKidsCheck
set_option autoImplicit false
-- Pod build (kjob lake build Tests.Gen5.NameKids2Check, exit 0, 688 jobs) on the tree of b870656c; NOT a clean issue-linked build (coder runs that). Observed counts: TYPE 9 (7 theorems + 2 definition bodies), MUTANT 15 (11 single-point theorem mutants + 2 definition-body mutants + 2 cross-statement controls), use-site examples 2, closure controls negative 8 + clean 1, REACH 7, AXIOMS 7 (standard only).
-- Count rule: each count is the number of `logInfo` lines of one class (TYPE = theorem or definition body compared against its Expected; MUTANT = distinct mutant def or cross-statement control, each counted once; REACH/AXIOMS = one per theorem).
-- No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U2 checks

Every `Exp…` statement is written from the Lean text of freeze `BOUNDARY_AUDIT_FREEZE_U2.md` §3, not from the implementation.
The Expected props may name the constants `kidNameAt`, `MemTagsNamed` (their BODIES are compared separately against `ExpKidNameAt`, `ExpMemTagsNamed`), `kidModName`, `memKey`, `originAt`, `callees`, `declRank`.
ONE comparator (`cmpTeleR` / `checkExpectedR` / `checkMutantR` of `Tests.Gen5.NameKidsCheck`, reducible) is used for positives and mutants.
Mutants are single-point, well-typed variants; a rejection is by signature / defeq, NOT a semantic counterexample.
Closure uses the improved U1 walker (`reachWith`, `auditRoot`: root-self judgement, unknown name fails, type-only path asserted). -/

namespace Tests.Gen5.NameKids2Check
open Lean Meta
open Sparkle.Compiler.Elab (MachineShape)
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Compiler.MachMemory (memChildName)
open Tools.ShippingSrm7Rank (kidModName CallGraph callees declRank)
open Tools.ShippingMemCloses (memKey)
open Tools.ShippingInstTagged (originAt TagsAgree)
open Tools.ShippingGen5NameKids2
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)
open Tests.Gen5.NameKidsCheck (cmpEqR cmpTeleR checkExpectedR checkMutantR reachWith auditRoot failsAudit)

/-! ## 1. Independent Expected definitions and statements (from freeze §3 text) -/
def ExpKidNameAt (shape : MachineShape) (k : Nat) : String :=
  kidModName (((shape.insts[k]?).map Prod.fst).getD Name.anonymous, originAt shape k)

def ExpMemTagsNamed (shape : MachineShape) : Prop :=
  ∀ (k : Nat) (hk : k < shape.insts.length) (cb : Bool) (aw dw : Nat),
    originAt shape k = InstOrigin.mem cb aw dw → (shape.insts[k]'hk).1 = memChildName cb aw dw

def ExpHn : Prop := ∀ (shape : MachineShape),
    ∀ (k : Nat) (hk : k < shape.insts.length),
      kidNameAt shape k = kidModName ((shape.insts[k]'hk).1, originAt shape k)
def ExpTagsToMem : Prop := ∀ (shape : MachineShape) (h : TagsAgree shape), MemTagsNamed shape
def ExpHmemSame : Prop := ∀ (shape : MachineShape) (h : MemTagsNamed shape),
    ∀ (k : Nat) (hk : k < shape.insts.length) (k' : Nat) (hk' : k' < shape.insts.length),
      memKey (originAt shape k) ≠ none → memKey (originAt shape k) = memKey (originAt shape k') →
      (shape.insts[k]'hk).1 = (shape.insts[k']'hk').1
def ExpHself : Prop := ∀ {g : CallGraph} {F r : Nat} {declName : Name} (shape : MachineShape)
    (hgraph : callees g declName = some shape.instTagged) (hr : declRank g F declName = some r),
    ∀ (k : Nat) (hk : k < shape.insts.length), memKey (originAt shape k) = none →
      (shape.insts[k]'hk).1 ≠ declName
def ExpKidMemName : Prop := ∀ (shape : MachineShape),
    ∀ (k : Nat) (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design),
      (originAt shape k).child? = some y → kidNameAt shape k = y.1.name
def ExpMemNeDecl : Prop := ∀ (shape : MachineShape),
    ∀ (k : Nat) (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design),
      (originAt shape k).child? = some y → ∀ (C : Name), y.1.name ≠ ofDecl C
def ExpSepKParent : Prop := ∀ {g : CallGraph} {F r : Nat} (shape : MachineShape) (declName : Name)
    (hmem : MemTagsNamed shape) (hgraph : callees g declName = some shape.instTagged)
    (hr : declRank g F declName = some r),
    (∀ (k : Nat) (hk : k < shape.insts.length) (k' : Nat) (hk' : k' < shape.insts.length),
      kidNameAt shape k = kidNameAt shape k' →
      (shape.insts[k]'hk).1 = (shape.insts[k']'hk').1 ∧ memKey (originAt shape k) = memKey (originAt shape k')) ∧
    (∀ (k : Nat), k < shape.insts.length → kidNameAt shape k ≠ ofDecl declName)

/-! ## 2. Mutants (single change each; rejection by signature, not a semantic counterexample) -/
def MutHnOrd : Prop := ∀ (shape : MachineShape),
    ∀ (k : Nat) (hk : k < shape.insts.length),
      kidNameAt shape k = kidModName ((shape.insts[k]'hk).1, InstOrigin.ord)
def MutHmemSameEq : Prop := ∀ (shape : MachineShape) (h : MemTagsNamed shape),
    ∀ (k : Nat) (hk : k < shape.insts.length) (k' : Nat) (hk' : k' < shape.insts.length),
      memKey (originAt shape k) = none → memKey (originAt shape k) = memKey (originAt shape k') →
      (shape.insts[k]'hk).1 = (shape.insts[k']'hk').1
def MutHmemSameNoKey : Prop := ∀ (shape : MachineShape) (h : MemTagsNamed shape),
    ∀ (k : Nat) (hk : k < shape.insts.length) (k' : Nat) (hk' : k' < shape.insts.length),
      memKey (originAt shape k) ≠ none →
      (shape.insts[k]'hk).1 = (shape.insts[k']'hk').1
def MutHselfMem : Prop := ∀ {g : CallGraph} {F r : Nat} {declName : Name} (shape : MachineShape)
    (hgraph : callees g declName = some shape.instTagged) (hr : declRank g F declName = some r),
    ∀ (k : Nat) (hk : k < shape.insts.length), memKey (originAt shape k) ≠ none →
      (shape.insts[k]'hk).1 ≠ declName
def MutHselfRankNone : Prop := ∀ {g : CallGraph} {F : Nat} {declName : Name} (shape : MachineShape)
    (hgraph : callees g declName = some shape.instTagged) (hr : declRank g F declName = none),
    ∀ (k : Nat) (hk : k < shape.insts.length), memKey (originAt shape k) = none →
      (shape.insts[k]'hk).1 ≠ declName
def MutHselfGraphNone : Prop := ∀ {g : CallGraph} {F r : Nat} {declName : Name} (shape : MachineShape)
    (hgraph : callees g declName = none) (hr : declRank g F declName = some r),
    ∀ (k : Nat) (hk : k < shape.insts.length), memKey (originAt shape k) = none →
      (shape.insts[k]'hk).1 ≠ declName
def MutKidMemNameNe : Prop := ∀ (shape : MachineShape),
    ∀ (k : Nat) (y : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design),
      (originAt shape k).child? = some y → kidNameAt shape k ≠ y.1.name
def MutTagsToTags : Prop := ∀ (shape : MachineShape) (h : TagsAgree shape), TagsAgree shape
def MutSepNoParent : Prop := ∀ {g : CallGraph} {F r : Nat} (shape : MachineShape) (declName : Name)
    (hmem : MemTagsNamed shape) (hgraph : callees g declName = some shape.instTagged)
    (hr : declRank g F declName = some r),
    (∀ (k : Nat) (hk : k < shape.insts.length) (k' : Nat) (hk' : k' < shape.insts.length),
      kidNameAt shape k = kidNameAt shape k' →
      (shape.insts[k]'hk).1 = (shape.insts[k']'hk').1 ∧ memKey (originAt shape k) = memKey (originAt shape k'))
def MutSepNoHmem : Prop := ∀ {g : CallGraph} {F r : Nat} (shape : MachineShape) (declName : Name)
    (hgraph : callees g declName = some shape.instTagged)
    (hr : declRank g F declName = some r),
    (∀ (k : Nat) (hk : k < shape.insts.length) (k' : Nat) (hk' : k' < shape.insts.length),
      kidNameAt shape k = kidNameAt shape k' →
      (shape.insts[k]'hk).1 = (shape.insts[k']'hk').1 ∧ memKey (originAt shape k) = memKey (originAt shape k')) ∧
    (∀ (k : Nat), k < shape.insts.length → kidNameAt shape k ≠ ofDecl declName)
def MutSepMem : Prop := ∀ {g : CallGraph} {F r : Nat} (shape : MachineShape) (declName : Name)
    (hmem : MemTagsNamed shape) (hgraph : callees g declName = some shape.instTagged)
    (hr : declRank g F declName = some r),
    (∀ (k : Nat) (hk : k < shape.insts.length) (k' : Nat) (hk' : k' < shape.insts.length),
      kidNameAt shape k = kidNameAt shape k' →
      (shape.insts[k]'hk).1 = (shape.insts[k']'hk').1 ∧ memKey (originAt shape k) = memKey (originAt shape k')) ∧
    (∀ (k : Nat), k < shape.insts.length → kidNameAt shape k ≠ ofMem true 0 0)
-- definition-body mutants (the body comparator must reject them)
def MutKidNameAtOrd (shape : MachineShape) (k : Nat) : String :=
  kidModName (((shape.insts[k]?).map Prod.fst).getD Name.anonymous, InstOrigin.ord)
def MutMemTagsNamedOrd (shape : MachineShape) : Prop :=
  ∀ (k : Nat) (hk : k < shape.insts.length) (cb : Bool) (aw dw : Nat),
    originAt shape k = InstOrigin.ord → (shape.insts[k]'hk).1 = memChildName cb aw dw

/-! ## 3. Consumer-shape use sites: `MemCalleeData.sepK` / `.parent` with `nameK := kidNameAt d.shape` (a type check, not a semantic claim) -/
section Use
open Tools.ShippingMachineAuto
example {g : CallGraph} {F r : Nat} (d : MachineData) (C : Name)
    (hmem : MemTagsNamed d.shape) (hgraph : callees g C = some d.shape.instTagged) (hr : declRank g F C = some r) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat) (hk' : k' < d.shape.insts.length),
      kidNameAt d.shape k = kidNameAt d.shape k' → (d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        memKey (originAt d.shape k) = memKey (originAt d.shape k') :=
  (sepK_parent_of_supply d.shape C hmem hgraph hr).1
example {g : CallGraph} {F r : Nat} (d : MachineData) (C : Name)
    (hmem : MemTagsNamed d.shape) (hgraph : callees g C = some d.shape.instTagged) (hr : declRank g F C = some r) :
    ∀ k, k < d.shape.insts.length → kidNameAt d.shape k ≠ Sparkle.IR.ModuleName.ofDecl C :=
  (sepK_parent_of_supply d.shape C hmem hgraph hr).2
end Use

/-! ## 4. Definition-body comparison (same reducible comparator), then theorem positives and mutants -/

partial def cmpLamR (what : String) (a e : Lean.Expr) (i : Nat := 0) : MetaM Unit := do
  match a, e with
  | .lam na ta ba bia, .lam ne te be bie =>
    unless na.eraseMacroScopes == ne.eraseMacroScopes do throwError "NK2 CHECK FAILED {what}: lambda {i} name {na} vs {ne}"
    unless bia == bie do throwError "NK2 CHECK FAILED {what}: lambda {i} info"
    cmpEqR s!"{what} lambda {i} ({na})" ta te
    withLocalDecl na bia ta fun x => cmpLamR what (ba.instantiate1 x) (be.instantiate1 x) (i + 1)
  | .lam .., _ => throwError "NK2 CHECK FAILED {what}: extra lambda {i}"
  | _, .lam .. => throwError "NK2 CHECK FAILED {what}: missing lambda {i}"
  | .forallE .., _ => cmpTeleR what a e
  | _, _ => cmpEqR s!"{what} body" a e

def valueOf (n : Name) : MetaM Lean.Expr := do
  let some ci := (← getEnv).find? n | throwError "NK2: unknown constant {n}"
  match ci with
  | .defnInfo d => pure d.value
  | _ => throwError "NK2: {n} is not a definition"

def checkBodyR (d exp : Name) : MetaM Unit := do
  cmpTeleR s!"{d} (type)" (← stmtOf d) (← stmtOf exp)
  cmpLamR s!"{d}" (← valueOf d) (← valueOf exp)
  logInfo m!"NK2 TYPE OK body of {d} against {exp} (reducible comparator)"

def checkBodyMutantR (d mt : Name) : MetaM Unit := do
  let accepted ← withoutModifyingState do
    try
      cmpLamR s!"{d} vs mutant {mt}" (← valueOf d) (← valueOf mt)
      pure true
    catch _ => pure false
  if accepted then throwError "NK2 MUTANT ACCEPTED: {mt} body matches {d}"
  logInfo m!"NK2 MUTANT REJECTED {mt} (body of {d}; same comparator)"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkBodyR ``kidNameAt ``ExpKidNameAt
  checkBodyR ``MemTagsNamed ``ExpMemTagsNamed
  checkExpectedR ``hn_kidNameAt ``ExpHn
  checkExpectedR ``memTagsNamed_of_tagsAgree ``ExpTagsToMem
  checkExpectedR ``hmemSame_of_memTagsNamed ``ExpHmemSame
  checkExpectedR ``hself_of_rank ``ExpHself
  checkExpectedR ``kidNameAt_eq_memModule_name ``ExpKidMemName
  checkExpectedR ``memModule_name_ne_ofDecl ``ExpMemNeDecl
  checkExpectedR ``sepK_parent_of_supply ``ExpSepKParent
  checkBodyMutantR ``kidNameAt ``MutKidNameAtOrd
  checkBodyMutantR ``MemTagsNamed ``MutMemTagsNamedOrd
  checkMutantR ``hn_kidNameAt ``MutHnOrd
  checkMutantR ``hmemSame_of_memTagsNamed ``MutHmemSameEq
  checkMutantR ``hmemSame_of_memTagsNamed ``MutHmemSameNoKey
  checkMutantR ``hself_of_rank ``MutHselfMem
  checkMutantR ``hself_of_rank ``MutHselfRankNone
  checkMutantR ``hself_of_rank ``MutHselfGraphNone
  checkMutantR ``kidNameAt_eq_memModule_name ``MutKidMemNameNe
  checkMutantR ``memTagsNamed_of_tagsAgree ``MutTagsToTags
  checkMutantR ``sepK_parent_of_supply ``MutSepNoParent
  checkMutantR ``sepK_parent_of_supply ``MutSepNoHmem
  checkMutantR ``sepK_parent_of_supply ``MutSepMem
  -- cross-statement controls
  checkMutantR ``sepK_parent_of_supply ``ExpHmemSame
  checkMutantR ``hself_of_rank ``ExpHn

/-! ## 5. Closure audit (U1 walker, as improved in R1/R2) -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let F := `Tests.Gen5.NameKidsFixture
  let expectHit := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (path : List Name) => do
    let r ← reachWith resolve root
    unless r.hit == some path do throwError "NK2 AUDIT CONTROL {what}: expected hit {path}, got {toString r.hit} (unknown {r.unknown})"
    unless ← failsAudit resolve root do throwError "NK2 AUDIT FAILED: {what} accepted"
  let expectUnknown := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (first : List Name) => do
    let r ← reachWith resolve root
    unless r.hit.isNone && r.unknown > 0 && r.unknownFirst == some first do
      throwError "NK2 AUDIT CONTROL {what}: expected unknown via {first}, got hit {toString r.hit}, unknown {r.unknown}, first {toString r.unknownFirst}"
    unless ← failsAudit resolve root do throwError "NK2 AUDIT FAILED: {what} accepted"
  expectHit "edge root->forbidden" env.find? (F ++ `badRoot) [F ++ `badRoot, ``Lean.ofReduceBool]
  expectHit "helper value" env.find? (F ++ `badViaValue) [F ++ `badViaValue, F ++ `helperV, ``Lean.ofReduceBool]
  let asAxiom := fun (ci : ConstantInfo) => ConstantInfo.axiomInfo { name := ci.name, levelParams := ci.levelParams, type := ci.type, isUnsafe := false }
  let synthRoot := fun (root helper : Name) =>
    ConstantInfo.thmInfo { name := root, levelParams := [], type := mkConst ``True, value := mkConst helper, all := [root] }
  let SR := F ++ `synthRoot
  let tyOnly := fun n =>
    if n == SR then some (synthRoot SR (F ++ `helperTy))
    else if n == F ++ `helperTy then (env.find? n).map asAxiom
    else env.find? n
  expectHit "helper type" tyOnly SR [SR, F ++ `helperTy, ``Lean.ofReduceBool]
  expectHit "forbidden root ofReduceBool" env.find? ``Lean.ofReduceBool [``Lean.ofReduceBool]
  expectHit "forbidden root sorryAx" env.find? ``sorryAx [``sorryAx]
  expectUnknown "unknown root" (fun n => if n == F ++ `badRoot then none else env.find? n) (F ++ `badRoot) [F ++ `badRoot]
  expectUnknown "unknown helper value" (fun n => if n == F ++ `helperV then none else env.find? n) (F ++ `badViaValue) [F ++ `badViaValue, F ++ `helperV]
  let tyOnlyU := fun n =>
    if n == SR then some (synthRoot SR (F ++ `helperTyU))
    else if n == F ++ `auxT then none
    else if n == F ++ `helperTyU then (env.find? n).map asAxiom
    else env.find? n
  expectUnknown "unknown name via helper type" tyOnlyU SR [SR, F ++ `helperTyU, F ++ `auxT]
  let rc ← auditRoot env.find? (F ++ `cleanRoot)
  logInfo m!"NK2 CONTROLS closure: negative 8 (edge root->forbidden, helper value, helper type, forbidden root ofReduceBool, forbidden root sorryAx, unknown root, unknown helper value, unknown name via helper type) all rejected with the intended path; clean 1 accepted (visited {rc.visited})"
  for r in [``hn_kidNameAt, ``memTagsNamed_of_tagsAgree, ``hmemSame_of_memTagsNamed, ``hself_of_rank,
      ``kidNameAt_eq_memModule_name, ``memModule_name_ne_ofDecl, ``sepK_parent_of_supply] do
    let a ← auditRoot env.find? r
    logInfo m!"NK2 REACH {r}: no ofReduceBool / sorryAx / trustCompiler, no unresolved name; visited {a.visited} constants (all namespaces)"

/-! ## 6. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``hn_kidNameAt, ``memTagsNamed_of_tagsAgree, ``hmemSame_of_memTagsNamed, ``hself_of_rank,
      ``kidNameAt_eq_memModule_name, ``memModule_name_ne_ofDecl, ``sepK_parent_of_supply] do
    checkAxioms n

end Tests.Gen5.NameKids2Check
