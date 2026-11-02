import Tools.ShippingGen5NameKids3
import Tools.ShippingGen2Defs
import Tests.Gen5.NameKidsCheck
-- Pod incremental build on the tree of 25993694 (incremental; superseded by the reviewed build below) (kjob lake build Tests.Gen5.NameKids3Check, exit 0, 722 jobs) observed: TYPE 11 (5 theorems + 4 definition bodies + 2 OrdPath constructor types), MUTANT 16 (12 single-point theorem mutants + 2 definition-body mutants + 2 cross-statement controls), use-site examples 2, closure controls negative 8 + clean 1, REACH 5, AXIOMS 5 (standard only).
-- Reviewed build: ba7v-01a2afbb (exit 0, 722 jobs, approved at 01a2afbb; src=base=end, dirty=false; clean issue-linked build). TYPE 11 (theorems 5 + definition bodies 4 + OrdPath constructor types 2). Inputs InClass / GraphAgrees / ReachSpans / hmem are unsupplied; minimality was not derived from ReachClosed alone. Approval is per U3; the final N1/G5/G7/M5/FG audit is not complete.
-- Count rule: each count is the number of `logInfo` lines of one class (TYPE = theorem, definition body or constructor type compared against its Expected; MUTANT = distinct mutant def or cross-statement control, each counted once; REACH/AXIOMS = one per theorem).
-- No sorry / axiom / native_decide.

/-! # BOUNDARY-AUDIT U3 checks

Every `Exp…` statement is written from the Lean text of freeze `BOUNDARY_AUDIT_FREEZE_U3.md` §3, not from the implementation.
The Expected props may name `OrdEdge`, `GraphAgrees`, `ReachClosed`, `OrdPath`, `ReachSpans` (their BODIES / constructor types are compared separately).
ONE comparator (`cmpTeleR` / `checkExpectedR` / `checkMutantR` of `Tests.Gen5.NameKidsCheck`, reducible) is used for positives and mutants.
Mutants are single-point, well-typed variants; a rejection is by signature / defeq, NOT a semantic counterexample. -/

namespace Tests.Gen5.NameKids3Check
open Lean Meta
open Sparkle.Compiler.Elab (MachineShape)
open Sparkle.IR.ModuleName (ofDecl ofMem)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingSrm7Rank (CallGraph callees declRank InClass)
open Tools.ShippingMemCloses (memKey)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingGen5NameKids2 (MemTagsNamed kidNameAt)
open Tools.ShippingGen5NameKids3
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)
open Tests.Gen5.NameKidsCheck (cmpEqR cmpTeleR checkExpectedR checkMutantR reachWith auditRoot failsAudit)

/-! ## 1. Independent Expected definitions and statements (from freeze §3 text) -/
def ExpOrdEdge (g : CallGraph) (a b : Name) : Prop :=
  ∃ (ks : List (Name × InstOrigin)) (o : InstOrigin), callees g a = some ks ∧ (b, o) ∈ ks ∧ memKey o = none

def ExpGraphAgrees (g : CallGraph) (Reach : Name → Prop) (S : Name → Option MachineShape) : Prop :=
  ∀ c, Reach c → callees g c = (S c).map MachineShape.instTagged

def ExpReachClosed (Reach : Name → Prop) (S : Name → Option MachineShape) : Prop :=
  ∀ c, Reach c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
    (sp.instOrigins.getD k InstOrigin.ord).child? = none → Reach (sp.insts[k]'hk).1

def ExpReachSpans (g : CallGraph) (top : Name) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → OrdPath g top c

-- constructor types of `OrdPath`
def ExpOrdPathRefl : Prop := ∀ {g : CallGraph} {top : Name}, OrdPath g top top
def ExpOrdPathStep : Prop := ∀ {g : CallGraph} {top : Name} {a b : Name},
  OrdPath g top a → OrdEdge g a b → OrdPath g top b

def ExpRankOfOrdEdge : Prop := ∀ {g : CallGraph} {F r : Nat} {a b : Name}
    (hr : declRank g F a = some r) (he : OrdEdge g a b), ∃ r', declRank g F b = some r' ∧ r' < r
def ExpRankOfReach : Prop := ∀ {g : CallGraph} {F r : Nat} {top c : Name}
    (hr : declRank g F top = some r) (hc : OrdPath g top c), ∃ r', declRank g F c = some r' ∧ r' ≤ r
def ExpReachOfOrdEdges : Prop := ∀ {g : CallGraph} {Reach : Name → Prop} {S : Name → Option MachineShape} {top c : Name}
    (hg : GraphAgrees g Reach S) (hcl : ReachClosed Reach S) (ht : Reach top) (hc : OrdPath g top c), Reach c
def ExpHselfAll : Prop := ∀ {g : CallGraph} {B r : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach),
    ∀ c, Reach c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      memKey (originAt sp k) = none → (sp.insts[k]'hk).1 ≠ c
def ExpHself : Prop := ∀ {g : CallGraph} {F r : Nat} {declName : Name} (shape : MachineShape)
    (hgraph : callees g declName = some shape.instTagged) (hr : declRank g F declName = some r),
    ∀ (k : Nat) (hk : k < shape.insts.length), memKey (originAt shape k) = none →
      (shape.insts[k]'hk).1 ≠ declName
def ExpSepKParentAll : Prop := ∀ {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach)
    (hmem : ∀ c, Reach c → ∀ sp, S c = some sp → MemTagsNamed sp),
    ∀ c, Reach c → ∀ sp, S c = some sp →
      (∀ (k : Nat) (hk : k < sp.insts.length) (k' : Nat) (hk' : k' < sp.insts.length),
        kidNameAt sp k = kidNameAt sp k' →
        (sp.insts[k]'hk).1 = (sp.insts[k']'hk').1 ∧ memKey (originAt sp k) = memKey (originAt sp k')) ∧
      (∀ (k : Nat), k < sp.insts.length → kidNameAt sp k ≠ ofDecl c)

/-! ## 2. Mutants (single change each; rejection by signature, not a semantic counterexample) -/
def MutRankEdgeGt : Prop := ∀ {g : CallGraph} {F r : Nat} {a b : Name}
    (hr : declRank g F a = some r) (he : OrdEdge g a b), ∃ r', declRank g F b = some r' ∧ r < r'
def MutRankEdgeNone : Prop := ∀ {g : CallGraph} {F r : Nat} {a b : Name}
    (hr : declRank g F a = some r) (he : OrdEdge g a b), ∃ r', declRank g F b = none ∧ r' < r
def MutRankReachLt : Prop := ∀ {g : CallGraph} {F r : Nat} {top c : Name}
    (hr : declRank g F top = some r) (hc : OrdPath g top c), ∃ r', declRank g F c = some r' ∧ r' < r
def MutReachNoTop : Prop := ∀ {g : CallGraph} {Reach : Name → Prop} {S : Name → Option MachineShape} {top c : Name}
    (hg : GraphAgrees g Reach S) (hcl : ReachClosed Reach S) (hc : OrdPath g top c), Reach c
def MutReachNoClosed : Prop := ∀ {g : CallGraph} {Reach : Name → Prop} {S : Name → Option MachineShape} {top c : Name}
    (hg : GraphAgrees g Reach S) (ht : Reach top) (hc : OrdPath g top c), Reach c
def MutHselfNoSpans : Prop := ∀ {g : CallGraph} {B r : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S),
    ∀ c, Reach c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      memKey (originAt sp k) = none → (sp.insts[k]'hk).1 ≠ c
def MutHselfInFalse : Prop := ∀ {g : CallGraph} {B r : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = false) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach),
    ∀ c, Reach c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      memKey (originAt sp k) = none → (sp.insts[k]'hk).1 ≠ c
def MutHselfMemKey : Prop := ∀ {g : CallGraph} {B r : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach),
    ∀ c, Reach c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      memKey (originAt sp k) ≠ none → (sp.insts[k]'hk).1 ≠ c
def MutHselfEq : Prop := ∀ {g : CallGraph} {B r : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach),
    ∀ c, Reach c → ∀ sp, S c = some sp → ∀ (k : Nat) (hk : k < sp.insts.length),
      memKey (originAt sp k) = none → (sp.insts[k]'hk).1 = c
def MutSepNoHmem : Prop := ∀ {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach),
    ∀ c, Reach c → ∀ sp, S c = some sp →
      (∀ (k : Nat) (hk : k < sp.insts.length) (k' : Nat) (hk' : k' < sp.insts.length),
        kidNameAt sp k = kidNameAt sp k' →
        (sp.insts[k]'hk).1 = (sp.insts[k']'hk').1 ∧ memKey (originAt sp k) = memKey (originAt sp k')) ∧
      (∀ (k : Nat), k < sp.insts.length → kidNameAt sp k ≠ ofDecl c)
def MutSepNoParent : Prop := ∀ {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach)
    (hmem : ∀ c, Reach c → ∀ sp, S c = some sp → MemTagsNamed sp),
    ∀ c, Reach c → ∀ sp, S c = some sp →
      (∀ (k : Nat) (hk : k < sp.insts.length) (k' : Nat) (hk' : k' < sp.insts.length),
        kidNameAt sp k = kidNameAt sp k' →
        (sp.insts[k]'hk).1 = (sp.insts[k']'hk').1 ∧ memKey (originAt sp k) = memKey (originAt sp k'))
def MutSepMem : Prop := ∀ {g : CallGraph} {B : Nat} {top : Name} {Reach : Name → Prop} {S : Name → Option MachineShape}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach S) (hsp : ReachSpans g top Reach)
    (hmem : ∀ c, Reach c → ∀ sp, S c = some sp → MemTagsNamed sp),
    ∀ c, Reach c → ∀ sp, S c = some sp →
      (∀ (k : Nat) (hk : k < sp.insts.length) (k' : Nat) (hk' : k' < sp.insts.length),
        kidNameAt sp k = kidNameAt sp k' →
        (sp.insts[k]'hk).1 = (sp.insts[k']'hk').1 ∧ memKey (originAt sp k) = memKey (originAt sp k')) ∧
      (∀ (k : Nat), k < sp.insts.length → kidNameAt sp k ≠ ofMem true 0 0)
-- definition-body mutants (the body comparator must reject them)
def MutOrdEdgeMem (g : CallGraph) (a b : Name) : Prop :=
  ∃ (ks : List (Name × InstOrigin)) (o : InstOrigin), callees g a = some ks ∧ (b, o) ∈ ks ∧ memKey o ≠ none
def MutReachSpansSwap (g : CallGraph) (top : Name) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → OrdPath g c top

/-! ## 3. Use sites (type checks, not semantic claims) -/
section Use
open Tools.ShippingGen2
-- (i) `ReachClosed` with `S := fun c => (P c).map (·.d.shape)` is the type of `T1Hyp.closed` for that `P`
example {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} (P : Pkgs ι dom) (Reach : Name → Prop)
    (hcl : ∀ c, Reach c → ∀ q, P c = some q → ∀ k (hk : k < q.d.shape.insts.length),
      (q.d.shape.instOrigins.getD k .ord).child? = none → Reach (q.d.shape.insts[k]).1) :
    ReachClosed Reach (fun c => (P c).map (fun q => q.d.shape)) := by
  intro c hc sp hS k hk hn
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hS
  exact hcl c hc q hq k hk hn
-- (ii) `hself_all_reached` at the shape of a `MachineData` has the `hself` binder shape of `hparent_of_kidNames`
open Tools.ShippingMachineAuto in
example {g : CallGraph} {B r : Nat} {top C : Name} {Reach : Name → Prop} (d : MachineData)
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach (fun c => if c = C then some d.shape else none))
    (hsp : ReachSpans g top Reach) (hC : Reach C) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length), memKey (originAt d.shape k) = none → (d.shape.insts[k]'hk).1 ≠ C :=
  hself_all_reached (r := r) hin hg hsp C hC d.shape (by simp)
end Use

/-! ## 4. Definition-body comparison (same reducible comparator), then theorem positives and mutants -/

partial def cmpLamR (what : String) (a e : Lean.Expr) (i : Nat := 0) : MetaM Unit := do
  match a, e with
  | .lam na ta ba bia, .lam ne te be bie =>
    unless na.eraseMacroScopes == ne.eraseMacroScopes do throwError "NK3 CHECK FAILED {what}: lambda {i} name {na} vs {ne}"
    unless bia == bie do throwError "NK3 CHECK FAILED {what}: lambda {i} info"
    cmpEqR s!"{what} lambda {i} ({na})" ta te
    withLocalDecl na bia ta fun x => cmpLamR what (ba.instantiate1 x) (be.instantiate1 x) (i + 1)
  | .lam .., _ => throwError "NK3 CHECK FAILED {what}: extra lambda {i}"
  | _, .lam .. => throwError "NK3 CHECK FAILED {what}: missing lambda {i}"
  | .forallE .., _ => cmpTeleR what a e
  | _, _ => cmpEqR s!"{what} body" a e

def valueOf (n : Name) : MetaM Lean.Expr := do
  let some ci := (← getEnv).find? n | throwError "NK3: unknown constant {n}"
  match ci with
  | .defnInfo d => pure d.value
  | _ => throwError "NK3: {n} is not a definition"

def checkBodyR (d exp : Name) : MetaM Unit := do
  cmpTeleR s!"{d} (type)" (← stmtOf d) (← stmtOf exp)
  cmpLamR s!"{d}" (← valueOf d) (← valueOf exp)
  logInfo m!"NK3 TYPE OK body of {d} against {exp} (reducible comparator)"

def checkBodyMutantR (d mt : Name) : MetaM Unit := do
  let accepted ← withoutModifyingState do
    try
      cmpLamR s!"{d} vs mutant {mt}" (← valueOf d) (← valueOf mt)
      pure true
    catch _ => pure false
  if accepted then throwError "NK3 MUTANT ACCEPTED: {mt} body matches {d}"
  logInfo m!"NK3 MUTANT REJECTED {mt} (body of {d}; same comparator)"

def checkCtorR (c exp : Name) : MetaM Unit := do
  let some ci := (← getEnv).find? c | throwError "NK3: unknown constant {c}"
  cmpTeleR s!"{c} (constructor type)" ci.type (← stmtOf exp)
  logInfo m!"NK3 TYPE OK constructor {c} against {exp} (reducible comparator)"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkBodyR ``OrdEdge ``ExpOrdEdge
  checkBodyR ``GraphAgrees ``ExpGraphAgrees
  checkBodyR ``ReachClosed ``ExpReachClosed
  checkBodyR ``ReachSpans ``ExpReachSpans
  checkCtorR ``OrdPath.refl ``ExpOrdPathRefl
  checkCtorR ``OrdPath.step ``ExpOrdPathStep
  checkExpectedR ``rank_of_ordEdge ``ExpRankOfOrdEdge
  checkExpectedR ``rank_of_reach ``ExpRankOfReach
  checkExpectedR ``reach_of_ordEdges ``ExpReachOfOrdEdges
  checkExpectedR ``hself_all_reached ``ExpHselfAll
  checkExpectedR ``sepK_parent_all_reached ``ExpSepKParentAll
  checkBodyMutantR ``OrdEdge ``MutOrdEdgeMem
  checkBodyMutantR ``ReachSpans ``MutReachSpansSwap
  checkMutantR ``rank_of_ordEdge ``MutRankEdgeGt
  checkMutantR ``rank_of_ordEdge ``MutRankEdgeNone
  checkMutantR ``rank_of_reach ``MutRankReachLt
  checkMutantR ``reach_of_ordEdges ``MutReachNoTop
  checkMutantR ``reach_of_ordEdges ``MutReachNoClosed
  checkMutantR ``hself_all_reached ``MutHselfNoSpans
  checkMutantR ``hself_all_reached ``MutHselfInFalse
  checkMutantR ``hself_all_reached ``MutHselfMemKey
  checkMutantR ``hself_all_reached ``MutHselfEq
  checkMutantR ``sepK_parent_all_reached ``MutSepNoHmem
  checkMutantR ``sepK_parent_all_reached ``MutSepNoParent
  checkMutantR ``sepK_parent_all_reached ``MutSepMem
  -- cross-statement controls
  checkMutantR ``hself_all_reached ``ExpRankOfReach
  checkMutantR ``sepK_parent_all_reached ``ExpHself

/-! ## 5. Closure audit (U1/U2 walker: root-self judgement, unknown name fails, type-only path asserted) -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let F := `Tests.Gen5.NameKidsFixture
  let expectHit := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (path : List Name) => do
    let r ← reachWith resolve root
    unless r.hit == some path do throwError "NK3 AUDIT CONTROL {what}: expected hit {path}, got {toString r.hit} (unknown {r.unknown})"
    unless ← failsAudit resolve root do throwError "NK3 AUDIT FAILED: {what} accepted"
  let expectUnknown := fun (what : String) (resolve : Name → Option ConstantInfo) (root : Name) (first : List Name) => do
    let r ← reachWith resolve root
    unless r.hit.isNone && r.unknown > 0 && r.unknownFirst == some first do
      throwError "NK3 AUDIT CONTROL {what}: expected unknown via {first}, got hit {toString r.hit}, unknown {r.unknown}, first {toString r.unknownFirst}"
    unless ← failsAudit resolve root do throwError "NK3 AUDIT FAILED: {what} accepted"
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
  logInfo m!"NK3 CONTROLS closure: negative 8 (edge root->forbidden, helper value, helper type, forbidden root ofReduceBool, forbidden root sorryAx, unknown root, unknown helper value, unknown name via helper type) all rejected with the intended path; clean 1 accepted (visited {rc.visited})"
  for r in [``rank_of_ordEdge, ``rank_of_reach, ``reach_of_ordEdges, ``hself_all_reached, ``sepK_parent_all_reached] do
    let a ← auditRoot env.find? r
    logInfo m!"NK3 REACH {r}: no ofReduceBool / sorryAx / trustCompiler, no unresolved name; visited {a.visited} constants (all namespaces)"

/-! ## 6. Axioms -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``rank_of_ordEdge, ``rank_of_reach, ``reach_of_ordEdges, ``hself_all_reached, ``sepK_parent_all_reached] do
    checkAxioms n

end Tests.Gen5.NameKids3Check
