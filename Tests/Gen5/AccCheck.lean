import Tools.ShippingGen5Acc
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Clean issue-linked build ac5v-802381fe: exit 0, source=base=end, dirty=false, approved at 802381fe (earlier clean build ac4v-5aab73de, 714 jobs). Earlier Pod builds: g5ac-r2 at fa4d6f1a. No sorry / axiom / native_decide in this source.

/-! # DG-ACC / DG-ASSIGN units A1-A2 checks (Tools/ShippingGen5Acc.lean; scripts/gen5/DG_ACC_FREEZE.md rev1 §A)

TYPE: each theorem / definition is compared (`checkExpected`) with an independently written `Expected…` statement.
MUTANT: one-place changes, each WELL-TYPED, rejected by `checkMutant` -- a rejection by signature / defeq, NOT a semantic counterexample.
AXIOMS: `Lean.collectAxioms` is a subset of the standard three.
CLOSURE: a separate walk that reads the explicit VALUE of every `thmInfo` / `defnInfo` / `opaqueInfo` (not `ConstantInfo.value?`,
which skips `opaqueInfo`) and the TYPE of every constant, over the transitive constants of the unit's roots. Its own walker is
validated by NEGATIVE controls (a forbidden constant reached directly, through a helper of the same namespace, through a helper of
another namespace, and through an `opaque`) and by clean CONTROLS (unrelated clean chains are not flagged). Constants not found in the
environment are reported (`logInfo`, "unknown"), never silently skipped. -/

namespace Tests.Gen5.AccCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab Sparkle.IR.Machine
open Tools.ShippingGen5Acc Tests.Gen3.ExpectedType
open Tools.ShippingGen5Sem (SemPkg)
open Tools.ShippingChildInv (Res)

section Expected
open Classical
-- definitions (independent restatements)
def ExpectedEntry₀ (env₀ : Environment) (X : Name) : Option ConstantInfo :=
  Option.map (fun ci => entryConst true false [] ci (instancePredicate env₀) (userInliner env₀) (structEnv env₀))
    (env₀.find? X)

def ExpectedCallEdge {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    (K : AssignKit ι dom env₀) (X c : Name) : Prop :=
  ∃ d, dataOf₀ K X = some d ∧ ∃ k, ∃ hk : k < d.shape.insts.length,
    (d.shape.instOrigins.getD k .ord).child? = none ∧ (d.shape.insts[k]'hk).1 = c

def ExpectedCallRel {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    (K : AssignKit ι dom env₀) : Name → Name → Prop := fun c X => CallEdge K X c

def ExpectedCacheAcc {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    (K : AssignKit ι dom env₀) (Reach : Name → Prop) (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, Reach c → m.get? c = some r → Acc (CallRel K) c

def ExpectedCoverAt {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    (K : AssignKit ι dom env₀) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∃ (E : ConstantInfo) (g : K.GD E), entry₀ env₀ c = some E ∧ K.genData₀ E = some g

-- theorems
def ExpectedCallEdgeOfOrd : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {X : Name} {E : ConstantInfo} {g : K.GD E} (hE : entry₀ env₀ X = some E) (hg : K.genData₀ E = some g),
    ∀ k ∈ K.ordCallees (K.dOf g), CallEdge K X ((K.dOf g).shape.insts[k]).1

def ExpectedGenSUnfold : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {X : Name} {E : ConstantInfo} {g : K.GD E} (hacc : Acc (CallRel K) X)
    (hE : entry₀ env₀ X = some E) (hg : K.genData₀ E = some g),
    genS K X =
      if (∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome)
      then some (K.genSem (genS K) X g) else none

def ExpectedGenSSomeInv : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {X : Name} {s : SemPkg ι dom} (hs : genS K X = some s),
    ∃ (E : ConstantInfo) (g : K.GD E), entry₀ env₀ X = some E ∧ K.genData₀ E = some g ∧ Acc (CallRel K) X ∧
      (∀ k ∈ K.ordCallees (K.dOf g), ∃ sc, genS K ((K.dOf g).shape.insts[k]).1 = some sc) ∧
      s = K.genSem (genS K) X g

def ExpectedCacheAccInsert : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {Reach : Name → Prop} {m : Std.HashMap Name Res} {n : Name} {r : Res} (h : CacheAcc K Reach m)
    (hr : Reach n → Acc (CallRel K) n), CacheAcc K Reach (m.insert n r)

def ExpectedCacheAccEmpty : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    (Reach : Name → Prop), CacheAcc K Reach {}

def ExpectedGenSIsSomeOfCover : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {Reach : Name → Prop} (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hacc : ∀ c, Reach c → Acc (CallRel K) c) (hcov : ReachCover K Reach), ∀ c, Reach c → ∃ s, genS K c = some s

-- mutants (each well-typed, one place changed)
/-- no strictness guard -/
def MutUnfoldNoGuard : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {X : Name} {E : ConstantInfo} {g : K.GD E} (hacc : Acc (CallRel K) X)
    (hE : entry₀ env₀ X = some E) (hg : K.genData₀ E = some g),
    genS K X = some (K.genSem (genS K) X g)

/-- callee-restricted table `Qx` instead of `genS K` in the `genSem` argument -/
def MutUnfoldQx : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {X : Name} {E : ConstantInfo} {g : K.GD E} (hacc : Acc (CallRel K) X)
    (hE : entry₀ env₀ X = some E) (hg : K.genData₀ E = some g),
    genS K X =
      if (∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome)
      then some (K.genSem (fun c => if CallEdge K X c then genS K c else none) X g) else none

/-- the result is built from the empty table -/
def MutSomeInvEmptyQ : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {X : Name} {s : SemPkg ι dom} (hs : genS K X = some s),
    ∃ (E : ConstantInfo) (g : K.GD E), entry₀ env₀ X = some E ∧ K.genData₀ E = some g ∧ Acc (CallRel K) X ∧
      (∀ k ∈ K.ordCallees (K.dOf g), ∃ sc, genS K ((K.dOf g).shape.insts[k]).1 = some sc) ∧
      s = K.genSem (fun _ => none) X g

/-- every index, not only the ordinary callees -/
def MutEdgeAllIdx : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {X : Name} {E : ConstantInfo} {g : K.GD E} (hE : entry₀ env₀ X = some E) (hg : K.genData₀ E = some g),
    ∀ k : Fin (K.dOf g).shape.insts.length, CallEdge K X ((K.dOf g).shape.insts[k]).1

/-- `CallEdge` without the `child? = none` test (memory entries become edges) -/
def MutCallEdgeAnyOrigin {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    (K : AssignKit ι dom env₀) (X c : Name) : Prop :=
  ∃ d, dataOf₀ K X = some d ∧ ∃ k, ∃ hk : k < d.shape.insts.length, (d.shape.insts[k]'hk).1 = c

/-- `CacheAcc` without the `Reach c →` antecedent -/
def MutCacheAccUnrestricted {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    (K : AssignKit ι dom env₀) (_Reach : Name → Prop) (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, m.get? c = some r → Acc (CallRel K) c

/-- insert without the premise on the inserted key -/
def MutInsertNoPremise : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {Reach : Name → Prop} {m : Std.HashMap Name Res} {n : Name} {r : Res} (h : CacheAcc K Reach m),
    CacheAcc K Reach (m.insert n r)

/-- strictness closes without `hcl` -/
def MutCoverNoClosure : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} (K : AssignKit ι dom env₀)
    {Reach : Name → Prop} (hacc : ∀ c, Reach c → Acc (CallRel K) c) (hcov : ReachCover K Reach), ∀ c, Reach c → ∃ s, genS K c = some s
end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``entry₀ ``ExpectedEntry₀
  checkExpected ``CallEdge ``ExpectedCallEdge
  checkExpected ``CallRel ``ExpectedCallRel
  checkExpected ``CacheAcc ``ExpectedCacheAcc
  checkExpected ``ReachCover ``ExpectedCoverAt
  checkExpected ``callEdge_of_ord ``ExpectedCallEdgeOfOrd
  checkExpected ``genS_unfold ``ExpectedGenSUnfold
  checkExpected ``genS_some_inv ``ExpectedGenSSomeInv
  checkExpected ``cacheAcc_insert ``ExpectedCacheAccInsert
  checkExpected ``cacheAcc_empty ``ExpectedCacheAccEmpty
  checkExpected ``genS_isSome_of_cover ``ExpectedGenSIsSomeOfCover
  checkMutant ``genS_unfold ``MutUnfoldNoGuard
  checkMutant ``genS_unfold ``MutUnfoldQx
  checkMutant ``genS_some_inv ``MutSomeInvEmptyQ
  checkMutant ``callEdge_of_ord ``MutEdgeAllIdx
  checkMutant ``CallEdge ``MutCallEdgeAnyOrigin
  checkMutant ``CacheAcc ``MutCacheAccUnrestricted
  checkMutant ``cacheAcc_insert ``MutInsertNoPremise
  checkMutant ``genS_isSome_of_cover ``MutCoverNoClosure

-- AXIOMS: standard axioms only.
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``entry₀, ``dataOf₀, ``dataOf₀_of_genData₀, ``CallEdge, ``callEdge_of_ord, ``CallRel, ``genStep, ``genSAcc, ``genS,
      ``genSAcc_intro, ``genSAcc_irrel, ``genS_of_acc, ``genS_of_not_acc, ``genS_step, ``genS_unfold, ``genS_some_inv,
      ``CacheAcc, ``cacheAcc_insert, ``cacheAcc_empty, ``ReachEdge, ``ReachCover, ``genS_isSome_of_cover] do
    checkAxioms n

/-! ## CLOSURE walker -/

/-- The explicit value of a constant (all three value-carrying kinds; `ConstantInfo.value?` skips `opaqueInfo`). -/
def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

/-- Walk the type and the explicit value of every reachable constant; constants missing from the environment are collected. -/
partial def walk (env : Environment) (root : Name) : StateT (NameSet × Array Name) MetaM Unit := do
  if (← get).1.contains root then return
  modify fun (s, u) => (s.insert root, u)
  match env.find? root with
  | none => modify fun (s, u) => (s, u.push root)
  | some ci =>
    for c in ci.type.getUsedConstants do walk env c
    match valueOfCI ci with
    | some v => for c in v.getUsedConstants do walk env c
    | none => pure ()

def forbidden : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]

/-- Roots' closure: (seen, unknown, forbidden hits). -/
def closureReport (env : Environment) (roots : List Name) : MetaM (NameSet × Array Name × List Name) := do
  let (_, (seen, unk)) ← (roots.forM (walk env)).run ({}, #[])
  pure (seen, unk, forbidden.filter seen.contains)

/-- Add a helper declaration to the current environment (callers restore it with `withoutModifyingEnv`). -/
def addThm (n : Name) (value : Expr) : MetaM Unit :=
  addDecl (.thmDecl { name := n, levelParams := [], type := mkConst ``True, value := value })

/-- Negative controls (the walker MUST flag) and clean controls (it MUST NOT). -/
def walkerControls : MetaM Unit := do
  let bad := mkApp2 (mkConst ``sorryAx [Level.zero]) (mkConst ``True) (mkConst ``Bool.false)
  let bad2 := mkConst ``Lean.trustCompiler
  let hits (roots : List Name) : MetaM (List Name) := do
    let (_, _, h) ← closureReport (← getEnv) roots
    pure h
  -- N1 direct: the root itself holds the forbidden constant
  let r1 ← withoutModifyingEnv do
    addThm `Tests.Gen5.AccCheck.NegDirect bad
    hits [`Tests.Gen5.AccCheck.NegDirect]
  unless r1 == [``sorryAx] do throwError "GEN5 WALKER CONTROL FAILED: direct negative not flagged ({r1})"
  -- N2 through a helper in the SAME namespace
  let r2 ← withoutModifyingEnv do
    addThm `Tests.Gen5.AccCheck.Helper bad2
    addThm `Tests.Gen5.AccCheck.NegViaSame (mkConst `Tests.Gen5.AccCheck.Helper)
    hits [`Tests.Gen5.AccCheck.NegViaSame]
  unless r2 == [``Lean.trustCompiler] do throwError "GEN5 WALKER CONTROL FAILED: same-namespace helper negative not flagged ({r2})"
  -- N3 through a helper in ANOTHER namespace (no prefix filter)
  let r3 ← withoutModifyingEnv do
    addThm `Other.Place.helper bad
    addThm `Tests.Gen5.AccCheck.NegViaOther (mkConst `Other.Place.helper)
    hits [`Tests.Gen5.AccCheck.NegViaOther]
  unless r3 == [``sorryAx] do throwError "GEN5 WALKER CONTROL FAILED: other-namespace helper negative not flagged ({r3})"
  -- N4 through an `opaque` value (ConstantInfo.value? would skip it)
  let r4 ← withoutModifyingEnv do
    addDecl (.opaqueDecl { name := `Other.Place.opq, levelParams := [], type := mkConst ``True, value := bad, isUnsafe := false })
    addThm `Tests.Gen5.AccCheck.NegViaOpaque (mkConst `Other.Place.opq)
    hits [`Tests.Gen5.AccCheck.NegViaOpaque]
  unless r4 == [``sorryAx] do throwError "GEN5 WALKER CONTROL FAILED: opaque negative not flagged ({r4})"
  -- C1/C2 clean controls: unrelated clean chains (one in this namespace, one elsewhere) are not flagged, no unknown constants
  let (r5, unk5) ← withoutModifyingEnv do
    addThm `Other.Place.cleanHelper (mkConst ``True.intro)
    addThm `Tests.Gen5.AccCheck.CleanControl (mkConst `Other.Place.cleanHelper)
    let (_, u, h) ← closureReport (← getEnv) [`Tests.Gen5.AccCheck.CleanControl]
    pure (h, u)
  unless r5.isEmpty && unk5.isEmpty do throwError "GEN5 WALKER CONTROL FAILED: clean control flagged ({r5}, unknown {unk5})"
  -- C3 the unit's own clean theorem is clean (checked below on the real roots)
  -- U1 a root that is not in the environment is reported as unknown, not skipped
  let (_, unk6, _) ← closureReport (← getEnv) [`Nonexistent.constant]
  unless unk6 == #[`Nonexistent.constant] do throwError "GEN5 WALKER CONTROL FAILED: unknown constant not reported ({unk6})"
  logInfo m!"GEN5 WALKER CONTROLS OK: 4 negatives flagged (direct / same namespace / other namespace / opaque), clean controls not flagged, unknown reported"

run_cmd Lean.Elab.Command.liftTermElabM walkerControls

-- Closure of the unit's real roots.
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``genS_unfold, ``genS_some_inv, ``callEdge_of_ord, ``genS_step, ``genS_of_acc, ``genS_of_not_acc,
    ``cacheAcc_insert, ``cacheAcc_empty, ``genS_isSome_of_cover, ``dataOf₀_of_genData₀, ``genSAcc_intro, ``genSAcc_irrel,
    ``genS, ``genStep, ``CacheAcc, ``ReachCover, ``ReachEdge]
  let (seen, unk, hits) ← closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  -- the unit uses the kit only as hypotheses: no supplier unit's constants are reached
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  if !unk.isEmpty then
    logInfo m!"GEN5 CLOSURE unknown (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK: {seen.toList.length} constants, no forbidden constant, no supplier-unit constant, {unk.size} unknown"

/-! ## Non-vacuity of the kit's spec fields: an inhabited kit (`GD := Empty`, so `genData₀ := none`).
This shows the spec fields are jointly satisfiable and that `genS` computes `none` there; it is a test of the statements, NOT of
DG-SEM's `genSem` or DG-DATAOF's `dataOf`. -/

def emptyKit {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} (env₀ : Environment) : AssignKit ι dom env₀ where
  dataOf := fun _ _ _ => none
  GD := fun _ => Empty
  dOf := fun g => nomatch g
  genData₀ := fun _ => none
  ordCallees := fun d => (List.finRange d.shape.insts.length).filter fun k => (d.shape.instOrigins.getD k .ord).child?.isNone
  genSem := fun _ _ {_} g => nomatch g
  mem_ordCallees := by
    intro d k
    simp [List.mem_filter, List.mem_finRange]
  genData₀_dataOf := by
    intro E g h
    cases h
  genSem_local := by
    intro Q Q' X E g
    exact nomatch g
  genSem_decl := by
    intro Q X E g
    exact nomatch g
  genSem_d := by
    intro Q X E g
    exact nomatch g

theorem emptyKit_genS {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} (env₀ : Environment) (X : Name) :
    genS (emptyKit (ι := ι) (dom := dom) env₀) X = none := by
  by_cases h : Acc (CallRel (emptyKit (ι := ι) (dom := dom) env₀)) X
  · rw [genS_step _ X h]
    unfold genStep
    cases hE : entry₀ env₀ X <;> simp [emptyKit]
  · exact genS_of_not_acc _ X h

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``emptyKit, ``emptyKit_genS] do checkAxioms n

end Tests.Gen5.AccCheck
