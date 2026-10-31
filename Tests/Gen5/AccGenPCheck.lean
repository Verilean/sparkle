import Tools.ShippingGen5AccGenP
import Tests.Gen5.AccCheck
set_option autoImplicit false
-- Built in g5ac-r4 at e8ef4249 (Pod `kjob lake build`, exit 0; the build was of the identical content; this header is the only later change). Clean build is the coder's. No sorry / axiom / native_decide in this source.

/-! # DG-ACC unit A3 checks (Tools/ShippingGen5AccGenP.lean; scripts/gen5/DG_ACC_FREEZE_REV2.md §B)

TYPE: the `Stmt` definitions are compared binder by binder (`checkExpected`, on definition VALUES) with independently written
`Expected…` statements; each theorem is checked by an `example` against the independent statement (kernel defeq, not a syntactic
match); `GenPPkgStmt`/`GenPClosedStmt` conclusions are checked against the field types of `T1Hyp.pkg`/`T1Hyp.closed` at `P := genP K hF`.
MUTANT: one-place, well-typed changes rejected by `checkMutant` -- a rejection by signature / defeq, NOT a semantic counterexample.
AXIOMS: standard three only. CLOSURE: the explicit-value walker of `AccCheck` (with its negative/clean controls re-run). -/
namespace Tests.Gen5.AccGenPCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tests.Gen3.ExpectedType
open Tools.ShippingGen2 (Pkg Pkgs Laws T1Hyp)
open Tools.ShippingGen5Sem (SemPkg FactsOf semOf genPkg)

section Expected
open Classical
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}

def ExpectedGenSFacts (K : AssignKit ι dom env₀) : Prop := ∀ X s, genS K X = some s → FactsOf s

def ExpectedSemOfGenPStmt (K : AssignKit ι dom env₀) : Prop := ∀ (hF : GenSFacts K), semOf (genP K hF) = genS K

def ExpectedGeneratedAtK (K : AssignKit ι dom env₀) (P : Pkgs ι dom) (X : Name) (E : ConstantInfo) (p : Pkg ι dom) : Prop :=
  ∃ g : K.GD E, p.toSem = K.genSem (semOf P) X g

noncomputable def ExpectedGenPGeneratedStmt (K : AssignKit ι dom env₀) : Prop :=
  ∀ (hF : GenSFacts K) {X : Name} {p : Pkg ι dom}, genP K hF X = some p →
    ∃ E, entry₀ env₀ X = some E ∧ ∃ g : K.GD E, p.toSem = K.genSem (semOf (genP K hF)) X g

noncomputable def ExpectedGenPDeclStmt (K : AssignKit ι dom env₀) : Prop :=
  ∀ (hF : GenSFacts K) {X : Name} {p : Pkg ι dom}, genP K hF X = some p → p.decl = X

noncomputable def ExpectedGenPDEdgesStmt (K : AssignKit ι dom env₀) : Prop :=
  ∀ (hF : GenSFacts K) {X : Name} {p : Pkg ι dom}, genP K hF X = some p → ∃ d, dataOf₀ K X = some d ∧ p.d = d

noncomputable def ExpectedGenPPkgStmt (K : AssignKit ι dom env₀) : Prop :=
  ∀ (hF : GenSFacts K) {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) (hacc : ∀ c, Reach c → Acc (CallRel K) c)
    (hcov : ReachCover K Reach) (hOk : ∀ c, Reach c → ∀ q, genP K hF c = some q → DataOk q),
    ∀ c, Reach c → ∃ q, genP K hF c = some q ∧ q.decl = c ∧ DataOk q

noncomputable def ExpectedGenPClosedStmt (K : AssignKit ι dom env₀) : Prop :=
  ∀ (hF : GenSFacts K) {Reach : Name → Prop} (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c),
    ∀ c, Reach c → ∀ q, genP K hF c = some q → ∀ k (hk : k < q.d.shape.insts.length),
      (q.d.shape.instOrigins.getD k .ord).child? = none → Reach (q.d.shape.insts[k]).1

-- mutants (each well-typed, one place changed)
/-- `p.d = d` dropped -/
def MutDEdgesNoEq (K : AssignKit ι dom env₀) : Prop :=
  ∀ (hF : GenSFacts K) {X : Name} {p : Pkg ι dom}, genP K hF X = some p → ∃ d, dataOf₀ K X = some d ∧ True

/-- `p.decl = X` dropped -/
def MutDeclTrivial (K : AssignKit ι dom env₀) : Prop :=
  ∀ (hF : GenSFacts K) {X : Name} {p : Pkg ι dom}, genP K hF X = some p → True

/-- closed for every instance, not only `child? = none` -/
def MutClosedAnyOrigin (K : AssignKit ι dom env₀) : Prop :=
  ∀ (hF : GenSFacts K) {Reach : Name → Prop} (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c),
    ∀ c, Reach c → ∀ q, genP K hF c = some q → ∀ k (hk : k < q.d.shape.insts.length),
      Reach (q.d.shape.insts[k]).1

/-- the pkg statement without the closure `hcl` -/
def MutPkgNoHcl (K : AssignKit ι dom env₀) : Prop :=
  ∀ (hF : GenSFacts K) {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (hacc : ∀ c, Reach c → Acc (CallRel K) c)
    (hcov : ReachCover K Reach) (hOk : ∀ c, Reach c → ∀ q, genP K hF c = some q → DataOk q),
    ∀ c, Reach c → ∃ q, genP K hF c = some q ∧ q.decl = c ∧ DataOk q

/-- generated from the empty callee table -/
def MutGeneratedEmptyTable (K : AssignKit ι dom env₀) : Prop :=
  ∀ (hF : GenSFacts K) {X : Name} {p : Pkg ι dom}, genP K hF X = some p →
    ∃ E, entry₀ env₀ X = some E ∧ ∃ g : K.GD E, p.toSem = K.genSem (fun _ => none) X g

/-- `semOf genP` is the constantly-empty table -/
def MutSemOfEmpty (K : AssignKit ι dom env₀) : Prop :=
  ∀ (hF : GenSFacts K), semOf (genP K hF) = fun _ => none

noncomputable def ExpectedGenP (K : AssignKit ι dom env₀) (hF : GenSFacts K) (X : Name) : Option (Pkg ι dom) :=
  match h : genS K X with
  | some s => some (genPkg s (hF X s h))
  | none => none
end Expected

-- Each theorem against the independent statement (kernel defeq).
section Examples
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
example (K : AssignKit ι dom env₀) : ExpectedSemOfGenPStmt K := semOf_genP K
example (K : AssignKit ι dom env₀) : ExpectedGenPGeneratedStmt K := genP_generated K
example (K : AssignKit ι dom env₀) : ExpectedGenPDeclStmt K := genP_decl K
example (K : AssignKit ι dom env₀) : ExpectedGenPDEdgesStmt K := genP_d_edges K
example (K : AssignKit ι dom env₀) : ExpectedGenPPkgStmt K := genP_pkg K
example (K : AssignKit ι dom env₀) : ExpectedGenPClosedStmt K := genP_closed K

-- Field types of `T1Hyp` at `P := genP K hF` (both directions, on the same literal text).
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
example (K : AssignKit ι dom env₀) (hF : GenSFacts K) (L : Laws mref cref) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) (H : T1Hyp L (genP K hF) Reach DataOk) :
    ∀ c, Reach c → ∃ q, genP K hF c = some q ∧ q.decl = c ∧ DataOk q := H.pkg
example (K : AssignKit ι dom env₀) (hF : GenSFacts K) (L : Laws mref cref) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (h : ∀ c, Reach c → ∃ q, genP K hF c = some q ∧ q.decl = c ∧ DataOk q) :
    ∀ c, Reach c → ∃ q, genP K hF c = some q ∧ q.decl = c ∧ DataOk q := h
example (K : AssignKit ι dom env₀) (hF : GenSFacts K) (L : Laws mref cref) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hacc : ∀ c, Reach c → Acc (CallRel K) c) (hcov : ReachCover K Reach)
    (hOk : ∀ c, Reach c → ∀ q, genP K hF c = some q → DataOk q) :
    ∀ c, Reach c → ∃ q, genP K hF c = some q ∧ q.decl = c ∧ DataOk q := genP_pkg K hF hcl hacc hcov hOk
example (K : AssignKit ι dom env₀) (hF : GenSFacts K) (L : Laws mref cref) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) (H : T1Hyp L (genP K hF) Reach DataOk) :
    ∀ c, Reach c → ∀ q, genP K hF c = some q → ∀ k (hk : k < q.d.shape.insts.length),
      (q.d.shape.instOrigins.getD k .ord).child? = none → Reach (q.d.shape.insts[k]).1 := H.closed
example (K : AssignKit ι dom env₀) (hF : GenSFacts K) (Reach : Name → Prop)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) :
    ∀ c, Reach c → ∀ q, genP K hF c = some q → ∀ k (hk : k < q.d.shape.insts.length),
      (q.d.shape.instOrigins.getD k .ord).child? = none → Reach (q.d.shape.insts[k]).1 := genP_closed K hF hcl
end Examples

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``GenSFacts ``ExpectedGenSFacts
  checkExpected ``genP ``ExpectedGenP
  checkExpected ``SemOfGenPStmt ``ExpectedSemOfGenPStmt
  checkExpected ``GeneratedAtK ``ExpectedGeneratedAtK
  checkExpected ``GenPGeneratedStmt ``ExpectedGenPGeneratedStmt
  checkExpected ``GenPDeclStmt ``ExpectedGenPDeclStmt
  checkExpected ``GenPDEdgesStmt ``ExpectedGenPDEdgesStmt
  checkExpected ``GenPPkgStmt ``ExpectedGenPPkgStmt
  checkExpected ``GenPClosedStmt ``ExpectedGenPClosedStmt
  checkMutant ``GenPDEdgesStmt ``MutDEdgesNoEq
  checkMutant ``GenPDeclStmt ``MutDeclTrivial
  checkMutant ``GenPClosedStmt ``MutClosedAnyOrigin
  checkMutant ``GenPPkgStmt ``MutPkgNoHcl
  checkMutant ``GenPGeneratedStmt ``MutGeneratedEmptyTable
  checkMutant ``SemOfGenPStmt ``MutSemOfEmpty

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``GenSFacts, ``genP, ``SemOfGenPStmt, ``GeneratedAtK, ``genP_eq_some, ``genP_eq_none, ``genP_some_inv, ``semOf_genP,
      ``genP_generated, ``genP_decl, ``genP_d_edges, ``genP_pkg, ``genP_closed] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM Tests.Gen5.AccCheck.walkerControls

/-- Unknown-name controls through the same `closureReport` path: a root, a helper value and a helper type that mention a name absent
from the environment MUST be reported unknown; a clean chain MUST NOT. (The helpers are added with the kernel type check skipped,
inside `withoutModifyingEnv`.) -/
def unknownControls : MetaM Unit := do
  let ghost := `Ghost.Absent.name
  let addU (n : Name) (type value : Expr) : MetaM Unit :=
    withOptions (fun o => debug.skipKernelTC.set o true) do
      addDecl (.thmDecl { name := n, levelParams := [], type := type, value := value })
  let unk (roots : List Name) : MetaM (Array Name) := do
    let (_, u, _) ← Tests.Gen5.AccCheck.closureReport (← getEnv) roots
    pure u
  let u1 ← unk [ghost]
  unless u1 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: unknown root not reported ({u1})"
  let u2 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.HelperVal (mkConst ``True) (mkConst ghost)
    addU `Tests.Gen5.UnkCtl.RootVal (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.HelperVal)
    unk [`Tests.Gen5.UnkCtl.RootVal]
  unless u2 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper value naming an unknown constant not reported ({u2})"
  let u3 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.HelperTy (mkConst ghost) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtl.RootTy (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.HelperTy)
    unk [`Tests.Gen5.UnkCtl.RootTy]
  unless u3 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper type naming an unknown constant not reported ({u3})"
  let u4 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.CleanHelper (mkConst ``True) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtl.CleanRoot (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.CleanHelper)
    unk [`Tests.Gen5.UnkCtl.CleanRoot]
  unless u4.isEmpty do throwError "GEN5 UNKNOWN CONTROL FAILED: clean control reported unknown ({u4})"
  logInfo m!"GEN5 UNKNOWN CONTROLS OK: 3 negatives reported unknown (root / helper value / helper type), clean control not reported"

run_cmd Lean.Elab.Command.liftTermElabM unknownControls

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``genP, ``genP_eq_some, ``genP_eq_none, ``genP_some_inv, ``semOf_genP, ``genP_generated, ``genP_decl,
    ``genP_d_edges, ``genP_pkg, ``genP_closed]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A3): {seen.toList.length} constants, no forbidden constant, no supplier-unit constant, no unknown constant"

end Tests.Gen5.AccGenPCheck
