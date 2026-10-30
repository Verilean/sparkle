import Tools.ShippingGen2PostFactsProof
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built: g3pf3-a9c42458 (clean snapshot, exit 0, standard axioms); written by reading at 35588c38. No `sorry`, no `axiom`, no `native_decide`.
-- REMAINING PREMISES of the G-POST producer (scripts/gen2/GPOST_ASSEMBLY_NOTE.md):
--   * `hrows : ∀ q, DataOk q → DataRows q`                         (GPOST_FREEZE §11 S1; UNSUPPLIED)
--   * `hrow  : ∀ q, DataOk q → OneOutNoMemRow q = true`             (U1 G-ONEOUT-REACH, R-ROW; UNSUPPLIED)
--   U2 (G-REACH) is NOT a premise. P1/P2 (F1), P3-P10 are discharged inside the proof.
-- `t1_of_step_rows` is CONDITIONAL on `StepStmt`, `hrows`, `hrow`. Nothing here completes G-POST, T1/M3 or FG.

/-! # G-POST assembly checks

1. **Expected types** (`checkExpected`, shared helper `Tests.Gen3.ExpectedType`), binder by binder, against
   independent texts:
   - `PostFactsStmt` against the GPOST_FREEZE rev1 §2 text;
   - `postFacts_proved`, `postFacts_of_hord`, `t1_of_step_rows`.
2. **Mutants** (`checkMutant`, must be REJECTED):
   - `PostFactsStmt` without the `InstClosed` conjunct ((i) only, the retired `NoTopStmt` shape);
   - `postFacts_proved` without `hrows` (= claiming P3's data unconditionally);
   - `postFacts_proved` without `hrow` (= claiming U1 unconditionally);
   - `postFacts_of_hord` with `hord` lacking its `instFields = []` antecedent (a stronger premise);
   - `t1_of_step_rows` without `hStep`.
3. **Terms**: the premises are exactly the listed ones.
4. **Axioms**: `checkAxioms` (standard only) and `#print axioms`. -/

namespace Tests.Gen3.PostFactsCheck
open Tools.ShippingGen2
open Tests.Gen3.ExpectedType
open Sparkle.Core.Domain

section Expected
open Lean hiding Module
open Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingEntrySoundness
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildBndCore (dv)

/-- GPOST_FREEZE rev1 §2, verbatim. -/
def ExpectedPostFactsStmt {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) : Prop :=
  T1Hyp L P Reach DataOk →
  ∀ (q : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (u u' w1 : Void IO.RealWorld)
    (M' raw : Sparkle.IR.AST.Module) (Dg' Dg : Design),
    Reach q.decl → P q.decl = some q → DataOk q → AdmCtx L.O.quiet mctx cctx →
    InvAt L P Reach (dv u) u →
    IHAt L P Reach (dv u + 1) → ChildKeepsInv L P Reach (dv u + 1) →
    RunsTo (synthesizeCombinational q.decl) mctx mref cctx cref u (M', Dg') u' →
    RunsTo (synthesizeCombinationalCore q.decl [] false) mctx mref cctx cref u (raw, Dg) w1 →
    (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      M' = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    Dg'.topModule = Dg.topModule →
    ((∀ x ∈ Dg.modules, x.name ≠ raw.name) → Dg'.modules = Dg.modules) →
    MachineTaken L mctx cctx (dv u + 1) q.decl q.d.shape raw Dg →
    (∀ x ∈ Dg.modules, x.name ≠ raw.name) ∧ InstClosed (M', Dg')

/-- MUTANT: the `InstClosed` conjunct dropped ((i) only). -/
def MutPostFactsStmt_noInstClosed {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) : Prop :=
  T1Hyp L P Reach DataOk →
  ∀ (q : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (u u' w1 : Void IO.RealWorld)
    (M' raw : Sparkle.IR.AST.Module) (Dg' Dg : Design),
    Reach q.decl → P q.decl = some q → DataOk q → AdmCtx L.O.quiet mctx cctx →
    InvAt L P Reach (dv u) u →
    IHAt L P Reach (dv u + 1) → ChildKeepsInv L P Reach (dv u + 1) →
    RunsTo (synthesizeCombinational q.decl) mctx mref cctx cref u (M', Dg') u' →
    RunsTo (synthesizeCombinationalCore q.decl [] false) mctx mref cctx cref u (raw, Dg) w1 →
    (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      M' = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    Dg'.topModule = Dg.topModule →
    ((∀ x ∈ Dg.modules, x.name ≠ raw.name) → Dg'.modules = Dg.modules) →
    MachineTaken L mctx cctx (dv u + 1) q.decl q.d.shape raw Dg →
    (∀ x ∈ Dg.modules, x.name ≠ raw.name)

def ExpectedPostFactsProved : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true),
    PostFactsStmt L P Reach DataOk

/-- MUTANT: `hrows` dropped. -/
def MutPostFacts_noRows : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true),
    PostFactsStmt L P Reach DataOk

/-- MUTANT: `hrow` dropped (U1 claimed unconditionally). -/
def MutPostFacts_noRow : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q),
    PostFactsStmt L P Reach DataOk

def ExpectedPostFactsOfHord : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] → ∀ k, k < q.d.shape.insts.length →
      (q.d.shape.instOrigins.getD k .ord).child? = none),
    PostFactsStmt L P Reach DataOk

/-- MUTANT: `hord` without its `instFields = []` antecedent. -/
def MutPostFactsOfHord_noGuard : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hord : ∀ q : Pkg ι dom, DataOk q → ∀ k, k < q.d.shape.insts.length →
      (q.d.shape.instOrigins.getD k .ord).child? = none),
    PostFactsStmt L P Reach DataOk

def ExpectedT1Rows : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hStep : StepStmt L P DataOk),
    T1Stmt L P Reach DataOk

/-- MUTANT: `StepStmt` dropped. -/
def MutT1Rows_noStep : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true),
    T1Stmt L P Reach DataOk

end Expected

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``Tools.ShippingGen2.PostFactsStmt ``ExpectedPostFactsStmt
  checkExpected ``Tools.ShippingGen2.postFacts_proved ``ExpectedPostFactsProved
  checkExpected ``Tools.ShippingGen2.postFacts_of_hord ``ExpectedPostFactsOfHord
  checkExpected ``Tools.ShippingGen2.t1_of_step_rows ``ExpectedT1Rows
  checkMutant ``Tools.ShippingGen2.PostFactsStmt ``MutPostFactsStmt_noInstClosed
  checkMutant ``Tools.ShippingGen2.postFacts_proved ``MutPostFacts_noRows
  checkMutant ``Tools.ShippingGen2.postFacts_proved ``MutPostFacts_noRow
  checkMutant ``Tools.ShippingGen2.postFacts_of_hord ``MutPostFactsOfHord_noGuard
  checkMutant ``Tools.ShippingGen2.t1_of_step_rows ``MutT1Rows_noStep

/-! ## Terms: the premises are exactly the listed ones -/

section Terms
open Lean hiding Module
open Meta

/-- The producer from exactly `hrows`, `hrow` (CONDITIONAL; not G-POST completion). -/
example {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true) :
    PostFactsStmt L P Reach DataOk :=
  postFacts_proved L P Reach DataOk hrows hrow

/-- `T1Stmt` from exactly `StepStmt`, `hrows`, `hrow` (CONDITIONAL; not T1/M3 completion). -/
example {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrows : ∀ q : Pkg ι dom, DataOk q → DataRows q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hStep : StepStmt L P DataOk) :
    T1Stmt L P Reach DataOk :=
  t1_of_step_rows L P Reach DataOk hrows hrow hStep

end Terms

/-! ## Axioms -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``Tools.ShippingGen2.closeCalls_post
  checkAxioms ``Tools.ShippingGen2.memChildren_of_closeCalls
  checkAxioms ``Tools.ShippingGen2.inst_source
  checkAxioms ``Tools.ShippingGen2.post_of_source
  checkAxioms ``Tools.ShippingGen2.postFacts_of_hord
  checkAxioms ``Tools.ShippingGen2.postFacts_proved
  checkAxioms ``Tools.ShippingGen2.t1_of_step_rows
  checkAxioms ``Tools.ShippingGen2KidsInst.closeInsts_kids_inst
  checkAxioms ``Tools.ShippingGen2KidsInst.closeInstsG_kids_inst

#print axioms Tools.ShippingGen2.postFacts_of_hord
#print axioms Tools.ShippingGen2.postFacts_proved
#print axioms Tools.ShippingGen2.t1_of_step_rows

end Tests.Gen3.PostFactsCheck
