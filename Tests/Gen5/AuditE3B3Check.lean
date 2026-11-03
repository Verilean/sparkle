import Tools.ShippingGen5AuditE3B3
import Tools.ShippingGen2Defs
import Tests.Gen5.NameKidsCheck
set_option autoImplicit false
-- NOT BUILT (no build run yet).
-- U-A4/U-A5 check. Expected statements are written from the Lean text of AUDIT_CARRIER_FREEZE §2 (AuditE3, B3 part of AuditE4_B3B4)
-- and AUD_UA4_FREEZE §1 (hLeafAlias), not copied from the implementation.
-- Mutants are well-typed variants; a rejection is by signature / defeq of a changed statement, NOT a semantic counterexample.
-- No instance of any premise is constructed: not evidence of non-vacuity. No sorry / axiom / native_decide.

namespace Tests.Gen5.AuditE3B3Check
open Lean Meta
open Sparkle.Compiler.Elab (MachineShape)
open Tools.ShippingGen2 Tools.ShippingGen5FG
open Tools.ShippingSrm7Rank (CallGraph InClass)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingGen5NameKids3 (GraphAgrees ReachSpans)
open Tools.ShippingGen5AuditCarrier (SOf)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildInv (Res)
open Sparkle.IR.AST (Stmt)
open Sparkle.IR.ModuleName (ofDecl)
open Tools.ShippingGen5AuditE3B3
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)
open Tests.Gen5.NameKidsCheck (cmpEqR cmpTeleR checkExpectedR checkMutantR auditRoot failsAudit)

/-! ## 1. Independent Expected defs (freeze text) -/
section Exp
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
  {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

def ExpE3 (P : Pkgs ι dom) (Reach : Name → Prop) (L : Laws mref cref) : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∀ (k : Nat) (hk : k < sp.insts.length), (originAt sp k).child? = none →
      ∀ y : Tools.ShippingChildInv.Res,
        Tools.ShippingChildCacheA.RealChildA L.O (sp.insts[k]'hk).1 y →
        y.1.name = ofDecl (sp.insts[k]'hk).1

/-- B3 part of `AuditE4_B3B4`: `namesK k` := names of the kid's top and design; `ChildIfaceP.desNames`, `.closed`, and `ofDecl c ∉ namesK k` -/
def ExpB3 (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∀ (k : Nat) (hk : k < sp.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA L.O (originAt sp k) (sp.insts[k]'hk).1 y →
      (∀ a ∈ y.2.modules, a.name ∈ (y.1 :: y.2.modules).map (·.name)) ∧
      (∀ a ∈ y.1 :: y.2.modules, ∀ mn i cs, Stmt.inst mn i cs ∈ a.body → mn ∈ (y.1 :: y.2.modules).map (·.name)) ∧
      ofDecl c ∉ (y.1 :: y.2.modules).map (·.name)

/-! ## 2. Expected final theorem -/
def ExpFinal : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk)
    (hMemRow : ∀ q : Pkg ι dom, DataOk q → MemParentDataOk q ∧ ExtInS q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hLeafAlias : ∀ q : Pkg ι dom, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true)
    (hA : AdmCtx L.O.quiet mctx cctx)
    {g : CallGraph} {B : Nat} {top : Name}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach (SOf P)),
    AuditE3 P Reach L ∧ AuditB3 L P Reach

/-! ## 3. Mutants (signature/defeq rejection, not semantic counterexamples) -/
def MutNoLeafAlias : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk)
    (hMemRow : ∀ q : Pkg ι dom, DataOk q → MemParentDataOk q ∧ ExtInS q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hA : AdmCtx L.O.quiet mctx cctx)
    {g : CallGraph} {B : Nat} {top : Name}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach (SOf P)),
    AuditE3 P Reach L ∧ AuditB3 L P Reach
def MutNoRow : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk)
    (hMemRow : ∀ q : Pkg ι dom, DataOk q → MemParentDataOk q ∧ ExtInS q)
    (hLeafAlias : ∀ q : Pkg ι dom, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true)
    (hA : AdmCtx L.O.quiet mctx cctx)
    {g : CallGraph} {B : Nat} {top : Name}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach (SOf P)),
    AuditE3 P Reach L ∧ AuditB3 L P Reach
def MutWeakAlias : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk)
    (hMemRow : ∀ q : Pkg ι dom, DataOk q → MemParentDataOk q ∧ ExtInS q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hLeafAlias : ∀ q : Pkg ι dom, DataOk q → q.d.letsAliasOk = true)
    (hA : AdmCtx L.O.quiet mctx cctx)
    {g : CallGraph} {B : Nat} {top : Name}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach (SOf P)),
    AuditE3 P Reach L ∧ AuditB3 L P Reach
def MutOnlyE3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk)
    (hMemRow : ∀ q : Pkg ι dom, DataOk q → MemParentDataOk q ∧ ExtInS q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hLeafAlias : ∀ q : Pkg ι dom, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true)
    (hA : AdmCtx L.O.quiet mctx cctx)
    {g : CallGraph} {B : Nat} {top : Name}
    (hin : InClass g B top = true) (hsp : ReachSpans g top Reach) (hg : GraphAgrees g Reach (SOf P)),
    AuditE3 P Reach L
def MutNoCarrier : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1Hyp L P Reach DataOk)
    (hMemRow : ∀ q : Pkg ι dom, DataOk q → MemParentDataOk q ∧ ExtInS q)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hLeafAlias : ∀ q : Pkg ι dom, DataOk q → q.d.shape.insts = [] → q.d.letsAliasOk = true)
    (hA : AdmCtx L.O.quiet mctx cctx)
    {g : CallGraph} {B : Nat} {top : Name}
    (hin : InClass g B top = true) (hg : GraphAgrees g Reach (SOf P)),
    AuditE3 P Reach L ∧ AuditB3 L P Reach
end Exp

/-! ## 4. Def bodies against the independent defs -/
def cmpDefValue (impl exp : Name) : MetaM Unit := do
  let some (.defnInfo a) := (← getEnv).find? impl | throwError "AUDIT E3B3 CHECK FAILED {impl}: not a def"
  let some (.defnInfo e) := (← getEnv).find? exp | throwError "AUDIT E3B3 CHECK FAILED {exp}: not a def"
  cmpEqR s!"def type {impl} vs {exp}" a.type e.type
  cmpEqR s!"def body {impl} vs {exp}" a.value e.value
  logInfo m!"AUDIT E3B3 DEF OK {impl} against {exp}"

run_cmd Lean.Elab.Command.liftTermElabM do
  cmpDefValue ``AuditE3 ``ExpE3
  cmpDefValue ``AuditB3 ``ExpB3
  logInfo m!"AUDIT E3B3 DEFS: 2 defs (AuditE3, AuditB3) compared by type and value against independent definitions"

/-! ## 5. Type -/
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpectedR ``auditE3B3_of_t1hyp ``ExpFinal
  logInfo m!"AUDIT E3B3 TYPE: 1 theorem against Expected"

/-! ## 6. Mutants: signature/defeq rejection only -/
run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutantR ``auditE3B3_of_t1hyp ``MutNoLeafAlias
  checkMutantR ``auditE3B3_of_t1hyp ``MutNoRow
  checkMutantR ``auditE3B3_of_t1hyp ``MutWeakAlias
  checkMutantR ``auditE3B3_of_t1hyp ``MutOnlyE3
  checkMutantR ``auditE3B3_of_t1hyp ``MutNoCarrier
  logInfo m!"AUDIT E3B3 MUTANT: 5 rejected (signature/defeq, not semantic counterexamples)"

/-! ## 7. Hypothesis (Prop binder) set: exactly T1Hyp + existing rows + hLeafAlias + AdmCtx + E-5 carriers -/
def propBinders (thm : Name) : MetaM (List Name) := do
  forallTelescope (← stmtOf thm) fun xs _ => do
    let mut out := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if ← isProp d.type then out := out ++ [d.userName.eraseMacroScopes]
    pure out

run_cmd Lean.Elab.Command.liftTermElabM do
  let got ← propBinders ``auditE3B3_of_t1hyp
  let exp : List Name := [`H, `hMemRow, `hrow, `hLeafAlias, `hA, `hin, `hsp, `hg]
  unless got == exp do throwError "AUDIT E3B3 BINDERS FAILED: expected {exp}, got {got}"
  -- the removed name premise is not a binder anywhere on the path
  for n in [`noMemName, `DataRes2, `hnomem, `hdomB, `outTy] do
    if got.contains n then throwError "AUDIT E3B3 BINDERS: unexpected premise {n}"
  -- negative control: a different set is rejected by the same comparison
  unless (got != exp.erase `hLeafAlias) do throwError "AUDIT E3B3 BINDERS CONTROL"
  logInfo m!"AUDIT E3B3 BINDERS: {got.length} Prop binders {got} (T1Hyp, T1L-12, T1L-04, new hLeafAlias, AdmCtx, E-5 carriers hin/hsp/hg)"

/-! Closure and axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let thms := [``auditE3B3_of_t1hyp, ``auditE3_of_t1hyp3, ``machPrem3_of_t1hyp, ``q_induct3, ``dataRes3_of_rows,
    ``leafCloses_of_data, ``closesAtA_of_closes, ``kidOK_of_kidTA, ``core_kids_facts_ranAO, ``deepChild_ifaceAO]
  let bad ← failsAudit env.find? ``Lean.ofReduceBool
  unless bad do throwError "AUDIT E3B3 CLOSURE CONTROL: forbidden root accepted"
  for r in thms do
    let a ← auditRoot env.find? r
    logInfo m!"AUDIT E3B3 CLOSURE {r}: no ofReduceBool / sorryAx / trustCompiler, no unresolved name; visited {a.visited} constants"
  for n in thms do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo m!"AUDIT E3B3 COUNTS: Tools theorems checked 10 (closure + axioms standard three only); carrier defs 2 (AuditE3, AuditB3); TYPE 1; MUTANT 5 (signature/defeq, not semantic); BINDERS 8 Prop binders; new premise hLeafAlias 1 (T1 +1); noMemName 0; sorry 0"

end Tests.Gen5.AuditE3B3Check
