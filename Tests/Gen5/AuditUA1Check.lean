import Tools.ShippingGen5AuditUA1
import Tools.ShippingGen2Defs
import Tests.Gen5.NameKidsCheck
set_option autoImplicit false
-- NOT BUILT (no build run yet).
-- U-A1 check. Expected statements are written from the Lean text of AUDIT_CARRIER_FREEZE §2 / §6, not from the implementation.
-- Mutants are well-typed variants; a rejection is by signature / defeq of a changed statement, NOT a semantic counterexample.
-- No instance of any premise (AuditE5, AuditE6, AuditE7, AuditE8, GraphAgrees) is constructed: not evidence of non-vacuity. No sorry / axiom / native_decide.

namespace Tests.Gen5.AuditUA1Check
open Lean Meta
open Sparkle.Compiler.Elab (MachineShape)
open Tools.ShippingGen2 Tools.ShippingGen5FG
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingSrm7Rank (CallGraph declRank InClass)
open Tools.ShippingSrm15Graph (graphOf FirstOcc)
open Tools.ShippingMemCloses (memKey)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingGen5NameKids2 (MemTagsNamed)
open Tools.ShippingGen5NameKids3 (GraphAgrees ReachSpans OrdPath ReachClosed)
open Tools.ShippingGen5AuditCarrier
open Tests.Gen3.ExpectedType (stmtOf checkAxioms)
open Tests.Gen5.NameKidsCheck (cmpEqR cmpTeleR checkExpectedR checkMutantR reachWith auditRoot failsAudit)

/-! ## 1. Independent Expected carrier (freeze §2 text; own names, compared by value to the implementation defs) -/
section Exp
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

def ExpSOf (P : Pkgs ι dom) : Name → Option MachineShape := fun c => (P c).map (fun q => q.d.shape)

def ExpE1 (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∀ (k : Nat) (hk : k < sp.insts.length) (k' : Nat) (hk' : k' < sp.insts.length),
      memKey (originAt sp k) ≠ none → memKey (originAt sp k) = memKey (originAt sp k') →
      (sp.insts[k]'hk).1 = (sp.insts[k']'hk').1
def ExpE2 (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∀ (k : Nat) (hk : k < sp.insts.length), memKey (originAt sp k) = none → (sp.insts[k]'hk).1 ≠ c
def ExpE5 (P : Pkgs ι dom) (Reach : Name → Prop) (ds : List (Name × MachineData)) (B : Nat) (top : Name) : Prop :=
  GraphAgrees (graphOf ds) Reach (SOf P) ∧ ReachSpans (graphOf ds) top Reach ∧
  InClass (graphOf ds) B top = true ∧
  (∀ c, Reach c → ∀ sp, SOf P c = some sp → MemTagsNamed sp)
def ExpE6 (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∃ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo)
      (senv : Sparkle.Compiler.Elab.StructEnv) (ai : Bool),
      Tools.ShippingReaderFuel.machineShapeF n sm ps ci senv ai = some (some sp)
def ExpE7 (P : Pkgs ι dom) (Reach : Name → Prop) (ds : List (Name × MachineData)) : Prop :=
  ∀ c, Reach c → ∃ d : MachineData, FirstOcc ds c d ∧ SOf P c = some d.shape
def ExpE8 (ds : List (Name × MachineData)) (B : Nat) (top : Name) : Prop :=
  (ds.map Prod.fst).eraseDups.length = ds.length ∧ (declRank (graphOf ds) B top).isSome = true
def ExpE9 (P : Pkgs ι dom) (ds : List (Name × MachineData)) (top : Name) : Prop :=
  GraphAgrees (graphOf ds) (OrdPath (graphOf ds) top) (SOf P)

/-! ## 2. Expected theorem statements (freeze §6 `#check` text, binders written out) -/
def ExpReachClosedTgtRun : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (top : Name), ReachClosed (TgtRun P top) (SOf P)
def ExpReachSpansTgtRun : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (top : Name) {g : CallGraph} (hg : GraphAgrees g (TgtRun P top) (SOf P)),
    ReachSpans g top (TgtRun P top)
def ExpIffOrdPath : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (top : Name) {g : CallGraph} (hg : GraphAgrees g (TgtRun P top) (SOf P)) (c : Name),
    TgtRun P top c ↔ OrdPath g top c
def ExpE9OfTgtRun : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (top : Name) {ds : List (Name × MachineData)}
    (hg : GraphAgrees (graphOf ds) (TgtRun P top) (SOf P)), ExpE9 P ds top
def ExpE1OfE5 : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (Reach : Name → Prop) {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (h : ExpE5 P Reach ds B top), ExpE1 P Reach
def ExpE2OfE5 : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (Reach : Name → Prop) {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (h : ExpE5 P Reach ds B top), ExpE2 P Reach
def ExpE5OfParts : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (Reach : Name → Prop) {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (hfo : ExpE7 P Reach ds) (hnr : ExpE8 ds B top)
    (hsp : ReachSpans (graphOf ds) top Reach) (hF : ExpE6 P Reach), ExpE5 P Reach ds B top
def ExpE5TgtRun : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    {P : Pkgs ι dom} {top : Name} {ds : List (Name × MachineData)} {B : Nat}
    (hfo : ExpE7 P (TgtRun P top) ds) (hnr : ExpE8 ds B top) (hF : ExpE6 P (TgtRun P top)),
    ExpE5 P (TgtRun P top) ds B top ∧ ExpE9 P ds top

/-! ## 3. Mutants (signature/defeq rejection, not semantic counterexamples) -/
def MutE1NoHyp : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (Reach : Name → Prop), ExpE1 P Reach
def MutE1ConclE2 : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (Reach : Name → Prop) {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (h : ExpE5 P Reach ds B top), ExpE2 P Reach
def MutE2ConclE1 : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (Reach : Name → Prop) {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (h : ExpE5 P Reach ds B top), ExpE1 P Reach
def MutE5NoHsp : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (Reach : Name → Prop) {ds : List (Name × MachineData)} {B : Nat} {top : Name}
    (hfo : ExpE7 P Reach ds) (hnr : ExpE8 ds B top) (hF : ExpE6 P Reach), ExpE5 P Reach ds B top
def MutE9ReachTrue : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (top : Name) {ds : List (Name × MachineData)}
    (hg : GraphAgrees (graphOf ds) (fun _ => True) (SOf P)), ExpE9 P ds top
def MutSpansNoHg : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (top : Name) {g : CallGraph}, ReachSpans g top (TgtRun P top)
def MutClosedSNone : Prop := ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
    (P : Pkgs ι dom) (top : Name), ReachClosed (TgtRun P top) (fun _ => none)
end Exp

/-! ## 4. Carrier def bodies against the independent defs (value comparison, reducible) -/
def cmpDefValue (impl exp : Name) : MetaM Unit := do
  let some (.defnInfo a) := (← getEnv).find? impl | throwError "NK CHECK FAILED {impl}: not a def"
  let some (.defnInfo e) := (← getEnv).find? exp | throwError "NK CHECK FAILED {exp}: not a def"
  cmpEqR s!"def type {impl} vs {exp}" a.type e.type
  cmpEqR s!"def body {impl} vs {exp}" a.value e.value
  logInfo m!"AUDIT UA1 DEF OK {impl} against {exp}"

/-! ## 5. Fully qualified constant sets (binder/conclusion constants of the statement), decoy negative control -/
namespace Decoy
-- same-suffix names in another namespace
def SOf : Nat := 0
def AuditE1 : Nat := 0
def AuditE2 : Nat := 0
def AuditE5 : Nat := 0
def AuditE6 : Nat := 0
def AuditE7 : Nat := 0
def AuditE8 : Nat := 0
def AuditE9 : Nat := 0
def GraphAgrees : Nat := 0
def ReachSpans : Nat := 0
end Decoy

def carrierNames : List Name :=
  [``SOf, ``AuditE1, ``AuditE2, ``AuditE5, ``AuditE6, ``AuditE7, ``AuditE8, ``AuditE9,
   ``GraphAgrees, ``ReachSpans, ``ReachClosed, ``OrdPath, ``TgtRun]

/-- fully qualified carrier/Reach constants occurring in the statement of `thm` -/
def usedCarrier (thm : Name) : MetaM (List Name) := do
  let t ← stmtOf thm
  let used := t.getUsedConstants
  pure (carrierNames.filter fun n => used.contains n)

def expectSet (thm : Name) (exp : List Name) : MetaM Unit := do
  let got ← usedCarrier thm
  unless exp.all got.contains && got.all exp.contains do
    throwError "AUDIT UA1 SET FAILED {thm}: expected {exp}, got {got}"
  -- negative control: a same-suffix decoy name is never accepted for a required name
  for n in exp do
    let decoy := `Tests.Gen5.AuditUA1Check.Decoy ++ n.componentsRev.head!.toString.toName
    if got.contains decoy then throwError "AUDIT UA1 DECOY PRESENT {thm}: {decoy}"
  logInfo m!"AUDIT UA1 SET OK {thm}: {exp}"

/-! ## 6. Run -/
run_cmd Lean.Elab.Command.liftTermElabM do
  cmpDefValue ``SOf ``ExpSOf
  cmpDefValue ``AuditE1 ``ExpE1
  cmpDefValue ``AuditE2 ``ExpE2
  cmpDefValue ``AuditE5 ``ExpE5
  cmpDefValue ``AuditE6 ``ExpE6
  cmpDefValue ``AuditE7 ``ExpE7
  cmpDefValue ``AuditE8 ``ExpE8
  cmpDefValue ``AuditE9 ``ExpE9
  logInfo m!"AUDIT UA1 DEFS: 8 carrier defs compared by type and value against independent definitions"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpectedR ``reachClosed_tgtRun ``ExpReachClosedTgtRun
  checkExpectedR ``reachSpans_tgtRun ``ExpReachSpansTgtRun
  checkExpectedR ``tgtRun_iff_ordPath ``ExpIffOrdPath
  checkExpectedR ``auditE9_of_tgtRun ``ExpE9OfTgtRun
  checkExpectedR ``auditE1_of_E5 ``ExpE1OfE5
  checkExpectedR ``auditE2_of_E5 ``ExpE2OfE5
  checkExpectedR ``auditE5_of_parts ``ExpE5OfParts
  checkExpectedR ``auditE5_tgtRun ``ExpE5TgtRun
  logInfo m!"AUDIT UA1 TYPE: 8 theorems against Expected"

/-! Mutants: signature/defeq rejection only -/
run_cmd Lean.Elab.Command.liftTermElabM do
  checkMutantR ``auditE1_of_E5 ``MutE1NoHyp
  checkMutantR ``auditE1_of_E5 ``MutE1ConclE2
  checkMutantR ``auditE2_of_E5 ``MutE2ConclE1
  checkMutantR ``auditE5_of_parts ``MutE5NoHsp
  checkMutantR ``auditE9_of_tgtRun ``MutE9ReachTrue
  checkMutantR ``reachSpans_tgtRun ``MutSpansNoHg
  checkMutantR ``reachClosed_tgtRun ``MutClosedSNone
  logInfo m!"AUDIT UA1 MUTANT: 7 rejected (signature/defeq, not semantic counterexamples)"

/-! Binder/conclusion constant sets by fully qualified name; decoys in `Decoy` namespace never present -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let A := `Tools.ShippingGen5AuditCarrier
  let N3 := `Tools.ShippingGen5NameKids3
  expectSet ``reachClosed_tgtRun [A ++ `SOf, N3 ++ `ReachClosed, ``TgtRun]
  expectSet ``reachSpans_tgtRun [A ++ `SOf, N3 ++ `GraphAgrees, N3 ++ `ReachSpans, ``TgtRun]
  expectSet ``auditE9_of_tgtRun [A ++ `SOf, A ++ `AuditE9, N3 ++ `GraphAgrees, ``TgtRun]
  expectSet ``auditE1_of_E5 [A ++ `AuditE1, A ++ `AuditE5]
  expectSet ``auditE2_of_E5 [A ++ `AuditE2, A ++ `AuditE5]
  expectSet ``auditE5_of_parts [A ++ `AuditE5, A ++ `AuditE6, A ++ `AuditE7, A ++ `AuditE8, N3 ++ `ReachSpans]
  expectSet ``auditE5_tgtRun [A ++ `AuditE5, A ++ `AuditE6, A ++ `AuditE7, A ++ `AuditE8, A ++ `AuditE9, ``TgtRun]
  -- negative control: the decoy set is rejected by the same comparison
  let bad ← try expectSet ``auditE1_of_E5 [`Tests.Gen5.AuditUA1Check.Decoy.AuditE1, A ++ `AuditE5]; pure false catch _ => pure true
  unless bad do throwError "AUDIT UA1 DECOY ACCEPTED"
  logInfo m!"AUDIT UA1 BINDERS: 7 sets by qualified name; decoy negative 1 rejected"

/-! Premise-supply table (computed from the theorem statements: which theorem concludes each D.E row's carrier prop) -/
def concHead (thm : Name) : MetaM Name := do
  forallTelescope (← stmtOf thm) fun _ c => pure c.getAppFn.constName!

run_cmd Lean.Elab.Command.liftTermElabM do
  let A := `Tools.ShippingGen5AuditCarrier
  let rows : List (String × Name × List Name) :=
    [("D.E-1 hmemSame", A ++ `AuditE1, [``auditE1_of_E5]),
     ("D.E-2 hself", A ++ `AuditE2, [``auditE2_of_E5]),
     ("D.E-5 hsp (ReachSpans)", `Tools.ShippingGen5NameKids3.ReachSpans, [``reachSpans_tgtRun]),
     ("D.E-5 (whole, parts)", A ++ `AuditE5, [``auditE5_of_parts, ``auditE5_tgtRun]),
     ("D.E-9 OrdPath GraphAgrees", A ++ `AuditE9, [``auditE9_of_tgtRun])]
  for (row, head, thms) in rows do
    for t in thms do
      let h ← concHead t
      let ok := h == head || (row.startsWith "D.E-5 (whole" && h == ``And)
      unless ok do throwError "AUDIT UA1 SUPPLY TABLE: {t} concludes {h}, expected {head}"
      logInfo m!"AUDIT UA1 SUPPLY {row} <- {t} (premises remain: see COUNTS)"
  logInfo m!"AUDIT UA1 SUPPLY: E-1 <- auditE1_of_E5 [prem E-5]; E-2 <- auditE2_of_E5 [prem E-5]; E-5 hsp <- reachSpans_tgtRun [prem GraphAgrees on TgtRun]; E-9 <- auditE9_of_tgtRun [prem GraphAgrees on TgtRun]; E-5 whole <- auditE5_of_parts / auditE5_tgtRun [prem E-6, E-7, E-8]"

/-! Closure and axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let thms := [``reachClosed_tgtRun, ``reachSpans_tgtRun, ``tgtRun_iff_ordPath, ``auditE9_of_tgtRun,
    ``auditE1_of_E5, ``auditE2_of_E5, ``auditE5_of_parts, ``auditE5_tgtRun]
  -- negative control: a root using ofReduceBool is rejected by the same walker
  let bad ← failsAudit env.find? ``Lean.ofReduceBool
  unless bad do throwError "AUDIT UA1 CLOSURE CONTROL: forbidden root accepted"
  for r in thms do
    let a ← auditRoot env.find? r
    logInfo m!"AUDIT UA1 CLOSURE {r}: no ofReduceBool / sorryAx / trustCompiler, no unresolved name; visited {a.visited} constants"
  for n in thms do
    checkAxioms n

/-! COUNTS -/
run_cmd Lean.Elab.Command.liftTermElabM do
  logInfo m!"AUDIT UA1 COUNTS: theorems 8; carrier defs 8 (SOf, AuditE1/2/5/6/7/8/9); TYPE 8; MUTANT 7 (signature/defeq, not semantic); BINDER sets 7 + decoy 1; SUPPLY rows 4 (E-1, E-2, E-5, E-9); CLOSURE 8 + control 1; AXIOMS 8 (standard three only); premise delta 0 (no new premise); sorry 0"

end Tests.Gen5.AuditUA1Check
