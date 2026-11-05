import Lean
import Tools.ShippingGen5AP17
import Tools.ShippingGen5AuditE3B3ND
import Tools.ShippingGen5SM7
import Tools.ShippingGen2MemShips
set_option autoImplicit false
-- A.P-12 scan (Issue sparkle-ledger-shorten): no final FG root has a standalone `ExtInS` binder.

/-! # A.P-12: `ExtInS` only as a conjunct of the bundled rows T1L-11 / T1L-12

The explicit list `roots` is the final FG statement (`FGLedgerPremisesStmtR`, `FGLedgerPremisesStmtG`, the bridge
`fgLedgerPremisesStmtG_of_R`) and the roots of its assembly (the ND chain of A.P-17, the D.E-3 audit root, the C.SM-7 root,
the top consumer `stepDec_of_ties`). Every hypothesis type is collected by a structural walk: the binders of the telescope,
and, when the body is a conjunction, the hypotheses of each conjunct (the FG statement is `CVF ∧ ∀ declName …`). A hypothesis
is classified by the head of the body of ITS OWN telescope:
* STANDALONE: the head is `ExtInS` (e.g. `hext : ExtInS q`, `∀ q, DataOk q → ExtInS q`);
* BUNDLED: the body is `A ∧ B` with `ExtInS` as the head of `A` or `B` (e.g. `hMemRow : ∀ q, DataOk q → MemParentDataOk q ∧ ExtInS q`).
Expected: no STANDALONE in any root. POSITIVE control: `auditE3B3_of_t1hypND_run`'s `hMemRow` is BUNDLED. NEGATIVE controls:
the same type with one added binder `hext : ExtInS q` is STANDALONE-detected; `Tools.ShippingGen2.memParent_childShips`-style
theorems outside the list (`memParent_ships`, which takes `hext`) are detected as STANDALONE when scanned. -/
open Lean Meta

namespace Tests.Gen5.AP12ScanCheck

def roots : List Name :=
  [``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtR,
   ``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtG,
   ``Tools.ShippingGenFGLedgerPremises.fgLedgerPremisesStmtG_of_R,
   ``Tools.ShippingGenFGLedgerPremises.hDT1_of_genGP,
   ``Tools.ShippingGen2.decAt_ND,
   ``Tools.ShippingGen2.ihAt_stepPF_ND,
   ``Tools.ShippingGen2.ih_allPF_ND,
   ``Tools.ShippingGen2.t1_of_stepPF_ND,
   ``Tools.ShippingGen2.closingRun0_of_runT1_ND,
   ``Tools.ShippingGen2.closingRun_of_runT1_ND,
   ``Tools.ShippingGen2.servedShips0_runND,
   ``Tools.ShippingGen2.postFacts_of_runND,
   ``Tools.ShippingGen2.houtTy_of_realChildND,
   ``Tools.ShippingGen2.reach_callee_of_t1ND,
   ``Tools.ShippingGen2.houtTy_of_closingND,
   ``Tools.ShippingGen2.callTie_of_served_oneOut_t1ND,
   ``Tools.ShippingGen2.callTie_of_served_kidW_closing_t1ND,
   ``Tools.ShippingGen5AuditE3B3.machPrem3R_of_t1hypND,
   ``Tools.ShippingGen5AuditE3B3.auditE3B3_of_t1hypND_run,
   ``Tools.ShippingGen5SM7.hT2Tie_of_genGP,
   ``Tools.ShippingGen2.stepDec_of_ties]

def isExt (e : Expr) : Bool := e.getAppFn.isConstOf ``Tools.ShippingGen2.ExtInS

/-- 0 = unrelated, 1 = BUNDLED, 2 = STANDALONE. -/
def classify (ty : Expr) : MetaM Nat :=
  forallTelescopeReducing ty fun _ body => do
    let body ← whnfR body
    if isExt body then return 2
    match body.and? with
    | some (a, b) => return (if isExt a || isExt b then 1 else 0)
    | none => return 0

/-- All hypothesis types of `e` with their binder names: the telescope, and recursively the conjuncts of the body. -/
partial def hyps (e : Expr) : MetaM (List (Name × Nat)) :=
  forallTelescope e fun xs body => do
    let mut out : List (Name × Nat) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      out := out ++ [(d.userName, ← classify d.type)]
    match body.and? with
    | some (a, b) => return out ++ (← hyps a) ++ (← hyps b)
    | none => return out

def rootType (n : Name) : MetaM Expr := do
  let ci ← getConstInfo n
  match ci with
  | .defnInfo d => if d.type.isProp || (← isProp d.type) then return d.value else return ci.type
  | _ => return ci.type

run_meta do
  let mut standalone : List (Name × Name) := []
  let mut bundled : List (Name × Name) := []
  let mut total := 0
  for r in roots do
    let hs ← hyps (← rootType r)
    total := total + hs.length
    for (h, k) in hs do
      if k == 2 then standalone := standalone ++ [(r, h)]
      if k == 1 then bundled := bundled ++ [(r, h)]
  logInfo m!"AP12 roots {roots.length}, hypotheses {total}; BUNDLED {bundled}; STANDALONE {standalone}"
  -- POSITIVE control: the bundled T1L-12 row of the D.E-3 root is seen
  unless bundled.contains (``Tools.ShippingGen5AuditE3B3.auditE3B3_of_t1hypND_run, `hMemRow) do
    throwError "CONTROL: hMemRow of auditE3B3_of_t1hypND_run not classified BUNDLED"
  unless standalone.isEmpty do throwError "standalone ExtInS binders in final FG roots: {standalone}"
  -- NEGATIVE control 1: the audit root with one added binder `hext : ExtInS q` is detected
  let ci ← getConstInfo ``Tools.ShippingGen5AuditE3B3.auditE3B3_of_t1hypND_run
  let neg ← forallTelescope ci.type fun xs body => do
    let mut pkgTy? : Option Expr := none
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.userName == `hMemRow then
        if let .forallE _ pt _ _ := d.type then pkgTy? := some pt
    let some pkgTy := pkgTy? | throwError "no hMemRow"
    withLocalDeclD `q pkgTy fun q => do
      let ext ← mkAppM ``Tools.ShippingGen2.ExtInS #[q]
      withLocalDeclD `hext ext fun hx => mkForallFVars (xs ++ #[q, hx]) body
  let negHs ← hyps neg
  unless negHs.contains (`hext, 2) do throwError "NEG1: an added hext : ExtInS q binder is not detected"
  -- NEGATIVE control 2: a theorem outside the list that takes `hext` is detected when scanned
  let negHs2 ← hyps (← getConstInfo ``Tools.ShippingGen2.memParent_childShips).type
  unless negHs2.any (·.2 == 2) do throwError "NEG2: memParent_childShips's hext not detected"
  logInfo m!"AP12 NEG: added hext detected {negHs.contains (`hext, 2)}; memParent_childShips standalone {negHs2.filter (·.2 == 2)}"
  logInfo m!"AP12 COUNTS: roots {roots.length}, standalone 0, bundled {bundled.length}, controls 3"

end Tests.Gen5.AP12ScanCheck
