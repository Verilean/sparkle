import Tests.Compiler.Srm33AuditExpected
import Tests.Compiler.Srm9ComposedTest
import Tests.Compiler.Srm31EndpointTest
import Tools.ShippingSlotRegsRun
-- UNBUILT (unit SRM33): see REPORT-SRM33.md for run names.
-- Audit of Tools/ShippingSrm33Core.lean and Tests/Compiler/Srm33EndpointTest.lean (3 theorems):
-- (1) literal count guards; full binder tuples printed per theorem (S33PREM) and a marker per theorem (S33THM);
-- (2) STRUCTURAL comparator `walk` of each theorem against the generated Exp_* (scripts/srm33/gen_audit_expected.py: TEXT of the ORIGINAL theorems + scripts/srm33/EXPECTED.txt);
-- (3) T2 = the ORIGINAL `Srm9ComposedTest.topshare{M,Q}_hierC_at_free` with EXACTLY ONE row deleted (the hstR antecedent; `dropRow`, count = 1): every other binder, name, type, and the whole remaining conclusion is defeq;
-- (4) absence at every depth of the ∀/∃/∧ spine: no binder is hstR (mentions `seqRegs`) or hWd (mentions `declWidth` and `SlotField` jointly) in T2 or in T1's conclusion; controls: the originals / SRM31's `_at_nw` ARE detected;
-- (5) wrong-expected mutants rejected with the specific kind (hstR kept; hWd added; conclusion weakened; ` ∧ True`; added data binder; reordered binders), each non-vacuous (a Prop, self-equal);
-- (6) one witness: `topshare{M,Q}_composedNW_hWd` occurs ONCE in each endpoint proof; `topshare{M,Q}_composedNW` and `composedNWRegs_of_composedNW` once in each `_composedNW_hWd`; the generic theorem once;
--     closure: standard axioms, forbidden old-form roots absent, with positive controls.
set_option Elab.async false
set_option autoImplicit false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm33AuditTest
open Tests.Compiler.Srm33AuditExpected

theorem wrapper_mutation (p : Prop) (h : p) : p := h

def audited33 : List Name :=
  [``Tools.ShippingSrm33.machine_ships_hierC_noHstR,
   ``Tests.Compiler.Srm33EndpointTest.topshareM_hierC_noHstR, ``Tests.Compiler.Srm33EndpointTest.topshareQ_hierC_noHstR]

def pairs33 : List (Name × Name) :=
  [(audited33[0]!, ``Exp_generic), (audited33[1]!, ``Exp_M), (audited33[2]!, ``Exp_Q)]

/-- (real theorem, mutant, expected first-difference kind) -/
def mutants33 : List (Name × Name × String) :=
  [(audited33[0]!, ``Exp_generic_mut_hstrKept, "leaf"), (audited33[0]!, ``Exp_generic_mut_hWdAdded, "leaf"),
   (audited33[1]!, ``Exp_M_mut_hstrKept, "leaf"), (audited33[1]!, ``Exp_M_mut_hWdAdded, "leaf"), (audited33[1]!, ``Exp_M_mut_weak, "leaf"),
   (audited33[1]!, ``Exp_M_mut_withTrue, "type"), (audited33[1]!, ``Exp_M_mut_addedBinder, "info"), (audited33[1]!, ``Exp_M_mut_reordered, "type"),
   (audited33[2]!, ``Exp_Q_mut_hstrKept, "leaf"), (audited33[2]!, ``Exp_Q_mut_hWdAdded, "leaf"), (audited33[2]!, ``Exp_Q_mut_weak, "leaf"),
   (audited33[2]!, ``Exp_Q_mut_withTrue, "type"), (audited33[2]!, ``Exp_Q_mut_addedBinder, "info"), (audited33[2]!, ``Exp_Q_mut_reordered, "type")]

def stdAx : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Structural comparator: the list of differences (kind@path), empty iff the statements agree row by row. -/
partial def walk (path : String) (a e : Expr) : MetaM (List String) := do
  match a, e with
  | .forallE n1 d1 b1 bi1, .forallE n2 d2 _ bi2 =>
    let mut diffs : List String := []
    if bi1 != bi2 then diffs := diffs ++ [s!"info@{path}/{n1}"]
    if bi1 != .instImplicit && !n1.hasMacroScopes && !n2.hasMacroScopes && n1 != n2 then diffs := diffs ++ [s!"name@{path}/{n1}"]
    if (← isProp d1) != (← isProp d2) then diffs := diffs ++ [s!"isProp@{path}/{n1}"]
    unless (← isDefEq d1 d2) do diffs := diffs ++ [s!"type@{path}/{n1}"]
    let rest ← withLocalDecl n1 bi1 d1 fun x => do
      let .forallE _ _ b2 _ := e | return ["leaf@impossible"]
      walk (path ++ "/" ++ toString n1) (b1.instantiate1 x) (b2.instantiate1 x)
    return diffs ++ rest
  | _, _ =>
    if a.isAppOfArity ``Exists 2 && e.isAppOfArity ``Exists 2 then
      let ty1 := a.getArg! 0
      let ty2 := e.getArg! 0
      let mut diffs : List String := []
      unless (← isDefEq ty1 ty2) do diffs := diffs ++ [s!"type@{path}/∃"]
      match a.getArg! 1, e.getArg! 1 with
      | .lam n1 t1 b1 bi1, .lam n2 _ b2 _ =>
        if !n1.hasMacroScopes && !n2.hasMacroScopes && n1 != n2 then diffs := diffs ++ [s!"name@{path}/∃{n1}"]
        let rest ← withLocalDecl n1 bi1 t1 fun x => walk (path ++ "/∃" ++ toString n1) (b1.instantiate1 x) (b2.instantiate1 x)
        return diffs ++ rest
      | _, _ => return diffs ++ [s!"leaf@{path}/∃body"]
    else if a.isAppOfArity ``And 2 && e.isAppOfArity ``And 2 then
      let l ← walk (path ++ "/∧L") (a.getArg! 0) (e.getArg! 0)
      let r ← walk (path ++ "/∧R") (a.getArg! 1) (e.getArg! 1)
      return l ++ r
    else if (← isDefEq a e) then return [] else return [s!"leaf@{path}"]

def kindOf (s : String) : String := (s.splitOn "@").head!

def expType (n : Name) : MetaM Expr := do
  let ei ← getConstInfo n
  return ei.value?.getD (mkConst n)

def thmType (n : Name) : MetaM Expr := return (← getConstInfo n).type

/-- all binder types of a statement, descended through ∀ / ∃ / ∧ -/
partial def binderTypes (e : Expr) : MetaM (Array Expr) := do
  match e with
  | .forallE n d b bi =>
    let rest ← withLocalDecl n bi d fun x => binderTypes (b.instantiate1 x)
    return #[d] ++ rest
  | _ =>
    if e.isAppOfArity ``Exists 2 then
      match e.getArg! 1 with
      | .lam n t b bi => withLocalDecl n bi t fun x => binderTypes (b.instantiate1 x)
      | _ => return #[]
    else if e.isAppOfArity ``And 2 then
      return (← binderTypes (e.getArg! 0)) ++ (← binderTypes (e.getArg! 1))
    else return #[]

def mentionsSeqRegs (e : Expr) : Bool := e.getUsedConstants.contains ``Sparkle.IR.OptCheck.seqRegs

def restatesConclusion (thm : Name) : MetaM Bool := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs concl => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if (← isProp d.type) then
        if (← withReducible (isDefEq d.type concl)) then return true
    return false

partial def countConst (n : Name) (e : Expr) : Nat :=
  match e with
  | .const c _ => if c == n then 1 else 0
  | .app f a => countConst n f + countConst n a
  | .lam _ d b _ => countConst n d + countConst n b
  | .forallE _ d b _ => countConst n d + countConst n b
  | .letE _ t v b _ => countConst n t + countConst n v + countConst n b
  | .mdata _ b => countConst n b
  | .proj _ _ b => countConst n b
  | _ => 0

def valueOf (ci : ConstantInfo) : Expr :=
  match ci with
  | .thmInfo t => t.value
  | .defnInfo t => t.value
  | _ => mkConst `none

def reachAll (n : Name) : MetaM (Std.HashSet Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut todo : List Name := [n]
  let mut fuel := 600000
  while fuel > 0 && !todo.isEmpty do
    fuel := fuel - 1
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      if seen.contains c then continue
      seen := seen.insert c
      if let some ci := (← getEnv).find? c then
        let mut cs : Array Name := ci.type.getUsedConstants
        match ci with
          | .thmInfo t => cs := cs ++ t.value.getUsedConstants
          | .defnInfo t => cs := cs ++ t.value.getUsedConstants
          | _ => pure ()
        for d in cs do
          if !seen.contains d then todo := d :: todo
  return seen


def mentionsHWd (e : Expr) : Bool :=
  e.getUsedConstants.contains ``Sparkle.IR.RegDedup.declWidth && e.getUsedConstants.contains ``Sparkle.IR.Machine.SlotField

/-- delete every non-dependent ∀-row whose domain mentions `seqRegs` (= hstR); count them. -/
partial def dropRow (cnt : IO.Ref Nat) (e : Expr) : MetaM Expr := do
  match e with
  | .forallE n d b bi =>
    if mentionsSeqRegs d && !b.hasLooseBVar 0 then
      cnt.modify (· + 1)
      dropRow cnt (b.lowerLooseBVars 1 1)
    else return .forallE n (← dropRow cnt d) (← dropRow cnt b) bi
  | .lam n d b bi => return .lam n (← dropRow cnt d) (← dropRow cnt b) bi
  | .app f a => return .app (← dropRow cnt f) (← dropRow cnt a)
  | _ => return e


elab "#srm33_audit" : command => liftTermElabM do
  unless audited33.length == 3 && pairs33.length == 3 && mutants33.length == 14 do throwError "SRM33 AUDIT FAILED: literal count guard"
  -- (1) binder tables + markers
  for t in audited33 do
    let ci ← getConstInfo t
    logInfo m!"S33THM|{t}"
    forallTelescope ci.type fun xs concl => do
      let mut i : Nat := 0
      for x in xs do
        let d ← x.fvarId!.getDecl
        logInfo m!"S33PREM|{t}|{i}|{repr d.binderInfo}|{d.userName}|{← isProp d.type}"
        i := i + 1
      logInfo m!"S33CONC|{t}|{concl.getAppFn.constName?}"
  -- (2) comparator against the generated expected statements
  for (t, e) in pairs33 do
    match ← walk "" (← thmType t) (← expType e) with
    | [] => logInfo m!"S33TABLEOK|{t}|{e}"
    | d :: _ => throwError "SRM33 AUDIT FAILED: {t} differs from {e}: {d}"
  -- (3) the endpoints = the ORIGINAL endpoints minus exactly the hstR row
  for (t, o, eo) in [(audited33[1]!, ``Tests.Compiler.Srm9ComposedTest.topshareM_hierC_at_free, ``Exp_M_orig),
                     (audited33[2]!, ``Tests.Compiler.Srm9ComposedTest.topshareQ_hierC_at_free, ``Exp_Q_orig)] do
    match ← walk "" (← expType eo) (← thmType o) with
    | [] => pure ()
    | d :: _ => throwError "SRM33 AUDIT FAILED: generated {eo} differs from the actual original {o}: {d}"
    let cnt ← IO.mkRef 0
    let dropped ← dropRow cnt (← thmType o)
    unless (← cnt.get) == 1 do throwError "SRM33 AUDIT FAILED: {o} has {← cnt.get} hstR rows, expected exactly 1"
    let ds ← walk "" (← thmType t) dropped
    unless ds.isEmpty do throwError "SRM33 AUDIT FAILED: {t} vs {o} minus hstR: {ds}"
    forallTelescope (← thmType t) fun xs _ => do
      let ns ← xs.mapM (fun x => do return (← x.fvarId!.getDecl).userName)
      forallTelescope (← thmType o) fun ys _ => do
        let ms ← ys.mapM (fun y => do return (← y.fvarId!.getDecl).userName)
        unless ns.toList == ms.toList do throwError "SRM33 AUDIT FAILED: outer binder names of {t} differ from {o}"
        logInfo m!"S33BINDERS|{t}|{xs.size} outer binders, names identical to {o}"
    logInfo m!"S33ONEROW|{t}|{o}|exactly one row (hstR) deleted, everything else defeq; no replacement row"
  -- (4) mutants
  for (t, mname, want) in mutants33 do
    let mt ← expType mname
    unless (← isProp mt) do throwError "SRM33 AUDIT FAILED: mutant {mname} is not a Prop"
    unless (← walk "" mt mt).isEmpty do throwError "SRM33 AUDIT FAILED: mutant {mname} not self-equal (vacuous)"
    match ← walk "" (← thmType t) mt with
    | [] => throwError "SRM33 AUDIT FAILED: mutant {mname} ACCEPTED"
    | d :: _ =>
      unless kindOf d == want do throwError "SRM33 AUDIT FAILED: mutant {mname} rejected for {d}, expected kind {want}"
      logInfo m!"S33MUTREJECT|{mname}|{d}"
  -- (5) absence of hstR / hWd at every depth, restatement, with controls
  for t in audited33 do
    if (← restatesConclusion t) then throwError "SRM33 AUDIT FAILED: a hypothesis of {t} restates its conclusion"
    let ty ← thmType t
    -- generic: the `composed` binder legitimately carries the width link as P; inspect the conclusion only
    let region ← if t == audited33[0]! then
        forallTelescope ty fun xs concl => do
          let mut ds : Array Expr := #[]
          for x in xs do
            let d ← x.fvarId!.getDecl
            if d.userName != `composed then ds := ds.push d.type
          return ds ++ (← binderTypes concl)
      else binderTypes ty
    for bt in region do
      if mentionsSeqRegs bt then throwError "SRM33 AUDIT FAILED: a binder of {t} mentions seqRegs (hstR)"
      if mentionsHWd bt then throwError "SRM33 AUDIT FAILED: a binder of {t} is/restates hWd (declWidth + SlotField)"
  unless (← restatesConclusion ``Tests.Compiler.Srm33AuditTest.wrapper_mutation) do
    throwError "SRM33 AUDIT FAILED: control wrapper not detected"
  for o in [``Tests.Compiler.Srm9ComposedTest.topshareM_hierC_at_free, ``Tests.Compiler.Srm9ComposedTest.topshareQ_hierC_at_free] do
    unless (← binderTypes (← thmType o)).any mentionsSeqRegs do throwError "SRM33 AUDIT FAILED: control: hstR not detected in {o}"
  for o in [``Tests.Compiler.Srm31EndpointTest.topshareM_hierC_at_nw, ``Tests.Compiler.Srm31EndpointTest.topshareQ_hierC_at_nw] do
    unless (← binderTypes (← thmType o)).any mentionsHWd do throwError "SRM33 AUDIT FAILED: control: hWd not detected in {o}"
  logInfo "S33ABSENT|no binder of T1's conclusion / T2 (any depth) is hstR or hWd; controls: original (hstR) and SRM31 _at_nw (hWd) are detected by the same predicates"
  -- (6) one witness and closure
  let forbidden : List Name := [``Tools.ShippingMachineShipsDepth.composedG_of_NW, ``Tools.ShippingSlotRegsRun.slotRegs_runMT,
    ``Tools.ShippingSrm26.sourceRegsAreSlots_of_wired]
  let hw := ``Tests.Compiler.Srm32InstTest.topshareM_composedNW_hWd
  for (inst, comp, cw) in [(audited33[1]!, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_composedNW, ``Tests.Compiler.Srm32InstTest.topshareM_composedNW_hWd),
                       (audited33[2]!, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_composedNW, ``Tests.Compiler.Srm32InstTest.topshareQ_composedNW_hWd)] do
    let _ := hw
    let ci ← getConstInfo inst
    let cnt := countConst cw (valueOf ci)
    unless cnt == 1 do throwError "SRM33 AUDIT FAILED: {cw} occurs {cnt} times in {inst}, expected 1 (one witness)"
    let cg := countConst ``Tools.ShippingSrm33.machine_ships_hierC_noHstR (valueOf ci)
    unless cg == 1 do throwError "SRM33 AUDIT FAILED: the generic theorem occurs {cg} times in {inst}"
    let cw1 := countConst comp (valueOf (← getConstInfo cw))
    unless cw1 == 1 do throwError "SRM33 AUDIT FAILED: {comp} occurs {cw1} times in {cw}"
    let cw2 := countConst ``Tools.ShippingSrm28.composedNWRegs_of_composedNW (valueOf (← getConstInfo cw))
    unless cw2 == 1 do throwError "SRM33 AUDIT FAILED: composedNWRegs_of_composedNW occurs {cw2} times in {cw}"
    let r ← reachAll inst
    for f in forbidden do
      if r.contains f then throwError "SRM33 AUDIT FAILED: forbidden root {f} in the closure of {inst}"
    for must in [``Tools.ShippingSrm31.hstR_of_wired_slots, ``Tools.ShippingSrm28.sourceRegsAreSlots_of_wired_all, ``Tools.ShippingSrm32.hWd_of_wired, cw, comp] do
      unless r.contains must do throwError "SRM33 AUDIT FAILED: {must} missing from the closure of {inst}"
    logInfo m!"S33ONEWITNESS|{inst}|{cw} once, {comp} once inside it; forbidden roots absent"
  for t in audited33 do
    let ax ← Lean.collectAxioms t
    for a in ax do
      unless stdAx.contains a do throwError "SRM33 AUDIT FAILED: non-standard axiom {a} in {t}"
    logInfo m!"S33AXIOMS|{t}|{ax.toList}"
  unless (← reachAll ``Tests.Compiler.Srm9ComposedTest.topshareM_hierC_at_free).contains ``Tools.ShippingMachineShipsDepth.composedG_of_NW do
    throwError "SRM33 AUDIT FAILED: forbidden-root control (composedG_of_NW) not detected"
  unless (← reachAll ``Tools.ShippingSlotRegsRun.slotRegs_runMT).contains ``Tools.ShippingChildInv.MachineClosesAt do
    throwError "SRM33 AUDIT FAILED: forbidden-root control (MachineClosesAt) not detected"
  logInfo "S33AUDIT|ok"
#srm33_audit

end Tests.Compiler.Srm33AuditTest
end
