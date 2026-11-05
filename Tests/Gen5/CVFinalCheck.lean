import Lean
import Tools.ShippingGen5CVFinal
import Tests.Gen5.CVTopCheck
set_option autoImplicit false
-- D.D-4 final check (Issue sparkle-ledger-dd4-final). No sorry / axiom / native_decide.

/-! # `FGLedgerPremisesStmtH` vs `FGLedgerPremisesStmtCV`: census, premise-to-ledger table, controls

One walk of the two telescopes (as in `SM1Check`): old binders are instantiated by the same-named new fvar, except the old `CV` which becomes `CVFinal PT` for the new fvar `PT`.
Required: removed = [CV]; added (outer) = [PT, h_D_LBR]; changed = []; the first conjunct `ConstValueFunctional (CVFinal PT)` `==`; the inner hypotheses of the second conjunct: none removed,
exactly the four premises added (`KernelClosedInvariant`, `LitRows`, `OblRowTypedV`, `∀ c ls, RowTeleEvAt`) between `EntryWitness` and `h_A_P06`; the conclusion `==` after the substitution.
Then: every named premise constant occurs in the statement, none of them is in `scripts/gen2/PREMISE_LEDGER.md` (new rows; the nearest existing rows are D.D-4 / D.D-5),
no binder of type `ConstValueRel` is left, the standard-axiom check, and controls. -/
open Lean Meta

namespace Tests.Gen5.CVFinalCheck
open Tools.ShippingGen5CVFinal

structure Diff where
  removed : List Name
  added : List Name
  changed : List Name
  firstConj : Bool
  innerRemoved : Nat
  innerAdded : List Name   -- head constants of the added inner hypotheses
  concl : Bool
deriving Repr

def baseName (x : Expr) : MetaM Name := return (← x.fvarId!.getDecl).userName.eraseMacroScopes

def valOf (n : Name) : MetaM Expr := do
  let some v := (← getConstInfo n).value? (allowOpaque := true) | throwError "{n}: no value"
  return v

/-- A short head description: the head constant, looking under `∀`. -/
partial def headOf (e : Expr) : MetaM Name := do
  match e with
  | .forallE _ _ b _ => do
    forallTelescope e fun _ c => do
      let h := c.getAppFn
      if h.isConst then return h.constName! else headOf b
  | _ => return e.getAppFn.constName?.getD `_

/-- Walk two telescopes: `tele` returns (binders, body). `sub` maps an old binder name to the replacement of the old fvar. -/
def compareCV (old new : Name) (mkRepl : Array Expr → Array Name → MetaM (Option (Name × Expr))) : MetaM Diff := do
  let ov ← valOf old
  let nv ← valOf new
  forallTelescope ov fun xo co => forallTelescope nv fun xn cn => do
    let nameN ← xn.mapM baseName
    let mut consumed := Array.replicate xn.size false
    let mut olds : Array Expr := #[]
    let mut news : Array Expr := #[]
    let mut removed : List Name := []
    let mut changed : List Name := []
    let repl ← mkRepl xn nameN
    for x in xo do
      let d ← x.fvarId!.getDecl
      let nm := d.userName.eraseMacroScopes
      let ty := d.type.replaceFVars olds news
      let cand := (List.range xn.size).find? fun j => !consumed[j]! && nameN[j]! == nm
      match cand with
      | some j =>
        consumed := consumed.set! j true
        unless ty == (← xn[j]!.fvarId!.getDecl).type do changed := changed ++ [nm]
        olds := olds.push x; news := news.push xn[j]!
      | none =>
        removed := removed ++ [nm]
        if let some (rn, re) := repl then
          if rn == nm then olds := olds.push x; news := news.push re
    let added := (List.range xn.size).filter (!consumed[·]!) |>.map (nameN[·]!)
    let co := co.replaceFVars olds news
    -- conclusion: `And a b`
    let (firstConj, innerRemoved, innerAdded, concl) ← do
      if co.isAppOfArity ``And 2 && cn.isAppOfArity ``And 2 then
        let fc := co.appFn!.appArg! == cn.appFn!.appArg!
        let bo := co.appArg!
        let bn := cn.appArg!
        forallTelescope bo fun yo cbo => forallTelescope bn fun yn cbn => do
          let mut used := Array.replicate yn.size false
          let mut so : Array Expr := #[]
          let mut sn : Array Expr := #[]
          let mut rem := 0
          for y in yo do
            let t := (← y.fvarId!.getDecl).type.replaceFVars so sn
            let mut found := false
            for j in [0:yn.size] do
              if !found && !used[j]! && t == (← yn[j]!.fvarId!.getDecl).type then
                used := used.set! j true; found := true
                so := so.push y; sn := sn.push yn[j]!
            unless found do rem := rem + 1
          let mut ad : List Name := []
          for j in [0:yn.size] do
            unless used[j]! do ad := ad ++ [← headOf (← yn[j]!.fvarId!.getDecl).type]
          pure (fc, rem, ad, cbo.replaceFVars so sn == cbn)
      else pure (false, 0, [], false)
    return { removed, added, changed, firstConj, innerRemoved, innerAdded, concl }

def H := ``Tools.ShippingGen5SM1.FGLedgerPremisesStmtH
def G := ``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtG
def C := ``Tools.ShippingGen5CVFinal.FGLedgerPremisesStmtCV

/-- Replacement of the old `CV` by `CVFinal PT` (`PT` the new fvar). -/
def cvRepl (target : Expr → Expr) : Array Expr → Array Name → MetaM (Option (Name × Expr)) := fun xn nameN => do
  let some j := (List.range xn.size).find? fun j => nameN[j]! == `PT | return none
  return some (`CV, target xn[j]!)

def finalRepl : Expr → Expr := fun pt => mkApp (mkConst ``Tools.ShippingGen5CVFinal.CVFinal) pt
def topRepl : Expr → Expr := fun _ => mkConst ``Tests.Gen5.CVTopCheck.cvTop

def okCV (d : Diff) : Bool :=
  d.removed == [`CV] && d.added == [`PT, `h_D_LBR] && d.changed.isEmpty && d.firstConj && d.innerRemoved == 0 &&
  d.innerAdded == [``Tools.ShippingGen5EnvDeclClosed.KernelClosedInvariant, ``Tools.ShippingGen5CVFinal.LitRows,
    ``Tools.ShippingGen5RowTypedV.OblRowTypedV, ``Tools.ShippingGen5ConstValueEVL.RowTeleEvAt] && d.concl

def isEmptyDiff (d : Diff) : Bool :=
  d.removed.isEmpty && d.added.isEmpty && d.changed.isEmpty && d.firstConj && d.innerRemoved == 0 && d.innerAdded.isEmpty && d.concl

/-- Binders (outer telescope) whose type is `ConstValueRel`. -/
def cvBinders (n : Name) : MetaM Nat := do
  forallTelescope (← valOf n) fun xs _ => do
    let mut c := 0
    for x in xs do
      if (← x.fvarId!.getDecl).type.isConstOf ``Tools.ShippingGen5DeclConnect.ConstValueRel then c := c + 1
    return c

def outerCount (n : Name) : MetaM Nat := do forallTelescope (← valOf n) fun xs _ => return xs.size

def innerCount (n : Name) : MetaM Nat := do
  forallTelescope (← valOf n) fun _ co => do
    if co.isAppOfArity ``And 2 then forallTelescope co.appArg! fun ys _ => return ys.size else return 0

/-- Axioms of a declaration are among the three standard ones (no `sorryAx`, no `Lean.ofReduceBool`, no user axiom). -/
def stdAxioms (n : Name) : CoreM (Bool × List Name) := do
  let ax ← Lean.collectAxioms n
  let ok := ax.all fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound
  return (ok, ax.toList)

/-! ## Model tables for the controls -/

def PTnil : Tools.ShippingGen5ConstValueEKey.PrimTableK := ⟨fun _ _ => none, fun _ _ => none⟩

/-- A table with exactly the two literal rows. -/
def PTlit : Tools.ShippingGen5ConstValueEKey.PrimTableK :=
  ⟨fun c ls => if c = `Nat ∧ ls = [] then some ⟨[], fun _ => some Nat⟩ else if c = `String ∧ ls = [] then some ⟨[], fun _ => some String⟩ else none,
   fun _ _ => none⟩

theorem not_litRows_nil (env : Environment) : ¬ LitRows PTnil env := by
  rintro ⟨rn, rs, hn, -⟩
  simp [PTnil] at hn

theorem litRows_lit (env : Environment) (hN : ¬ Tools.ShippingGen5ConstValueE.IsDefn env `Nat)
    (hS : ¬ Tools.ShippingGen5ConstValueE.IsDefn env `String) : LitRows PTlit env :=
  ⟨⟨[], fun _ => some Nat⟩, ⟨[], fun _ => some String⟩, by simp [PTlit], hN, rfl, rfl, by simp [PTlit], hS, rfl, rfl⟩

/-- The row premises do not constrain the empty table: they are satisfied by `PTnil` (so `PT` stays free: this is the G-PRIM question). -/
theorem rows_nil (env : Environment) :
    Tools.ShippingGen5RowTypedV.OblRowTypedV PTnil env ∧
    (∀ (c : Name) (ls : List Level), Tools.ShippingGen5ConstValueEVL.RowTeleEvAt PTnil env c ls) :=
  ⟨fun c ls => Tools.ShippingGen5RowTypedV.rowTypedAtV_of_none _ _ c ls rfl,
   fun c ls => Tools.ShippingGen5ConstValueEVL.rowTeleEvAt_of_none _ _ c ls rfl⟩

/-- The refutation of `CVTopCheck` needs the carrier to be a universally quantified relation; the final carrier is functional for every `PT`. -/
theorem cv_not_top (PT : Tools.ShippingGen5ConstValueEKey.PrimTableK) (env : Environment) :
    ¬ (CVFinal PT = Tests.Gen5.CVTopCheck.cvTop) := cvFinal_ne_top PT env

/-- The first conjunct of the CV statement is a theorem: the step that refuted G (`cvTop_not_functional`) has no counterpart. -/
theorem first_conjunct_proved (PT : Tools.ShippingGen5ConstValueEKey.PrimTableK) :
    Tools.ShippingGen5FG.ConstValueFunctional (CVFinal PT) := cvFinal_functional PT

def premiseConsts : List Name :=
  [``Tools.ShippingGen5ConstValueESoundK.OblLbrZero, ``Tools.ShippingGen5EnvDeclClosed.KernelClosedInvariant, ``Tools.ShippingGen5CVFinal.LitRows,
   ``Tools.ShippingGen5RowTypedV.OblRowTypedV, ``Tools.ShippingGen5ConstValueEVL.RowTeleEvAt]

/-- Short names as they appear in the ledger text. -/
def ledgerNeedles : List (Name × String) :=
  [(``Tools.ShippingGen5ConstValueESoundK.OblLbrZero, "OblLbrZero"), (``Tools.ShippingGen5EnvDeclClosed.KernelClosedInvariant, "KernelClosedInvariant"),
   (``Tools.ShippingGen5ConstValueESL.EnvDeclClosed, "EnvDeclClosed"), (``Tools.ShippingGen5CVFinal.LitRows, "LitRows"),
   (``Tools.ShippingGen5RowTypedV.RowTypedAtV, "RowTypedAtV"), (``Tools.ShippingGen5RowTypedV.OblRowTypedV, "OblRowTypedV"),
   (``Tools.ShippingGen5ConstValueEVL.RowTeleEvAt, "RowTeleEvAt")]

run_meta do
  -- 1. census H vs CV
  let d ← compareCV H C (cvRepl finalRepl)
  unless okCV d do throwError "H vs CV: unexpected diff {repr d}"
  let dG ← compareCV G C (cvRepl finalRepl)  -- G vs CV: removes CV, initsOf, hs
  -- controls on the census
  if okCV (← compareCV H C (fun _ _ => pure none)) then throwError "CONTROL: census passes without substituting CV := CVFinal PT"
  if okCV (← compareCV H C (cvRepl topRepl)) then throwError "CONTROL: census passes with CV := cvTop"
  unless isEmptyDiff (← compareCV H H (fun _ _ => pure none)) do throwError "CONTROL: H against itself is not empty"
  if okCV (← compareCV C H (fun _ _ => pure none)) then throwError "CONTROL: CV against H passes (direction)"
  if dG.removed == [`CV] then throwError "CONTROL: G vs CV removes only CV: {repr dG}"
  -- 2. binders
  let (cH, cC) := (← cvBinders H, ← cvBinders C)
  unless cH == 1 && cC == 0 do throwError "ConstValueRel binders: H {cH}, CV {cC}"
  let (oH, oC, iH, iC) := (← outerCount H, ← outerCount C, ← innerCount H, ← innerCount C)
  unless oC == oH + 1 && iC == iH + 4 do throwError "binder counts: outer {oH} -> {oC}, inner {iH} -> {iC}"
  -- 3. premises occur in the statement; PT is a PrimTableK binder, h_D_LBR is OblLbrZero
  let env ← getEnv
  let used := (← valOf C).getUsedConstants
  for p in premiseConsts do
    unless used.contains p do throwError "premise {p} does not occur in the statement"
  unless used.contains ``Tools.ShippingGen5CVFinal.CVFinal do throwError "CVFinal does not occur"
  forallTelescope (← valOf C) fun xs _ => do
    let mut found := false
    for x in xs do
      let dx ← x.fvarId!.getDecl
      if dx.userName.eraseMacroScopes == `PT then
        found := true
        unless dx.type.isConstOf ``Tools.ShippingGen5ConstValueEKey.PrimTableK do throwError "PT is not a PrimTableK"
    unless found do throwError "no PT"
  -- 4. ledger correspondence (text lookup in the premise ledger)
  let ledger : String ← (try IO.FS.readFile "scripts/gen2/PREMISE_LEDGER.md" catch _ => pure "")
  let mut tbl : List String := []
  if ledger.isEmpty then
    logInfo "LEDGER: scripts/gen2/PREMISE_LEDGER.md not readable from the build copy; correspondence not checked here"
  else
    for (n, s) in ledgerNeedles do
      unless env.contains n do throwError "{n} does not exist"
      let hit := (ledger.splitOn s).length - 1
      if hit != 0 then throwError "ledger already mentions {s} ({hit} times): not a new row"
      tbl := tbl ++ [s!"{s}: 0 mentions"]
    for id in ["| D.D-4 |", "| D.D-5 |"] do
      if (ledger.splitOn id).length < 2 then throwError "ledger has no row {id}"
    tbl := tbl ++ ["rows D.D-4 / D.D-5 present"]
  -- 5. axioms
  let thms := [``Tools.ShippingGen5CVFinal.cvFinal_functional, ``Tools.ShippingGen5CVFinal.cvFinal_typed, ``Tools.ShippingGen5CVFinal.cvFinal_ne_top,
    ``Tools.ShippingGen5CVFinal.declConnect_cvFinal_iff, ``Tools.ShippingGen5CVFinal.declConnect_cvFinal_typed,
    ``Tools.ShippingGen5CVFinal.fgLedgerPremisesStmtCV_of_H, ``Tools.ShippingGen5CVFinal.fgLedgerPremisesStmtCV_of_G,
    ``Tools.ShippingGen5CVFinal.envDeclClosed_of_premises, ``Tests.Gen5.CVFinalCheck.not_litRows_nil, ``Tests.Gen5.CVFinalCheck.litRows_lit,
    ``Tests.Gen5.CVFinalCheck.rows_nil, ``Tests.Gen5.CVFinalCheck.cv_not_top]
  for t in thms do
    let (ok, ax) ← stdAxioms t
    unless ok do throwError "{t}: non-standard axioms {ax}"
  -- axiom detector control: a declaration with a user axiom and one using sorryAx are flagged
  let axName : Name := `Tests.Gen5.CVFinalCheck.ctrlAx
  addDecl (.axiomDecl { name := axName, levelParams := [], type := mkConst ``False, isUnsafe := false })
  let (okA, _) ← stdAxioms axName
  if okA then throwError "CONTROL: axiom detector misses a user axiom"
  let thmName : Name := `Tests.Gen5.CVFinalCheck.ctrlThm
  addDecl (.thmDecl { name := thmName, levelParams := [], type := mkConst ``False, value := mkConst axName })
  let (okT, _) ← stdAxioms thmName
  if okT then throwError "CONTROL: axiom detector misses a theorem that uses a user axiom"
  -- 6. summary
  logInfo m!"CVFINAL CHECK: 1 statement pair (FGLedgerPremisesStmtH vs FGLedgerPremisesStmtCV): removed {repr d.removed}, added (outer) {repr d.added}, changed {repr d.changed}, first conjunct ==, inner hypotheses removed {d.innerRemoved}, added {repr d.innerAdded}, conclusion == after CV := CVFinal PT; ConstValueRel binders H {cH} -> CV {cC}; outer binders {oH} -> {oC}, inner hypotheses {iH} -> {iC}; named premises 5 (1 outer, 4 inner), ledger: {tbl}; G vs CV also removes {repr dG.removed} (added {repr dG.added}); controls: no substitution fails, CV := cvTop fails, H vs H empty, CV vs H fails, axiom detector flags user axiom/theorem; standard axioms for {thms.length} declarations"

end Tests.Gen5.CVFinalCheck

#print axioms Tests.Gen5.CVFinalCheck.not_litRows_nil
#print axioms Tests.Gen5.CVFinalCheck.litRows_lit
#print axioms Tests.Gen5.CVFinalCheck.rows_nil
#print axioms Tests.Gen5.CVFinalCheck.cv_not_top
#print axioms Tests.Gen5.CVFinalCheck.first_conjunct_proved
