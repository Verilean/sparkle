import Lean
import Tools.ShippingGen5CR4
set_option autoImplicit false
-- C.CR-4 check (Issue sparkle-ledger-cr4). No sorry / axiom / native_decide.

/-! Structural `Expr` comparison of each ND root with its row-form counterpart, in ONE walk of the two telescopes. Old binders are
instantiated by the same-named new fvar (a repeated, e.g. hygienic, name is matched in order); the old `Reach` is instantiated
by `TgtRun P declName`. Per root: removed = the `T1HypND` binder (and `Reach`, replaced by `declName`); added ⊆ {declName, hpkg, hA6,
hcl}, each row `==` the existing row (hpkg / hcl: the `T1HypND.pkg` / `T1HypND.closes` field types at `Reach := TgtRun P declName`;
hA6: `h_A_P06` of `FGLedgerPremisesStmtG`); changed = []; conclusion `==`. The new type and value do not use `T1HypND`; the value uses
`t1HypND_of_rows`. Negative controls: self-comparison is empty; refusing to count `H` as removed fails; a mismatched pair fails. -/
open Lean Meta

namespace Tests.Gen5.CR4Check

structure Diff where
  hRemoved : Nat
  reachRepl : Bool
  otherRemoved : List Name
  added : List Name
  changed : List Name
  concl : Bool
  addedBad : List Name
deriving Repr

def unf : List Name := [``Tools.ShippingGen2.ServedShips0StmtND, ``Tools.ShippingGen2.PostFactsStmtND]

partial def tele {α : Type} (ty : Expr) (xs : Array Expr) (k : Array Expr → Expr → MetaM α) : MetaM α :=
  forallTelescope ty fun ys body => do
    let xs := xs ++ ys
    if let .const c _ := body.getAppFn then
      if unf.contains c then
        if let some b' ← unfoldDefinition? body then
          return ← tele b' xs k
    k xs body

def usesT (e : Expr) : Bool := e.getUsedConstants.contains ``Tools.ShippingGen2.T1HypND

def baseName (x : Expr) : MetaM Name := return (← x.fvarId!.getDecl).userName.eraseMacroScopes

/-- Every `genGP …` (7 arguments) becomes `P`; further arguments (the applied name) are kept. -/
def replaceGenGP (e : Expr) (P : Expr) : Expr :=
  e.replace fun s =>
    if s.getAppFn.constName? == some `Tools.ShippingGenFGLedgerPremises.genGP then
      some (mkAppN P (s.getAppArgs.extract 7 s.getAppNumArgs))   -- genGP ι dom lvl initsOf hs genData₀ env, then the applied name
    else none

def compareRoots (old new : Name) : MetaM Diff := do
  let oi ← getConstInfo old
  let ni ← getConstInfo new
  tele oi.type #[] fun xo co => tele ni.type #[] fun xn cn => do
    let nameN ← xn.mapM baseName
    let find (nm : Name) : Option Expr := (List.range xn.size).findSome? fun j => if nameN[j]! == nm then some xn[j]! else none
    let need (nm : Name) : MetaM Expr := do
      let some x := find nm | throwError "{new}: no binder {nm}"
      return x
    -- P and declName of the new theorem, read off `hpkg : ∀ c, TgtRun P declName c → …`
    let mut Pnew : Option Expr := none
    let mut dnew : Option Expr := none
    if let some h := find `hpkg then
      let t := (← h.fvarId!.getDecl).type
      if t.isForall && t.bindingBody!.isForall then
        let a := t.bindingBody!.bindingDomain!.getAppArgs
        if t.bindingBody!.bindingDomain!.getAppFn.constName? == some ``Tools.ShippingGen5FG.TgtRun && a.size == 5 then
          Pnew := some a[2]!
          dnew := some a[3]!
    let mut consumed := Array.replicate xn.size false
    let mut olds : Array Expr := #[]
    let mut news : Array Expr := #[]
    let mut hRem := 0
    let mut reachRepl := false
    let mut otherRem : List Name := []
    let mut changed : List Name := []
    for x in xo do
      let d ← x.fvarId!.getDecl
      let nm := d.userName.eraseMacroScopes
      let ty := d.type.replaceFVars olds news
      let isH := usesT d.type
      let cand := (List.range xn.size).find? fun j => !consumed[j]! && nameN[j]! == nm
      let mut target : Option Nat := cand
      if isH then
        match cand with
        | some j => unless usesT (← xn[j]!.fvarId!.getDecl).type do target := none
        | none => pure ()
        if target.isNone then hRem := hRem + 1; continue
      match target with
      | some j =>
        consumed := consumed.set! j true
        let tn := (← xn[j]!.fvarId!.getDecl).type
        unless ty == tn do changed := changed ++ [nm]
        olds := olds.push x; news := news.push xn[j]!
      | none =>
        if nm == `Reach then
          let (some P, some dn) := (Pnew, dnew) | throwError "{new}: Reach is replaced but no hpkg row to read P / declName from"
          reachRepl := true
          olds := olds.push x; news := news.push (← mkAppM ``Tools.ShippingGen5FG.TgtRun #[P, dn])
        else otherRem := otherRem ++ [nm]
    let conclEq := co.replaceFVars olds news == cn
    -- existing rows
    let mut added : List Name := []
    let mut addedBad : List Name := []
    let mapNew (nm : Name) : MetaM Expr := need nm
    for j in [:xn.size] do
      unless consumed[j]! do
        let nm := nameN[j]!
        added := added ++ [nm]
        let tn := (← xn[j]!.fvarId!.getDecl).type
        let some P := Pnew | continue
        let some dn := dnew | continue
        let reach ← mkAppM ``Tools.ShippingGen5FG.TgtRun #[P, dn]
        let fieldRef (fld : Name) : MetaM Expr := do
          forallBoundedTelescope (← getConstInfo fld).type (some 9) fun ys body => do
            let names := [`ι, `dom, `mref, `cref, `L, `P, `Reach, `DataOk]
            let mut tos : Array Expr := #[]
            for i in [:8] do
              unless (← baseName ys[i]!) == names[i]! do throwError "{fld}: parameter {i} is not {names[i]!}"
              let t ← (if names[i]! == `P then pure P else if names[i]! == `Reach then pure reach else mapNew names[i]!)
              tos := tos.push t
            return body.replaceFVars (ys.extract 0 8) tos
        if nm == `hpkg then unless tn == (← fieldRef ``Tools.ShippingGen2.T1HypND.pkg) do addedBad := addedBad ++ [nm]
        else if nm == `hcl then unless tn == (← fieldRef ``Tools.ShippingGen2.T1HypND.closes) do addedBad := addedBad ++ [nm]
        else if nm == `hA6 then
          let some fg := (← getEnv).find? ``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtG | throwError "no FGLedgerPremisesStmtG"
          let some fgv := fg.value? | throwError "no value"
          let ref ← forallTelescope fgv fun fxs fbody => do
            let args := fbody.getAppArgs
            unless fbody.isAppOf ``And && args.size == 2 do throwError "FGLedgerPremisesStmtG: unexpected shape"
            forallTelescope args[1]! fun yxs _ => do
              let h := (← yxs[9]!.fvarId!.getDecl).type
              let h := replaceGenGP h P
              let mut fr : Array Expr := #[]
              let mut tos : Array Expr := #[]
              for x in fxs ++ yxs do
                let n ← baseName x
                if n ∈ [`ι, `dom, `mref, `cref, `L] then fr := fr.push x; tos := tos.push (← mapNew n)
                if n == `declName then fr := fr.push x; tos := tos.push dn
              return h.replaceFVars fr tos
          unless tn == ref do addedBad := addedBad ++ [nm]
    return { hRemoved := hRem, reachRepl, otherRemoved := otherRem, added, changed, concl := conclEq, addedBad }

def allowedAdded : List Name := [`declName, `hpkg, `hA6, `hcl]

/-- The verdict of a root: exactly one `T1HypND` binder removed (only if `allowH`), `Reach` replaced, nothing else removed or changed. -/
def okRoot (d : Diff) (allowH : Bool) : Bool :=
  (if allowH then d.hRemoved == 1 else d.hRemoved == 0) && d.otherRemoved.isEmpty && d.changed.isEmpty && d.concl &&
  d.addedBad.isEmpty && d.added.all allowedAdded.contains && [`hpkg, `hA6, `hcl].all (d.added.contains ·)

def isEmptyDiff (d : Diff) : Bool :=
  d.hRemoved == 0 && !d.reachRepl && d.otherRemoved.isEmpty && d.added.isEmpty && d.changed.isEmpty && d.concl && d.addedBad.isEmpty

def pairs : List (Name × Name) :=
  [(``Tools.ShippingGen2.servedShips0_runND, ``Tools.ShippingGen5CR4.servedShips0_runND_rows),
   (``Tools.ShippingGen2.postFacts_of_runND, ``Tools.ShippingGen5CR4.postFacts_of_runND_rows),
   (``Tools.ShippingGen2.t1_of_stepPF_ND, ``Tools.ShippingGen5CR4.t1_of_stepPF_ND_rows),
   (``Tools.ShippingGen2.closingRun0_of_runT1_ND, ``Tools.ShippingGen5CR4.closingRun0_of_runT1_ND_rows),
   (``Tools.ShippingGen2.closingRun_of_runT1_ND, ``Tools.ShippingGen5CR4.closingRun_of_runT1_ND_rows),
   (``Tools.ShippingGen5SM7.hT2Tie_of_genGP, ``Tools.ShippingGen5CR4.hT2Tie_of_genGP_rows),
   (``Tools.ShippingGen5AuditE3B3.auditE3B3_of_t1hypND_run, ``Tools.ShippingGen5CR4.auditE3B3_of_t1hypND_run_rows)]

run_meta do
  let mut n : Nat := 0
  for (o, nw) in pairs do
    let d ← compareRoots o nw
    unless okRoot d true do throwError "{o} vs {nw}: unexpected diff {repr d}"
    -- NEGATIVE CONTROL 1: self-comparison is empty
    let s ← compareRoots o o
    unless isEmptyDiff s do throwError "CONTROL: {o} against itself is not empty: {repr s}"
    -- NEGATIVE CONTROL 2: not counting `H` as removed makes the root fail
    if okRoot d false then throwError "CONTROL: {o}: the comparison passes without counting H as removed"
    -- the new type and value do not use T1HypND; the value goes through t1HypND_of_rows
    let ci ← getConstInfo nw
    if usesT ci.type then throwError "{nw}: its type uses T1HypND"
    let some v := ci.value? (allowOpaque := true) | throwError "{nw}: no value"
    let cs := v.getUsedConstants
    if cs.contains ``Tools.ShippingGen2.T1HypND then throwError "{nw}: its value uses T1HypND"
    unless cs.contains ``Tools.ShippingGen5CR4.t1HypND_of_rows do throwError "{nw}: its value does not use t1HypND_of_rows"
    n := n + 1
  -- NEGATIVE CONTROL 3: a mismatched pair fails
  let bad ← compareRoots ``Tools.ShippingGen2.servedShips0_runND ``Tools.ShippingGen5CR4.postFacts_of_runND_rows
  if okRoot bad true then throwError "CONTROL: a mismatched pair passes"
  -- the one place T1HypND is built: control that the detection sees it, and that `closed` is `TgtRun.call`
  let ci ← getConstInfo ``Tools.ShippingGen5CR4.t1HypND_of_rows
  unless usesT ci.type do throwError "CONTROL: T1HypND not seen in t1HypND_of_rows"
  unless (ci.value? (allowOpaque := true)).any (·.getUsedConstants.contains ``Tools.ShippingGen5FG.TgtRun.call) do
    throwError "t1HypND_of_rows does not use TgtRun.call for `closed`"
  logInfo m!"CR4 CHECK: {n} roots: removed [H] (Reach := TgtRun P declName), added ⊆ [declName, hpkg, hA6, hcl] with rows == existing rows, changed [], conclusion ==; T1HypND absent from new types and values (t1HypND_of_rows only); controls: self-compare empty, H-not-removed fails, mismatched pair fails"

end Tests.Gen5.CR4Check
