import Lean
import Tools.ShippingGen5SM1
set_option autoImplicit false
-- C.SM-1 check (Issue sparkle-ledger-sm1). No sorry / axiom / native_decide.

/-! Structural `Expr` comparison of `FGLedgerPremisesStmtG` with `FGLedgerPremisesStmtH` (Tools/ShippingGen5SM1.lean), one walk of the
two telescopes. Old binders are instantiated by the same-named new fvar, except `initsOf := Tools.ShippingGen5DataOfPure.initsOf` and
`hs := dataOfSound_initsOf lvl` (the concrete `initsOf`, `dataOfAt_sound`). Required: removed = [initsOf, hs] exactly; added = [];
changed = []; the whole remainder (the outer binders, then the conjunction with its inner hypotheses and conclusion) `==`; every
`genGP` in the new statement has `initsOf` = the constant and `hs` = `dataOfSound_initsOf lvl` (so the conclusion is `genGP` with a
concrete proof). Negative controls: (1) not specializing (`initsOf`, `hs` left arbitrary) fails; (2) a wrong `initsOf` fails; (3) G
against itself is empty; (4) H is not G (the binders differ).

Why the specialization is meaningful (DataOfPure.lean:354): the concrete function is
`def initsOf (d : MachineData) : HList (tys d.ss) := initsFrom d.shape.layout.slots d.ss`, with
`initsFrom slots (s :: ss) = (decInit s ((slots.head?.map (·.init)).getD 0), initsFrom slots.tail ss)`: the register reset values read
off the layout `slots` of `d`, the data the generator `dataOfCore`/`dataOfAt` produces. The statement `DataOfSound dataOf initsOf`
asks `d.initOk (initsOf d) = true` for every `d` that `dataOf` returns, and `dataOfAt_sound` (DataOf.lean:211) proves it for
exactly this `initsOf` (and `initOk_of_ok`: `d.ok = true → d.initOk (initsOf d) = true`). Checked below: the type of `dataOfAt_sound`
mentions that constant, `initsOf` unfolds to `initsFrom … layout.slots`, and `dataOfSound_initsOf` is proved by `dataOfAt_sound`. -/
open Lean Meta

namespace Tests.Gen5.SM1Check

structure Diff where
  removed : List Name
  added : List Name
  changed : List Name
  concl : Bool
deriving Repr

def baseName (x : Expr) : MetaM Name := return (← x.fvarId!.getDecl).userName.eraseMacroScopes

def initsC : Expr := mkConst ``Tools.ShippingGen5DataOfPure.initsOf

def valOf (n : Name) : MetaM Expr := do
  let some v := (← getConstInfo n).value? (allowOpaque := true) | throwError "{n}: no value"
  return v

/-- `spec`: instantiate old `initsOf` by `initsT` and old `hs` by `dataOfSound_initsOf lvl`; otherwise leave them. -/
def compareStmts (old new : Name) (spec : Bool) (initsT : Expr := initsC) : MetaM Diff := do
  let ov ← valOf old
  let nv ← valOf new
  forallTelescope ov fun xo co => forallTelescope nv fun xn cn => do
    let nameN ← xn.mapM baseName
    let mut consumed := Array.replicate xn.size false
    let mut olds : Array Expr := #[]
    let mut news : Array Expr := #[]
    let mut removed : List Name := []
    let mut changed : List Name := []
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
        if spec then
          if nm == `initsOf then olds := olds.push x; news := news.push initsT
          else if nm == `hs then
            let some l := (List.range xn.size).findSome? fun j => if nameN[j]! == `lvl then some xn[j]! else none
              | throwError "no lvl"
            olds := olds.push x; news := news.push (mkApp (mkConst ``Tools.ShippingGen5SM1.dataOfSound_initsOf) l)
    let added := (List.range xn.size).filter (!consumed[·]!) |>.map (nameN[·]!)
    return { removed, added, changed, concl := co.replaceFVars olds news == cn }

def okSM1 (d : Diff) : Bool :=
  d.removed == [`initsOf, `hs] && d.added.isEmpty && d.changed.isEmpty && d.concl

def isEmptyDiff (d : Diff) : Bool := d.removed.isEmpty && d.added.isEmpty && d.changed.isEmpty && d.concl

/-- All `genGP` applications of an expression. -/
partial def collectGP (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.getAppFn.constName? == some `Tools.ShippingGenFGLedgerPremises.genGP then
    e.getAppArgs.foldl (fun acc a => collectGP a acc) (acc.push e)
  else
  match e with
  | .app f a => collectGP a (collectGP f acc)
  | .lam _ d b _ | .forallE _ d b _ => collectGP b (collectGP d acc)
  | .letE _ t v b _ => collectGP b (collectGP v (collectGP t acc))
  | .mdata _ b | .proj _ _ b => collectGP b acc
  | _ => acc

run_meta do
  let G := ``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtG
  let H := ``Tools.ShippingGen5SM1.FGLedgerPremisesStmtH
  let d ← compareStmts G H true
  unless okSM1 d do throwError "G vs H: unexpected diff {repr d}"
  -- every genGP of H: initsOf = the constant, hs = dataOfSound_initsOf lvl
  let hv ← valOf H
  let gps := collectGP hv #[]
  if gps.isEmpty then throwError "H has no genGP"
  for g in gps do
    let a := g.getAppArgs
    unless a.size ≥ 6 do throwError "genGP with {a.size} args"
    unless a[3]! == initsC do throwError "genGP: initsOf is not the constant: {a[3]!}"
    unless a[4]! == mkApp (mkConst ``Tools.ShippingGen5SM1.dataOfSound_initsOf) a[2]! do throwError "genGP: hs is not dataOfSound_initsOf lvl"
  -- G itself has the arbitrary initsOf / hs in each genGP (not constants)
  let gps0 := collectGP (← valOf G) #[]
  if gps0.any (fun g => g.getAppArgs[3]! == initsC) then throwError "CONTROL: G already uses the constant initsOf"
  -- NEGATIVE CONTROL 1: no specialization (arbitrary initsOf / hs kept) fails
  if okSM1 (← compareStmts G H false) then throwError "CONTROL: comparison passes without specializing initsOf / hs"
  -- NEGATIVE CONTROL 2: a wrong initsOf fails
  let wrong := mkConst ``Tools.ShippingGen5DataOfPure.initsFrom
  if okSM1 (← compareStmts G H true wrong) then throwError "CONTROL: a wrong initsOf passes"
  -- NEGATIVE CONTROL 3: G against itself is empty; G against H differs when nothing is removed
  unless isEmptyDiff (← compareStmts G G false) do throwError "CONTROL: G against itself is not empty"
  let hg ← compareStmts H G false
  if okSM1 hg || hg.removed != [] then throwError "CONTROL: H against G should add, not remove: {repr hg}"
  -- the specialization is meaningful: the concrete initsOf is the layout reset-value function used by dataOfAt_sound
  let sty := (← getConstInfo ``Tools.ShippingGen5DataOf.dataOfAt_sound).type
  unless sty.getUsedConstants.contains ``Tools.ShippingGen5DataOfPure.initsOf do throwError "dataOfAt_sound does not mention initsOf"
  let iv ← valOf ``Tools.ShippingGen5DataOfPure.initsOf
  unless iv.getUsedConstants.contains ``Tools.ShippingGen5DataOfPure.initsFrom do throwError "initsOf does not unfold to initsFrom"
  let pv ← valOf ``Tools.ShippingGen5SM1.dataOfSound_initsOf
  unless pv.getUsedConstants.contains ``Tools.ShippingGen5DataOf.dataOfAt_sound do throwError "dataOfSound_initsOf does not use dataOfAt_sound"
  let hty := (← getConstInfo ``Tools.ShippingGen5SM1.fgLedgerPremisesStmtH_of_G).type
  unless hty.getUsedConstants.contains G && hty.getUsedConstants.contains H do throwError "H_of_G has the wrong type"
  logInfo m!"SM1 CHECK: 1 statement pair (FGLedgerPremisesStmtG vs FGLedgerPremisesStmtH): removed {repr d.removed} (initsOf := DataOfPure.initsOf, hs := dataOfSound_initsOf lvl), added {repr d.added}, changed {repr d.changed}, conclusion and inner hypotheses == ; {gps.size} genGP occurrences in H all concrete; controls: no-specialization fails, wrong initsOf fails, G-vs-G empty, H-vs-G not a removal; initsOf = initsFrom layout.slots mentioned by dataOfAt_sound"

end Tests.Gen5.SM1Check
