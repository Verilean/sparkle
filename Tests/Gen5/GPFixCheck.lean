import Lean
import Tools.ShippingGenFGLedgerPremisesG
set_option autoImplicit false
-- GPFIX check (scripts/gen5/GPFIX_FREEZE.md §3): structural Expr comparison of FGLedgerPremisesStmtR and FGLedgerPremisesStmtG.

/-! # GPFIX: `GP` fixed to `genGP`, `h_D_T1` removed

OUTER: the telescope of `FGLedgerPremisesStmtG` is opened once; each binder of `FGLedgerPremisesStmtR` is instantiated with the `G`
free variable of the same name, except `GP`, which is instantiated with the TERM `genGP lvl hs genData₀` built from the `G` free
variables (so the comparison is "R at GP := genGP"). Types are compared with `Expr` `==` (structural, alpha-equivalence).
INNER: after the outer substitution both bodies are `ConstValueFunctional CV ∧ ∀ declName …`. The first conjuncts must be `==`; the
second conjuncts are walked positionally, skipping exactly one premise of `R` (the `h_D_T1` position), and the remaining premises and
the conclusions must be `==`. NEGATIVE controls: no skip, a wrong skip, and an unsubstituted `GP` must fail. -/
open Lean Meta

namespace Tests.Gen5.GPFixCheck

/-- Positional walk: `old` and `new` foralls together, skipping old premise number `skip` (or none). -/
partial def walkPos (old new : Expr) (skip : Option Nat) (i : Nat := 0) : MetaM Bool := do
  match old, new with
  | .forallE n d b bi, _ =>
    if skip == some i then
      withLocalDecl n bi d fun x => walkPos (b.instantiate1 x) new skip (i + 1)
    else
      match new with
      | .forallE _ d' b' bi' =>
        if !(d == d' && bi == bi') then return false
        withLocalDecl n bi d fun x => walkPos (b.instantiate1 x) (b'.instantiate1 x) skip (i + 1)
      | _ => return false
  | _, .forallE .. => return false
  | _, _ => return old == new

/-- Opens G's telescope; walks R's, substituting `GP := gpTerm xs` (or a fresh local when `subst = false`). -/
abbrev Res := List Name × List Name × List Name × Bool × Bool

partial def walkR (gFvars : Array (Name × BinderInfo × Expr × Expr)) (gpTerm : Expr) (subst : Bool) :
    Expr → List Name → List Name → (Expr → List Name → List Name → MetaM Res) → MetaM Res
  | .forallE n d b bi, rm, ch, k =>
    if n == `GP then
      if subst then walkR gFvars gpTerm subst (b.instantiate1 gpTerm) (rm ++ [n]) ch k
      else withLocalDecl n bi d fun x => walkR gFvars gpTerm subst (b.instantiate1 x) (rm ++ [n]) ch k
    else match gFvars.find? (·.1 == n) with
      | some (_, bi', fv, ty') =>
        let ch := if bi == bi' && d == ty' then ch else ch ++ [n]
        walkR gFvars gpTerm subst (b.instantiate1 fv) rm ch k
      | none => withLocalDecl n bi d fun x => walkR gFvars gpTerm subst (b.instantiate1 x) (rm ++ [n]) ch k
  | body, rm, ch, k => k body rm ch

/-- Runs the comparison; returns (removed, added, changed, first conjunct ==, inner result for `skip`). -/
def compare (subst : Bool) (skip : Option Nat) : MetaM Res := do
  let r ← unfoldDefinition (mkConst ``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtR)
  let g ← unfoldDefinition (mkConst ``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtG)
  let rNames ← forallTelescope r fun xs _ => xs.toList.mapM fun x => return (← x.fvarId!.getDecl).userName
  forallTelescope g fun xs gbody => do
    let mut ys : Array (Name × BinderInfo × Expr × Expr) := #[]
    for x in xs do
      let dcl ← x.fvarId!.getDecl
      ys := ys.push (dcl.userName, dcl.binderInfo, x, dcl.type)
    let fv (n : Name) : MetaM Expr := match ys.find? (·.1 == n) with
      | some (_, _, e, _) => pure e
      | none => throwError "G lacks binder {n}"
    let gpTerm ← mkAppOptM ``Tools.ShippingGenFGLedgerPremises.genGP
      #[some (← fv `ι), some (← fv `dom), some (← fv `lvl), some (← fv `initsOf), some (← fv `hs), some (← fv `genData₀)]
    let ys' := ys
    walkR ys' gpTerm subst r [] [] fun rbody rm ch => do
      let added := (ys'.toList.filter fun y => !rNames.contains y.1).map (·.1)
      match rbody.and?, gbody.and? with
      | some (r1, r2), some (g1, g2) =>
        let inner ← walkPos r2 g2 skip
        return (rm, added, ch, r1 == g1, inner)
      | _, _ => throwError "bodies are not conjunctions"

run_meta do
  -- the h_D_T1 premise is number 10 of the inner telescope of R:
  -- declName parameters mctx cctx w w' b D (EntryWitness) (h_A_P06) (h_D_T1) (h_D_T4)
  let (rm, added, ch, first, inner) ← compare true (some 10)
  logInfo m!"GPFIX: removed {rm} added {added} changed {ch} firstConjunct== {first} inner(skip h_D_T1)== {inner}"
  unless rm == [`GP] && added == [`lvl, `initsOf, `hs, `genData₀] && ch == [] && first && inner do
    throwError "GPFIX comparison unexpected"
  -- NEGATIVE CONTROLS
  let (_, _, _, _, i0) ← compare true none
  if i0 then throwError "NEG1: inner comparison without skipping h_D_T1 passed"
  let (_, _, _, _, i1) ← compare true (some 11)
  if i1 then throwError "NEG2: skipping h_D_T4 instead of h_D_T1 passed"
  let (_, _, _, _, i2) ← compare true (some 9)
  if i2 then throwError "NEG3: skipping h_A_P06 instead of h_D_T1 passed"
  let (_, _, ch3, f3, i3) ← compare false (some 10)
  if ch3 == [] && f3 && i3 then throwError "NEG4: comparison with GP NOT substituted passed"
  logInfo m!"GPFIX NEG: noSkip {i0} skipT4 {i1} skipA6 {i2} unsubstituted {(ch3, f3, i3)} (all must be rejected)"

-- `hs` is C.SM-1's `DataOfSound (dataOfAt lvl) initsOf`
run_meta do
  let g ← unfoldDefinition (mkConst ``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtG)
  forallTelescope g fun xs _ => do
    let mut lvl? : Option Expr := none
    let mut ini? : Option Expr := none
    let mut hs? : Option Expr := none
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.userName == `lvl then lvl? := some x
      if d.userName == `initsOf then ini? := some x
      if d.userName == `hs then hs? := some d.type
    let some lvl := lvl? | throwError "no lvl"
    let some ini := ini? | throwError "no initsOf"
    let some hsTy := hs? | throwError "no hs"
    let expected ← mkAppM ``Tools.ShippingGen5Sem.DataOfSound
      #[← mkAppM ``Tools.ShippingGen5DataOf.dataOfAt #[lvl], ini]
    unless hsTy == expected do throwError "hs is not DataOfSound (dataOfAt lvl) initsOf: {hsTy}"
    logInfo m!"HS: {hsTy} == DataOfSound (dataOfAt lvl) initsOf"

#print axioms Tools.ShippingGenFGLedgerPremises.hDT1_of_genGP
#print axioms Tools.ShippingGenFGLedgerPremises.fgLedgerPremisesStmtG_of_R

end Tests.Gen5.GPFixCheck
