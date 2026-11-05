import Lean
import Tools.ShippingGen5DG1
import Tools.ShippingGen5CR4
import Tools.ShippingGen5SM7
set_option autoImplicit false
-- C.DG-1 check (Issue sparkle-ledger-dg1). No sorry / axiom / native_decide.

/-! # C.DG-1: is the `GeneratedAt` requirement still a premise of the final roots?

Part 1 (roots, listed explicitly): for each final root the STATEMENT (the value of a `def … : Prop`, otherwise the type) and
every definition reachable from it inside `Tools.` / `Sparkle.` (not through `genGP` / `genKit`) is scanned for the GeneratedAt
vocabulary `GeneratedAtK`, `GenSFacts`, `GenPGeneratedStmt`, `GenPPkgStmt`, `ReachCover`, `ReachEdge`. A root is classified `fixed`
(the table is `genGP …`, no binder `GP`/`P` of type `Pkgs`) or `generic`; the classification must equal the declared one.
Part 2 (glue, `Tools/ShippingGen5DG1.lean`): the conclusion of `hpkg_tgtRun_of_cover` is structurally `==` the `T1HypND.pkg` field at
`P := genGP`, `Reach := TgtRun genGP declName`; the conclusion of `pkgAssign_of_cover` is `==` the `hDG_PKGASSIGN` binder of
`stepDec_of_ties` at `P := genGP`; each has a `ReachCover` binder (C.AC-4 stays a premise); `genGP_fields` states the `GenData`
fields `wf` / `hshape` / `hdata` as `==` the field types of `GenData`.
NEGATIVE controls: a generic `P` (R's `GP`, a fresh local in place of `genGP`) is rejected; the glue type without its `hcov` binder
is rejected; the pkg row against the `closes` field is rejected; the scanner sees `GeneratedAtK` in `genP_generated`'s statement. -/
open Lean Meta

namespace Tests.Gen5.DG1Check

def vocab : List Name :=
  [``Tools.ShippingGen5Acc.GeneratedAtK, ``Tools.ShippingGen5Acc.GenSFacts, ``Tools.ShippingGen5Acc.GenPGeneratedStmt,
   ``Tools.ShippingGen5Acc.GenPPkgStmt, ``Tools.ShippingGen5Acc.ReachCover, ``Tools.ShippingGen5Acc.ReachEdge]

def stops : List Name := [``Tools.ShippingGenFGLedgerPremises.genGP, ``Tools.ShippingGenFGLedgerPremises.genKit]

def statement (n : Name) : MetaM Expr := do
  let ci ← getConstInfo n
  match ci with
  | .defnInfo d => if d.type.isProp || d.type == mkSort levelZero then return d.value else return ci.type
  | _ => return ci.type

/-- The vocabulary constants reachable from `e` through definitions in `Tools.` / `Sparkle.` (stopping at `genGP`, `genKit`). -/
partial def reach (e : Expr) : MetaM (List Name) := do
  let mut seen : NameSet := {}
  let mut todo : List Name := e.getUsedConstants.toList
  let mut found : List Name := []
  let env ← getEnv
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n || stops.contains n then continue
    seen := seen.insert n
    if vocab.contains n then found := found ++ [n]
    let root := n.getRoot
    unless root == `Tools || root == `Sparkle do continue
    let some ci := env.find? n | continue
    match ci with
    | .defnInfo d => todo := todo ++ d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList
    | .inductInfo i => todo := todo ++ i.type.getUsedConstants.toList ++ i.ctors
    | .ctorInfo c => todo := todo ++ c.type.getUsedConstants.toList
    | .recInfo _ => pure ()
    | _ => todo := todo ++ ci.type.getUsedConstants.toList   -- theorems / opaque: the type only
  return found.eraseDups

def baseName (x : Expr) : MetaM Name := return (← x.fvarId!.getDecl).userName.eraseMacroScopes

/-- fixed = the statement uses `genGP` and has no binder of type `Pkgs …`/`… → Pkgs …`; generic = such a binder. -/
def pkgsBinder (t : Expr) : Bool := t.getUsedConstants.contains ``Tools.ShippingGen2.Pkgs

partial def binderTypes (e : Expr) : MetaM (List Expr) := do
  forallTelescope e fun xs body => do
    let mut r : List Expr := []
    for x in xs do r := r ++ [(← x.fvarId!.getDecl).type]
    -- one level into an implication chain's conclusion (a conjunction of statements)
    return r ++ (if body.isAppOf ``And then body.getAppArgs.toList else [])

inductive Kind | fixed | generic deriving BEq, Repr

def classify (stmt : Expr) : MetaM Kind := do
  let bs ← binderTypes stmt
  let usesGP := stmt.getUsedConstants.contains ``Tools.ShippingGenFGLedgerPremises.genGP
  -- a binder whose TYPE is exactly `Pkgs ι dom` or `Environment → Pkgs ι dom`
  let isPkgs (t : Expr) : Bool :=
    let t := if t.isForall then t.bindingBody! else t
    t.getAppFn.constName? == some ``Tools.ShippingGen2.Pkgs
  if usesGP && !bs.any isPkgs then return .fixed else return .generic

structure Root where
  name : Name
  kind : Kind

def roots : List Root :=
  [⟨``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtR, .generic⟩,
   ⟨``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtG, .fixed⟩,
   ⟨``Tools.ShippingGenFGLedgerPremises.hDT1_of_genGP, .fixed⟩,
   ⟨``Tools.ShippingGen2.servedShips0_runND, .generic⟩,
   ⟨``Tools.ShippingGen2.postFacts_of_runND, .generic⟩,
   ⟨``Tools.ShippingGen2.t1_of_stepPF_ND, .fixed⟩,
   ⟨``Tools.ShippingGen2.closingRun0_of_runT1_ND, .fixed⟩,
   ⟨``Tools.ShippingGen2.closingRun_of_runT1_ND, .fixed⟩,
   ⟨``Tools.ShippingGen5AuditE3B3.auditE3B3_of_t1hypND_run, .generic⟩,
   ⟨``Tools.ShippingGen5SM7.hT2Tie_of_genGP, .fixed⟩,
   ⟨``Tools.ShippingGen5CR4.servedShips0_runND_rows, .generic⟩,
   ⟨``Tools.ShippingGen5CR4.postFacts_of_runND_rows, .generic⟩,
   ⟨``Tools.ShippingGen5CR4.t1_of_stepPF_ND_rows, .fixed⟩,
   ⟨``Tools.ShippingGen5CR4.closingRun0_of_runT1_ND_rows, .fixed⟩,
   ⟨``Tools.ShippingGen5CR4.closingRun_of_runT1_ND_rows, .fixed⟩,
   ⟨``Tools.ShippingGen5CR4.hT2Tie_of_genGP_rows, .fixed⟩,
   ⟨``Tools.ShippingGen5CR4.auditE3B3_of_t1hypND_run_rows, .generic⟩,
   ⟨``Tools.ShippingGen2.stepDec_of_ties, .generic⟩]

def firstIdx (xs : Array Expr) (nm : Name) : MetaM (Option Expr) := do
  for x in xs do
    if (← baseName x) == nm then return some x
  return none

def has (ts : List Name) (e : Expr) : Bool := ts.any e.getUsedConstants.contains

def binderHeads (e : Expr) : MetaM (List Name) :=
  forallTelescope e fun xs _ => do
    let mut r := []
    for x in xs do
      let t ← instantiateMVars (← x.fvarId!.getDecl).type
      let h ← forallTelescope t fun _ b => pure (b.getAppFn.constName?.getD Name.anonymous)
      r := r ++ [h]
    return r

/-- Number of leading binders before the first one named `stop` (the conclusion's own `∀`). -/
def headCount (t : Expr) (stop : Name) : Nat :=
  match t with
  | .forallE n _ b _ => if n == stop then 0 else 1 + headCount b stop
  | _ => 0

def hasCover (e : Expr) : MetaM Bool := return (← binderHeads e).contains ``Tools.ShippingGen5Acc.ReachCover

run_meta do
  let mut nFixed := 0
  let mut nGeneric := 0
  -- Part 1: roots
  for r in roots do
    let st ← statement r.name
    -- fgLedgerPremisesStmtG_of_R is handled below (an implication between two statements)
    let k ← classify st
    unless k == r.kind do throwError "{r.name}: classified {repr k}, declared {repr r.kind}"
    let v ← reach st
    unless v.isEmpty do throwError "{r.name}: the GeneratedAt vocabulary {v} occurs in its statement"
    if k == .fixed then nFixed := nFixed + 1 else nGeneric := nGeneric + 1
  -- fgLedgerPremisesStmtG_of_R : R → G : the premise is generic, the conclusion fixed
  let impl ← statement ``Tools.ShippingGenFGLedgerPremises.fgLedgerPremisesStmtG_of_R
  let .forallE _ a b _ := impl | throwError "fgLedgerPremisesStmtG_of_R: not an implication"
  unless a.isConstOf ``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtR && b.isConstOf ``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtG do
    throwError "fgLedgerPremisesStmtG_of_R is not R → G"
  -- NEGATIVE 1: a generic `P` is not `fixed` (R, the generic ND roots)
  for n in [``Tools.ShippingGenFGLedgerPremises.FGLedgerPremisesStmtR, ``Tools.ShippingGen5CR4.servedShips0_runND_rows] do
    if (← classify (← statement n)) == .fixed then throwError "NEG1: the generic root {n} is classified fixed"
  -- NEGATIVE 2: the scanner sees the vocabulary where it is (genP_generated states `GeneratedAtK`; genP_pkg states `ReachCover`)
  unless (← reach (← statement ``Tools.ShippingGen5Acc.genP_generated)).contains ``Tools.ShippingGen5Acc.GeneratedAtK do
    throwError "NEG2: the scan does not see GeneratedAtK in GenPGeneratedStmt"
  unless (← reach (← statement ``Tools.ShippingGen5Acc.genP_pkg)).contains ``Tools.ShippingGen5Acc.ReachCover do
    throwError "NEG2: the scan does not see ReachCover in GenPPkgStmt"
  -- Part 2: the glue
  -- (a) hpkg_tgtRun_of_cover
  let gl ← getConstInfo ``Tools.ShippingGen5DG1.hpkg_tgtRun_of_cover
  let pkgFld ← getConstInfo ``Tools.ShippingGen2.T1HypND.pkg
  let (okPkg, okPkgGeneric, coverLess, coverBinder, closesMismatch) ← forallBoundedTelescope gl.type (some (headCount gl.type `c)) fun xs concl => do
    let some ι := ← firstIdx xs `ι | throwError "no ι"
    let some dom := ← firstIdx xs `dom | throwError "no dom"
    let some declName := ← firstIdx xs `declName | throwError "no declName"
    let some dataOk := ← firstIdx xs `DataOk | throwError "no DataOk"
    -- P read off the `TgtRun` of the conclusion
    let .forallE _ _ cb _ := concl | throwError "conclusion shape"
    let .forallE _ tr _ _ := cb | throwError "conclusion shape (TgtRun)"
    unless tr.getAppFn.constName? == some ``Tools.ShippingGen5FG.TgtRun && tr.getAppNumArgs == 5 do throwError "no TgtRun in the conclusion"
    let Pterm := tr.getAppArgs[2]!
    unless Pterm.getAppFn.constName? == some ``Tools.ShippingGenFGLedgerPremises.genGP do throwError "P is not genGP: {Pterm}"
    let ref (fld : Name) (Pt : Expr) : MetaM Expr := do
      let fi ← getConstInfo fld
      forallBoundedTelescope fi.type (some 9) fun ys body => do
        let names := [`ι, `dom, `mref, `cref, `L, `P, `Reach, `DataOk]
        for i in [:8] do
          unless (← baseName ys[i]!) == names[i]! do throwError "{fld}: parameter {i} is not {names[i]!}"
        let reach ← mkAppM ``Tools.ShippingGen5FG.TgtRun #[Pt, declName]
        return body.replaceFVars #[ys[0]!, ys[1]!, ys[5]!, ys[6]!, ys[7]!] #[ι, dom, Pt, reach, dataOk]
    let ok := concl == (← ref ``Tools.ShippingGen2.T1HypND.pkg Pterm)
    -- NEG: a generic P (a fresh local in place of genGP)
    let gen ← withLocalDeclD `GP (← mkAppM ``Tools.ShippingGen2.Pkgs #[ι, dom]) fun gp => do
      return concl == (← ref ``Tools.ShippingGen2.T1HypND.pkg gp)
    let closesBad := concl == (← ref ``Tools.ShippingGen2.T1HypND.closes Pterm) |> fun b => b
    -- NEG: the glue type without its hcov binder
    let some hcov := ← firstIdx xs `hcov | throwError "no hcov"
    let xs' := xs.filter (· != hcov)
    let noCov ← mkForallFVars xs' concl
    return (ok, gen, ← hasCover noCov, ← hasCover gl.type, closesBad)
  unless okPkg do throwError "hpkg_tgtRun_of_cover: conclusion is not the T1HypND.pkg row at P := genGP, Reach := TgtRun genGP declName"
  if okPkgGeneric then throwError "NEG3: the pkg row matched with a generic P"
  if coverLess then throwError "NEG4: the glue type without hcov still has a ReachCover binder"
  unless coverBinder do throwError "hpkg_tgtRun_of_cover has no ReachCover binder (C.AC-4 must stay)"
  if closesMismatch then throwError "NEG5: the pkg conclusion matched the `closes` field"
  -- (b) pkgAssign_of_cover against stepDec_of_ties's hDG_PKGASSIGN at P := genGP
  let pa ← getConstInfo ``Tools.ShippingGen5DG1.pkgAssign_of_cover
  let sd ← getConstInfo ``Tools.ShippingGen2.stepDec_of_ties
  let (okPA, paGeneric, paCover) ← forallBoundedTelescope pa.type (some (headCount pa.type `k)) fun xs concl => do
    let some ι := ← firstIdx xs `ι | throwError "no ι"
    let some dom := ← firstIdx xs `dom | throwError "no dom"
    let some p := ← firstIdx xs `p | throwError "no p"
    -- genGP term read off the `∃ q, genGP … = some q` of the conclusion
    let Pt ← forallTelescope concl fun _ b => do
      let .app _ lam := b | throwError "PA: ∃ shape"
      let .lam _ _ eq _ := lam | throwError "PA: ∃ lambda"
      -- eq : GPP name = some q ; the function applied
      pure eq.getAppArgs[1]!.appFn!
    let Pfull := Pt
    unless Pfull.getAppFn.constName? == some ``Tools.ShippingGenFGLedgerPremises.genGP do throwError "PA: P is not genGP: {Pfull}"
    let ref (Pt : Expr) : MetaM Expr := forallTelescope sd.type fun ys _ => do
      let some sι := ← firstIdx ys `ι | throwError "sd: no ι"
      let some sdom := ← firstIdx ys `dom | throwError "sd: no dom"
      let some sP := ← firstIdx ys `P | throwError "sd: no P"
      let some sp := ← firstIdx ys `p | throwError "sd: no p"
      let some h := ← firstIdx ys `hDG_PKGASSIGN | throwError "sd: no hDG_PKGASSIGN"
      return (← h.fvarId!.getDecl).type.replaceFVars #[sι, sdom, sP, sp] #[ι, dom, Pt, p]
    let ok := concl == (← ref Pfull)
    let gen ← withLocalDeclD `GP (← mkAppM ``Tools.ShippingGen2.Pkgs #[ι, dom]) fun gp => do
      return concl == (← ref gp)
    return (ok, gen, ← hasCover pa.type)
  unless okPA do throwError "pkgAssign_of_cover: conclusion is not stepDec_of_ties's hDG_PKGASSIGN at P := genGP"
  if paGeneric then throwError "NEG3': pkgAssign matched with a generic P"
  unless paCover do throwError "pkgAssign_of_cover has no ReachCover binder"
  -- (c) genGP_fields: the GenData fields wf / hshape / hdata are the field types of `GenData`
  let gf ← getConstInfo ``Tools.ShippingGen5DG1.genGP_fields
  let fieldsOk ← forallTelescope gf.type fun _ concl => do
    -- ∃ E g, entry = some E ∧ genData₀ env E = some g ∧ wf ∧ shape ∧ data ∧ Acc ∧ GeneratedAtK
    let .app _ lamE := concl | throwError "GF: ∃ E"
    let .lam _ eTy bodyE _ := lamE | throwError "GF: lam E"
    withLocalDeclD `E eTy fun E => do
      let bodyE := bodyE.instantiate1 E
      let .app _ lamG := bodyE | throwError "GF: ∃ g"
      let .lam _ gTy bodyG _ := lamG | throwError "GF: lam g"
      withLocalDeclD `g gTy fun g => do
        let b := bodyG.instantiate1 g
        let conj := (List.range 6).foldl (fun (acc : Expr × List Expr) _ =>
          match acc.1.and? with
          | some (l, r) => (r, acc.2 ++ [l])
          | none => acc) (b, [])
        let parts := conj.2
        unless parts.length == 6 do throwError "GF: expected 6 leading conjuncts, got {parts.length}"
        let wfT ← inferType (← mkAppM ``Tools.ShippingGen5Sem.GenData.wf #[g])
        let shT ← inferType (← mkAppM ``Tools.ShippingGen5Sem.GenData.hshape #[g])
        let daT ← inferType (← mkAppM ``Tools.ShippingGen5Sem.GenData.hdata #[g])
        return parts[2]! == wfT && parts[3]! == shT && parts[4]! == daT && (has [``Tools.ShippingGen5Acc.entry₀] parts[0]!)
  unless fieldsOk do throwError "genGP_fields: wf / hshape / hdata are not the GenData field types"
  -- axioms of the glue
  for n in [``Tools.ShippingGen5DG1.genGP_fields, ``Tools.ShippingGen5DG1.hpkg_tgtRun_of_cover, ``Tools.ShippingGen5DG1.pkgAssign_of_cover] do
    let ax ← collectAxioms n
    for a in ax do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do throwError "{n}: axiom {a}"
  logInfo m!"DG1 CHECK: {roots.length + 1} roots ({nFixed} with P = genGP, {nGeneric} generic-P) have no GeneratedAt/coverage vocabulary (GeneratedAtK, GenSFacts, GenPGeneratedStmt, GenPPkgStmt, ReachCover, ReachEdge) in their statements; glue: hpkg_tgtRun_of_cover == T1HypND.pkg at genGP and pkgAssign_of_cover == stepDec_of_ties hDG_PKGASSIGN at genGP, both keep a ReachCover binder (C.AC-4 remains); genGP_fields wf/hshape/hdata == GenData field types; controls: generic P rejected, hcov-less form rejected, pkg vs closes rejected, scanner sees GeneratedAtK / ReachCover; axioms standard"

end Tests.Gen5.DG1Check
