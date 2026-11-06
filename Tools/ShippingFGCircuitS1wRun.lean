import Tools.ShippingFGCircuitS1wGen
set_option autoImplicit false
-- FG circuit pilot S1w2: runs the generator on `hftRootValue` and emits the kernel-checked theorem `hftObCDW_of_tables`. docs/FG-CIRCUIT-PILOT.md §23.3 / §23.6.
-- Nothing here is trusted: the emitted declarations are checked by the kernel (`addDecl`). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.
namespace Tools.ShippingFGCircuitS1wRun
open Lean Meta Elab Command
open Lean (mkConst mkApp mkApp2 mkApp3 mkApp4 mkAppN)
open Sparkle.Core Tools.ShippingGen5ConstValueE Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1sCD
open Tools.ShippingFGCircuitS1wTbl Tools.ShippingFGCircuitS1wGen

/-- the lookup of a literal association list -/
def mkDelta (l : List (Name × DefRow)) : Name → Option DefRow := fun c => (l.find? (fun p => p.1 == c)).map (·.2)
def mkGamma (l : List (Name × CtorRow)) : Name → Option CtorRow := fun c => (l.find? (fun p => p.1 == c)).map (·.2)

def listE (α : Lean.Expr) : List Lean.Expr → Lean.Expr
  | [] => mkApp (Lean.mkConst ``List.nil [Level.zero]) α
  | x :: xs => mkApp3 (Lean.mkConst ``List.cons [Level.zero]) α x (listE α xs)

def pairE (α β a b : Lean.Expr) : Lean.Expr := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) α β a b

unsafe def runImpl (tag : String) (probe : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.find? ``Tools.ShippingFGCircuitS1kStmt.hftRootValue | throwError "hftRootValue"
  let some v := ci.value? | throwError "hftRootValue value"
  let root ← liftTermElabM (do let r ← unsafe evalExpr Lean.Expr (Lean.mkConst ``Lean.Expr) v; pure r)
  let t0 ← IO.monoMsNow
  let (res, st) ← liftTermElabM do
    let envT := Lean.mkConst ``Environment
    withLocalDeclD `env envT fun envV => do
    withLocalDeclD `lk (Lean.mkConst ``Look) fun lkV => do
    withLocalDeclD `hlk (mkApp2 (Lean.mkConst ``EnvLk) envV lkV) fun hlkV => do
      let K : Kx := { env := envV, hlk := hlkV, lk := lkV }
      let (p, st) ← (derive K false [] root).run { probe := probe }
      pure ((p, envV, lkV, hlkV), st)
  let t1 ← IO.monoMsNow
  logInfo m!"derive: {st.nodes} nodes, {st.defs.size} defs, {st.ctors.size} ctors, hasRec {st.hasRec}, misses {st.misses}, {t1 - t0} ms\nsteps: {st.steps.toList}"
  if probe then
    let uniq := st.stops.toList.eraseDups
    logInfo m!"PROBE: {st.stops.size} stuck sub-derivations, {uniq.length} distinct:\n{String.intercalate "\n" uniq}"
    return
  let (p, envV, lkV, hlkV) := res
  -- tables
  let dRow := Lean.mkConst ``DefRow
  let cRow := Lean.mkConst ``CtorRow
  let (dTbl, cTbl) ← liftTermElabM do
    let (dl, st1) ← (do
      let mut out := []
      for (c, lps, val) in st.defs do
        out := out ++ [pairE nameT dRow (toExpr c) (mkApp2 (Lean.mkConst ``DefRow.mk) (toExpr lps) (← qE val))]
      pure out : G (List Lean.Expr)).run {}
    let cl := st.ctors.toList.map fun (c, ind, np, nf) => pairE nameT cRow (toExpr c) (ctorRowE ind np nf)
    pure (mkApp (Lean.mkConst ``mkDelta) (listE (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) nameT dRow) dl),
          mkApp (Lean.mkConst ``mkGamma) (listE (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) nameT cRow) cl))
  let nD := Name.mkStr (← getCurrNamespace) s!"hftDelta{tag}"
  let nG := Name.mkStr (← getCurrNamespace) s!"hftGamma{tag}"
  let tyD := Lean.Expr.forallE `c nameT (optT dRow) .default
  let tyG := Lean.Expr.forallE `c nameT (optT cRow) .default
  liftCoreM <| addDecl (.defnDecl { name := nD, levelParams := [], type := tyD, value := dTbl, hints := .abbrev, safety := .safe })
  liftCoreM <| addDecl (.defnDecl { name := nG, levelParams := [], type := tyG, value := cTbl, hints := .abbrev, safety := .safe })
  let t2 ← IO.monoMsNow
  logInfo m!"tables added ({t2 - t1} ms)"
  let thmName := Name.mkStr (← getCurrNamespace) s!"hftObCDW_of_tables{tag}"
  liftTermElabM do
    let ΔC := Lean.mkConst nD
    let ΓC := Lean.mkConst nG
    withLocalDeclD `env (Lean.mkConst ``Environment) fun e2 => do
    withLocalDeclD `hΔ (mkApp2 (Lean.mkConst ``EnvDefs) e2 ΔC) fun hΔ => do
    withLocalDeclD `hΓ (mkApp2 (Lean.mkConst ``EnvCtors) e2 ΓC) fun hΓ => do
    withLocalDeclD `hrec (mkApp (Lean.mkConst ``RecFact) e2) fun hrec => do
      let lkVal := mkApp2 (Lean.mkConst ``lookOf) ΔC ΓC
      let hlkVal := mkAppN (Lean.mkConst ``envLk_of) #[e2, ΔC, ΓC, hΔ, hΓ, hrec]
      let body := (p.replaceFVars #[envV, lkV, hlkV] #[e2, lkVal, hlkVal])
      let pf ← mkLambdaFVars #[e2, hΔ, hΓ, hrec] body
      let goal := mkApp (Lean.mkConst ``HftObCDW) e2
      let ty ← mkForallFVars #[e2, hΔ, hΓ, hrec] goal
      let t3 ← IO.monoMsNow
      addDecl (.thmDecl { name := thmName, levelParams := [], type := ty, value := pf })
      let t4 ← IO.monoMsNow
      logInfo m!"{thmName} kernel-checked ({t4 - t3} ms)"

@[implemented_by runImpl] opaque run (tag : String) (probe : Bool := false) : CommandElabM Unit

elab "derive_hft_ob " tag:str : command => run tag.getString
elab "probe_hft_ob" : command => run "" true

end Tools.ShippingFGCircuitS1wRun
