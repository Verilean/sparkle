import Tools.ShippingFGCircuitS2bGen
set_option autoImplicit false
-- FG circuit pilot S1w2: runs the generator on `hftRootValue` and emits the kernel-checked theorem `hftObCDW_of_tables`. docs/FG-CIRCUIT-PILOT.md §23.3 / §23.6.
-- Nothing here is trusted: the emitted declarations are checked by the kernel (`addDecl`). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.
namespace Tools.ShippingFGCircuitS2bRun
open Lean Meta Elab Command
open Lean (mkConst mkApp mkApp2 mkApp3 mkApp4 mkAppN)
open Sparkle.Core Tools.ShippingGen5ConstValueE Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1sCD
open Tools.ShippingFGCircuitS1wTbl Tools.ShippingFGCircuitS2bGen Tools.ShippingFGCircuitS2bShare

/-- the lookup of a literal association list -/
def mkDelta (l : List (Name × DefRow)) : Name → Option DefRow := fun c => (l.find? (fun p => p.1 == c)).map (·.2)
def mkGamma (l : List (Name × CtorRow)) : Name → Option CtorRow := fun c => (l.find? (fun p => p.1 == c)).map (·.2)

def listE (α : Lean.Expr) : List Lean.Expr → Lean.Expr
  | [] => mkApp (Lean.mkConst ``List.nil [Level.zero]) α
  | x :: xs => mkApp3 (Lean.mkConst ``List.cons [Level.zero]) α x (listE α xs)

def pairE (α β a b : Lean.Expr) : Lean.Expr := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) α β a b

/-- derive `DS env [] root r` (r inferred) for a closed `root : Expr`, add the tables and the theorem `thm`; reports nodes/time/term size. `cap > 0` stops after that many nodes (probe). -/
unsafe def deriveRoot (root : Lean.Expr) (thmName : Name) (cap : Nat := 0) : CommandElabM (Nat × Nat × Nat) := do
  let t0 ← IO.monoMsNow
  let (res, st) ← liftTermElabM do
    withLocalDeclD `env (Lean.mkConst ``Environment) fun envV => do
    withLocalDeclD `lk (Lean.mkConst ``Look) fun lkV => do
    withLocalDeclD `hlk (mkApp2 (Lean.mkConst ``EnvLk) envV lkV) fun hlkV => do
      let K : Kx := { env := envV, hlk := hlkV, lk := lkV }
      let (p, st) ← (derive K false [] root).run { cap := cap }
      pure ((p, envV, lkV, hlkV), st)
  let t1 ← IO.monoMsNow
  let (p, envV, lkV, hlkV) := res
  let dRow := Lean.mkConst ``DefRow
  let cRow := Lean.mkConst ``CtorRow
  let (dTbl, cTbl) ← liftTermElabM do
    let (dl, _) ← (do
      let mut out := []
      for (c, lps, val) in st.defs do
        out := out ++ [pairE nameT dRow (toExpr c) (mkApp2 (Lean.mkConst ``DefRow.mk) (toExpr lps) (← qE val))]
      pure out : G (List Lean.Expr)).run {}
    let cl := st.ctors.toList.map fun (c, ind, np, nf) => pairE nameT cRow (toExpr c) (ctorRowE ind np nf)
    pure (mkApp (Lean.mkConst ``mkDelta) (listE (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) nameT dRow) dl),
          mkApp (Lean.mkConst ``mkGamma) (listE (mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) nameT cRow) cl))
  let nD := Name.str thmName "Delta"
  let nG := Name.str thmName "Gamma"
  liftCoreM <| addDecl (.defnDecl { name := nD, levelParams := [], type := Lean.Expr.forallE `c nameT (optT dRow) .default, value := dTbl, hints := .abbrev, safety := .safe })
  liftCoreM <| addDecl (.defnDecl { name := nG, levelParams := [], type := Lean.Expr.forallE `c nameT (optT cRow) .default, value := cTbl, hints := .abbrev, safety := .safe })
  let t2 ← IO.monoMsNow
  let sz ← liftTermElabM do
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
      let ty ← mkForallFVars #[e2, hΔ, hΓ, hrec] (← inferType body)
      let t3 ← IO.monoMsNow
      addDecl (.thmDecl { name := thmName, levelParams := [], type := ty, value := pf })
      let t4 ← IO.monoMsNow
      logInfo m!"{thmName}: derive {st.nodes} nodes ({t1 - t0} ms), tables {st.defs.size} defs {st.ctors.size} ctors ({t2 - t1} ms), kernel {t4 - t3} ms, term dag {(dagTree pf).1}"
      pure (dagTree pf).1
  pure (st.nodes, t1 - t0, sz)

unsafe def runImpl (tag : String) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.find? ``Tools.ShippingFGCircuitS1kStmt.hftRootValue | throwError "hftRootValue"
  let some v := ci.value? | throwError "hftRootValue value"
  let root ← liftTermElabM (do let r ← unsafe evalExpr Lean.Expr (Lean.mkConst ``Lean.Expr) v; pure r)
  discard <| deriveRoot root (Name.mkStr (← getCurrNamespace) s!"hftObCDS_of_tables{tag}")

@[implemented_by runImpl] opaque run (tag : String) : CommandElabM Unit

elab "derive_hft_ob " tag:str : command => run tag.getString

/-- derive the typed `DS` derivation of a closed `Expr` given by a term, as the theorem `name` -/
unsafe def deriveTermImpl (name : Name) (e : Lean.Expr) : CommandElabM Unit := discard <| deriveRoot e name
@[implemented_by deriveTermImpl] opaque deriveTerm (name : Name) (e : Lean.Expr) : CommandElabM Unit

elab "derive_expr " n:ident " := " t:term : command => do
  let e ← liftTermElabM do
    let tm ← Term.elabTerm t (some (Lean.mkConst ``Lean.Expr))
    Term.synthesizeSyntheticMVarsNoPostponing
    unsafe evalExpr Lean.Expr (Lean.mkConst ``Lean.Expr) (← instantiateMVars tm)
  deriveTerm (Name.mkStr (← getCurrNamespace) n.getId.toString) e

end Tools.ShippingFGCircuitS2bRun
