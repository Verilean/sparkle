import Tools.ShippingFGCircuitS2iGen
import Tools.ShippingFGCircuitS2bRun
set_option autoImplicit false
-- FG circuit pilot S2i: runs the closure generator on a closed `Expr` and emits the kernel-checked theorem over the tables `EnvDefs`/`EnvCtors`/`RecFact`. docs/FG-CIRCUIT-PILOT.md §35.
-- Nothing here is trusted: the emitted declarations are checked by the kernel (`addDecl`). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.
namespace Tools.ShippingFGCircuitS2iRun
open Lean Meta Elab Command
open Lean (mkConst mkApp mkApp2 mkApp3 mkApp4 mkAppN)
open Sparkle.Core Tools.ShippingGen5ConstValueE Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1sCD
open Tools.ShippingFGCircuitS1wTbl Tools.ShippingFGCircuitS2bGen Tools.ShippingFGCircuitS2bShare Tools.ShippingFGCircuitS2bRun Tools.ShippingFGCircuitS2iSh
open Tools.ShippingFGCircuitS2iDT Tools.ShippingFGCircuitS2iTbl Tools.ShippingFGCircuitS2iGen

structure RootStats where
  nodes : Nat
  shSteps : Nat
  viaN : Nat
  msGen : Nat
  msTables : Nat
  msKernel : Nat
  dagNodes : Nat
  treeNodes : Nat
  defs : Nat
  ctors : Nat
  kinds : Array (String × Nat)
  steps : Array (String × Nat)

def hwmKb : IO Nat := do
  let s ← IO.FS.readFile "/proc/self/status"
  match (s.splitOn "\n").filter (fun l => l.startsWith "VmHWM") with
  | l :: _ => pure ((l.splitOn " ").filter (· ≠ "") |>.getD 1 "0").toNat!
  | [] => pure 0

/-- derive `DT env [] root r` (r inferred) for a closed `root : Expr`, add the tables and the theorem `thm`; `cap > 0` stops after that many nodes (probe) -/
unsafe def deriveRootT (root : Lean.Expr) (thmName : Name) (cap : Nat := 0) : CommandElabM RootStats := do
  let t0 ← IO.monoMsNow
  let (res, st, st2) ← liftTermElabM do
    withLocalDeclD `env (Lean.mkConst ``Environment) fun envV => do
    withLocalDeclD `lk (Lean.mkConst ``Look) fun lkV => do
    withLocalDeclD `hlk (mkApp2 (Lean.mkConst ``EnvLk) envV lkV) fun hlkV => do
      let K : Kx := { env := envV, hlk := hlkV, lk := lkV }
      let ((p, st2), st) ← ((deriveT K false nilCx root).run {}).run { cap := cap }
      pure ((p, envV, lkV, hlkV), st, st2)
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
      let ty ← mkForallFVars #[e2, hΔ, hΓ, hrec] (← inferType body)
      let (dag, tree) := dagTree pf
      let t3 ← IO.monoMsNow
      addDecl (.thmDecl { name := thmName, levelParams := [], type := ty, value := pf })
      let t4 ← IO.monoMsNow
      let rss ← hwmKb
      let stats : RootStats := { nodes := st.nodes, shSteps := st2.shSteps, viaN := st2.viaN, msGen := t1 - t0, msTables := t2 - t1, msKernel := t4 - t3,
                                  dagNodes := dag, treeNodes := tree, defs := st.defs.size, ctors := st.ctors.size, kinds := st2.shKinds, steps := st.steps }
      logInfo m!"{thmName}: derive {st.nodes} DT nodes, {st2.shSteps} Sh steps ({st2.viaN} viaSh) in {t1 - t0} ms, tables {st.defs.size} defs {st.ctors.size} ctors ({t2 - t1} ms), kernel {t4 - t3} ms, term dag {dag} tree {tree}, peak RSS {rss} kB"
      pure stats

unsafe def deriveTermT (name : Name) (e : Lean.Expr) : CommandElabM Unit := discard <| deriveRootT e name
@[implemented_by deriveTermT] opaque deriveTerm (name : Name) (e : Lean.Expr) : CommandElabM Unit

elab "derive_expr_t " n:ident " := " t:term : command => do
  let e ← liftTermElabM do
    let tm ← Term.elabTerm t (some (Lean.mkConst ``Lean.Expr))
    Term.synthesizeSyntheticMVarsNoPostponing
    unsafe evalExpr Lean.Expr (Lean.mkConst ``Lean.Expr) (← instantiateMVars tm)
  deriveTerm (Name.mkStr (← getCurrNamespace) n.getId.toString) e

unsafe def runHftImpl (tag : String) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.find? ``Tools.ShippingFGCircuitS1kStmt.hftRootValue | throwError "hftRootValue"
  let some v := ci.value? | throwError "hftRootValue value"
  let root ← liftTermElabM (do let r ← unsafe evalExpr Lean.Expr (Lean.mkConst ``Lean.Expr) v; pure r)
  discard <| deriveRootT root (Name.mkStr (← getCurrNamespace) s!"hftObCDT_of_tables{tag}")

@[implemented_by runHftImpl] opaque runHft (tag : String) : CommandElabM Unit

/-- derive the typed `DT` derivation of `hftRootValue` (the S2i attempt); not used by the light checks -/
elab "derive_hft_t " tag:str : command => runHft tag.getString

end Tools.ShippingFGCircuitS2iRun
