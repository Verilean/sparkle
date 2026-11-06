import Tools.ShippingFGCircuitS2bRun
set_option autoImplicit false
-- NOT in the lakefile (manual probe, docs §30.3): `ulimit -v 24000000; kjob lake env lean Tools/ShippingFGCircuitS2bProbe.lean`.
-- Runs the generator in probe mode on `hftRootValue` with a node cap, old (`instE`, tree) vs native (`instantiate1`, DAG) evaluators; prints nodes / ms / peak RSS / the heaviest structure arguments.
open Lean Meta Elab Command Term
open Tools.ShippingFGCircuitS2bGen Tools.ShippingFGCircuitS1wTbl Tools.ShippingFGCircuitS2bShare
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def hwm : IO String := do
  let s ← IO.FS.readFile "/proc/self/status"
  pure ((s.splitOn "\n").filter (fun l => l.startsWith "VmHWM") |>.headD "")
unsafe def runProbe (cap : Nat) (nat : Bool) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.find? ``Tools.ShippingFGCircuitS1kStmt.hftRootValue | throwError "x"
  let some v := ci.value? | throwError "y"
  let root ← liftTermElabM (do unsafe evalExpr Lean.Expr (Lean.mkConst ``Lean.Expr) v)
  let t0 ← IO.monoMsNow
  let r ← liftTermElabM do
    withLocalDeclD `env (Lean.mkConst ``Environment) fun envV => do
    withLocalDeclD `lk (Lean.mkConst ``Look) fun lkV => do
    withLocalDeclD `hlk (mkApp2 (Lean.mkConst ``EnvLk) envV lkV) fun hlkV => do
      let K : Kx := { env := envV, hlk := hlkV, lk := lkV }
      let act : G Unit := do
        try discard (derive K false [] root) catch _ => pure ()
      let ((), st) ← act.run { probe := true, cap := cap, native := nat }
      pure st
  IO.eprintln s!"PROBE native={nat} cap={cap}: nodes={r.nodes} {(← IO.monoMsNow) - t0} ms {← hwm} stops={r.stops.size}"
  for (t, d, _, _) in r.heavy.toList do
    IO.eprintln s!"  heaviest structure argument: tree={t} dag={d}"
  let sumDag := r.log.foldl (fun a l => a + ((l.splitOn "dag=").getLast!.splitOn " ").head!.toNat!) 0
  IO.eprintln s!"  logged steps={r.log.size} sum(dag over completed steps)={sumDag}"
@[implemented_by runProbe] opaque runP (cap : Nat) (nat : Bool) : CommandElabM Unit
elab "probe_cap " n:num " native " b:ident : command => runP n.getNat (b.getId == `true)
probe_cap 12000 native true
