import Tools.ShippingFGCircuitS2iRun
set_option autoImplicit false
-- NOT in the lakefile (manual probe, docs §35): `kjob lake env lean Tools/ShippingFGCircuitS2iProbe.lean` (bounded by `timeout`, measured with /usr/bin/time -v).
-- Runs the closure generator in probe mode on `hftRootValue` with a node cap; prints DT nodes / Sh steps / ms / peak RSS and the (deduplicated) stops, i.e. the exact unsupported subterms.
open Lean Meta Elab Command Term
open Tools.ShippingFGCircuitS2bGen Tools.ShippingFGCircuitS1wTbl Tools.ShippingFGCircuitS2bShare Tools.ShippingFGCircuitS2iGen Tools.ShippingFGCircuitS2iSh Tools.ShippingFGCircuitS2iRun
set_option maxHeartbeats 0
set_option maxRecDepth 100000
unsafe def runProbe (cap : Nat) : CommandElabM Unit := do
  let env ← getEnv
  let some ci := env.find? ``Tools.ShippingFGCircuitS1kStmt.hftRootValue | throwError "x"
  let some v := ci.value? | throwError "y"
  let root ← liftTermElabM (do unsafe evalExpr Lean.Expr (Lean.mkConst ``Lean.Expr) v)
  let t0 ← IO.monoMsNow
  let (st, st2) ← liftTermElabM do
    withLocalDeclD `env (Lean.mkConst ``Environment) fun envV => do
    withLocalDeclD `lk (Lean.mkConst ``Look) fun lkV => do
    withLocalDeclD `hlk (mkApp2 (Lean.mkConst ``EnvLk) envV lkV) fun hlkV => do
      let K : Kx := { env := envV, hlk := hlkV, lk := lkV }
      let act : G2 Unit := do
        try discard (deriveT K false nilCx root) catch ex => do
          let m ← ex.toMessageData.toString
          modifyThe St fun s => { s with stops := s.stops.push s!"TOP: {m}" }
      let (((), st2), st) ← ((act.run {}).run { probe := true, cap := cap })
      pure (st, st2)
  IO.eprintln s!"PROBE cap={cap}: DT nodes={st.nodes} Sh steps={st2.shSteps} viaSh={st2.viaN} {(← IO.monoMsNow) - t0} ms peakRSS={← hwmKb} kB stops={st.stops.size}"
  IO.eprintln s!"  DT rules={st.steps.toList}"
  IO.eprintln s!"  Sh steps by kind={st2.shKinds.toList}"
  IO.eprintln s!"  poly unfoldings={st2.poly.size}"
  for s in (st.stops.toList.eraseDups) do
    IO.eprintln s!"  stop: {s.take 600}"
@[implemented_by runProbe] opaque runP (cap : Nat) : CommandElabM Unit
elab "probe_cap_t " n:num : command => runP n.getNat
probe_cap_t 0
