import Lean
import Tools.VedMemLoop

/-!
# Diagnosis only: the kernel check of the causal side condition of the memory loop (sparkle-ved-mem-r033-proof)

NOT imported by any production module (`Tools.VedMemEntry`, `Tests.AllTests`).  A diagnosis case `import`s it; its `initialize`
installs a function in the no-op hook `Tools.VedMemLoop.causalHook`, which `ved_loop_unfold_mem` calls with the closed side
condition.  Environment (all optional; the hook does nothing without `VED_KERNEL_PROBE` or `VED_STOP_AFTER_CAUSAL`):

* `VED_STOP_AFTER_CAUSAL=n`: act only on the first side condition whose goal has at least `n` tree nodes, and after acting stop the
  process with exit code 3.
* `VED_STOP_AFTER_CAUSAL_N=n`: count the closed side conditions; every one is reported (tree size, time), and after the `n`-th
  (the kernel probe below acts on it only) the process stops with exit code 3.
* `VED_KERNEL_PROBE=s`: kernel-check the closed side condition (an auxiliary theorem over the goal's local context, checked by
  `Kernel.Environment.addDecl`, the result is dropped), synchronously, with a wall cap of `s` seconds (on the cap the check is
  cancelled and "not finished" is recorded).  The kernel's own heartbeat limit is off for the probe (the wall cap bounds it).

Lines go to stderr (`VED PROBE ...`) and, with `VED_DUMP_DIR`, to `addr.log`.
-/

open Lean Meta Elab Tactic

namespace Tools.VedMemCausalProbe

initialize closedCount : IO.Ref Nat ← IO.mkRef 0

def probe (hSc : MVarId) : TacticM Unit := do
  let stop := (← IO.getEnv "VED_STOP_AFTER_CAUSAL").bind (·.toNat?)
  let stopN := (← IO.getEnv "VED_STOP_AFTER_CAUSAL_N").bind (·.toNat?)
  let kprobe := (← IO.getEnv "VED_KERNEL_PROBE").map fun s => s.toNat?.getD 600
  if stop.isNone && kprobe.isNone && stopN.isNone then return
  let szT := Tools.VedU1Loop.treeSizeVal (← instantiateMVars (← hSc.getType))
  let cnt := (← closedCount.get) + 1
  closedCount.set cnt
  if let some n := stopN then
    let msg := s!"causal side condition #{cnt} closed tree={szT} t={← IO.monoMsNow} hb={(← IO.getNumHeartbeats) / 1000}"
    IO.eprintln s!"VED PROBE {msg}"
    Tools.VedMemLoop.dbgLog s!"PROBE {msg}"
    if cnt < n then return
  else if szT < stop.getD 0 then return
  let say (msg : String) : IO Unit := do
    IO.eprintln s!"VED PROBE {msg}"
    Tools.VedMemLoop.dbgLog s!"PROBE {msg}"
  say s!"side condition tree={szT} t={← IO.monoMsNow} hb={(← IO.getNumHeartbeats) / 1000}"
  if let some cap := kprobe then
    try
      hSc.withContext do
        let xs := (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d.toExpr
        let ty ← mkForallFVars xs (← instantiateMVars (← hSc.getType))
        let pf ← mkLambdaFVars xs (← instantiateMVars (mkMVar hSc))
        let dag := (Tools.VedU1WireShare.collectDag (fun _ => true) pf).size
        say s!"proof term dag={dag} has_mvar={pf.hasMVar} type_dag={(Tools.VedU1WireShare.collectDag (fun _ => true) ty).size}"
        let decl := Declaration.thmDecl { name := `ved_kernel_probe, levelParams := [], type := ty, value := pf }
        let opts := (← getOptions).insert `maxHeartbeats (DataValue.ofNat 0)
        let kenv := (← getEnv).toKernelEnv
        let tk ← IO.CancelToken.new
        let t0 ← IO.monoMsNow
        let task := Task.spawn (prio := .dedicated) fun _ => kenv.addDecl opts decl (some tk)
        let mut capped := false
        while !(← IO.hasFinished task) do
          if (← IO.monoMsNow) - t0 ≥ cap * 1000 then
            tk.set
            capped := true
            break
          IO.sleep 200
        let t1 ← IO.monoMsNow
        if capped then
          say s!"KERNEL not finished within {cap} s (cancelled) ms={t1 - t0} proofDag={dag}"
        else
          match task.get with
          | .ok _ => say s!"KERNEL ok ms={t1 - t0} proofDag={dag}"
          | .error _ => say s!"KERNEL rejected ms={t1 - t0} proofDag={dag}"
    catch e => say s!"KERNEL probe error {(← e.toMessageData.toString).take 300}"
  if stop.isSome || stopN.isSome then
    say s!"STOP_AFTER_CAUSAL t={← IO.monoMsNow} tree={szT}"
    IO.Process.exit 3

initialize Tools.VedMemLoop.causalHook.set (some probe)

end Tools.VedMemCausalProbe
