import Tools.ShippingFGCircuitS3vChild
set_option autoImplicit false
-- FG circuit pilot Check58v (S3v): (A) the COMPLETE TYPE of the final theorem `k0_childFn` (`ChildFn pilotK0 (childRange kd) (childValue …)` for the closed child `httpGetByte`), spelled out again with no `ChildFn`/`childValue`/`childRange`/`argPorts` abbreviation and ascribed to the theorem (a mismatch is a compile error); the bridge `ofData_sound` and the slot form `RootShowsAt` uses; (B) negative controls (kernel- or proof-checked; their types restated here); (C) the side conditions of the bridge for `httpGetByte` (closed kernel facts); (D) sizes and kernel time (ONE run); (E) AXIOMS of the S3v modules: standard only.  Scope: ONE closed child; the other child (`pilotK1`) and the root's `bodyOk` are NOT covered.  docs/FG-CIRCUIT-PILOT.md §71.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck58v
open Sparkle.IR.AST Tools.ShippingFGCircuitS3rArtifact Tools.ShippingFGCircuitS3vChild Tools.ShippingFGCircuitS3vBridge
open Sparkle.IR.Semantics (Env MEnv evalAssigns)
open Sparkle.Core.Signal (Signal)

/-! ### (A) the complete type of `k0_childFn`, written again from the design text (no `ChildFn`, `childValue`, `childRange`, `argPorts`) -/

/-- the child's module has ONE output port, and for every memory state and every environment with reset 0 whose argument values (the module's inputs but `clk`/`rst`, in order) are in range of `httpGetByte`'s non-domain input binders' types, the module's IR semantics succeeds and the output port carries the first source observation of `httpGetByte.machineSource` at time 0 on the constant signals the decoded argument values give (`decB`/`decV`, by the binders of `machineData.bsIn`) -/
example : ∃ outP : Port, pilotK0.outputs = [outP] ∧ ∀ (mems : MEnv) (env : Env), env "rst" = 0 →
    Tools.ShippingMachineClose.Zip₂
      (fun (v : Nat) (b : Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder) => match b.2 with
        | .bool => v < 2
        | .bits n => v < 2 ^ n
        | .domain => True)
      ((pilotK0.inputs.filter fun p => p.name != "clk" && p.name != "rst").map fun p => env p.name)
      (Sparkle.IP.Net.HTTP.httpGetByte.machineData.bsIn.filter fun b => b.2 != .domain) →
    ∃ cres, evalAssigns (Sparkle.IR.RegDedup.declWidth pilotK0) mems pilotK0.body env = some cres ∧
      cres outP.name =
        ((Sparkle.IP.Net.HTTP.httpGetByte.machineSource Sparkle.Core.Domain.defaultDomain
            (fun p => Signal.pure
              ((((pilotK0.inputs.filter fun p => p.name != "clk" && p.name != "rst").map fun p => env p.name).getD
                  (Tools.ShippingMachineChild.portIdx Sparkle.IP.Net.HTTP.httpGetByte.machineData.bsIn p) 0) != 0))
            (fun p n => Signal.pure
              (BitVec.ofNat n
                (((pilotK0.inputs.filter fun p => p.name != "clk" && p.name != "rst").map fun p => env p.name).getD
                  (Tools.ShippingMachineChild.portIdx Sparkle.IP.Net.HTTP.httpGetByte.machineData.bsIn p) 0))))[0]?.map
          (fun g => g 0)).getD 0 :=
  k0_childFn

/-- the same theorem, stated through the project's definitions with the data and the function written out -/
example : Tools.ShippingMachineCompose.ChildFn pilotK0
    (Tools.ShippingMachineChild.childRange Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (Tools.ShippingMachineChild.childValue Sparkle.IP.Net.HTTP.httpGetByte.machineSource
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.bsIn Sparkle.Core.Domain.defaultDomain) := k0_childFn

/-- the form `RootShowsAt` needs for call 0: `kidData[0]`/`kidFs[0]` of the root's data (fixed by `SourceData`) and the closed child's module -/
example : ∃ (kd : Tools.ShippingMachineAuto.MachineData) (f : List Nat → Nat),
    Tools.ShippingFGCircuitS3tSpec.kidData[0]? = some kd ∧ Tools.ShippingFGCircuitS3tSpec.kidFs[0]? = some f ∧
      Tools.ShippingMachineCompose.ChildFn pilotK0 (Tools.ShippingMachineChild.childRange kd) f := k0_childFn_slot

/-- the module is the generated closed child: the validator accepted it (kernel) -/
example : Tools.ShippingFGCircuitS3tCombRun.checkK0 pilotK0 = true := Tools.ShippingFGCircuitS3tCombRun.k0_check

/-- the bridge, spelled again: for data with no state whose lets and outputs are in the fragment `Frag`, every output term `ofData` reads off denotes the encoding of `Term.eval` on the typed valuation, with the sort's width -/
example : ∀ (d : Tools.ShippingMachineAuto.MachineData), d.ss.length = 0 → ∀ (V : Nat → Nat)
    (x : Sparkle.Core.HList (Tools.ShippingMachineDenote.tys d.ss)) (B : Nat → Bool) (W : (p w : Nat) → BitVec w),
    (∀ p w, p < d.nIn → (W p w).toNat = V p % 2 ^ w) →
    (∀ l ∈ d.ls, Frag d l.2 = true) → (∀ o ∈ d.outs, Frag d o.2 = true) →
    ∀ (s : Tools.ShippingFGCircuitS3tComb.CSrc), Tools.ShippingFGCircuitS3tCombRun.ofData d = some s →
      s.inPos = Tools.ShippingFGCircuitS3tCombRun.inputPositions d ∧ s.outs.length = d.outs.length ∧
      ∀ (k : Nat) (o : Σ s : Tools.ShippingUnifiedSource.SType, Tools.ShippingUnifiedSource.Term s) (c : Tools.ShippingFGCircuitS3tComb.CTerm),
        d.outs[k]? = some o → s.outs[k]? = some c →
        c.den V = Tools.ShippingMachineDenote.enc o.1
            (Tools.ShippingUnifiedSource.eval (fun j => (letTV d x B W).b (d.bpos j))
              (fun j w => (letTV d x B W).v (d.vpos j) w) o.2) ∧ c.width = sortW o.1 :=
  fun d hss V x B W hW hl ho s h => ofData_sound d hss V x B W hW hl ho s h

/-- `letTV` IS `typedVal` at a time (so the bridge speaks of what `machine_result` speaks of) -/
example : ∀ (d : Tools.ShippingMachineAuto.MachineData) (bools : Nat → Signal Sparkle.Core.Domain.defaultDomain Bool)
    (bits : (j n : Nat) → Signal Sparkle.Core.Domain.defaultDomain (BitVec n)) (t : Nat)
    (x : Sparkle.Core.HList (Tools.ShippingMachineDenote.tys d.ss)),
    Tools.ShippingMachineDenote.typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x =
      letTV d x (fun p => (bools p).val t) (fun p w => (bits p w).val t) := fun d bools bits t x => typedVal_eq d bools bits t x

/-! ### (B) negative controls -/

-- a changed module, a dropped statement, a wrong width, a wrong output: the validator rejects (S3t controls, restated)
example : Tools.ShippingFGCircuitS3tCombRun.checkK0 (Tools.ShippingFGCircuitS3tCombRun.flipConst pilotK0) = false :=
  Tools.ShippingFGCircuitS3tCombRun.neg_flip_const
example : Tools.ShippingFGCircuitS3tCombRun.checkK0 (Tools.ShippingFGCircuitS3tCombRun.swapMux pilotK0) = false :=
  Tools.ShippingFGCircuitS3tCombRun.neg_swap_mux
example : Tools.ShippingFGCircuitS3tCombRun.checkK0 (Tools.ShippingFGCircuitS3tCombRun.dropLast pilotK0) = false :=
  Tools.ShippingFGCircuitS3tCombRun.neg_drop_last
-- the OTHER child's module, and the OTHER child's data, are not `pilotK0` / `httpGetByte`
example : Tools.ShippingFGCircuitS3tCombRun.checkK0 pilotK1 = false := Tools.ShippingFGCircuitS3tCombRun.neg_other_child
example : checkWith Sparkle.IP.Bus.PCIe.tlpCplByte.machineData pilotK0 = false := neg_other_data
-- the conclusion is not vacuous: a wrong function is refused (the module gives 71 at the argument 1, not 0)
example : ¬ Tools.ShippingMachineCompose.ChildFn pilotK0
    (Tools.ShippingMachineChild.childRange Sparkle.IP.Net.HTTP.httpGetByte.machineData) (fun _ => 0) := k0_not_zero
-- a mutated module (the constant 71 changed to 72) does not satisfy the SAME ChildFn
example : ¬ Tools.ShippingMachineCompose.ChildFn (Tools.ShippingFGCircuitS3tCombRun.flipConst pilotK0)
    (Tools.ShippingMachineChild.childRange Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (Tools.ShippingMachineChild.childValue Sparkle.IP.Net.HTTP.httpGetByte.machineSource
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.bsIn Sparkle.Core.Domain.defaultDomain) := flip_not_childFn
-- the evaluation behind the last two (kernel): the module gives 71, the mutated one 72, at the argument 1
example : eval1 pilotK0 = some 71 := k0_eval1
example : eval1 (Tools.ShippingFGCircuitS3tCombRun.flipConst pilotK0) = some 72 := k0_eval1_flip

/-! ### (C) the bridge's side conditions, for `httpGetByte` (closed facts, kernel) -/

example : kd0.ss.length = 0 := k0_ss
example : kd0.ls.all (fun l => Frag kd0 l.2) = true := k0_frag_ls
example : kd0.outs.all (fun o => Frag kd0 o.2) = true := k0_frag_outs
example : kd0.outs.length = 1 := k0_outs_len
example : Tools.ShippingFGCircuitS3tCombRun.inputPositions kd0 = [1] := k0_inpos
example : pilotK0.inputs.length = 1 ∧ pilotK0.outputs.length = 1 := ⟨k0_inputs_len, k0_outputs_len⟩

/-! ### (D) sizes and kernel time, (E) axioms -/

open Lean Meta Elab Command Term

def retime (p : TSyntax `term) : TermElabM Nat := do
  let stx ← `((by decide +kernel : $p ∧ True))
  let t0 ← IO.monoMsNow
  let _ ← elabTermEnsuringType stx none
  synthesizeSyntheticMVarsNoPostponing
  return (← IO.monoMsNow) - t0

run_cmd liftTermElabM do
  let env ← getEnv
  let pre : List Name := [`Tools.ShippingFGCircuitS3vBridge, `Tools.ShippingFGCircuitS3vChild]
  let thms := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    match ci with
    | .thmInfo _ => if pre.any (·.isPrefixOf n) then acc.push n else acc
    | _ => acc
  let mut axs : NameSet := {}
  for nm in thms do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  let finalAx ← Lean.collectAxioms `Tools.ShippingFGCircuitS3vChild.k0_childFn
  logInfo m!"FGCIRCUIT58V AXIOMS: {thms.size} theorems of the S3v modules (Bridge, Child), standard axioms only ({axs.toList}); k0_childFn depends on {finalAx.toList}; no sorryAx, no Lean.ofReduceBool (no native_decide)"
  let sz (n : Name) : MetaM Nat := do
    match (← getConstInfo n) with
    | .thmInfo i => pure i.value.sizeWithoutSharing
    | .defnInfo i => pure i.value.sizeWithoutSharing
    | _ => pure 0
  let sizes ← [`Tools.ShippingFGCircuitS3vBridge.tC_sound, `Tools.ShippingFGCircuitS3vBridge.letsC_sound,
    `Tools.ShippingFGCircuitS3vBridge.ofData_sound, `Tools.ShippingFGCircuitS3vChild.k0_childFn,
    `Tools.ShippingFGCircuitS3vChild.k0_frag_ls, `Tools.ShippingFGCircuitS3vChild.k0_eval1].mapM fun n => do pure (n, ← sz n)
  let t1 ← retime (← `(Tools.ShippingFGCircuitS3vChild.kd0.ls.all (fun l => Tools.ShippingFGCircuitS3vBridge.Frag Tools.ShippingFGCircuitS3vChild.kd0 l.2) = true))
  let t2 ← retime (← `(Tools.ShippingFGCircuitS3vChild.eval1 Tools.ShippingFGCircuitS3rArtifact.pilotK0 = some 71))
  logInfo m!"FGCIRCUIT58V SIZE/TIME (ONE run, this machine; not a bound): term sizes without sharing {sizes}; a fresh `decide +kernel` of the Frag check on the lets took {t1} ms, of `eval1 pilotK0 = some 71` {t2} ms (elaboration + kernel)"
  logInfo m!"FGCIRCUIT58V SIGNATURES: k0_childFn (complete type, spelled without ChildFn/childValue/childRange/argPorts; and through them), the slot form for RootShowsAt call 0 (kidData[0]/kidFs[0]), the bridge ofData_sound, letTV = typedVal: all ascribed to independently written types (a mismatch is a compile error)"
  logInfo m!"FGCIRCUIT58V NEGATIVE CONTROLS: 7 — validator refuses a changed constant, swapped mux branches, a dropped output statement, the other child's module, the other child's data; ChildFn pilotK0 for `fun _ => 0` is false; the mutated module (71→72) does not satisfy the same ChildFn (all kernel- or proof-checked); plus the evaluations behind them"
  logInfo m!"FGCIRCUIT58V SCOPE: ONE closed child (pilotK0 = httpGetByte, 88 statements) for ALL inputs in its range, no run premise; the bridge side conditions (no state, Frag on every let and output, input positions [1], one input one output) are kernel facts for httpGetByte; pilotK1 (tlpCplByte) and the root's bodyOk are NOT covered; ledger unchanged"

end Tests.Gen5.FGCircuitPilotCheck58v
