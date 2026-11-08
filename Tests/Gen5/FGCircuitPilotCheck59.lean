import Tools.ShippingFGCircuitS3wChild
set_option autoImplicit false
-- FG circuit pilot Check59 (S3w): (A) the COMPLETE TYPES of the S3w results written again from the design text (`k1_childFn` without `ChildFn`/`childValue`/`childRange`/`argPorts`; `checkCombN_sound` without `checkCombN`'s help; `normB`'s three facts), (B) the K0 results of S3t/S3v/S3w still hold, (C) negative controls (a mutated `pilotK1`, the other child's data/module, a non-vacuity control, the normalisation's boundary), (D) the bridge side conditions for `tlpCplByte`, (E) sizes, kernel time, AXIOMS.  docs/FG-CIRCUIT-PILOT.md §72.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck59
open Sparkle.IR.AST Tools.ShippingFGCircuitS3rArtifact Tools.ShippingFGCircuitS3wChild Tools.ShippingFGCircuitS3wRun
open Tools.ShippingFGCircuitS3wComb Tools.ShippingFGCircuitS3wBridge Tools.ShippingFGCircuitS3tComb
open Sparkle.IR.Semantics (Env MEnv evalAssigns)
open Sparkle.Core.Signal (Signal)

/-! ### (A) complete types -/

/-- `k1_childFn`, spelled out: ONE output port; for every memory state and every environment with reset 0 whose six argument values (the module's inputs but `clk`/`rst`, in order) are in range of `tlpCplByte`'s input binders, the IR semantics succeeds and the output carries the first observation of `tlpCplByte.machineSource` at time 0 on the constant inputs those values decode to -/
example : ∃ outP : Port, pilotK1.outputs = [outP] ∧ ∀ (mems : MEnv) (env : Env), env "rst" = 0 →
    Tools.ShippingMachineClose.Zip₂
      (fun (v : Nat) (b : Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder) => match b.2 with
        | .bool => v < 2
        | .bits n => v < 2 ^ n
        | .domain => True)
      ((pilotK1.inputs.filter fun p => p.name != "clk" && p.name != "rst").map fun p => env p.name)
      (Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn.filter fun b => b.2 != .domain) →
    ∃ cres, evalAssigns (Sparkle.IR.RegDedup.declWidth pilotK1) mems pilotK1.body env = some cres ∧
      cres outP.name =
        ((Sparkle.IP.Bus.PCIe.tlpCplByte.machineSource Sparkle.Core.Domain.defaultDomain
            (fun p => Signal.pure
              ((((pilotK1.inputs.filter fun p => p.name != "clk" && p.name != "rst").map fun p => env p.name).getD
                  (Tools.ShippingMachineChild.portIdx Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn p) 0) != 0))
            (fun p n => Signal.pure
              (BitVec.ofNat n
                (((pilotK1.inputs.filter fun p => p.name != "clk" && p.name != "rst").map fun p => env p.name).getD
                  (Tools.ShippingMachineChild.portIdx Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn p) 0))))[0]?.map
          (fun g => g 0)).getD 0 :=
  k1_childFn

/-- the same theorem through the project's definitions -/
example : Tools.ShippingMachineCompose.ChildFn pilotK1
    (Tools.ShippingMachineChild.childRange Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (Tools.ShippingMachineChild.childValue Sparkle.IP.Bus.PCIe.tlpCplByte.machineSource
      Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn Sparkle.Core.Domain.defaultDomain) := k1_childFn

/-- the form `RootShowsAt` needs for call 1 -/
example : ∃ (kd : Tools.ShippingMachineAuto.MachineData) (f : List Nat → Nat),
    Tools.ShippingFGCircuitS3tSpec.kidData[1]? = some kd ∧ Tools.ShippingFGCircuitS3tSpec.kidFs[1]? = some f ∧
      Tools.ShippingMachineCompose.ChildFn pilotK1 (Tools.ShippingMachineChild.childRange kd) f := k1_childFn_slot

/-- both calls' conjuncts together (call 0 from S3v, call 1 from S3w) -/
example : (∃ (kd : Tools.ShippingMachineAuto.MachineData) (f : List Nat → Nat),
      Tools.ShippingFGCircuitS3tSpec.kidData[0]? = some kd ∧ Tools.ShippingFGCircuitS3tSpec.kidFs[0]? = some f ∧
        Tools.ShippingMachineCompose.ChildFn pilotK0 (Tools.ShippingMachineChild.childRange kd) f) ∧
    (∃ (kd : Tools.ShippingMachineAuto.MachineData) (f : List Nat → Nat),
      Tools.ShippingFGCircuitS3tSpec.kidData[1]? = some kd ∧ Tools.ShippingFGCircuitS3tSpec.kidFs[1]? = some f ∧
        Tools.ShippingMachineCompose.ChildFn pilotK1 (Tools.ShippingMachineChild.childRange kd) f) :=
  ⟨Tools.ShippingFGCircuitS3vChild.k0_childFn_slot, k1_childFn_slot⟩

/-- `checkCombN_sound`, spelled out: if the normalising validator accepts, the IR semantics of the module succeeds for every valuation, memory state and environment carrying the inputs, and each output port carries the source term's value -/
example : ∀ (s : CSrc) (m : Module), checkCombN s m = true → ∀ (V : Nat → Nat) (mems : MEnv) (env : Env),
    (∀ (i : Nat) (p : Port) (q : Nat), m.inputs[i]? = some p → s.inPos[i]? = some q →
      env p.name = V q % 2 ^ portW p) →
    ∃ env', evalAssigns (Sparkle.IR.RegDedup.declWidth m) mems m.body env = some env' ∧
      ∀ (i : Nat) (p : Port) (c : CTerm), m.outputs[i]? = some p → s.outs[i]? = some c → env' p.name = c.den V :=
  fun s m h V mems env hin => checkCombN_sound s m h V mems env hin

/-- `normB_sound`, spelled out -/
example : ∀ (V : Nat → Nat) (c : CTerm), c.wf = true →
    (normB c).width = c.width ∧ (normB c).wf = true ∧ (normB c).den V = c.den V := fun V c h => normB_sound V c h

/-- the normalisation's behaviour on the shapes in question (kernel): it rewrites exactly `mux c (lit 1 1) (lit 1 0)` with a one-bit `c`; the swapped pair, a wider condition, and a width-1 literal of another value are NOT rewritten -/
example : normB (.mux (.eq (.var 1 5) (.var 2 5)) (.lit 1 1) (.lit 1 0)) = .eq (.var 1 5) (.var 2 5) := by decide +kernel
example : normB (.mux (.eq (.var 1 5) (.var 2 5)) (.lit 1 0) (.lit 1 1)) ≠ .eq (.var 1 5) (.var 2 5) := by decide +kernel
example : normB (.mux (.var 1 2) (.lit 1 1) (.lit 1 0)) = .mux (.var 1 2) (.lit 1 1) (.lit 1 0) := by decide +kernel
example : normB (.mux (.var 1 1) (.lit 2 1) (.lit 2 0)) = .mux (.var 1 1) (.lit 2 1) (.lit 2 0) := by decide +kernel
example : normB (.mux (.var 1 1) (.lit 1 1) (.lit 1 1)) = .mux (.var 1 1) (.lit 1 1) (.lit 1 1) := by decide +kernel

/-! ### (B) the K0 results still hold -/

example : Tools.ShippingFGCircuitS3tCombRun.checkK0 pilotK0 = true := Tools.ShippingFGCircuitS3tCombRun.k0_check
example : checkWithN kd0 pilotK0 = true := k0_checkN
example : Tools.ShippingMachineCompose.ChildFn pilotK0
    (Tools.ShippingMachineChild.childRange Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (Tools.ShippingMachineChild.childValue Sparkle.IP.Net.HTTP.httpGetByte.machineSource
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.bsIn Sparkle.Core.Domain.defaultDomain) :=
  Tools.ShippingFGCircuitS3vChild.k0_childFn
-- the S3t controls on `pilotK0` still hold for the S3t validator, and now for the normalising one
example : Tools.ShippingFGCircuitS3tCombRun.checkK0 (Tools.ShippingFGCircuitS3tCombRun.flipConst pilotK0) = false :=
  Tools.ShippingFGCircuitS3tCombRun.neg_flip_const
example : checkWithN kd0 (Tools.ShippingFGCircuitS3tCombRun.flipConst pilotK0) = false := neg0_flip_const
example : checkWithN kd0 (Tools.ShippingFGCircuitS3tCombRun.swapMux pilotK0) = false := neg0_swap_mux
example : checkWithN kd0 (Tools.ShippingFGCircuitS3tCombRun.dropLast pilotK0) = false := neg0_drop_last
example : checkWithN kd0 (Tools.ShippingFGCircuitS3tCombRun.dropFirst pilotK0) = false := neg0_drop_first
example : checkWithN kd0 (Tools.ShippingFGCircuitS3tCombRun.wrongWidth pilotK0) = false := neg0_wrong_width
example : checkWithN kd0 (Tools.ShippingFGCircuitS3tCombRun.wrongOutW pilotK0) = false := neg0_wrong_out_w
example : checkWithN kd0 (Tools.ShippingFGCircuitS3tCombRun.wrongOutName pilotK0) = false := neg0_wrong_out_name
example : checkWithN kd0 pilotK1 = false := neg0_other_child
example : checkCombN ⟨[1], [CTerm.lit 8 0]⟩ pilotK0 = false := neg0_wrong_source
-- the S3v non-vacuity controls
example : ¬ Tools.ShippingMachineCompose.ChildFn pilotK0
    (Tools.ShippingMachineChild.childRange Sparkle.IP.Net.HTTP.httpGetByte.machineData) (fun _ => 0) :=
  Tools.ShippingFGCircuitS3vChild.k0_not_zero

/-! ### (C) the diagnosis, and negative controls for `pilotK1` -/

-- the diagnosis as kernel facts: `ofData` reads `tlpCplByte`; the S3t validator rejects `pilotK1`; the normalising one accepts it
example : (Tools.ShippingFGCircuitS3tCombRun.ofData kd1).isSome = true := k1_ofData_some
example : (match Tools.ShippingFGCircuitS3tCombRun.ofData kd1 with | some s => checkComb s pilotK1 | none => true) = false :=
  k1_check_unnormalised
example : checkWithN kd1 pilotK1 = true := k1_checkN
-- a mutated `pilotK1` is rejected (dropped statements, a changed constant, a moved slice bound, swapped mux operands, the swapped Bool-to-bit pair, a wrong declared width, a wrong output port)
example : checkWithN kd1 (Tools.ShippingFGCircuitS3tCombRun.dropFirst pilotK1) = false := neg1_drop_first
example : checkWithN kd1 (Tools.ShippingFGCircuitS3tCombRun.dropLast pilotK1) = false := neg1_drop_last
example : checkWithN kd1 (flip74 pilotK1) = false := neg1_flip_const
example : checkWithN kd1 (moveSlice pilotK1) = false := neg1_move_slice
example : checkWithN kd1 (Tools.ShippingFGCircuitS3tCombRun.swapMux pilotK1) = false := neg1_swap_mux
example : checkWithN kd1 (swapBoolPair pilotK1) = false := neg1_swap_bool_pair
example : checkWithN kd1 (Tools.ShippingFGCircuitS3tCombRun.wrongWidth pilotK1) = false := neg1_wrong_width
example : checkWithN kd1 (Tools.ShippingFGCircuitS3tCombRun.wrongOutW pilotK1) = false := neg1_wrong_out_w
example : checkWithN kd1 (Tools.ShippingFGCircuitS3tCombRun.wrongOutName pilotK1) = false := neg1_wrong_out_name
-- the other child's module / data
example : checkWithN kd1 pilotK0 = false := neg1_other_child
example : checkCombN ⟨[1, 2, 3, 4, 5, 6], [CTerm.lit 8 0]⟩ pilotK1 = false := neg1_wrong_source
-- the conclusion is not vacuous: a wrong function is refused (the module gives 74 at count 1, not 0), and a mutated module (74 → 75) does not satisfy the same `ChildFn`
example : ¬ Tools.ShippingMachineCompose.ChildFn pilotK1
    (Tools.ShippingMachineChild.childRange Sparkle.IP.Bus.PCIe.tlpCplByte.machineData) (fun _ => 0) := k1_not_zero
example : ¬ Tools.ShippingMachineCompose.ChildFn (flip74 pilotK1)
    (Tools.ShippingMachineChild.childRange Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (Tools.ShippingMachineChild.childValue Sparkle.IP.Bus.PCIe.tlpCplByte.machineSource
      Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn Sparkle.Core.Domain.defaultDomain) := flip74_not_childFn
example : k1eval pilotK1 = some 74 := k1_eval
example : k1eval (flip74 pilotK1) = some 75 := k1_eval_flip

/-! ### (D) the bridge's side conditions, for `tlpCplByte` (closed facts, kernel) -/

example : Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.ss.length = 0 := k1_ss
example : Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.ls.all
    (fun l => FragW Sparkle.IP.Bus.PCIe.tlpCplByte.machineData l.2) = true := k1_frag_ls
example : Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.outs.all
    (fun o => FragW Sparkle.IP.Bus.PCIe.tlpCplByte.machineData o.2) = true := k1_frag_outs
example : Tools.ShippingFGCircuitS3tCombRun.inputPositions Sparkle.IP.Bus.PCIe.tlpCplByte.machineData = [1, 2, 3, 4, 5, 6] := k1_inpos
example : pilotK1.inputs.length = 6 ∧ pilotK1.outputs.length = 1 := ⟨k1_inputs_len, k1_outputs_len⟩

/-! ### (E) sizes, kernel time, axioms -/

open Lean Meta Elab Command Term

def retime (p : TSyntax `term) : TermElabM Nat := do
  let stx ← `((by decide +kernel : $p ∧ True))
  let t0 ← IO.monoMsNow
  let _ ← elabTermEnsuringType stx none
  synthesizeSyntheticMVarsNoPostponing
  return (← IO.monoMsNow) - t0

run_cmd liftTermElabM do
  let env ← getEnv
  let pre : List Name := [`Tools.ShippingFGCircuitS3wComb, `Tools.ShippingFGCircuitS3wRun, `Tools.ShippingFGCircuitS3wBridge,
    `Tools.ShippingFGCircuitS3wChild]
  let thms := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    match ci with
    | .thmInfo _ => if pre.any (·.isPrefixOf n) then acc.push n else acc
    | _ => acc
  let mut axs : NameSet := {}
  for nm in thms do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  let finalAx ← Lean.collectAxioms `Tools.ShippingFGCircuitS3wChild.k1_childFn
  logInfo m!"FGCIRCUIT59 AXIOMS: {thms.size} theorems of the S3w modules (Comb, Run, Bridge, Child), standard axioms only ({axs.toList}); k1_childFn depends on {finalAx.toList}; no sorryAx, no Lean.ofReduceBool (no native_decide)"
  let sz (n : Name) : MetaM Nat := do
    match (← getConstInfo n) with
    | .thmInfo i => pure i.value.sizeWithoutSharing
    | .defnInfo i => pure i.value.sizeWithoutSharing
    | _ => pure 0
  let sizes ← [`Tools.ShippingFGCircuitS3wComb.normB_sound, `Tools.ShippingFGCircuitS3wComb.checkCombN_sound,
    `Tools.ShippingFGCircuitS3wBridge.tC_soundW, `Tools.ShippingFGCircuitS3wBridge.ofData_soundW,
    `Tools.ShippingFGCircuitS3wChild.k1_childFn, `Tools.ShippingFGCircuitS3wChild.k1_frag_ls,
    `Tools.ShippingFGCircuitS3wRun.k1_checkN].mapM fun n => do pure (n, ← sz n)
  let t1 ← retime (← `(Tools.ShippingFGCircuitS3wRun.checkWithN Tools.ShippingFGCircuitS3wRun.kd1 Tools.ShippingFGCircuitS3rArtifact.pilotK1 = true))
  let t2 ← retime (← `(Tools.ShippingFGCircuitS3wChild.k1eval Tools.ShippingFGCircuitS3rArtifact.pilotK1 = some 74))
  logInfo m!"FGCIRCUIT59 SIZE/TIME (ONE run, this machine; not a bound): term sizes without sharing {sizes}; a fresh `decide +kernel` of `checkWithN kd1 pilotK1 = true` took {t1} ms, of `k1eval pilotK1 = some 74` {t2} ms (elaboration + kernel)"
  logInfo m!"FGCIRCUIT59 SIGNATURES: k1_childFn (complete type, spelled without ChildFn/childValue/childRange/argPorts; and through them), the slot form for call 1 (kidData[1]/kidFs[1]) and both slots together, checkCombN_sound, normB_sound: all ascribed to independently written types above"
  logInfo m!"FGCIRCUIT59 NEGATIVE CONTROLS: pilotK1 mutated 9 (dropped first/last statement, constant 74→75, slice bound moved, swapped mux operands, swapped Bool-to-bit constants, wrong declared width, 7-bit output, renamed output) + the other child's module/data + a wrong source term; ChildFn pilotK1 for `fun _ => 0` is false; the mutated module (74→75) does not satisfy the same ChildFn; normB leaves the swapped pair, a 2-bit condition, a 2-bit literal pair, and a (1,1) pair alone; all S3t/S3v pilotK0 controls (9 + 2) still hold"
  logInfo m!"FGCIRCUIT59 SCOPE: TWO closed children (pilotK0 = httpGetByte 88 statements, pilotK1 = tlpCplByte 159 statements) for ALL inputs in their range, no run premise; the new rule is ONE proved normalisation of the MODULE side (mux c (lit 1 1) (lit 1 0), c one bit, is c); the comparison with the source term is still equality; the root's bodyOk and checkRoot_sound are NOT proved"

end Tests.Gen5.FGCircuitPilotCheck59
