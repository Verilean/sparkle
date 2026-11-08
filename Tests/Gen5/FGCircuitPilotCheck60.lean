import Tools.ShippingFGCircuitS3yEntry
set_option autoImplicit false
-- FG circuit pilot Check60 (S3y): (A) the COMPLETE TYPES of the general theorems `checkData_sound` (G1) and `certifiedEntryC_sound` (G2), the definitions `dataValue` / `DataShows` / `checkData` unfolded (G2 takes the run's success as its premise) and ascribed to independently written types (a mismatch is a compile error); `k0_childFn'` through the general theorem; (B) controls: a wrong module rejected, another child's data rejected, `DataShows` non-vacuous (a constant function fails for `pilotK0`'s data; the data's value at the argument 1 is 71; a mutated module is not `DataShows`), the guard (a false check admits no successful run); (C) the freeze-independence of the statements (no `Laws`/`CellPrem`/`hr`/quiet in the types); (D) sizes and kernel time (ONE run); (B2, S3y2) the CONTRACT of the first fragment: complete types of `circOk_spec` / `portsOk_spec` / `checkData_contract`, a kernel control for each rejection (Bool input, zero-width input, zero-width output, no output, two outputs, output port width mismatch, an extra input port, two output ports, a `clk` port) and vacuity controls (the range is never empty, the output list is non-empty, a wrong value function is not satisfied); the read-failure theorem `certifiedEntryC_no_read`; (E) AXIOMS: standard only.  Scope: the combinational sub-language, ONE closed child as the instance; registers, instances, the top operators and `DeclDenotes` are NOT covered.  docs/FG-CIRCUIT-PILOT.md §73.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck60
open Sparkle.IR.AST Tools.ShippingFGCircuitS3rArtifact Tools.ShippingFGCircuitS3yGen Tools.ShippingFGCircuitS3yEntry
open Tools.ShippingFGCircuitS3vChild (kd0 k0_childFn k0_not_zero flip_not_childFn k0_range_one)
open Tools.ShippingFGCircuitS3tSpec (designOk)
open Tools.ShippingFGCircuitS3tCombRun (flipConst dropFirst dropLast swapMux)
open Sparkle.IR.Semantics (Env MEnv evalAssigns)

/-! ### (A) complete types, written again from the design text -/

/-- G1: for every data `d` and module `m`, a true `checkData d m` gives, for every state value, a single output port whose IR value on every memory state and every environment with reset 0 and in-range argument values is the encoding of `Term.eval` of the data's first output under `letTV` at the decoding of those argument values (`dataValue` unfolded) -/
example : ∀ (d : Tools.ShippingMachineAuto.MachineData) (m : Module), checkData d m = true →
    ∀ x : Sparkle.Core.HList (Tools.ShippingMachineDenote.tys d.ss),
      ∃ outP : Port, m.outputs = [outP] ∧ ∀ (mems : MEnv) (env : Env), env "rst" = 0 →
        Tools.ShippingMachineClose.Zip₂
          (fun (v : Nat) (b : Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder) => match b.2 with
            | .bool => v < 2
            | .bits n => v < 2 ^ n
            | .domain => True)
          ((m.inputs.filter fun p => p.name != "clk" && p.name != "rst").map fun p => env p.name)
          (d.bsIn.filter fun b => b.2 != .domain) →
        ∃ cres, evalAssigns (Sparkle.IR.RegDedup.declWidth m) mems m.body env = some cres ∧
          cres outP.name =
            (match d.outs[0]? with
             | none => 0
             | some o =>
               Tools.ShippingMachineDenote.enc o.1
                 (Tools.ShippingUnifiedSource.eval
                   (fun j => (Tools.ShippingFGCircuitS3vBridge.letTV d x
                      (Tools.ShippingMachineChild.decB d.bsIn
                        ((m.inputs.filter fun p => p.name != "clk" && p.name != "rst").map fun p => env p.name))
                      (Tools.ShippingMachineChild.decV d.bsIn
                        ((m.inputs.filter fun p => p.name != "clk" && p.name != "rst").map fun p => env p.name))).b (d.bpos j))
                   (fun j w => (Tools.ShippingFGCircuitS3vBridge.letTV d x
                      (Tools.ShippingMachineChild.decB d.bsIn
                        ((m.inputs.filter fun p => p.name != "clk" && p.name != "rst").map fun p => env p.name))
                      (Tools.ShippingMachineChild.decV d.bsIn
                        ((m.inputs.filter fun p => p.name != "clk" && p.name != "rst").map fun p => env p.name))).v (d.vpos j) w)
                   o.2)) :=
  fun d m h x => checkData_sound d m h x

/-- `checkData` unfolded: the fragment/port checks, then the source terms `ofData` read off the data and the validator `checkComb` on them -/
example : ∀ (d : Tools.ShippingMachineAuto.MachineData) (m : Module), checkData d m =
    (circOk d && portsOk d m &&
      (match Tools.ShippingFGCircuitS3tCombRun.ofData d with
       | some s => Tools.ShippingFGCircuitS3tComb.checkComb s m
       | none => false)) := fun _ _ => rfl

/-- `circOk` unfolded -/
example : ∀ (d : Tools.ShippingMachineAuto.MachineData), circOk d =
    ((d.ss.isEmpty && (d.outs.length == 1) &&
      d.ls.all (fun l => Tools.ShippingFGCircuitS3vBridge.Frag d l.2) &&
      d.outs.all (fun o => Tools.ShippingFGCircuitS3vBridge.Frag d o.2)) &&
      d.outs.all (fun o => decide (0 < Tools.ShippingFGCircuitS3vBridge.sortW o.1))) := fun _ => rfl

/-- `portsOk` unfolded: count, no clk/rst, port width = binder width (in order), `inputPositions`/`portIdx`, one output; then only non-zero-width bits inputs; then the output port width = the output sort's width -/
example : ∀ (d : Tools.ShippingMachineAuto.MachineData) (m : Module), portsOk d m =
    (((m.inputs.length == (d.bsIn.filter (fun b => b.2 != .domain)).length) &&
      m.inputs.all (fun p => p.name != "clk" && p.name != "rst") &&
      (m.inputs.zip (d.bsIn.filter (fun b => b.2 != .domain))).all (fun (p, b) => Tools.ShippingFGCircuitS3tComb.portW p == binderW b.2) &&
      ((Tools.ShippingFGCircuitS3tCombRun.inputPositions d).length == (d.bsIn.filter (fun b => b.2 != .domain)).length) &&
      (List.range (Tools.ShippingFGCircuitS3tCombRun.inputPositions d).length).all (fun i =>
        Tools.ShippingMachineChild.portIdx d.bsIn ((Tools.ShippingFGCircuitS3tCombRun.inputPositions d).getD i 0) == i) &&
      (m.outputs.length == 1)) &&
     (d.bsIn.filter (fun b => b.2 != .domain)).all (fun b => inKindOk b.2) &&
     (m.outputs.zip d.outs).all (fun (p, o) => Tools.ShippingFGCircuitS3tComb.portW p == Tools.ShippingFGCircuitS3vBridge.sortW o.1)) := fun _ _ => rfl

/-- `inKindOk`: only `BitVec n` with `0 < n`; `Bool` and (as a hardware input) `domain` are refused -/
example : (inKindOk .bool = false) ∧ (inKindOk (.bits 0) = false) ∧ (inKindOk (.bits 6) = true) ∧ (inKindOk .domain = false) := by decide

/-- `circOk_spec`, complete type -/
example : ∀ (d : Tools.ShippingMachineAuto.MachineData), circOk d = true →
    d.ss = [] ∧ d.outs.length = 1 ∧
    d.ls.all (fun l => Tools.ShippingFGCircuitS3vBridge.Frag d l.2) = true ∧
    d.outs.all (fun o => Tools.ShippingFGCircuitS3vBridge.Frag d o.2) = true ∧
    (∀ o ∈ d.outs, 0 < Tools.ShippingFGCircuitS3vBridge.sortW o.1) := circOk_spec

/-- `checkData_contract`, complete type: exactly one output term of non-zero width; exactly one output port; every hardware input is `BitVec n`, `0 < n` -/
example : ∀ (d : Tools.ShippingMachineAuto.MachineData) (m : Module), checkData d m = true →
    (∃ o, d.outs = [o] ∧ 0 < Tools.ShippingFGCircuitS3vBridge.sortW o.1) ∧ (∃ p, m.outputs = [p]) ∧
    (∀ b ∈ d.bsIn.filter (fun b => b.2 != .domain), ∃ n, b.2 = .bits n ∧ 0 < n) := checkData_contract

/-- `portsOk_spec`: the contract part, complete type (the six count/width/order facts are `portsOk0_spec`) -/
example : ∀ (d : Tools.ShippingMachineAuto.MachineData) (m : Module), portsOk d m = true →
    (∀ b ∈ d.bsIn.filter (fun b => b.2 != .domain), ∃ n, b.2 = .bits n ∧ 0 < n) ∧
    (∀ (p : Port) (o : Σ s : Tools.ShippingMachineDenote.SType, Tools.ShippingUnifiedSource.Term s), p ∈ m.outputs → o ∈ d.outs →
      m.outputs.length = 1 → d.outs.length = 1 → Tools.ShippingFGCircuitS3tComb.portW p = Tools.ShippingFGCircuitS3vBridge.sortW o.1) :=
  fun d m h => ⟨(portsOk_spec d m h).2.1, (portsOk_spec d m h).2.2⟩

/-- G2: a successful run of `certifiedEntryC` returns `(b, D)` such that the same run read some `d` (`readData`), the UNCHANGED entry `synthesizeCombinationalCoreOff` ran after that read and returned this `(b, D)`, the check is true on exactly that `d` and `(b, D)`, the design is `designOk`, and `DataShows d b` -/
example : ∀ (lvl : Lean.Expr → Nat) (declName : Lean.Name) (mctx : Lean.Meta.Context)
    (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State)
    (w : Void IO.RealWorld) (b : Module) (D : Design) (w' : Void IO.RealWorld),
    Tools.ShippingEntrySoundness.RunsTo (certifiedEntryC lvl declName) mctx mref cctx cref w (b, D) w' →
    ∃ (d : Tools.ShippingMachineAuto.MachineData) (w₁ w₂ : Void IO.RealWorld),
      Tools.ShippingEntrySoundness.RunsTo (readData lvl declName) mctx mref cctx cref w d w₁ ∧
      Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCoreOff declName)
        mctx mref cctx cref w₁ (b, D) w₂ ∧
      checkData d b = true ∧ designOk b D = true ∧
      ∀ x : Sparkle.Core.HList (Tools.ShippingMachineDenote.tys d.ss),
        Tools.ShippingMachineCompose.ChildFn b (Tools.ShippingMachineChild.childRange d) (dataValue d x) :=
  fun _ _ _ _ _ _ _ _ _ _ h => by
    obtain ⟨d, w₁, w₂, h1, h2, h3, h4, h5⟩ := certifiedEntryC_sound h
    exact ⟨d, w₁, w₂, h1, h2, h3, h4, h5⟩

/-- the checked entry's body, unfolded: read the data, run the unchanged entry, check the pair, return it -/
example (lvl : Lean.Expr → Nat) (declName : Lean.Name) : certifiedEntryC lvl declName =
    (do let d ← readData lvl declName
        let (b, D) ← Sparkle.Compiler.Elab.synthesizeCombinationalCoreOff declName
        unless checkData d b && designOk b D do throwError "certificate check failed"
        pure (b, D)) := rfl

/-- `k0_childFn` through the general theorem (the kernel fact `k0_checkData` plus the per-declaration tie) -/
example : Tools.ShippingMachineCompose.ChildFn pilotK0
    (Tools.ShippingMachineChild.childRange Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (Tools.ShippingMachineChild.childValue Sparkle.IP.Net.HTTP.httpGetByte.machineSource
      Sparkle.IP.Net.HTTP.httpGetByte.machineData.bsIn Sparkle.Core.Domain.defaultDomain) := k0_childFn'

example : checkData kd0 pilotK0 = true := k0_checkData

/-! ### (B) controls -/

/-- a changed constant, a dropped statement, swapped mux branches: the general check rejects -/
example : checkData kd0 (flipConst pilotK0) = false := by decide +kernel
example : checkData kd0 (dropFirst pilotK0) = false := by decide +kernel
example : checkData kd0 (dropLast pilotK0) = false := by decide +kernel
example : checkData kd0 (swapMux pilotK0) = false := by decide +kernel
/-- the other child's module under `httpGetByte`'s data, and `httpGetByte`'s module under the other child's data -/
example : checkData kd0 pilotK1 = false := by decide +kernel
example : checkData Sparkle.IP.Bus.PCIe.tlpCplByte.machineData pilotK0 = false := by decide +kernel
/-- a module with a `clk` input (the ports check) -/
example : checkData kd0 { pilotK0 with inputs := pilotK0.inputs ++ [{ name := "clk", ty := .bit }] } = false := by decide +kernel

/-- `DataShows` is not vacuous: the data's value at the argument 1 is 71, not 0 (kernel) -/
theorem dataValue_one : dataValue kd0 Sparkle.IP.Net.HTTP.httpGetByte.machineInits [1] = 71 := by decide +kernel
/-- a constant function is not what `pilotK0` computes on `httpGetByte`'s data -/
example : ¬ (∀ x : Sparkle.Core.HList (Tools.ShippingMachineDenote.tys kd0.ss),
    Tools.ShippingMachineCompose.ChildFn pilotK0 (Tools.ShippingMachineChild.childRange kd0) (fun _ => 0)) :=
  fun h => k0_not_zero (h Sparkle.IP.Net.HTTP.httpGetByte.machineInits)
/-- a mutated module (71 → 72) is not `DataShows` for the same data -/
theorem flip_not_dataShows : ¬ DataShows kd0 (flipConst pilotK0) := by
  intro h
  obtain ⟨outP, hout, h⟩ := h Sparkle.IP.Net.HTTP.httpGetByte.machineInits
  apply flip_not_childFn
  exact ⟨outP, hout, fun mems env hr hP => by
    obtain ⟨cres, he, hv⟩ := h mems env hr hP
    exact ⟨cres, he, by rw [hv, dataValue_k0]⟩⟩

/-- the guard: if the check is false whatever data was read, no successful run returns the pair -/
example : ∀ (lvl : Lean.Expr → Nat) (declName : Lean.Name) (mctx : Lean.Meta.Context)
    (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State)
    (w : Void IO.RealWorld) (b : Module) (D : Design) (w' : Void IO.RealWorld),
    (∀ d : Tools.ShippingMachineAuto.MachineData, checkData d b = false ∨ designOk b D = false) →
    ¬ Tools.ShippingEntrySoundness.RunsTo (certifiedEntryC lvl declName) mctx mref cctx cref w (b, D) w' :=
  fun _ _ _ _ _ _ _ _ _ _ h => certifiedEntryC_refuses h

/-- the guard, instantiated: a design whose top is not the module's name is refused whatever the data -/
example (lvl : Lean.Expr → Nat) (declName : Lean.Name) (mctx : Lean.Meta.Context)
    (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State)
    (w w' : Void IO.RealWorld) (D : Design) (hD : D.topModule ≠ pilotK0.name) :
    ¬ Tools.ShippingEntrySoundness.RunsTo (certifiedEntryC lvl declName) mctx mref cctx cref w (pilotK0, D) w' :=
  certifiedEntryC_refuses (fun _ => Or.inr (by
    unfold Tools.ShippingFGCircuitS3tSpec.designOk
    simp [hD]))

/-! ### (B2) the contract of the first fragment: rejections and vacuity (S3y2) -/

/-- `httpGetByte`'s input is one `BitVec 6` (and a domain), the output is a non-zero-width bits sort: the contract holds at the instance -/
example : kd0.bsIn.filter (fun b => b.2 != .domain) |>.map (·.2) = [.bits 6] := by decide +kernel
example : kd0.outs.map (fun o => Tools.ShippingFGCircuitS3vBridge.sortW o.1) = [8] := by decide +kernel
example : circOk kd0 = true := by decide +kernel
example : portsOk kd0 pilotK0 = true := by decide +kernel

/-- a data variant whose `BitVec 6` input is a `Bool` / a zero-width bits: refused (kernel) -/
def kdBool : Tools.ShippingMachineAuto.MachineData :=
  { kd0 with shape := { kd0.shape with binders := kd0.shape.binders.map fun b => if b.2 == .bits 6 then (b.1, .bool) else b } }
def kdW0 : Tools.ShippingMachineAuto.MachineData :=
  { kd0 with shape := { kd0.shape with binders := kd0.shape.binders.map fun b => if b.2 == .bits 6 then (b.1, .bits 0) else b } }
example : portsOk kdBool pilotK0 = false := by decide +kernel
example : portsOk kdW0 pilotK0 = false := by decide +kernel
example : checkData kdBool pilotK0 = false := by decide +kernel
example : checkData kdW0 pilotK0 = false := by decide +kernel
/-- one more input port than the data has (count), a `clk` port is refused above; an input of the wrong width (width/order) -/
example : portsOk kd0 { pilotK0 with inputs := pilotK0.inputs ++ [{ name := "extra", ty := .bit }] } = false := by decide +kernel
example : portsOk kd0 { pilotK0 with inputs := pilotK0.inputs.map fun p => { p with ty := .bitVector 7 } } = false := by decide +kernel
/-- two output ports (single-output limit); the output port's width differs from the output sort's -/
example : portsOk kd0 { pilotK0 with outputs := pilotK0.outputs ++ pilotK0.outputs } = false := by decide +kernel
example : portsOk kd0 { pilotK0 with outputs := pilotK0.outputs.map fun p => { p with ty := .bitVector 9 } } = false := by decide +kernel
example : checkData kd0 { pilotK0 with outputs := pilotK0.outputs.map fun p => { p with ty := .bitVector 9 } } = false := by decide +kernel
/-- an EMPTY output list, TWO outputs (single-output limit of `ChildFn`/`dataValue`), a ZERO-width output: refused on the data side -/
example : circOk { kd0 with outs := [] } = false := by decide +kernel
example : checkData { kd0 with outs := [] } pilotK0 = false := by decide +kernel
example : circOk { kd0 with outs := kd0.outs ++ kd0.outs } = false := by decide +kernel
example : circOk { kd0 with outs := [⟨.bits 0, .bitsLit 0 0⟩] } = false := by decide +kernel
example : checkData { kd0 with outs := [⟨.bits 0, .bitsLit 0 0⟩] } pilotK0 = false := by decide +kernel
/-- state is refused (the fragment is stateless) -/
example : circOk { kd0 with ss := [.bool] } = false := by decide +kernel

/-- vacuity 1: the argument range is NEVER empty, for any data: at least the all-zero list is in range; for `kd0` also the list `[1]` and the list `[0]` -/
example : ∀ d : Tools.ShippingMachineAuto.MachineData, ∃ vals, Tools.ShippingMachineChild.childRange d vals := childRange_nonempty
example : Tools.ShippingMachineChild.childRange kd0 [1] := k0_range_one
/-- vacuity 2: the output list is non-empty, single, of non-zero width -/
example : ∀ (d : Tools.ShippingMachineAuto.MachineData) (m : Module), checkData d m = true → d.outs ≠ [] := by
  intro d m h
  obtain ⟨⟨o, ho, -⟩, -, -⟩ := checkData_contract d m h
  simp [ho]
/-- vacuity 3: a WRONG value function is not satisfied.  Any function satisfying `ChildFn pilotK0 (childRange kd0)` takes the value 71 at `[1]`, so every function with another value there fails; and `DataShows kd0 pilotK0` holds for the data's own value, not for the value + 1 -/
theorem wrong_value_fails (f : List Nat → Nat) (hf : f [1] ≠ 71) :
    ¬ Tools.ShippingMachineCompose.ChildFn pilotK0 (Tools.ShippingMachineChild.childRange kd0) f := by
  intro h
  have := Tools.ShippingFGCircuitS3vChild.childFn_eval1 pilotK0 rfl f h
  rw [Tools.ShippingFGCircuitS3vChild.k0_eval1] at this
  exact hf (Option.some.inj this).symm
theorem dataShows_k0 : DataShows kd0 pilotK0 := checkData_sound kd0 pilotK0 k0_checkData
theorem dataShows_k0_succ_fails :
    ¬ (∀ x : Sparkle.Core.HList (Tools.ShippingMachineDenote.tys kd0.ss),
      Tools.ShippingMachineCompose.ChildFn pilotK0 (Tools.ShippingMachineChild.childRange kd0) (fun vs => dataValue kd0 x vs + 1)) := by
  intro h
  exact wrong_value_fails _ (by rw [show (fun vs => dataValue kd0 Sparkle.IP.Net.HTTP.httpGetByte.machineInits vs + 1) [1] = 72 by
      show dataValue kd0 Sparkle.IP.Net.HTTP.httpGetByte.machineInits [1] + 1 = 72
      rw [dataValue_one]]; decide) (h Sparkle.IP.Net.HTTP.httpGetByte.machineInits)

/-- a failed `readData` gives no successful run of `certifiedEntryC` -/
example : ∀ (lvl : Lean.Expr → Nat) (declName : Lean.Name) (mctx : Lean.Meta.Context)
    (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State)
    (w : Void IO.RealWorld),
    (∀ (d : Tools.ShippingMachineAuto.MachineData) (w₁ : Void IO.RealWorld),
      ¬ Tools.ShippingEntrySoundness.RunsTo (readData lvl declName) mctx mref cctx cref w d w₁) →
    ∀ (r : Module × Design) (w' : Void IO.RealWorld),
      ¬ Tools.ShippingEntrySoundness.RunsTo (certifiedEntryC lvl declName) mctx mref cctx cref w r w' :=
  fun _ _ _ _ _ _ _ _ h => certifiedEntryC_no_read h

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
  let pre : List Name := [`Tools.ShippingFGCircuitS3yGen, `Tools.ShippingFGCircuitS3yEntry, `Tests.Gen5.FGCircuitPilotCheck60]
  let thms := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    match ci with
    | .thmInfo _ => if pre.any (·.isPrefixOf n) then acc.push n else acc
    | _ => acc
  let mut axs : NameSet := {}
  for nm in thms do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  let a1 ← Lean.collectAxioms `Tools.ShippingFGCircuitS3yGen.checkData_sound
  let a2 ← Lean.collectAxioms `Tools.ShippingFGCircuitS3yEntry.certifiedEntryC_sound
  logInfo m!"FGCIRCUIT60 AXIOMS: {thms.size} theorems of the S3y modules (Gen, Entry, this Check), standard axioms only ({axs.toList}); checkData_sound depends on {a1.toList}; certifiedEntryC_sound depends on {a2.toList}; no sorryAx, no Lean.ofReduceBool (no native_decide)"
  let sz (n : Name) : MetaM Nat := do
    match (← getConstInfo n) with
    | .thmInfo i => pure i.value.sizeWithoutSharing
    | .defnInfo i => pure i.value.sizeWithoutSharing
    | _ => pure 0
  let sizes ← [`Tools.ShippingFGCircuitS3yGen.portsOk_spec, `Tools.ShippingFGCircuitS3yGen.checkData_sound,
    `Tools.ShippingFGCircuitS3yGen.k0_childFn', `Tools.ShippingFGCircuitS3yEntry.certifiedEntryC_sound,
    `Tools.ShippingFGCircuitS3yEntry.certifiedEntryC_refuses, `Tools.ShippingFGCircuitS3yEntry.certifiedEntryC_no_read,
    `Tools.ShippingFGCircuitS3yGen.circOk_spec, `Tools.ShippingFGCircuitS3yGen.checkData_contract].mapM fun n => do pure (n, ← sz n)
  let t1 ← retime (← `(Tools.ShippingFGCircuitS3yGen.checkData Tools.ShippingFGCircuitS3vChild.kd0 Tools.ShippingFGCircuitS3rArtifact.pilotK0 = true))
  logInfo m!"FGCIRCUIT60 SIZE/TIME (ONE run, this machine; not a bound): term sizes without sharing {sizes}; a fresh `decide +kernel` of `checkData kd0 pilotK0 = true` took {t1} ms (elaboration + kernel)"
  logInfo m!"FGCIRCUIT60 SIGNATURES: checkData_sound (G1, complete type, dataValue unfolded), checkData / circOk unfolded, certifiedEntryC_sound (G2) and the entry body, k0_childFn' through G1: all ascribed to independently written types (a mismatch is a compile error)"
  logInfo m!"FGCIRCUIT60 CONTROLS: 7 rejections by the general check (changed constant, dropped first statement, dropped output statement, swapped mux, the other child's module, the other child's data, a clk input) by the kernel; DataShows non-vacuous (data value 71 at argument 1, a constant function fails, the mutated module is not DataShows); the guard (a false check admits no successful run), plus its instance for a wrong design top"
  logInfo m!"FGCIRCUIT60 SCOPE: the combinational sub-language (no state, one output, Frag), general in the data and the module; ONE closed child (pilotK0 = httpGetByte) as the instance; the entry is a different entry from synthesizeCombinational (old-entry proofs not counted); DeclDenotes (the d read is the declaration's data), registers, instances, the top operators, optimisation and SV are NOT covered; required-IP baseline NOT measured here; ledger unchanged"
  logInfo m!"FGCIRCUIT60 CONTRACT: first fragment = one output of non-zero width (ChildFn/dataValue are single-output; multi-output IPs are later work), inputs only BitVec n with 0 < n (Bool and zero-width refused), port count/order/width and the output port width checked; 16 kernel rejections (Bool input, zero-width input, extra port, wrong input width, two output ports, wrong output width x2, no output x2, two outputs, zero-width output x2, state, ...); vacuity: childRange d is non-empty for every d (all-zero list), the output list of a passing check is non-empty, a wrong value function is not ChildFn pilotK0; read failure gives no run (certifiedEntryC_no_read); G2 takes the run's success as its premise"

end Tests.Gen5.FGCircuitPilotCheck60
