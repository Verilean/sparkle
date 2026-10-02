import Tests.Compiler.ShippingMachineEntryTest
import Tools.ShippingMachineCommand
import IP.Crypto.EcdsaSignDemo
import IP.Crypto.P256SignDemo
import IP.USB.Fido2Demo

/-! The machine endpoint, generated.

`#machine_endpoint f` reads the typed terms off the transition of `f`,
adds the data and six kernel-checked `Eq.refl`s, and concludes
`f.machine_sound`: a run of the real synthesis entry on `f` at the machine
boundary returns a module that shows, on every output port and at every
cycle, the SOURCE declaration `f` (`Tools.ShippingMachineAuto.MachineTrace`).

* The declarations of `ShippingMachineEntryTest`, whose endpoints were
  written by hand (`mThree`, the LIN checksum), are generated here by one
  line each — and so are the others, which had none.
* IP declarations themselves: the LIN checksum module, and the tagged
  sub-modules of the ECDSA / P-256 / FIDO2 demos (structure results, five
  slots, two dozen hardware `let`s).
* `checksumHW_ports` unfolds `MachineTrace` for the LIN checksum module into
  the statement `linHW_execution` makes, port by port.
* A declaration that is not a machine is refused, and nothing is added.
* `f.machine_ships` (the optimized module and its emitted Verilog show the
  source) is generated too, and its gates are evaluated on the real modules
  of every declaration here. -/
namespace Sparkle.Tests.Compiler.ShippingMachineCommandTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tools.ShippingEntrySoundness Tools.ShippingMixedEntrySoundness
open Tools.ShippingMixedSourceBridge Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Sparkle.Tests.Compiler.ShippingMachineEntryTest

/-! ## Declarations of this file -/

/-- A concrete domain (synchronous reset), a Bool slot and a Bool result. -/
def toggle (en : Signal defaultDomain Bool) : Signal defaultDomain Bool :=
  circuit do
    let t ← Signal.reg false
    let ts := (t : Signal defaultDomain Bool)
    t <~ Signal.mux en (~~~ts) ts
    return ts

/-- Not a machine: a combinational declaration. -/
def plain {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := a + b

/-! ## The endpoints -/

#machine_endpoint mThree
#machine_endpoint twoHW
#machine_endpoint twoFlag
#machine_endpoint twoCnt
#machine_endpoint linChk
#machine_endpoint linChkDefault
#machine_endpoint toggle
#machine_endpoint Sparkle.IP.Bus.LINHW.checksumHW
#machine_endpoint Sparkle.IP.Crypto.EcdsaSignDemo.wMulN
#machine_endpoint Sparkle.IP.Crypto.EcdsaSignDemo.wTx
#machine_endpoint Sparkle.IP.Crypto.P256SignDemo.wMul
#machine_endpoint Sparkle.IP.Crypto.P256SignDemo.wMulN
#machine_endpoint Sparkle.IP.USB.Fido2Demo.wTx

-- A declaration that is not a machine is refused, and nothing is added.
run_cmd liftTermElabM do
  let refused ← try
      let _ ← Tools.ShippingMachineCommand.generate ``plain
      pure false
    catch _ => pure true
  unless refused do throwError "a combinational declaration got a machine endpoint"
  if (← getEnv).contains (``plain ++ `machineData) then
    throwError "a refused declaration left data behind"

/-! ## What the generated statement says, port by port -/

/-- **The generated endpoint of the LIN checksum module, unfolded.** The
statement `linHW_execution` makes — one register, the ports `acc` and `chk`
showing the two fields of the SOURCE declaration at every cycle — from
`checksumHW.machine_sound`. -/
theorem checksumHW_ports {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``Sparkle.IP.Bus.LINHW.checksumHW [] false)
      mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Sparkle.IP.Bus.LINHW.checksumHW
      Sparkle.IP.Bus.LINHW.checksumHW.machineData.shape)
    (closes : MachineCloses mctx mref cctx cref ``Sparkle.IP.Bus.LINHW.checksumHW
      Sparkle.IP.Bus.LINHW.checksumHW.machineData.shape) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = 23 ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (racc : String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ t st, t < T → SourceInputs ``Sparkle.IP.Bus.LINHW.checksumHW
          Sparkle.IP.Bus.LINHW.checksumHW.machineData.bsIn ids cache
          (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
          (seed t st)) →
        (∀ t st, seed t st racc = st racc) →
        (∀ t st, seed t st "rst" = 0) →
        st0 racc = 0 →
        ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
          ∀ j (hj : j < envs.length),
            (envs[j]'hj) "acc" = ((Sparkle.IP.Bus.LINHW.checksumHW (bools 1) (bits 2 8)
              (bools 3)).acc.val j).toNat ∧
            (envs[j]'hj) "chk" = ((Sparkle.IP.Bus.LINHW.checksumHW (bools 1) (bits 2 8)
              (bools 3)).chk.val j).toNat := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, h⟩ :=
    Sparkle.IP.Bus.LINHW.checksumHW.machine_sound hr entry closes
  have rlen' : regs.length = 1 := rlen
  match regs, rlen', rnd, h with
  | [racc], _, _, h =>
  refine ⟨ids, nd, len, cache, racc, ?_⟩
  intro D bools bits T seed st0 mems inputs pass rst ia
  obtain ⟨envs, hrun, hlen, hobs⟩ := h D bools bits T seed st0 mems inputs
    (by
      intro t st r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact pass t st)
    rst
    (by
      intro k r f hr hf
      have hk : k = 0 := by
        have := (List.getElem?_eq_some_iff.mp hr).1
        simpa using this
      subst hk
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      have slot0 : Sparkle.IP.Bus.LINHW.checksumHW.machineData.shape.layout.slots[0]? =
          some { lo := 0, width := 8, init := 0 } := rfl
      rw [slot0] at hf
      cases hf
      exact ia)
  exact ⟨envs, hrun, hlen, fun j hj => ⟨hobs j hj 0 _ _ rfl rfl, hobs j hj 1 _ _ rfl rfl⟩⟩

/-! ## To the emitted Verilog

`f.machine_ships` carries the endpoint across the merge, the optimizer and
the printer, under gates that are decidable facts about the modules of the
run. The gates are evaluated here on the real modules of every declaration
above: the core module, the module the full entry returns, and the module
the printer is given (`checkedOptimize`). -/

run_cmd liftTermElabM do
  let env ← getEnv
  let senv := structEnv env
  for n in [``mThree, ``twoHW, ``twoFlag, ``twoCnt, ``linChk, ``linChkDefault, ``toggle,
      ``Sparkle.IP.Bus.LINHW.checksumHW, ``Sparkle.IP.Crypto.EcdsaSignDemo.wMulN,
      ``Sparkle.IP.Crypto.EcdsaSignDemo.wTx, ``Sparkle.IP.Crypto.P256SignDemo.wMul,
      ``Sparkle.IP.Crypto.P256SignDemo.wMulN, ``Sparkle.IP.USB.Fido2Demo.wTx] do
    unless (← getEnv).contains (n ++ `machine_ships) do
      throwError "{n}: no machine_ships"
    let ci ← getConstInfo n
    let entry := entryConst true false [] ci (instancePredicate env) (userInliner env) senv
    let some shape := machineShape? false [] entry senv | throwError "{n}: not a machine"
    let (raw, _) ← synthesizeCombinationalCore n [] false
    let (b, _) ← synthesizeCombinational n
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let wof := Tools.SVParser.RoundtripProof.moduleWof o
    let oo := Sparkle.IR.Optimize.optimizeModule b
    unless o.body == oo.body && o.wires == oo.wires && o.inputs == oo.inputs &&
        o.outputs == oo.outputs do
      throwError "{n}: the printer is not given the optimizer's output"
    unless Sparkle.IR.RefineCheck.refineCheck raw b do
      throwError "{n}: refineCheck rejects the cleanup/merge step"
    unless Sparkle.IR.RefineCheck.refineCheck b o do
      throwError "{n}: refineCheck rejects the optimizer's output"
    unless (raw.inputs.map (·.name)).contains "rst" do throwError "{n}: no reset port"
    unless shape.layout.outs.all (fun q => raw.outputs.any (·.name == q.name)) do
      throwError "{n}: an output port is missing"
    unless Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body do
      throwError "{n}: the emitted-Verilog check rejects the optimized module"
    unless (Tools.ShippingSeqSVSoundness.seqNames o.body).all (fun x =>
        Sparkle.IR.RegDedup.declWidth o x == Tools.SVParser.EmitSem.weOf wof x) do
      throwError "{n}: checker and emitter widths disagree"
  logInfo m!"MACHINE SHIPPING GATES: the merge and the optimizer are accepted by refineCheck, and the emitted-Verilog check passes, on all thirteen declarations"

/-! ## Axioms -/

run_cmd do
  if (← get).messages.hasErrors then throwError "machine command regression failed"
  for name in [``checksumHW_ports, ``Tools.ShippingMachineAuto.machine_trace_of_data,
      ``Tools.ShippingMachineDenote.machine_endpoint,
      ``Tools.ShippingRefineSoundness.refineCheck_transfer,
      ``Tools.ShippingRefineSoundness.rNormE_sound,
      ``Tools.ShippingRefineSoundness.rSlice_sound,
      ``Tools.ShippingMachineShipping.machine_ships,
      ``Tools.ShippingMachineShipping.machine_ships_full,
      ``Sparkle.IP.Bus.LINHW.checksumHW.machine_ships,
      ``Sparkle.IP.Crypto.EcdsaSignDemo.wMulN.machine_ships,
      ``mThree.machine_ships, ``toggle.machine_ships,
      ``Sparkle.IP.Bus.LINHW.checksumHW.machine_sound,
      ``Sparkle.IP.Crypto.EcdsaSignDemo.wMulN.machine_sound,
      ``Sparkle.IP.Crypto.EcdsaSignDemo.wTx.machine_sound,
      ``Sparkle.IP.Crypto.P256SignDemo.wMul.machine_sound,
      ``Sparkle.IP.Crypto.P256SignDemo.wMulN.machine_sound,
      ``Sparkle.IP.USB.Fido2Demo.wTx.machine_sound,
      ``mThree.machine_sound, ``twoHW.machine_sound, ``twoFlag.machine_sound,
      ``twoCnt.machine_sound, ``linChk.machine_sound, ``linChkDefault.machine_sound,
      ``toggle.machine_sound] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"MACHINE COMMAND: endpoints generated and checked by the kernel; standard axioms only"

end Sparkle.Tests.Compiler.ShippingMachineCommandTest
