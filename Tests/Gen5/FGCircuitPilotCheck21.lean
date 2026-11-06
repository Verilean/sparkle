import Tools.ShippingFGCircuitS2cLink
set_option autoImplicit false
-- FG circuit pilot S2c check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §31.

/-! # FGCircuitPilotCheck21 (light)

1. SIGNATURES21: the complete types of the chain endpoint's new per-call facts `machine_arg_0`, `machine_arg_1` of `synth_hftPcieOutByte`, against independently written statements (`isDefEq`, default transparency); each mutant (another call, a missing earlier-call extension, a dropped argument). `machine_states`'s type is stated in docs §31.1 and checked by its generation; an `isDefEq` against an independent text exceeded the heartbeat limit (docs §31.5), so it is not compared here. is rejected at `instances` transparency (an unfolding of the data would be needed to identify them).
2. AXIOMS21 (the link itself is NOT proved in this bundle: docs §31.5). -/
namespace Tests.Gen5.FGCircuitPilotCheck21
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineTeleStates Tools.ShippingMachineFuse
open Tools.ShippingMachineNest (happendT castSS)
open Tools.ShippingUnifiedSource (SType eval)
open Tools.ShippingFGCircuitS1kRoot

/-! ## 1. expected statements, written independently -/

abbrev Sg := Signal defaultDomain
noncomputable abbrev Lc := synth_hftPcieOutByte.machineInners
noncomputable abbrev Dc : MachineData := synth_hftPcieOutByte.machineData
abbrev T10 : List SType := [SType.bits 32, SType.bits 32, SType.bits 32, SType.bits 32, SType.bits 5, SType.bits 16,
  SType.bits 8, SType.bits 8, SType.bits 32, SType.bool]

/-- `machine_arg_0`; knob `kk`: the call whose argument wires are read -/
noncomputable def ExpArg0 (kk : Nat) : Prop :=
  ∀ (i : Unit) (bools : Nat → Sg Bool) (bits : Nat → (n : Nat) → Sg (BitVec n)) (S : Sg (HList (tys [SType.bits 6])))
    (Ss : (Lc.at i bools bits).Sigs) (t : Nat),
    callArgVals Dc bools bits t (teleState Lc rfl i bools bits S Ss t) (callArgsOf Dc kk) =
      [((regsOf (tys [SType.bits 6]) S).fst.fst.val t).toNat]

/-- `machine_arg_1`; knob `pre`: the extension of the earlier call is present; `drop`: the last argument is dropped -/
noncomputable def ExpArg1 (pre drop : Bool) : Prop :=
  ∀ (i : Unit) (bools : Nat → Sg Bool) (bits : Nat → (n : Nat) → Sg (BitVec n)) (S : Sg (HList (tys [SType.bits 6])))
    (Ss : (Lc.at i bools bits).Sigs) (t : Nat),
    callArgVals Dc bools (if pre then extendBits bits 5 8 (synth_hftPcieOutByte.machineCall_0 i bools bits S Ss) else bits) t
      (teleState Lc rfl i bools bits S Ss t) (callArgsOf Dc 1) =
      ([((bits 4 16).val t).toNat,
        ((regsOf (tys T10) Ss.2.1).snd.snd.snd.snd.snd.fst.fst.val t).toNat,
        ((regsOf (tys T10) Ss.2.1).snd.snd.snd.snd.snd.snd.fst.fst.val t).toNat,
        ((regsOf (tys T10) Ss.2.1).snd.snd.snd.snd.snd.snd.snd.fst.fst.val t).toNat,
        ((regsOf (tys T10) Ss.2.1).snd.snd.snd.snd.snd.snd.snd.snd.fst.fst.val t).toNat,
        ((regsOf (tys T10) Ss.2.1).snd.snd.snd.snd.fst.fst.val t).toNat].take (if drop then 5 else 6))

/-- `machine_states`; knobs: `useExt` (the Lean extension, not the plain inputs), `withInit` (the initial-state clause) -/
noncomputable def ExpStates (useExt withInit : Bool) : Prop :=
  ∀ (i : Unit) (bools : Nat → Sg Bool) (bits : Nat → (n : Nat) → Sg (BitVec n)),
    ∃ (S₂ : Sg (HList (tys [SType.bits 6]))) (Ss : (Lc.at i bools bits).Sigs),
      (if withInit then teleState Lc rfl i bools bits S₂ Ss 0 = castSS (b := Dc.ss) rfl (happendT [SType.bits 6] Lc.sss synth_hftPcieOutByte.machineInits Lc.initsT) else True) ∧
      (∀ t, teleState Lc rfl i bools bits S₂ Ss (t + 1) = evalTerms
        (fun j => (typedVal Dc.nIn Dc.bpos Dc.vpos Dc.ss Dc.ls bools
          (if useExt then synth_hftPcieOutByte.machineExt i bools bits S₂ Ss else bits) t (teleState Lc rfl i bools bits S₂ Ss t)).b (Dc.bpos j))
        (fun j w => (typedVal Dc.nIn Dc.bpos Dc.vpos Dc.ss Dc.ls bools
          (if useExt then synth_hftPcieOutByte.machineExt i bools bits S₂ Ss else bits) t (teleState Lc rfl i bools bits S₂ Ss t)).v (Dc.vpos j) w) Dc.nexts) ∧
      ∀ t, (synth_hftPcieOutByte.machineSource i bools bits).map (fun f => f t) = Dc.outs.map fun o => enc o.1 (eval
        (fun k => (typedVal Dc.nIn Dc.bpos Dc.vpos Dc.ss Dc.ls bools
          (if useExt then synth_hftPcieOutByte.machineExt i bools bits S₂ Ss else bits) t (teleState Lc rfl i bools bits S₂ Ss t)).b (Dc.bpos k))
        (fun k w => (typedVal Dc.nIn Dc.bpos Dc.vpos Dc.ss Dc.ls bools
          (if useExt then synth_hftPcieOutByte.machineExt i bools bits S₂ Ss else bits) t (teleState Lc rfl i bools bits S₂ Ss t)).v (Dc.vpos k) w) o.2)

/-- unfold the expected statement's definition and its `if` on a literal `Bool`, so that `isDefEq` compares statements -/
def mkE (n : Name) (args : List Bool) (nat : Option Nat := none) : MetaM Lean.Expr := do
  let mut e := Lean.mkConst n
  if let some k := nat then e := mkApp e (mkNatLit k)
  for b in args do e := mkApp e (toExpr b)
  pure e

def sameType (thm : Name) (exp : Lean.Expr) (tr : TransparencyMode := .default) : MetaM Bool := do
  let some ci := (← getEnv).find? thm | throwError "{thm} missing"
  Meta.withTransparency tr <| Meta.isDefEq ci.type (← do let u ← Meta.unfoldDefinition? exp; pure (u.getD exp))

run_cmd liftTermElabM do
  let p := `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte
  let mut ok := true
  let mut rej : Nat := 0
  let mut tot : Nat := 0
  -- the real statements
  for (nm, e) in [(p ++ `machine_arg_0, ← mkE ``ExpArg0 [] (some 0)), (p ++ `machine_arg_1, ← mkE ``ExpArg1 [true, false])] do
    let b ← sameType nm e
    logInfo m!"FGCIRCUIT21 SIGNATURES {nm}: defeq expected = {b}"
    ok := ok && b
  -- the mutants must be rejected
  for (nm, e) in [(p ++ `machine_arg_0, ← mkE ``ExpArg0 [] (some 1)),
      (p ++ `machine_arg_1, ← mkE ``ExpArg1 [false, false]), (p ++ `machine_arg_1, ← mkE ``ExpArg1 [true, true])] do
    let b ← sameType nm e .instances
    tot := tot + 1
    if !b then rej := rej + 1
  logInfo m!"FGCIRCUIT21 SIGNATURES mutants rejected {rej} / {tot}; real statements all defeq: {ok}"
  unless ok && rej == tot do throwError "FGCIRCUIT21 SIGNATURES failed"

/-! ## 4. axioms -/

open Lean Elab Command in
run_cmd liftTermElabM do
  let mut bad : List Name := []
  let mut n : Nat := 0
  for nm in [`Tools.ShippingFGCircuitS2cLink.partial_tagree, `Tools.ShippingFGCircuitS2cLink.typedVal_tagree, `Tools.ShippingFGCircuitS2cLink.callArgVals_tagree, `Tools.ShippingFGCircuitS2cLink.kid_pw,
      `Tools.ShippingFGCircuitS2cLink.stage1, `Tools.ShippingFGCircuitS2cLink.stage2, `Tools.ShippingFGCircuitS2cLink.http_pw,
      `Tools.ShippingFGCircuitS2cLink.tlp_pw, `Tools.ShippingMachineTeleStates.machine_states_of_tele_ext,
      `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte.machine_arg_0, `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte.machine_arg_1,
      `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte.machine_states] do
    n := n + 1
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do bad := ax :: bad
  logInfo m!"FGCIRCUIT21 AXIOMS: {n} names, non-standard axioms: {bad}"
  unless bad.isEmpty do throwError "FGCIRCUIT21 AXIOMS failed"

end Tests.Gen5.FGCircuitPilotCheck21
