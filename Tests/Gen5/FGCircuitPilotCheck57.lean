import Tools.ShippingFGCircuitS3tCert
import Tools.ShippingFGCircuitS3tCalls
import Tools.ShippingFGCircuitS3tCombRun
set_option autoImplicit false
-- FG circuit pilot Check57 (S3t): (A) COMPLETE-TYPE SIGNATURES of the freeze definitions (`SourceData`, `SrcEq`, `RootShowsAt`, `CheckRoot`, the statement of `checkRoot_sound`, `certifiedReturn`, its statement) and of `checkComb`/`checkComb_sound`, against INDEPENDENTLY WRITTEN expected types (type ascriptions and `Iff.rfl` between two spellings; a mismatch is a compile error); (B) negative controls (kernel-checked theorems of the Cert and CombRun modules, their types restated here); (C) the simultaneous-satisfaction example (`rootS.ok`, `rootS.SrcEq`, the four seed premises at the artifact's registers); (D) kernel time and sizes (ONE run); (E) AXIOMS (every theorem of the S3t modules: standard only).  `CheckRoot` is false for every input today (`bodyOk` is not written): this Check does not claim a validated root.  S3u: RootShowsAt/structuralOk now bind the Design's top and the top inputs' types/widths.  docs/FG-CIRCUIT-PILOT.md §69.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck57
open Sparkle.IR.AST Tools.ShippingFGCircuitS3tSpec Tools.ShippingFGCircuitS3rArtifact
open Sparkle.IR.Semantics (Env MEnv evalAssigns)

/-! ### (A) signatures, against independently written expected types -/

example : SourceData → Bool := SourceData.ok
example : SourceData → Prop := SourceData.SrcEq
example : SourceData → Prop := SourceData.SrcCore
example : SourceData → Prop := SourceData.CallsEq
example : SourceData → Module → Design → Prop := RootShowsAt
example : SourceData → Module → Design → Cert → Bool := CheckRoot
example : SourceData → Module → Design → Cert → Bool := structuralOk
example : Prop := CheckRootSoundStmt
example : SourceData → (Module → Design → Cert) → Lean.Name → Lean.MetaM (Module × Design) := certifiedReturn
example : Prop := CertifiedReturnSoundStmt
noncomputable example : SourceData := rootS
example : Cert := Tools.ShippingFGCircuitS3tCert.cert0
example : Cert := ⟨[173, 238], Tools.ShippingFGCircuitS3tCert.cert0.regs⟩

/-- the fields of `SourceData`, in order, with their types -/
example : Lean.Name → Tools.ShippingMachineAuto.MachineData →
    ((Nat → Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain Bool) →
      ((j n : Nat) → Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain (BitVec n)) → List (Nat → Nat)) →
    List String → List String → List (List Nat) → List (List Nat) → Nat → SourceData := SourceData.mk

/-- `Cert`'s fields -/
example : List Nat → List String → Cert := Cert.mk

/-- the statement of `checkRoot_sound`, spelled again -/
example : CheckRootSoundStmt ↔ ∀ (S : SourceData) (b : Module) (D : Design) (cert : Cert),
    S.ok = true → S.SrcEq → CheckRoot S b D cert = true → RootShowsAt S b D := Iff.rfl

/-- `CheckRoot` is the structural part and the body part -/
example : ∀ (S : SourceData) (b : Module) (D : Design) (cert : Cert),
    CheckRoot S b D cert = (structuralOk S b D cert && bodyOk S b D cert) := fun _ _ _ _ => rfl

/-- the body validator is not written: it is false, so `CheckRoot` is false for every input -/
example : ∀ (S : SourceData) (b : Module) (D : Design) (cert : Cert), bodyOk S b D cert = false := fun _ _ _ _ => rfl

/-- `SrcEq` is `SrcCore` and `CallsEq` (no IR, no allocator names) -/
example : ∀ S : SourceData, S.SrcEq ↔ (S.SrcCore ∧ S.CallsEq) := fun _ => Iff.rfl

/-- `certifiedReturn`'s statement, spelled again -/
example : CertifiedReturnSoundStmt ↔ ∀ (S : SourceData) (mk : Module → Design → Cert) (declName : Lean.Name)
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld} {b : Module} {D : Design},
    Tools.ShippingEntrySoundness.RunsTo (certifiedReturn S mk declName) mctx mref cctx cref w (b, D) w' →
    ∃ cert, CheckRoot S b D cert = true := Iff.rfl

/-- **`RootShowsAt`, written again from the design text** (docs §67.3, §69.1): the instance fields are empty and there are two calls; the top module's own inputs carry the claimed names, `clk` and `rst` are inputs, the outputs are the layout's, the body is in the linked order; and there are register names such that: distinct, one per slot, among the claimed names' register range, register `k` is a clocked register statement with slot `k`'s width and init and is not an input, every register statement is one of those; every call `k < 2` has its statement in the body, the `CallStmt` shape, its module is what its name resolves to in the design, and the module computes the child's source function on the child's range (`ChildFn`, a CONJUNCT); every instance statement of the body is one of the two calls with the same conclusions; and for every inputs, state witnesses, run length, seed, initial state and memories under the four premises, the linked run succeeds with `T` environments and every output is the source's. -/
def ExpectedRootShowsAt (S : SourceData) (b : Module) (D : Design) : Prop :=
  S.d.shape.instFields = [] ∧ List.length S.d.shape.insts = 2 ∧
  D.topModule = b.name ∧ List.Nodup (List.map (fun m => m.name) D.modules) ∧ (∀ m, m ∈ D.modules → m.name ≠ b.name) ∧
  b.inputs = List.map (fun (x : String × Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder) =>
      ({ name := x.1, ty := match x.2.2 with
          | .bits n => Sparkle.IR.Type.HWType.bitVector n
          | .bool => Sparkle.IR.Type.HWType.bit
          | .domain => Sparkle.IR.Type.HWType.bitVector 0 } : Port))
      (List.zip (List.take S.kD S.portNames) (List.take S.kD S.d.bsIn)) ++
    [({ name := "clk", ty := Sparkle.IR.Type.HWType.bit } : Port), ({ name := "rst", ty := Sparkle.IR.Type.HWType.bit } : Port)] ∧
  (∀ (n : String) (w : Nat), (n, w) ∈ List.map (fun (x : String × Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder) =>
      (x.1, match x.2.2 with | .bits n => n | .bool => 1 | .domain => 0))
      (List.zip (List.take S.kD S.portNames) (List.take S.kD S.d.bsIn)) → Sparkle.IR.RegDedup.declWidth b n = w) ∧
  b.outputs = List.map (fun o => ({ name := o.name, ty := o.ty } : Port)) S.d.shape.layout.outs ∧
  Sparkle.IR.Machine.linkedOk (Sparkle.IR.Machine.moduleByName D.modules) b.body = true ∧
  ∃ (regs : List String),
    List.Nodup regs ∧ List.length regs = List.length S.d.ss ∧
    (∀ r, r ∈ regs → r ∈ List.drop (List.length S.portNames - S.d.shape.layout.lets - List.length S.d.shape.layout.slots) S.portNames) ∧
    (∀ (k : Nat) (r : String) (f : Sparkle.IR.Machine.SlotField), regs[k]? = some r → S.d.shape.layout.slots[k]? = some f →
      Tools.ShippingEntrySoundness.weOf b r = f.width ∧ r ∉ List.map (fun p => p.name) b.inputs ∧
      ∃ (rk : Sparkle.IR.Type.ResetKind) (inp : Expr), Stmt.register r "clk" ("rst", rk) inp (Int.ofNat f.init) ∈ b.body) ∧
    (∀ (r c : String) (rs : String × Sparkle.IR.Type.ResetKind) (inp : Expr) (init : Int),
      Stmt.register r c rs inp init ∈ b.body →
      ∃ (k : Nat) (f : Sparkle.IR.Machine.SlotField), regs[k]? = some r ∧ S.d.shape.layout.slots[k]? = some f ∧
        init = Int.ofNat f.init) ∧
    (∀ k, k < 2 → ∃ (args : List Nat) (mc : Module) (st : Stmt) (kd : Tools.ShippingMachineAuto.MachineData) (f : List Nat → Nat),
      (List.map (fun x => x.2.1) S.d.shape.insts)[k]? = some args ∧ st ∈ b.body ∧
      Tools.ShippingMachineInst.CallStmt (Tools.ShippingMachineEntry.machNIn S.d.shape) (List.length S.d.shape.insts)
        (List.length S.d.shape.layout.slots) S.portNames k args mc st ∧
      Sparkle.IR.Machine.moduleByName D.modules mc.name = some mc ∧ kidData[k]? = some kd ∧ kidFs[k]? = some f ∧
      Tools.ShippingMachineCompose.ChildFn mc (Tools.ShippingMachineChild.childRange kd) f) ∧
    (∀ (mn iname : String) (conns : List (String × Expr)), Stmt.inst mn iname conns ∈ b.body →
      ∃ (k : Nat) (args : List Nat) (mc : Module) (kd : Tools.ShippingMachineAuto.MachineData) (f : List Nat → Nat), k < 2 ∧
        (List.map (fun x => x.2.1) S.d.shape.insts)[k]? = some args ∧
        Sparkle.IR.Machine.moduleByName D.modules mn = some mc ∧
        Tools.ShippingMachineInst.CallStmt (Tools.ShippingMachineEntry.machNIn S.d.shape) (List.length S.d.shape.insts)
          (List.length S.d.shape.layout.slots) S.portNames k args mc (Stmt.inst mn iname conns) ∧
        kidData[k]? = some kd ∧ kidFs[k]? = some f ∧
        Tools.ShippingMachineCompose.ChildFn mc (Tools.ShippingMachineChild.childRange kd) f) ∧
    ∀ (i : Unit) (bools : Nat → Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain Bool)
      (bits : (j n : Nat) → Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain (BitVec n))
      (S₂ : Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain
        (Sparkle.Core.HList (Tools.ShippingMachineDenote.tys [Tools.ShippingUnifiedSource.SType.bits 6])))
      (Ss : Tools.ShippingMachineTele.Tele.Sigs
        (Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte.machineInners.at i bools bits)),
      SourceData.Wit i bools bits S₂ Ss →
      ∀ (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ (t : Nat) (st : String → Nat), t < T → ∀ (q : Nat) (nm : String), q < S.kD → S.portNames[q]? = some nm →
          seed t st nm = Tools.ShippingMachineEntry.posEnc (fun p => (bools p).val (T - 1 - t))
            (fun p n => ((Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) p n).val (T - 1 - t))
            q (Option.getD (Option.map (fun x => x.2) (S.d.bsIn)[q]?) .domain)) →
        (∀ (t : Nat) (st : String → Nat) (r : String), r ∈ regs → seed t st r = st r) →
        (∀ (t : Nat) (st : String → Nat), seed t st "rst" = 0) →
        (∀ (k : Nat) (r : String) (f : Sparkle.IR.Machine.SlotField), regs[k]? = some r →
          S.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        ∃ envs, Tools.ShippingMachineLinked.runModuleH (Tools.ShippingEntrySoundness.weOf b)
            (Tools.ShippingMachineLinked.childMap D.modules) b.body seed T st0 mems = some envs ∧ envs.length = T ∧
          ∀ (j : Nat) (hj : j < envs.length) (k : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
            S.d.shape.layout.outs[k]? = some o →
            (Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte.machineSource i bools bits)[k]? = some f →
            (envs[j]'hj) o.name = f j

example : ∀ (S : SourceData) (b : Module) (D : Design), RootShowsAt S b D ↔ ExpectedRootShowsAt S b D :=
  fun _ _ _ => Iff.rfl

/-! ### (B) negative controls: the types of the kernel-checked theorems, restated -/

section Controls
open Tools.ShippingFGCircuitS3tCert Tools.ShippingFGCircuitS3tCombRun

-- the structural validator on the root: a missing child, a swapped child (names exchanged; a certificate naming the wrong statements), a wrong width, a wrong output, a register reset value changed, no `rst`, a rejected certificate
example : structuralOk rootS pilotB0 (noKid1 pilotD0) cert0 = false := neg_no_kid1
example : structuralOk rootS pilotB0 (noKid0 pilotD0) cert0 = false := neg_no_kid0
example : structuralOk rootS pilotB0 (swapNames pilotD0) cert0 = false := neg_swap_names
example : structuralOk rootS pilotB0 (narrowKid1 pilotD0) cert0 = false := neg_narrow_kid1
example : structuralOk rootS (narrowOut pilotB0) pilotD0 cert0 = false := neg_narrow_out
example : structuralOk rootS (flipInit pilotB0) pilotD0 cert0 = false := neg_flip_init
example : structuralOk rootS (noRst pilotB0) pilotD0 cert0 = false := neg_no_rst
example : structuralOk rootS pilotB0 pilotD0 { cert0 with callAt := [238, 173] } = false := neg_cert_swapped
example : structuralOk rootS pilotB0 pilotD0 { cert0 with callAt := [173, 173] } = false := neg_cert_same
example : structuralOk rootS pilotB0 pilotD0 { cert0 with regs := cert0.regs.reverse } = false := neg_cert_regs
example : structuralOk { rootS with kidInW := [[7], [16, 16, 8, 8, 32, 5]] } pilotB0 pilotD0 cert0 = false := neg_data_width
example : structuralOk { rootS with kidMod := ["Sparkle_IP_Net_HTTP_httpGetByte"] } pilotB0 pilotD0 cert0 = false := neg_data_kids
-- P1-1 (the returned Design's top and module table): a different top name, a duplicate module name, a child named like the top
example : structuralOk rootS pilotB0 (otherTop pilotD0) cert0 = false := neg_other_top
example : structuralOk rootS pilotB0 (dupModule pilotD0) cert0 = false := neg_dup_module
example : structuralOk rootS pilotB0 (kidNamedTop pilotD0 pilotB0) cert0 = false := neg_kid_named_top
-- P1-2 (top input types/widths): an input width changed (port and wire; port only; wire only), two inputs swapped, a duplicate input name, `clk` of two bits, a claimed `clk`
example : structuralOk rootS (narrowIn pilotB0) pilotD0 cert0 = false := neg_narrow_in
example : structuralOk rootS (narrowInPortOnly pilotB0) pilotD0 cert0 = false := neg_narrow_in_port_only
example : structuralOk rootS (narrowInWireOnly pilotB0) pilotD0 cert0 = false := neg_narrow_in_wire_only
example : structuralOk rootS (swapInputs pilotB0) pilotD0 cert0 = false := neg_swap_inputs
example : structuralOk rootS (dupInput pilotB0) pilotD0 cert0 = false := neg_dup_input
example : structuralOk rootS (wideClk pilotB0) pilotD0 cert0 = false := neg_wide_clk
example : structuralOk { rootS with portNames := "clk" :: rootS.portNames.tail } pilotB0 pilotD0 cert0 = false := neg_claim_clk
-- `CheckRoot` itself refuses today (its body validator is not written)
example : CheckRoot rootS pilotB0 pilotD0 cert0 = false := check_root_refuses
-- the combinational validator on `pilotK0`: an altered child module, a dropped statement, a wrong width, a wrong output, the other child, a wrong source term
example : checkK0 (dropFirst pilotK0) = false := neg_drop_first
example : checkK0 (dropLast pilotK0) = false := neg_drop_last
example : checkK0 (flipConst pilotK0) = false := neg_flip_const
example : checkK0 (swapMux pilotK0) = false := neg_swap_mux
example : checkK0 (wrongWidth pilotK0) = false := neg_wrong_width
example : checkK0 (wrongOutW pilotK0) = false := neg_wrong_out_w
example : checkK0 (wrongOutName pilotK0) = false := neg_wrong_out_name
example : checkK0 pilotK1 = false := neg_other_child
example : Tools.ShippingFGCircuitS3tComb.checkComb ⟨[1], [Tools.ShippingFGCircuitS3tComb.CTerm.lit 8 0]⟩ pilotK0 = false := neg_wrong_source
end Controls

/-! ### (C) the simultaneous-satisfaction example, and the validators on the artifact -/

example : rootS.ok = true := rootS_ok
example : rootS.SrcEq := Tools.ShippingFGCircuitS3tCalls.rootS_srcEq
example : Tools.ShippingFGCircuitS3tCert.struct_ok = Tools.ShippingFGCircuitS3tCert.struct_ok := rfl
example : structuralOk rootS pilotB0 pilotD0 Tools.ShippingFGCircuitS3tCert.cert0 = true := Tools.ShippingFGCircuitS3tCert.struct_ok
example : Tools.ShippingFGCircuitS3tCombRun.checkK0 pilotK0 = true := Tools.ShippingFGCircuitS3tCombRun.k0_check
example (val : Nat → Nat → Nat) : ∃ (seed : Nat → (String → Nat) → Env) (st0 : String → Nat),
    (∀ (t : Nat) (st : String → Nat) (q : Nat) (nm : String), q < rootS.kD → rootS.portNames[q]? = some nm →
      seed t st nm = val t q) ∧
    (∀ (t : Nat) (st : String → Nat) (r : String), r ∈ Tools.ShippingFGCircuitS3tCert.cert0.regs → seed t st r = st r) ∧
    (∀ (t : Nat) (st : String → Nat), seed t st "rst" = 0) ∧
    (∀ (k : Nat) (r : String) (f : Sparkle.IR.Machine.SlotField), Tools.ShippingFGCircuitS3tCert.cert0.regs[k]? = some r →
      rootS.d.shape.layout.slots[k]? = some f → st0 r = f.init) :=
  Tools.ShippingFGCircuitS3tCert.example_premises val

/-- `checkComb_sound`, spelled again -/
example : ∀ (s : Tools.ShippingFGCircuitS3tComb.CSrc) (m : Module), Tools.ShippingFGCircuitS3tComb.checkComb s m = true →
    ∀ (V : Nat → Nat) (mems : MEnv) (env : Env),
      (∀ (i : Nat) (p : Port) (q : Nat), m.inputs[i]? = some p → s.inPos[i]? = some q →
        env p.name = V q % 2 ^ Tools.ShippingFGCircuitS3tComb.portW p) →
      ∃ env', evalAssigns (Sparkle.IR.RegDedup.declWidth m) mems m.body env = some env' ∧
        ∀ (i : Nat) (p : Port) (c : Tools.ShippingFGCircuitS3tComb.CTerm), m.outputs[i]? = some p → s.outs[i]? = some c →
          env' p.name = c.den V :=
  Tools.ShippingFGCircuitS3tComb.checkComb_sound

example : Tools.ShippingFGCircuitS3tComb.CSrc → Module → Bool := Tools.ShippingFGCircuitS3tComb.checkComb

/-! ### (D) kernel time and sizes, (E) axioms -/

open Lean Meta Elab Command Term

/-- decide the proposition `P ∧ True` by the kernel afresh (a type no earlier auxiliary lemma has); returns the milliseconds of the elaboration including the kernel run -/
def retime (p : TSyntax `term) : TermElabM Nat := do
  let stx ← `((by decide +kernel : $p ∧ True))
  let t0 ← IO.monoMsNow
  let _ ← elabTermEnsuringType stx none
  synthesizeSyntheticMVarsNoPostponing
  return (← IO.monoMsNow) - t0

run_cmd liftTermElabM do
  let env ← getEnv
  -- (E) AXIOMS: every theorem of the S3t modules
  let pre : List Name := [`Tools.ShippingFGCircuitS3tSpec, `Tools.ShippingFGCircuitS3tSat, `Tools.ShippingFGCircuitS3tCert,
    `Tools.ShippingFGCircuitS3tCalls, `Tools.ShippingFGCircuitS3tComb, `Tools.ShippingFGCircuitS3tCombRun]
  let thms := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    match ci with
    | .thmInfo _ => if pre.any (·.isPrefixOf n) then acc.push n else acc
    | _ => acc
  let mut axs : NameSet := {}
  for nm in thms do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT57 AXIOMS: {thms.size} theorems of the S3t modules (Spec, Sat, Cert, Calls, Comb, CombRun), standard axioms only ({axs.toList}); no sorryAx, no Lean.ofReduceBool (no native_decide)"
  -- (D) size and time: ONE run
  let sz (n : Name) : MetaM Nat := do
    match (← getConstInfo n) with
    | .thmInfo i => pure i.value.sizeWithoutSharing
    | .defnInfo i => pure i.value.sizeWithoutSharing
    | _ => pure 0
  let sizes ← [`Tools.ShippingFGCircuitS3tComb.checkComb_sound, `Tools.ShippingFGCircuitS3tCombRun.k0_check,
    `Tools.ShippingFGCircuitS3tCert.struct_ok, `Tools.ShippingFGCircuitS3tCert.cert0,
    `Tools.ShippingFGCircuitS3tCalls.rootS_callsEq, `Tools.ShippingFGCircuitS3tSat.premises_satisfiable].mapM fun n => do pure (n, ← sz n)
  let t1 ← retime (← `(Tools.ShippingFGCircuitS3tCombRun.checkK0 Tools.ShippingFGCircuitS3rArtifact.pilotK0 = true))
  let t2 ← retime (← `(Tools.ShippingFGCircuitS3tSpec.structuralOk Tools.ShippingFGCircuitS3tSpec.rootS Tools.ShippingFGCircuitS3rArtifact.pilotB0 Tools.ShippingFGCircuitS3rArtifact.pilotD0 Tools.ShippingFGCircuitS3tCert.cert0 = true))
  let t3 ← retime (← `(Tools.ShippingFGCircuitS3tSpec.rootS.ok = true))
  logInfo m!"FGCIRCUIT57 SIZE/TIME (ONE run, this machine; not a bound): proof/definition term sizes without sharing {sizes}; a fresh `decide +kernel` of `checkK0 pilotK0 = true` took {t1} ms, of `structuralOk rootS pilotB0 pilotD0 cert0 = true` {t2} ms, of `rootS.ok = true` {t3} ms (elaboration + kernel)"
  logInfo m!"FGCIRCUIT57 KERNEL: checkComb (httpGetByte's source terms read off its MachineData by `ofData`) accepts the closed child module pilotK0 (88 statements); structuralOk accepts the closed artifact pilotB0/pilotD0 with the certificate cert0; rootS.ok = true; each by `decide +kernel`.  checkComb_sound is a theorem over ALL modules and ALL inputs (not an evaluation); rootS.SrcEq is proved (no IR); CheckRoot is false for every input today, so no root claim"
  logInfo m!"FGCIRCUIT57 SIGNATURES: the type ascriptions of SourceData (+ its 8 fields), SrcEq/SrcCore/CallsEq, RootShowsAt, CheckRoot, structuralOk, the statement of checkRoot_sound, certifiedReturn, the statement of certifiedReturn_sound, Cert, checkComb, checkComb_sound check the FUNCTION TYPES only; they are not an independent comparison of the bodies of SrcCore / CallsEq / structuralOk.  Separately, RootShowsAt's body is compared with an independently written statement (ExpectedRootShowsAt, Iff.rfl), and CheckRootSoundStmt / CertifiedReturnSoundStmt are respelled (Iff.rfl).  Not every SourceData field is fixed by SrcEq (portNames and kidMod are claims); CertifiedReturnSoundStmt only extracts the checker's acceptance (no relation between declName and S.declName)"
  logInfo m!"FGCIRCUIT57 NEGATIVE CONTROLS: structural validator on the root 12 + 3 design-top (other top name, duplicate module name, child named like the top) + 7 input-boundary (width changed in port+wire, port only, wire only, inputs swapped, duplicate input name, clk two bits, claimed clk) (missing child ×2, swapped names, wrong child width, wrong output width, register reset value, no rst, certificate swapped, certificate repeated, registers permuted, wrong data width, wrong child count) + CheckRoot refuses; combinational validator on pilotK0 9 (dropped first, dropped last, changed constant, swapped mux branches, wrong wire width, wrong output width, wrong output name, the other child, a wrong source term) + the altered modules differ; every one kernel-checked"
  logInfo m!"FGCIRCUIT57 SATISFIABILITY: rootS.ok = true; rootS.SrcEq proved; the four seed premises of RootShowsAt hold together at the artifact's 17 registers (and Tools.ShippingFGCircuitS3tSat.posEnc_fits: the value of premise (a) fits the declared port width) for every per-cycle input values (example_premises); CheckRoot = true is NOT shown (bodyOk is not written)"

end Tests.Gen5.FGCircuitPilotCheck57
