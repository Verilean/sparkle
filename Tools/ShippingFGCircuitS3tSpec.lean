import Tools.ShippingFGCircuitS2kLink
import Tools.ShippingFGCircuitS2vLink
import Tools.ShippingFGCircuitS3rArtifact
import Tools.ShippingFGCircuitS3jStart
set_option autoImplicit false
-- FG circuit pilot S3t, step 1 (FREEZE DRAFT): the full STATEMENT of the certificate design for the pilot root, type-checked: `SourceData`, `SrcEq`, `RootShowsAt`, `CheckRoot`, the statement of `checkRoot_sound` (a `def … : Prop`, NOT proved here), `certifiedReturn` (guard on `CheckRoot`, refuse on false; no fallback), and the simultaneous-satisfaction example.
-- No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §69.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3tSpec
open Lean hiding Module Expr
open Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Machine Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge Tools.ShippingUnifiedSource
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt
open Tools.ShippingEntrySoundness (RunsTo weOf)
open Tools.ShippingMachineLinked (runModuleH childMap)
open Tools.ShippingMachineCompose (ChildFn)
open Tools.ShippingMachineChild (childValue childRange)
open Tools.ShippingMachineInst (CallStmt)
open Tools.ShippingMachineDenote Tools.ShippingMachineTeleNest Tools.ShippingMachineTeleStates
open Tools.ShippingMachineNest (happendT castSS)

/-! ## The two children and the root, fixed (order, range, value, input widths) -/

/-- the root's two children in call order (`kid 0 = httpGetByte`, `kid 1 = tlpCplByte`); no `getD` default: the list has length 2 (`kids_length`) -/
noncomputable def kidData : List MachineData :=
  [Sparkle.IP.Net.HTTP.httpGetByte.machineData, Sparkle.IP.Bus.PCIe.tlpCplByte.machineData]

/-- the children's source functions on their argument ports (`childValue` of the child's own `machineSource`) -/
noncomputable def kidFs : List (List Nat → Nat) :=
  [childValue Sparkle.IP.Net.HTTP.httpGetByte.machineSource Sparkle.IP.Net.HTTP.httpGetByte.machineData.bsIn defaultDomain,
   childValue Sparkle.IP.Bus.PCIe.tlpCplByte.machineSource Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.bsIn defaultDomain]

theorem kids_length : kidData.length = 2 ∧ kidFs.length = 2 := ⟨rfl, rfl⟩

/-- the width of a port binder (a domain binder has no port) -/
def kindW : MixedGateBinder → Nat
  | .bits n => n
  | .bool => 1
  | .domain => 0

/-- the input port widths of a machine's declaration binders, domain binders (no port) left out -/
def inWidths (bs : List (Name × MixedGateBinder)) : List Nat :=
  (bs.filter fun b => b.2 != .domain).map (fun b => kindW b.2)

/-! ## SourceData -/

/-- The source side for the pilot root, as data: the machine the front end read off the declaration, the declaration's own observation, the allocator's port names, the two children's module names and port widths, and the number `kD` of the root's own input binders.  This is a statement about THIS root: `SrcEq` pins every field to the root's generated constants.  `instFields = []` is required (`ok`), so the soundness statement covers no root with instance fields. -/
structure SourceData where
  declName : Name
  d : MachineData
  /-- `declObs`: the declaration's own value, `monoObs shHft R` -/
  declObs : (Nat → Signal defaultDomain Bool) → ((j n : Nat) → Signal defaultDomain (BitVec n)) → List (Nat → Nat)
  /-- the names the allocator gives the transition's ports (every binder, in order) -/
  portNames : List String
  /-- the module names of the two children, in call order -/
  kidMod : List String
  /-- the children's input port widths and output port widths, in call order -/
  kidInW : List (List Nat)
  kidOutW : List (List Nat)
  /-- the number of the root's own input binders (the first `kD` binders; the calls' output ports follow) -/
  kD : Nat

namespace SourceData

/-- the Bool checks on the data: the root has no instance fields, exactly two calls, the children are two, widths and names are present for both, and the port names are one per binder.  (Each is decided by `decide +kernel` for the root: `rootS_ok`.) -/
def ok (S : SourceData) : Bool :=
  S.d.ok && S.d.shape.instFields.isEmpty && (S.d.shape.insts.length == 2) &&
  (S.kidMod.length == 2) && (S.kidInW.length == 2) && (S.kidOutW.length == 2) &&
  (S.portNames.length == S.d.shape.binders.length) && decide S.portNames.Nodup

/-- the state witnesses of the root's source: Lean state signals `S₂` (the enclosing registers) and `Ss` (the chain's) whose fused state starts at the reset tuple, steps by the data's `nexts` over the Lean extension `machineExt … S₂ Ss`, and shows the data's outputs as `machineSource` (the content of `machine_states`, `Tools.ShippingFGCircuitS2vLink.root_states`; it contains no IR) -/
def Wit (i : Unit) (bools : Nat → Signal defaultDomain Bool)
    (bits : (j n : Nat) → Signal defaultDomain (BitVec n))
    (S₂ : Signal defaultDomain (HList (tys [SType.bits 6])))
    (Ss : Tools.ShippingMachineTele.Tele.Sigs (synth_hftPcieOutByte.machineInners.at i bools bits)) : Prop :=
  teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
      Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss 0 =
    castSS Tools.ShippingFGCircuitS2vLink.root_hss
      (happendT [SType.bits 6] synth_hftPcieOutByte.machineInners.sss synth_hftPcieOutByte.machineInits
        synth_hftPcieOutByte.machineInners.initsT) ∧
  (∀ t, teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
      Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss (t + 1) = evalTerms
    (fun j => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos
      synth_hftPcieOutByte.machineData.vpos synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools
      (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t
      (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
        Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss t)).b (synth_hftPcieOutByte.machineData.bpos j))
    (fun j w => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos
      synth_hftPcieOutByte.machineData.vpos synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools
      (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t
      (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
        Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss t)).v (synth_hftPcieOutByte.machineData.vpos j) w)
    synth_hftPcieOutByte.machineData.nexts) ∧
  ∀ t, (synth_hftPcieOutByte.machineSource i bools bits).map (fun f => f t) =
    synth_hftPcieOutByte.machineData.outs.map fun o => enc o.1 (eval
      (fun k => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos
        synth_hftPcieOutByte.machineData.vpos synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools
        (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t
        (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
          Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss t)).b (synth_hftPcieOutByte.machineData.bpos k))
      (fun k w => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos
        synth_hftPcieOutByte.machineData.vpos synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools
        (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t
        (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
          Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss t)).v (synth_hftPcieOutByte.machineData.vpos k) w) o.2)

/-- the SOURCE's call facts at a cycle (no IR): at the state the witnesses give, every call `k`'s argument values are in the child's range and the child's function on them is the value the root's extension carries at the call's input position.  This is the premise that `machine_linked` states about `lsrc`; it mentions only the source (`callArgVals`, `kidFs`). -/
def CallsEq (S : SourceData) : Prop :=
  ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n))
    (S₂ : Signal defaultDomain (HList (tys [SType.bits 6])))
    (Ss : Tools.ShippingMachineTele.Tele.Sigs (synth_hftPcieOutByte.machineInners.at i bools bits)),
    Wit i bools bits S₂ Ss → ∀ (k : Nat) (args : List Nat) (kd : MachineData) (f : List Nat → Nat) (j : Nat),
      (S.d.shape.insts.map (·.2.1))[k]? = some args → kidData[k]? = some kd → kidFs[k]? = some f →
      (∀ q ∈ args, q < S.d.ls.length) ∧
      childRange kd (callArgVals synth_hftPcieOutByte.machineData bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) j
        (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
          Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss j) args) ∧
      f (callArgVals synth_hftPcieOutByte.machineData bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) j
        (teleState synth_hftPcieOutByte.machineInners (d := synth_hftPcieOutByte.machineData)
          Tools.ShippingFGCircuitS2vLink.root_hss i bools bits S₂ Ss j) args) =
        posEnc (fun p => (bools p).val j) (fun p n => ((synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) p n).val j)
          (S.kD + k) (((S.d.bsIn.drop S.kD)[k]?.map (·.2)).getD .domain)

/-- the allocator's port names: some compiler ids and cache give the transition's ports the names `S.portNames` (the names depend on the binders' names and the module name only).  NOT kernel-evaluable: the allocator's `sanitizeName`/`clean` use `String.replace`/`String.all` (well-founded, opaque to the kernel); see docs §69 gap G1. -/
def NamesEq (S : SourceData) : Prop :=
  ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
    ids.Nodup ∧ ids.length = S.d.shape.binders.length ∧
    (machPorts S.declName ids cache S.d.shape.binders).map (·.name) = S.portNames

/-- the fields of the data are the root's and its children's, the declaration's own observation is `machineSource`, and the state witnesses exist for every input; no IR, no names, no calls -/
def SrcCore (S : SourceData) : Prop :=
  S.declName = hftRoot ∧ S.d = synth_hftPcieOutByte.machineData ∧
  (∀ bools bits, S.declObs bools bits = synth_hftPcieOutByte.machineSource () bools bits) ∧
  (∀ (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n)),
    ∃ (S₂ : Signal defaultDomain (HList (tys [SType.bits 6])))
      (Ss : Tools.ShippingMachineTele.Tele.Sigs (synth_hftPcieOutByte.machineInners.at () bools bits)),
      Wit () bools bits S₂ Ss) ∧
  S.kidInW = kidData.map (fun kd => inWidths kd.bsIn) ∧
  S.kidOutW = kidData.map (fun kd => kd.shape.layout.outs.map (·.width)) ∧
  S.kD = 5

/-- **`SrcEq`**: the connection of the ORIGINAL value `R` to `machineSource`, and the data's fields to the root's generated constants.  It carries NO statement about the IR `b`, `D` (nothing about `MachineWired`, `ChildFn`, `runModuleH`): `SrcCore` (the fields are the root's, the declaration's own observation equals `machineSource` (`monoObs_root`, `rfl`), the state witnesses exist (`machine_states`)), `NamesEq` (the allocator's port names), `CallsEq` (the source's call facts). -/
def SrcEq (S : SourceData) : Prop := S.SrcCore ∧ S.NamesEq ∧ S.CallsEq

end SourceData

/-! ## RootShowsAt: run-free meaning preservation for ALL inputs -/

/-- The meaning a returned `(b, D)` has for the root.  Built from the shape of the generated `machine_composed` conclusion, with the children's `MachineRun` HYPOTHESIS moved into a conjunct of the conclusion (`ChildFn`).  The child conditions cover every call (`k < 2`: the call's statement is in the body, its module is what its name resolves to in `D`, and the module computes the child's source function on the child's range) and every `inst` statement of the body (each is one of the calls); a failed lookup makes the statement FALSE, not vacuous.  The run part is quantified over ALL inputs, the state witnesses, the run length `T`, `seed`, `st0`, `mems`, under the four exact premises `(a)`–`(d)` (their simultaneous satisfaction: `premises_satisfiable`). -/
def RootShowsAt (S : SourceData) (b : Module) (D : Design) : Prop :=
  S.d.shape.instFields = [] ∧ S.d.shape.insts.length = 2 ∧
  ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs lets : List String),
    ids.Nodup ∧ ids.length = S.d.shape.binders.length ∧
    (machPorts S.declName ids cache S.d.shape.binders).map (·.name) = S.portNames ∧
    regs.Nodup ∧ regs.length = S.d.ss.length ∧ lets.length = S.d.letBs.length ∧
    MachineWired S.declName S.d.shape ids cache b D regs lets ∧
    -- every call k < 2 is covered: statement, module lookup, `ChildFn` (a conjunct, not a hypothesis)
    (∀ k, k < 2 → ∃ (args : List Nat) (mc : Module) (st : Stmt) (kd : MachineData) (f : List Nat → Nat),
      (S.d.shape.insts.map (·.2.1))[k]? = some args ∧ st ∈ b.body ∧
      CallStmt (machNIn S.d.shape) S.d.shape.insts.length S.d.shape.layout.slots.length S.portNames k args mc st ∧
      moduleByName D.modules mc.name = some mc ∧ kidData[k]? = some kd ∧ kidFs[k]? = some f ∧
      ChildFn mc (childRange kd) f) ∧
    -- every instance statement of the body is one of those calls
    (∀ (mn iname : String) (conns : List (String × Expr)), Stmt.inst mn iname conns ∈ b.body →
      ∃ (k : Nat) (args : List Nat) (mc : Module) (kd : MachineData) (f : List Nat → Nat), k < 2 ∧
        (S.d.shape.insts.map (·.2.1))[k]? = some args ∧ moduleByName D.modules mn = some mc ∧
        CallStmt (machNIn S.d.shape) S.d.shape.insts.length S.d.shape.layout.slots.length S.portNames k args mc
          (Stmt.inst mn iname conns) ∧
        kidData[k]? = some kd ∧ kidFs[k]? = some f ∧ ChildFn mc (childRange kd) f) ∧
    -- the run, for all inputs
    ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n))
      (S₂ : Signal defaultDomain (HList (tys [SType.bits 6])))
      (Ss : Tools.ShippingMachineTele.Tele.Sigs (synth_hftPcieOutByte.machineInners.at i bools bits)),
      SourceData.Wit i bools bits S₂ Ss →
      ∀ (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        -- (a) the input ports carry the source's inputs
        (∀ (t : Nat) (st : String → Nat), t < T →
          SourceInputs S.declName (S.d.bsIn.take S.kD) ids cache (fun j => (bools j).val (T - 1 - t))
            (fun j n => ((synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) j n).val (T - 1 - t)) (seed t st)) →
        -- (b) a register reads the state
        (∀ (t : Nat) (st : String → Nat) (r : String), r ∈ regs → seed t st r = st r) →
        -- (c) reset is 0
        (∀ (t : Nat) (st : String → Nat), seed t st "rst" = 0) →
        -- (d) the initial value of register k is its slot's init
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → S.d.shape.layout.slots[k]? = some f →
          st0 r = f.init) →
        ∃ envs, runModuleH (weOf b) (childMap D.modules) b.body seed T st0 mems = some envs ∧ envs.length = T ∧
          ∀ (j : Nat) (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            S.d.shape.layout.outs[k]? = some o → (synth_hftPcieOutByte.machineSource i bools bits)[k]? = some f →
            (envs[j]'hj) o.name = f j

/-! ## The certificate and the (pure) validator -/

/-- the untrusted hints: the index of call `k`'s `inst` statement in the body, and the register names in slot order -/
structure Cert where
  callAt : List Nat
  regs : List String

/-- is the statement an `inst`? -/
def isInstStmt : Stmt → Bool
  | .inst .. => true
  | _ => false

/-- is the statement a `register`? -/
def isRegStmt : Stmt → Bool
  | .register .. => true
  | _ => false

/-- width of a port's type (`bit` = 1, `bitVector n` = n; anything else 0, which no child port has) -/
def portW (p : Port) : Nat :=
  match p.ty with
  | .bit => 1
  | .bitVector n => n
  | _ => 0

/-- the child's input ports (clock and reset are not arguments) -/
def argPortsOf (mc : Module) : List Port := mc.inputs.filter fun p => p.name != "clk" && p.name != "rst"

/-- call `k`'s check: the cert's index names an `inst` statement of the body whose module is the `k`-th child's and resolves in `D`, whose connections are exactly the ones `CallStmt` describes (the argument ports to the argument wires of the allocator's names, the output port to the call's wire), and the child module has the fixed port widths -/
def callOk (S : SourceData) (b : Module) (D : Design) (cert : Cert) (k : Nat) : Bool :=
  match cert.callAt[k]?, S.kidMod[k]?, S.kidInW[k]?, S.kidOutW[k]?, (S.d.shape.insts.map (·.2.1))[k]? with
  | some p, some mn, some ws, some ows, some args =>
    match b.body[p]?, moduleByName D.modules mn with
    | some (.inst mn' _ conns), some mc =>
      match S.portNames[machNIn S.d.shape + k]?, args.mapM (fun j => S.portNames[machNIn S.d.shape + S.d.shape.insts.length + S.d.shape.layout.slots.length + j]?), mc.outputs with
      | some outW, some argWs, [outP] =>
        (mn' == mn) && (mc.name == mn) &&
        ((argPortsOf mc).map portW == ws) && ([portW outP] == ows) &&
        (!(mc.inputs.any fun p => p.name == "clk" || p.name == "rst")) &&
        ((argPortsOf mc).length == argWs.length) &&
        decide ((argPortsOf mc).map (·.name)).Nodup &&
        (!(argWs.contains outW)) && (!(((argPortsOf mc).map (·.name)).contains outP.name)) && (outP.name != "rst") &&
        decide (conns = ((argPortsOf mc).zip argWs).map (fun (p, w) => (p.name, Expr.ref w)) ++ [(outP.name, Expr.ref outW)])
      | _, _, _ => false
    | _, _ => false
  | _, _, _, _, _ => false

/-- register `r` of the body is a clocked register with synchronous reset `rst` and initial value `init` -/
def regOk (b : Module) (r : String) (init : Nat) : Bool :=
  b.body.any fun st => match st with
    | .register o c (rn, _) _ i => (o == r) && (c == "clk") && (rn == "rst") && (i == Int.ofNat init)
    | _ => false

/-- the registers: one per slot, named by the cert, distinct, each a register statement with the slot's init, and no other register statement -/
def regsOk (S : SourceData) (b : Module) (cert : Cert) : Bool :=
  (cert.regs.length == S.d.ss.length) && decide cert.regs.Nodup &&
  ((List.range cert.regs.length).all fun k =>
    match cert.regs[k]?, S.d.shape.layout.slots[k]? with
    | some r, some f => regOk b r f.init
    | _, _ => false) &&
  ((b.body.filter isRegStmt).length == cert.regs.length)

/-- the structural part of the validator (the coverage the freeze requires): no instance fields, two calls, both children found through `moduleByName` with the fixed widths, exactly those two `inst` statements, the registers, the output ports, the `rst` input.  A missing, swapped, or width-changed child, an extra `inst`, a changed register init, a missing `rst` make it false. -/
def structuralOk (S : SourceData) (b : Module) (D : Design) (cert : Cert) : Bool :=
  S.ok && (cert.callAt.length == 2) && decide (cert.callAt.Nodup) &&
  callOk S b D cert 0 && callOk S b D cert 1 &&
  ((b.body.filter isInstStmt).length == 2) &&
  regsOk S b cert &&
  (b.outputs.map (fun p => (p.name, portW p)) == S.d.shape.layout.outs.map (fun o => (o.name, o.width))) &&
  ((b.inputs.map (·.name)).contains "rst")

/-- NOT WRITTEN YET (M1, the body validator): the statements of the body against the source terms (`checkComb` for a combinational child is the step-2 piece).  It is `false` for every input, so `CheckRoot` is false for every input and `certifiedReturn` refuses: the freeze fixes the statement and the structural part, not a claim that the body is validated. -/
def bodyOk (_S : SourceData) (_b : Module) (_D : Design) (_cert : Cert) : Bool := false

/-- the validator -/
def CheckRoot (S : SourceData) (b : Module) (D : Design) (cert : Cert) : Bool :=
  structuralOk S b D cert && bodyOk S b D cert

/-- **the statement of `checkRoot_sound`** (a `def … : Prop`; its proof is NOT in this file): for every source data, module, design and certificate, with the data's checks and `SrcEq`, a validator that returns true shows the root. -/
def CheckRootSoundStmt : Prop :=
  ∀ (S : SourceData) (b : Module) (D : Design) (cert : Cert),
    S.ok = true → S.SrcEq → CheckRoot S b D cert = true → RootShowsAt S b D

/-! ## certifiedReturn: run the entry, guard on `CheckRoot`, refuse on false (no fallback) -/

/-- run `pilotEntry3` and return ITS `(b, D)` only if `CheckRoot` accepts exactly that pair with the certificate `mk b D` (an untrusted builder); otherwise throw -/
def certifiedReturn (S : SourceData) (mk : Module → Design → Cert) (declName : Name) :
    MetaM (Module × Design) := do
  let (b, D) ← Tools.ShippingFGCircuitS3jStart.pilotEntry3 declName
  unless CheckRoot S b D (mk b D) do throwError "certificate check failed"
  pure (b, D)

/-- the statement of `certifiedReturn_sound` (not proved here): a successful run returns a pair the validator accepted -/
def CertifiedReturnSoundStmt : Prop :=
  ∀ (S : SourceData) (mk : Module → Design → Cert) (declName : Name) {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {b : Module} {D : Design},
    RunsTo (certifiedReturn S mk declName) mctx mref cctx cref w (b, D) w' →
    ∃ cert, CheckRoot S b D cert = true

/-! ## The concrete root and the simultaneous-satisfaction example -/

/-- the allocator's names of the 69 binders of the root's transition (5 inputs, 2 call outputs, 17 slots, 45 `let`s) -/
def rootPortNames : List String :=
  ["_gen_rxByte", "_gen_rxValid", "_gen_sopTlp", "_gen_dataDword", "_gen_cplId", "_gen_inst0", "_gen_inst1", "_gen_cnt", "_gen_cnt_1", "_gen_fmtR_1", "_gen_reqR_1", "_gen_tagR_1", "_gen_addrR_1", "_gen_doneR_1", "_gen_r0_2", "_gen_r1_2", "_gen_r2_2", "_gen_r3_2", "_gen_cplCnt_2", "_gen_reqIdLatch_2", "_gen_tagLatch_2", "_gen_lowAddrLatch_2", "_gen_dataLatch_2", "_gen_wPulseR_2", "_gen_pZero", "_gen_p1", "_gen_pLast", "_gen_isIdle", "_gen_isLast", "_gen_isEmitting", "_gen_inst0_arg0", "_gen_cntInc", "_gen_p1_1", "_gen_p4", "_gen_p5", "_gen_p6", "_gen_p8", "_gen_p9", "_gen_p10", "_gen_p11", "_gen_inReq", "_gen_inTag", "_gen_inAddr", "_gen_isLast_1", "_gen_cntInc_1", "_gen_topBit", "_gen_isWriteSig", "_gen_addrIdx", "_gen_isR0", "_gen_isR1", "_gen_isR2", "_gen_isR3", "_gen_writeFire", "_gen_readFire", "_gen_regSel", "_gen_lowByte", "_gen_pZ5", "_gen_p1_5", "_gen_p16_5", "_gen_cplInc", "_gen_isCplIdle", "_gen_isCplLast", "_gen_inst1_arg0", "_gen_inst1_arg1", "_gen_inst1_arg2", "_gen_inst1_arg3", "_gen_inst1_arg4", "_gen_inst1_arg5", "_gen_cplValidOut"]

/-- the concrete source data of the pilot root -/
noncomputable def rootS : SourceData where
  declName := hftRoot
  d := synth_hftPcieOutByte.machineData
  declObs := Tools.ShippingFGCircuit.monoObs Tools.ShippingFGCircuitS1kStmt.shHft synth_hftPcieOutByte
  portNames := rootPortNames
  kidMod := ["Sparkle_IP_Net_HTTP_httpGetByte", "Sparkle_IP_Bus_PCIe_tlpCplByte"]
  kidInW := [[6], [16, 16, 8, 8, 32, 5]]
  kidOutW := [[8], [8]]
  kD := 5

theorem rootS_ok : rootS.ok = true := by decide +kernel

/-- the declaration's own observation is `machineSource` (`monoObs_root`, `rfl`) -/
theorem rootS_obs : ∀ bools bits, rootS.declObs bools bits = synth_hftPcieOutByte.machineSource () bools bits :=
  fun bools bits => Tools.ShippingFGCircuitS2cLink.monoObs_root bools bits

/-- the state witnesses exist for every input (`root_states`, the specialised `machine_states`) -/
theorem rootS_wit (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) :
    ∃ (S₂ : Signal defaultDomain (HList (tys [SType.bits 6])))
      (Ss : Tools.ShippingMachineTele.Tele.Sigs (synth_hftPcieOutByte.machineInners.at () bools bits)),
      SourceData.Wit () bools bits S₂ Ss := by
  obtain ⟨S₂, Ss, X, hX, h0, hstep, hobs⟩ := Tools.ShippingFGCircuitS2vLink.root_states () bools bits
  refine ⟨S₂, Ss, ?_, ?_, ?_⟩
  · exact (hX 0).symm.trans h0
  · intro t
    rw [← hX (t + 1), hstep t, hX t]
  · intro t
    rw [hobs t, hX t]

theorem rootS_widths : rootS.kidInW = kidData.map (fun kd => inWidths kd.bsIn) ∧
    rootS.kidOutW = kidData.map (fun kd => kd.shape.layout.outs.map (·.width)) := by
  constructor <;> decide +kernel

/-- the data-and-source part of `SrcEq` holds for the concrete root: every field is the root's, the declaration's observation is `machineSource`, the witnesses exist -/
theorem rootS_srcCore : rootS.SrcCore :=
  ⟨rfl, rfl, rootS_obs, rootS_wit, rootS_widths.1, rootS_widths.2, rfl⟩

end Tools.ShippingFGCircuitS3tSpec
