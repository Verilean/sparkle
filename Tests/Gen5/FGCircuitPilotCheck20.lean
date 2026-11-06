import Tools.ShippingFGCircuitS1xNoRaw
set_option autoImplicit false
-- FG circuit pilot S1x check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §26.

/-! # FGCircuitPilotCheck20 (light: each part is a small `run_cmd`)

1. SIGNATURES-A: `HftPostGate`, `coreOff_closed` against independently written statements (`isDefEq`, default transparency, binder kinds), and mutants (each must NOT be defeq).
2. SIGNATURES-B: `hftObNoRawOff_of_run` and `HftFinalStmtOffLN` / `synth_hftPcieOutByte_finalOffLN_Z`.
3. HYPS: the explicit hypotheses of the instance by name (`hnoraw` is gone; `hcl`, `hgate` are in its place), and what they mention.
4. AXIOMS. 5. SNAPSHOT20: kernel facts. -/
namespace Tests.Gen5.FGCircuitPilotCheck20
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1xNoRaw
open Tools.ShippingMachineEntry
open Tools.ShippingHierMono (NoInstOf)
open Tools.ShippingGen5DCEntryD (PostEntry)
open Sparkle.Compiler.Elab

abbrev W := Void IO.RealWorld
abbrev Cx := Meta.Context
abbrev Rf1 := ST.Ref IO.RealWorld Meta.State
abbrev Cc := Core.Context
abbrev Rf2 := ST.Ref IO.RealWorld Core.State
abbrev Md := Sparkle.IR.AST.Module
abbrev Dg := Sparkle.IR.AST.Design
noncomputable def RootShape : MachineShape := synth_hftPcieOutByte.machineData.shape
noncomputable def OtherShape : MachineShape := Sparkle.Tests.SignalLoopTest.counterLoop.machineData.shape

/-! ## 1. HftPostGate and coreOff_closed -/

def ExpGate (G : Md → Bool) (root : Name) (post : Prop → Prop) (mctx : Cx) (mref : Rf1) (cctx : Cc) (cref : Rf2) (w : W) (b : Md) (D' : Dg) : Prop :=
  ∀ (raw : Md) (D₀ : Dg) (w1 : W), RunsTo (synthesizeCombinationalCoreOff root) mctx mref cctx cref w (raw, D₀) w1 → PostEntry b raw D₀ D' → G b = true
def GateTrue := ExpGate Sparkle.IR.RefineCheck.hierGate hftRoot (fun p => p)
def GateOtherRoot := ExpGate Sparkle.IR.RefineCheck.hierGate hftHttp (fun p => p)
def GateBinds := ExpGate Sparkle.IR.RefineCheck.hierBinds hftRoot (fun p => p)
def GateConst := ExpGate (fun _ => true) hftRoot (fun p => p)
def GateNoPE (mctx : Cx) (mref : Rf1) (cctx : Cc) (cref : Rf2) (w : W) (b : Md) (D' : Dg) : Prop :=
  ∀ (raw : Md) (D₀ : Dg) (w1 : W), RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 → Sparkle.IR.RefineCheck.hierGate b = true

/-- `coreOff_closed` and three mutants (no closing premise; no instance premise; the design half about another name) -/
def ExpClosed : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {declName : Name} {w w' : W} {m : Md} {d : Dg} {shape : MachineShape}
    (_hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (_entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (_closes : MachineCloses mctx mref cctx cref declName shape)
    (_hI : shape.insts ≠ []),
    NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, NoInstOf m.name g.body
def ClosedNoCl : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {declName : Name} {w w' : W} {m : Md} {d : Dg} {shape : MachineShape}
    (_hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (_entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (_hI : shape.insts ≠ []),
    NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, NoInstOf m.name g.body
def ClosedNoI : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {declName : Name} {w w' : W} {m : Md} {d : Dg} {shape : MachineShape}
    (_hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (_entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (_closes : MachineCloses mctx mref cctx cref declName shape),
    NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, NoInstOf m.name g.body
def ClosedBodyOnly : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {declName : Name} {w w' : W} {m : Md} {d : Dg} {shape : MachineShape}
    (_hr : RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (m, d) w')
    (_entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (_closes : MachineCloses mctx mref cctx cref declName shape)
    (_hI : shape.insts ≠ []),
    NoInstOf m.name m.body
def ClosedOldCore : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {declName : Name} {w w' : W} {m : Md} {d : Dg} {shape : MachineShape}
    (_hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (_entry : MachineDefinesLinkedOff mctx mref cctx cref declName shape w m d w')
    (_closes : MachineCloses mctx mref cctx cref declName shape)
    (_hI : shape.insts ≠ []),
    NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, NoInstOf m.name g.body

def whitelist : List Name := [``HftPostGate, ``HftFinalStmtOffLN, ``HftFinalStmtOffL]
def inQ (c : Name) : Bool := (`Tests.Gen5.FGCircuitPilotCheck20).isPrefixOf c
def normOnce (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if whitelist.contains c || inQ c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:4] do
    e ← normOnce e
  return e
def sameTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  let a ← norm ty
  let e ← norm exp
  unless ← withDefault (isDefEq a e) do throwError "{what}: type is NOT the expected statement"
def diffTy (what : String) (ty exp : Lean.Expr) : MetaM Unit := do
  let a ← norm ty
  let e ← norm exp
  if a == e then throwError "{what}: the MUTANT is the same expression"
  if ← withReducible (isDefEq a e) then throwError "{what}: the MUTANT was accepted"
def tyOf (n : Name) : MetaM Lean.Expr := do
  let ci ← getConstInfo n
  unless ci.levelParams.isEmpty do throwError "{n}: level parameters"
  pure ci.type
partial def binderInfos : Lean.Expr → List BinderInfo
  | .forallE _ _ b bi => bi :: binderInfos b
  | _ => []

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS1xNoRaw
  let Q := `Tests.Gen5.FGCircuitPilotCheck20
  sameTy "HftPostGate" (C (X ++ `HftPostGate)) (C (Q ++ `GateTrue))
  let mut nm : Nat := 0
  for mu in ["GateOtherRoot", "GateBinds", "GateConst", "GateNoPE"] do
    diffTy s!"HftPostGate vs {mu}" (C (X ++ `HftPostGate)) (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  let t ← tyOf (X ++ `coreOff_closed)
  sameTy "coreOff_closed" t (C (Q ++ `ExpClosed))
  unless binderInfos (← norm t) == binderInfos (← norm (C (Q ++ `ExpClosed))) do throwError "coreOff_closed: binder kinds differ"
  for mu in ["ClosedNoCl", "ClosedNoI", "ClosedBodyOnly", "ClosedOldCore"] do
    diffTy s!"coreOff_closed vs {mu}" t (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  logInfo m!"FGCIRCUIT20 SIGNATURES-A: HftPostGate and coreOff_closed (complete types, binder kinds) match independently written statements (isDefEq, default); {nm} mutants rejected (gate: other root / hierBinds / constant / no PostEntry; closed: no closing premise / no instance premise / body only / old core entry)"

/-! ## 2. hftObNoRawOff_of_run and the final statement -/

noncomputable def GtT : Cx → Rf1 → Cc → Rf2 → W → Md → Dg → Prop := GateTrue
noncomputable def GtNone : Cx → Rf1 → Cc → Rf2 → W → Md → Dg → Prop := fun _ _ _ _ _ _ _ => True
noncomputable def GtConst : Cx → Rf1 → Cc → Rf2 → W → Md → Dg → Prop := GateConst
noncomputable def GtOther : Cx → Rf1 → Cc → Rf2 → W → Md → Dg → Prop := GateOtherRoot
noncomputable def ExpRun (Shd Shc : MachineShape) (rootD rootC : Name) (Gt : Cx → Rf1 → Cc → Rf2 → W → Md → Dg → Prop) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} {w : W} {b : Md} {D' : Dg}
    (_hdRun : ∀ (raw : Md) (D₀ : Dg) (w1 : W), MachineDefinesLinkedOff mctx mref cctx cref rootD Shd w raw D₀ w1)
    (_hcl : MachineCloses mctx mref cctx cref rootC Shc)
    (_hgate : Gt mctx mref cctx cref w b D'),
    HftObNoRawOff mctx mref cctx cref w b D'
noncomputable def RunTrue := ExpRun RootShape RootShape hftRoot hftRoot GtT
noncomputable def RunOtherD := ExpRun OtherShape RootShape hftRoot hftRoot GtT
noncomputable def RunOtherC := ExpRun RootShape OtherShape hftRoot hftRoot GtT
noncomputable def RunHttpC := ExpRun RootShape RootShape hftRoot hftHttp GtT
noncomputable def RunHttpD := ExpRun RootShape RootShape hftHttp hftRoot GtT
noncomputable def RunNoGate := ExpRun RootShape RootShape hftRoot hftRoot GtNone
noncomputable def RunConstGate := ExpRun RootShape RootShape hftRoot hftRoot GtConst

noncomputable def ExpFLN (Ob : Environment → Prop) (CV : CDRel) (Cl : Cx → Rf1 → Cc → Rf2 → Prop) (Gt : Cx → Rf1 → Cc → Rf2 → W → Md → Dg → Prop) : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : Rf1} {cref : Rf2}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Md} {D' : Dg}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hcd : Ob (envAt cref w))
    (htop : ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hcl : Cl mctx mref cctx cref)
    (hgate : Gt mctx mref cctx cref w b D'),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p
noncomputable def ClT : Cx → Rf1 → Cc → Rf2 → Prop := fun mctx mref cctx cref => MachineCloses mctx mref cctx cref hftRoot RootShape
noncomputable def ClOther : Cx → Rf1 → Cc → Rf2 → Prop := fun mctx mref cctx cref => MachineCloses mctx mref cctx cref hftRoot OtherShape
noncomputable def ClNone : Cx → Rf1 → Cc → Rf2 → Prop := fun _ _ _ _ => True
noncomputable def FZ := ExpFLN HftObCDZ cdvZ ClT GtT

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS1xNoRaw
  let Q := `Tests.Gen5.FGCircuitPilotCheck20
  let U := `Tools.ShippingFGCircuitS1uSrc
  let mut nm : Nat := 0
  let t ← tyOf (X ++ `hftObNoRawOff_of_run)
  sameTy "hftObNoRawOff_of_run" t (C (Q ++ `RunTrue))
  unless binderInfos (← norm t) == binderInfos (← norm (C (Q ++ `RunTrue))) do throwError "hftObNoRawOff_of_run: binder kinds differ"
  for mu in ["RunOtherD", "RunOtherC", "RunHttpC", "RunHttpD", "RunNoGate", "RunConstGate"] do
    diffTy s!"hftObNoRawOff_of_run vs {mu}" t (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  logInfo m!"FGCIRCUIT20 SIGNATURES-B1: hftObNoRawOff_of_run (premises: the machine boundary of the core run, MachineCloses of the root's shape, the gate of the post-processed IR top; conclusion HftObNoRawOff) matches; {nm} mutants rejected"

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS1xNoRaw
  let Q := `Tests.Gen5.FGCircuitPilotCheck20
  let U := `Tools.ShippingFGCircuitS1uSrc
  let mut nm : Nat := 0
  let t ← tyOf (X ++ `synth_hftPcieOutByte_finalOffLN_Z)
  sameTy "finalOffLN_Z" t (C (Q ++ `FZ))
  unless binderInfos (← norm t) == binderInfos (← norm (C (Q ++ `FZ))) do throwError "finalOffLN_Z: binder kinds differ"
  let ap (ob cv cl gt : Lean.Expr) : Lean.Expr := mkApp4 (C (Q ++ `ExpFLN)) ob cv cl gt
  let ob := C ``HftObCDZ
  let cvZ := C ``cdvZ
  let cl := C (Q ++ `ClT)
  let gt := C (Q ++ `GtT)
  let muts : List (String × Lean.Expr) := [
    ("no closing premise", ap ob cvZ (C (Q ++ `ClNone)) gt), ("closing of another shape", ap ob cvZ (C (Q ++ `ClOther)) gt),
    ("no gate premise", ap ob cvZ cl (C (Q ++ `GtNone))), ("gate = constant true", ap ob cvZ cl (C (Q ++ `GtConst))), ("gate of another root", ap ob cvZ cl (C (Q ++ `GtOther))),
    ("carrier Y", ap ob (C ``cdvY) cl gt), ("carrier old", ap ob (C ``cdvOld) cl gt), ("obligation Y", ap (C ``HftObCDY) cvZ cl gt),
    ("hnoraw kept (S1u statement)", mkApp2 (C (U ++ `HftFinalStmtOffL)) ob cvZ)]
  for (what, m) in muts do
    diffTy s!"finalOffLN_Z vs {what}" t m; nm := nm + 1
  -- the general theorem against its definition
  logInfo m!"FGCIRCUIT20 SIGNATURES-B2: synth_hftPcieOutByte_finalOffLN_Z (hnoraw replaced by hcl + hgate) matches the independently written ExpFLN; {nm} mutants rejected (no closing / other shape / no gate / constant gate / other root's gate / carrier Y, old / obligation Y / hnoraw kept)"

/-! ## 3. HYPS -/

run_cmd liftTermElabM do
  let env ← getEnv
  let X := `Tools.ShippingFGCircuitS1xNoRaw
  let ci ← getConstInfo (X ++ `synth_hftPcieOutByte_finalOffLN_Z)
  let some ty ← unfoldDefinition? ci.type | throwError "the instance's type is not a definition"
  let names ← forallTelescope ty fun xs _ => do
    let mut hs : List (String × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, ← instantiateMVars d.type)]
    return hs
  let expected := ["hlink", "L", "lvl", "env₀", "hstart", "hr", "hcell", "hchk", "hreadH", "hreadT", "hcd", "htop", "hcl", "hgate"]
  unless names.map (·.1) == expected do throwError "hypotheses are {names.map (·.1)}, expected {expected}"
  for gone in ["hnoraw", "hsrc", "hhead", "hdRun", "hquiet", "hg", "hio", "hgates", "hRead", "hE", "hP", "hdesign"] do
    if (names.map (·.1)).contains gone then throwError "{gone} is a hypothesis"
  let diag : List Name := [``synthesizeCombinational, ``synthesizeCombinationalCore, ``synthesizeEntry, ``Tools.ShippingFGCircuitLinked.MachineDefinesLinked, ``Tools.ShippingFGCircuitBridge.PostRun,
    ``Tools.ShippingEntryReadsLinked.coreHead, ``synthesizeChild, ``HftObSrc, ``sorryAx]
  for (n, t) in names do
    let mut used := t.getUsedConstants
    for c in t.getUsedConstants do
      if c.toString.startsWith "Tools.ShippingFGCircuitS1t" || c.toString.startsWith "Tools.ShippingFGCircuitS1kStmt" || c.toString.startsWith "Tools.ShippingFGCircuitS1u" || c.toString.startsWith "Tools.ShippingFGCircuitS1x" then
        match env.find? c with
        | some (.defnInfo dd) => used := used ++ dd.value.getUsedConstants
        | _ => pure ()
    for b in diag do
      if used.contains b then throwError "hypothesis {n} mentions {b}"
    if n == "hcl" || n == "hgate" then
      let pp ← try pure (toString (← ppExpr t)) catch _ => pure s!"<constants: {t.getUsedConstants.toList.map (·.toString)}>"
      logInfo m!"FGCIRCUIT20 REMAINING {n} : {pp}"
  -- hcl is MachineCloses of the root's shape; hgate is HftPostGate
  let some (_, hcl) := names.find? (·.1 == "hcl") | throwError "hcl missing"
  unless hcl.getUsedConstants.contains ``Tools.ShippingMachineEntry.MachineCloses do throwError "hcl is not MachineCloses"
  let some (_, hg) := names.find? (·.1 == "hgate") | throwError "hgate missing"
  unless hg.getUsedConstants.contains (X ++ `HftPostGate) do throwError "hgate is not HftPostGate"
  logInfo m!"FGCIRCUIT20 HYPS: HftFinalStmtOffLN Ob CV = hlink L lvl env₀ hstart hr(synthesizeCombinationalOff) hcell hchk hreadH hreadT hcd htop(HftObTopCoreOff) hcl(MachineCloses of the root's shape: the closing is not none; D.T-4) hgate(HftPostGate: hierGate of the post-processed IR top; D.T-4): {names.length} explicit hypotheses (S1u: hnoraw is gone, hcl and hgate in its place). hnoraw is DERIVED (hftObNoRawOff_of_run) from the machine boundary of the core run (derived inside from hchk/hcell as in S1t), hcl and hgate; neither mentions a diagnostic entry in the limited scan (the types and a one-level unfolding of the S1t/S1kStmt/S1u/S1x definitions; NOT the whole dependency closure)"

/-! ## 4. AXIOMS -/

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS1xNoRaw
  let names : List Name := [X ++ `coreOff_closed, X ++ `coreOff_noRawBelow, X ++ `dropZeroWidth_inst_target, X ++ `post_inst_target, X ++ `noB_of_post, X ++ `noRawBelow_opt,
    X ++ `hftShape_insts_ne, X ++ `hftObNoRawOff_of_run, X ++ `synth_hftPcieOutByte_finalOffLN, X ++ `synth_hftPcieOutByte_finalOffLN_Z, X ++ `synth_hftPcieOutByte_finalOffLN_Y, X ++ `synth_hftPcieOutByte_finalOffLN_X]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT20 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 5. SNAPSHOT20 -/

example : synth_hftPcieOutByte.machineData.shape.insts.length = 2 := by decide +kernel
example : synth_hftPcieOutByte.machineData.shape.insts.map (·.1) = [hftHttp, hftTlp] := by decide +kernel

run_cmd liftTermElabM do
  let env ← getEnv
  let NmRoot : Name := `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte
  -- the root still has no `machine_closes`: `hcl` is a named hypothesis; the four leaf roots have it (derivable there)
  if env.contains (NmRoot ++ `machine_closes) then throwError "the root now has machine_closes: hcl is derivable; update §26"
  for n in [`Sparkle.Tests.SignalLoopTest.counterLoop] do
    unless env.contains (n ++ `machine_closes) do throwError "{n}: no machine_closes"
  logInfo m!"FGCIRCUIT20 SNAPSHOT20: the root has two calls (httpGetByte, tlpCplByte; kernel decide), so the core run ends in closeInsts/closeInstsG (shape.insts ≠ []); the root has no machine_closes (hcl is a named hypothesis; D.T-4); a leaf root has it"

end Tests.Gen5.FGCircuitPilotCheck20
