import Tools.ShippingFGCircuitS2aClose
set_option autoImplicit false
-- FG circuit pilot S2a check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §29.

/-! # FGCircuitPilotCheck24 (light: each part is a small `run_cmd`)

1. SIGNATURES-A: `HftKidsDefine` against an independently written `ExpKD`; controls: another child, swapped, both the same, another shape, one conjunct only.
2. SIGNATURES-B: `hftCoreCloses_of_kids`, `synth_hftPcieOutByte_finalOffLNK_Z`; HYPS (13 names; `hclL` is not a hypothesis, `hkids` is last).
3. CONTROLS: the pure closing checks on small modules (a combinational child passes; a sequential child, an unconnected input, an instance of the parent fail) and the root's data checks (another `nDecl`, another argument count fail).
4. REMAINING, AXIOMS. -/
namespace Tests.Gen5.FGCircuitPilotCheck24
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuitS2aClose
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine

abbrev Cx := Meta.Context
abbrev Rf1 := ST.Ref IO.RealWorld Meta.State
abbrev Cc := Core.Context
abbrev Rf2 := ST.Ref IO.RealWorld Core.State
noncomputable def RootShape : MachineShape := synth_hftPcieOutByte.machineData.shape
noncomputable def OtherShape : MachineShape := Sparkle.Tests.SignalLoopTest.counterLoop.machineData.shape
noncomputable def HttpShape : MachineShape := Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape
noncomputable def TlpShape : MachineShape := Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.shape

/-! ## 1. HftKidsDefine, independently -/

/-- the reflection of two called declarations (name, shape) in the run's contexts, written again -/
def ExpKD (n1 n2 : Name) (s1 s2 : MachineShape) (mctx : Cx) (mref : Rf1) (cctx : Cc) (cref : Rf2) : Prop :=
  MachineDefines mctx mref cctx cref n1 s1 ∧ MachineDefines mctx mref cctx cref n2 s2
def http : Name := ``Sparkle.IP.Net.HTTP.httpGetByte
def tlp : Name := ``Sparkle.IP.Bus.PCIe.tlpCplByte
noncomputable def KDRoot : Cx → Rf1 → Cc → Rf2 → Prop := ExpKD http tlp HttpShape TlpShape
noncomputable def KDSwapped : Cx → Rf1 → Cc → Rf2 → Prop := ExpKD tlp http HttpShape TlpShape
noncomputable def KDBothHttp : Cx → Rf1 → Cc → Rf2 → Prop := ExpKD http http HttpShape HttpShape
noncomputable def KDBothTlp : Cx → Rf1 → Cc → Rf2 → Prop := ExpKD tlp tlp TlpShape TlpShape
noncomputable def KDOtherShape : Cx → Rf1 → Cc → Rf2 → Prop := ExpKD http tlp OtherShape TlpShape
noncomputable def KDRootShape : Cx → Rf1 → Cc → Rf2 → Prop := ExpKD http tlp HttpShape RootShape
noncomputable def KDOtherChild : Cx → Rf1 → Cc → Rf2 → Prop := ExpKD http ``Sparkle.Tests.SignalLoopTest.counterLoop HttpShape OtherShape
noncomputable def KDOne : Cx → Rf1 → Cc → Rf2 → Prop := fun mctx mref cctx cref => MachineDefines mctx mref cctx cref http HttpShape
noncomputable def KDTrue : Cx → Rf1 → Cc → Rf2 → Prop := fun _ _ _ _ => True

def normOnce (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if c == ``HftKidsDefine || (`Tests.Gen5.FGCircuitPilotCheck24).isPrefixOf c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:5] do
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

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS2aClose
  let Q := `Tests.Gen5.FGCircuitPilotCheck24
  sameTy "HftKidsDefine" (C (X ++ `HftKidsDefine)) (C (Q ++ `KDRoot))
  let mut nm : Nat := 0
  for mu in ["KDSwapped", "KDBothHttp", "KDBothTlp", "KDOtherShape", "KDRootShape", "KDOtherChild", "KDOne", "KDTrue"] do
    diffTy s!"HftKidsDefine vs {mu}" (C (X ++ `HftKidsDefine)) (C (Q ++ Name.mkSimple mu)); nm := nm + 1
  logInfo m!"FGCIRCUIT24 SIGNATURES-A: HftKidsDefine matches the independently written ExpKD http tlp (MachineDefines of httpGetByte and tlpCplByte at their generated shapes, in the run's contexts); {nm} mutants rejected (swapped, both httpGetByte, both tlpCplByte, another shape, the root's shape, another child, one conjunct, True)"

/-! ## 2. the closing and the final statement -/

partial def binderNames : Lean.Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2aClose
  let mut nm : Nat := 0
  -- hftCoreCloses_of_kids: premises Start L, HftKidsDefine; conclusion HftCoreCloses at the same world
  let t ← tyOf (X ++ `hftCoreCloses_of_kids)
  let names := binderNames (← instantiateMVars t) |>.map (·.toString)
  unless names == ["mctx", "mref", "cctx", "cref", "L", "w", "hstart", "hk"] do throwError "hftCoreCloses_of_kids binders: {names}"
  let ty := t
  let uses := ty.getUsedConstants
  for c in [``Tools.ShippingGen2.Start, ``HftKidsDefine, ``HftCoreCloses] do
    unless uses.contains c do throwError "hftCoreCloses_of_kids does not mention {c}"
  for bad in [``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingChildRunAKids.MachineClosesAtA, ``CoreCloses] do
    if uses.contains bad then throwError "hftCoreCloses_of_kids mentions {bad}"
  nm := nm + 3
  -- the final statement: 13 hypotheses, `hclL` replaced by `hkids`
  let t2 ← tyOf (X ++ `synth_hftPcieOutByte_finalOffLNK_Z)
  let some ty2 ← unfoldDefinition? t2 | throwError "the instance's type is not a definition"
  let hs ← forallTelescope ty2 fun xs _ => do
    let mut hs : List (String × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, ← instantiateMVars d.type)]
    return hs
  let expected := ["hlink", "L", "lvl", "env₀", "hstart", "hr", "hcell", "hchk", "hreadH", "hreadT", "hcd", "htop", "hkids"]
  unless hs.map (·.1) == expected do throwError "hypotheses are {hs.map (·.1)}, expected {expected}"
  for gone in ["hclL", "hcl", "hgate", "hnoraw", "hdRun", "hsrc", "hhead"] do
    if (hs.map (·.1)).contains gone then throwError "{gone} is a hypothesis"
  let some (_, hk) := hs.find? (·.1 == "hkids") | throwError "hkids missing"
  unless hk.getUsedConstants.contains ``HftKidsDefine do throwError "hkids is not HftKidsDefine"
  if hk.getUsedConstants.contains ``HftCoreCloses then throwError "hkids mentions HftCoreCloses"
  -- the S1z statement differs from it exactly in the last hypothesis
  let t3 ← tyOf (X.getPrefix ++ `ShippingFGCircuitS1zClose ++ `synth_hftPcieOutByte_finalOffLNL_Z)
  unless (← norm t3) != (← norm t2) do throwError "finalOffLNK_Z is the finalOffLNL_Z statement"
  nm := nm + 2
  logInfo m!"FGCIRCUIT24 SIGNATURES-B: hftCoreCloses_of_kids (premises Start L, HftKidsDefine; conclusion HftCoreCloses; no MachineCloses / MachineClosesAtA / CoreCloses premise) and synth_hftPcieOutByte_finalOffLNK_Z: {nm} structural checks; hypotheses {expected} (13, hclL replaced by hkids, which is HftKidsDefine and does not mention HftCoreCloses)"
  logInfo m!"FGCIRCUIT24 HYPS: HftFinalStmtOffLNK Ob CV = {expected}: {hs.length} explicit hypotheses"

/-! ## 3. CONTROLS: the pure closing checks on small modules (kernel-decided; the build fails if one flips) -/

def pt (n : String) : Port := { name := n, ty := .bitVector 8 }
/-- a combinational child: `o := a` -/
def kidComb : Sparkle.IR.AST.Module := { name := "kid", inputs := [pt "a"], outputs := [pt "o"], wires := [], body := [.assign "o" (.ref "a")] }
/-- a sequential child: a register -/
def kidSeq : Sparkle.IR.AST.Module := { kidComb with body := [.register "o" "clk" ("rst", .synchronous) (.ref "a") 0] }
/-- a child whose output port is not the one its body writes (another child output) -/
def kidOtherOut : Sparkle.IR.AST.Module := { kidComb with outputs := [pt "z"] }
/-- a call with a connected input / with a constant (not a wire) on the input -/
def callOk : List Stmt := [.inst "kid" "i0" [("a", .ref "x"), ("o", .ref "y")]]
def callBad : List Stmt := [.inst "kid" "i0" [("a", .const 1 8), ("o", .ref "y")]]
def parentInst : List Stmt := [.inst "parent" "i0" [("a", .ref "x")]]

theorem ctl_comb_ok : kidsCombB [kidComb] callOk = true := by decide +kernel
theorem ctl_seq_fails : kidsCombB [kidSeq] callOk = false := by decide +kernel
theorem ctl_unwired_fails : kidsCombB [kidComb] callBad = false := by decide +kernel
theorem ctl_other_output_fails : kidsCombB [kidOtherOut] callOk = false := by decide +kernel
theorem ctl_missing_fails : kidsCombB [] callOk = false := by decide +kernel
theorem ctl_noinst_ok : noInstOfB "parent" callOk = true := by decide +kernel
theorem ctl_parent_inst_fails : noInstOfB "parent" parentInst = false := by decide +kernel
theorem ctl_closeLets_noPacked : closeLets 1 { kidComb with inputs := [pt "a", pt "b"] } = none := by decide +kernel
theorem ctl_closeLets_zero : (closeLets 0 kidComb).isSome = true := by decide +kernel
-- the root: the real checks hold, another `nDecl` and another argument count fail
theorem ctl_root_gate_ok : synth_hftPcieOutByte.machineData.gateCallsOk (Tools.ShippingGen5Sem.kDOf synth_hftPcieOutByte.machineData) = true := hft_gateCalls
theorem ctl_root_gate_other : synth_hftPcieOutByte.machineData.gateCallsOk (Tools.ShippingGen5Sem.kDOf synth_hftPcieOutByte.machineData + 1) = false := by decide +kernel
theorem ctl_root_args_other : ¬ (∀ x ∈ synth_hftPcieOutByte.machineData.shape.insts, nkOf x.1 + 1 = x.2.1.length) := by decide +kernel
theorem ctl_root_alias_other : Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape.layout.lets ≠ 0 := by decide +kernel
theorem ctl_kid_not_root_name : ¬ (∀ x ∈ synth_hftPcieOutByte.machineData.shape.insts, x.1 = tlp) := by decide +kernel

run_cmd liftTermElabM do
  let Q := `Tests.Gen5.FGCircuitPilotCheck24
  let env ← getEnv
  let names := ["ctl_comb_ok", "ctl_seq_fails", "ctl_unwired_fails", "ctl_other_output_fails", "ctl_missing_fails", "ctl_noinst_ok", "ctl_parent_inst_fails", "ctl_closeLets_noPacked", "ctl_closeLets_zero",
    "ctl_root_gate_ok", "ctl_root_gate_other", "ctl_root_args_other", "ctl_root_alias_other", "ctl_kid_not_root_name"]
  for n in names do
    unless env.contains (Q ++ Name.mkSimple n) do throwError "{n} missing"
    for ax in ← Lean.collectAxioms (Q ++ Name.mkSimple n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{n} uses {ax}"
  logInfo m!"FGCIRCUIT24 CONTROLS: {names.length} kernel-decided controls (a combinational child passes kidsCombB; a sequential child, an unwired input, a child whose output is not written and a missing child fail it; an instance of the parent fails noInstOfB; closeLets refuses a module without the packed wire; the root's gateCallsOk holds at its nDecl and fails at another; the argument counts of another reading fail), standard axioms"

/-! ## 4. REMAINING, AXIOMS -/

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2aClose
  let c ← getConstInfo (X ++ `HftKidsDefine)
  let pp ← try pure (toString (← ppExpr c.value!)) catch _ => pure "<unprintable>"
  logInfo m!"FGCIRCUIT24 REMAINING hkids : HftKidsDefine mctx mref cctx cref := {pp}  (FG D.T-4, children's part: the reflection of the two called declarations in the run's contexts; hclL itself is DERIVED by hftCoreCloses_of_kids from Start L and hkids)"

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2aClose
  let names : List Name := [X ++ `machineChild_ifaceA, X ++ `machineChild_of_realA, X ++ `hft_kid_iface, X ++ `hft_closesAtA, X ++ `hftCoreCloses_of_kids, X ++ `hft_gateCalls, X ++ `hft_alias,
    X ++ `hft_argsN, X ++ `hft_kids_names, X ++ `hft_noparent, X ++ `hft_outs_head,
    X ++ `synth_hftPcieOutByte_finalOffLNK, X ++ `synth_hftPcieOutByte_finalOffLNK_Z, X ++ `synth_hftPcieOutByte_finalOffLNK_Y, X ++ `synth_hftPcieOutByte_finalOffLNK_X]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT24 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck24
