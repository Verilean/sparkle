/-
  Sparkle.Verification.CostCmd — `#verify_cost` and
  `#verify_fpga` commands.

  `#verify_cost <fn> <budget>` — generic area/depth budget,
  cost-model-agnostic.  See `Cost.Budget`.

      def myAdder (a b : Signal _ (BitVec 16)) : Signal _ (BitVec 16) :=
        Signal.map₂ (· + ·) a b
      #verify_cost myAdder { area := 32, depth := 16 }

  `#verify_fpga <fn> <target>` — FPGA-fit check.  Estimates
  LUT / FF / BRAM / DSP usage and asserts each stays under
  the part's published ceiling.  See `CostTargets` for
  available targets (`tangNano9K`, `tangNano50K`).

      #verify_fpga sha256Block Sparkle.Verification.Cost.Targets.tangNano50K

  Both commands run at command-elab time — budget overruns
  abort `lake build` and surface as CI gates, mirroring how
  `#synthesizeVerilog` gates on synthesis errors.
-/
import Lean
import Lean.Elab.Command
import Sparkle.Verification.Cost
import Sparkle.Verification.CostTargets
import Sparkle.Compiler.Elab

namespace Sparkle.Verification.CostCmd

open Lean Elab Command
open Sparkle.Verification.Cost
open Sparkle.Verification.Cost.Targets

/-- Internal: evaluate a Budget literal at elab time. -/
private unsafe def evalBudgetImpl (e : Expr) : Lean.Meta.MetaM Budget :=
  Lean.Meta.evalExpr Budget (mkConst ``Budget) e

@[implemented_by evalBudgetImpl]
private opaque evalBudget (e : Expr) : Lean.Meta.MetaM Budget

/-- Internal: evaluate a Target literal at elab time. -/
private unsafe def evalTargetImpl (e : Expr) : Lean.Meta.MetaM Target :=
  Lean.Meta.evalExpr Target (mkConst ``Target) e

@[implemented_by evalTargetImpl]
private opaque evalTarget (e : Expr) : Lean.Meta.MetaM Target

/-- `#verify_cost <ident> <budget>` — generic area/depth check. -/
syntax (name := verifyCostCmd) "#verify_cost " ident term : command

@[command_elab verifyCostCmd]
def elabVerifyCost : CommandElab := fun stx => do
  match stx with
  | `(#verify_cost $id:ident $budgetStx:term) => do
    let declName ← liftCoreM <| Lean.resolveGlobalConstNoOverload id
    let (mod, design) ← liftTermElabM do
      Sparkle.Compiler.Elab.synthesizeCombinational declName
    let budget ← liftTermElabM do
      let e ← Term.elabTermAndSynthesize budgetStx (some (mkConst ``Budget))
      evalBudget e
    let report := analyze CostModel.default mod design budget
    let label := s!"`{declName}`"
    let areaTag :=
      if report.budget.area = 0 then s!"area = {report.area} (unbudgeted)"
      else if report.areaOk    then s!"area = {report.area} (≤ {report.budget.area})"
      else                          s!"area = {report.area} (> {report.budget.area})"
    let depthTag :=
      if report.budget.depth = 0 then s!"depth = {report.depth} (unbudgeted)"
      else if report.depthOk    then s!"depth = {report.depth} (≤ {report.budget.depth})"
      else                           s!"depth = {report.depth} (> {report.budget.depth})"
    if report.ok then
      logInfoAt id m!"✅ verified: {label} — {areaTag}, {depthTag}"
    else
      throwErrorAt id m!"❌ violated: {label} — {areaTag}, {depthTag}"
  | _ => throwUnsupportedSyntax

/-- `#verify_fpga <ident> <target>` — FPGA-fit check. -/
syntax (name := verifyFpgaCmd) "#verify_fpga " ident term : command

@[command_elab verifyFpgaCmd]
def elabVerifyFpga : CommandElab := fun stx => do
  match stx with
  | `(#verify_fpga $id:ident $targetStx:term) => do
    let declName ← liftCoreM <| Lean.resolveGlobalConstNoOverload id
    let (mod, design) ← liftTermElabM do
      Sparkle.Compiler.Elab.synthesizeCombinational declName
    let target ← liftTermElabM do
      let e ← Term.elabTermAndSynthesize targetStx (some (mkConst ``Target))
      evalTarget e
    let usage : Resources := moduleResources mod + designResources design
    let fits :=
      usage.lut ≤ target.maxLUT
      ∧ usage.ff ≤ target.maxFF
      ∧ usage.bsram9k ≤ target.maxBSRAM9k
      ∧ usage.dsp18x18 ≤ target.maxDSP18x18
    let depth := Nat.max
      (moduleDepth CostModel.default mod)
      (designDepth CostModel.default design)
    let fmaxTag : String :=
      if depth = 0 then "Fmax_est = ∞ (purely combinational, no registered path)"
      else
        let picoSec := depth * target.picoSecPerUnit
        let mhz := 1000000 / picoSec
        s!"Fmax_est ≈ {mhz} MHz (depth = {depth})"
    let label := s!"`{declName}`"
    let tag (used max : Nat) (name : String) : String :=
      let pct := if max = 0 then 0 else used * 100 / max
      if used ≤ max then s!"{name} {used}/{max} ({pct}%)"
      else                s!"{name} {used}/{max} (OVER by {used - max})"
    let lutT := tag usage.lut target.maxLUT "LUT"
    let ffT := tag usage.ff target.maxFF "FF"
    let bsT := tag usage.bsram9k target.maxBSRAM9k "BSRAM9k"
    let dspT := tag usage.dsp18x18 target.maxDSP18x18 "DSP"
    if fits then
      logInfoAt id m!"✅ fits {target.name}: {label} — {lutT}, {ffT}, {bsT}, {dspT}, {fmaxTag}"
    else
      throwErrorAt id m!"❌ overflow on {target.name}: {label} — {lutT}, {ffT}, {bsT}, {dspT}, {fmaxTag}"
  | _ => throwUnsupportedSyntax

end Sparkle.Verification.CostCmd
