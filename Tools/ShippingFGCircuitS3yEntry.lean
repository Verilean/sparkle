import Tools.ShippingFGCircuitS3yGen
import Tools.ShippingGen5Acc
import Tools.ShippingEntrySoundness
set_option autoImplicit false
-- FG circuit pilot S3y, step 3: the CHECKED entry `certifiedEntryC` and its soundness `certifiedEntryC_sound` (G2).  The entry reads the declaration's `MachineData` in `MetaM` (`readData`: the front end's own `entry₀` + `machineShape?` + `dataOfAt lvl`, the pattern `RootReader` states), runs the EXISTING entry `synthesizeCombinationalCoreOff` unchanged, and returns its `(b, D)` only if `checkData d b && designOk b D`; otherwise it throws.  The soundness proof uses only the `RunsTo` inversions of `bind` / `if` / `throwError` / `pure`: no Laws, no CellPrem, no `hr`, no quiet/start premise, no binder for `SrcEq`/`ChildFn`/environment correspondence (`checkData` decides them on the run's own `d` and `(b, D)`).  Not proved: that the `d` read is the declaration's data (`DeclDenotes`), see docs §73.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §73.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3yEntry
open Lean Meta Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingFGCircuitS3yGen
open Tools.ShippingFGCircuitS3tSpec (designOk)
open Tools.ShippingGen5Acc (entry₀)
open Tools.ShippingGen5DataOf (dataOfAt)

/-- **the front end's reading of a declaration's `MachineData`** in `MetaM`.  There is NO function in `Sparkle/` that returns `MachineData` (it is a `Tools` structure; `Sparkle.Compiler.Elab.machineShape?` returns the `MachineShape` only, and the generated constants `f.machineData` come from the `#machine_endpoint` command).  This is the closest existing reading, the one `RootReader` states: the entry constant `entry₀ env X`, its `machineShape?`, and `dataOfAt lvl` on it (`lvl` is the reader's level function, a parameter: the soundness below holds for any). -/
def readData (lvl : Lean.Expr → Nat) (declName : Name) : MetaM MachineData := do
  let env ← getEnv
  match entry₀ env declName with
  | none => throwError "certified entry: no entry constant"
  | some E =>
    match (machineShape? false [] E (structEnv env)).bind (dataOfAt lvl E (structEnv env)) with
    | none => throwError "certified entry: no machine data"
    | some d => pure d

/-- **the checked entry**: the data the front end reads, the unchanged entry's `(b, D)`, and the check of exactly that pair -/
def certifiedEntryC (lvl : Lean.Expr → Nat) (declName : Name) :
    MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) := do
  let d ← readData lvl declName
  let (b, D) ← synthesizeCombinationalCoreOff declName
  unless checkData d b && designOk b D do throwError "certificate check failed"
  pure (b, D)

section Runs
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- a `pure` returns its value and keeps the world -/
theorem runsTo_pure {α : Type} {a r : α} {w w' : Void IO.RealWorld}
    (h : RunsTo (pure a : MetaM α) mctx mref cctx cref w r w') : r = a ∧ w' = w := by
  unfold RunsTo at h
  change EST.Out.ok a w = _ at h
  cases h; exact ⟨rfl, rfl⟩

/-- **G2, the entry connection**: a successful run of `certifiedEntryC` returns `(b, D)` such that (1) the same run read some `d` (a run of `readData`), (2) the unchanged entry ran from the world after that read and returned this `(b, D)`, (3) `checkData d b = true` and `designOk b D = true`, hence `DataShows d b` (G1).  No premise about the run beyond its success. -/
theorem certifiedEntryC_sound {lvl : Lean.Expr → Nat} {declName : Name} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (h : RunsTo (certifiedEntryC lvl declName) mctx mref cctx cref w (b, D) w') :
    ∃ (d : MachineData) (w₁ w₂ : Void IO.RealWorld),
      RunsTo (readData lvl declName) mctx mref cctx cref w d w₁ ∧
      RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w₁ (b, D) w₂ ∧
      checkData d b = true ∧ designOk b D = true ∧ DataShows d b := by
  unfold certifiedEntryC at h
  obtain ⟨d, w₁, h1, h⟩ := RunsTo.bind h
  obtain ⟨pr, w₂, h2, h⟩ := RunsTo.bind h
  obtain ⟨b', D'⟩ := pr
  dsimp only at h
  by_cases hc : (checkData d b' && designOk b' D') = true
  · rw [if_pos hc] at h
    obtain ⟨hr, -⟩ := runsTo_pure h
    have hbD : b' = b ∧ D' = D := by simpa using hr.symm
    obtain ⟨rfl, rfl⟩ := hbD
    simp only [Bool.and_eq_true] at hc
    exact ⟨d, w₁, w₂, h1, h2, hc.1, hc.2, checkData_sound d b' hc.1⟩
  · rw [if_neg hc] at h
    obtain ⟨u, w₃, h3, -⟩ := RunsTo.bind h
    exact (RunsTo.throwError_false h3).elim

end Runs

end Tools.ShippingFGCircuitS3yEntry
