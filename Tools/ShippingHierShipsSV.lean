import Tools.ShippingHierSVRun
import Tools.ShippingHierPremisesBase
import Tools.ShippingMachineShipsHier

/-! # From the shipped module's linked run to its emitted Verilog

The shipping theorems for machines with instances end at the shipped
module's linked run from the full entry's seeding (`seedIn b ins`, `b` the
full entry's module, `checkedOptimize b` the shipped one). `linked_sv_of_run`
turns a linked run of a module, from ITS seeding, into the run of its emitted
Verilog. The two meet because the shipped module keeps `b`'s inputs whenever
the instance gate binds (`checkedOptimize_inputs`). `shipped_sv` is the
result: the shipped module's emitted Verilog, from the oracle seeding, runs
to the very environments of the linked run the shipping theorem gives —
under the decidable emitted-Verilog premises of the shipped module and the
children's output bound. -/
namespace Tools.ShippingHierShipsSV
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Sparkle.IR.OptCheck (checkedOptimize)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierOptRun
open Tools.ShippingSeqOptSoundness (seedIn)

/-- The optimizer check keeps the inputs. -/
theorem hierRefineCheck_inputs {m o : Module}
    (h : Sparkle.IR.RefineCheck.hierRefineCheck m o = true) : o.inputs = m.inputs := by
  simp only [Sparkle.IR.RefineCheck.hierRefineCheck, Bool.and_eq_true] at h
  obtain ⟨_, hrc⟩ := h
  simpa [Sparkle.IR.HierCheck.openFlat] using (Tools.ShippingRefineSoundness.refineCheck_ports hrc).1

/-- **The shipped module keeps the full entry's inputs**, where the
instance gate binds. -/
theorem checkedOptimize_inputs {b : Module} (hb : Sparkle.IR.RefineCheck.hierBinds b = true) :
    (checkedOptimize b).inputs = b.inputs := by
  have hI := Tools.ShippingMachineShipsHier.hasInst_of_hierBinds hb
  have hopt : checkedOptimize b = (if Sparkle.IR.RefineCheck.hierRefineCheck b
      (Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b))
      then Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b) else b) := by
    unfold checkedOptimize
    simp only [Tools.ShippingMachineShipsHier.simpleBody_inst hI,
      Tools.ShippingMachineShipsHier.not_all_seqOk hI, hb, Bool.false_eq_true, if_false, if_true]
  rw [hopt]
  split
  · rename_i h; exact hierRefineCheck_inputs h
  · rfl

theorem seedIn_eq {m₁ m₂ : Module} (h : m₁.inputs = m₂.inputs) (ins : Nat → String → Nat) :
    seedIn m₁ ins = seedIn m₂ ins := by
  unfold seedIn; rw [h]

/-- **The shipped module's emitted Verilog runs as its linked run.** For a
linked run of `o = checkedOptimize b` from the full entry's seeding (what
`machine_ships_hier` / `_hierN` give), the emitted Verilog of `o`, from the
oracle seeding (the instance outputs at each cycle the values the children
drove), runs to the same environments. -/
theorem shipped_sv {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv))
    {b : Module} {wof : String → Option Nat} (Inv : Module → σ → Prop)
    (hchk : Tools.ShippingHierPremisesBase.hierCheck children b = true)
    (hKSb : KSBoundedIn children KS (checkedOptimize b).body Inv)
    (hIW : instOutWidthsOk children (declWidth (checkedOptimize b)) (checkedOptimize b).body = true)
    (hOut : ∀ w ∈ bodyInstOuts children (checkedOptimize b).body,
      w ∈ (Sparkle.IR.HierCheck.openIns (checkedOptimize b)).map (·.name))
    (hOW : ∀ w ∈ bodyInstOuts children (checkedOptimize b).body,
      declWidth (checkedOptimize b) w ≤ Tools.SVParser.EmitSem.weOf wof w)
    (hok : (checkedOptimize b).body.all Tools.ShippingHierSVSoundness.seqStmtOkI = true)
    (hsv : Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof)
      (checkedOptimize b).body = true)
    (hwag : ∀ n ∈ Tools.ShippingSeqSVSoundness.seqNames (checkedOptimize b).body,
      declWidth (checkedOptimize b) n = Tools.SVParser.EmitSem.weOf wof n)
    (ins : Nat → String → Nat)
    (hinsW : ∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.SVParser.EmitSem.weOf wof x)
    {T : Nat} {s : KState σ} {envs : List Env}
    (hrun : runModuleTG KS (declWidth (checkedOptimize b)) children (checkedOptimize b).body
      (seedIn b ins) T s = some envs)
    (hinv : ∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body → ∀ child cwe,
      children mn = some (child, cwe) → Inv child (s.kids iname))
    (hstX : ∀ x ∈ (Sparkle.IR.HierCheck.openIns (checkedOptimize b)).map (·.name),
      x ∉ bodyInstOuts children (checkedOptimize b).body → s.st x < 2 ^ declWidth (checkedOptimize b) x)
    (hst : Bounded (Tools.SVParser.EmitSem.weOf wof) s.st) :
    ∃ pairs regs mprog,
      Tools.SVParser.EmitSem.emitAssigns wof (checkedOptimize b).body = some pairs ∧
      Tools.SVParser.EmitSem.emitRegs wof (checkedOptimize b).body = some regs ∧
      Tools.SVParser.EmitSem.emitMemWrites wof (checkedOptimize b).body = some mprog ∧
      Tools.SVParser.EmitSem.runModuleSV wof pairs regs mprog
        (Tools.ShippingHierSVRun.oracle children (checkedOptimize b).body
          (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) (seedIn b ins)) T
        s.st s.mems = some envs := by
  have hF := Tools.ShippingHierPremisesBase.hierCheck_sound hchk
  have hin := checkedOptimize_inputs hF.binds
  have hseed := seedIn_eq hin ins
  rw [← hseed] at hrun ⊢
  exact Tools.ShippingHierSVRun.linked_sv_of_run KS children Inv hKSb hF.wfO hF.ndO hIW hOut hOW
    hok hsv hwag ins (by rw [hin]; exact hinsW) hrun hinv hstX hst

end Tools.ShippingHierShipsSV
