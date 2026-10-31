import Tools.ShippingGen4FbPP
import Tools.ShippingPostSoundness
set_option autoImplicit false
-- BUILT (unit FB-20): kjob lake build Tools.ShippingGen4FbDzRun exit 0 (702 jobs) at cd693e12 in the Pod; clean issue-linked build fb20v-cc9890f2 exit 0 (814 jobs, dirty=false), approved at cc9890f2. Written against scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §29.3 (committed d283cd0d before this file).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # FB-19: `ChildRunN` run transport across the zero-width clean-up, instance-free body

Partial supply: only bodies without instance statements, and only the arm of `PPRel` that is the clean-up. It does not
say which arm holds nor what the module computes. -/

namespace Tools.ShippingGen4FbDzRun
open Lean Meta Sparkle.IR.AST Sparkle.IR.Machine Sparkle.Compiler.Elab
open Tools.ShippingGen2 Tools.ShippingMachineDepth Tools.ShippingHierStateG
open Tools.ShippingSeqOptSoundness (seedIn)

theorem childRunN_dz_instFree
    {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat}
    {raw out : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hbody : out.body = raw.body) (hin : out.inputs = raw.inputs) (hout : out.outputs = raw.outputs)
    (hwe : Sparkle.IR.RegDedup.declWidth out = Sparkle.IR.RegDedup.declWidth raw)
    (hf : Tools.ShippingHierStateG.instFree raw.body)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S) :
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n out bsC outsC S := by
  have hfo : instFree out.body := by rw [hbody]; exact hf
  have hreset : ∀ (m : Nat) (s : KT m), ResetN dsn₂ m out s → ResetN dsn₁ m raw s := by
    intro m s hr
    cases m with
    | zero =>
      obtain ⟨a, b, c, -⟩ := hr
      refine ⟨?_, b, ?_, trivial⟩
      · intro r c' rs inp init hm
        exact a r c' rs inp init (by rw [hbody]; exact hm)
      · intro nm aw dw c' wa wd we ra rd cr ew er hm
        exact c nm aw dw c' wa wd we ra rd cr ew er (by rw [hbody]; exact hm)
    | succ k =>
      obtain ⟨a, b, c, -⟩ := hr
      refine ⟨?_, b, ?_, ?_⟩
      · intro r c' rs inp init hm
        exact a r c' rs inp init (by rw [hbody]; exact hm)
      · intro nm aw dw c' wa wd we ra rd cr ew er hm
        exact c nm aw dw c' wa wd we ra rd cr ew er (by rw [hbody]; exact hm)
      · intro mn iname conns mc' hm
        have := hf _ hm
        simp [Sparkle.IR.Machine.isInst] at this
  have hseed : seedIn out = seedIn raw := by
    funext ins t st x
    unfold seedIn
    rw [hin]
  have hrun : ∀ (ins : Nat → String → Nat) (T : Nat) (s : KT n),
      RunOn ch₂ n out (seedIn out ins) T s = RunOn ch₁ n raw (seedIn raw ins) T s := by
    intro ins T s
    rw [RunOn_instFree ch₂ out hfo (seedIn out ins) n T s,
      RunOn_instFree ch₁ raw hf (seedIn raw ins) n T s, hbody, hwe, hseed]
  have hap : Tools.ShippingMachineCompose.argPorts out = Tools.ShippingMachineCompose.argPorts raw := by
    unfold Tools.ShippingMachineCompose.argPorts; rw [hin]
  rcases h with ⟨a1, a2, a3, a4, a5, a6, a7⟩ | ⟨a1, a2, a3, a4, a5, a6, a7⟩
  · refine Or.inl ⟨by rw [hout]; exact a1, by rw [hin]; exact a2, by rw [hin]; exact a3,
      by rw [hin]; exact a4, by rw [hout, hin]; exact a5, by rw [hap]; exact a6, ?_⟩
    intro T ins s vals hr hp hrst hclk hres
    rw [hap] at hp
    rw [hrun ins T s]
    exact a7 T ins s vals hr hp hrst hclk (hreset n s hres)
  · refine Or.inr ⟨by rw [hout]; exact a1, by rw [hin]; exact a2, by rw [hin]; exact a3,
      by rw [hin]; exact a4, by rw [hout, hin]; exact a5, by rw [hap]; exact a6, ?_⟩
    intro T ins s vals hr hp hres
    rw [hap] at hp
    rw [hrun ins T s]
    exact a7 T ins s vals hr hp (hreset n s hres)

theorem childRunN_dz_postReady
    {ch₁ ch₂ : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn₁ dsn₂ : Sparkle.IR.AST.Design} {n : Nat} {k : Nat} {raw : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {outsC : List Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hk : 0 < k) (hpr : Tools.ShippingEntrySoundness.PostReady raw k)
    (hf : Tools.ShippingHierStateG.instFree raw.body)
    (h : Tools.ShippingGen2.ChildRunN ch₁ dsn₁ n raw bsC outsC S) :
    Tools.ShippingGen2.ChildRunN ch₂ dsn₂ n (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) bsC outsC S := by
  obtain ⟨hb, hw, hi, ho, -⟩ := Tools.ShippingPostSoundness.dropZeroWidth_entry raw k hk hpr
  have hdw : ∀ M : Sparkle.IR.AST.Module, Sparkle.IR.RegDedup.declWidth M = Tools.ShippingEntrySoundness.weOf M :=
    fun _ => rfl
  exact childRunN_dz_instFree hb hi ho (by rw [hdw, hdw]; exact hw) hf h

end Tools.ShippingGen4FbDzRun
