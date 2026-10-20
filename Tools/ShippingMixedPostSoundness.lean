import Tools.ShippingMixedEntrySoundness
import Tools.ShippingOptSoundness

/-! The actual mixed synthesis entry, cleanup and checked optimizer compose.
Neither readiness nor bounded physical inputs are caller-supplied certificates:
the raw entry derives both from source inputs and the real compilation run. -/
namespace Tools.ShippingMixedPostSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.OptCheck Sparkle.IR.RegDedup Sparkle.IR.ZeroWidth
open Tools.ShippingEntrySoundness Tools.ShippingPostSoundness Tools.ShippingTypedPostSoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingOptSoundness

/-- Both branches inside the checked shape gate preserve outputs. The mixed
entry derives this gate; the compiler's unchecked outside-gate path is not
covered by this theorem. -/
theorem checkedOptimize_flat_sound {m : Sparkle.IR.AST.Module} {mems : MEnv} {initial result : Env}
    (shape : SimpleStmts m.body)
    (bounds : ∀ p ∈ m.inputs, initial p.name < 2 ^ weOf m p.name)
    (run : evalAssigns (weOf m) mems m.body initial = some result) :
    ∃ final, evalAssigns (weOf (checkedOptimize m)) mems (checkedOptimize m).body initial = some final ∧
      (∀ p ∈ m.outputs, final p.name = result p.name) ∧
      (checkedOptimize m).inputs = m.inputs ∧ (checkedOptimize m).outputs = m.outputs := by
  apply checkedOptimize_sound (simpleBody_of m shape) ?_ run
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact bounds p hp

/-- Cleanup and checked merging leave the scalar declaration widths unchanged.
The evaluation premise is supplied by the source entry when this is composed. -/
theorem typed_postprocess_widths {m m' : Sparkle.IR.AST.Module}
    (h : TypedPostReady m)
    (hm : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m))
    {mems : MEnv} {initial result : Env}
    (run : evalAssigns (weOf m) mems m.body initial = some result) : weOf m' = weOf m := by
  obtain ⟨body, widths, _, _, typed⟩ := dropZeroWidth_typed h
  rcases hm with rfl | rfl
  · exact widths
  · have run' : evalAssigns (weOf (dropZeroWidthModule m)) mems (dropZeroWidthModule m).body initial = some result := by
      rw [body, widths]; exact run
    obtain ⟨_, wires, _⟩ := mergeDuplicates_sound _ mems initial result typed.isAssign run'
    unfold weOf
    rw [wires]
    exact widths

/-- All actual postprocessing choices and both checked-optimizer branches.
The result concerns precisely the module passed to the Verilog printer. -/
theorem mixed_postprocess_checked {declName bs body m m'}
    (source : MixedPreserves declName bs body m)
    (post : m' = dropZeroWidthModule m ∨ m' = mergeDuplicates (dropZeroWidthModule m)) :
    MixedSourcePreserves declName bs body fun initial mems expected =>
      ∃ result, evalAssigns (weOf (checkedOptimize m')) mems (checkedOptimize m').body initial = some result ∧
        result "out" = expected ∧ "out" ∈ (checkedOptimize m').outputs.map (·.name) := by
  apply MixedSourcePreserves.map source
  intro initial mems expected h
  obtain ⟨result, run, value, ready, simple, widths, out, bounds, _⟩ := h
  rw [← widths] at run
  have postWidths := typed_postprocess_widths ready post run
  obtain ⟨run', _, inputs, outputs⟩ := typed_postprocess_sound ready post mems initial result run
  have bounds' : ∀ p ∈ m'.inputs, initial p.name < 2 ^ weOf m' p.name := by
    rw [inputs, postWidths]; exact bounds
  have simple' : SimpleStmts m'.body := by
    have sd : SimpleStmts (dropZeroWidthModule m).body := by rw [(dropZeroWidth_typed ready).1]; exact simple
    rcases post with rfl | rfl
    · exact sd
    · exact mergeDuplicates_simple _ sd
  obtain ⟨final, finalRun, agrees, _, finalOutputs⟩ := checkedOptimize_flat_sound simple' bounds' run'
  obtain ⟨port, hp, name⟩ := List.mem_map.mp out
  have val := agrees port (outputs ▸ hp)
  rw [name, value] at val
  refine ⟨final, finalRun, val, ?_⟩
  rw [finalOutputs, outputs]
  exact List.mem_map.mpr ⟨port, hp, name⟩

/-- Successful shipping synthesis, including its actual postprocessing, followed
by the exact optimizer used by `verilogOf`. The declaration is the one read in
this execution. Source quotation/input correspondence and EnvDefines remain
explicit, as in the raw mixed entry theorem. -/
theorem synthesizeCombinational_mixed_checked {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        (∀ isInst, mixedCertifiedShape? false [] ci isInst = some (bs, body)) →
        MixedSourcePreserves declName bs body fun initial mems expected =>
          ∃ result, evalAssigns (weOf (checkedOptimize m)) mems (checkedOptimize m).body initial = some result ∧
            result "out" = expected ∧ "out" ∈ (checkedOptimize m).outputs.map (·.name) := by
  obtain ⟨raw, design, world, core, post⟩ := synthesizeCombinational_reads hr
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_mixed_sound core
  exact ⟨ci, w1, w2, get, fun bs body old shape => mixed_postprocess_checked (source bs body old shape) post⟩

end Tools.ShippingMixedPostSoundness
