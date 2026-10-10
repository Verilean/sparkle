import Tools.ShippingMachineEntry
import Tools.ShippingInlineSoundness
import Tools.ShippingChildKeeps

/-! # The reflection premises and the Meta / Core contexts

A child is synthesised in whatever contexts the translator has reached (a
handler under `withLocalDecl`, a telescope, a changed transparency), so the
child-side premises of the composed endpoints are asked in EVERY Meta and
Core context. What that costs, premise by premise:

* `MachineDefines`, `EntryDefines` — NOTHING. They speak of runs of
  `getConstInfo` and `getEnv` only. A successful run of either reads the
  environment out of the Core STATE and returns it (resp. the constant found
  in it); neither the Meta context (local context, transparency, …) nor the
  Core context enters the returned value or the end world. So a successful
  run in one pair of contexts is one in any other (`getEnv_ctx`,
  `getConstInfo_ctx` — the failing branch `throwUnknownConstant` reads the
  Core context's `ref`, but does not return), and the premise in one pair of
  contexts is the premise in every pair (`MachineDefines.ctx`,
  `EntryDefines.ctx`), over the same state references.
* `MachineCloses` and a child's own boundary — NOT transferred. They speak of
  runs of the machine synthesis itself, which does run under the contexts
  (local declarations, `whnf` at the context's transparency); nothing here
  says a run in one pair of contexts closes because a run in another does.
  They are asked in the contexts the child IS synthesised in
  (`Tools.ShippingChildInv.ChildRanIn`: the child's entry has a successful
  run there from a world satisfying the invariant) — every consumer holds
  such a run (`RealChild.ranIn`, or the run its per-call premise is about),
  so the restriction is derived from the run, not assumed of the contexts. -/
namespace Tools.ShippingReflectCtx
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingInlineSoundness
open Tools.ShippingChildInv

variable {mctx mctx' : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx cctx' : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- A read of the environment: the same run in any contexts. -/
theorem getEnv_ctx {w e w'}
    (h : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w e w') :
    RunsTo (Lean.getEnv : MetaM Environment) mctx' mref cctx' cref w e w' := h

/-- `throwUnknownConstant` does not return. -/
theorem throwUnknownConstant_not_runs {α : Type} (c : Name) {w a w'}
    (h : RunsTo (Lean.throwUnknownConstant c : MetaM α) mctx mref cctx cref w a w') : False := by
  unfold Lean.throwUnknownConstant at h
  obtain ⟨ref, w1, -, h⟩ := RunsTo.bind h
  unfold Lean.throwUnknownConstantAt Lean.throwUnknownIdentifierAt at h
  obtain ⟨msg, w2, -, h⟩ := RunsTo.bind h
  unfold Lean.throwErrorAt at h
  exact throwError_not_runs (mctx := mctx)
    (cctx := { cctx with ref := replaceRef ref cctx.ref }) msg h

/-- Two successful runs in sequence are a successful run of the bind. -/
theorem RunsTo.bind_intro {α β : Type} {m : MetaM α} {f : α → MetaM β} {w a w1 b w2}
    (h1 : RunsTo m mctx mref cctx cref w a w1) (h2 : RunsTo (f a) mctx mref cctx cref w1 b w2) :
    RunsTo (m >>= f) mctx mref cctx cref w b w2 := by
  unfold RunsTo at h1 h2 ⊢
  change (EST.bind (m mctx mref cctx cref) fun a => f a mctx mref cctx cref) w = _
  unfold EST.bind
  rw [h1]
  exact h2

/-- A successful `getConstInfo`: the same run in any contexts. -/
theorem getConstInfo_ctx (c : Name) {w ci w'}
    (h : RunsTo (Lean.getConstInfo c : MetaM ConstantInfo) mctx mref cctx cref w ci w') :
    RunsTo (Lean.getConstInfo c : MetaM ConstantInfo) mctx' mref cctx' cref w ci w' := by
  unfold Lean.getConstInfo at h ⊢
  obtain ⟨env, w1, he, hm⟩ := RunsTo.bind h
  refine RunsTo.bind_intro (getEnv_ctx he) ?_
  cases hf : env.find? c with
  | none => rw [hf] at hm; exact (throwUnknownConstant_not_runs c hm).elim
  | some i => rw [hf] at hm; exact hm

/-- **`MachineDefines` does not depend on the contexts.** -/
theorem MachineDefines.ctx {c : Name} {shape : MachineShape}
    (h : MachineDefines mctx mref cctx cref c shape) :
    MachineDefines mctx' mref cctx' cref c shape :=
  fun _ _ _ _ _ _ _ _ _ g e1 e2 =>
    h _ _ _ _ _ _ _ _ _ (getConstInfo_ctx c g) (getEnv_ctx e1) (getEnv_ctx e2)

/-- **`EntryDefines` does not depend on the contexts.** -/
theorem EntryDefines.ctx {c : Name} {v : Lean.Expr}
    (h : EntryDefines mctx mref cctx cref c v) : EntryDefines mctx' mref cctx' cref c v :=
  fun _ _ _ _ _ _ g e1 => h _ _ _ _ _ _ (getConstInfo_ctx c g) (getEnv_ctx e1)

end Tools.ShippingReflectCtx
