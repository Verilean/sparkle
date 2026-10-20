import Tools.ShippingLegacySemEntryOne
import Tools.ShippingLegacySemBinderBound

variable {tenv : Lean.Environment}

/-! # The legacy entry on a one-binder declaration: two outcomes, not three

`one_binder_entry_output` (`Tools/ShippingLegacySemEntryOne.lean`) concludes
`MemoHit ∨ (output statement) ∨ InputSkipped`. With the premise
`InfersNoCatch T` (`Tools/ShippingLegacySemBinderBound.lean`: the hardware
type oracle has no catchable failure on the binder's type) the binder walk
cannot skip (`bindInputsLegacy_one_bound`), and the third disjunct is gone.

**Proved here**: `one_binder_entry_output_bound` — the same premises plus
`InfersNoCatch T`; conclusion `MemoHit ∨ (output statement)`. The proof is
`one_binder_entry_output`'s with the binder walk's single outcome. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)

/-- **The output of a legacy-route declaration with one `bits n` binder and a
scalar Signal result, the skipped outcome excluded** by `InfersNoCatch T`
(the type oracle has no catchable failure on the binder's type). -/
theorem one_binder_entry_output_bound {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool} {nm : Name} {n : Nat} {T : Lean.Expr}
    {leafOf : FVarId → Lean.Expr} {m : Sparkle.IR.AST.Module} {d : Design} {cfe : Bool}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (OneBinderScope nm T leafOf))
    (hsig : SignalTestFrame T) (hinf : InfersBits T n) (hnt : InfersNoCatch T)
    (hleaf : ∀ id : FVarId, (leafOf id).isLambda = false ∧ SignalTyped (leafOf id))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire tenv e hint top named)
      logProf declName [] false cfe (.defnInfo dv) isInst) (m, d)) :
    MemoHit declName m d ∨
    ∃ (id : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
        ([(nm, MixedGateBinder.bits n)].zip [id])
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl declName)) →
      ∀ v : Value, 0 < v.kind.width →
      LeafDom tenv (setupOf declName [(nm, MixedGateBinder.bits n)] [id] cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName [(nm, MixedGateBinder.bits n)] [id] cache bools bits).bools
          (setupOf declName [(nm, MixedGateBinder.bits n)] [id] cache bools bits).bits)
        "out" true (leafOf id) v →
      Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width
        [(nm, MixedGateBinder.bits n)] m initial mems v.toNat := by
  rcases legacy_entry_walk_in old mixed hmach htele hr with hit |
    ⟨body0, mctx, xs, inner, leaves, cache, returned, st, hopen,
      ⟨id, d0, hxs, hinner, hfind, hnm, hty⟩, hsplit, run, hm, legal⟩
  · exact Or.inl hit
  · refine Or.inr ?_
    -- the leaves: one, `("out", leafOf id)`
    rw [hinner] at hsplit
    have hl : leaves.toList = [("out", leafOf id)] :=
      splitReturnLeaves_scalar (hleaf id).1 (hleaf id).2 hsplit
    rw [hl] at run
    rw [hxs] at run
    -- the binder walk, in the context the telescope installed
    have hsig' : SignalTestFrame d0.type := by
      rw [hty]
      exact hsig
    have hinf' : InfersBits d0.type n := by
      rw [hty]
      exact hinf
    have hnt' : InfersNoCatch d0.type := by
      rw [hty]
      exact hnt
    have bound := bindInputsLegacy_one_bound hfind hsig' hinf' hnt' run
    refine ⟨id, cache, ?_⟩
    rw [hnm] at bound
    have run' : HarnessRun tenv logProf declName [(nm, MixedGateBinder.bits n)] [id] cache
        (leafOf id) returned st := bound
    intro bools bits initial mems values v pos dom
    exact leaf_output run' hm legal bools bits initial mems values v pos dom

end Tools.ShippingLegacySem
