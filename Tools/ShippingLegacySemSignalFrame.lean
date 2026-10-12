import Tools.ShippingLegacySemBinder

/-! # `isSignalBinderType` leaves the builder state (OPTIONAL discharge)

`SignalTestFrame T` (`Tools/ShippingLegacySemBinder.lean`) is a premise of the
binder walk. It is provable: `isSignalBinderType T` is one lifted `whnf`
followed by a `match` whose arms are both `pure`. This file proves it for
every `T`. It is kept apart, and nothing imports it, so that a failure here
(the `match` on `Lean.Expr`) does not block the walk; once it builds, the
`hsig` hypotheses of `one_binder_entry_output` / `useDbl_output` can be
dropped by passing `isSignalBinderType_frame _`.

**Program shape EXPECTED** after `unfold isSignalBinderType`:

```
CompilerM.liftMetaM (whnf T) >>= fun type =>
  match type.getAppFn with
  | .const name _ => pure (name.toString.endsWith "Signal")
  | _ => pure false
```

Three ways to split the `match` are tried: by cases on the head with the
equation rewritten into the run; `split`; `dsimp only` then `split`. -/
namespace Tools.ShippingLegacySem
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness

/-- **The Signal test leaves the builder state**, for every type. -/
theorem isSignalBinderType_frame (T : Lean.Expr) : SignalTestFrame T := by
  intro ctx s t b h
  unfold isSignalBinderType at h
  obtain ⟨ty, s1, hw, h1⟩ := Returns.bind h
  have hs1 : s1 = s := Returns.liftMetaM hw
  rw [hs1] at h1
  first
    | (cases hfn : ty.getAppFn <;> rw [hfn] at h1 <;> exact (Returns.pure h1).2)
    | (split at h1 <;> exact (Returns.pure h1).2)
    | (dsimp only at h1
       split at h1 <;> exact (Returns.pure h1).2)

end Tools.ShippingLegacySem
