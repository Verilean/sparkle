import Tools.ShippingGen4FbPP
import Tools.ShippingMachineDepthRunR
set_option autoImplicit false
-- BUILT (unit FB-15): kjob lake build Tools.ShippingGen4FbPPLookup exit 0 (702 jobs, Pod build at f21380e345c9b94b58878d7d7474d57c8af6c42f; not a clean build). Written against scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §25.3 + §26 (committed before this file). Build record is added by a comments-only commit.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # FB-15: T-PP-LOOKUP — design lookup through `PPRel`

First-match `moduleByName` lookups in `dout` against `dsg`: the entry's own name (`ppRel_lookup_self`) and every other
name (`ppRel_lookup_other`). Partial supply: it does not connect a real run to `PPRel` and does not transport the run
conjunct of `ChildRunN`. No `Nodup` of module names is assumed. -/

namespace Tools.ShippingGen4FbPPLookup
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingGen4FbPP

theorem moduleByName_map_self (N : String) (f : Module → Module) (hf : ∀ x, (f x).name = x.name) :
    ∀ (l : List Module) (x : Module), moduleByName l N = some x →
      moduleByName (l.map fun y => if y.name == N then f y else y) N = some (f x) := by
  intro l
  unfold moduleByName
  induction l with
  | nil => intro x h; simp at h
  | cons y ys ih =>
    intro x h
    by_cases hy : (y.name == N) = true
    · rw [List.find?_cons, hy] at h
      have hxy : y = x := Option.some.inj h
      subst hxy
      rw [List.map_cons, List.find?_cons, if_pos hy, hf]
      rw [hy]
    · have hy' : (y.name == N) = false := by simpa using hy
      rw [List.find?_cons, hy'] at h
      rw [List.map_cons, List.find?_cons, if_neg hy, hy']
      exact ih x h

theorem ppRel_lookup_self {raw : Module} {dsg : Design} {out : Module} {dout : Design}
    (h : PPRel raw dsg out dout)
    (hraw : moduleByName dsg.modules raw.name = some raw) :
    moduleByName dout.modules out.name = some out := by
  obtain ⟨hn, -, -⟩ := ppRel_ports h
  have hz : ∀ x, (Sparkle.IR.ZeroWidth.dropZeroWidthModule x).name = x.name :=
    Tools.ShippingMachineDepthRun.dropZW_name
  have hm : ∀ x, (Sparkle.IR.RefineCheck.mergeChecked x).name = x.name :=
    Tools.ShippingMachineDepthRun.mergeChecked_name
  have h1 := moduleByName_map_self raw.name _ hz dsg.modules raw hraw
  rw [hn]
  rcases h with ⟨ho, hd⟩ | ⟨ho, hd⟩
  · subst hd
    rw [ho]
    exact h1
  · subst hd
    rw [ho]
    exact moduleByName_map_self raw.name _ hm _ _ h1

theorem ppRel_lookup_other {raw : Module} {dsg : Design} {out : Module} {dout : Design}
    (h : PPRel raw dsg out dout) :
    ∀ y : String, y ≠ raw.name → moduleByName dout.modules y = moduleByName dsg.modules y := by
  intro y hy
  have hz : ∀ x, (Sparkle.IR.ZeroWidth.dropZeroWidthModule x).name = x.name :=
    Tools.ShippingMachineDepthRun.dropZW_name
  have hm : ∀ x, (Sparkle.IR.RefineCheck.mergeChecked x).name = x.name :=
    Tools.ShippingMachineDepthRun.mergeChecked_name
  have h1 := Tools.ShippingMachineDepthRun.moduleByName_map_other raw.name _ hz dsg.modules y hy
  rcases h with ⟨-, hd⟩ | ⟨-, hd⟩
  · subst hd
    exact h1
  · subst hd
    exact (Tools.ShippingMachineDepthRun.moduleByName_map_other raw.name _ hm _ y hy).trans h1

end Tools.ShippingGen4FbPPLookup
