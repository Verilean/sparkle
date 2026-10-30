import Tools.ShippingGen2Pkg      -- Tools.ShippingGen2.Pkg
import Tools.ShippingChildInv     -- notag_at
set_option autoImplicit false
-- Built: g3sv-b5be62e6 (clean snapshot, exit 0, standard axioms); written by reading at 96cbd548. No `sorry`, no `axiom`, no `native_decide`.

/-! # LOCAL COPY (scripts/gen2/SERVED_FREEZE.md rev1 D2) of 4 declarations of `par/gen2-spec`
Tools/ShippingGen2DataBridge.lean

SOURCE: `par/gen2-spec`, file `Tools/ShippingGen2DataBridge.lean`, last changed at 48775f38, read at e134c63a (lines
33-60: `noMemRowS`, `OneOutNoMemRow`, `hord_of_rowS`, `hord_of_row`). The declaration texts below are copied
TEXT-IDENTICALLY. Only these differ:
- the namespace (`Tools.ShippingGen2ServedDataBridgeCopy`, so that the two files can be imported together);
- the imports (that file imports `Tools.ShippingGen2FitChain`, which is not on `par/gen3-induct`).

`OneOutNoMemRow_eq` (source line 40) is copied too, as the `rfl` link between the two forms.

UNIFY PLAN (rev1 §4.4 step 1). At the integration SHA, a check file proves, by `rfl` (and by `checkExpected` for the
two theorems), that each copy equals its source:
- `Tools.ShippingGen2ServedDataBridgeCopy.noMemRowS = Tools.ShippingGen2DataBridge.noMemRowS`;
- `…OneOutNoMemRow = …OneOutNoMemRow` at every `ι dom`.

Then this file is deleted, and `Tools/ShippingGen2Served.lean` imports `Tools.ShippingGen2DataBridge` instead. On
`par/gen2-spec`, `Pkg` has the extra `.comb` constructor. The texts do not mention constructors (`p.d.shape` only), so
they are unchanged by it.

These are supplier-local data bridges. A row is an extra premise, NOT a coverage guarantee (G-DATA). -/
namespace Tools.ShippingGen2ServedDataBridgeCopy
open Lean
open Sparkle.Compiler.Elab
open Sparkle.Core.Domain

variable {ι : Type} {dom : ι → DomainConfig}

/-- The row on a shape: with no field list (the one-output closing), no call entry has a memory origin. -/
def noMemRowS (s : MachineShape) : Bool :=
  !s.instFields.isEmpty || s.instTagged.all (fun x => x.2.child?.isNone)

/-- **The P-MEM row** of a package (implication form: memory parents, whose `instFields ≠ []`, pass it). -/
def OneOutNoMemRow (p : Tools.ShippingGen2.Pkg ι dom) : Bool :=
  !p.d.shape.instFields.isEmpty || p.d.shape.instTagged.all (fun x => x.2.child?.isNone)

theorem OneOutNoMemRow_eq (p : Tools.ShippingGen2.Pkg ι dom) : OneOutNoMemRow p = noMemRowS p.d.shape := rfl

/-- The shape form of `hord_of_row`. -/
theorem hord_of_rowS {s : MachineShape} (h : noMemRowS s = true) (hf : s.instFields = [])
    {k : Nat} (hk : k < s.insts.length) :
    (s.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none := by
  have hall : s.instTagged.all (fun x => x.2.child?.isNone) = true := by
    have h0 := h
    unfold noMemRowS at h0
    rw [hf] at h0
    first
      | exact h0
      | (simp only [List.isEmpty_nil, Bool.not_true, Bool.false_or] at h0; exact h0)
      | simpa using h0
  exact Tools.ShippingChildInv.notag_at (fun o ho => List.all_eq_true.mp hall o ho) hk

/-- **`hord_of_row`**: the row and an empty field list give the `.ord`-like origin at every entry IN RANGE. -/
theorem hord_of_row {p : Tools.ShippingGen2.Pkg ι dom} (h : OneOutNoMemRow p = true)
    (hf : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) :
    (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none :=
  hord_of_rowS (s := p.d.shape) h hf hk

end Tools.ShippingGen2ServedDataBridgeCopy

#print axioms Tools.ShippingGen2ServedDataBridgeCopy.OneOutNoMemRow_eq
#print axioms Tools.ShippingGen2ServedDataBridgeCopy.hord_of_rowS
#print axioms Tools.ShippingGen2ServedDataBridgeCopy.hord_of_row
