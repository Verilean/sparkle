import Tools.ShippingChecksWidths
import Tools.ShippingChildIfaceTy

/-! # The width agreement of a call and its child, as a condition on the DATA (G1, Finding A)

`core_instOutWidthsOk` takes, per real child, `hkidW`: the child's port for
the field a call entry reads has the width of the type of the entry's
binder. This file restates it run-free:

* `callWidthsOk d nDecl kidOuts` (a `Bool`, decidable on the two
  declarations' reflected data): for every call entry `k` and every output
  field `o` of its child's LAYOUT (`kidOuts k`) named `instFields[k]`, the
  type of the binder `binders[nDecl + k]` has `o`'s type's width;
* `hkidW_of_data`: `hkidW` from `callWidthsOk` and, per real child, "its
  module's output ports are the layout's fields with their types"
  (`ChildOutTys`: `leaf_real_outTys` for a child without calls).

## Why this is a data condition and not a reader lemma

Read from `Sparkle/Compiler/Elab.lean`:
* the PARENT's kind of entry `k` is `f.2` for the `k`-th field of
  `machOuts? senv resTy`, `resTy` the callee's type INSTANTIATED with the
  call's arguments (`machInstanceS`, 4085–4111; one-output calls:
  `machInstance`, the kind passed in); the entry's binder is
  `(inst{k}, insts[k].2.2)` (the shape's `instBinders`, 5162–5165);
* the CHILD's layout field is `machOutFields … outs` (5174) with `outs` its
  own `machOuts?` of its DECLARED result type (under its binders, not
  instantiated), and the port type is `machHWType kind`.

Both sides call the same `machOuts?`, on type expressions that differ by
the instantiation of the callee's binders; for a structure result the
kinds come from the structure's declaration (`senv.fields`), for a Signal
result from the type's literal width. The readers are `partial def`s over
`Lean.Expr`: there is no equation to prove an agreement lemma from, and
nothing compares the two results. What IS available in the logic is each
declaration's reflected shape (`MachineDefines`), i.e. the data — on which
the agreement is the decidable `callWidthsOk`. For a pair of declarations
it is one `decide`; it is a premise per pair, like `outTy`.

BUILT (as a dependency of runs `k1` / `cr1`, exit 0; header corrected 2026-10-18). MEASURED axioms (run `ax18`, poc after 3a1938a3): `hkidW_of_data`:
[propext, Classical.choice, Quot.sound]. -/
namespace Tools.ShippingCallWidths
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv

/-- **The calls' widths agree with the children's layouts** (run-free): for
every entry `k`, the layout field of child `k` that the entry reads has the
width of the type of the entry's binder. -/
def callWidthsOk (d : MachineData) (nDecl : Nat) (kidOuts : Nat → List OutField) : Bool :=
  (List.range d.shape.insts.length).all fun k =>
    (kidOuts k).all fun o =>
      o.name != d.shape.instFields.getD k "" ||
        decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some o.ty.bitWidth)

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`hkidW` from the data**: the run-free width condition and, per real
child, its output ports being its layout's fields. -/
theorem hkidW_of_data {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    (hcw : callWidthsOk d nDecl kidOuts = true)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys (kidOuts k) y.1) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth := by
  intro k hk y hy p hp hpn
  unfold callWidthsOk at hcw
  have h1 : ((kidOuts k).all fun o =>
      o.name != d.shape.instFields.getD k "" ||
        decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some o.ty.bitWidth)) = true :=
    List.all_eq_true.mp hcw k (List.mem_range.mpr hk)
  rw [(hkidT k hk y hy).outputs] at hp
  obtain ⟨o, ho, e⟩ := List.mem_map.mp hp
  have h2 : (o.name != d.shape.instFields.getD k "" ||
      decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
        some o.ty.bitWidth)) = true :=
    List.all_eq_true.mp h1 o ho
  have hpn' : o.name = d.shape.instFields.getD k "" := by
    rw [← e] at hpn
    exact hpn
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact absurd hpn' (bne_iff_ne.mp h2)
  · have h3 := of_decide_eq_true h2
    rw [← e]
    exact h3

end Tools.ShippingCallWidths
