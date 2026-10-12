import Tools.ShippingCallWidths

/-! # The call-width condition without the vacuous case (finding A)

`Tools.ShippingCallWidths.callWidthsOk` tests the child's output named
`d.shape.instFields.getD k ""`. On the one-output closing
(`Sparkle.IR.Machine.closeInsts`, `instFields = []`) that name is `""`, no
field has it, and the condition says nothing — while the closing connects
the child's ONLY output, whatever its name (`instStmt`: `let [outP] :=
mc.outputs`).

`callWidthsStrict` asks, for entry `k`:

* `instFields[k]? = some f` (the closing with fields, `closeInstsG`): every
  layout output named `f` has the width of the type of the entry's binder —
  as `callWidthsOk`;
* `instFields[k]? = none` (the one-output closing): EVERY layout output of
  the child has that width.

`hkidW_strict` is `hkidW` in that form; `hkidW_of_strict` is the statement
`Tools.ShippingCallWidths.hkidW_of_data` concludes (so every existing use of
`callWidthsOk` can take `callWidthsStrict` instead: `parent_callWidths` /
`parent_kidW_data` in `Tests/Compiler/ChecksRawTest.lean`, and the
generated endpoints' `hkidW`); `callWidthsOk_of_strict` gives the old
condition from the new one.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingCallWidthsStrict
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv

/-- **The calls' widths agree with the children's layouts**, the one-output
closing included. -/
def callWidthsStrict (d : MachineData) (nDecl : Nat) (kidOuts : Nat → List OutField) : Bool :=
  (List.range d.shape.insts.length).all fun k =>
    (kidOuts k).all fun o =>
      (d.shape.instFields[k]?).any (fun f => o.name != f) ||
        decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some o.ty.bitWidth)

/-- What the condition gives at an entry and a layout output. -/
theorem callWidthsStrict_at {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    (hcw : callWidthsStrict d nDecl kidOuts = true)
    {k : Nat} (hk : k < d.shape.insts.length) {o : OutField} (ho : o ∈ kidOuts k)
    (hname : ∀ f, d.shape.instFields[k]? = some f → o.name = f) :
    (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth := by
  unfold callWidthsStrict at hcw
  have h1 : ((kidOuts k).all fun o =>
      (d.shape.instFields[k]?).any (fun f => o.name != f) ||
        decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some o.ty.bitWidth)) = true :=
    List.all_eq_true.mp hcw k (List.mem_range.mpr hk)
  have h2 : ((d.shape.instFields[k]?).any (fun f => o.name != f) ||
      decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
        some o.ty.bitWidth)) = true :=
    List.all_eq_true.mp h1 o ho
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · cases hf : d.shape.instFields[k]? with
    | none =>
      rw [hf] at h2
      exact absurd h2 Bool.false_ne_true
    | some f =>
      rw [hf] at h2
      have h3 : (o.name != f) = true := h2
      exact absurd (hname f hf) (bne_iff_ne.mp h3)
  · exact of_decide_eq_true h2

/-- `getD` at a position holding `f`. -/
theorem getD_of_getElem? {l : List String} {k : Nat} {f : String} (hf : l[k]? = some f) :
    l.getD k "" = f := by
  have h0 : l.getD k "" = (l[k]?).getD "" := by
    first | rfl | simp [List.getD_eq_getElem?_getD]
  exact h0.trans (congrArg (fun x => Option.getD x "") hf)

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`hkidW`, strict**: per real child, the port the closing connects —
the field's port, or on the one-output closing every output port — has the
width of the type of the entry's binder. -/
theorem hkidW_strict {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    (hcw : callWidthsStrict d nDecl kidOuts = true)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys (kidOuts k) y.1) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, (∀ f, d.shape.instFields[k]? = some f → p.name = f) →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth := by
  intro k hk y hy p hp hpn
  rw [(hkidT k hk y hy).outputs] at hp
  obtain ⟨o, ho, e⟩ := List.mem_map.mp hp
  have h := callWidthsStrict_at hcw hk ho (by
    intro f hf
    have := hpn f hf
    rw [← e] at this
    exact this)
  rw [← e]
  exact h

/-- The statement `hkidW_of_data` concludes, from the strict condition. -/
theorem hkidW_of_strict {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    (hcw : callWidthsStrict d nDecl kidOuts = true)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys (kidOuts k) y.1) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth := by
  intro k hk y hy p hp hpn
  refine hkidW_strict hcw hkidT k hk y hy p hp ?_
  intro f hf
  exact hpn.trans (getD_of_getElem? hf)

/-- The strict condition implies the old one. -/
theorem callWidthsOk_of_strict {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    (hcw : callWidthsStrict d nDecl kidOuts = true) :
    Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true := by
  unfold Tools.ShippingCallWidths.callWidthsOk
  refine List.all_eq_true.mpr fun k hk => List.all_eq_true.mpr fun o ho => ?_
  have hk' : k < d.shape.insts.length := List.mem_range.mp hk
  show (o.name != d.shape.instFields.getD k "" ||
    decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
      some o.ty.bitWidth)) = true
  by_cases hn : o.name = d.shape.instFields.getD k ""
  · have h := callWidthsStrict_at hcw hk' ho (fun f hf => hn.trans (getD_of_getElem? hf))
    rw [Bool.or_eq_true]
    exact Or.inr (decide_eq_true h)
  · rw [Bool.or_eq_true]
    exact Or.inl (bne_iff_ne.mpr hn)

end Tools.ShippingCallWidthsStrict
