import Tools.ShippingGen5Cover5
import Tools.ShippingGen5DataOfDims
import Tools.ShippingGen5GDCover1
set_option autoImplicit false
-- NOT BUILT (skeleton; build result is added by a comment-only commit). No sorry / axiom / native_decide.

/-! # C.CV-5: `shapeAgree_of_sides` without `hsp hss hls hn` (`scripts/gen5/AC9CV5_FREEZE.md`)

The four `d`-side facts are the conclusion of `dataOfAt_dims` for `hd : dataOfAt lvl E senv sp = some d`; they are derived inside the proof.
`shapeAgree_of_witness` takes the state side from a `StateSideWitness` (the `st` of the witness, not a fresh one).
Not supplied: that `dataOfAt` is `some` on a run, `hbr` / `stateSide_of_production` (C.CV-4), `FullInv`, `LetQuoteEq`. -/
namespace Tools.ShippingGen5Cover5R
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingMachineAuto Tools.ShippingGen5GDCover1

theorem shapeAgree_of_sidesR {d : MachineData} {st : MachRead} {sp : MachineShape}
    (hs : sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
          sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size)
    {lvl : Lean.Expr → Nat} {E : ConstantInfo} {senv : StructEnv}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d) :
    ShapeAgree d st := by
  obtain ⟨hsp, hss, hls, hn⟩ := Tools.ShippingGen5DataOf.dataOfAt_dims lvl hd
  exact Tools.ShippingGen5Cover5.shapeAgree_of_sides hs hsp hss hls hn

theorem shapeAgree_of_witness {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape} {n : Nat}
    {p : ShapePre} {en : Lean.Expr} {st0 : MachRead} {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr}
    (w : StateSideWitness E senv sp n p en st0 env st1 st v)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d) :
    ShapeAgree d st := by
  obtain ⟨_, _, _, _, _, _, _, a, b, c, e⟩ := w
  exact shapeAgree_of_sidesR ⟨a, b, c, e⟩ hd

end Tools.ShippingGen5Cover5R

#print axioms Tools.ShippingGen5Cover5R.shapeAgree_of_sidesR
#print axioms Tools.ShippingGen5Cover5R.shapeAgree_of_witness
