import Tools.ShippingGen5Cover5
import Tools.ShippingGen5DataOfDims
set_option autoImplicit false
-- NOT BUILT (draft; freeze scripts/gen5/GDCOVER01_FREEZE.md). No sorry / axiom / native_decide.

/-! # G1 + W1 (scripts/gen5/GDCOVER01_FREEZE.md): the state-side witness of one production run, and `ShapeAgree d st` for the SAME `st`

`StateSideWitness` is the 11 clauses of `machineShapeF_state_side` (Cover5.lean:55) at `sm := false`, `ps := []`, `ai := true`.
`stateSide_of_production` takes the inline hypothesis `hbr` (C.CV-4, the text of `shapeAgree_of_production`; assumed, not proved).
`shapeAgree_witness` adds the `d`-side facts from `dataOfAt_dims` and concludes `ShapeAgree d st` for the `st` of the witness (not a fresh existential).
No new premise; nothing here supplies (D), (W), `LetQuoteEq`, `FullInv`, `LetsNoLoose`, or the identification of `dataOf` with `dataOfAt`. -/
namespace Tools.ShippingGen5GDCover1
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingReaderFuel Tools.ShippingReaderLenOk
  Tools.ShippingReaderFuelShapeR5 Tools.ShippingShapeDecomp Tools.ShippingMachineAuto Tools.ShippingGen5Cover5

def StateSideWitness (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape) (n : Nat)
    (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr) : Prop :=
  shapePre false [] E senv = some p ∧
  machNormF n senv p.e = some en ∧
  (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
  (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n)
      = some (some (env, st1)) ∧
  (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
  shapePost true p (shapeMid senv p en) st v = some sp ∧
  st.LenOk ∧
  sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
  sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size

theorem stateSide_of_production
    (hbr : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, machineShapeF n false [] E senv true = some (some sp))
    {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr), StateSideWitness E senv sp n p en st0 env st1 st v := by
  obtain ⟨n, hn⟩ := hbr E senv sp h
  obtain ⟨p, en, st0, env, st1, st, v, w⟩ := machineShapeF_state_side hn
  exact ⟨n, p, en, st0, env, st1, st, v, w⟩

theorem shapeAgree_witness_from
    (hbr : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, machineShapeF n false [] E senv true = some (some sp))
    {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfFrom lvl E senv sp tin fl = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st := by
  obtain ⟨hsp, hss, hls, hn⟩ := Tools.ShippingGen5DataOf.dataOfFrom_dims lvl hd
  obtain ⟨n, p, en, st0, env, st1, st, v, w⟩ := stateSide_of_production hbr h
  obtain ⟨_, _, _, _, _, _, _, a, b, c, e⟩ := w
  exact ⟨n, p, en, st0, env, st1, st, v, ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, a, b, c, e⟩,
    shapeAgree_of_sides ⟨a, b, c, e⟩ hsp hss hls hn⟩

theorem shapeAgree_witness
    (hbr : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, machineShapeF n false [] E senv true = some (some sp))
    {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData}
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl E senv sp = some d) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E senv sp n p en st0 env st1 st v ∧ ShapeAgree d st := by
  unfold Tools.ShippingGen5DataOf.dataOfAt at hd
  split at hd
  · cases hd
  · exact shapeAgree_witness_from hbr h hd

end Tools.ShippingGen5GDCover1

#print axioms Tools.ShippingGen5GDCover1.StateSideWitness
#print axioms Tools.ShippingGen5GDCover1.stateSide_of_production
#print axioms Tools.ShippingGen5GDCover1.shapeAgree_witness_from
#print axioms Tools.ShippingGen5GDCover1.shapeAgree_witness
