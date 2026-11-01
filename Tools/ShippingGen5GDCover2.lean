import Tools.ShippingGen5GDCover0
import Tools.ShippingGen5GDCover1
set_option autoImplicit false

namespace Tools.ShippingGen5GDCover2
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingReaderFuel Tools.ShippingReaderLenOk
  Tools.ShippingReaderFuelShapeR5 Tools.ShippingShapeDecomp Tools.ShippingMachineAuto Tools.ShippingGen5Cover5
  Tools.ShippingGen5GDCover1

theorem shapePost_binders_len {allowInsts : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr}
    {sp : MachineShape} (h : shapePost allowInsts p m st v = some sp) (hl : st.LenOk) :
    sp.binders.length = p.bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets := by
  unfold shapePost at h
  simp only [bind, pure] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
  rcases hq : p.tup? with _ | ks
  · rw [hq] at h
    dsimp only at h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    split at h; · cases h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · obtain rfl := Option.some.inj h
      simp [machSlotFields_length, hl.names, hl.inits, List.length_zip]
      omega
    · cases h
  · rw [hq] at h
    dsimp only at h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · obtain rfl := Option.some.inj h
      simp [machSlotFields_length, hl.names, hl.inits, List.length_zip]
      omega
    · cases h

theorem dataOfFront_len_of_witness {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape} {n : Nat}
    {p : ShapePre} {en : Lean.Expr} {st0 : MachRead} {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr}
    (w : StateSideWitness E senv sp n p en st0 env st1 st v) :
    sp.binders.length = p.bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets := by
  obtain ⟨_, _, _, _, _, hpost, hl, _⟩ := w
  exact shapePost_binders_len hpost hl

theorem shapePre_peel {E : ConstantInfo} {senv : StructEnv} {p : ShapePre}
    (h : shapePre false [] E senv = some p) :
    E = .defnInfo p.d ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs p.d.value) = some (p.bs, p.e) := by
  unfold shapePre at h
  cases E with
  | defnInfo d =>
    have hc : ((false : Bool) || !([] : List (String × Nat)).isEmpty) = false := rfl
    rw [hc] at h
    simp only [Bool.false_eq_true, if_false, bind, pure] at h
    obtain ⟨pr, hpr, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    all_goals
      obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · cases h
      · obtain rfl := Option.some.inj h
        exact ⟨rfl, hpr⟩
  | _ => cases h

theorem dataOfFront_len_of_production
    (hbr : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, machineShapeF n false [] E senv true = some (some sp))
    {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (h : machineShape? false [] E senv = some sp) :
    ∃ (d : DefinitionVal) (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      E = .defnInfo d ∧
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      sp.binders.length = bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets := by
  obtain ⟨n, p, en, st0, env, st1, st, v, w⟩ := stateSide_of_production hbr h
  obtain ⟨hE, hpeel⟩ := shapePre_peel w.1
  exact ⟨p.d, p.bs, p.e, hE, hpeel, dataOfFront_len_of_witness w⟩

end Tools.ShippingGen5GDCover2
