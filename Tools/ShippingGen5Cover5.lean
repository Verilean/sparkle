import Tools.ShippingGen5Cover3
import Tools.ShippingReaderFuelShapeR5
import Tools.ShippingReaderLenOk
import Tools.ShippingShapeDecomp
set_option autoImplicit false
-- NOT BUILT. Clean build is the coder's. No sorry / axiom / native_decide in source.

/-! # DG-COVER rev6 unit U-E2: row 6a (state side of `ShapeAgree`), fuel model only

Statements are those of `scripts/gen5/DG_COVER_FREEZE_REV6.md` §2 (T1–T6).
T3 keeps the phase trace of one run (`st0`, `env`, `st1`, `st`, `v`, `shapePost … = some sp`) together with the four state-side facts of THAT `st`.
T4 (`shapeAgree_of_sides`) is the combination with the `d`-side premises, all about the same `sp`.
T5/T6 conclude only `∃ st, st.LenOk ∧ ShapeAgree d st`: this existential FORGETS the phase trace and is NOT identified with any other witness;
a later R-trace connection must use T3's witness together with T4, not T5/T6.
T6 is conditional on the inline hypothesis `hbr` (the `ShapeFuelBridge` text, assumed once, not proved).
Not supplied: row 6b (`d.shape = sp`, `d.ss.length`, `d.ls.length`, `d.nIn`), production/Issue/FG, R-trace/R-in/R-nl/R-dom/B3, `LetQuoteEq`, `LetsNoLoose`, `FullInv`, `d.ok`. -/

namespace Tools.ShippingGen5Cover5
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingReaderFuel Tools.ShippingReaderLenOk
  Tools.ShippingReaderFuelShapeR5 Tools.ShippingShapeDecomp Tools.ShippingMachineAuto

/-- T1: sizes of the layout read off `shapePost`; no `LenOk`, so the slot count is the `min`. -/
theorem shapePost_layout_sizes {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp) :
    sp.layout.lets = st.lets.size ∧ sp.layout.slots.length = min st.kinds.size st.inits.size := by
  unfold shapePost at h
  try dsimp only at h
  repeat' first
    | (replace h := ite_none_inv h)
    | (replace h := bind_inv h; obtain ⟨_, _, h⟩ := h)
    | (replace h := Option.bind_eq_some_iff.mp h; obtain ⟨_, _, h⟩ := h)
    | (split at h)
  all_goals first
    | (cases h; done)
    | skip
  all_goals
    try (replace h := ite_else_none_inv h)
    have hsp := Option.some.inj h
    subst hsp
    refine ⟨rfl, ?_⟩
    simp [machSlotFields_length]

/-- T2: the four state-side facts of `ShapeAgree` for the shape built from `st`, given `LenOk`. -/
theorem shapePost_state_side {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp) (hL : st.LenOk) :
    sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
    sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size := by
  obtain ⟨h1, h2⟩ := shapePost_layout_sizes h
  refine ⟨shapePost_insts' h, shapePost_instOrigins h, ?_, h1⟩
  rw [h2, hL.inits]
  exact Nat.min_self _

/-- T3 (fuel model): for every successful candidate run, the SAME final state `st` of that run (with the phases that produced it,
as in `machineShapeF_steps`) is `LenOk` and satisfies the four facts for the returned `sp`. -/
theorem machineShapeF_state_side {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size := by
  obtain ⟨p, en, st0, env, st1, st, v, hp, hen, h0, h1, h2, h3⟩ := machineShapeF_steps h
  have l0 : st0.LenOk := shapeStart_lenOk h0
  have l1 : st1.LenOk := rootLets_lenOk h1 l0
  have l2 : st.LenOk := shapeBody_lenOk h2 l1
  obtain ⟨a, b, c, d⟩ := shapePost_state_side h3 l2
  exact ⟨p, en, st0, env, st1, st, v, hp, hen, h0, h1, h2, h3, l2, a, b, c, d⟩

/-- T4: pure combination (no fuel, no bridge). The state-side facts are about `sp` and `st`; the `d`-side premises are about the same `sp`. -/
theorem shapeAgree_of_sides {d : MachineData} {st : MachRead} {sp : MachineShape}
    (hs : sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
          sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size)
    (hsp : d.shape = sp) (hss : d.ss.length = sp.layout.slots.length)
    (hls : d.ls.length = sp.layout.lets) (hn : sp.insts.length ≤ d.nIn) :
    ShapeAgree d st := by
  subst hsp
  obtain ⟨h1, h2, h3, h4⟩ := hs
  exact ⟨h1, h2, hss.trans h3, hls.trans h4, hn⟩

/-- T5: fuel model → `ShapeAgree` for the run's own `sp`: the `d`-side premises of T4 are kept, `st` is produced by the run. -/
theorem shapeAgree_of_fuel_run {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some (some sp)) {d : MachineData}
    (hsp : d.shape = sp) (hss : d.ss.length = sp.layout.slots.length)
    (hls : d.ls.length = sp.layout.lets) (hn : sp.insts.length ≤ d.nIn) :
    ∃ st : MachRead, st.LenOk ∧ ShapeAgree d st := by
  obtain ⟨_, _, _, _, _, st, _, _, _, _, _, _, _, hL, a, b, c, e⟩ := machineShapeF_state_side h
  exact ⟨st, hL, shapeAgree_of_sides ⟨a, b, c, e⟩ hsp hss hls hn⟩

/-- T6: connection to production, **conditional on the boundary `ShapeFuelBridge` (inline hypothesis `hbr`, assumed once, not proved)**. -/
theorem shapeAgree_of_production {E : ConstantInfo} {senv : StructEnv} {sp : MachineShape}
    (hbr : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, machineShapeF n false [] E senv true = some (some sp))
    (h : machineShape? false [] E senv = some sp) {d : MachineData}
    (hsp : d.shape = sp) (hss : d.ss.length = sp.layout.slots.length)
    (hls : d.ls.length = sp.layout.lets) (hn : sp.insts.length ≤ d.nIn) :
    ∃ st : MachRead, st.LenOk ∧ ShapeAgree d st := by
  obtain ⟨n, hn'⟩ := hbr E senv sp h
  exact shapeAgree_of_fuel_run hn' hsp hss hls hn

end Tools.ShippingGen5Cover5
