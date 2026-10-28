import Tools.Prototype.ExtReaderDefs

/-! # Unit EXT2 (2a/N): the block-only call table of the reader with the operations `O`, and the phases of a successful run

STATUS: see REPORT-EXT2.md for the build log. `btabX O senv n` answers the block calls with the fuel table `readFX O senv n` and the
normaliser calls with `none` (a successful run of the phases after the single normaliser call reads no `norm` call: `BlkCong`).
`machineShapeX_steps` is NMI's `machineShapeNM_steps` for the reader `machineShapeX O` (one common fuel `n`). No sorry / axiom /
native_decide. -/

namespace Tools.Prototype.ExtReader
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
  Tools.Prototype.NormNodeModelLetOk Tools.Prototype.ReaderLfp Lean.Order
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk
open Tools.Prototype.NormStepModel Tools.Prototype.ExtModelLetOk

/-- The block-only call table at fuel `n` (`norm` calls: not answered). -/
def btabX (O : ExtOps) (senv : StructEnv) (n : Nat) : (c : WCall) → Option (WCall.Res c)
  | .norm _ => none
  | .blk c => readFX O senv n c

/-- The block-only table with the kernel-visible block. -/
def xtabBX (O : ExtOps) (senv : StructEnv) : (c : WCall) → Option (WCall.Res c)
  | .norm _ => none
  | .blk c => execBlockX O senv c

theorem btabX_mono (O : ExtOps) (senv : StructEnv) {n m : Nat} (hnm : n ≤ m) :
    HLe (btabX O senv n) (btabX O senv m) := by
  intro c r h
  cases c with
  | norm e =>
    have h' : (none : Option (WCall.Res (.norm e))) = some r := h
    cases h'
  | blk c => exact fuel_mono (stepX O senv) hnm c r h

theorem ext_btabX_of_reach (O : ExtOps) (senv : StructEnv) :
    ∀ L : List (Sigma WCall.Res), (∀ q ∈ L, ∃ n, btabX O senv n q.1 = some q.2) →
      ∃ N, Ext (btabX O senv N) L := by
  intro L
  induction L with
  | nil => intro _; exact ⟨0, ext_nil _⟩
  | cons q L ih =>
    intro hL
    obtain ⟨N, hN⟩ := ih (fun p hp => hL p (List.mem_cons.mpr (Or.inr hp)))
    obtain ⟨n, hn⟩ := hL q (List.mem_cons.mpr (Or.inl rfl))
    refine ⟨n + N, ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact btabX_mono O senv (Nat.le_add_right n N) _ _ hn
    · exact btabX_mono O senv (Nat.le_add_left N n) _ _ (hN p hp)

/-- **Initial → domain → reserve** for an ARBITRARY table (the proof of `shapeStart_inv` reads no property of the table). -/
theorem shapeStart_invT {senv : StructEnv} {T : (c : WCall) → Option (WCall.Res c)} {m : ShapeMid} {st0 : MachRead}
    (hr : (shapeStart senv m).run T = some (some st0)) :
    (m.run? = none ∧ st0 = ({} : MachRead)) ∨
    ∃ (dom αs initsE body dom' : Lean.Expr) (stc : MachRead) (base : Nat),
      m.run? = some (dom, αs, initsE, body) ∧
      T (.blk (Call.conv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead))) = some (some (dom', stc)) ∧
      machReserve senv.natOf dom' αs initsE body ({} : MachRead) = some (base, st0) := by
  unfold shapeStart at hr
  rcases hm : m.run? with _ | ⟨dom, αs, initsE, body⟩
  · rw [hm] at hr
    try dsimp only at hr
    exact Or.inl ⟨by first | rfl | exact hm, (okO_run_inv hr).symm⟩
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨dom', stc⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    obtain ⟨⟨base, st'⟩, hres, hr⟩ := optK_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    subst e
    exact Or.inr ⟨dom, αs, initsE, body, dom', stc, base, by first | rfl | exact hm, hc, hres⟩

/-- The part of `shapeWX` after its single normaliser call. -/
def shapeRestX (O : ExtOps) (senv : StructEnv) (ai : Bool) (p : ShapePre) (en : Lean.Expr) : WM (Option MachineShape) :=
  let m := shapeMidX O senv p en
  bindO (shapeStart senv m) fun st =>
  bindO (foldO (shapeRootLet senv) (([] : List MachVal), st) m.rootLets) fun (env, st) =>
  bindO (shapeBody m env st) fun (st, v) =>
  FM.pure (shapePost ai p m st v)

theorem shapeWX_eq (O : ExtOps) (sm : Bool) (ps : List (String × Nat)) (ci : Lean.ConstantInfo) (senv : StructEnv)
    (ai : Bool) :
    shapeWX O sm ps ci senv ai =
      optK (shapePre sm ps ci senv) fun p => FM.bind (wNorm p.e) (shapeRestX O senv ai p) := rfl

theorem bc_shapeRestX (O : ExtOps) (senv : StructEnv) (ai : Bool) (p : ShapePre) (en : Lean.Expr) :
    BlkCong (shapeRestX O senv ai p en) := by
  unfold shapeRestX
  refine bc_bindO (bc_shapeStart senv _) (fun st => ?_)
  refine bc_bindO (bc_foldO (bc_shapeRootLet senv) _ _) (fun es => ?_)
  rcases es with ⟨env, st'⟩
  refine bc_bindO (bc_shapeBody _ _ _) (fun sv => ?_)
  rcases sv with ⟨st'', v⟩
  exact bc_pure _

theorem compact_shapeRestX (O : ExtOps) (senv : StructEnv) (ai : Bool) (p : ShapePre) (en : Lean.Expr) :
    Compact (shapeRestX O senv ai p en) := by
  unfold shapeRestX
  refine compact_bindO (compact_shapeStart senv _) (fun st => ?_)
  refine compact_bindO (compact_foldO (compact_shapeRootLet senv) _ _) (fun es => ?_)
  rcases es with ⟨env, st'⟩
  refine compact_bindO (compact_shapeBody _ _ _) (fun sv => ?_)
  rcases sv with ⟨st'', v⟩
  exact compact_pure _

/-- The rest of a successful run holds at ONE fuel of the block-only fuel table. -/
theorem shapeRestX_fuel {O : ExtOps} {senv : StructEnv} {ai : Bool} {p : ShapePre} {en : Lean.Expr}
    {r : Option MachineShape}
    (h : (shapeRestX O senv ai p en).run (xtabX O senv) = some r) :
    ∃ n, (shapeRestX O senv ai p en).run (btabX O senv n) = some r := by
  have h1 : (shapeRestX O senv ai p en).run (xtabBX O senv) = some r := by
    rw [← h]; exact (bc_shapeRestX O senv ai p en).eq _ _ (fun k => rfl)
  obtain ⟨L, e, k⟩ := (compact_shapeRestX O senv ai p en).ok (xtabBX O senv) r h1
  obtain ⟨N, hN⟩ := ext_btabX_of_reach O senv L (by
    intro q hq
    obtain ⟨c, y⟩ := q
    have hx : xtabBX O senv c = some y := e _ hq
    cases c with
    | norm e' =>
      have h' : (none : Option (WCall.Res (.norm e'))) = some y := hx
      cases h'
    | blk c' => exact (execBlockX_iff O senv).mp hx)
  exact ⟨N, k (btabX O senv N) hN⟩

/-- The phases of a successful run of `machineShapeX O`, with every intermediate state at ONE common fuel `n`. -/
theorem machineShapeX_steps {O : ExtOps} {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape}
    (h : machineShapeX O sm ps ci senv ai = some (some sp)) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      execNormX O machNormNodeM senv p.e = some en ∧
      (shapeStart senv (shapeMidX O senv p en)).run (btabX O senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0)
          (shapeMidX O senv p en).rootLets).run (btabX O senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMidX O senv p en) env st1).run (btabX O senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMidX O senv p en) st v = some sp := by
  have h' : (shapeWX O sm ps ci senv ai).run (xtabX O senv) = some (some sp) := h
  rw [shapeWX_eq] at h'
  obtain ⟨p, hp, h'⟩ := optK_some_inv h'
  obtain ⟨en, hen, h2⟩ := bind_some_inv h'
  obtain ⟨n, hn⟩ := shapeRestX_fuel h2
  unfold shapeRestX at hn
  try dsimp only at hn
  obtain ⟨st0, h0, hn⟩ := bindO_some_inv hn
  try dsimp only at hn
  obtain ⟨⟨env, st1⟩, h1, hn⟩ := bindO_some_inv hn
  try dsimp only at hn
  obtain ⟨⟨st, v⟩, h3, hn⟩ := bindO_some_inv hn
  try dsimp only at hn
  exact ⟨n, p, en, st0, env, st1, st, v, hp, hen, h0, h1, h3, pure_run_inv hn⟩

#print axioms machineShapeX_steps

end Tools.Prototype.ExtReader
