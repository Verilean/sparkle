import Tools.ShippingPostSoundness
import Tools.ShippingRegisterSoundness

/-! # The full entry's two post passes on an instance body (worker N, round 1)

WRITTEN, NOT BUILT. PURE: about the IR passes only, no run.

The full entry returns `dropZeroWidthModule M` or `mergeChecked
(dropZeroWidthModule M)` of the core module `M`
(`Tools.ShippingMachineShipping.synthesizeCombinational_checked`). The built
facts about these passes are for assignment-only bodies
(`Tools.ShippingTypedPostSoundness.dropZeroWidth_typed`,
`Tools.ShippingCombKidText.mergeChecked_assign`). A gate-route parent's core
module (the S6 shape, `Tools.ShippingGateParentRun.InstanceNShape`) has the
body `[.inst c i conns, .assign "out" (.ref outW)]`, every connection a
reference. For that body:

* `dropZeroWidth_instBody` — the cleanup keeps the body, the ports and the
  name, given the output's entry in the module's width map is positive (the
  only statement it could drop is the `assign` to a width-0 name);
* `instBody_notAssign`, `mergeChecked_instBody` — the body is not
  assignment-only, so the checked merge is a `refineCheck`-accepted
  refinement or the module itself (the built `mergeChecked_nonAssign`), and
  it keeps the ports (`mergeChecked_ports`);
* `hierGate_instBody` — the instance gate of `checkedOptimize` holds on that
  body (so `checkedOptimize` takes the checked-deinline branch when
  `hierBinds` holds and returns the module unoptimised otherwise; the probe
  MEASURED `hierBinds b = true` on the eight parents — not proved here);
* `post_instBody` — the two passes together, on the module the full entry
  returns. -/
namespace Tools.ShippingGateParentPost
open Sparkle.IR.AST Sparkle.IR.ZeroWidth

/-- A connection list of references is fixed by the zero-width cleanup. -/
theorem dz_refConns (wm : Sparkle.IR.Optimize.WidthMap) :
    ∀ (conns : List (String × Sparkle.IR.AST.Expr)),
      (∀ c ∈ conns, ∃ x, c.2 = .ref x) →
      conns.map (fun p => (p.1, dzExpr wm p.2)) = conns
  | [], _ => rfl
  | (n, e) :: rest, h => by
    obtain ⟨x, hx⟩ := h (n, e) List.mem_cons_self
    rw [List.map_cons, dz_refConns wm rest (fun c' hc => h c' (List.mem_cons_of_mem _ hc))]
    show (n, dzExpr wm e) :: rest = (n, e) :: rest
    rw [Tools.ShippingPostSoundness.dzExpr_shaped wm e (Or.inr ⟨x, hx⟩)]

/-- **The zero-width cleanup on an instance body**: body, ports and name kept,
given the assigned name has a positive width in the module's width map. -/
theorem dropZeroWidth_instBody {M : Sparkle.IR.AST.Module} {cn iname : String}
    {conns : List (String × Sparkle.IR.AST.Expr)} {l r : String} {k : Nat}
    (hb : M.body = [.inst cn iname conns, .assign l (.ref r)])
    (hconns : ∀ c ∈ conns, ∃ x, c.2 = .ref x)
    (hl : (Sparkle.IR.Optimize.buildWidthMap M).get? l = some k) (hk : k ≠ 0) :
    (dropZeroWidthModule M).body = M.body ∧ (dropZeroWidthModule M).inputs = M.inputs ∧
      (dropZeroWidthModule M).outputs = M.outputs ∧ (dropZeroWidthModule M).name = M.name := by
  have h1 : dzStmt (Sparkle.IR.Optimize.buildWidthMap M) (.inst cn iname conns) =
      some (.inst cn iname conns) := by
    show some (Stmt.inst cn iname (conns.map fun p =>
      (p.1, dzExpr (Sparkle.IR.Optimize.buildWidthMap M) p.2))) = _
    rw [dz_refConns _ conns hconns]
  have h2 : dzStmt (Sparkle.IR.Optimize.buildWidthMap M) (.assign l (.ref r)) =
      some (.assign l (.ref r)) := by
    rw [Tools.ShippingRegisterSoundness.dzStmt_assign _ l (.ref r) hl hk,
      Tools.ShippingPostSoundness.dzExpr_shaped _ (.ref r) (Or.inr ⟨r, rfl⟩)]
  unfold dropZeroWidthModule
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · refine ⟨?_, rfl, rfl, rfl⟩
    show M.body.filterMap (dzStmt (Sparkle.IR.Optimize.buildWidthMap M)) = M.body
    rw [hb, List.filterMap_cons_some h1, List.filterMap_cons_some h2, List.filterMap_nil]

/-- The instance body is not assignment-only. -/
theorem instBody_notAssign (cn iname : String) (conns : List (String × Sparkle.IR.AST.Expr))
    (l : String) (rhs : Sparkle.IR.AST.Expr) :
    ([Stmt.inst cn iname conns, Stmt.assign l rhs] : List Stmt).all
      Sparkle.IR.RegDedup.isAssign = false := rfl

/-- **The checked merge on an instance body**: a `refineCheck`-accepted
refinement, or the module itself. -/
theorem mergeChecked_instBody {M : Sparkle.IR.AST.Module} {cn iname : String}
    {conns : List (String × Sparkle.IR.AST.Expr)} {l : String} {rhs : Sparkle.IR.AST.Expr}
    (hb : M.body = [.inst cn iname conns, .assign l rhs]) :
    Sparkle.IR.RefineCheck.refineCheck M (Sparkle.IR.RefineCheck.mergeChecked M) = true ∨
      Sparkle.IR.RefineCheck.mergeChecked M = M :=
  Sparkle.IR.RefineCheck.mergeChecked_nonAssign (by rw [hb]; exact instBody_notAssign _ _ _ _ _)

/-- **The instance gate of `checkedOptimize`** holds on the instance body. -/
theorem hierGate_instBody {M : Sparkle.IR.AST.Module} {cn iname : String}
    {conns : List (String × Sparkle.IR.AST.Expr)} {l : String} {rhs : Sparkle.IR.AST.Expr}
    (hb : M.body = [.inst cn iname conns, .assign l rhs]) :
    Sparkle.IR.RefineCheck.hierGate M = true := by
  unfold Sparkle.IR.RefineCheck.hierGate
  rw [hb]
  rfl

/-- **The two post passes on the module the full entry returns.** If the
returned module is the cleanup or the checked merge of the cleanup of a core
module with the instance body: it has the core module's ports, the cleaned
module has the core module's body and passes the instance gate, and the
returned module is the cleaned module or a `refineCheck`-accepted refinement
of it. -/
theorem post_instBody {M b : Sparkle.IR.AST.Module} {cn iname : String}
    {conns : List (String × Sparkle.IR.AST.Expr)} {l r : String} {k : Nat}
    (hpost : b = dropZeroWidthModule M ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (dropZeroWidthModule M))
    (hb : M.body = [.inst cn iname conns, .assign l (.ref r)])
    (hconns : ∀ c ∈ conns, ∃ x, c.2 = .ref x)
    (hl : (Sparkle.IR.Optimize.buildWidthMap M).get? l = some k) (hk : k ≠ 0) :
    (dropZeroWidthModule M).body = M.body ∧
      Sparkle.IR.RefineCheck.hierGate (dropZeroWidthModule M) = true ∧
      b.inputs = M.inputs ∧ b.outputs = M.outputs ∧
      (b = dropZeroWidthModule M ∨
        Sparkle.IR.RefineCheck.refineCheck (dropZeroWidthModule M) b = true) := by
  obtain ⟨hbody, hin, hout, -⟩ := dropZeroWidth_instBody hb hconns hl hk
  have hbz : (dropZeroWidthModule M).body = [.inst cn iname conns, .assign l (.ref r)] := by
    rw [hbody, hb]
  refine ⟨hbody, hierGate_instBody hbz, ?_, ?_, ?_⟩
  · rcases hpost with h | h
    · rw [h, hin]
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).1, hin]
  · rcases hpost with h | h
    · rw [h, hout]
    · rw [h, (Sparkle.IR.RefineCheck.mergeChecked_ports _).2.1, hout]
  · rcases hpost with h | h
    · exact Or.inl h
    · rcases mergeChecked_instBody hbz with h' | h'
      · right
        rw [h]
        exact h'
      · left
        rw [h, h']

end Tools.ShippingGateParentPost
