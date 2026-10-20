import Tools.ShippingGateDesignWalk
import Tools.ShippingGateParentPost

/-! # Gate-route parents, obstacle (B): the post passes keep the core module (worker N, round 11)

WRITTEN, NOT BUILT. PURE: about the IR passes only, no run.

`Tools.ShippingGateDesignLift.PostKeeps b M` (obstacle (B)): the returned
module `b` (`dropZeroWidthModule M` or its checked merge) has the core
module's body, the body is assignments and instances (`combStmtI`), and
`declWidth b = moduleWidths M`. Proved here from the walk's `ModOk N M`
(`Tools.ShippingGateDesignWalk`: an instance statement in the body, the body
of `op [ref, ref]` / `ref` assignments and reference-connected instances,
every port and wire a scalar of positive width) — generalising
`Tools.ShippingGateParentPost.post_instBody` from its two-statement shape:

* `dz_fields` — the zero-width cleanup keeps the body and the wires: every
  width in the module's width map is positive (`buildWidthMap_pos`), so no
  assignment is dropped and no wire filtered; every expression is a fixed
  point of `dzExpr` (`dzStmt_des`, with `dz_refConns` for instances);
* `refineCheck_of_inst`, `mergeChecked_of_inst` — a body holding an
  instance is not `seqStmtOk`, so `refineCheck` refuses every refinement and
  the checked merge returns the module itself (so the merge branch of the
  full entry IS the cleanup);
* `declWidth_eq_moduleWidths` — with scalar wires the two width readings
  agree;
* **`postKeeps_of_modOk`** — (B). -/
namespace Tools.ShippingGateDesignPost
open Sparkle.IR.AST Sparkle.IR.ZeroWidth
open Tools.ShippingGateParentRun (PosTy DesStmt HasInst ModOk)

/-- `filterMap` with a function fixing every element is the identity. -/
theorem filterMap_self {α : Type} {f : α → Option α} :
    ∀ (l : List α), (∀ a ∈ l, f a = some a) → l.filterMap f = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons_some (h a List.mem_cons_self),
      filterMap_self l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- A width read from a fold of port insertions comes from the start map or
from a port of the list. -/
theorem foldl_insert_get :
    ∀ (ports : List Port) (acc : Std.HashMap String Nat) (x : String) (k : Nat),
    (ports.foldl (fun acc (p : Port) => acc.insert p.name p.ty.bitWidth) acc).get? x = some k →
    acc.get? x = some k ∨ ∃ p ∈ ports, p.ty.bitWidth = k
  | [], _, _, _, h => Or.inl h
  | p :: ps, acc, x, k, h => by
    rcases foldl_insert_get ps (acc.insert p.name p.ty.bitWidth) x k h with h1 | ⟨q, hq, hk⟩
    · rw [Std.HashMap.get?_insert] at h1
      split at h1
      · exact Or.inr ⟨p, List.mem_cons_self, Option.some.inj h1⟩
      · exact Or.inl h1
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hk⟩

/-- **Every width in the module's width map is positive** when every port
and wire is a positive scalar. -/
theorem buildWidthMap_pos {m : Sparkle.IR.AST.Module}
    (hp : ∀ p ∈ m.inputs ++ m.outputs ++ m.wires, PosTy p.ty) {x : String} {k : Nat}
    (h : (Sparkle.IR.Optimize.buildWidthMap m).get? x = some k) : 0 < k := by
  have h' : (m.wires.foldl (fun acc (p : Port) => acc.insert p.name p.ty.bitWidth)
      (m.outputs.foldl (fun acc (p : Port) => acc.insert p.name p.ty.bitWidth)
        (m.inputs.foldl (fun acc (p : Port) => acc.insert p.name p.ty.bitWidth)
          ({} : Std.HashMap String Nat)))).get? x = some k := h
  have pos : ∀ p ∈ m.inputs ++ m.outputs ++ m.wires, 0 < p.ty.bitWidth :=
    fun p hp' => Tools.ShippingGateParentRun.PosTy.bitWidth_pos (hp p hp')
  rcases foldl_insert_get _ _ _ _ h' with h1 | ⟨p, hp', hk⟩
  · rcases foldl_insert_get _ _ _ _ h1 with h2 | ⟨p, hp', hk⟩
    · rcases foldl_insert_get _ _ _ _ h2 with h3 | ⟨p, hp', hk⟩
      · simp at h3
      · rw [← hk]
        exact pos p (by simp [hp'])
    · rw [← hk]
      exact pos p (by simp [hp'])
  · rw [← hk]
    exact pos p (by simp [hp'])

/-- An assignment to a name of nonzero width is kept, its expression cleaned. -/
theorem dzStmt_assign_pos (wm : Sparkle.IR.Optimize.WidthMap) (l : String)
    (r : Sparkle.IR.AST.Expr) (h : ∀ k, wm.get? l = some k → k ≠ 0) :
    dzStmt wm (.assign l r) = some (.assign l (dzExpr wm r)) := by
  cases hg : wm.get? l with
  | none =>
    have hg' : wm[l]? = none := by
      first
        | exact hg
        | (rw [← Std.HashMap.get?_eq_getElem?]; exact hg)
        | simpa using hg
    simp [dzStmt, hg']
  | some k => exact Tools.ShippingRegisterSoundness.dzStmt_assign wm l r hg (h k hg)

/-- **The cleanup fixes every statement of the walk's shape** in a width map
without zero widths. -/
theorem dzStmt_des (wm : Sparkle.IR.Optimize.WidthMap)
    (hpos : ∀ x k, wm.get? x = some k → 0 < k) :
    ∀ st, DesStmt st → dzStmt wm st = some st := by
  intro st hst
  rcases hst with ⟨l, o, a, b, rfl⟩ | ⟨l, x, rfl⟩ | ⟨mn, i, cs, rfl, hcs⟩
  · rw [dzStmt_assign_pos wm l _ (fun k hk => Nat.pos_iff_ne_zero.mp (hpos l k hk))]
    simp [dzExpr, dzList]
  · rw [dzStmt_assign_pos wm l _ (fun k hk => Nat.pos_iff_ne_zero.mp (hpos l k hk))]
    simp [dzExpr]
  · show some (Stmt.inst mn i (cs.map fun p => (p.1, dzExpr wm p.2))) = _
    rw [Tools.ShippingGateParentPost.dz_refConns wm cs hcs]

/-- **The zero-width cleanup keeps the walk's module's body and wires.** -/
theorem dz_fields {N : String} {m : Sparkle.IR.AST.Module} (h : ModOk N m) :
    (dropZeroWidthModule m).body = m.body ∧ (dropZeroWidthModule m).wires = m.wires := by
  have hpos : ∀ x k, (Sparkle.IR.Optimize.buildWidthMap m).get? x = some k → 0 < k :=
    fun _ _ hk => buildWidthMap_pos h.ports hk
  have hb : m.body.filterMap (dzStmt (Sparkle.IR.Optimize.buildWidthMap m)) = m.body :=
    filterMap_self m.body (fun st hst => dzStmt_des _ hpos st (h.body st hst))
  have hw : m.wires.filter (fun p => p.ty.bitWidth != 0) = m.wires := by
    apply List.filter_eq_self.mpr
    intro p hp
    have h0 : 0 < p.ty.bitWidth := Tools.ShippingGateParentRun.PosTy.bitWidth_pos (h.ports p (by simp [hp]))
    exact bne_iff_ne.mpr (Nat.pos_iff_ne_zero.mp h0)
  unfold dropZeroWidthModule
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨hb, hw⟩

/-- **`refineCheck` refuses every refinement of a body holding an instance**
(`seqStmtOk` is false on an instance statement). -/
theorem refineCheck_of_inst {m o : Sparkle.IR.AST.Module} (h : HasInst m.body) :
    Sparkle.IR.RefineCheck.refineCheck m o = false := by
  obtain ⟨mn, i, cs, hmem⟩ := h
  have hS : m.body.all Sparkle.IR.OptCheck.seqStmtOk = false := by
    cases hc : m.body.all Sparkle.IR.OptCheck.seqStmtOk with
    | false => rfl
    | true =>
      have := List.all_eq_true.mp hc _ hmem
      simp [Sparkle.IR.OptCheck.seqStmtOk] at this
  unfold Sparkle.IR.RefineCheck.refineCheck
  simp [hS]

/-- **The checked merge returns a module holding an instance unchanged.** -/
theorem mergeChecked_of_inst {m : Sparkle.IR.AST.Module} (h : HasInst m.body) :
    Sparkle.IR.RefineCheck.mergeChecked m = m := by
  have hA : m.body.all Sparkle.IR.RegDedup.isAssign = false := by
    obtain ⟨mn, i, cs, hmem⟩ := h
    cases hc : m.body.all Sparkle.IR.RegDedup.isAssign with
    | false => rfl
    | true =>
      have := List.all_eq_true.mp hc _ hmem
      simp [Sparkle.IR.RegDedup.isAssign] at this
  have hR := refineCheck_of_inst (o := Sparkle.IR.RegDedup.mergeDuplicates m) h
  unfold Sparkle.IR.RefineCheck.mergeChecked
  simp [hA, hR]

/-- With scalar wires, the declared widths and the module widths agree. -/
theorem declWidth_eq_moduleWidths {m : Sparkle.IR.AST.Module}
    (hw : ∀ p ∈ m.wires, PosTy p.ty) :
    Sparkle.IR.RegDedup.declWidth m = Tools.ShippingMixedEntrySoundness.moduleWidths m := by
  funext x
  cases hf : m.wires.find? (fun p => p.name == x) with
  | none =>
    simp [Sparkle.IR.RegDedup.declWidth, Tools.ShippingMixedEntrySoundness.moduleWidths, hf]
  | some p =>
    have hp := hw p (List.mem_of_find?_eq_some hf)
    obtain ⟨pn, pty⟩ := p
    rcases hp with hb | ⟨n, -, hn⟩
    · simp only at hb
      subst hb
      simp [Sparkle.IR.RegDedup.declWidth, Tools.ShippingMixedEntrySoundness.moduleWidths, hf,
        Sparkle.IR.Type.HWType.bitWidth]
    · simp only at hn
      subst hn
      simp [Sparkle.IR.RegDedup.declWidth, Tools.ShippingMixedEntrySoundness.moduleWidths, hf,
        Sparkle.IR.Type.HWType.bitWidth]

/-- **Obstacle (B) from the walk's `ModOk`**: whichever post pass the full
entry ran, the returned module has the core body (assignments and
instances) and its declared widths are the core module's widths. -/
theorem postKeeps_of_modOk {N : String} {M b : Sparkle.IR.AST.Module} (h : ModOk N M)
    (hpost : b = dropZeroWidthModule M ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (dropZeroWidthModule M)) :
    Tools.ShippingGateDesignLift.PostKeeps b M := by
  obtain ⟨hb, hw⟩ := dz_fields h
  have hasZ : HasInst (dropZeroWidthModule M).body := by
    rw [hb]
    exact h.has
  have hmc : Sparkle.IR.RefineCheck.mergeChecked (dropZeroWidthModule M) =
      dropZeroWidthModule M := mergeChecked_of_inst hasZ
  have hbz : b = dropZeroWidthModule M := by
    rcases hpost with e | e
    · exact e
    · rw [e, hmc]
  subst hbz
  refine ⟨?_, hb, ?_⟩
  · rw [List.all_eq_true]
    intro st hst
    rcases h.body st hst with ⟨l, o, a, c, rfl⟩ | ⟨l, x, rfl⟩ | ⟨mn, i, cs, rfl, -⟩ <;> rfl
  · have hdw : Sparkle.IR.RegDedup.declWidth (dropZeroWidthModule M) =
        Sparkle.IR.RegDedup.declWidth M := by
      funext x
      unfold Sparkle.IR.RegDedup.declWidth
      rw [hw]
    rw [hdw]
    exact declWidth_eq_moduleWidths (fun p hp => h.ports p (by simp [hp]))

end Tools.ShippingGateDesignPost

#print axioms Tools.ShippingGateDesignPost.dz_fields
#print axioms Tools.ShippingGateDesignPost.mergeChecked_of_inst
#print axioms Tools.ShippingGateDesignPost.postKeeps_of_modOk
