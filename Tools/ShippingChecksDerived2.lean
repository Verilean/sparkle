import Tools.ShippingChecksDerived
import Tools.ShippingHierShipsSV

/-! # Output checks on the optimized body, from the compiler's own checks (G1)

The endpoints' checks speak about `(checkedOptimize b).body`, the printed
module. `checkedOptimize` keeps an optimizer output of an instance-bearing
module only under `hierRefineCheck`, whose first two conjuncts are
`instsKept` both ways. Hence:

* `hierRefineCheck_inst_iff`: under `hierRefineCheck m o`, a statement is an
  instance statement of `o` iff it is one of `m` (MEMBERSHIP both ways —
  that is what the check gives; see below for what it does not give);
* `checkedOptimize_inst_iff`: where the instance gate binds (`hierBinds b`),
  the instance statements of `(checkedOptimize b).body` are those of
  `b.body`, as sets;
* every check of the form "each instance statement satisfies …" moves from
  `b.body` to `(checkedOptimize b).body`: `all_inst_transfer` and its
  instances `kidsPass_opt`, `kidsComb_opt`, `kidsLocal_opt`, `kidsMem_opt`,
  `kidsMasked_opt`, `kidsMixed_opt`, `kidsMaskedN_opt`, `noSelfRead_opt`,
  `resolved_opt`.

Outputs assigned, through `refineCheck`:
* `rNormBody_lookup`, `refineCheck_outs_assigned`,
  `outsAssigned_of_refineCheck`: a module `refineCheck` accepts as the
  refinement assigns every output (the check asks a normal form of each);
* `mergeChecked_outsAssigned`: the checked merge of a body with a
  non-assignment keeps "every output assigned";
* `outsLeaf_of_assigned`.

A module with instances whose children are leaves:
* `outsCheck0_opt`: the depth-0 `outsCheck` of the PRINTED module, from
  `hierBinds b`, the resolution of `b`'s instance statements in the design's
  modules, and each resolved child assigning its outputs (`outsA`).

What is NOT proved here
* `(instNames (checkedOptimize b).body).Nodup` from `(instNames b.body).Nodup`:
  NOT derivable from `hierRefineCheck` — `instsKept` is membership, and
  `deinline` rebuilds the body statement by statement from the optimizer's
  output, so a repeated instance statement in that output would pass the
  check. It needs a fact about the optimizer (it does not duplicate
  instance statements) or a stronger check (the instance statements as a
  LIST). Same for `linkedWF` of the optimized body (order).
* `outsCheck0_opt` over a RUN: its hypothesis `hres` (each instance statement
  of the full entry's module resolves in the full entry's design to a
  child's module) is inside the proof of
  `Tools.ShippingKidsChildIface.kidsChild_iface` (`MachineWired`, the design
  join), not in its conclusion `ChildIfaceD` (which has the instance NAMES
  only). It has to be exported there before this composes with a run.
* The checked merge of an assignment-only body (a slotless child): its merge
  is validated by `validateMerge`, not `refineCheck`; not treated. -/
namespace Tools.ShippingChecksDerived2
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Tools.ShippingOptSoundness (lookup_cons_eq')
open Tools.ShippingChecksDerived
open Tools.ShippingMachineLinked (childMap)

/-! ## Instance statements under the hierarchical check -/

/-- **`hierRefineCheck` keeps the instance statements, as a set.** -/
theorem hierRefineCheck_inst_iff {m o : Sparkle.IR.AST.Module}
    (h : hierRefineCheck m o = true) (mn iname : String) (conns : List (String × Expr)) :
    Stmt.inst mn iname conns ∈ o.body ↔ Stmt.inst mn iname conns ∈ m.body := by
  simp only [hierRefineCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hk1, hk2⟩, -⟩, -⟩, -⟩ := h
  exact ⟨Tools.ShippingHierOptSoundness.instsKept_mem hk1 mn iname conns,
    Tools.ShippingHierOptSoundness.instsKept_mem hk2 mn iname conns⟩

/-- **The printed module has the full entry's instance statements**, where
the instance gate binds. -/
theorem checkedOptimize_inst_iff {b : Sparkle.IR.AST.Module} (hb : hierBinds b = true)
    (mn iname : String) (conns : List (String × Expr)) :
    Stmt.inst mn iname conns ∈ (checkedOptimize b).body ↔ Stmt.inst mn iname conns ∈ b.body := by
  have hI := Tools.ShippingMachineShipsHier.hasInst_of_hierBinds hb
  have hopt : checkedOptimize b = (if hierRefineCheck b
      (Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b))
      then Sparkle.IR.HierCheck.deinline b (Sparkle.IR.Optimize.optimizeModule b) else b) := by
    unfold checkedOptimize
    simp only [Tools.ShippingMachineShipsHier.simpleBody_inst hI,
      Tools.ShippingMachineShipsHier.not_all_seqOk hI, hb, Bool.false_eq_true, if_false, if_true]
  rw [hopt]
  split
  · rename_i h
    exact hierRefineCheck_inst_iff h mn iname conns
  · exact Iff.rfl

/-- A per-statement check that accepts every non-instance statement moves to
a body whose instance statements are among the first body's. -/
theorem all_inst_transfer {body body' : List Stmt} (g : Stmt → Bool)
    (hsub : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body' →
      Stmt.inst mn iname conns ∈ body)
    (hg : ∀ st, (∀ mn iname conns, st ≠ Stmt.inst mn iname conns) → g st = true)
    (h : body.all g = true) : body'.all g = true :=
  List.all_eq_true.mpr fun st hst => by
    cases st with
    | inst mn iname conns => exact List.all_eq_true.mp h _ (hsub mn iname conns hst)
    | _ => exact hg _ (fun _ _ _ e => by cases e)

section
variable {b : Sparkle.IR.AST.Module} (hb : hierBinds b = true)
include hb

theorem kidsPass_opt {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    {f : Sparkle.IR.AST.Module → Bool}
    (h : Tools.ShippingDesignSV.kidsPass C f b.body = true) :
    Tools.ShippingDesignSV.kidsPass C f (checkedOptimize b).body = true :=
  all_inst_transfer _ (fun mn iname conns => (checkedOptimize_inst_iff hb mn iname conns).mp)
    (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) h

theorem kidsComb_opt {ms : List Sparkle.IR.AST.Module}
    (h : Tools.ShippingMachineDepthH.kidsComb ms b.body = true) :
    Tools.ShippingMachineDepthH.kidsComb ms (checkedOptimize b).body = true :=
  all_inst_transfer _ (fun mn iname conns => (checkedOptimize_inst_iff hb mn iname conns).mp)
    (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) h

theorem kidsLocal_opt {ms : List Sparkle.IR.AST.Module}
    (h : Tools.ShippingHierOptRunH.kidsLocal ms b.body = true) :
    Tools.ShippingHierOptRunH.kidsLocal ms (checkedOptimize b).body = true :=
  all_inst_transfer _ (fun mn iname conns => (checkedOptimize_inst_iff hb mn iname conns).mp)
    (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) h

theorem kidsMem_opt {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    (h : Tools.ShippingMachineShipsHier.kidsMem C b.body = true) :
    Tools.ShippingMachineShipsHier.kidsMem C (checkedOptimize b).body = true :=
  all_inst_transfer _ (fun mn iname conns => (checkedOptimize_inst_iff hb mn iname conns).mp)
    (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) h

theorem kidsMasked_opt {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    (h : Tools.ShippingMachineShipsHier.kidsMasked C b.body = true) :
    Tools.ShippingMachineShipsHier.kidsMasked C (checkedOptimize b).body = true :=
  all_inst_transfer _ (fun mn iname conns => (checkedOptimize_inst_iff hb mn iname conns).mp)
    (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) h

theorem kidsMixed_opt {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    (h : Tools.ShippingMachineShipsHier.kidsMixed C b.body = true) :
    Tools.ShippingMachineShipsHier.kidsMixed C (checkedOptimize b).body = true :=
  all_inst_transfer _ (fun mn iname conns => (checkedOptimize_inst_iff hb mn iname conns).mp)
    (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) h

theorem kidsMaskedN_opt {ms : List Sparkle.IR.AST.Module}
    (h : Tools.ShippingMachineShipsDepth.kidsMaskedN ms b.body = true) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN ms (checkedOptimize b).body = true :=
  all_inst_transfer _ (fun mn iname conns => (checkedOptimize_inst_iff hb mn iname conns).mp)
    (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) h

theorem noSelfRead_opt {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    (h : Tools.ShippingHierPremisesBase.noSelfRead C b.body = true) :
    Tools.ShippingHierPremisesBase.noSelfRead C (checkedOptimize b).body = true :=
  all_inst_transfer _ (fun mn iname conns => (checkedOptimize_inst_iff hb mn iname conns).mp)
    (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) h

/-- Resolution of the instance statements moves to the printed module. -/
theorem resolved_opt {C : String → Option (Sparkle.IR.AST.Module × WEnv)}
    {P : Sparkle.IR.AST.Module → Prop}
    (h : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ child cwe, C mn = some (child, cwe) ∧ P child) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      ∃ child cwe, C mn = some (child, cwe) ∧ P child :=
  fun mn iname conns hm => h mn iname conns ((checkedOptimize_inst_iff hb mn iname conns).mp hm)

end

/-! ## Outputs assigned, through `refineCheck` -/

/-- A name with a normal form after `rNormBody` had one before or is assigned
in the body. -/
theorem rNormBody_lookup {we : WEnv} {ins : List String} :
    ∀ (body : List Stmt) (defs D : List (String × Expr)) (x : String) (e : Expr),
      rNormBody we ins defs body = some D → D.lookup x = some e →
      (∃ e', defs.lookup x = some e') ∨ ∃ r, Stmt.assign x r ∈ body
  | [], defs, D, x, e, h, hx => by
    simp only [rNormBody, Option.some.injEq] at h
    subst h
    exact Or.inl ⟨e, hx⟩
  | .assign l r :: rest, defs, D, x, e, h, hx => by
    simp only [rNormBody] at h
    cases he : rNormE we ins defs r with
    | none => simp [he] at h
    | some e0 =>
      simp only [he, Option.bind_eq_bind, Option.bind_some] at h
      rcases rNormBody_lookup rest _ D x e h hx with ⟨e', hl⟩ | ⟨r', hr'⟩
      · rw [lookup_cons_eq'] at hl
        split at hl
        · rename_i hxl
          subst hxl
          exact Or.inr ⟨r, List.Mem.head _⟩
        · exact Or.inl ⟨e', hl⟩
      · exact Or.inr ⟨r', List.Mem.tail _ hr'⟩
  | .register .. :: _, _, _, _, _, h, _ => by simp [rNormBody] at h
  | .memory .. :: _, _, _, _, _, h, _ => by simp [rNormBody] at h
  | .inst .. :: _, _, _, _, _, h, _ => by simp [rNormBody] at h

/-- **A module `refineCheck` accepts as the refinement assigns every output.** -/
theorem refineCheck_outs_assigned {m o : Sparkle.IR.AST.Module} (h : refineCheck m o = true) :
    ∀ p ∈ o.outputs, ∃ r, Stmt.assign p.name r ∈ o.body := by
  have hports := (Tools.ShippingRefineSoundness.refineCheck_ports h).2
  simp only [refineCheck] at h
  rw [Bool.and_eq_true] at h
  obtain ⟨-, h2⟩ := h
  intro p hp
  rw [hports] at hp
  split at h2
  · rename_i dm dO hdm hdO
    simp only [Bool.and_eq_true] at h2
    obtain ⟨⟨hA, -⟩, -⟩ := h2
    have hp' := List.all_eq_true.mp hA p hp
    split at hp'
    · rename_i em eo hem heo
      rcases rNormBody_lookup _ _ _ _ _ hdO heo with ⟨e', hl⟩ | ⟨r, hr⟩
      · have hl' : (none : Option Expr) = some e' := hl
        cases hl'
      · exact ⟨r, (List.mem_filter.mp hr).1⟩
    · cases hp'
  · cases h2

theorem outsAssigned_of_assigned {m : Sparkle.IR.AST.Module}
    (h : ∀ p ∈ m.outputs, ∃ r, Stmt.assign p.name r ∈ m.body) :
    Tools.ShippingDesignSVBack.outsAssigned m = true := by
  unfold Tools.ShippingDesignSVBack.outsAssigned
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  rw [List.any_eq_true]
  exact ⟨Stmt.assign p.name r, hr, by simp⟩

theorem outsLeaf_of_assigned {m : Sparkle.IR.AST.Module}
    (h : ∀ p ∈ m.outputs, ∃ r, Stmt.assign p.name r ∈ m.body) :
    Tools.ShippingDesignSV.outsLeaf m = true := by
  unfold Tools.ShippingDesignSV.outsLeaf
  rw [List.all_eq_true]
  intro p hp
  obtain ⟨r, hr⟩ := h p hp
  rw [List.any_eq_true]
  exact ⟨Stmt.assign p.name r, hr, by simp⟩

theorem outsAssigned_of_refineCheck {m o : Sparkle.IR.AST.Module}
    (h : refineCheck m o = true) : Tools.ShippingDesignSVBack.outsAssigned o = true :=
  outsAssigned_of_assigned (refineCheck_outs_assigned h)

/-- The checked merge of a body with a non-assignment keeps "every output
assigned": the merge is kept only under `refineCheck`. -/
theorem mergeChecked_outsAssigned {m : Sparkle.IR.AST.Module}
    (hna : m.body.all Sparkle.IR.RegDedup.isAssign = false)
    (ha : Tools.ShippingDesignSVBack.outsAssigned m = true) :
    Tools.ShippingDesignSVBack.outsAssigned (mergeChecked m) = true := by
  rcases mergeChecked_nonAssign hna with hrc | heq
  · exact outsAssigned_of_refineCheck hrc
  · rw [heq]
    exact ha

/-! ## A module with instances whose children are leaves -/

/-- **The depth-0 `outsCheck` of the PRINTED module of a machine with
calls.** `hres`: every instance statement of the full entry's module
resolves, among the design's modules, to a module; `outsA`: each such module
assigns its outputs (the one fact asked of a child beyond `ChildIfaceG`). -/
theorem outsCheck0_opt {b : Sparkle.IR.AST.Module} {ms : List Sparkle.IR.AST.Module}
    (hb : hierBinds b = true)
    (hres : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, Sparkle.IR.Machine.moduleByName ms mn = some mc)
    (outsA : ∀ mn mc, Sparkle.IR.Machine.moduleByName ms mn = some mc →
      (∃ iname conns, Stmt.inst mn iname conns ∈ b.body) →
      Tools.ShippingDesignSVBack.outsAssigned mc = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap ms) 0 (checkedOptimize b) = true :=
  outsCheck0_of_insts fun mn iname conns hm => by
    have hmb := (checkedOptimize_inst_iff hb mn iname conns).mp hm
    obtain ⟨mc, hmc⟩ := hres mn iname conns hmb
    exact ⟨mc, _, congrArg (Option.map fun c => (c, Sparkle.IR.RegDedup.declWidth c)) hmc,
      outsLeaf_of_assigned
        (Tools.ShippingDesignSVBack.outsAssigned_sound (outsA mn mc hmc ⟨iname, conns, hmb⟩))⟩

end Tools.ShippingChecksDerived2
