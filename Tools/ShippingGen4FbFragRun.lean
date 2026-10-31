import Tools.ShippingGen4FbPP
import Tools.ShippingFirstGateChild
import Tools.ShippingGen2CombKid
import Tools.ShippingMachineShipsComb
-- BUILT (unit FB-22): `kjob lake build Tools.ShippingGen4FbFragRun` exit 0 (705 jobs) in the Pod (Lean commit 7dd7d127; comment-only header edit after); NOT a clean issue-linked build (coder). Written against scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §33.3 (freeze 14e312de, approved, committed before this file).
-- NOT BUILT (unit FB-22): written against scripts/gen4/FALLBACK_SUPPLY_FREEZE.md §33.3 (freeze 14e312de, approved, committed before this file).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # FB-22: `ChildRunN` for the real full-entry module of a first-gate fragment (from `ChildFnR`), both `PPRel` arms

Partial supply. Conditional on `EntryDefines`, `WF`, `0 < n` and the pointwise premise `hS` on the package's `S`
(not supplied here); first-gate fragments only. Says nothing about `S`'s correspondence with the package,
instance-bearing bodies, non-fragment `mergeChecked`, T-LEG, T-MEMO, K4, M4 or FG. -/

namespace Tools.ShippingGen4FbFragRun
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.RegDedup (isAssign)
open Tools.ShippingMachineShipsComb (regNexts_assigns memNexts_assigns applyNexts_nil)

theorem runModule_assigns_exists {we : Sparkle.IR.Semantics.WEnv} {body : List Sparkle.IR.AST.Stmt}
    {seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env}
    (hA : body.all Sparkle.IR.RegDedup.isAssign = true)
    (st : String → Nat) (mems : Sparkle.IR.Semantics.MEnv) :
    ∀ (T : Nat),
      (∀ j, j < T → ∃ e, Sparkle.IR.Semantics.evalAssigns we mems body (seed j st) = some e) →
      ∃ envs, Sparkle.IR.Semantics.runModule we body seed T st mems = some envs
  | 0, _ => ⟨[], rfl⟩
  | k + 1, h => by
    obtain ⟨e, he⟩ := h k (Nat.lt_succ_self k)
    obtain ⟨rest, hr⟩ := runModule_assigns_exists hA st mems k (fun j hj => h j (Nat.lt_succ_of_lt hj))
    refine ⟨e :: rest, ?_⟩
    simp only [runModule, stepModule, he, regNexts_assigns hA, memNexts_assigns hA, Option.bind_eq_bind,
      Option.bind_some, applyNexts_nil, hr]

theorem combChildRunN_of_childFnR
    {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {n : Nat} {mc : Sparkle.IR.AST.Module}
    {bsC : List (Lean.Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {o : Sparkle.IR.Machine.OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    {F : List Nat → Nat}
    (hpf : Tools.ShippingGen4FbPP.CombPortFacts mc bsC [o])
    (hA : mc.body.all Sparkle.IR.RegDedup.isAssign = true)
    (hfn : Tools.ShippingFirstGateChild.ChildFnR mc
      (fun vs => Tools.ShippingMachineChild.InRange vs (bsC.filter fun b => b.2 != .domain)) F)
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j) (bsC.filter fun b => b.2 != .domain) →
        f j = F (vals j)) :
    Tools.ShippingGen2.CombChildRunN ch dsn n mc bsC [o] S := by
  obtain ⟨houts, hnd, hclk, hrst, hdisj, hlen⟩ := hpf
  obtain ⟨outP, hout, hf⟩ := hfn
  refine ⟨houts, hnd, hclk, hrst, hdisj, hlen, ?_⟩
  intro T ins s vals hrange hports _hreset
  have hseed : ∀ (t : Nat) (st : String → Nat),
      (Tools.ShippingMachineCompose.argPorts mc).map
          (fun p => Tools.ShippingSeqOptSoundness.seedIn mc ins t st p.name) =
        (Tools.ShippingMachineCompose.argPorts mc).map (fun p => ins t p.name) := by
    intro t st
    apply List.map_congr_left
    intro p hp
    have hpin : p ∈ mc.inputs := (List.mem_filter.mp hp).1
    have hc : (mc.inputs.map (·.name)).contains p.name = true :=
      List.contains_iff_mem.mpr (List.mem_map_of_mem hpin)
    simp only [Tools.ShippingSeqOptSoundness.seedIn, hc, if_true]
  have hex : ∀ j, j < T → ∃ cres,
      evalAssigns (Sparkle.IR.RegDedup.declWidth mc) (Tools.ShippingHierStateG.memsOf n s) mc.body
        (Tools.ShippingSeqOptSoundness.seedIn mc ins j (Tools.ShippingHierStateG.stOf n s)) = some cres ∧
      cres outP.name = F (vals (T - 1 - j)) := by
    intro j hj
    have hv : (Tools.ShippingMachineCompose.argPorts mc).map
        (fun p => Tools.ShippingSeqOptSoundness.seedIn mc ins j (Tools.ShippingHierStateG.stOf n s) p.name) =
        vals (T - 1 - j) := by
      rw [hseed]; exact hports j hj
    obtain ⟨cres, hev, hres⟩ := hf (Tools.ShippingHierStateG.memsOf n s)
      (Tools.ShippingSeqOptSoundness.seedIn mc ins j (Tools.ShippingHierStateG.stOf n s))
      (by rw [hv]; exact hrange (T - 1 - j) (by omega))
    exact ⟨cres, hev, by rw [hres, hv]⟩
  obtain ⟨envs, hrun⟩ := runModule_assigns_exists (we := Sparkle.IR.RegDedup.declWidth mc)
    (seed := Tools.ShippingSeqOptSoundness.seedIn mc ins) hA (Tools.ShippingHierStateG.stOf n s)
    (Tools.ShippingHierStateG.memsOf n s) T
    (fun j hj => by obtain ⟨c, hc, -⟩ := hex j hj; exact ⟨c, hc⟩)
  refine ⟨envs, ?_, ?_, ?_⟩
  · rw [Tools.ShippingMachineDepth.RunOn_instFree ch mc (Tools.ShippingGen2.instFree_of_assigns hA)]
    exact hrun
  · exact (Tools.ShippingGen2.runModule_assigns_get hA T _ _ envs hrun).1
  · intro j hj k o' f ho hf'
    obtain ⟨hl, hg⟩ := Tools.ShippingGen2.runModule_assigns_get hA T _ _ envs hrun
    have hjT : j < T := by omega
    obtain ⟨cres, hev, hres⟩ := hex (T - 1 - j) (by omega)
    have h1 := hg j hj
    rw [hev] at h1
    have h2 : cres = envs[j]'hj := Option.some.inj h1
    have hk : k = 0 ∧ o' = o := by
      cases k with
      | zero => exact ⟨rfl, by simpa using ho.symm⟩
      | succ k => simp at ho
    obtain ⟨rfl, rfl⟩ := hk
    have hon : outP.name = o'.name := by
      rw [hout] at houts
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at houts
      rw [houts.1]
    rw [← hon, ← h2, hres, show T - 1 - (T - 1 - j) = j by omega]
    exact (hS vals f hf' j (hrange j hjT)).symm

theorem synthesizeCombinational_fragment_childRunN {declName : Lean.Name} {mctx : Lean.Meta.Context}
    {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    {dn : Lean.Name} {names : List Lean.Name} {n : Nat} {fe : Tools.ShippingEntrySoundness.FExpr}
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational declName)
      mctx mref cctx cref w (b, design) w')
    (entry : Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref declName
      (Tools.ShippingEntrySoundness.quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n)
    {ch : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Sparkle.IR.AST.Design} {m : Nat}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hS : ∀ (vals : Nat → List Nat) (f : Nat → Nat), (S vals)[0]? = some f →
      ∀ j, Tools.ShippingMachineChild.InRange (vals j)
          ((Tools.ShippingFirstGateChild.firstBs dn names n).filter fun x => x.2 != .domain) →
        f j = Tools.ShippingFirstGateChild.firstFn dn names n fe (vals j)) :
    Tools.ShippingGen2.ChildRunN ch dsn m b (Tools.ShippingFirstGateChild.firstBs dn names n)
      [({ name := "out", lo := 0, width := n, ty := .bitVector n } : Sparkle.IR.Machine.OutField)] S := by
  have hfn := Tools.ShippingFirstGateChild.first_child_fnR hr entry hwf hn
  have hout := Tools.ShippingFirstGateChild.first_full_outputs hr entry hwf hn
  obtain ⟨hnd, hlen, hin⟩ := Tools.ShippingFirstGateChild.first_full_inputs hr entry hwf hn
  have full := Tools.ShippingFirstGateChild.first_child_fullFacts hr entry hwf hn
  refine Or.inr (combChildRunN_of_childFnR ?_ full.comb.assigns hfn hS)
  have hap : Tools.ShippingMachineCompose.argPorts b = b.inputs := by
    unfold Tools.ShippingMachineCompose.argPorts
    apply List.filter_eq_self.mpr
    intro p hp
    obtain ⟨-, h1, h2, -⟩ := hin p hp
    simp [h1, h2]
  refine ⟨hout, hnd, ?_, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp h
    exact (hin p hp).2.1 hpn
  · intro h
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp h
    exact (hin p hp).2.2.1 hpn
  · intro x hx hxi
    rw [hout] at hx
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
    subst hx
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hxi
    exact (hin p hp).2.2.2 hpn
  · rw [hap, hlen, Tools.ShippingFirstGateChild.firstBs_filter]
    simp

end Tools.ShippingGen4FbFragRun
