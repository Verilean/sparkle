import Tools.ShippingGen2C6
import Tools.ShippingGen2Defs
set_option autoImplicit false
-- WRITTEN, NOT BUILT (2026-10-29). To be confirmed by
-- `kjob lake build Tools.ShippingGen2SlotlessParent` (scripts/gen2/S5_SLOTLESS_FREEZE.md §9).
-- Case (S) of A3 is C6 (Tools/ShippingGen2C6.lean:59-137) verbatim: MARKED FOR BUILD CONFIRMATION.

/-! # S5 stage A: slotless parents, pure lemmas (scripts/gen2/S5_SLOTLESS_FREEZE.md rev0 §3)

* A1 `calls_ports_sl`: `calls_ports` (MachineDepthChild:41-56) with `hsl : slots ≠ []` replaced by
  `hsl0 : slots = []`; the clock/reset conjuncts become ONE disjunction, decided by the wiring's `extra`
  (`MachineWired`'s input clause, MachineEntry:742): case (S) `extra = [clk, rst]` (both inputs), case (C)
  `extra = []` (neither).
* A2 `NoTouchZ`, `runModuleTG_seed_offZ`: the `runModuleTG` analogue of S1 (`runModule_seed_local`, Gen2Comb:28) /
  `runModule_rst_irrel` (SlotlessLeaf:108): a body of assignments and instances none of which reads or writes a
  name of `Z` (assignments by `refsOf`, instances by their `.ref` connections) runs the same off `Z` from two seeds
  that agree off `Z`. Instances use `KSLocal` (HierStateG:30): the same child step, the same `bindOuts` writes
  (`bindOuts` writes only on `some (.ref w)`, HierarchySoundness:30-34), and `regNexts`/`memNexts` are `[]`/identity,
  so the next state (registers, memories AND kids) is the SAME (`stepModuleTG_offZ`, the intermediate lemma).
* A3 `slSeedZ`, `childRunN_of_composedNW_runSl`: C6 (Gen2C6:29-55) with `hsl0`, one new internal premise `hZ`
  (discharged by B1 from the run), conclusion `ChildRunN`. Case (S): C6's proof verbatim, `Or.inl`. Case (C):
  `ComposedNW`'s `H` at the zeroed seed `slSeedZ`, then A2 at `Z := ["rst", "clk"]` to `seedIn`.

No new semantic premise (`hZ` is internal, B1). No `SeqKid`. The case is decided from the module's actual inputs. -/
namespace Tools.ShippingGen2SlotlessParent
-- Gen2C6:13-24
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge
open Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierMono
open Tools.ShippingMachineDepth Tools.ShippingMachineDepthChild Tools.ShippingMachineDepthRun
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineCompose (argPorts machPorts_length)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingEntrySoundness (RunsTo)
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildRunAKids
open Tools.ShippingMachineDepthRunRA Tools.ShippingMachineCallsLinkedTNR Tools.ShippingChildBndCore Tools.ShippingChildInv
-- MachineDepthChild:19 (for A1)
open Tools.ShippingMachineCompose (machPorts_append)

/-! ## Small facts -/

/-- An allocated name is neither the reset nor the clock. -/
theorem allocated_notZ {x : String} (h : Sparkle.IR.NameHints.Allocated x) : x ∉ ["rst", "clk"] := by
  intro hx
  rcases List.mem_cons.mp hx with h1 | h1
  · exact Tools.ShippingRegisterSoundness.not_allocated_rst (h1 ▸ h)
  · exact Tools.ShippingMachineCleanup.not_allocated_clk ((List.mem_singleton.mp h1) ▸ h)

/-- An `outNameOk` name is neither the reset nor the clock (`outNameOk_facts`; the clock as in `calls_ports`). -/
theorem outName_notZ {s : String} (hok : outNameOk s = true) : s ∉ ["rst", "clk"] := by
  have hr : s ≠ "rst" := (Tools.ShippingMachineClose.outNameOk_facts hok).2.1
  have hc : s ≠ "clk" := by
    simp only [outNameOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    exact hok.2
  intro hx
  rcases List.mem_cons.mp hx with h1 | h1
  · exact hr h1
  · exact hc (List.mem_singleton.mp h1)

/-! ## A1 `calls_ports_sl` -/

/-- **The ports of a machine with calls and NO slot** (A1). Copy of `calls_ports` (MachineDepthChild:41-56): `hsl`
becomes `hsl0`, the clock/reset conjuncts one disjunction (case S: both inputs; case C: neither). -/
theorem calls_ports_sl {declName : Name} {d : MachineData} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName d.shape ids cache m dsn regs lets)
    (len : ids.length = d.shape.binders.length)
    (hsl0 : d.shape.layout.slots = [])
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain) (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length) :
    (m.inputs.map (·.name)).Nodup ∧
    (("clk" ∈ m.inputs.map (·.name) ∧ "rst" ∈ m.inputs.map (·.name)) ∨
      ("clk" ∉ m.inputs.map (·.name) ∧ "rst" ∉ m.inputs.map (·.name))) ∧
    (∀ x ∈ m.outputs.map (·.name), x ∉ m.inputs.map (·.name)) ∧
    argPorts m = machPorts declName ids cache (d.bsIn.take kD) ∧
    (∀ x ∈ ((machPorts declName ids cache d.shape.binders).map (·.name)).drop
        (((machPorts declName ids cache d.shape.binders).map (·.name)).length -
          d.shape.layout.lets - d.shape.layout.slots.length), x ∉ m.inputs.map (·.name)) := by
  obtain ⟨hnd, halloc, -, -, -, -, -, houts, -, -, -, -, -, -, -, -, hcl, -⟩ := wired
  have hlenB : d.shape.binders.length ≤ ids.length := by omega
  have hsplit := d.binders_split
  -- the ports of the binders: the declaration's first
  obtain ⟨restP, hPapp⟩ := machPorts_append (declName := declName) (ids := ids) (cache := cache)
    (d.bsIn.take kD) (d.bsIn.drop kD ++ d.slotBs ++ d.letBs) (by
      rw [len, hsplit]; simp only [List.length_append, List.length_take, List.length_drop]; omega)
  have hPeq : machPorts declName ids cache d.shape.binders =
      machPorts declName ids cache (d.bsIn.take kD) ++ restP := by
    rw [← hPapp, hsplit]
    conv => lhs; rw [← List.take_append_drop kD d.bsIn]
    simp only [List.append_assoc]
  have hDlen : (machPorts declName ids cache (d.bsIn.take kD)).length = machNIn d.shape := by
    rw [machPorts_length _ (by rw [len, hsplit]; simp; omega), hNIn]
  generalize hP : machPorts declName ids cache d.shape.binders = P at hnd halloc hcl hPeq ⊢
  obtain ⟨outWs, extra, hsub, hsup, hex, hin⟩ := hcl
  -- CHANGED: no slot, so the slot clock/reset block is empty; `extra` is `[]` or `[clk, rst]`
  have hif : ∀ (a b : List Port), (if d.shape.layout.slots.isEmpty then a else b) = a := by
    intro a b; rw [hsl0]; rfl
  rw [hif, List.append_nil] at hin
  generalize hK : (P.map (·.name)).length - d.shape.layout.lets - d.shape.layout.slots.length = K
    at hin ⊢
  -- the names
  have hnClk : ∀ p ∈ P, p.name ≠ "clk" := fun p hp h =>
    Tools.ShippingMachineCleanup.not_allocated_clk (h ▸ halloc _ (List.mem_map_of_mem hp))
  have hnRst : ∀ p ∈ P, p.name ≠ "rst" := fun p hp h =>
    Tools.ShippingRegisterSoundness.not_allocated_rst (h ▸ halloc _ (List.mem_map_of_mem hp))
  have hOW : ∀ w ∈ outWs, w ∈ P.map (·.name) := by
    intro w hw
    obtain ⟨k, _, hk⟩ := hsub w hw
    exact List.mem_of_getElem? hk
  have clkOut : "clk" ∉ outWs := fun h => by
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (hOW _ h); exact hnClk p hp hpn
  have rstOut : "rst" ∉ outWs := fun h => by
    obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (hOW _ h); exact hnRst p hp hpn
  have hTmem : ∀ p ∈ P.take K, p ∈ P := fun p hp => List.mem_of_mem_take hp
  have hTnd : ((P.take K).map (·.name)).Nodup := by
    rw [List.map_take]; exact hnd.sublist (List.take_sublist _ _)
  -- CHANGED: `extra`'s names are the clock and the reset, distinct
  have hEx : ∀ q ∈ extra, q.name = "clk" ∨ q.name = "rst" := by
    rcases hex with rfl | ⟨rfl, -⟩
    · intro q hq; exact absurd hq List.not_mem_nil
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact Or.inl rfl
      · rw [List.mem_singleton.mp hq']; exact Or.inr rfl
  have hEnd : (extra.map (·.name)).Nodup := by
    rcases hex with rfl | ⟨rfl, -⟩
    · exact List.nodup_nil
    · simp
  have hinN : m.inputs.map (·.name) = ((P.take K).map (·.name) ++ extra.map (·.name)).filter
      fun x => !outWs.contains x := by
    rw [hin, ← List.map_append, List.filter_map]
    rfl
  have hLnd : ((P.take K).map (·.name) ++ extra.map (·.name)).Nodup := by
    refine List.nodup_append.mpr ⟨hTnd, hEnd, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hb
    rcases hEx q hq with h | h
    · exact hnClk p (hTmem p hp) (hqn.symm.trans h)
    · exact hnRst p (hTmem p hp) (hqn.symm.trans h)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hinN]; exact hLnd.filter _
  · -- CHANGED: the case, from `extra`
    rcases hex with rfl | ⟨rfl, -⟩
    · right
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [hinN, List.mem_filter, List.map_nil, List.append_nil] at h
        obtain ⟨p, hp, hpn⟩ := List.mem_map.mp h.1
        exact hnClk p (hTmem p hp) hpn
      · rw [hinN, List.mem_filter, List.map_nil, List.append_nil] at h
        obtain ⟨p, hp, hpn⟩ := List.mem_map.mp h.1
        exact hnRst p (hTmem p hp) hpn
    · left
      refine ⟨?_, ?_⟩
      · rw [hinN, List.mem_filter]; exact ⟨by simp, by simpa [List.contains_eq_mem] using clkOut⟩
      · rw [hinN, List.mem_filter]; exact ⟨by simp, by simpa [List.contains_eq_mem] using rstOut⟩
  · intro x hx hxi
    rw [houts] at hx
    simp only [List.map_map, List.mem_map, Function.comp] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    have hok := houtOk o ho
    obtain ⟨hna, hnr, _⟩ := Tools.ShippingMachineClose.outNameOk_facts hok
    have hnc : o.name ≠ "clk" := by
      simp only [outNameOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
      exact hok.2
    rw [hinN, List.mem_filter] at hxi
    rcases List.mem_append.mp hxi.1 with h | h
    · obtain ⟨p, hp, hpn⟩ := List.mem_map.mp h
      exact hna (hpn ▸ halloc _ (List.mem_map_of_mem (hTmem p hp)))
    · obtain ⟨q, hq, hqn⟩ := List.mem_map.mp h
      rcases hEx q hq with h' | h'
      · exact hnc (hqn.symm.trans h')
      · exact hnr (hqn.symm.trans h')
  · -- the argument ports: the declaration's
    have hA : argPorts m = (P.take K).filter fun p => !outWs.contains p.name := by
      unfold argPorts
      rw [hin, List.filter_append, List.filter_append]
      have e1 : ((extra.filter fun p => !outWs.contains p.name).filter
          fun p => p.name != "clk" && p.name != "rst") = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        have := (List.mem_filter.mp hx).1
        rcases hEx x this with h | h <;> simp [h]
      rw [e1, List.append_nil]
      apply List.filter_eq_self.mpr
      intro p hp
      have hp' := hTmem p (List.mem_filter.mp hp).1
      simp [hnClk p hp', hnRst p hp']
    -- the lengths
    have hNL : (P.map (·.name)).length = (d.shape.binders.filter fun b => b.2 != .domain).length := by
      rw [List.length_map, ← hP, machPorts_length _ hlenB]
    have hSLf : ((d.slotBs ++ d.letBs).filter fun b => b.2 != .domain).length =
        d.slotBs.length + d.letBs.length := by
      rw [List.filter_eq_self.mpr (fun b hb => bne_iff_ne.mpr (hSL b hb)), List.length_append]
    have hKv : K = ((d.bsIn.filter fun b => b.2 != .domain)).length := by
      rw [← hK, hNL, hsplit, List.append_assoc, List.filter_append, List.length_append, hSLf,
        hSlen, hLlen]
      omega
    have hBsplit : (d.bsIn.filter fun b => b.2 != .domain).length =
        ((d.bsIn.take kD).filter fun b => b.2 != .domain).length +
          ((d.bsIn.drop kD).filter fun b => b.2 != .domain).length := by
      conv => lhs; rw [← List.take_append_drop kD d.bsIn]
      rw [List.filter_append, List.length_append]
    have hDrop : ((d.bsIn.drop kD).filter fun b => b.2 != .domain).length ≤ d.shape.insts.length := by
      rw [← hIlen]; exact List.length_filter_le _ _
    generalize hNv : machNIn d.shape = N at hsub hsup hDlen
    have hNK : N ≤ K := by rw [hKv, hBsplit, ← hNIn, hNv]; omega
    have hKN : K ≤ N + d.shape.insts.length := by rw [hKv, hBsplit, ← hNIn, hNv]; omega
    have hKlen : K ≤ P.length := by
      have := hK; rw [List.length_map] at this; omega
    have htk : (P.take K).length = K := by simp; omega
    have hfeq : (P.take K).filter (fun p => !outWs.contains p.name) = (P.take K).take N := by
      apply filter_eq_take _ _ N (by rw [htk]; exact hNK)
      · intro i hi hiN
        simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
        intro hmem
        obtain ⟨k, _, hk⟩ := hsub _ hmem
        have hi' : i < P.length := by rw [htk] at hi; omega
        have hkl : N + k < (P.map (·.name)).length := (List.getElem?_eq_some_iff.mp hk).1
        have hik : (P.map (·.name))[N + k]? = (P.map (·.name))[i]? := by
          rw [hk, List.getElem?_map, List.getElem?_eq_getElem hi', List.getElem_take]
          rfl
        have := (List.getElem?_inj hkl hnd).mp hik
        omega
      · intro i hi hiN
        simp only [Bool.not_eq_false', List.contains_eq_mem, decide_eq_true_eq]
        have hik : i - N < d.shape.insts.length := by rw [htk] at hi; omega
        obtain ⟨w, hw, hwo⟩ := hsup (i - N) hik
        rw [show N + (i - N) = i by omega, List.getElem?_map] at hw
        have hi' : i < P.length := by rw [htk] at hi; omega
        rw [List.getElem?_eq_getElem hi', Option.map_some, Option.some.injEq] at hw
        rw [List.getElem_take, hw]; exact hwo
    rw [hA, hfeq, List.take_take, show min N K = N by omega, hPeq,
      List.take_append_of_le_length (Nat.le_of_eq hDlen.symm),
      List.take_of_length_le (Nat.le_of_eq hDlen)]
  · -- a slot or `let` port is not an input
    intro x hx hxi
    rw [hinN, List.mem_filter] at hxi
    have hxP : x ∈ P.map (·.name) := List.mem_of_mem_drop hx
    rcases List.mem_append.mp hxi.1 with h | h
    · rw [List.map_take] at h
      have hsplit : (P.map (·.name)).take K ++ (P.map (·.name)).drop K = P.map (·.name) :=
        List.take_append_drop _ _
      have := hnd
      rw [← hsplit] at this
      exact (List.nodup_append.mp this).2.2 x h x hx rfl
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hxP
      obtain ⟨q, hq, hqn⟩ := List.mem_map.mp h
      rcases hEx q hq with h' | h'
      · exact hnClk p hp (hqn.symm.trans h')
      · exact hnRst p hp (hqn.symm.trans h')

/-! ## A2 `NoTouchZ`, `runModuleTG_seed_offZ` -/

/-- No statement reads or writes a name of `Z`: assignments (target and `refsOf`) and instances (their `.ref`
connections) only. -/
def NoTouchZ (Z : List String) (body : List Stmt) : Prop :=
  ∀ st ∈ body,
    (∃ l r, st = Stmt.assign l r ∧ l ∉ Z ∧ ∀ z ∈ Z, z ∉ Sparkle.IR.Reorder.refsOf r) ∨
    (∃ mn iname conns, st = Stmt.inst mn iname conns ∧ ∀ c ∈ conns, ∀ w, c.2 = .ref w → w ∉ Z)

theorem noTouchZ_tail {Z : List String} {st : Stmt} {rest : List Stmt} (h : NoTouchZ Z (st :: rest)) :
    NoTouchZ Z rest :=
  fun s hs => h s (List.mem_cons_of_mem _ hs)

/-- `bindOuts` keeps agreement off `Z` (it writes the same value at the same wire on both sides). -/
theorem bindOuts_agreeZ {Z : List String} (conns : List (String × Expr)) (cres : Env) :
    ∀ (outs : List Port) (e₁ e₂ : Env), (∀ y, y ∉ Z → e₂ y = e₁ y) →
      ∀ y, y ∉ Z → Tools.ShippingHierarchySoundness.bindOuts outs conns cres e₂ y =
        Tools.ShippingHierarchySoundness.bindOuts outs conns cres e₁ y
  | [], _, _, h, y, hy => h y hy
  | p :: outs, e₁, e₂, h, y, hy => by
    show Tools.ShippingHierarchySoundness.bindOuts outs conns cres
      (match conns.lookup p.name with
       | some (.ref w) => fun n => if n = w then cres p.name else e₂ n
       | _ => e₂) y =
      Tools.ShippingHierarchySoundness.bindOuts outs conns cres
      (match conns.lookup p.name with
       | some (.ref w) => fun n => if n = w then cres p.name else e₁ n
       | _ => e₁) y
    apply bindOuts_agreeZ conns cres outs _ _ ?_ y hy
    intro m hm
    cases hl : conns.lookup p.name with
    | none => exact h m hm
    | some e =>
      cases e with
      | ref w =>
        show (if m = w then cres p.name else e₂ m) = (if m = w then cres p.name else e₁ m)
        by_cases he : m = w
        · subst he; simp only [if_true]
        · simp only [he, if_false]; exact h m hm
      | _ => exact h m hm

/-- One cycle's elaboration of a `NoTouchZ` body: from environments agreeing off `Z`, the same child states and
environments agreeing off `Z`. -/
theorem evalAssignsKG_offZ {σ : Type} (KS : KStep σ) (hloc : KSLocal KS) (we : WEnv)
    (children : String → Option (Module × WEnv)) (kids : String → σ) (mems : MEnv) {Z : List String} :
    ∀ (body : List Stmt), NoTouchZ Z body →
      ∀ (env₁ env₂ : Env) (acc : String → σ) (e₁ : Env) (k₁ : String → σ),
        (∀ y, y ∉ Z → env₂ y = env₁ y) →
        evalAssignsKG KS we children kids mems body env₁ acc = some (e₁, k₁) →
        ∃ e₂, evalAssignsKG KS we children kids mems body env₂ acc = some (e₂, k₁) ∧
          ∀ y, y ∉ Z → e₂ y = e₁ y
  | [], _, env₁, env₂, acc, e₁, k₁, hag, h => by
    simp only [evalAssignsKG, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨env₂, rfl, hag⟩
  | .assign l r :: rest, hZ, env₁, env₂, acc, e₁, k₁, hag, h => by
    have hlr : l ∉ Z ∧ ∀ z ∈ Z, z ∉ Sparkle.IR.Reorder.refsOf r := by
      rcases hZ _ List.mem_cons_self with ⟨l', r', heq, hl', hr'⟩ | ⟨mn, iname, conns, heq, -⟩
      · cases heq; exact ⟨hl', hr'⟩
      · cases heq
    have hev : evalExpr we env₂ r = evalExpr we env₁ r := by
      apply Sparkle.IR.Reorder.evalExpr_congr
      intro n hn
      exact hag n (fun hnZ => hlr.2 n hnZ hn)
    simp only [evalAssignsKG, Option.bind_eq_bind] at h ⊢
    obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
    rw [hev, hv, Option.bind_some]
    refine evalAssignsKG_offZ KS hloc we children kids mems rest (noTouchZ_tail hZ)
      (fun n => if n = l then v else env₁ n) (fun n => if n = l then v else env₂ n) acc e₁ k₁ ?_ h
    intro y hy
    by_cases hyl : y = l
    · subst hyl; simp only [if_true]
    · simp only [hyl, if_false]; exact hag y hy
  | .inst mn iname conns :: rest, hZ, env₁, env₂, acc, e₁, k₁, hag, h => by
    have hc : ∀ c ∈ conns, ∀ w, c.2 = .ref w → w ∉ Z := by
      rcases hZ _ List.mem_cons_self with ⟨l', r', heq, -⟩ | ⟨mn', iname', conns', heq, hc'⟩
      · cases heq
      · cases heq; exact hc'
    simp only [evalAssignsKG, Option.bind_eq_bind] at h ⊢
    obtain ⟨cp, hcp, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨child, cwe⟩ := cp
    try dsimp only at h
    obtain ⟨kr, hk, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cres, ks'⟩ := kr
    try dsimp only at h
    have hks : KS child cwe (inConns child.outputs conns) env₂ (kids iname) = some (cres, ks') := by
      rw [← hk]
      apply hloc
      intro c hcm w hw
      exact hag w (hc c (List.mem_filter.mp hcm).1 w hw)
    rw [hcp, Option.bind_some]
    try dsimp only
    rw [hks, Option.bind_some]
    try dsimp only
    exact evalAssignsKG_offZ KS hloc we children kids mems rest (noTouchZ_tail hZ) _ _ _ e₁ k₁
      (bindOuts_agreeZ conns cres child.outputs env₁ env₂ hag) h
  | .register .. :: _, hZ, _, _, _, _, _, _, _ => by
    rcases hZ _ List.mem_cons_self with ⟨l', r', heq, -⟩ | ⟨mn', iname', conns', heq, -⟩ <;> cases heq
  | .memory .. :: _, hZ, _, _, _, _, _, _, _ => by
    rcases hZ _ List.mem_cons_self with ⟨l', r', heq, -⟩ | ⟨mn', iname', conns', heq, -⟩ <;> cases heq

/-- A `NoTouchZ` body has no register update. -/
theorem regNexts_noTouch {Z : List String} (we : WEnv) (mems : MEnv) :
    ∀ (body : List Stmt), NoTouchZ Z body → ∀ env, regNexts we mems body env = some []
  | [], _, _ => rfl
  | .assign _ _ :: rest, hZ, env => by
    simp only [regNexts]; exact regNexts_noTouch we mems rest (noTouchZ_tail hZ) env
  | .inst _ _ _ :: rest, hZ, env => by
    simp only [regNexts]; exact regNexts_noTouch we mems rest (noTouchZ_tail hZ) env
  | .register .. :: _, hZ, _ => by
    rcases hZ _ List.mem_cons_self with ⟨l', r', heq, -⟩ | ⟨mn', iname', conns', heq, -⟩ <;> cases heq
  | .memory .. :: _, hZ, _ => by
    rcases hZ _ List.mem_cons_self with ⟨l', r', heq, -⟩ | ⟨mn', iname', conns', heq, -⟩ <;> cases heq

/-- A `NoTouchZ` body writes no memory. -/
theorem memNexts_noTouch {Z : List String} (we : WEnv) :
    ∀ (body : List Stmt), NoTouchZ Z body → ∀ mems env, memNexts we body mems env = some mems
  | [], _, _, _ => rfl
  | .assign _ _ :: rest, hZ, mems, env => by
    simp only [memNexts]; exact memNexts_noTouch we rest (noTouchZ_tail hZ) mems env
  | .inst _ _ _ :: rest, hZ, mems, env => by
    simp only [memNexts]; exact memNexts_noTouch we rest (noTouchZ_tail hZ) mems env
  | .register .. :: _, hZ, _, _ => by
    rcases hZ _ List.mem_cons_self with ⟨l', r', heq, -⟩ | ⟨mn', iname', conns', heq, -⟩ <;> cases heq
  | .memory .. :: _, hZ, _, _ => by
    rcases hZ _ List.mem_cons_self with ⟨l', r', heq, -⟩ | ⟨mn', iname', conns', heq, -⟩ <;> cases heq

/-- **The intermediate lemma** (freeze §3 A2, reviewer): one cycle of a `NoTouchZ` body from environments agreeing
off `Z` gives the SAME next state (registers, memories and kids) and environments agreeing off `Z`. -/
theorem stepModuleTG_offZ {σ : Type} (KS : KStep σ) (hloc : KSLocal KS) (we : WEnv)
    (children : String → Option (Module × WEnv)) {body : List Stmt} {Z : List String}
    (hZ : NoTouchZ Z body) {env₁ env₂ : Env} (hag : ∀ y, y ∉ Z → env₂ y = env₁ y) (s : KState σ)
    {r : Env × KState σ} (h : stepModuleTG KS we children body env₁ s = some r) :
    ∃ e₂, stepModuleTG KS we children body env₂ s = some (e₂, r.2) ∧ ∀ y, y ∉ Z → e₂ y = r.1 y := by
  unfold stepModuleTG at h ⊢
  simp only [Option.bind_eq_bind] at h ⊢
  obtain ⟨ek, hE, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨e₁, k₁⟩ := ek
  obtain ⟨e₂, hE₂, hag₂⟩ :=
    evalAssignsKG_offZ KS hloc we children s.kids s.mems body hZ env₁ env₂ s.kids e₁ k₁ hag hE
  simp only [regNexts_noTouch we s.mems body hZ, memNexts_noTouch we body hZ, Option.bind_some,
    Option.some.injEq] at h
  subst h
  refine ⟨e₂, ?_, hag₂⟩
  simp only [hE₂, regNexts_noTouch we s.mems body hZ, memNexts_noTouch we body hZ, Option.bind_some]

/-- **A2: seed locality of a `NoTouchZ` body at TG level.** Two seeds agreeing off `Z` give runs of the same length
whose environments agree off `Z` (and, by `stepModuleTG_offZ`, through the SAME states). -/
theorem runModuleTG_seed_offZ {σ : Type} (KS : KStep σ) (hloc : KSLocal KS) (we : WEnv)
    (children : String → Option (Module × WEnv)) {body : List Stmt} {Z : List String}
    (hZ : NoTouchZ Z body) {seed₁ seed₂ : Nat → (String → Nat) → Env}
    (hagree : ∀ t st y, y ∉ Z → seed₁ t st y = seed₂ t st y) :
    ∀ (T : Nat) (s : KState σ) (envs₁ : List Env),
      runModuleTG KS we children body seed₁ T s = some envs₁ →
      ∃ envs₂, runModuleTG KS we children body seed₂ T s = some envs₂ ∧ envs₂.length = envs₁.length ∧
        ∀ j (h₁ : j < envs₁.length) (h₂ : j < envs₂.length) (y : String), y ∉ Z →
          (envs₂[j]'h₂) y = (envs₁[j]'h₁) y
  | 0, s, envs₁, h => by
    simp only [runModuleTG, Option.some.injEq] at h
    subst h
    exact ⟨[], rfl, rfl, fun j h₁ => absurd h₁ (Nat.not_lt_zero j)⟩
  | k + 1, s, envs₁, h => by
    simp only [runModuleTG, Option.bind_eq_bind] at h ⊢
    obtain ⟨r, hS, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e₁, s₁⟩ := r
    try dsimp only at h
    obtain ⟨rest, hR, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨e₂, hS₂, hag₂⟩ := stepModuleTG_offZ KS hloc we children hZ (env₁ := seed₁ k s.st)
      (env₂ := seed₂ k s.st) (fun y hy => (hagree k s.st y hy).symm) s hS
    obtain ⟨rest₂, hR₂, hlen, hpt⟩ := runModuleTG_seed_offZ KS hloc we children hZ hagree k s₁ rest hR
    refine ⟨e₂ :: rest₂, ?_, by simp [hlen], ?_⟩
    · simp only [hS₂, hR₂, Option.bind_some]
    · intro j h₁ h₂ y hy
      cases j with
      | zero => exact hag₂ y hy
      | succ j => exact hpt j (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂) y hy

/-! ## A3 `slSeedZ`, `childRunN_of_composedNW_runSl` -/

/-- The seed with the reset and the clock zeroed in the state part. -/
def slSeedZ (m : Module) (ins : Nat → String → Nat) : Nat → (String → Nat) → Env :=
  fun t st => seedIn m ins t (fun x => if x = "rst" ∨ x = "clk" then 0 else st x)

theorem slSeedZ_agree (m : Module) (ins : Nat → String → Nat) :
    ∀ t st y, y ∉ ["rst", "clk"] → slSeedZ m ins t st y = seedIn m ins t st y := by
  intro t st y hy
  have h1 : y ≠ "rst" := fun h => hy (by subst h; simp)
  have h2 : y ≠ "clk" := fun h => hy (by subst h; simp)
  simp [slSeedZ, seedIn, h1, h2]

open Tools.ShippingMachineChild (boolsOf bitsOf sourceInputs_of_vals) in
set_option maxHeartbeats 4000000 in
/-- **A3: a slotless parent's child run.** C6 (Gen2C6:29-55) with `hsl` → `hsl0`, the internal premise `hZ`
(B1 supplies it from the run), conclusion `ChildRunN`. The case is decided from the module's actual inputs
(`calls_ports_sl`): (S) clock and reset inputs → `SeqChildRunN` by C6's proof (verbatim); (C) neither →
`CombChildRunN`, the run at `slSeedZ` transferred to `seedIn` by A2. -/
theorem childRunN_of_composedNW_runSl (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl0 : d.shape.layout.slots = [])
    (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length) (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (hextB : ∀ i bools bits j, j < kD → extB i bools bits j = bools j)
    (hext : ∀ i bools bits j n', j < kD → ext i bools bits j n' = bits j n')
    (i : ι) {mc raw : Module} {D dsn : Design}
    (hcomp : ComposedNW n c d kD raw D dom src ext extB)
    (hpost : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hEA : ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules))
    (hNI : NoInstOf raw.name raw.body)
    (hZ : "rst" ∉ raw.inputs.map (·.name) → NoTouchZ ["rst", "clk"] raw.body) :
    Tools.ShippingGen2.ChildRunN (childMap dsn.modules) dsn (n + 1) mc (d.bsIn.take kD)
      d.shape.layout.outs (fun vals => src i (boolsOf (d.bsIn.take kD) vals) (bitsOf (d.bsIn.take kD) vals)) := by
  obtain ⟨ids, nd, len, cache, regs, _, _, lets, _, wired, H⟩ := hcomp
  obtain ⟨hnd_in, hcase, hdisj, hargs, hslotNI⟩ :=
    calls_ports_sl wired len hsl0 houtOk kD hkD hIlen hSL hSlen hLlen hNIn
  obtain ⟨-, halloc, regsIn, -, calls1, -, -, houts, -, -, -, -, gCalls, -, -, hcleanG, -, hW1, -⟩ := wired
  obtain ⟨hb, hw, hi, ho⟩ := hcleanG houtTy
  -- the core module has an instance, so the full entry kept it (C6 verbatim)
  have hInst : Tools.ShippingMachineShipsHier.hasInst (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) := by
    by_cases hfe : d.shape.instFields = []
    · obtain ⟨args, mc', st, _, hst, _, hcall⟩ := calls1 hfe 0 hI0
      obtain ⟨_, _, _, iname, _, _, _, _, _, _, _, _, _, heq⟩ := hcall
      subst heq
      exact ⟨_, _, _, by rw [hb]; exact hst⟩
    · obtain ⟨st, hst, args, outs, mc', hcall, _⟩ := gCalls hfe 0 hI0
      obtain ⟨_, _, iname, _, _, _, _, _, _, _, _, _, _, _, heq⟩ := hcall
      subst heq
      exact ⟨_, _, _, by rw [hb]; exact hst⟩
  have hmc : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · rw [h, mergeChecked_of_hasInst hInst]
  subst hmc
  have hargsMc : argPorts (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) = argPorts raw := by
    unfold argPorts; rw [hi]
  have hlenIn : (d.bsIn.take kD).length ≤ ids.length := by
    rw [len, d.binders_split]; simp; omega
  rcases hcase with ⟨hclk, hrst⟩ | ⟨hclk, hrst⟩
  · -- case (S): clock and reset are inputs: C6:83-137 verbatim
    refine Or.inl ⟨by rw [ho, houts], by rw [hi]; exact hnd_in, by rw [hi]; exact hclk,
      by rw [hi]; exact hrst, by rw [hi, ho]; exact hdisj, ?_, ?_⟩
    · rw [hargsMc, hargs, machPorts_length _ hlenIn]
    intro T ins s vals hrange hports hrstZ hclkZ hreset
    have hseed : seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) ins = seedIn raw ins := by
      unfold seedIn; rw [hi]
    unfold ResetN at hreset
    obtain ⟨hregR, _, _, hkidR⟩ := hreset
    obtain ⟨envs, hrun, hlen, hobs⟩ := H i (boolsOf (d.bsIn.take kD) vals)
      (bitsOf (d.bsIn.take kD) vals) T (seedIn raw ins) s.st s.mems s.kids
      (fun t st ht => by
        have hS := sourceInputs_of_vals nd hlenIn hargs (seedIn raw ins t st) (vals (T - 1 - t))
          (by
            rw [← hports t ht, hargsMc]
            apply List.map_congr_left
            intro p hp
            have hpi : p ∈ raw.inputs := (List.mem_filter.mp hp).1
            simp [seedIn, List.contains_eq_mem, List.mem_map_of_mem hpi])
          (hrange _ (by omega))
        refine Tools.ShippingMachineEntry.sourceInputs_congr nd ?_ ?_ hS
        · intro j hj
          have hjk : j < kD := by simp at hj; omega
          rw [hextB _ _ _ j hjk]; rfl
        · intro j hj n'
          have hjk : j < kD := by simp at hj; omega
          rw [hext _ _ _ j n' hjk]; rfl)
      (fun t st r hr => by
        have hnot := hslotNI r (regsIn r hr)
        simp [seedIn, List.contains_eq_mem, hnot])
      (fun t st => by simp [seedIn, List.contains_eq_mem, hrst, hrstZ])
      (fun t st => by simp [seedIn, List.contains_eq_mem, hclk, hclkZ])
      (fun k r f hr hf => by
        obtain ⟨rk, inp, hmem⟩ := hW1 k r f hr hf
        have := hregR r "clk" ("rst", rk) inp (Int.ofNat f.init) (by rw [hb]; exact hmem)
        simpa [stOf] using this)
      (fun iname mc' ⟨conns, hm⟩ hf => by
        have hc1 : childMap D.modules mc'.name = some (mc', Sparkle.IR.RegDedup.declWidth mc') :=
          childMap_some.mpr ⟨mc', hf, rfl⟩
        have hc2 := hEA.1 _ _ (hNI _ _ _ hm) hc1
        obtain ⟨x, hx, hxe⟩ := childMap_some.mp hc2
        have : x = mc' := by injection hxe with h; exact h.symm
        subst this
        exact resetN_away hEA n x (s.kids iname) (hEA.2 _ _ hc1)
          (hkidR x.name iname conns x (by rw [hb]; exact hm) hx))
    have hrun' := runModuleTG_mono_away (KSn_mono_away hEA n) hEA _ raw.body hNI _ T _ envs hrun
    refine ⟨envs, ?_, hlen, hobs⟩
    show runModuleTG (KSn (childMap dsn.modules) n)
      (Sparkle.IR.RegDedup.declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (childMap dsn.modules)
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body
      (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) ins) T s = some envs
    rw [hseed, hb]
    have hwe : Sparkle.IR.RegDedup.declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) =
        Tools.ShippingEntrySoundness.weOf raw := hw
    rw [hwe]
    exact hrun'
  · -- case (C): neither clock nor reset is an input
    refine Or.inr ⟨by rw [ho, houts], by rw [hi]; exact hnd_in, by rw [hi]; exact hclk,
      by rw [hi]; exact hrst, by rw [hi, ho]; exact hdisj, ?_, ?_⟩
    · rw [hargsMc, hargs, machPorts_length _ hlenIn]
    intro T ins s vals hrange hports hreset
    have hseed : seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) ins = seedIn raw ins := by
      unfold seedIn; rw [hi]
    unfold ResetN at hreset
    obtain ⟨hregR, _, _, hkidR⟩ := hreset
    -- the registers are on allocated (slot/let) ports: neither the reset nor the clock
    have hregZ : ∀ r ∈ regs, r ≠ "rst" ∧ r ≠ "clk" := by
      intro r hr
      have hal := halloc r (List.mem_of_mem_drop (regsIn r hr))
      exact ⟨fun h => Tools.ShippingRegisterSoundness.not_allocated_rst (h ▸ hal),
        fun h => Tools.ShippingMachineCleanup.not_allocated_clk (h ▸ hal)⟩
    -- `H` at the zeroed seed (its reset/clock premises hold there for every state)
    obtain ⟨envs, hrun, hlen, hobs⟩ := H i (boolsOf (d.bsIn.take kD) vals)
      (bitsOf (d.bsIn.take kD) vals) T (slSeedZ raw ins) s.st s.mems s.kids
      (fun t st ht => by
        have hS := sourceInputs_of_vals nd hlenIn hargs
          (seedIn raw ins t (fun x => if x = "rst" ∨ x = "clk" then 0 else st x)) (vals (T - 1 - t))
          (by
            rw [← hports t ht, hargsMc]
            apply List.map_congr_left
            intro p hp
            have hpi : p ∈ raw.inputs := (List.mem_filter.mp hp).1
            simp [seedIn, List.contains_eq_mem, List.mem_map_of_mem hpi])
          (hrange _ (by omega))
        refine Tools.ShippingMachineEntry.sourceInputs_congr nd ?_ ?_ hS
        · intro j hj
          have hjk : j < kD := by simp at hj; omega
          rw [hextB _ _ _ j hjk]; rfl
        · intro j hj n'
          have hjk : j < kD := by simp at hj; omega
          rw [hext _ _ _ j n' hjk]; rfl)
      (fun t st r hr => by
        have hnot := hslotNI r (regsIn r hr)
        obtain ⟨h1, h2⟩ := hregZ r hr
        simp [slSeedZ, seedIn, List.contains_eq_mem, hnot, h1, h2])
      (fun t st => by simp [slSeedZ, seedIn, List.contains_eq_mem, hrst])
      (fun t st => by simp [slSeedZ, seedIn, List.contains_eq_mem, hclk])
      (fun k r f hr hf => by
        obtain ⟨rk, inp, hmem⟩ := hW1 k r f hr hf
        have := hregR r "clk" ("rst", rk) inp (Int.ofNat f.init) (by rw [hb]; exact hmem)
        simpa [stOf] using this)
      (fun iname mc' ⟨conns, hm⟩ hf => by
        have hc1 : childMap D.modules mc'.name = some (mc', Sparkle.IR.RegDedup.declWidth mc') :=
          childMap_some.mpr ⟨mc', hf, rfl⟩
        have hc2 := hEA.1 _ _ (hNI _ _ _ hm) hc1
        obtain ⟨x, hx, hxe⟩ := childMap_some.mp hc2
        have : x = mc' := by injection hxe with h; exact h.symm
        subst this
        exact resetN_away hEA n x (s.kids iname) (hEA.2 _ _ hc1)
          (hkidR x.name iname conns x (by rw [hb]; exact hm) hx))
    have hrun' := runModuleTG_mono_away (KSn_mono_away hEA n) hEA _ raw.body hNI _ T _ envs hrun
    -- A2 at `Z := ["rst", "clk"]`: from the zeroed seed to `seedIn`
    obtain ⟨envs₂, hrun₂, hlen₂, hpt⟩ :=
      runModuleTG_seed_offZ (KSn (childMap dsn.modules) n) (KSn_local (childMap dsn.modules) n) _
        (childMap dsn.modules) (hZ hrst) (slSeedZ_agree raw ins) T _ envs hrun'
    refine ⟨envs₂, ?_, by rw [hlen₂, hlen], ?_⟩
    · show runModuleTG (KSn (childMap dsn.modules) n)
        (Sparkle.IR.RegDedup.declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (childMap dsn.modules)
        (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body
        (seedIn (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) ins) T s = some envs₂
      rw [hseed, hb]
      have hwe : Sparkle.IR.RegDedup.declWidth (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) =
          Tools.ShippingEntrySoundness.weOf raw := hw
      rw [hwe]
      exact hrun₂
    · intro j hj k o f hk hf
      have hoZ : o.name ∉ ["rst", "clk"] := outName_notZ (houtOk o (List.mem_of_getElem? hk))
      rw [hpt j (by omega) hj o.name hoZ]
      exact hobs j (by omega) k o f hk hf

end Tools.ShippingGen2SlotlessParent
