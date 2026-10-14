import Tools.ShippingGateNamesWalk
import Tools.ShippingGateDesignRun
import Tools.ShippingGateCombSide
import Tools.ShippingMachineDepthHR
import Tools.ShippingGateChildComb
import Tools.ShippingFirstGateKidText

variable {tenv : Lean.Environment}

/-! # Gate-route parents: five `combSideB` conjuncts from the naming walk (worker N, round 13)

WRITTEN, NOT BUILT.

From `NOk` at the end of the walk (`Tools.ShippingGateNamesWalk`), the
returned core module `M = finalize (out := wire :: body)` satisfies
(`names_final_of`, `NFin`):

* `(instNames M.body).Nodup`;
* for any design `ms` resolving every `G` module to itself:
  `linkedWF (childMap ms) M.body` (`linkedWF_of`: the builder order, every
  written wire mentioned by no earlier statement, `out` mentioned by none),
  `noSelfRead (childMap ms) M.body` (an instance's input connections carry
  wires other than its output wire), `outsExtracted (childMap ms) M` (an
  instance output wire is a declared wire, connected, written by no
  assignment — two writers of one wire contradict the order — and not an
  input), and, when every `G` module is a gate child (`ChildComb`),
  `kidsComb ms M.body` (the connections are keyed by the callee's inputs).

`gate_cone_runNames` (a copy of `gate_cone_runGED`'s run reading, the old
theorems kept) gives `FinalOk ∧ NFin` of the core module from the run, for a
design predicate whose `DesW` AND `NamW` hold of the body. `gate_combFacts`:
for a parent whose instance leaves are calls of one first-gate child `c`
(`ChildGN c mF`), from the run, `GateDefines` (NOT ALLOWED), `ChildBnd`, the
child facts (incl. the child's own `kidCheck`, `first_child_kidK` for a
first-gate child) and the per-body walks, the SHIPPED full-entry module `b`
satisfies the five conjuncts of `combSideB design.modules b` other than
`hierTyped`, and the children's-check conjunct of `designSideB` (every
instance's child is the cache's `c` entry); `designSideB3` is what is left of
`designSideB` (`designSideB_of3`). -/
namespace Tools.ShippingGateParentRun

set_option linter.unusedSectionVars false

/-! ## Lists of statements -/

section lists
open Sparkle.IR.AST
open Tools.ShippingHierOpen (linkedWF linkedWrites bodyInstOuts stmtInstOuts instOutWires)
open Tools.ShippingHierState (instNames inConns)

/-- Every statement an assignment or an instance. -/
def KindN (S : Stmt) : Prop :=
  (∃ l r, S = Stmt.assign l r) ∨ (∃ mn i cs, S = Stmt.inst mn i cs)

/-- What the checks ask of every instance statement of a body. -/
def InstFactsN (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
    (L : List Stmt) : Prop :=
  ∀ mn i cs, Stmt.inst mn i cs ∈ L →
    ∃ child cwe w, C mn = some (child, cwe) ∧ instOutWires child.outputs cs = [w] ∧
      WritesN (.inst mn i cs) w ∧
      ∀ c ∈ inConns child.outputs cs, ∀ a, c.2 = Sparkle.IR.AST.Expr.ref a → a ≠ w

theorem instNames_appendN : ∀ (l1 l2 : List Stmt),
    instNames (l1 ++ l2) = instNames l1 ++ instNames l2
  | [], _ => rfl
  | st :: l1, l2 => by
    cases st
    case inst mn i cs => exact congrArg (i :: ·) (instNames_appendN l1 l2)
    all_goals exact instNames_appendN l1 l2

theorem instNames_reverseN : ∀ (l : List Stmt), instNames l.reverse = (instNames l).reverse
  | [] => rfl
  | st :: l => by
    rw [List.reverse_cons, instNames_appendN, instNames_reverseN l]
    cases st
    case inst mn i cs => exact List.reverse_cons.symm
    all_goals exact List.append_nil _

theorem stmtInstOuts_writesN {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {L : List Stmt} (hk : ∀ S ∈ L, KindN S) (hi : InstFactsN C L) :
    ∀ T ∈ L, ∀ x ∈ stmtInstOuts C T, ∃ mn i cs, T = Stmt.inst mn i cs ∧ WritesN T x := by
  intro T hT x hx
  rcases hk T hT with ⟨l, r, rfl⟩ | ⟨mn, i, cs, rfl⟩
  · exact absurd (show x ∈ ([] : List String) from hx) List.not_mem_nil
  · obtain ⟨child, cwe, w, hC, hout, hwr, -⟩ := hi mn i cs hT
    have he : stmtInstOuts C (.inst mn i cs) = instOutWires child.outputs cs := by
      simp only [stmtInstOuts, hC]
    rw [he, hout, List.mem_singleton] at hx
    rw [hx]
    exact ⟨mn, i, cs, rfl, hwr⟩

theorem bodyInstOuts_instN {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)} :
    ∀ (L : List Stmt),
    (∀ T ∈ L, ∀ x ∈ stmtInstOuts C T, ∃ mn i cs, T = Stmt.inst mn i cs ∧ WritesN T x) →
    ∀ x ∈ bodyInstOuts C L, ∃ mn i cs, Stmt.inst mn i cs ∈ L ∧ WritesN (.inst mn i cs) x
  | [], _, x, hx => by simp [bodyInstOuts] at hx
  | T :: rest, h, x, hx => by
    have hx' : x ∈ stmtInstOuts C T ++ bodyInstOuts C rest := hx
    rcases List.mem_append.mp hx' with h1 | h1
    · obtain ⟨mn, i, cs, hT, hw⟩ := h T List.mem_cons_self x h1
      subst hT
      exact ⟨mn, i, cs, List.mem_cons_self, hw⟩
    · obtain ⟨mn, i, cs, hm, hw⟩ :=
        bodyInstOuts_instN rest (fun T' hT' => h T' (List.mem_cons_of_mem _ hT')) x h1
      exact ⟨mn, i, cs, List.mem_cons_of_mem _ hm, hw⟩

theorem linkedWrites_writesN {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)} :
    ∀ (L : List Stmt), (∀ S ∈ L, KindN S) →
    (∀ T ∈ L, ∀ x ∈ stmtInstOuts C T, ∃ mn i cs, T = Stmt.inst mn i cs ∧ WritesN T x) →
    ∀ x ∈ linkedWrites C L, ∃ T ∈ L, WritesN T x
  | [], _, _, x, hx => by simp [linkedWrites] at hx
  | T :: rest, hk, h, x, hx => by
    have ih := linkedWrites_writesN rest (fun S hS => hk S (List.mem_cons_of_mem _ hS))
      (fun T' hT' => h T' (List.mem_cons_of_mem _ hT'))
    rcases hk T List.mem_cons_self with ⟨l, r, rfl⟩ | ⟨mn, i, cs, rfl⟩
    · have hx' : x ∈ l :: linkedWrites C rest := hx
      rcases List.mem_cons.mp hx' with rfl | h1
      · exact ⟨_, List.mem_cons_self, Or.inl ⟨r, rfl⟩⟩
      · obtain ⟨T', hT', hw⟩ := ih x h1
        exact ⟨T', List.mem_cons_of_mem _ hT', hw⟩
    · have hx' : x ∈ stmtInstOuts C (.inst mn i cs) ++ linkedWrites C rest := hx
      rcases List.mem_append.mp hx' with h1 | h1
      · obtain ⟨-, -, -, -, hw⟩ := h _ List.mem_cons_self x h1
        exact ⟨_, List.mem_cons_self, hw⟩
      · obtain ⟨T', hT', hw⟩ := ih x h1
        exact ⟨T', List.mem_cons_of_mem _ hT', hw⟩

/-- **Two different statements of an ordered body never write one wire.** -/
theorem pw_two_writersN {L : List Stmt} (h : L.Pairwise RWN) {S T : Stmt} {x : String}
    (hS : S ∈ L) (hT : T ∈ L) (hne : S ≠ T) (hSx : WritesN S x) (hTx : WritesN T x) : False := by
  induction L with
  | nil => simp at hS
  | cons U rest ih =>
    have hc := List.pairwise_cons.mp h
    rcases List.mem_cons.mp hS with hSU | hS'
    · rcases List.mem_cons.mp hT with hTU | hT'
      · exact hne (hSU.trans hTU.symm)
      · rw [hSU] at hSx
        exact hc.1 T hT' x hTx (writesN_names hSx)
    · rcases List.mem_cons.mp hT with hTU | hT'
      · rw [hTU] at hTx
        exact hc.1 S hS' x hSx (writesN_names hTx)
      · exact ih hc.2 hS' hT'

/-- **`linkedWF` of an ordered body of assignments and instances.** -/
theorem linkedWF_ofN {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)} :
    ∀ (L : List Stmt), L.Pairwise RWN → (∀ S ∈ L, KindN S) → InstFactsN C L →
      linkedWF C L = true
  | [], _, _, _ => rfl
  | S :: rest, hpw, hk, hi => by
    have hp := List.pairwise_cons.mp hpw
    have hkr : ∀ S' ∈ rest, KindN S' := fun S' h => hk S' (List.mem_cons_of_mem _ h)
    have hir : InstFactsN C rest := fun mn i cs h => hi mn i cs (List.mem_cons_of_mem _ h)
    have ih := linkedWF_ofN rest hp.2 hkr hir
    have hwr := stmtInstOuts_writesN hkr hir
    have hlw : ∀ x ∈ stmtNamesN S, (linkedWrites C rest).contains x = false := by
      intro x hx
      cases hc : (linkedWrites C rest).contains x with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨T, hT, hTw⟩ := linkedWrites_writesN rest hkr hwr x (List.contains_iff_mem.mp hc)
        exact hp.1 T hT x hTw hx
    have hbo : ∀ x ∈ stmtNamesN S, (bodyInstOuts C rest).contains x = false := by
      intro x hx
      cases hc : (bodyInstOuts C rest).contains x with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨mn, i, cs, hT, hTw⟩ :=
          bodyInstOuts_instN rest hwr x (List.contains_iff_mem.mp hc)
        exact hp.1 _ hT x hTw hx
    rcases hk S List.mem_cons_self with ⟨l, r, rfl⟩ | ⟨mn, i, cs, rfl⟩
    · have e1 : (!(bodyInstOuts C rest).contains l) = true := by
        simp only [hbo l (by rw [stmtNamesN_assign]; exact List.mem_cons_self), Bool.not_false]
      have e2 : (Sparkle.IR.Reorder.refsOf r).all
          (fun n => !(bodyInstOuts C rest).contains n) = true := by
        apply List.all_eq_true.mpr
        intro n hn
        simp only [hbo n (by rw [stmtNamesN_assign]; exact List.mem_cons_of_mem _ hn),
          Bool.not_false]
      simp only [linkedWF, e1, e2, ih, Bool.and_self]
    · obtain ⟨child, cwe, w, hC, hout, hwS, -⟩ := hi mn i cs List.mem_cons_self
      have hA : (instOutWires child.outputs cs).all
          (fun w => !(linkedWrites C rest).contains w) = true := by
        rw [hout]
        simp only [List.all_cons, List.all_nil, Bool.and_true,
          hlw w (writesN_names hwS), Bool.not_false]
      have hB : decide (instOutWires child.outputs cs).Nodup = true := by
        rw [hout]
        simp
      -- the connection conjunct is proved in place (its `match` is the definition's own)
      simp only [linkedWF, hC, hA, hB, ih, Bool.and_self, Bool.true_and, Bool.and_true]
      apply List.all_eq_true.mpr
      intro c hc
      try dsimp only
      cases hc2 : c.2
      case ref w' =>
        have hw' : w' ∈ stmtNamesN (.inst mn i cs) := by
          rw [stmtNamesN_inst]
          exact List.mem_filterMap.mpr ⟨c, hc, connRefN_of hc2⟩
        simp only [hlw w' hw', Bool.not_false, Bool.or_true]
      all_goals rfl

/-- **`noSelfRead`** from the instance facts. -/
theorem noSelfRead_ofN {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {L : List Stmt} (hk : ∀ S ∈ L, KindN S) (hi : InstFactsN C L) :
    Tools.ShippingHierPremisesBase.noSelfRead C L = true := by
  unfold Tools.ShippingHierPremisesBase.noSelfRead
  apply List.all_eq_true.mpr
  intro S hS
  rcases hk S hS with ⟨l, r, rfl⟩ | ⟨mn, i, cs, rfl⟩
  · rfl
  · obtain ⟨child, cwe, w, hC, hout, -, hself⟩ := hi mn i cs hS
    simp only [hC]
    rw [hout]
    apply List.all_eq_true.mpr
    intro c hc
    try dsimp only
    cases hc2 : c.2
    case ref a =>
      have hne : a ≠ w := hself c hc a hc2
      have hcw : [w].contains a = false := by
        cases hcw : [w].contains a with
        | false => rfl
        | true => exact absurd (List.mem_singleton.mp (List.contains_iff_mem.mp hcw)) hne
      simp only [hcw, Bool.not_false]
    all_goals rfl

/-- **`kidsComb`** from the callees' combinational facts and the keyed
connections. -/
theorem kidsComb_ofN {ms : List Sparkle.IR.AST.Module} {L : List Stmt}
    (hk : ∀ S ∈ L, KindN S)
    (hi : ∀ mn i cs, Stmt.inst mn i cs ∈ L → ∃ x, Sparkle.IR.Machine.moduleByName ms mn = some x ∧
      Tools.ShippingGateChildComb.ChildComb x ∧
      ∀ p ∈ x.inputs, ∃ a, cs.lookup p.name = some (Sparkle.IR.AST.Expr.ref a)) :
    Tools.ShippingMachineDepthH.kidsComb ms L = true := by
  unfold Tools.ShippingMachineDepthH.kidsComb
  apply List.all_eq_true.mpr
  intro S hS
  rcases hk S hS with ⟨l, r, rfl⟩ | ⟨mn, i, cs, rfl⟩
  · rfl
  · obtain ⟨x, hx, cc, hconn⟩ := hi mn i cs hS
    obtain ⟨ty, hty⟩ := cc.output
    have hno : (x.inputs.map (·.name)).contains "out" = false := by
      cases hc : (x.inputs.map (·.name)).contains "out" with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
        have ha := cc.inputAlloc p hp
        rw [hpn] at ha
        exact nAllocOutN ha
    have h2 : Tools.ShippingHierOptRunH.readsClosed (x.inputs.map (·.name)) x.body = true := by
      rw [← Tools.ShippingMachineDepthHR.readsClosedB_eq]
      exact cc.closed
    have h3 : x.outputs.all (fun p => (Sparkle.IR.Reorder.writesOf x.body).contains p.name) =
        true := by
      rw [hty]
      simp only [List.all_cons, List.all_nil, Bool.and_true]
      exact List.contains_iff_mem.mpr cc.outDriven
    have h4 : x.outputs.all (fun p => !(x.inputs.map (·.name)).contains p.name) = true := by
      rw [hty]
      simp only [List.all_cons, List.all_nil, Bool.and_true, hno, Bool.not_false]
    -- the connection conjunct is proved in place (its `match` is the definition's own)
    simp only [hx, cc.assigns, h2, h3, h4, Bool.and_self, Bool.true_and]
    apply List.all_eq_true.mpr
    intro p hp
    obtain ⟨a, ha⟩ := hconn p hp
    try dsimp only
    simp only [ha]

/-! ## Connections keyed by ports -/

theorem lookup_snocN {ins : List (String × Sparkle.IR.AST.Expr)} {o : String}
    {v : Sparkle.IR.AST.Expr} (h : o ∉ ins.map Prod.fst) : (ins ++ [(o, v)]).lookup o = some v := by
  induction ins with
  | nil => simp [List.lookup]
  | cons q rest ih =>
    obtain ⟨k, v'⟩ := q
    have hq : o ≠ k := fun he => h (by rw [he]; exact List.mem_cons_self)
    have hr : o ∉ rest.map Prod.fst := fun hm => h (List.mem_cons_of_mem _ hm)
    have hb : (o == k) = false := by simpa using hq
    show List.lookup o ((k, v') :: (rest ++ [(o, v)])) = some v
    rw [List.lookup_cons]
    simp only [hb]
    exact ih hr

theorem lookup_of_fstN {ins : List (String × Sparkle.IR.AST.Expr)} {k : String}
    (h : k ∈ ins.map Prod.fst) : ∃ v, ins.lookup k = some v ∧ (k, v) ∈ ins := by
  induction ins with
  | nil => simp at h
  | cons q rest ih =>
    obtain ⟨k', v'⟩ := q
    by_cases hk : k = k'
    · subst hk
      exact ⟨v', by simp [List.lookup], List.mem_cons_self⟩
    · have h0 : k ∈ k' :: rest.map Prod.fst := h
      have h' : k ∈ rest.map Prod.fst := by
        rcases List.mem_cons.mp h0 with he | he
        · exact absurd he hk
        · exact he
      obtain ⟨v, hv, hm⟩ := ih h'
      refine ⟨v, ?_, List.mem_cons_of_mem _ hm⟩
      have hb : (k == k') = false := by simpa using hk
      show List.lookup k ((k', v') :: rest) = some v
      rw [List.lookup_cons]
      simp only [hb]
      exact hv

/-- **One instance's facts** from its keyed connections. -/
theorem instFacts_oneN {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {x : Sparkle.IR.AST.Module} {cwe : Sparkle.IR.Semantics.WEnv} {i : String}
    {cs : List (String × Sparkle.IR.AST.Expr)}
    (hC : C x.name = some (x, cwe)) (hc : ConnOkN x cs) :
    ∃ child cwe w, C x.name = some (child, cwe) ∧ instOutWires child.outputs cs = [w] ∧
      WritesN (.inst x.name i cs) w ∧
      ∀ c ∈ inConns child.outputs cs, ∀ a, c.2 = Sparkle.IR.AST.Expr.ref a → a ≠ w := by
  obtain ⟨ins, o, k, w, hout, hcs, hmap, hrefs, hoin⟩ := hc
  have hoin' : o ∉ ins.map Prod.fst := by rw [hmap]; exact hoin
  have hl : cs.lookup o = some (Sparkle.IR.AST.Expr.ref w) := by
    rw [hcs]
    exact lookup_snocN hoin'
  refine ⟨x, cwe, w, hC, ?_, ?_, ?_⟩
  · rw [hout]
    have hl' : cs.lookup ({ name := o, ty := .bitVector k } : Sparkle.IR.AST.Port).name =
        some (Sparkle.IR.AST.Expr.ref w) := hl
    rw [Tools.ShippingHierOpen.instOutWires_cons, hl']
    try rfl
  · rw [hcs]
    exact Or.inr ⟨x.name, i, o, ins, rfl⟩
  · intro c hc a ha he
    have hc' := List.mem_filter.mp hc
    rw [hcs] at hc'
    rcases List.mem_append.mp hc'.1 with h1 | h1
    · obtain ⟨a', ha', hne⟩ := hrefs c h1
      rw [ha] at ha'
      apply hne
      rw [← Sparkle.IR.AST.Expr.ref.inj ha']
      exact he
    · have hco : c = (o, Sparkle.IR.AST.Expr.ref w) := List.mem_singleton.mp h1
      have h2 := hc'.2
      rw [hout, hco] at h2
      simp at h2

/-- The keyed connections connect every input port by a wire. -/
theorem conn_inputsN {x : Sparkle.IR.AST.Module} {cs : List (String × Sparkle.IR.AST.Expr)}
    (hc : ConnOkN x cs) :
    ∀ p ∈ x.inputs, ∃ a, cs.lookup p.name = some (Sparkle.IR.AST.Expr.ref a) := by
  obtain ⟨ins, o, k, w, -, hcs, hmap, hrefs, -⟩ := hc
  intro p hp
  have hk : p.name ∈ ins.map Prod.fst := by
    rw [hmap]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  obtain ⟨v, hv, hm⟩ := lookup_of_fstN hk
  obtain ⟨a, ha, -⟩ := hrefs _ hm
  refine ⟨a, ?_⟩
  rw [hcs, List.lookup_append, hv]
  exact congrArg some ha

end lists

/-! ## The returned core module -/

section final
open Sparkle.IR.AST Sparkle.IR.Builder Sparkle.Compiler.Elab
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingHierState (instNames)

/-- What the naming walk concludes of the core module (file header). -/
def NFin (G : Sparkle.IR.AST.Module → Prop) (m : Sparkle.IR.AST.Module) : Prop :=
  (instNames m.body).Nodup ∧
  (∀ mn i cs, Stmt.inst mn i cs ∈ m.body → ∃ x, G x ∧ x.name = mn) ∧
  ∀ ms : List Sparkle.IR.AST.Module,
    (∀ x, G x → Sparkle.IR.Machine.moduleByName ms x.name = some x) →
    Tools.ShippingHierOpen.linkedWF (childMap ms) m.body = true ∧
    Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) m.body = true ∧
    Tools.ShippingHierPremisesBase.outsExtracted (childMap ms) m = true ∧
    ((∀ x, G x → Tools.ShippingGateChildComb.ChildComb x) →
      Tools.ShippingMachineDepthH.kidsComb ms m.body = true)

/-- **`outsExtracted`** of a module whose instance outputs are declared,
non-input wires, from the order and the instance facts. -/
theorem outsExtracted_ofN {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {m : Sparkle.IR.AST.Module} (hk : ∀ S ∈ m.body, KindN S) (hpw : m.body.Pairwise RWN)
    (hi : InstFactsN C m.body)
    (hwire : ∀ mn i cs, Stmt.inst mn i cs ∈ m.body → ∀ w, WritesN (.inst mn i cs) w →
      w ∈ m.wires.map (·.name) ∧ w ∉ m.inputs.map (·.name)) :
    Tools.ShippingHierPremisesBase.outsExtracted C m = true := by
  unfold Tools.ShippingHierPremisesBase.outsExtracted
  apply List.all_eq_true.mpr
  intro w hw
  try dsimp only
  obtain ⟨mn, i, cs, hT, hTw⟩ := bodyInstOuts_instN m.body (stmtInstOuts_writesN hk hi) w hw
  obtain ⟨hwW, hwI⟩ := hwire mn i cs hT w hTw
  obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hwW
  obtain ⟨o, hmem⟩ := writesN_inst_mem hTw
  have ha : (Sparkle.IR.HierCheck.connRefs m.body).contains w = true := by
    apply List.contains_iff_mem.mpr
    unfold Sparkle.IR.HierCheck.connRefs
    exact List.mem_flatMap.mpr ⟨_, hT, List.mem_filterMap.mpr ⟨_, hmem, rfl⟩⟩
  have hb : (Sparkle.IR.HierCheck.drivesOf m.body).contains w = false := by
    cases hc : (Sparkle.IR.HierCheck.drivesOf m.body).contains w with
    | false => rfl
    | true =>
      exfalso
      have hm := List.contains_iff_mem.mp hc
      unfold Sparkle.IR.HierCheck.drivesOf at hm
      rcases List.mem_append.mp hm with h1 | h1
      · have h1' : w ∈ m.body.flatMap Sparkle.IR.Reorder.stmtWrites := h1
        obtain ⟨S, hS, hSw⟩ := List.mem_flatMap.mp h1'
        rcases hk S hS with ⟨l, r, rfl⟩ | ⟨mn', i', cs', rfl⟩
        · have hwl : w = l := List.mem_singleton.mp hSw
          rw [← hwl] at hS
          exact pw_two_writersN hpw hS hT (by intro h; cases h) (Or.inl ⟨r, rfl⟩) hTw
        · exact absurd (show w ∈ ([] : List String) from hSw) List.not_mem_nil
      · obtain ⟨S, hS, hSr⟩ := List.mem_filterMap.mp h1
        rcases hk S hS with ⟨l, r, rfl⟩ | ⟨mn', i', cs', rfl⟩ <;> simp at hSr
  have hc : (m.inputs.map (·.name)).contains w = false := by
    cases hc : (m.inputs.map (·.name)).contains w with
    | false => rfl
    | true => exact absurd (List.contains_iff_mem.mp hc) hwI
  refine List.contains_iff_mem.mpr (List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, ?_⟩, hpn⟩)
  show ((Sparkle.IR.HierCheck.connRefs m.body).contains p.name &&
    !(Sparkle.IR.HierCheck.drivesOf m.body).contains p.name &&
    !(m.inputs.map (·.name)).contains p.name) = true
  simp only [hpn, ha, hb, hc, Bool.not_false, Bool.and_self]

/-- **The naming walk's conclusion on the returned core module** (the
entry's tail: output port, `out := wire`, no clock/reset, `finalize`). -/
theorem names_final_of {G : Sparkle.IR.AST.Module → Prop} {I : List String}
    {sm0 st : CircuitState} {wire : String} {ty : Sparkle.IR.Type.HWType}
    {m : Sparkle.IR.AST.Module}
    (h : NOk G I sm0)
    (hst : st = (CircuitM.emitAssign "out" (.ref wire) (CircuitM.addOutput "out" ty sm0).2).2)
    (hm : m = (addClockResetIfSequential st.module).finalize) : NFin G m := by
  have hmod : st.module =
      (sm0.module.addOutput { name := "out", ty := ty }).addStmt (.assign "out" (.ref wire)) := by
    subst hst; rfl
  have hkst : ∀ x ∈ st.module.body, KindN x := by
    intro x hx
    rw [hmod] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl ⟨_, _, rfl⟩
    · exact h.kinds x hx
  have hcomb : addClockResetIfSequential st.module = st.module := by
    apply addClockReset_des
    intro x hx
    rcases hkst x hx with ⟨l, r, rfl⟩ | ⟨mn, i, cs, rfl⟩
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr ⟨_, _, _, rfl⟩
  have hbody : m.body = (Stmt.assign "out" (.ref wire) :: sm0.module.body).reverse := by
    rw [hm, hcomb, hmod]
    try rfl
  have hwires : m.wires = sm0.module.wires.reverse := by
    rw [hm, hcomb, hmod]
    try rfl
  have hins : m.inputs = sm0.module.inputs.reverse := by
    rw [hm, hcomb, hmod]
    try rfl
  have hout : ∀ S ∈ sm0.module.body, "out" ∉ stmtNamesN S :=
    fun S hS ho => nAllocOutN (h.alloc _ (h.nmU S hS _ ho))
  have hpw : m.body.Pairwise RWN := by
    rw [hbody]
    apply List.pairwise_reverse.mpr
    apply List.pairwise_cons.mpr
    refine ⟨fun S hS x hx => ?_, h.ord⟩
    rw [writesN_assign hx]
    exact hout S hS
  have hk : ∀ S ∈ m.body, KindN S := by
    intro S hS
    rw [hbody, List.mem_reverse] at hS
    rcases List.mem_cons.mp hS with rfl | hS
    · exact Or.inl ⟨_, _, rfl⟩
    · exact h.kinds S hS
  have hinst : ∀ mn i cs, Stmt.inst mn i cs ∈ m.body → Stmt.inst mn i cs ∈ sm0.module.body := by
    intro mn i cs hmem
    rw [hbody, List.mem_reverse] at hmem
    rcases List.mem_cons.mp hmem with he | hmem
    · cases he
    · exact hmem
  refine ⟨?_, ?_, fun ms hms => ?_⟩
  · rw [hbody, instNames_reverseN]
    exact Tools.ShippingEntrySoundness.nodup_reverse h.nd
  · intro mn i cs hmem
    obtain ⟨x, hG, hxn, -⟩ := h.conn mn i cs (hinst mn i cs hmem)
    exact ⟨x, hG, hxn⟩
  · have hC : ∀ x, G x → childMap ms x.name = some (x, declWidth x) := by
      intro x hx
      show (Sparkle.IR.Machine.moduleByName ms x.name).map _ = _
      rw [hms x hx]
      try rfl
    have hfacts : InstFactsN (childMap ms) m.body := by
      intro mn i cs hmem
      obtain ⟨x, hG, hxn, hc⟩ := h.conn mn i cs (hinst mn i cs hmem)
      subst hxn
      exact instFacts_oneN (hC x hG) hc
    refine ⟨linkedWF_ofN _ hpw hk hfacts, noSelfRead_ofN hk hfacts,
      outsExtracted_ofN hk hpw hfacts ?_, fun hcc => kidsComb_ofN hk ?_⟩
    · intro mn i cs hmem w hw
      obtain ⟨h1, h2⟩ := h.wr _ (hinst mn i cs hmem) w hw
      refine ⟨?_, ?_⟩
      · rw [hwires, List.map_reverse, List.mem_reverse]
        exact h1
      · rw [hins, List.map_reverse, List.mem_reverse, h.ins]
        exact h2
    · intro mn i cs hmem
      obtain ⟨x, hG, hxn, hc⟩ := h.conn mn i cs (hinst mn i cs hmem)
      subst hxn
      exact ⟨x, hms x hG, hcc x hG, conn_inputsN hc⟩

end final

/-! ## The prepared state -/

section prepared
open Sparkle.Compiler.Elab Sparkle.IR.Builder
open Tools.ShippingMixedEntrySoundness (Setup prepare extend start)
open Tools.ShippingMixedInputSoundness (inputState inputWire)

/-- A prepared state: no statement, no record, reserved names allocated,
inputs reserved. -/
def PrepOkN (s : CircuitState) : Prop :=
  s.module.body = [] ∧ (∀ w e, s.translateRecord.get? w = some e → False) ∧
    (∀ x, s.usedNames.contains x = true → Sparkle.IR.NameHints.Allocated x) ∧
    (∀ x ∈ s.module.inputs.map (·.name), s.usedNames.contains x = true)

theorem prepOk_initN (N : String) : PrepOkN (CircuitM.init N) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro w e he
    simp [CircuitM.init] at he
  · intro x hx
    simp [CircuitM.init] at hx
  · intro x hx
    simp [CircuitM.init, Sparkle.IR.AST.Module.empty] at hx

theorem inputState_eqN (s : CircuitState) (name : String) (ty : Sparkle.IR.Type.HWType) :
    inputState s name ty =
      { (CircuitM.makeWire name ty true s).2 with
        usedNames := (CircuitM.makeWire name ty true s).2.usedNames.insert (inputWire s name ty),
        module := (CircuitM.makeWire name ty true s).2.module.addInput
          { name := inputWire s name ty, ty := ty } } :=
  Tools.ShippingEntrySoundness.addInput_state _ _ _

theorem inputState_inputsN (s : CircuitState) (name : String) (ty : Sparkle.IR.Type.HWType) :
    (inputState s name ty).module.inputs =
      { name := inputWire s name ty, ty := ty } :: s.module.inputs := by
  rw [inputState_eqN]
  show { name := inputWire s name ty, ty := ty } ::
    (CircuitM.makeWire name ty true s).2.module.inputs = _
  rw [makeWire_module]
  try rfl

theorem prepOk_inputN {s : CircuitState} (h : PrepOkN s) (name : String)
    (ty : Sparkle.IR.Type.HWType) : PrepOkN (inputState s name ty) := by
  have hspec := CircuitM.makeWire_spec name ty true s
  have hbody : (inputState s name ty).module.body = s.module.body := by
    rw [inputState_eqN]
    exact hspec.2.2.1
  have hrec : (inputState s name ty).translateRecord = s.translateRecord := by
    rw [inputState_eqN]
    exact CircuitM.makeWire_translateRecord name ty true s
  have hused : (inputState s name ty).usedNames =
      (s.usedNames.insert (inputWire s name ty)).insert (inputWire s name ty) := by
    rw [inputState_eqN]
    show (CircuitM.makeWire name ty true s).2.usedNames.insert (inputWire s name ty) = _
    rw [hspec.2.1]
    try rfl
  have halloc : Sparkle.IR.NameHints.Allocated (inputWire s name ty) :=
    CircuitM.makeWire_allocated name ty true s
  refine ⟨by rw [hbody]; exact h.1, ?_, ?_, ?_⟩
  · intro w e he
    rw [hrec] at he
    exact h.2.1 w e he
  · intro x hx
    rw [hused] at hx
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hx
    rcases hx with h1 | h1 | h1
    · rw [← h1]; exact halloc
    · rw [← h1]; exact halloc
    · exact h.2.2.1 x h1
  · intro x hx
    rw [inputState_inputsN, List.map_cons] at hx
    rw [hused]
    rcases List.mem_cons.mp hx with h1 | h1
    · rw [h1]
      simp [Std.HashSet.contains_insert]
    · simp [Std.HashSet.contains_insert, h.2.2.2 x h1]

theorem prepare_prepOkN (bools : Lean.FVarId → Bool)
    (bits : (id : Lean.FVarId) → (n : Nat) → BitVec n) :
    ∀ (L : List ((Lean.Name × MixedGateBinder) × Lean.FVarId)) (a : Setup),
    PrepOkN a.state → PrepOkN (prepare bools bits L a).state
  | [], _, h => h
  | ((nm, k), id) :: rest, a, h => by
    apply prepare_prepOkN bools bits rest (extend a ((nm, k), id) bools bits)
    cases k with
    | domain => exact h
    | bool => exact prepOk_inputN h nm.toString .bit
    | bits n => exact prepOk_inputN h nm.toString (.bitVector n)

theorem prepare_inputs_monoN (bools : Lean.FVarId → Bool)
    (bits : (id : Lean.FVarId) → (n : Nat) → BitVec n) :
    ∀ (L : List ((Lean.Name × MixedGateBinder) × Lean.FVarId)) (a : Setup) (x : String),
    x ∈ a.state.module.inputs.map (·.name) →
      x ∈ (prepare bools bits L a).state.module.inputs.map (·.name)
  | [], _, _, h => h
  | ((nm, k), id) :: rest, a, x, h => by
    apply prepare_inputs_monoN bools bits rest (extend a ((nm, k), id) bools bits) x
    cases k with
    | domain => exact h
    | bool =>
      show x ∈ (inputState a.state nm.toString .bit).module.inputs.map (·.name)
      rw [inputState_inputsN, List.map_cons]
      exact List.mem_cons_of_mem _ h
    | bits n =>
      show x ∈ (inputState a.state nm.toString (.bitVector n)).module.inputs.map (·.name)
      rw [inputState_inputsN, List.map_cons]
      exact List.mem_cons_of_mem _ h

/-- **A prepared (non-domain) binder is bound to an input port** of the
prepared state (`prepare_lookup_hit` with the port). -/
theorem prepare_lookup_hitI (bools : Lean.FVarId → Bool)
    (bits : (id : Lean.FVarId) → (n : Nat) → BitVec n) :
    ∀ (L : List ((Lean.Name × MixedGateBinder) × Lean.FVarId)) (a : Setup) (nm : Lean.Name)
      (k : MixedGateBinder) (id : Lean.FVarId),
    (L.map (·.2)).Nodup → ((nm, k), id) ∈ L → k ≠ .domain →
    ∃ z, (prepare bools bits L a).context.varMap.lookup id = some z ∧
      z ∈ (prepare bools bits L a).state.module.inputs.map (·.name)
  | [], _, _, _, _, _, hm, _ => by simp at hm
  | ((nm', k'), i) :: rest, a, nm, k, id, hnd, hm, hk => by
    have hnd' := List.nodup_cons.mp hnd
    show ∃ z, (prepare bools bits rest (extend a ((nm', k'), i) bools bits)).context.varMap.lookup
      id = some z ∧
      z ∈ (prepare bools bits rest (extend a ((nm', k'), i) bools bits)).state.module.inputs.map
        (·.name)
    rcases List.mem_cons.mp hm with he | hm'
    · have hid : id = i := (Prod.mk.inj he).2
      have hkk : k = k' := (Prod.mk.inj (Prod.mk.inj he).1).2
      rw [hkk] at hk
      rw [hid]
      rw [prepare_lookup_keep bools bits rest _ i
        (fun x hx hxe => hnd'.1 (List.mem_map.mpr ⟨x, hx, hxe⟩))]
      cases k' with
      | domain => exact absurd rfl hk
      | bool =>
        refine ⟨_, Tools.ShippingEntrySoundness.lookup_cons_self _ _ _, ?_⟩
        apply prepare_inputs_monoN
        show inputWire a.state nm'.toString .bit ∈
          (inputState a.state nm'.toString .bit).module.inputs.map (·.name)
        rw [inputState_inputsN, List.map_cons]
        exact List.mem_cons_self
      | bits n =>
        refine ⟨_, Tools.ShippingEntrySoundness.lookup_cons_self _ _ _, ?_⟩
        apply prepare_inputs_monoN
        show inputWire a.state nm'.toString (.bitVector n) ∈
          (inputState a.state nm'.toString (.bitVector n)).module.inputs.map (·.name)
        rw [inputState_inputsN, List.map_cons]
        exact List.mem_cons_self
    · exact prepare_lookup_hitI bools bits rest _ nm k id hnd'.2 hm' hk

/-- **The naming invariant at a prepared state** (empty body). -/
theorem nok_of_prepN {G : Sparkle.IR.AST.Module → Prop} {s : CircuitState} (h : PrepOkN s) :
    NOk G (s.module.inputs.map (·.name)) s := by
  obtain ⟨hb, hr, ha, hi⟩ := h
  refine ⟨rfl, hi, ha, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb]; intro st hst; simp at hst
  · rw [hb]; intro st hst; simp at hst
  · rw [hb]; intro mn i cs hst; simp at hst
  · rw [hb]; exact List.nodup_nil
  · rw [hb]; exact List.Pairwise.nil
  · rw [hb]; intro mn i cs hst; simp at hst
  · rw [hb]; intro st hst; simp at hst
  · intro w e he; exact (hr w e he).elim

end prepared

/-! ## The harness and the full entry -/

section harnessN
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingUnifiedEntrySoundness (lookup_of_ports)
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedOutputSoundness (PortInputs declaredWidths declaredWidths_agree)
open Tools.ShippingMixedInputSoundness Tools.ShippingEntrySoundness
open Tools.ShippingCompareLoweringSoundness (ScalarWidthsAgree)
open Tools.ShippingMixedLiteralSoundness (DeclGrows)
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingHierarchySoundness Tools.ShippingLinkCtx
open Tools.ShippingHierTermSoundness (HierValue InstsLinked LeafMeaning initial_link)
open Tools.ShippingMixedInvariant (Separate)
open Tools.ShippingMixedBinarySoundness (Frame)
open Tools.ShippingChildInv (RefLaws InvV Res CacheInv ChildBnd bodyRel profLogIO RealChild)
open Tools.ShippingCacheCoherentRun (SubMap sub_refl)
open Tools.ShippingGateDefines (GateDefines)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- The prepared input names of a body instantiated at `ids`. -/
abbrev prepInsN (bs : List (Lean.Name × MixedGateBinder)) (ids : List FVarId)
    (cache : IO.Ref (Lean.ExprStructMap String)) (N : String) : List String :=
  (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
    (start (entryCompilerState false cache) N)).state.module.inputs.map (·.name)

/-- **On the harness run**: the naming walk's contract of the body gives
`NFin` of the returned core module. -/
theorem namesFinal_of_run {L : RefLaws mref cref} {mF : Std.HashMap Lean.Name Res} {D : Nat}
    {rec : TranslateFn} {bs : List (Lean.Name × MixedGateBinder)} {ids : List FVarId}
    {cache : IO.Ref (Lean.ExprStructMap String)} {N : String}
    {G : Sparkle.IR.AST.Module → Prop} {e : Lean.Expr}
    {wT wT' : Void IO.RealWorld} {wire : String} {sm0 st : CircuitState}
    {ty : Sparkle.IR.Type.HWType} {m : Sparkle.IR.AST.Module}
    (hE : NamW L mF D rec
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) N)).context G (prepInsN bs ids cache N) e)
    (hwT : InvV L wT) (hdT : L.dval wT = D) (hsubT : SubMap (L.val wT') mF)
    (htr : RunsC (rec e "out" false true)
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) N)).context
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) N)).state
      mctx mref cctx cref wT (wire, sm0) wT')
    (hst : st = (CircuitM.emitAssign "out" (.ref wire) (CircuitM.addOutput "out" ty sm0).2).2)
    (hm : m = (addClockResetIfSequential st.module).finalize) : NFin G m := by
  have h0 : NOk G (prepInsN bs ids cache N)
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) N)).state :=
    nok_of_prepN (prepare_prepOkN _ _ (bs.zip ids) (start (entryCompilerState false cache) N)
      (prepOk_initN N))
  obtain ⟨h1, -, -, -⟩ := hE mctx cctx "out" false true _ sm0 wire wT wT' hwT hdT hsubT htr h0
  exact names_final_of h1 hst hm

/-- **The harness with both walks** (`cone_harness_runKED`'s reading of
`mixedHarness_runs`; the old theorems kept): for a design predicate whose
`DesW` and `NamW` hold of the body at every fresh id list, `FinalOk` and
`NFin` of the returned core module and design. -/
theorem cone_harness_names (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) {b : Bool}
    {declName : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)} {body : Lean.Expr}
    {w : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named)
      (profLogIO b) declName bs body) mctx mref cctx cref w (m, d) w') :
    ∃ wT' : Void IO.RealWorld, CacheInv mref cref (L.val wT') ∧
      ∀ G : Sparkle.IR.AST.Module → Prop,
        (∀ (cache' : IO.Ref (Lean.ExprStructMap String)) (ids' : List FVarId), ids'.Nodup →
          ids'.length = bs.length →
          DesW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
              (start (entryCompilerState false cache')
                (Sparkle.IR.ModuleName.ofDecl declName))).context
            G (Sparkle.IR.ModuleName.ofDecl declName)
            (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body) true ∧
          NamW L (L.val wT') D (translateFuelFix (translateStep tenv) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids')
              (start (entryCompilerState false cache')
                (Sparkle.IR.ModuleName.ofDecl declName))).context
            G (prepInsN bs ids' cache' (Sparkle.IR.ModuleName.ofDecl declName))
            (instFVars (ids'.map Lean.Expr.fvar).toArray 0 body)) →
        (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
        FinalOk G (Sparkle.IR.ModuleName.ofDecl declName) m d ∧ NFin G m := by
  obtain ⟨ids, cache, wT, wT', wire, sm0, ty, st, nd, len, hwT, hdT, htr, -, hst, hty, hm,
    hdd⟩ :=
    mixedHarness_runs L hw hd hr
  obtain ⟨⟨hcT, -, -⟩, -, -⟩ := fuel_runsW (tenv := tenv) L hD translateFuelLimit hwT hdT htr
  refine ⟨wT', hcT, fun G hE hpos => ⟨?_, ?_⟩⟩
  · exact desFinal_of_run (hE cache ids nd len).1 hpos hwT hdT (sub_refl _) htr hst hty hm hdd
  · exact namesFinal_of_run (hE cache ids nd len).2 hwT hdT (sub_refl _) htr hst hm

/-- **The full entry with both walks** (`gate_cone_runGED`'s reading of the
run, a copy of its first half; the old theorems kept). -/
theorem gate_cone_runNames {f : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
    {body : Lean.Expr} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module}
    {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref f bs body)
    (bnd : ChildBnd mref cref w) :
    ∃ (M : Sparkle.IR.AST.Module) (Dd : Sparkle.IR.AST.Design) (envR : Lean.Environment)
      (mF : Std.HashMap Lean.Name Res),
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) ∧
      ((∀ x ∈ Dd.modules, x.name ≠ M.name) → design.modules = Dd.modules) ∧
      (∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
        (Sparkle.Compiler.Elab.instancePredicate envR) = some (bs, body)) ∧
      CacheInv mref cref mF ∧
      (∀ G : Sparkle.IR.AST.Module → Prop,
        (∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 →
          ∀ (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId), ids.Nodup →
          ids.length = bs.length →
          DesW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
              (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
            G (Sparkle.IR.ModuleName.ofDecl f)
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) true ∧
          NamW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
            (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
              (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
            G (prepInsN bs ids cache (Sparkle.IR.ModuleName.ofDecl f))
            (instFVars (ids.map Lean.Expr.fvar).toArray 0 body)) →
        (∀ x ∈ bs, ∀ n, x.2 = MixedGateBinder.bits n → 0 < n) →
        FinalOk G (Sparkle.IR.ModuleName.ofDecl f) M Dd ∧ NFin G M) := by
  obtain ⟨L, ⟨hsv, hdep⟩, hq⟩ := bnd
  obtain ⟨M, Dd, w1, hcore, hpost⟩ :=
    Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨M2, D2, w2, hcore2, -, hname, hmods⟩ := Tools.ShippingCacheCoherentRun.full_split L hr
  obtain ⟨hMD, -⟩ := runsTo_det hcore2 hcore
  obtain ⟨hM, hD⟩ := Prod.mk.inj hMD
  rw [hM] at hname
  rw [hM, hD] at hmods
  have hreads : ∃ (bb : Bool) (envR : Lean.Environment) (ci : Lean.ConstantInfo)
      (a1 a2 a3 a4 a5 a6 : Void IO.RealWorld),
      RunsTo (Lean.getConstInfo f) mctx mref cctx cref a1 ci a2 ∧
      RunsTo (Lean.getEnv : Lean.Meta.MetaM Lean.Environment) mctx mref cctx cref a5 envR a6 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n)
        (profLogIO bb) f [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref a3 (M, Dd) a4 ∧ InvV L a3 ∧ L.dval a3 ≠ 0 := by
    by_cases h0 : L.dval w = 0
    · obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3, -, -, -⟩ :=
        Tools.ShippingCacheCoherentOuter.core_reads_val0 L (fun L' => bodyRel L') hsv hq h0 hcore
      exact ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩
    · rcases hdep with hz | hci
      · exact absurd hz h0
      · obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3, -, -, -⟩ :=
          Tools.ShippingCacheCoherentVia.core_reads_val L (fun L' => bodyRel L')
            ⟨hci, hsv, hq⟩ h0 hcore
        exact ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩
  obtain ⟨bb, envR, ci, a1, a2, a3, a4, a5, a6, hget, henv, run, hw3, hd3⟩ := hreads
  obtain ⟨dv, hdv, hold, hshape⟩ := gdef a1 ci a2 a5 envR a6 hget henv
  rw [hdv] at run
  obtain ⟨wa, wb, hwa, hda, hharn⟩ := sfc_mixed_run L hold hshape hw3 run
  have hDa : L.dval wa ≠ 0 := by rw [hda]; exact hd3
  obtain ⟨wT', hcache, hdes⟩ :=
    cone_harness_names (tenv := envR) L (D := L.dval wa) hDa hwa rfl hharn
  exact ⟨M, Dd, envR, L.val wT', hpost, hmods, ⟨dv, hshape⟩, hcache,
    fun G hE hpos => hdes G (fun cache ids nd len => hE L (L.dval wa) hDa cache ids nd len)
      hpos⟩

end harnessN

/-! ## The five conjuncts for a parent of one first-gate child -/

section facts
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST
open Tools.ShippingChildInv (RefLaws Res CacheInv ChildBnd RealChild)
open Tools.ShippingEntrySoundness (RunsTo FExpr quoteDecl)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingGateDefines (GateDefines)
open Tools.ShippingMixedEntrySoundness (prepare start)
open Tools.ShippingMachineLinked (childMap)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- The design predicate: `mF`'s entry of the callee `c`. -/
def ChildGN (c : Lean.Name) (mF : Std.HashMap Lean.Name Res) (x : Sparkle.IR.AST.Module) : Prop :=
  ∃ y : Res, mF.get? c = some y ∧ x = y.1

theorem childGN_eq {c : Lean.Name} {mF : Std.HashMap Lean.Name Res} {y : Res}
    (hy : mF.get? c = some y) : ∀ x, ChildGN c mF x → x = y.1 := by
  intro x hx
  obtain ⟨y', hy', hx'⟩ := hx
  rw [hy] at hy'
  cases hy'
  exact hx'

/-- A gate child's output port is not named like an input. -/
theorem leaf_extra_of_combN {x : Sparkle.IR.AST.Module}
    (cc : Tools.ShippingGateChildComb.ChildComb x) :
    ∀ p ∈ x.outputs, p.name ∉ x.inputs.map (·.name) := by
  intro p hp hpin
  obtain ⟨ty, hty⟩ := cc.output
  rw [hty] at hp
  have hpn : p.name = "out" := by rw [List.mem_singleton.mp hp]
  obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hpin
  have ha := cc.inputAlloc q hq
  rw [hqn, hpn] at ha
  exact nAllocOutN ha

/-- **A first-gate child's module is combinational and closed**
(`ChildFull.comb`, from the child's own run and `EntryDefines`). -/
theorem first_child_combN {c : Name} {y : Res} {dn : Name} {names : List Name} {n : Nat}
    {fe : FExpr}
    (entry : EntryDefines mctx mref cctx cref c (quoteDecl dn names n fe))
    (hwf : fe.WF names.length n) (hn : 0 < n) (h : RealChild mref cref c y) :
    Tools.ShippingGateChildComb.ChildComb y.1 := by
  obtain ⟨b, design⟩ := y
  obtain ⟨mctx', cctx', w, w', -, hr⟩ := h.inv
  have entry' : EntryDefines mctx' mref cctx' cref c (quoteDecl dn names n fe) :=
    Tools.ShippingReflectCtx.EntryDefines.ctx entry
  exact (Tools.ShippingFirstGateChild.first_child_fullFacts hr entry' hwf hn).comb

/-- `b` and the core module agree on body, wires and inputs. -/
theorem post_fieldsN {N : String} {M b : Sparkle.IR.AST.Module} (h : ModOk N M)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) :
    b.body = M.body ∧ b.wires = M.wires ∧ b.inputs = M.inputs := by
  obtain ⟨hb, hw⟩ := Tools.ShippingGateDesignPost.dz_fields h
  have hi : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).inputs = M.inputs := by
    unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
    split <;> rfl
  have hasZ : HasInst (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body := by
    rw [hb]
    exact h.has
  have hmc := Tools.ShippingGateDesignPost.mergeChecked_of_inst hasZ
  have hbz : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M := by
    rcases hpost with e | e
    · exact e
    · rw [e, hmc]
  subst hbz
  exact ⟨hb, hw, hi⟩

/-- **Five conjuncts of `combSideB design.modules b`, derived** for a gate
parent whose instance leaves call one first-gate child `c` (file header).
Premises: the run, `GateDefines` (NOT ALLOWED), `ChildBnd`; the child facts
of every `c` entry of a `CacheInv` cache; the body's two walks. -/
theorem gate_combFacts {f c : Lean.Name} {bs : List (Lean.Name × MixedGateBinder)}
    {body : Lean.Expr} {n : Nat} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module}
    {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational f) mctx mref cctx cref w (b, design) w')
    (gdef : GateDefines mctx mref cctx cref f bs body)
    (bnd : ChildBnd mref cref w)
    (hkid : ∀ mF : Std.HashMap Lean.Name Res, CacheInv mref cref mF → ∀ y : Res,
      mF.get? c = some y →
      InstLeafOk (ChildGN c mF) n y ∧ Tools.ShippingGateChildComb.ChildComb y.1 ∧
        y.1.name ≠ Sparkle.IR.ModuleName.ofDecl f ∧
        ∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (k : Nat),
          Tools.ShippingChecksDesign.kidCheck C k y.1 = true)
    (hwalk : ∀ envR : Lean.Environment,
      (∃ dv : Lean.DefinitionVal, mixedCertifiedShape? false [] (.defnInfo dv)
        (Sparkle.Compiler.Elab.instancePredicate envR) = some (bs, body)) →
      ∀ mF : Std.HashMap Lean.Name Res,
      (∀ y : Res, mF.get? c = some y → InstLeafOk2 (ChildGN c mF) n y) →
      ∀ (L' : RefLaws mref cref) (D : Nat), D ≠ 0 →
      ∀ (cache : IO.Ref (Lean.ExprStructMap String)) (ids : List FVarId), ids.Nodup →
      ids.length = bs.length →
      DesW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
        (ChildGN c mF) (Sparkle.IR.ModuleName.ofDecl f)
        (instFVars (ids.map Lean.Expr.fvar).toArray 0 body) true ∧
      NamW L' mF D (translateFuelFix (translateStep envR) translateFuelLimit)
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl f))).context
        (ChildGN c mF) (prepInsN bs ids cache (Sparkle.IR.ModuleName.ofDecl f))
        (instFVars (ids.map Lean.Expr.fvar).toArray 0 body))
    (hpos : ∀ x ∈ bs, ∀ k, x.2 = MixedGateBinder.bits k → 0 < k) :
    Tools.ShippingHierOpen.linkedWF (childMap design.modules) b.body = true ∧
      (Tools.ShippingHierState.instNames b.body).Nodup ∧
      Tools.ShippingHierPremisesBase.noSelfRead (childMap design.modules) b.body = true ∧
      Tools.ShippingHierPremisesBase.outsExtracted (childMap design.modules) b = true ∧
      Tools.ShippingMachineDepthH.kidsComb design.modules b.body = true ∧
      Tools.ShippingDesignSV.kidsPass (childMap design.modules)
        (Tools.ShippingChecksDesign.kidCheck (childMap design.modules) 0) b.body = true := by
  obtain ⟨M, Dd, envR, mF, hpost, hmods, hacc, hcache, hdes⟩ := gate_cone_runNames hr gdef bnd
  have hleaf2 : ∀ y : Res, mF.get? c = some y → InstLeafOk2 (ChildGN c mF) n y :=
    fun y hy => ⟨(hkid mF hcache y hy).1, leaf_extra_of_combN (hkid mF hcache y hy).2.1⟩
  obtain ⟨fin, hnd, hins, hrest⟩ := hdes (ChildGN c mF)
    (fun L' D hD cache ids nd len => hwalk envR hacc mF hleaf2 L' D hD cache ids nd len) hpos
  have hms : ∀ x, ChildGN c mF x →
      Sparkle.IR.Machine.moduleByName design.modules x.name = some x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [hxy]
    exact designHasChild_of_final fin (childGN_eq hy) (hkid mF hcache y hy).2.2.1 hmods
  have hcc : ∀ x, ChildGN c mF x → Tools.ShippingGateChildComb.ChildComb x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [hxy]
    exact (hkid mF hcache y hy).2.1
  obtain ⟨hwf, hself, hout, hkc⟩ := hrest design.modules hms
  obtain ⟨hb, hw, hi⟩ := post_fieldsN fin.mod hpost
  have hopen : Sparkle.IR.HierCheck.openIns b = Sparkle.IR.HierCheck.openIns M := by
    unfold Sparkle.IR.HierCheck.openIns
    rw [hb, hw, hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb]; exact hwf
  · rw [hb]; exact hnd
  · rw [hb]; exact hself
  · unfold Tools.ShippingHierPremisesBase.outsExtracted
    rw [hb, hopen]
    exact hout
  · rw [hb]; exact hkc hcc
  · -- every instance's child is THE `c` entry, a first-gate child: its own check passes
    rw [hb]
    unfold Tools.ShippingDesignSV.kidsPass
    apply List.all_eq_true.mpr
    intro st hst
    cases st
    case inst mn i cs =>
      obtain ⟨x, hx, hxn⟩ := hins mn i cs hst
      subst hxn
      obtain ⟨y, hy, hxy⟩ := hx
      have hC : childMap design.modules x.name = some (x, Sparkle.IR.RegDedup.declWidth x) := by
        show (Sparkle.IR.Machine.moduleByName design.modules x.name).map _ = _
        rw [hms x ⟨y, hy, hxy⟩]
        try rfl
      simp only [hC]
      rw [hxy]
      exact (hkid mF hcache y hy).2.2.2 _ 0
    all_goals rfl

/-- `combSideB` from its six conjuncts. -/
theorem combSideB_ofN {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    (h1 : Tools.ShippingHierOpen.linkedWF (childMap ms) b.body = true)
    (h2 : (Tools.ShippingHierState.instNames b.body).Nodup)
    (h3 : Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) b.body = true)
    (h4 : Tools.ShippingHierPremisesBase.outsExtracted (childMap ms) b = true)
    (h5 : Tools.ShippingMachineDepthH.kidsComb ms b.body = true)
    (h6 : Tools.ShippingHierTyped.hierTyped (childMap ms) b = true) :
    Tools.ShippingGateCombSide.combSideB ms b = true := by
  simp only [Tools.ShippingGateCombSide.combSideB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩

/-- What `designSideB` still asks once the children's check is derived: the
two emitted-text conjuncts of `b` and the connection widths of the shipped
module (decidable, OUTSIDE ALLOWED). -/
def designSideB3 (ms : List Sparkle.IR.AST.Module) (b : Sparkle.IR.AST.Module) : Bool :=
  Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
      (Tools.ShippingDesignSV.weS b) b.body &&
    (Tools.ShippingSeqSVSoundness.seqNames b.body).all
      (fun x => Sparkle.IR.RegDedup.declWidth b x == Tools.ShippingDesignSV.weS b x) &&
    Tools.ShippingDesignSV.portsMatchB (childMap ms) (Sparkle.IR.OptCheck.checkedOptimize b)

/-- `designSideB` from `designSideB3` and the children's check. -/
theorem designSideB_of3 {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    (h : designSideB3 ms b = true)
    (hk : Tools.ShippingDesignSV.kidsPass (childMap ms)
      (Tools.ShippingChecksDesign.kidCheck (childMap ms) 0) b.body = true) :
    Tools.ShippingGateCombSide.designSideB ms b = true := by
  simp only [designSideB3, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [Tools.ShippingGateCombSide.designSideB, Bool.and_eq_true]
  exact ⟨⟨⟨h1, h2⟩, h3⟩, hk⟩

end facts

end Tools.ShippingGateParentRun

#print axioms Tools.ShippingGateParentRun.linkedWF_ofN
#print axioms Tools.ShippingGateParentRun.names_final_of
#print axioms Tools.ShippingGateParentRun.cone_harness_names
#print axioms Tools.ShippingGateParentRun.gate_cone_runNames
#print axioms Tools.ShippingGateParentRun.gate_combFacts
