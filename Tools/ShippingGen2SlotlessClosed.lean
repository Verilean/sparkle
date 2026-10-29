import Tools.ShippingGen2Leaf
import Tools.ShippingSeqChildIfaceA
import Tools.ShippingMachineChildComb
import Tools.ShippingMergeClosed
import Tools.ShippingLeafOneOut
import Tools.ShippingCombKidText
import Tools.ShippingCallsParent
set_option autoImplicit false

/-! # S2-c: read-closedness of the slotless leaf's shipped module (scripts/gen2/STEP_S2C_FREEZE.md rev1)

* `slotless_closed_full` (pure, §1): from `closeLets`' success, the transition's closedness and assign-only body,
  `slots = []` and the zero-width cleanup identity, the module the full entry returns (either `hpost` branch) is
  read-closed over its input ports and assignments only. Any `K` (including `K = 0`) and any `lay.outs`. Internal
  steps: `closeLets_closed` (`t → t'`) and `closeMachine_slotless_closed` (`t' → closeMachine lay t'`).
  No name freshness, no packed-tail premise, no `Acyclic t.body` premise.
* `slotless_closed_ofRun` (A boundary, §2): the premises of `slotless_closed_full` from the run `ran` itself
  (`synthesizeMachineCertified_leaf_runs`, `synthesizeMixedCertified_returns`, `transition_closed` with
  `Pkg.body_eq`, and the `MachineWired` cleanup conjunct of `Pkg.trace`). No `MachineCloses`. -/
namespace Tools.ShippingGen2

section Pure
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder

/-! ## Small pure facts -/

/-- An acyclic body is assignments only. -/
theorem slc_assign_of_acyclic {body : List Stmt} (h : Tools.ShippingSettledSoundness.Acyclic body) :
    ∀ st ∈ body, ∃ l r, st = Stmt.assign l r := by
  induction h with
  | nil => intro st hs; cases hs
  | @cons l r rest _ _ _ ih =>
    intro st hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨l, r, rfl⟩
    · exact ih st hs

/-- Assignments only, as the `Bool` check. -/
theorem slc_all_isAssign {body : List Stmt} (h : ∀ st ∈ body, ∃ l r, st = Stmt.assign l r) :
    body.all Sparkle.IR.RegDedup.isAssign = true := by
  rw [List.all_eq_true]
  intro st hs
  obtain ⟨l, r, rfl⟩ := h st hs
  rfl

/-- A body with a packed wire ends in `assign out = w`. -/
theorem slc_packed_split {body : List Stmt} {w : String} (h : packedWire? body = some w) :
    body = body.dropLast ++ [Stmt.assign "out" (Expr.ref w)] := by
  unfold packedWire? at h
  split at h
  · rename_i w0 hl
    cases h
    exact Tools.ShippingMachineClose.eq_dropLast_append _ _ hl
  · cases h

theorem slc_mem_writes {st : Stmt} {X : List Stmt} {n : String} (hs : st ∈ X) (hn : n ∈ stmtWrites st) :
    n ∈ writesOf X := by
  unfold writesOf
  exact List.mem_flatMap.mpr ⟨st, hs, hn⟩

theorem slc_of_mem_writes {X : List Stmt} {n : String} (h : n ∈ writesOf X) :
    ∃ st ∈ X, n ∈ stmtWrites st := by
  unfold writesOf at h
  exact List.mem_flatMap.mp h

/-- The first statement of a read-closed body reads only names of `S`. -/
theorem slc_head_reads {S : List String} {st : Stmt} {rest : List Stmt}
    (h : readsClosedB S (st :: rest) = true) : ∀ n ∈ stmtReads st, n ∈ S := by
  intro n hn
  simp only [readsClosedB, Bool.and_eq_true, List.all_eq_true] at h
  simpa using h.1 n hn

/-- Every alias operand of a `let` chain is the high part of a two-operand concatenation of the body. -/
theorem slc_chain_operand {body : List Stmt} {al : List (Port × String)} {w core : String}
    (hc : Tools.ShippingMachineClose.LetChain body al w core) :
    ∀ pa ∈ al, ∃ x b, Stmt.assign x (Expr.concat [Expr.ref pa.2, Expr.ref b]) ∈ body := by
  induction hc with
  | nil => intro pa hpa; cases hpa
  | @cons p a b w' rest core' hm _ ih =>
    intro pa hpa
    rcases List.mem_cons.mp hpa with rfl | hpa
    · exact ⟨w', b, hm⟩
    · exact ih pa hpa

/-! ## `closeLets` keeps closedness and assignments only -/

set_option maxHeartbeats 2000000 in
/-- **`t → t'`**: the let-closed transition is read-closed over its own inputs and assignments only. `K = 0`:
`t' = t`. `K ≠ 0`: the order is `closeLets`' own `assignmentOrderCheck`; every read of the closed body is an
input port left, or a name the closed body drives (the `let` ports by their aliases, `alias_placed`). -/
theorem closeLets_closed {K : Nat} {t t' : Sparkle.IR.AST.Module}
    (hcl : closeLets K t = some t')
    (hclosed : readsClosedB (t.inputs.map (·.name)) t.body = true)
    (hassign : ∀ stmt ∈ t.body, ∃ l r, stmt = Stmt.assign l r) :
    readsClosedB (t'.inputs.map (·.name)) t'.body = true ∧
      (∀ stmt ∈ t'.body, ∃ l r, stmt = Stmt.assign l r) := by
  by_cases hK : K = 0
  · subst hK
    have ht : t' = t := by
      unfold closeLets at hcl
      simpa using hcl.symm
    subst ht
    exact ⟨hclosed, hassign⟩
  obtain ⟨w, al, core, hpw, hops, ht', hord⟩ := Tools.ShippingCallsParent.closeLets_eq hK hcl
  have hti : t'.inputs = t.inputs.take (t.inputs.length - K) := by rw [ht']
  have htb : t'.body = Tools.ShippingCloseLetsSplit.closedBody t al core := by rw [ht']
  clear ht'
  have hacy : Tools.ShippingSettledSoundness.Acyclic (Tools.ShippingCloseLetsSplit.closedBody t al core) :=
    (Tools.ShippingSettledSoundness.assignmentOrderCheck_iff _).mp hord
  rw [hti, htb]
  unfold Tools.ShippingCloseLetsSplit.closedBody at hacy ⊢
  have hsplit := slc_packed_split hpw
  obtain ⟨hchain, hal⟩ := Tools.ShippingMachineClose.letOperands_chain _ w hops
  generalize hBdef : t.body.dropLast = B at hacy hsplit ⊢
  have hB : ∀ st ∈ B, ∃ l r, st = Stmt.assign l r := fun st hs =>
    hassign st (by rw [hsplit]; exact List.mem_append_left _ hs)
  -- every name the transition could read: an input port left, or driven by the closed body
  have hinT : ∀ n, (n ∈ t.inputs.map (·.name) ∨ n ∈ writesOf t.body) →
      n ∈ (t.inputs.take (t.inputs.length - K)).map (·.name) ∨
        n ∈ writesOf ((frontAliases al B ++ insertAliases al B) ++ [Stmt.assign "out" (Expr.ref core)]) := by
    intro n hn
    rcases hn with hn | hn
    · have hsp : t.inputs.map (·.name) = (t.inputs.take (t.inputs.length - K)).map (·.name) ++
          (t.inputs.drop (t.inputs.length - K)).map (·.name) := by
        rw [← List.map_append, List.take_append_drop]
      rw [hsp] at hn
      rcases List.mem_append.mp hn with h | h
      · exact Or.inl h
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        rw [← hal] at hp
        obtain ⟨pa, hpa, rfl⟩ := List.mem_map.mp hp
        have hm : aliasStmt pa.1 pa.2 ∈ frontAliases al B ++ insertAliases al B :=
          Tools.ShippingMachineClose.alias_placed hpa hB
        exact Or.inr (slc_mem_writes (List.mem_append_left _ hm) (by simp [aliasStmt, stmtWrites]))
    · obtain ⟨st, hst, hw⟩ := slc_of_mem_writes hn
      rw [hsplit] at hst
      rcases List.mem_append.mp hst with hst | hst
      · exact Or.inr (slc_mem_writes
          (List.mem_append_left _ (List.mem_append_right _
            (Tools.ShippingMachineClose.insertAliases_keeps hst))) hw)
      · have hst' : st = Stmt.assign "out" (Expr.ref w) := List.mem_singleton.mp hst
        subst hst'
        have hnout : n = "out" := by simpa [stmtWrites] using hw
        subst hnout
        exact Or.inr (slc_mem_writes (List.mem_append_right _ (List.mem_singleton.mpr rfl))
          (by simp [stmtWrites]))
  have hreadT : ∀ st ∈ t.body, ∀ n ∈ stmtReads st,
      n ∈ (t.inputs.take (t.inputs.length - K)).map (·.name) ∨
        n ∈ writesOf ((frontAliases al B ++ insertAliases al B) ++ [Stmt.assign "out" (Expr.ref core)]) :=
    fun st hs n hn => hinT n (Tools.ShippingMachineChildComb.reads_of_closed _ _ hclosed st hs n hn)
  -- the operand of every alias is read by a concatenation of the transition
  have hreadAlias : ∀ pa ∈ al, pa.2 ∈ (t.inputs.take (t.inputs.length - K)).map (·.name) ∨
      pa.2 ∈ writesOf ((frontAliases al B ++ insertAliases al B) ++ [Stmt.assign "out" (Expr.ref core)]) := by
    intro pa hpa
    obtain ⟨x, b, hm⟩ := slc_chain_operand hchain pa hpa
    exact hreadT _ hm pa.2 (by simp [stmtReads, refsOf, refsOf.refsList])
  -- the remaining wire is read by the transition: by a concatenation, or (no `let` port) by `out`
  have hreadCore : core ∈ (t.inputs.take (t.inputs.length - K)).map (·.name) ∨
      core ∈ writesOf ((frontAliases al B ++ insertAliases al B) ++ [Stmt.assign "out" (Expr.ref core)]) := by
    by_cases hne : t.inputs.drop (t.inputs.length - K) = []
    · rw [hne] at hops
      simp only [letOperands, Option.some.injEq, Prod.mk.injEq] at hops
      obtain ⟨-, hcw⟩ := hops
      have hmem := hreadT (Stmt.assign "out" (Expr.ref w))
        (by rw [hsplit]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)) w
        (by simp [stmtReads, refsOf])
      rw [hcw] at hmem
      exact hmem
    · obtain ⟨x, a, hcp⟩ := Tools.ShippingMachineChildComb.letOperands_core _ w hne hops
      exact hreadT _ (Tools.ShippingMachineClose.concatParts?_mem hcp) core
        (by simp [stmtReads, refsOf, refsOf.refsList])
  refine ⟨Tools.ShippingMachineChildComb.closed_of_acyclic hacy _ ?_, slc_assign_of_acyclic hacy⟩
  intro st hs n hn
  have halias : ∀ pa ∈ al, st = aliasStmt pa.1 pa.2 → n = pa.2 := by
    intro pa _ he
    subst he
    simpa [aliasStmt, stmtReads, refsOf] using hn
  rcases List.mem_append.mp hs with h | h
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨pa, hpa, he⟩ := Tools.ShippingMachineClose.mem_frontAliases h
      rw [halias pa hpa he]
      exact hreadAlias pa hpa
    · rcases Tools.ShippingMachineClose.mem_insertAliases h with h | ⟨pa, hpa, he⟩
      · exact hreadT st (by rw [hsplit]; exact List.mem_append_left _ h) n hn
      · rw [halias pa hpa he]
        exact hreadAlias pa hpa
  · have hst : st = Stmt.assign "out" (Expr.ref core) := List.mem_singleton.mp h
    subst hst
    have hnc : n = core := by simpa [stmtReads, refsOf] using hn
    rw [hnc]
    exact hreadCore

/-! ## `closeMachine` without slots keeps closedness and assignments only -/

set_option maxHeartbeats 1000000 in
/-- **`t' → closeMachine lay t'`** (`slots = []`). Without a packed wire the module is `t'`; with one, `w`, the
inputs are `t'`'s and the body is `t'.body.dropLast ++ outAssigns w lay.outs`: the prefix is closed, `w` is an
input or driven by the prefix (it is read by the dropped `assign out = w`), and every out assignment reads `w`
only. Any `lay.outs`. -/
theorem closeMachine_slotless_closed {lay : Layout} {t' : Sparkle.IR.AST.Module} (hslots : lay.slots = [])
    (hclosed : readsClosedB (t'.inputs.map (·.name)) t'.body = true)
    (hassign : ∀ stmt ∈ t'.body, ∃ l r, stmt = Stmt.assign l r) :
    readsClosedB ((closeMachine lay t').inputs.map (·.name)) (closeMachine lay t').body = true ∧
      (∀ stmt ∈ (closeMachine lay t').body, ∃ l r, stmt = Stmt.assign l r) := by
  cases hp : packedWire? t'.body with
  | none =>
    have hM : closeMachine lay t' = t' := by
      unfold closeMachine
      simp only [hp]
    rw [hM]
    exact ⟨hclosed, hassign⟩
  | some w =>
    have hMi : (closeMachine lay t').inputs = t'.inputs := by
      unfold closeMachine
      simp only [hp, hslots, List.length_nil, Nat.sub_zero, List.isEmpty_nil, ↓reduceIte,
        List.append_nil, List.take_length]
    have hMb : (closeMachine lay t').body = t'.body.dropLast ++ outAssigns w lay.outs := by
      unfold closeMachine
      simp only [hp, hslots, Tools.ShippingMachineChildComb.nextAssigns_nil,
        Tools.ShippingMachineChildComb.registers_nil, List.append_nil]
    have hsplit := slc_packed_split hp
    have hpre : readsClosedB (t'.inputs.map (·.name)) t'.body.dropLast = true ∧
        readsClosedB (t'.inputs.map (·.name) ++ writesOf t'.body.dropLast)
          [Stmt.assign "out" (Expr.ref w)] = true := by
      have h := hclosed
      rw [hsplit, Tools.ShippingHarnessClosed.readsClosedB_append] at h
      exact (Bool.and_eq_true _ _).mp h
    have hw : w ∈ t'.inputs.map (·.name) ++ writesOf t'.body.dropLast :=
      slc_head_reads hpre.2 w (by simp [stmtReads, refsOf])
    have hout : ∀ st ∈ outAssigns w lay.outs, ∀ n ∈ stmtReads st,
        n ∈ t'.inputs.map (·.name) ++ writesOf t'.body.dropLast := by
      intro st hs n hn
      simp only [outAssigns, List.mem_map] at hs
      obtain ⟨o, _, rfl⟩ := hs
      have hnw : n = w := by simpa [stmtReads, fieldRhs, refsOf] using hn
      rw [hnw]
      exact hw
    refine ⟨?_, ?_⟩
    · rw [hMi, hMb, Tools.ShippingHarnessClosed.readsClosedB_append]
      exact (Bool.and_eq_true _ _).mpr
        ⟨hpre.1, Tools.ShippingLeafOneOut.readsClosedB_of_all _ _ hout⟩
    · rw [hMb]
      intro st hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hassign st (by rw [hsplit]; exact List.mem_append_left _ hs)
      · simp only [outAssigns, List.mem_map] at hs
        obtain ⟨o, _, rfl⟩ := hs
        exact ⟨_, _, rfl⟩

/-! ## §1: the pure lemma -/

set_option maxHeartbeats 1000000 in
/-- **S2-c pure lemma** (STEP_S2C_FREEZE.md §1, type verbatim). -/
theorem slotless_closed_full {t t' M b : Sparkle.IR.AST.Module} {lay : Layout} {K : Nat}
    (hcl : closeLets K t = some t')
    (hclosed : readsClosedB (t.inputs.map (·.name)) t.body = true)
    (hassign : ∀ stmt ∈ t.body, ∃ l r, stmt = Stmt.assign l r)
    (hslots : lay.slots = [])
    (hM : M = closeMachine lay t')
    (hzb : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body = M.body)
    (hzi : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).inputs = M.inputs)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)) :
    readsClosedB (b.inputs.map (·.name)) b.body = true ∧ b.body.all Sparkle.IR.RegDedup.isAssign = true := by
  obtain ⟨h1, h2⟩ := closeLets_closed hcl hclosed hassign
  obtain ⟨hMc, hMa⟩ := closeMachine_slotless_closed (lay := lay) hslots h1 h2
  rw [← hM] at hMc hMa
  have hZc : readsClosedB ((Sparkle.IR.ZeroWidth.dropZeroWidthModule M).inputs.map (·.name))
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body = true := by
    rw [hzb, hzi]
    exact hMc
  have hZa : (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).body.all Sparkle.IR.RegDedup.isAssign = true := by
    rw [hzb]
    exact slc_all_isAssign hMa
  rcases hpost with rfl | rfl
  · exact ⟨hZc, hZa⟩
  · obtain ⟨mi, -, -⟩ :=
      Sparkle.IR.RefineCheck.mergeChecked_ports (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)
    obtain ⟨mc, -⟩ := Tools.ShippingMergeClosed.mergeChecked_closed
      (S := (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).inputs.map (·.name)) hZa hZc
    refine ⟨by rw [mi]; exact mc, ?_⟩
    rw [Tools.ShippingCombKidText.mergeChecked_assign hZa]
    exact Tools.ShippingLeafOneOut.mergeDuplicates_assign hZa

end Pure

/-! ## §2: the run-level supplier (A boundary) -/

section Run
open Lean hiding Module Expr
open Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildBndCore (cv dv)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 2000000 in
/-- **S2-c run-level supplier** (STEP_S2C_FREEZE.md §2, type verbatim): steps 1-7 on the one run `ran`. -/
theorem slotless_closed_ofRun (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld}
    {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : LeafDataOk p) (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D) :
    readsClosedB (b.inputs.map (·.name)) b.body = true ∧ b.body.all Sparkle.IR.RegDedup.isAssign = true := by
  obtain ⟨_, _, _, houtTy⟩ := hdata.rows
  -- step 6: the cleanup identity, from the `MachineWired` conjunct of the trace of this run
  have hL := (Pkg.trace L.O L.T hA p ran).toLB
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hclean, _⟩ := wired
  obtain ⟨⟨hzb, _, hzi, _⟩, _⟩ := hclean hnoI houtTy
  -- step 1: the successful machine synthesis of `ran` (the `none` result is excluded by `ran` itself)
  obtain ⟨tenv, bb, w9, w10, hrun9, _⟩ := ran
  -- step 2: the closing facts
  obtain ⟨t, t', d₀, run, hcl, hMeq, _⟩ :=
    Tools.ShippingCallWidthsChildRealA.synthesizeMachineCertified_leaf_runs hnoI hrun9
  -- step 4: binder facts from `ok`
  have ok := Pkg.ok p
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨_, _, positive, _, _, _, _, _, hwf, hb, hv,
    _, _, _, _, _, _, _, _, _, _, _⟩ := ok
  have hposv : Tools.ShippingMixedEntrySoundness.PositiveBinders p.d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < p.d.kb → ∃ name, p.d.shape.binders[p.d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : p.d.shape.binders[p.d.bpos j]? with
    | none => rw [h] at this; cases this
    | some pr =>
      obtain ⟨name, k⟩ := pr
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < p.d.kv → ∃ name,
      p.d.shape.binders[p.d.vpos j]? = some (name, .bits (p.d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : p.d.shape.binders[p.d.vpos j]? with
    | none => rw [h] at this; cases this
    | some pr =>
      obtain ⟨name, k⟩ := pr
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  -- step 3: the translator run
  obtain ⟨ids', cache', returned, st, nd, len, hrun, hm, _, nameLegal⟩ :=
    Tools.ShippingMixedEntrySoundness.synthesizeMixedCertified_returns run
  -- step 5: closedness of the transition module (both package kinds, via `Pkg.body_eq`)
  obtain ⟨hclosed, hassign, -, -, -, -⟩ :=
    Tools.ShippingTransitionClosed.transition_closed nd len hrun hm nameLegal hposv p.d.packed hwf hb' hv'
      (Pkg.body_eq p)
  -- step 7: assembly
  exact slotless_closed_full hcl hclosed hassign hsl0 hMeq hzb hzi hpost

end Run

end Tools.ShippingGen2
