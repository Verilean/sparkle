import Tools.ShippingClosedKinds

/-! # The closed machine's outputs are masked (G1, branch `fix/merge-guards`)

`Sparkle.IR.RefineCheck.outMaskedB we body p`: the port `p` is written
exactly once in `body`, by a constant or a slice no wider than the port.

* `outMaskedB_closed`: on a body `A ++ (N ++ (R ++ outAssigns w outs))` with
  `Acyclic (A ++ (N ++ outAssigns w outs))` and `R` registers, every output
  field of positive width whose type has that width is masked — the single
  writer from `Acyclic.nodup` (registers write nothing), the right-hand side
  `fieldRhs w lo width`, a slice of width `width`.
* `closedBody_masked`, `closedBody_masked_of_run`: the same on the closed
  machine of a real harness run. Their statements' hypotheses and their
  proofs up to `closeMachine_body` are COPIED by a script from
  `Tools/ShippingClosedKinds.lean` (`closedBody_kinds`,
  `closedBody_kinds_of_run`), which conclude only the statement kinds; the
  originals are not changed. If they change, these copies do not follow.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingClosedMasked
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingSettledSoundness (Acyclic)
open Tools.ShippingTopoBody Tools.ShippingTopoChecks Tools.ShippingTopoLinked
open Tools.ShippingCloseInstsSome Tools.ShippingCloseChecks Tools.ShippingCloseMachineFacts
open Tools.ShippingInstStmt Tools.ShippingGateChildComb Tools.ShippingKidsComb
open Tools.ShippingCallsParent Tools.ShippingCallsStmts Tools.ShippingDesignWith
open Tools.ShippingRankRun Tools.ShippingRankNames Tools.ShippingCallsRank
open Tools.ShippingClosedOrder Tools.ShippingMachineCloses
open Tools.ShippingCloseLetsSplit (closedBody)
open Tools.ShippingMachineClose (concatParts?_mem mem_frontAliases mem_insertAliases)
open Tools.ShippingCallsAssembly
open Sparkle.IR.OptCheck (seqStmtOk)
open Tools.ShippingClosedKinds

theorem and2 {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  subst ha
  subst hb
  rfl

theorem and3 {a b c : Bool} (ha : a = true) (hb : b = true) (hc : c = true) :
    (a && b && c) = true := by
  subst ha
  subst hb
  subst hc
  rfl

/-- **The outputs of a closed body are masked.** -/
theorem outMaskedB_closed {A N R : List Stmt} {w : String} {outs : List OutField}
    (we : Sparkle.IR.Semantics.WEnv)
    (hacy : Acyclic (A ++ (N ++ outAssigns w outs)))
    (hR : ∀ st ∈ R, isReg st = true)
    {o : OutField} (ho : o ∈ outs) (hpos : 0 < o.width) (hty : o.ty.bitWidth = o.width) :
    Sparkle.IR.RefineCheck.outMaskedB we (A ++ (N ++ (R ++ outAssigns w outs)))
      { name := o.name, ty := o.ty } = true := by
  have hRw : writesOf R = [] := by
    unfold writesOf
    rw [List.flatMap_eq_nil_iff]
    intro st hs
    have hreg := hR st hs
    cases st <;> first | rfl | (simp [isReg] at hreg)
  have e1 : writesOf (R ++ outAssigns w outs) = writesOf (outAssigns w outs) :=
    (Sparkle.IR.Reorder.writesOf_append R (outAssigns w outs)).trans
      ((congrArg (fun l => l ++ writesOf (outAssigns w outs)) hRw).trans (List.nil_append _))
  have hW : writesOf (A ++ (N ++ (R ++ outAssigns w outs))) =
      writesOf (A ++ (N ++ outAssigns w outs)) :=
    (Sparkle.IR.Reorder.writesOf_append A _).trans
      ((congrArg (fun l => writesOf A ++ l)
        ((Sparkle.IR.Reorder.writesOf_append N _).trans
          ((congrArg (fun l => writesOf N ++ l) e1).trans (Sparkle.IR.Reorder.writesOf_append N _).symm))).trans
        (Sparkle.IR.Reorder.writesOf_append A _).symm)
  have hnd := Acyclic.nodup hacy
  have hmemO : o.name ∈ writesOf (outAssigns w outs) := by
    rw [writesOf_outAssigns]
    exact List.mem_map.mpr ⟨o, ho, rfl⟩
  have hmem : o.name ∈ writesOf (A ++ (N ++ outAssigns w outs)) := by
    rw [Sparkle.IR.Reorder.writesOf_append A, Sparkle.IR.Reorder.writesOf_append N]
    exact List.mem_append_right _ (List.mem_append_right _ hmemO)
  have hcount : (writesOf (A ++ (N ++ (R ++ outAssigns w outs)))).count o.name = 1 := by
    rw [hW, List.Nodup.count hnd, if_pos hmem]
  have hst : Stmt.assign o.name (fieldRhs w o.lo o.width) ∈
      A ++ (N ++ (R ++ outAssigns w outs)) :=
    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_map.mpr ⟨o, ho, rfl⟩)))
  have hwid : (o.lo + o.width - 1) - o.lo + 1 ≤ o.ty.bitWidth := by omega
  unfold Sparkle.IR.RefineCheck.outMaskedB
  refine and2 (beq_iff_eq.mpr hcount) (List.any_eq_true.mpr ⟨_, hst, ?_⟩)
  show (o.name == o.name && Sparkle.IR.RefineCheck.maskedRhs (fieldRhs w o.lo o.width) &&
    decide (Sparkle.IR.Semantics.widthOf we (fieldRhs w o.lo o.width) ≤ o.ty.bitWidth)) = true
  exact and3 (beq_self_eq_true _) rfl (decide_eq_true hwid)

set_option maxHeartbeats 4000000 in
/-- `closedBody_kinds`, concluding the masked outputs (copied; see the header). -/
theorem closedBody_masked {P : String → Prop} {bnd : Lean.FVarId → Option String}
    {t t' : Module} {lay : Layout} {bodyB : List Stmt} {w : String}
    {PI ls : List Port} {kI n K : Nat} {cs : List Nat}
    (hcl : closeLets K t = some t')
    (hin : t.inputs = PI ++ ls) (hlsLen : ls.length = kI + n + K)
    (hnd : (t.inputs.map (·.name)).Nodup) (hinW : ∀ p ∈ t.inputs, p ∈ t.wires)
    (hwAlloc : ∀ p ∈ t.wires, Allocated p.name)
    (hbody : t.body = bodyB.reverse ++ [.assign "out" (.ref w)]) (hacy : Acyclic t.body)
    (hnamed : ∀ l r, Stmt.assign l r ∈ bodyB.reverse → Allocated l ∧ ∀ x ∈ refsOf r, Allocated x)
    (hnw : ∀ l r, Stmt.assign l r ∈ bodyB → ¬ P l) (hP : ∀ p ∈ t.inputs, P p.name)
    (hF : ∀ (al : List (Port × String)) (core : String),
      letOperands t.body (t.inputs.drop (t.inputs.length - K)) w = some (al, core) →
      ∃ es ws, Facts P bnd
        (fun i x => ∀ (idx : Nat) (p : Port), ls[idx]? = some p → x = p.name → okRule kI n cs i idx)
        t.wires t.body bodyB 0 al es ws ∧ al.map (·.1) = ls.drop (kI + n) ∧ Allocated core)
    (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (lay.outs.map (·.name)).Nodup) :
    ∀ (we : Sparkle.IR.Semantics.WEnv) (o : OutField), o ∈ lay.outs → o.ty.bitWidth = o.width →
      Sparkle.IR.RefineCheck.outMaskedB we (closeMachine lay t').body
        { name := o.name, ty := o.ty } = true := by
  obtain ⟨w0, al, core, hpw, hops, ht', hord⟩ := closeLets_eq' hbody hacy hcl
  have hti : t'.inputs = t.inputs.take (t.inputs.length - K) := by rw [ht']
  have htw : t'.wires = t.wires := by rw [ht']
  have htn : t'.name = t.name := by rw [ht']
  have htb : t'.body = closedBody t al core := by rw [ht']
  clear ht'
  have hpw' : packedWire? t.body = some w := by simp [packedWire?, hbody]
  rw [hpw'] at hpw
  cases hpw
  obtain ⟨es, ws, hfacts, hal, hcoreA⟩ := hF al core hops
  have hT : Acyclic bodyB.reverse := Acyclic.prefix (hbody ▸ hacy)
  have hKal : al.length = K := by
    have := congrArg List.length hal
    simp only [List.length_map, List.length_drop] at this
    omega
  have hdrop : t.body.dropLast = bodyB.reverse := by simp [hbody]
  -- the ports
  have hlsMem : ∀ p ∈ ls, p ∈ t.inputs := fun p hp => hin ▸ List.mem_append_right _ hp
  have hlsNd : (ls.map (·.name)).Nodup := by
    rw [hin, List.map_append] at hnd
    exact (List.nodup_append.mp hnd).2.1
  have hlsAlloc : ∀ p ∈ ls, Allocated p.name := fun p hp => hwAlloc p (hinW p (hlsMem p hp))
  have hPls : ∀ p ∈ ls, P p.name := fun p hp => hP p (hlsMem p hp)
  have notDriven : ∀ x, P x → x ∉ writesOf bodyB.reverse := by
    intro x hp hw
    obtain ⟨r, hr⟩ := mem_of_writes hT hw
    exact hnw x r (List.mem_reverse.mp hr) hp
  have hletEq : al.map (·.1.name) = (ls.drop (kI + n)).map (·.name) := by
    rw [← hal, List.map_map]
    rfl
  have letAt : ∀ (a : Nat) (p : Port), ls[kI + n + a]? = some p →
      (al.map (·.1.name))[a]? = some p.name ∧ ∃ pa ∈ al, pa.1 = p := by
    intro a p hp
    refine ⟨by rw [hletEq, List.getElem?_map, List.getElem?_drop, hp]; rfl, ?_⟩
    have : (al.map (·.1))[a]? = some p := by rw [hal, List.getElem?_drop, hp]
    rw [List.getElem?_map] at this
    cases hpa : al[a]? with
    | none => rw [hpa] at this; cases this
    | some pa =>
      rw [hpa] at this
      exact ⟨pa, List.mem_of_getElem? hpa, by simpa using this⟩
  -- the let-closed transition and the closed machine
  have hbody' : t'.body =
      (frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        [.assign "out" (.ref core)] := by
    rw [htb]
    unfold closedBody
    rw [hdrop]
  have halP : ∀ pa ∈ al, pa.1 ∈ ls := fun pa hpa =>
    List.mem_of_mem_drop (hal ▸ List.mem_map_of_mem hpa)
  obtain ⟨pres0, _, hall0⟩ := facts_pres al es ws 0 hfacts
  have halloc2 : ∀ pa ∈ al, Allocated pa.2 := by
    intro pa hpa
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hpa
    obtain ⟨pre, _, _, _, _, _, x', b', hcp⟩ := hall0 a pa ha
    have hm := concatParts?_mem hcp
    rw [hbody] at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact (hnamed _ _ hm).2 pa.2 (by simp [refsOf, refsOf.refsList])
    · simp at hm
  have named' : ∀ l r, Stmt.assign l r ∈
      frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse →
      Allocated l ∧ ∀ x ∈ refsOf r, Allocated x := by
    intro l r hm
    have alias : ∀ pa ∈ al, Stmt.assign l r = aliasStmt pa.1 pa.2 →
        Allocated l ∧ ∀ x ∈ refsOf r, Allocated x := by
      intro pa hpa he
      unfold aliasStmt at he
      cases he
      refine ⟨hlsAlloc _ (halP pa hpa), fun x hx => ?_⟩
      have : x = pa.2 := by simpa [refsOf] using hx
      exact this ▸ halloc2 pa hpa
    rcases List.mem_append.mp hm with h | h
    · obtain ⟨pa, hpa, he⟩ := mem_frontAliases h
      exact alias pa hpa he
    · rcases mem_insertAliases h with h | ⟨pa, hpa, he⟩
      · exact hnamed l r h
      · exact alias pa hpa he
  obtain ⟨ps, hps, hMbody, hMacy, hR, psNd⟩ := closeMachine_body (lay := lay) hbody'
    (by rw [htb]; exact (Tools.ShippingSettledSoundness.assignmentOrderCheck_iff _).mp hord)
    named' hcoreA
    (by
      rw [hti, List.map_take]
      exact hnd.sublist (List.take_sublist _ _)) outsOk outsNodup
  intro we o ho hty
  rw [hMbody]
  exact outMaskedB_closed we hMacy hR ho (outsOk o ho).1 hty

open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun
open Tools.ShippingChildInv
open Tools.ShippingCallsGate
set_option maxHeartbeats 2000000 in
/-- **On a real harness run**: every output port of the closed machine is
assigned once, by a slice of the packed wire of the port's width. -/
theorem closedBody_masked_of_run {declName : Lean.Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    {logProf : String → IO Unit} {t t' : Sparkle.IR.AST.Module} {d₀ : Design}
    (run : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      d.shape.binders d.shape.body) (t, d₀))
    (hcl : closeLets d.shape.layout.lets t = some t') :
    ∀ (we : Sparkle.IR.Semantics.WEnv) (o : OutField), o ∈ d.shape.layout.outs →
      o.ty.bitWidth = o.width →
      Sparkle.IR.RefineCheck.outMaskedB we (closeMachine d.shape.layout t').body
        { name := o.name, ty := o.ty } = true := by
  simp only [MachineData.callsOk, Bool.and_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨hnIn, hargs⟩, hfields⟩, hcoreR⟩ := hC
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, _, _, _, outsOk, outsNodup, hwf, hb, hv,
    _, _, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  obtain ⟨hfitL, -⟩ := scoped_fit d.letBs d.letFields _ hscoped
  have hlsLen : d.letFields.length = d.ls.length := by simp [MachineData.letFields]
  have hletBs : d.letBs.length = d.shape.binders.length - (d.nIn + d.ss.length) := by
    simp [MachineData.letBs]
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  have hA : (d.shape.binders.take nDecl).length = nDecl := by
    rw [List.length_take]
    omega
  have hsplit : d.shape.binders = d.shape.binders.take nDecl ++ d.shape.binders.drop nDecl :=
    (List.take_append_drop ..).symm
  have hBlen : (d.shape.binders.drop nDecl).length =
      d.shape.insts.length + d.ss.length + d.letBs.length := by
    rw [List.length_drop]
    omega
  have hcoreWF := core_wf d.core.2 d.letFields hwf
  obtain ⟨PI, ls, bodyB, w, P, bnd, hin, hPI, hlsL, hndI, hinW, hwAlloc, hbodyT, hacy, hnamed, hnw,
      hP, hF, hdes, hname⟩ :=
    transition_calls_facts (cs := d.callBounds) nd len hrun hm nameLegal hposv d.letFields d.core.2
      hwf hb' hv' hbody hsplit hdomB hBlen hfitL
      (by rw [hA]; exact fieldsOK_of_B d.letFields 0 d.core.2 hfields hwf)
      (by
        rw [hA, hlsLen]
        exact uses_of_reads (fun j hj hr => ⟨hj, posOk_rule hr⟩)
          (fun j hj hr => ⟨hj, posOk_rule hr⟩) d.core.2 hcoreWF hcoreR)
  rw [hlets] at hcl
  exact closedBody_masked (cs := d.callBounds) (lay := d.shape.layout) hcl hin hlsL
    hndI hinW hwAlloc hbodyT hacy hnamed hnw hP hF outsOk outsNodup

end Tools.ShippingClosedMasked
