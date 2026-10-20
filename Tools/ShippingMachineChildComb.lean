import Tools.ShippingCallsAssembly

/-! # A slotless machine child is combinational and closed

A machine-route child WITHOUT registers and without calls (a combinational
body with hardware `let`s, e.g. `pickByteH`) is compiled by the machine
route: the harness' transition, `closeLets`, `closeMachine`. Here: that
module has the child-side facts of the one-output closing (`ChildComb`) —
assignments only, every read an input port or a name driven EARLIER, one
output `out`, driven, distinct allocated input names.

* `reads_of_closed`: a read-closed body reads inputs or names it drives;
* `closed_of_acyclic`: an acyclic body (single assignment, no read of a name
  driven later or by the statement itself) ALL of whose reads are inputs or
  names it drives is read-closed in order. Acyclicity alone does not give
  this (a read of an undefined name is acyclic): the membership of every read
  is a separate premise, derived below from the transition's own closure;
* `slotless_childComb`: the assembly — `closeLets`' success gives the order
  (`assignmentOrderCheck`, its own check), the transition's closure
  (`transition_closed`) gives the membership of the original reads, the alias
  statements drive the `let` ports and read operand wires the packed
  concatenations read. -/
namespace Tools.ShippingMachineChildComb
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingSettledSoundness (Acyclic)
open Tools.ShippingCloseMachineFacts Tools.ShippingGateChildComb
open Tools.ShippingCallsParent Tools.ShippingCallsAssembly
open Tools.ShippingRankRun
open Tools.ShippingClosedOrder Tools.ShippingMachineCloses
open Tools.ShippingCloseLetsSplit (closedBody)
open Tools.ShippingMachineClose (concatParts?_mem mem_frontAliases mem_insertAliases)

/-- A read-closed body reads names of `S` or names it drives. -/
theorem reads_of_closed : ∀ (body : List Stmt) (S : List String), readsClosedB S body = true →
    ∀ st ∈ body, ∀ n ∈ stmtReads st, n ∈ S ∨ n ∈ writesOf body
  | [], _, _, _, hs, _, _ => by simp at hs
  | st0 :: rest, S, h, st, hs, n, hn => by
    simp only [readsClosedB, Bool.and_eq_true, List.all_eq_true] at h
    have hw : writesOf (st0 :: rest) = stmtWrites st0 ++ writesOf rest := rfl
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Or.inl (by simpa using h.1 n hn)
    · rcases reads_of_closed rest _ h.2 st hs n hn with h1 | h1
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (by rw [hw]; exact List.mem_append_left _ h2)
      · exact Or.inr (by rw [hw]; exact List.mem_append_right _ h1)

/-- **An acyclic body whose reads are all inputs or names it drives is
read-closed, in its order.** -/
theorem closed_of_acyclic {body : List Stmt} (hacy : Acyclic body) :
    ∀ (S : List String), (∀ st ∈ body, ∀ n ∈ stmtReads st, n ∈ S ∨ n ∈ writesOf body) →
      readsClosedB S body = true := by
  induction hacy with
  | nil => intro S _; rfl
  | @cons l r rest ht hr _ ih =>
    intro S h
    have hw : ∀ n, n ∈ writesOf (Stmt.assign l r :: rest) → n = l ∨ n ∈ writesOf rest := by
      intro n hn
      have : writesOf (Stmt.assign l r :: rest) = l :: writesOf rest := rfl
      rw [this] at hn
      exact List.mem_cons.mp hn
    simp only [readsClosedB, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun n hn => ?_, ih _ ?_⟩
    · rcases h _ (List.mem_cons_self ..) n hn with hS | hW
      · simpa using hS
      · rcases hw n hW with e | e
        · exact absurd e (hr n hn).1
        · exact absurd e (hr n hn).2
    · intro st hs n hn
      rcases h st (List.mem_cons_of_mem _ hs) n hn with hS | hW
      · exact Or.inl (List.mem_append_left _ hS)
      · rcases hw n hW with e | e
        · exact Or.inl (List.mem_append_right _ (by simp [stmtWrites, e]))
        · exact Or.inr e

/-- With a `let`, the core wire is the low part of a packed concatenation. -/
theorem letOperands_core {body : List Stmt} :
    ∀ (ps : List Port) (w : String) {al : List (Port × String)} {core : String}, ps ≠ [] →
      letOperands body ps w = some (al, core) → ∃ x a, concatParts? body x = some (a, core)
  | [], _, _, _, h, _ => absurd rfl h
  | p :: ps, w, al, core, _, h => by
    simp only [letOperands] at h
    cases hc : concatParts? body w with
    | none => rw [hc] at h; cases h
    | some ab =>
      obtain ⟨a, b⟩ := ab
      rw [hc] at h
      dsimp only at h
      cases hl : letOperands body ps b with
      | none => rw [hl] at h; cases h
      | some rc =>
        obtain ⟨rest, c⟩ := rc
        rw [hl] at h
        cases h
        by_cases hps : ps = []
        · subst hps
          simp only [letOperands, Option.some.injEq, Prod.mk.injEq] at hl
          exact ⟨w, a, by rw [hc, hl.2]⟩
        · exact letOperands_core ps b hps hl

theorem mem_insert_of_mem (al : List (Port × String)) :
    ∀ {B : List Stmt} {s : Stmt}, s ∈ B → s ∈ insertAliases al B
  | st :: rest, s, h => by
    simp only [insertAliases, List.mem_cons, List.mem_append]
    rcases List.mem_cons.mp h with e | h
    · exact Or.inl e
    · exact Or.inr (Or.inr (mem_insert_of_mem al h))

theorem nextAssigns_nil (w : String) : ∀ (ps : List Port), nextAssigns w ps [] = []
  | [] => rfl
  | _ :: _ => rfl

theorem registers_nil (rk : Sparkle.IR.Type.ResetKind) : ∀ (ps : List Port), registers rk ps [] = []
  | [] => rfl
  | _ :: _ => rfl

set_option maxHeartbeats 2000000 in
/-- **The slotless machine child's module**, from the facts of its
transition's run and the success of `closeLets`. -/
theorem slotless_childComb {P : String → Prop} {bnd : Lean.FVarId → Option String}
    {Vk : Nat → String → Prop}
    {t t' : Module} {lay : Layout} {bodyB : List Stmt} {w : String}
    {PI ls : List Port} {K : Nat}
    (hK : K ≠ 0) (hcl : closeLets K t = some t')
    (hin : t.inputs = PI ++ ls) (hlsLen : ls.length = K)
    (hnd : (t.inputs.map (·.name)).Nodup) (hinW : ∀ p ∈ t.inputs, p ∈ t.wires)
    (hwAlloc : ∀ p ∈ t.wires, Allocated p.name)
    (hbody : t.body = bodyB.reverse ++ [.assign "out" (.ref w)]) (hacy : Acyclic t.body)
    (hnamed : ∀ l r, Stmt.assign l r ∈ bodyB.reverse → Allocated l ∧ ∀ x ∈ refsOf r, Allocated x)
    (hF : ∀ (al : List (Port × String)) (core : String),
      letOperands t.body (t.inputs.drop (t.inputs.length - K)) w = some (al, core) →
      ∃ es ws, Facts P bnd Vk t.wires t.body bodyB 0 al es ws ∧ al.map (·.1) = ls ∧ Allocated core)
    (hclosed : readsClosedB (t.inputs.map (·.name)) t.body = true)
    (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true)
    (hslots : lay.slots = [])
    (houts : ∃ o, lay.outs = [o] ∧ o.name = "out") :
    ChildComb (closeMachine lay t') ∧ (closeMachine lay t').inputs = PI ∧
      (closeMachine lay t').name = t.name ∧ Acyclic (closeMachine lay t').body := by
  obtain ⟨w0, al, core, hpw, hops, ht', hord⟩ := closeLets_eq hK hcl
  have hti : t'.inputs = t.inputs.take (t.inputs.length - K) := by rw [ht']
  have htn : t'.name = t.name := by rw [ht']
  have htb : t'.body = closedBody t al core := by rw [ht']
  clear ht'
  have hpw' : packedWire? t.body = some w := by simp [packedWire?, hbody]
  rw [hpw'] at hpw
  cases hpw
  obtain ⟨es, ws, hfacts, hal, hcoreA⟩ := hF al core hops
  have hT : Acyclic bodyB.reverse := Acyclic.prefix (hbody ▸ hacy)
  have hdrop : t.body.dropLast = bodyB.reverse := by simp [hbody]
  have hPI : t.inputs.take (t.inputs.length - K) = PI := by
    rw [hin, List.length_append, hlsLen, Nat.add_sub_cancel, List.take_left']
    rfl
  have hlsMem : ∀ p ∈ ls, p ∈ t.inputs := fun p hp => hin ▸ List.mem_append_right _ hp
  have hlsAlloc : ∀ p ∈ ls, Allocated p.name := fun p hp => hwAlloc p (hinW p (hlsMem p hp))
  have hbody' : t'.body =
      (frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        [.assign "out" (.ref core)] := by
    rw [htb]
    unfold closedBody
    rw [hdrop]
  have halP : ∀ pa ∈ al, pa.1 ∈ ls := fun pa hpa => hal ▸ List.mem_map_of_mem hpa
  obtain ⟨pres0, _, hall0⟩ := facts_pres al es ws 0 hfacts
  -- the operand of every alias is the high part of a packed concatenation
  have hconcat : ∀ pa ∈ al, ∃ x b, Stmt.assign x (.concat [.ref pa.2, .ref b]) ∈ t.body := by
    intro pa hpa
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hpa
    obtain ⟨pre, _, _, _, _, _, x', b', hcp⟩ := hall0 a pa ha
    exact ⟨x', b', concatParts?_mem hcp⟩
  have halloc2 : ∀ pa ∈ al, Allocated pa.2 := by
    intro pa hpa
    obtain ⟨x, b, hm⟩ := hconcat pa hpa
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
  obtain ⟨o, hlo, hon⟩ := houts
  have outsNodup : (lay.outs.map (·.name)).Nodup := by rw [hlo]; simp
  obtain ⟨ps, hps, hMbody, hMacy, -, -⟩ := closeMachine_body (lay := lay) hbody'
    (by rw [htb]; exact (Tools.ShippingSettledSoundness.assignmentOrderCheck_iff _).mp hord)
    named' hcoreA
    (by
      rw [hti, List.map_take]
      exact hnd.sublist (List.take_sublist _ _)) outsOk outsNodup
  obtain ⟨hname, -, -, -, houtsM⟩ := closeMachine_parts (lay := lay) hbody'
  rw [hslots, nextAssigns_nil, registers_nil, List.nil_append, List.nil_append] at hMbody
  rw [hslots, nextAssigns_nil, List.nil_append] at hMacy
  have hMin : (closeMachine lay t').inputs = PI := by
    have hp : packedWire? t'.body = some core := by simp [packedWire?, hbody']
    unfold closeMachine
    simp only [hp, hslots, List.length_nil, Nat.sub_zero, List.isEmpty_nil, ↓reduceIte,
      List.append_nil, List.take_length]
    rw [hti, hPI]
  -- every name the transition could read: an input port of the child, or
  -- driven by the closed body
  have hinT : ∀ n, (n ∈ t.inputs.map (·.name) ∨ n ∈ writesOf t.body) →
      n ∈ PI.map (·.name) ∨ n ∈ writesOf ((frontAliases al bodyB.reverse ++
        insertAliases al bodyB.reverse) ++ outAssigns core lay.outs) := by
    intro n hn
    rcases hn with hn | hn
    · rw [hin, List.map_append] at hn
      rcases List.mem_append.mp hn with h | h
      · exact Or.inl h
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        rw [← hal] at hp
        obtain ⟨pa, hpa, rfl⟩ := List.mem_map.mp hp
        have := alias_mem hT hpa
        exact Or.inr (mem_writes_left (mem_writes_assign (r := .slice (.ref pa.2)
          (pa.1.ty.bitWidth - 1) 0) (by simpa [aliasStmt] using this)))
    · rw [hbody, Tools.ShippingTopoChecks.writesOf_append] at hn
      rcases List.mem_append.mp hn with h | h
      · obtain ⟨r, hr⟩ := mem_of_writes hT h
        exact Or.inr (mem_writes_left (mem_writes_assign
          (List.mem_append_right _ (mem_insert_of_mem al hr))))
      · have : n = "out" := by simpa [writesOf, stmtWrites] using h
        subst this
        refine Or.inr (mem_writes_right ?_)
        rw [hlo]
        simp [outAssigns, writesOf, stmtWrites, hon]
  have hreadT : ∀ st ∈ t.body, ∀ n ∈ stmtReads st,
      n ∈ PI.map (·.name) ∨ n ∈ writesOf ((frontAliases al bodyB.reverse ++
        insertAliases al bodyB.reverse) ++ outAssigns core lay.outs) :=
    fun st hs n hn => hinT n (reads_of_closed _ _ hclosed st hs n hn)
  have hreadAlias : ∀ pa ∈ al, pa.2 ∈ PI.map (·.name) ∨ pa.2 ∈ writesOf
      ((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        outAssigns core lay.outs) := by
    intro pa hpa
    obtain ⟨x, b, hm⟩ := hconcat pa hpa
    exact hreadT _ hm pa.2 (by simp [stmtReads, refsOf, refsOf.refsList])
  have hreadCore : core ∈ PI.map (·.name) ∨ core ∈ writesOf
      ((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        outAssigns core lay.outs) := by
    obtain ⟨x, a, hcp⟩ := letOperands_core _ w (by
      intro h
      have := congrArg List.length h
      simp only [List.length_drop, List.length_nil, hin, List.length_append, hlsLen] at this
      omega) hops
    exact hreadT _ (concatParts?_mem hcp) core (by simp [stmtReads, refsOf, refsOf.refsList])
  have hclosedM : readsClosedB (PI.map (·.name))
      ((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        outAssigns core lay.outs) = true := by
    refine closed_of_acyclic hMacy _ ?_
    intro st hs n hn
    have halias : ∀ pa ∈ al, st = aliasStmt pa.1 pa.2 → n = pa.2 := by
      intro pa _ he
      subst he
      simpa [aliasStmt, stmtReads, refsOf] using hn
    rcases List.mem_append.mp hs with h | h
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨pa, hpa, he⟩ := mem_frontAliases h
        exact halias pa hpa he ▸ hreadAlias pa hpa
      · rcases mem_insertAliases h with h | ⟨pa, hpa, he⟩
        · exact hreadT st (by rw [hbody]; exact List.mem_append_left _ h) n hn
        · exact halias pa hpa he ▸ hreadAlias pa hpa
    · simp only [outAssigns, List.mem_map] at h
      obtain ⟨o', _, rfl⟩ := h
      have : n = core := by simpa [stmtReads, fieldRhs, refsOf] using hn
      exact this ▸ hreadCore
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hMin, by rw [hname, htn], by rw [hMbody]; exact hMacy⟩
  · rw [hMbody]
    exact acyclic_isAssign hMacy
  · rw [hMin, hMbody]
    exact hclosedM
  · rw [houtsM, hlo]
    exact ⟨o.ty, by simp [hon]⟩
  · rw [hMbody, hlo]
    refine mem_writes_right ?_
    simp [outAssigns, writesOf, stmtWrites, hon]
  · rw [hMin]
    rw [hin, List.map_append] at hnd
    exact (List.nodup_append.mp hnd).1
  · rw [hMin]
    intro p hp
    exact hwAlloc p (hinW p (hin ▸ List.mem_append_left _ hp))

set_option maxHeartbeats 2000000 in
/-- **The slotless machine child at the full entry**: the zero-width cleanup
changes nothing of the closed module (typed statements, positive widths:
`closeMachine_comb_cleanup`), and the checked merge keeps closure and the
driven names (`mergeChecked_closed`) — so the module the entry returns has
the child-side facts, the declaration's input ports and the transition's
name. -/
theorem slotless_childComb_full {P : String → Prop} {bnd : Lean.FVarId → Option String}
    {Vk : Nat → String → Prop}
    {t t' b : Module} {lay : Layout} {bodyB : List Stmt} {w : String}
    {PI ls : List Port} {K : Nat}
    (hK : K ≠ 0) (hcl : closeLets K t = some t')
    (hin : t.inputs = PI ++ ls) (hlsLen : ls.length = K)
    (hnd : (t.inputs.map (·.name)).Nodup) (hinW : ∀ p ∈ t.inputs, p ∈ t.wires)
    (hwAlloc : ∀ p ∈ t.wires, Allocated p.name)
    (hbody : t.body = bodyB.reverse ++ [.assign "out" (.ref w)]) (hacy : Acyclic t.body)
    (hnamed : ∀ l r, Stmt.assign l r ∈ bodyB.reverse → Allocated l ∧ ∀ x ∈ refsOf r, Allocated x)
    (hF : ∀ (al : List (Port × String)) (core : String),
      letOperands t.body (t.inputs.drop (t.inputs.length - K)) w = some (al, core) →
      ∃ es ws, Facts P bnd Vk t.wires t.body bodyB 0 al es ws ∧ al.map (·.1) = ls ∧ Allocated core)
    (hclosed : readsClosedB (t.inputs.map (·.name)) t.body = true)
    (typed : Tools.ShippingTypedPostSoundness.TypedStmts (Tools.ShippingEntrySoundness.weOf t) t.body)
    (wnd : (t.wires.map (·.name)).Nodup)
    (hwty : ∀ p ∈ t.wires, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n)
    (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outTy : ∀ o ∈ lay.outs, o.ty.bitWidth = o.width)
    (hslots : lay.slots = [])
    (houts : ∃ o, lay.outs = [o] ∧ o.name = "out")
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule (closeMachine lay t') ∨
      b = Sparkle.IR.RefineCheck.mergeChecked
        (Sparkle.IR.ZeroWidth.dropZeroWidthModule (closeMachine lay t'))) :
    ChildComb b ∧ b.inputs = PI ∧ b.name = t.name := by
  obtain ⟨hM, hMin, hMname, hMacy⟩ := slotless_childComb hK hcl hin hlsLen hnd hinW hwAlloc hbody
    hacy hnamed hF hclosed outsOk hslots houts
  obtain ⟨w0, al, core, hpw, hops, ht', hord⟩ := closeLets_eq hK hcl
  have htw : t'.wires = t.wires := by rw [ht']
  have hti : t'.inputs = t.inputs.take (t.inputs.length - K) := by rw [ht']
  have htb : t'.body = closedBody t al core := by rw [ht']
  clear ht'
  have hpw' : packedWire? t.body = some w := by simp [packedWire?, hbody]
  rw [hpw'] at hpw
  cases hpw
  obtain ⟨es, ws, hfacts, hal, -⟩ := hF al core hops
  have hdrop : t.body.dropLast = bodyB.reverse := by simp [hbody]
  have hbody' : t'.body =
      (frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        [.assign "out" (.ref core)] := by
    rw [htb]
    unfold closedBody
    rw [hdrop]
  -- the let-closed body is typed
  have hport : ∀ pa ∈ al, Tools.ShippingEntrySoundness.weOf t pa.1.name = pa.1.ty.bitWidth := by
    intro pa hpa
    have hp : pa.1 ∈ t.wires :=
      hinW _ (hin ▸ List.mem_append_right _ (hal ▸ List.mem_map_of_mem hpa))
    rw [Tools.ShippingMachineCleanup.weOf_port wnd hp]
    rcases hwty _ hp with h | ⟨n, h⟩ <;> rw [h] <;> rfl
  have hcorePos : 0 < Tools.ShippingEntrySoundness.weOf t core := by
    obtain ⟨x, a, hcp⟩ := letOperands_core _ w (by
      intro h
      have := congrArg List.length h
      simp only [List.length_drop, List.length_nil, hin, List.length_append, hlsLen] at this
      omega) hops
    obtain ⟨l', e, k, heq, hte, _⟩ := typed _ (concatParts?_mem hcp)
    cases heq
    exact hte.refs_positive core (by simp [refsOf, refsOf.refsList])
  have typed' := Tools.ShippingMachineClose.closeLets_typed hK hcl hpw' hops typed hport hcorePos
  obtain ⟨o, hlo, hon⟩ := houts
  have outsNodup : (lay.outs.map (·.name)).Nodup := by rw [hlo]; simp
  obtain ⟨dzb, -, dzi, dzo⟩ := Tools.ShippingMachineClose.closeMachine_comb_cleanup (lay := lay)
    hbody' typed' (by rw [htw]; exact hwAlloc)
    (fun p hp => by
      rw [htw]
      rw [hti] at hp
      exact hinW p (List.mem_of_mem_take hp))
    (by rw [htw]; exact wnd) outsOk outsNodup outTy hslots
  generalize closeMachine lay t' = M at hM hMin hMname hMacy dzb dzi dzo hpost
  have hZ : ChildComb (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) :=
    { assigns := by rw [dzb]; exact hM.assigns
      closed := by rw [dzb, dzi]; exact hM.closed
      output := by rw [dzo]; exact hM.output
      outDriven := by rw [dzb]; exact hM.outDriven
      inputNames := by rw [dzi]; exact hM.inputNames
      inputAlloc := by rw [dzi]; exact hM.inputAlloc }
  rcases hpost with rfl | rfl
  · exact ⟨hZ, by rw [dzi, hMin], by rw [dropZeroWidth_name, hMname]⟩
  · obtain ⟨mi, mo, _⟩ := Sparkle.IR.RefineCheck.mergeChecked_ports
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule M)
    obtain ⟨mc, mw⟩ := Tools.ShippingMergeClosed.mergeChecked_closed
      (S := (Sparkle.IR.ZeroWidth.dropZeroWidthModule M).inputs.map (·.name)) hZ.assigns hZ.closed
    refine ⟨{ assigns := ?_, closed := by rw [mi]; exact mc, output := by rw [mo]; exact hZ.output,
              outDriven := by rw [mw]; exact hZ.outDriven, inputNames := by rw [mi]; exact hZ.inputNames,
              inputAlloc := by rw [mi]; exact hZ.inputAlloc },
      by rw [mi, dzi, hMin],
      by rw [Tools.ShippingMachineDepthRun.mergeChecked_name, dropZeroWidth_name, hMname]⟩
    -- the merge of an ordered assignment-only body is ordered, so assignments
    have hmd : Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) =
        Sparkle.IR.RegDedup.mergeDuplicates (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) := by
      unfold Sparkle.IR.RefineCheck.mergeChecked
      simp only [hZ.assigns, if_true]
    rw [hmd]
    exact acyclic_isAssign (Tools.ShippingPostSoundness.mergeDuplicates_order
      (by rw [dzb]; exact hMacy))

end Tools.ShippingMachineChildComb
