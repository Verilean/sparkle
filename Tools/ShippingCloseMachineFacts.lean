import Tools.ShippingMachineCleanup
import Tools.ShippingClosedOrder
import Tools.ShippingCloseChecks

/-! # The closed machine's body, statically

`closeMachine lay t` for a transition `t` whose body is ordered assignments
ending in `assign out = w`: the body is the transition's assignments, the
next-value assignments, the registers, the output assignments; its
assignments are in dependency order (`Acyclic`); hence `woCheck`, the
distinct register keys, and what is beside the combinational statements. No
evaluation, no run: facts about the list. -/
namespace Tools.ShippingCloseMachineFacts
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder Sparkle.IR.Semantics
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingSettledSoundness (Acyclic)
open Tools.ShippingMachineClose Tools.ShippingClosedOrder
open Tools.ShippingTypedPostSoundness Tools.ShippingEntrySoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingMachineCleanup (registers_mem nextAssigns_mem)
open Tools.ShippingTopoBody Tools.ShippingTopoChecks Tools.ShippingCloseChecks

/-! ## Ordered assignments -/

theorem Acyclic.append' : ∀ {X Y : List Stmt}, Acyclic X → Acyclic Y →
    (∀ n ∈ writesOf X, n ∉ writesOf Y) →
    (∀ l r, Stmt.assign l r ∈ X → ∀ x ∈ refsOf r, x ∉ writesOf Y) → Acyclic (X ++ Y)
  | [], _, _, hy, _, _ => hy
  | _ :: X, Y, hx, hy, hw, hr => by
    cases hx with
    | @cons l r _ ht hrd htl =>
      have hwX : writesOf (X ++ Y) = writesOf X ++ writesOf Y :=
        Tools.ShippingTopoChecks.writesOf_append X Y
      refine Acyclic.cons ?_ ?_ (Acyclic.append' htl hy
        (fun n hn => hw n (List.mem_cons_of_mem _ hn))
        (fun l' r' hm => hr l' r' (List.mem_cons_of_mem _ hm)))
      · show l ∉ writesOf (X ++ Y)
        rw [hwX]
        intro h
        rcases List.mem_append.mp h with h | h
        · exact ht h
        · exact hw l (List.mem_cons_self ..) h
      · intro x hx
        refine ⟨(hrd x hx).1, ?_⟩
        show x ∉ writesOf (X ++ Y)
        rw [hwX]
        intro h
        rcases List.mem_append.mp h with h | h
        · exact (hrd x hx).2 h
        · exact hr l r (List.mem_cons_self ..) x hx h

theorem Acyclic.nodup : ∀ {X : List Stmt}, Acyclic X → (writesOf X).Nodup
  | [], _ => List.nodup_nil
  | _ :: X, h => by
    cases h with
    | @cons l r _ ht _ htl => exact List.nodup_cons.mpr ⟨ht, Acyclic.nodup htl⟩

theorem writesOf_nextAssigns (w : String) :
    ∀ (ps : List Port) (fs : List SlotField) (n : String), n ∈ writesOf (nextAssigns w ps fs) →
      ∃ p ∈ ps, n = nextName p.name
  | [], _, _, h => by simp [nextAssigns, writesOf] at h
  | _ :: _, [], _, h => by simp [nextAssigns, writesOf] at h
  | p :: ps, f :: fs, n, h => by
    rcases List.mem_cons.mp (show n ∈ nextName p.name :: writesOf (nextAssigns w ps fs) from h) with
      e | h
    · exact ⟨p, List.mem_cons_self .., e⟩
    · obtain ⟨q, hq, e⟩ := writesOf_nextAssigns w ps fs n h
      exact ⟨q, List.mem_cons_of_mem _ hq, e⟩

theorem nextName_inj {a b : String} (h : nextName a = nextName b) : a = b := by
  unfold nextName at h
  exact String.append_right_inj _ |>.mp h

theorem acyclic_nextAssigns (w : String) :
    ∀ (ps : List Port) (fs : List SlotField), (ps.map Port.name).Nodup →
      (∀ p ∈ ps, nextName p.name ≠ w) → Acyclic (nextAssigns w ps fs)
  | [], _, _, _ => .nil
  | _ :: _, [], _, _ => .nil
  | p :: ps, f :: fs, hnd, hw => by
    have hnd' := List.nodup_cons.mp (show (p.name :: ps.map Port.name).Nodup from hnd)
    refine Acyclic.cons ?_ ?_ (acyclic_nextAssigns w ps fs hnd'.2
      (fun q hq => hw q (List.mem_cons_of_mem _ hq)))
    · intro h
      obtain ⟨q, hq, e⟩ := writesOf_nextAssigns w ps fs _ h
      exact hnd'.1 (nextName_inj e ▸ List.mem_map_of_mem hq)
    · intro x hx
      have hxw : x = w := by simpa [fieldRhs, refsOf] using hx
      subst hxw
      refine ⟨fun e => hw p (List.mem_cons_self ..) e.symm, fun h => ?_⟩
      obtain ⟨q, hq, e⟩ := writesOf_nextAssigns x ps fs _ h
      exact hw q (List.mem_cons_of_mem _ hq) e.symm

theorem writesOf_outAssigns (w : String) (outs : List OutField) :
    writesOf (outAssigns w outs) = outs.map (·.name) := by
  induction outs with
  | nil => rfl
  | cons o outs ih =>
    show o.name :: writesOf (outAssigns w outs) = _
    rw [ih]
    rfl

theorem acyclic_outAssigns (w : String) :
    ∀ (outs : List OutField), (outs.map (·.name)).Nodup → (∀ o ∈ outs, o.name ≠ w) →
      Acyclic (outAssigns w outs)
  | [], _, _ => .nil
  | o :: outs, hnd, hw => by
    have hnd' := List.nodup_cons.mp (show (o.name :: outs.map (·.name)).Nodup from hnd)
    refine Acyclic.cons (l := o.name) (r := fieldRhs w o.lo o.width) ?_ ?_
      (acyclic_outAssigns w outs hnd'.2 (fun q hq => hw q (List.mem_cons_of_mem _ hq)))
    · show o.name ∉ writesOf (outAssigns w outs)
      rw [writesOf_outAssigns]
      exact hnd'.1
    · intro x hx
      have hxw : x = w := by simpa [fieldRhs, refsOf] using hx
      subst hxw
      refine ⟨fun e => hw o (List.mem_cons_self ..) e.symm, ?_⟩
      show x ∉ writesOf (outAssigns x outs)
      rw [writesOf_outAssigns]
      intro h
      obtain ⟨q, hq, e⟩ := List.mem_map.mp h
      exact hw q (List.mem_cons_of_mem _ hq) e

/-! ## `woCheck` -/

theorem woCheck_acyclic : ∀ {X : List Stmt}, Acyclic X → ∀ (done : List String),
    (∀ n ∈ done, n ∉ writesOf X) → woCheck done X = true
  | [], _, _, _ => rfl
  | _ :: X, h, done, hd => by
    cases h with
    | @cons l r _ ht hrd htl =>
      have ih := woCheck_acyclic htl (done ++ [l]) (by
        intro n hn hX
        rcases List.mem_append.mp hn with h | h
        · exact hd n h (List.mem_cons_of_mem _ hX)
        · have : n = l := by simpa using h
          exact ht (this ▸ hX))
      simp only [woCheck, stmtReads, stmtWrites, Bool.and_eq_true, List.all_eq_true,
        Bool.not_eq_true', List.mem_singleton, forall_eq, ih, and_true]
      refine ⟨fun n hn => by simpa using (hrd n hn).2, ?_, by simpa using ht⟩
      simpa using fun h => hd l h (List.mem_cons_self ..)

theorem woCheck_regs_front : ∀ (R Y : List Stmt) (done : List String),
    (∀ st ∈ R, isReg st = true) → woCheck done Y = true → woCheck done (R ++ Y) = true
  | [], _, _, _, h => h
  | st :: R, Y, done, hr, h => by
    have h1 := hr st (List.mem_cons_self ..)
    have ih := woCheck_regs_front R Y done (fun s hs => hr s (List.mem_cons_of_mem _ hs)) h
    cases st <;> simp_all [isReg, woCheck, stmtReads, stmtWrites]

/-- Registers put inside a body do not change `woCheck`. -/
theorem woCheck_insert_regs (R Y : List Stmt) (hr : ∀ st ∈ R, isReg st = true) :
    ∀ (X : List Stmt) (done : List String), woCheck done (X ++ Y) = true →
      woCheck done (X ++ (R ++ Y)) = true
  | [], done, h => woCheck_regs_front R Y done hr h
  | st :: X, done, h => by
    simp only [List.cons_append, woCheck, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hw : writesOf (X ++ (R ++ Y)) = writesOf (X ++ Y) := by
      rw [Tools.ShippingTopoChecks.writesOf_append, Tools.ShippingTopoChecks.writesOf_append,
        Tools.ShippingTopoChecks.writesOf_append, writesOf_regs R hr, List.nil_append]
    rw [hw]
    exact ⟨⟨h1, h2⟩, woCheck_insert_regs R Y hr X _ h3⟩

/-! ## The closed machine -/

/-- **The closed machine's body.** For a transition whose body is ordered
assignments `B` ending in `assign out = w` (declared, allocated names): the
closed body is `B`, the next-value assignments, the registers, the output
assignments; the assignments are in dependency order. -/
theorem closeMachine_body {t : Module} {lay : Layout} {B : List Stmt} {w : String}
    (hbody : t.body = B ++ [.assign "out" (.ref w)])
    (acyclic : Acyclic t.body)
    (typed : TypedStmts (weOf t) t.body)
    (names : ∀ p ∈ t.wires, Allocated p.name)
    (inNodup : (t.inputs.map Port.name).Nodup)
    (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (lay.outs.map (·.name)).Nodup) :
    ∃ ps : List Port, ps = t.inputs.drop (t.inputs.length - lay.slots.length) ∧
      (closeMachine lay t).body = B ++ (nextAssigns w ps lay.slots ++
        (registers lay.resetKind ps lay.slots ++ outAssigns w lay.outs)) ∧
      Acyclic (B ++ (nextAssigns w ps lay.slots ++ outAssigns w lay.outs)) ∧
      (∀ st ∈ registers lay.resetKind ps lay.slots, isReg st = true) := by
  have hpw : packedWire? t.body = some w := by simp [packedWire?, hbody]
  have hdrop : t.body.dropLast = B := by simp [hbody]
  obtain ⟨ps, hps⟩ : ∃ ps, ps = t.inputs.drop (t.inputs.length - lay.slots.length) := ⟨_, rfl⟩
  refine ⟨ps, hps, by simp [closeMachine, hpw, hdrop, hps], ?_, ?_⟩
  · rw [hbody] at acyclic
    have haB : Acyclic B := Acyclic.prefix acyclic
    have outFresh : "out" ∉ writesOf B := acyclic_last_fresh acyclic
    have hBassign : ∀ st ∈ B, ∃ l r, st = .assign l r := by
      intro st hs
      obtain ⟨l, e, n, rfl, _⟩ := typed st (by rw [hbody]; exact List.mem_append_left _ hs)
      exact ⟨l, e, rfl⟩
    have hpos : ∀ l r, Stmt.assign l r ∈ B → ∀ n ∈ refsOf r, 0 < weOf t n := by
      intro l r hs n hn
      obtain ⟨l', e, k, heq, ht, _⟩ := typed _ (by rw [hbody]; exact List.mem_append_left _ hs)
      cases heq
      exact ht.refs_positive n hn
    have hwpos : 0 < weOf t w := by
      obtain ⟨l', e, k, heq, ht, _⟩ := typed (.assign "out" (.ref w)) (by rw [hbody]; simp)
      cases heq
      exact ht.refs_positive w (by simp [refsOf])
    have allocOf : ∀ x, 0 < weOf t x → Allocated x := by
      intro x hx
      unfold weOf at hx
      cases h : t.wires.find? (fun p => p.name == x) with
      | none => rw [h] at hx; simp at hx
      | some p =>
        have hn : p.name = x := by simpa using List.find?_some h
        exact hn ▸ names p (List.mem_of_find?_eq_some h)
    have targets : ∀ n ∈ writesOf B, Allocated n := by
      intro n hn
      obtain ⟨r, hr⟩ := assign_of_writes hBassign hn
      obtain ⟨l', e, k, heq, ht, hl⟩ := typed _ (by rw [hbody]; exact List.mem_append_left _ hr)
      cases heq
      rcases hl with hl | hl
      · exact allocOf n (by rw [hl]; exact ht.positive)
      · exact absurd (hl ▸ hn) outFresh
    have psNodup : (ps.map Port.name).Nodup := by
      rw [hps, List.map_drop]
      exact inNodup.sublist (List.drop_sublist _ _)
    have nextNeW : ∀ p ∈ ps, nextName p.name ≠ w := fun p _ heq =>
      nextName_not_allocated p.name (heq ▸ allocOf w hwpos)
    have outsW : ∀ o ∈ lay.outs, o.name ≠ w := fun o ho heq =>
      (outNameOk_facts (outsOk o ho).2).1 (heq ▸ allocOf w hwpos)
    have haN := acyclic_nextAssigns w ps lay.slots psNodup nextNeW
    have haO := acyclic_outAssigns w lay.outs outsNodup outsW
    have notAllocNO : ∀ n ∈ writesOf (nextAssigns w ps lay.slots ++ outAssigns w lay.outs),
        ¬ Allocated n := by
      intro n hn
      rw [Tools.ShippingTopoChecks.writesOf_append] at hn
      rcases List.mem_append.mp hn with h | h
      · obtain ⟨q, _, e⟩ := writesOf_nextAssigns w ps lay.slots n h
        exact e ▸ nextName_not_allocated q.name
      · rw [writesOf_outAssigns] at h
        obtain ⟨o, ho, e⟩ := List.mem_map.mp h
        exact e ▸ (outNameOk_facts (outsOk o ho).2).1
    have haNO : Acyclic (nextAssigns w ps lay.slots ++ outAssigns w lay.outs) := by
      refine Acyclic.append' haN haO ?_ ?_
      · intro n hn hO
        obtain ⟨q, _, e⟩ := writesOf_nextAssigns w ps lay.slots n hn
        rw [writesOf_outAssigns] at hO
        obtain ⟨o, ho, e'⟩ := List.mem_map.mp hO
        exact (outNameOk_facts (outsOk o ho).2).2.2 q.name (e'.trans e)
      · intro l r hm x hx hO
        obtain ⟨p, f, heq⟩ := nextAssigns_mem w ps lay.slots _ hm
        cases heq
        have hxw : x = w := by simpa [fieldRhs, refsOf] using hx
        rw [writesOf_outAssigns] at hO
        obtain ⟨o, ho, e'⟩ := List.mem_map.mp hO
        exact outsW o ho (e'.trans hxw)
    exact Acyclic.append' haB haNO
      (fun n hn hNO => notAllocNO n hNO (targets n hn))
      (fun l r hm x hx hNO => notAllocNO x hNO (allocOf x (hpos l r hm x hx)))
  · intro st hs
    obtain ⟨k, p, f, _, _, rfl⟩ := registers_mem lay.resetKind ps lay.slots st hs
    rfl

/-! ## What `closeChecks_of` asks of the body -/

theorem filter_comb_assigns {X : List Stmt} (h : ∀ st ∈ X, ∃ l r, st = Stmt.assign l r) :
    X.filter isComb = X := by
  rw [List.filter_eq_self]
  intro st hs
  obtain ⟨l, r, rfl⟩ := h st hs
  rfl

theorem filter_comb_regs {R : List Stmt} (h : ∀ st ∈ R, isReg st = true) :
    R.filter isComb = [] := by
  rw [List.filter_eq_nil_iff]
  intro st hs
  have := h st hs
  cases st <;> simp_all [isReg, isComb]

theorem filter_comb_insts {S : List Stmt} (h : S.all isInst = true) : S.filter isComb = S := by
  rw [List.filter_eq_self]
  intro st hs
  have := List.all_eq_true.mp h st hs
  cases st <;> simp_all [isInst, isComb]

theorem nextKeys_registers (rk : Sparkle.IR.Type.ResetKind) :
    ∀ (ps : List Port) (fs : List SlotField) (n : String), n ∈ nextKeys (registers rk ps fs) →
      n ∈ ps.map Port.name
  | [], _, _, h => by simp [registers, nextKeys] at h
  | _ :: _, [], _, h => by simp [registers, nextKeys] at h
  | p :: ps, f :: fs, n, h => by
    rcases List.mem_cons.mp (show n ∈ p.name :: nextKeys (registers rk ps fs) from h) with e | h
    · exact e ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (nextKeys_registers rk ps fs n h)

theorem nextKeys_registers_nodup (rk : Sparkle.IR.Type.ResetKind) :
    ∀ (ps : List Port) (fs : List SlotField), (ps.map Port.name).Nodup →
      (nextKeys (registers rk ps fs)).Nodup
  | [], _, _ => by simp [registers, nextKeys]
  | _ :: _, [], _ => by simp [registers, nextKeys]
  | p :: ps, f :: fs, h => by
    have h' := List.nodup_cons.mp (show (p.name :: ps.map Port.name).Nodup from h)
    show (p.name :: nextKeys (registers rk ps fs)).Nodup
    exact List.nodup_cons.mpr ⟨fun hm => h'.1 (nextKeys_registers rk ps fs _ hm),
      nextKeys_registers_nodup rk ps fs h'.2⟩

theorem nextKeys_assigns {X : List Stmt} (h : ∀ st ∈ X, ∃ l r, st = Stmt.assign l r) :
    nextKeys X = [] := by
  unfold nextKeys
  rw [List.flatMap_eq_nil_iff]
  intro st hs
  obtain ⟨l, r, rfl⟩ := h st hs
  rfl

/-- **The static premises of `closeChecks_of`**, for a body
`X ++ (R ++ Y)` — ordered assignments `X ++ Y` around registers `R` — and
instance statements `stmts`. -/
theorem static_checks {X R Y stmts : List Stmt} (hacy : Acyclic (X ++ Y))
    (hR : ∀ st ∈ R, isReg st = true) (hkeys : (nextKeys R).Nodup)
    (hinst : stmts.all isInst = true) :
    woCheck [] (X ++ (R ++ Y)) = true ∧
    combOf ((X ++ (R ++ Y)) ++ stmts) = (X ++ Y) ++ stmts ∧
    (∀ st ∈ othersOf ((X ++ (R ++ Y)) ++ stmts), isReg st = true) ∧
    (writesOf (combOf ((X ++ (R ++ Y)) ++ stmts))).Nodup ∧
    (nextKeys (X ++ (R ++ Y))).Nodup := by
  have hXY := Acyclic.assign hacy
  have hX : ∀ st ∈ X, ∃ l r, st = Stmt.assign l r := fun st hs => hXY st (List.mem_append_left _ hs)
  have hY : ∀ st ∈ Y, ∃ l r, st = Stmt.assign l r := fun st hs => hXY st (List.mem_append_right _ hs)
  have hcomb : combOf ((X ++ (R ++ Y)) ++ stmts) = (X ++ Y) ++ stmts := by
    rw [combOf_eq]
    simp only [List.filter_append, filter_comb_assigns hX, filter_comb_assigns hY,
      filter_comb_regs hR, filter_comb_insts hinst, List.nil_append]
  refine ⟨woCheck_insert_regs R Y hR X [] (woCheck_acyclic hacy [] (fun _ h => by simp at h)),
    hcomb, ?_, ?_, ?_⟩
  · intro st hs
    rw [othersOf_eq] at hs
    obtain ⟨hm, hc⟩ := List.mem_filter.mp hs
    simp only [List.mem_append] at hm
    rcases hm with (h | h | h) | h
    · obtain ⟨l, r, rfl⟩ := hX st h
      simp [isComb] at hc
    · exact hR st h
    · obtain ⟨l, r, rfl⟩ := hY st h
      simp [isComb] at hc
    · have := List.all_eq_true.mp hinst st h
      cases st <;> simp_all [isInst, isComb]
  · rw [hcomb, Tools.ShippingTopoChecks.writesOf_append, writesOf_insts stmts hinst,
      List.append_nil]
    exact Acyclic.nodup hacy
  · unfold nextKeys at hkeys ⊢
    have h1 := nextKeys_assigns hX
    have h2 := nextKeys_assigns hY
    unfold nextKeys at h1 h2
    rw [List.flatMap_append, List.flatMap_append, h1, h2, List.nil_append, List.append_nil]
    exact hkeys

end Tools.ShippingCloseMachineFacts
