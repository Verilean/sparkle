import Tools.ShippingMachineCleanup

/-! # The closed machine is typed in its own wire table (G1, `designCheck` text conjuncts)

`closeMachine lay t` of a transition `t` whose body is `B ++ [out := w]`:

    wires   = t.wires ++ [next<p> : p.ty | p a slot port]
    inputs  = t.inputs without the slot ports (++ clk, rst when there are slots)
    outputs = [o.name : o.ty | o ∈ lay.outs]
    body    = B ++ [next<p> := w[f.lo + f.width - 1 : f.lo]] ++
              [register p ← next<p>] ++ [o.name := w[o.lo + o.width - 1 : o.lo]]

`closeMachine_typed`: for a transition typed in its wire table
(`TypedStmts (weOf t) t.body`), with allocated distinct wire names, its
inputs wires, its slot ports at their slots' widths (`SlotOk`), and every
slot / output field inside the packed wire's declared width —

* FRAME: a name of positive width in `t` keeps its width
  (`weOf (closeMachine lay t) x = weOf t x`): the new wires are `next…`
  names, which no allocated name is;
* the closed machine's wire names are distinct, each allocated or the
  `next…` name of an allocated name; its inputs are allocated names, `clk`
  or `rst`; its outputs are the layout's;
* every statement is an assignment or a register;
* every assignment `l := r` is `TypedExpr (weOf M) r n` with `weOf M l = n`
  (a wire: a statement of `B`, or a next-value wire at its slot's width) or
  `l` an output port of `M` whose type has width `n`;
* every register's input is typed at its output's declared width.

`fieldRhs_typed`: a field `[lo + width - 1 : lo]` of a wire at least
`lo + width` wide is a `TypedExpr.slice` of width `width`.

The first part of the proof (the closed module's components, the distinct
wire names) is `closeMachine_fixed`'s (`Tools/ShippingMachineCleanup.lean`),
copied; that theorem CONSUMES typedness, this one concludes it.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingCloseMachineTyped
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingTypedPostSoundness Tools.ShippingRegisterSoundness
open Tools.ShippingMachineClose
open Tools.ShippingMachineCleanup (weOf_port zip_left registers_mem)
open Sparkle.IR.NameHints (Allocated)

/-- A field of a wide enough wire is a typed part-select of the field's
width. -/
theorem fieldRhs_typed {we : WEnv} {w : String} {lo width : Nat} (hpos : 0 < width)
    (hfit : lo + width ≤ we w) : TypedExpr we (fieldRhs w lo width) width := by
  have h := TypedExpr.slice (we := we) w (lo + width - 1) lo (by omega) (by omega)
  have e : lo + width - 1 - lo + 1 = width := by omega
  rw [e] at h
  exact h

/-- A next-value assignment is its slot port's, with the port and the field
related as the lists are. -/
theorem nextAssigns_zip {R : Port → SlotField → Prop} (w : String) {ps : List Port}
    {fs : List SlotField} (hz : Zip₂ R ps fs) :
    ∀ st ∈ nextAssigns w ps fs, ∃ p f, p ∈ ps ∧ f ∈ fs ∧ R p f ∧
      st = Stmt.assign (nextName p.name) (fieldRhs w f.lo f.width) := by
  induction hz with
  | nil =>
    intro st h
    have h' : st ∈ ([] : List Stmt) := h
    cases h'
  | @cons p f ps fs hab rest ih =>
    intro st h
    have h' : st ∈ Stmt.assign (nextName p.name) (fieldRhs w f.lo f.width) ::
        nextAssigns w ps fs := h
    rcases List.mem_cons.mp h' with h1 | h1
    · exact ⟨p, f, List.Mem.head _, List.Mem.head _, hab, h1⟩
    · obtain ⟨p', f', hp, hf, hr, he⟩ := ih st h1
      exact ⟨p', f', List.Mem.tail _ hp, List.Mem.tail _ hf, hr, he⟩

set_option maxHeartbeats 1000000 in
/-- **The closed machine is typed in its own wire table.** -/
theorem closeMachine_typed {t : Module} {lay : Layout} {B : List Stmt} {w : String}
    (hbody : t.body = B ++ [.assign "out" (.ref w)])
    (typed : TypedStmts (weOf t) t.body)
    (named : ∀ l r, Stmt.assign l r ∈ B → Allocated l)
    (names : ∀ p ∈ t.wires, Allocated p.name)
    (inWires : ∀ p ∈ t.inputs, p ∈ t.wires)
    (inNodup : (t.inputs.map Port.name).Nodup)
    (wiresNodup : (t.wires.map Port.name).Nodup)
    (slots : Zip₂ (SlotOk (weOf t))
      (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots)
    (fitS : ∀ f ∈ lay.slots, f.lo + f.width ≤ weOf t w)
    (fitO : ∀ o ∈ lay.outs, o.lo + o.width ≤ weOf t w)
    (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outTy : ∀ o ∈ lay.outs, o.ty.bitWidth = o.width) :
    -- the frame: the transition's widths are kept
    (∀ x, 0 < weOf t x → weOf (closeMachine lay t) x = weOf t x) ∧
    -- the wires
    ((closeMachine lay t).wires.map Port.name).Nodup ∧
    (∀ p ∈ (closeMachine lay t).wires,
      Allocated p.name ∨ ∃ y, Allocated y ∧ p.name = nextName y) ∧
    -- the ports
    (∀ p ∈ (closeMachine lay t).inputs, Allocated p.name ∨ p.name = "clk" ∨ p.name = "rst") ∧
    (closeMachine lay t).outputs =
      lay.outs.map (fun o => ({ name := o.name, ty := o.ty } : Port)) ∧
    -- the statement kinds
    (∀ st ∈ (closeMachine lay t).body,
      (∃ l r, st = Stmt.assign l r) ∨ ∃ o c rk i iv, st = Stmt.register o c rk i iv) ∧
    -- the assignments
    (∀ l r, Stmt.assign l r ∈ (closeMachine lay t).body →
      ∃ n, TypedExpr (weOf (closeMachine lay t)) r n ∧
        (weOf (closeMachine lay t) l = n ∨
          ∃ q ∈ (closeMachine lay t).outputs, q.name = l ∧ q.ty.bitWidth = n)) ∧
    -- the registers
    (∀ o c rk i iv, Stmt.register o c rk i iv ∈ (closeMachine lay t).body →
      TypedExpr (weOf (closeMachine lay t)) i (weOf (closeMachine lay t) o)) := by
  have hpw : packedWire? t.body = some w := by simp [packedWire?, hbody]
  have hdrop : t.body.dropLast = B := by simp [hbody]
  generalize hps : t.inputs.drop (t.inputs.length - lay.slots.length) = ps at slots
  generalize hM : closeMachine lay t = M
  have hMw : M.wires = t.wires ++ ps.map fun p => { name := nextName p.name, ty := p.ty } := by
    rw [← hM]; simp [closeMachine, hpw, hps]
  have hMi : M.inputs = t.inputs.take (t.inputs.length - lay.slots.length) ++
      (if lay.slots.isEmpty then [] else
        [{ name := "clk", ty := .bit }, { name := "rst", ty := .bit }]) := by
    rw [← hM]; simp [closeMachine, hpw]
  have hMo : M.outputs = lay.outs.map fun o => ({ name := o.name, ty := o.ty } : Port) := by
    rw [← hM]; simp [closeMachine, hpw]
  have hMb : M.body = B ++ nextAssigns w ps lay.slots ++ registers lay.resetKind ps lay.slots ++
      outAssigns w lay.outs := by
    rw [← hM]; simp [closeMachine, hpw, hdrop, hps]
  have psIn : ∀ p ∈ ps, p ∈ t.inputs := fun p hp => List.mem_of_mem_drop (hps ▸ hp)
  have psNodup : (ps.map Port.name).Nodup := by
    rw [← hps, List.map_drop]; exact inNodup.sublist (List.drop_sublist _ _)
  -- the closed module's wires are distinct
  have hndM : (M.wires.map Port.name).Nodup := by
    rw [hMw, List.map_append, List.map_map]
    refine List.nodup_append.mpr ⟨wiresNodup, ?_, ?_⟩
    · show (ps.map fun p => nextName p.name).Nodup
      rw [show (fun p : Port => nextName p.name) = nextName ∘ Port.name from rfl, ← List.map_map]
      exact List.pairwise_map.mpr (psNodup.imp fun h he => h (nextName_inj he))
    · intro a ha b hb hab
      subst hab
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      obtain ⟨p, _, hpq⟩ := List.mem_map.mp hb
      exact nextName_not_allocated p.name (by
        have : (fun p : Port => ({ name := nextName p.name, ty := p.ty } : Port).name) p = q.name := hpq
        simp only at this
        rw [this]; exact names q hq)
  -- widths of the transition's wires are kept
  have hweT : ∀ x, 0 < weOf t x → weOf M x = weOf t x := fun x hx => weOf_wires_append hMw hx
  -- the packed wire
  have hwpos : 0 < weOf t w := by
    obtain ⟨l', e, k, heq, ht, _⟩ := typed (.assign "out" (.ref w)) (by rw [hbody]; simp)
    cases heq
    exact ht.refs_positive w (by simp [Sparkle.IR.Reorder.refsOf])
  have hwM : weOf M w = weOf t w := hweT w hwpos
  -- a slot port and its next-value wire
  have slotW : ∀ p ∈ ps, 0 < weOf t p.name ∧ weOf M (nextName p.name) = weOf t p.name ∧
      weOf M p.name = weOf t p.name := by
    intro p hp
    obtain ⟨f, hf⟩ : ∃ f, (SlotOk (weOf t)) p f := zip_left slots p hp
    have hpos : 0 < weOf t p.name := by rw [hf.1]; exact hf.2
    have hq : ({ name := nextName p.name, ty := p.ty } : Port) ∈ M.wires := by
      rw [hMw]; exact List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have h1 := weOf_port hndM hq
    have h2 := weOf_port wiresNodup (inWires p (psIn p hp))
    have hnx : weOf M (nextName p.name) = weOf t p.name := h1.trans h2.symm
    exact ⟨hpos, hnx, hweT _ hpos⟩
  -- every statement, classified
  have cls : ∀ st ∈ M.body,
      (∃ l r n, st = Stmt.assign l r ∧ TypedExpr (weOf M) r n ∧
        (weOf M l = n ∨ ∃ q ∈ M.outputs, q.name = l ∧ q.ty.bitWidth = n)) ∨
      (∃ p ∈ ps, ∃ (c : String) (rk : String × ResetKind) (iv : Int),
        st = Stmt.register p.name c rk (.ref (nextName p.name)) iv) := by
    intro st hst
    rw [hMb] at hst
    simp only [List.mem_append] at hst
    rcases hst with ((hB | hN) | hR) | hO
    · -- a statement of the transition
      obtain ⟨l, e, n, heq, ht, hl⟩ := typed st (by rw [hbody]; exact List.mem_append_left _ hB)
      rw [heq] at hB
      refine Or.inl ⟨l, e, n, heq,
        ht.we_congr (fun x hx => hweT x (ht.refs_positive x hx)), Or.inl ?_⟩
      rcases hl with hl | hl
      · exact (hweT l (by rw [hl]; exact ht.positive)).trans hl
      · have ha := named l e hB
        rw [hl] at ha
        exact absurd ha Tools.ShippingRegisterSoundness.not_allocated_out
    · -- a next-value assignment
      obtain ⟨p, f, hp, hf, hok, heq⟩ := nextAssigns_zip w slots st hN
      refine Or.inl ⟨nextName p.name, fieldRhs w f.lo f.width, f.width, heq,
        fieldRhs_typed hok.2 (by rw [hwM]; exact fitS f hf), Or.inl ?_⟩
      rw [(slotW p hp).2.1]
      exact hok.1
    · -- a slot register
      obtain ⟨k, p, f, hp, -, heq⟩ := registers_mem lay.resetKind ps lay.slots st hR
      exact Or.inr ⟨p, List.mem_of_getElem? hp, "clk", ("rst", lay.resetKind), Int.ofNat f.init,
        heq⟩
    · -- an output's part-select of the packed wire
      simp only [outAssigns, List.mem_map] at hO
      obtain ⟨o, ho, heq⟩ := hO
      refine Or.inl ⟨o.name, fieldRhs w o.lo o.width, o.width, heq.symm,
        fieldRhs_typed (outsOk o ho).1 (by rw [hwM]; exact fitO o ho),
        Or.inr ⟨({ name := o.name, ty := o.ty } : Port), ?_, rfl, outTy o ho⟩⟩
      rw [hMo]
      exact List.mem_map.mpr ⟨o, ho, rfl⟩
  refine ⟨hweT, hndM, ?_, ?_, hMo, ?_, ?_, ?_⟩
  · -- the wires
    intro p hp
    rw [hMw] at hp
    rcases List.mem_append.mp hp with h | h
    · exact Or.inl (names p h)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
      exact Or.inr ⟨q.name, names q (inWires q (psIn q hq)), rfl⟩
  · -- the inputs
    intro p hp
    rw [hMi] at hp
    rcases List.mem_append.mp hp with h | h
    · exact Or.inl (names p (inWires p (List.mem_of_mem_take h)))
    · split at h
      · cases h
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
        rcases h with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
  · -- the kinds
    intro st hst
    rcases cls st hst with ⟨l, r, n, heq, -, -⟩ | ⟨p, hp, c, rk, iv, heq⟩
    · exact Or.inl ⟨l, r, heq⟩
    · exact Or.inr ⟨_, _, _, _, _, heq⟩
  · -- the assignments
    intro l r hm
    rcases cls _ hm with ⟨l', r', n, heq, ht, hl⟩ | ⟨p, hp, c, rk, iv, heq⟩
    · cases heq
      exact ⟨n, ht, hl⟩
    · cases heq
  · -- the registers
    intro o c rk i iv hm
    rcases cls _ hm with ⟨l', r', n, heq, -, -⟩ | ⟨p, hp, c', rk', iv', heq⟩
    · cases heq
    · cases heq
      obtain ⟨hpos, hnx, hpM⟩ := slotW p hp
      have h := TypedExpr.ref (we := weOf M) (nextName p.name) (by rw [hnx]; exact hpos)
      rw [hnx, ← hpM] at h
      exact h

end Tools.ShippingCloseMachineTyped
