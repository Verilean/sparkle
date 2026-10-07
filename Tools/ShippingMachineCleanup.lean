import Tools.ShippingMachineClose

/-! # The zero-width cleanup on a closed machine module

`closeMachine_comb_cleanup` (ShippingMachineClose) shows that the full
entry's zero-width cleanup changes nothing on a closed machine WITHOUT
slots. With slots the closed module also has the next-value wires
(`nextName`), their assignments (part-selects of the packed wire) and the
slot registers (reading the next-value wires): every one of them has a
positive width (the slot's), so the cleanup again keeps every statement,
width and port. -/
namespace Tools.ShippingMachineCleanup
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingTypedPostSoundness Tools.ShippingRegisterSoundness
open Tools.ShippingMachineClose
open Sparkle.IR.NameHints (Allocated)

/-- The width a port's type gives its name, for distinct wire names. -/
theorem weOf_port {m : Module} (nd : (m.wires.map (·.name)).Nodup) {p : Port} (hp : p ∈ m.wires) :
    weOf m p.name = match p.ty with
      | .bitVector k => k
      | .bit => 1
      | _ => 0 := by
  unfold weOf
  rw [find?_of_nodup nd hp]
  obtain ⟨name, ty⟩ := p
  cases ty <;> rfl

/-- The cleanup keeps the next-value assignments whose targets have a
positive entry. -/
theorem dz_nextAssigns (wm : Sparkle.IR.Optimize.WidthMap) (w : String) :
    ∀ (ps : List Port) (fs : List SlotField),
      (∀ p ∈ ps, wm.get? (nextName p.name) ≠ some 0) →
      ∀ st ∈ nextAssigns w ps fs, Sparkle.IR.ZeroWidth.dzStmt wm st = some st
  | p :: ps, f :: fs, h, st, hst => by
    simp only [nextAssigns, List.mem_cons] at hst
    rcases hst with rfl | hst
    · have hp := h p List.mem_cons_self
      rw [Std.HashMap.get?_eq_getElem?] at hp
      cases hg : wm[nextName p.name]? with
      | none => simp [Sparkle.IR.ZeroWidth.dzStmt, hg, fieldRhs, Sparkle.IR.ZeroWidth.dzExpr]
      | some k =>
        cases k with
        | zero => exact absurd hg hp
        | succ k => simp [Sparkle.IR.ZeroWidth.dzStmt, hg, fieldRhs, Sparkle.IR.ZeroWidth.dzExpr]
    · exact dz_nextAssigns wm w ps fs (fun q hq => h q (List.mem_cons_of_mem _ hq)) st hst
  | [], _, _, st, hst => by simp [nextAssigns] at hst
  | _ :: _, [], _, st, hst => by simp [nextAssigns] at hst

/-- The cleanup keeps the slot registers (they read plain wires). -/
theorem dz_registers (wm : Sparkle.IR.Optimize.WidthMap) (rk : ResetKind) :
    ∀ (ps : List Port) (fs : List SlotField),
      ∀ st ∈ registers rk ps fs, Sparkle.IR.ZeroWidth.dzStmt wm st = some st
  | p :: ps, f :: fs, st, hst => by
    simp only [registers, List.mem_cons] at hst
    rcases hst with rfl | hst
    · simp [Sparkle.IR.ZeroWidth.dzStmt, Sparkle.IR.ZeroWidth.dzExpr]
    · exact dz_registers wm rk ps fs st hst
  | [], _, st, hst => by simp [registers] at hst
  | _ :: _, [], st, hst => by simp [registers] at hst

theorem zip_left {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Zip₂ R as bs → ∀ a ∈ as, ∃ b, R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hab rest, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, hab⟩
    · exact zip_left rest a h

theorem not_allocated_clk : ¬ Allocated "clk" := by
  intro h
  have := h.2
  revert this
  decide

theorem nextName_ne_rst (s : String) : nextName s ≠ "rst" := by
  intro h
  have := congrArg String.length h
  have h3 : "rst".length = 3 := by decide
  have h4 : "next".length = 4 := by decide
  rw [nextName, String.length_append, h4, h3] at this
  omega

theorem nextName_ne_clk (s : String) : nextName s ≠ "clk" := by
  intro h
  have := congrArg String.length h
  have h3 : "clk".length = 3 := by decide
  have h4 : "next".length = 4 := by decide
  rw [nextName, String.length_append, h4, h3] at this
  omega

/-- A closed transition's wires are distinct. -/
theorem closeMachine_wiresNodup {t : Module} {lay : Layout} {B : List Stmt} {w : String}
    (hbody : t.body = B ++ [.assign "out" (.ref w)])
    (names : ∀ p ∈ t.wires, Allocated p.name)
    (inNodup : (t.inputs.map Port.name).Nodup)
    (wiresNodup : (t.wires.map Port.name).Nodup) :
    ((closeMachine lay t).wires.map Port.name).Nodup := by
  have hpw : packedWire? t.body = some w := by simp [packedWire?, hbody]
  generalize hps : t.inputs.drop (t.inputs.length - lay.slots.length) = ps
  have hMw : (closeMachine lay t).wires =
      t.wires ++ ps.map fun p => { name := nextName p.name, ty := p.ty } := by
    simp [closeMachine, hpw, hps]
  have psNodup : (ps.map Port.name).Nodup := by
    rw [← hps, List.map_drop]; exact inNodup.sublist (List.drop_sublist _ _)
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

/-- Every statement of a closed transition is kept by the cleanup under any
width map that agrees with the module's own off the clock and reset. -/
theorem closeMachine_fixed {t : Module} {lay : Layout} {B : List Stmt} {w : String}
    (hbody : t.body = B ++ [.assign "out" (.ref w)])
    (typed : TypedStmts (weOf t) t.body)
    (names : ∀ p ∈ t.wires, Allocated p.name)
    (inWires : ∀ p ∈ t.inputs, p ∈ t.wires)
    (inNodup : (t.inputs.map Port.name).Nodup)
    (wiresNodup : (t.wires.map Port.name).Nodup)
    (slots : Zip₂ (SlotOk (weOf t))
      (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots)
    (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (lay.outs.map (·.name)).Nodup)
    (outTy : ∀ o ∈ lay.outs, o.ty.bitWidth = o.width)
    (wm : Sparkle.IR.Optimize.WidthMap)
    (hagree : ∀ x, x ≠ "clk" → x ≠ "rst" →
      wm.get? x = (Sparkle.IR.Optimize.buildWidthMap (closeMachine lay t)).get? x) :
    ∀ st ∈ (closeMachine lay t).body, Sparkle.IR.ZeroWidth.dzStmt wm st = some st := by
  have hpw : packedWire? t.body = some w := by simp [packedWire?, hbody]
  have hdrop : t.body.dropLast = B := by simp [hbody]
  generalize hps : t.inputs.drop (t.inputs.length - lay.slots.length) = ps at slots
  generalize hM : closeMachine lay t = M at hagree ⊢
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
  -- a name no wire carries
  have notWire : ∀ x, ¬ Allocated x → (∀ y, x ≠ nextName y) → x ∉ M.wires.map Port.name := by
    intro x hx hn hm
    rw [hMw, List.map_append] at hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
      exact hx (names p hp)
    · rw [List.map_map] at hm
      obtain ⟨p, _, hpx⟩ := List.mem_map.mp hm
      exact hn p.name hpx.symm
  have hOutNames : (M.outputs.map Port.name).Nodup := by
    rw [hMo, List.map_map]; exact outsNodup
  -- widths of the transition's wires are kept
  have hweT : ∀ x, 0 < weOf t x → weOf M x = weOf t x := fun x hx => weOf_wires_append hMw hx
  -- an output port's entry in the width map
  have outEntry : ∀ o ∈ lay.outs,
      (Sparkle.IR.Optimize.buildWidthMap M).get? o.name = some o.width := by
    intro o ho
    obtain ⟨hna, -, hnn⟩ := outNameOk_facts (outsOk o ho).2
    simp only [Sparkle.IR.Optimize.buildWidthMap]
    rw [Tools.ShippingPostSoundness.wmFold_notin M.wires _ _ (notWire _ hna hnn)]
    have hp : ({ name := o.name, ty := o.ty } : Port) ∈ M.outputs := by
      rw [hMo]; exact List.mem_map.mpr ⟨o, ho, rfl⟩
    rw [show o.name = ({ name := o.name, ty := o.ty } : Port).name from rfl,
      Tools.ShippingPostSoundness.wmFold_mem M.outputs _ _ hOutNames hp, outTy o ho]
  -- a next-value wire's entry: its slot's positive width
  have nextEntry : ∀ p ∈ ps,
      (Sparkle.IR.Optimize.buildWidthMap M).get? (nextName p.name) ≠ some 0 := by
    intro p hp
    obtain ⟨f, hf⟩ : ∃ f, (SlotOk (weOf t)) p f := zip_left slots p hp
    have hpos : 0 < weOf t p.name := by rw [hf.1]; exact hf.2
    have hq : ({ name := nextName p.name, ty := p.ty } : Port) ∈ M.wires := by
      rw [hMw]; exact List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩)
    have h1 := weOf_port hndM hq
    have h2 := weOf_port wiresNodup (inWires p (psIn p hp))
    have hposM : 0 < weOf M (nextName p.name) := by
      rw [show nextName p.name = ({ name := nextName p.name, ty := p.ty } : Port).name from rfl,
        h1]
      rw [h2] at hpos; exact hpos
    rw [widthMap_internal hndM hposM]
    simp only [ne_eq, Option.some.injEq]; omega
  -- the agreement at the names the statements read and write
  have allocNe : ∀ x, Allocated x → x ≠ "clk" ∧ x ≠ "rst" := fun x hx =>
    ⟨fun h => not_allocated_clk (h ▸ hx), fun h => Tools.ShippingRegisterSoundness.not_allocated_rst (h ▸ hx)⟩
  intro st hst
  rw [hMb] at hst
  simp only [List.mem_append] at hst
  rcases hst with ((hB | hN) | hR) | hO
  · -- a statement of the transition
    obtain ⟨l, e, n, rfl, ht, hl⟩ := typed st (by rw [hbody]; exact List.mem_append_left _ hB)
    have hwm : ∀ x ∈ Sparkle.IR.Reorder.refsOf e,
        Sparkle.IR.ZeroWidth.exprWidth wm (.ref x) ≠ 0 := by
      intro x hx
      have hpos := ht.refs_positive x hx
      have hg := widthMap_internal hndM (show 0 < weOf M x by rw [hweT x hpos]; exact hpos)
      have hxa : Allocated x := by
        unfold weOf at hpos
        cases hf : t.wires.find? (fun p => p.name == x) with
        | none => rw [hf] at hpos; simp at hpos
        | some p =>
          have hx := List.find?_some hf
          simp only [beq_iff_eq] at hx
          exact hx ▸ names p (List.mem_of_find?_eq_some hf)
      rw [← hagree x (allocNe x hxa).1 (allocNe x hxa).2] at hg
      simp only [Sparkle.IR.ZeroWidth.exprWidth, Std.HashMap.getD_eq_getD_getElem?,
        ← Std.HashMap.get?_eq_getElem?, hg, Option.getD_some]
      rw [hweT x hpos]; omega
    have hnz : (Sparkle.IR.Optimize.buildWidthMap M).get? l ≠ some 0 := by
      rcases hl with hl | rfl
      · have hpl : 0 < weOf t l := by rw [hl]; exact ht.positive
        rw [widthMap_internal hndM (show 0 < weOf M l by rw [hweT l hpl]; exact hpl),
          hweT l hpl, hl]
        have := ht.positive
        simp only [ne_eq, Option.some.injEq]; omega
      · -- `out`: no wire, no input; an output with a positive width, or absent
        have hna : ¬ Allocated "out" := Tools.ShippingRegisterSoundness.not_allocated_out
        have hnn : ∀ y, "out" ≠ nextName y := fun y h => nextName_ne_out y h.symm
        by_cases ho : ∃ o ∈ lay.outs, o.name = "out"
        · obtain ⟨o, ho, hon⟩ := ho
          rw [← hon, outEntry o ho]
          have := (outsOk o ho).1
          simp only [ne_eq, Option.some.injEq]; omega
        · simp only [Sparkle.IR.Optimize.buildWidthMap]
          rw [Tools.ShippingPostSoundness.wmFold_notin M.wires _ _ (notWire _ hna hnn),
            Tools.ShippingPostSoundness.wmFold_notin M.outputs _ _ (by
              rw [hMo, List.map_map]
              intro hm
              obtain ⟨o, ho', hon⟩ := List.mem_map.mp hm
              exact ho ⟨o, ho', hon⟩),
            Tools.ShippingPostSoundness.wmFold_notin M.inputs _ _ (by
              rw [hMi, List.map_append]
              intro hm
              rcases List.mem_append.mp hm with hm | hm
              · obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hm
                exact hna (hpn ▸ names p (inWires p (List.mem_of_mem_take hp)))
              · split at hm
                · simp at hm
                · simp at hm)]
          simp
    have hdz := dzExpr_typed ht wm hwm
    have hnz' : wm.get? l ≠ some 0 := by
      have hl' : l ≠ "clk" ∧ l ≠ "rst" := by
        rcases hl with hl | rfl
        · have hpl : 0 < weOf t l := by rw [hl]; exact ht.positive
          unfold weOf at hpl
          cases hf : t.wires.find? (fun p => p.name == l) with
          | none => rw [hf] at hpl; simp at hpl
          | some p =>
            have hx := List.find?_some hf
            simp only [beq_iff_eq] at hx
            exact allocNe l (hx ▸ names p (List.mem_of_find?_eq_some hf))
        · exact ⟨by decide, by decide⟩
      rw [hagree l hl'.1 hl'.2]; exact hnz
    simp only [Sparkle.IR.ZeroWidth.dzStmt]
    cases hg : wm.get? l with
    | none => simp [hdz]
    | some k =>
      cases k with
      | zero => exact absurd hg hnz'
      | succ k => simp [hdz]
  · exact dz_nextAssigns _ w ps lay.slots (fun p hp => by
      rw [hagree _ (nextName_ne_clk _) (nextName_ne_rst _)]; exact nextEntry p hp) st hN
  · exact dz_registers _ lay.resetKind ps lay.slots st hR
  · -- an output's part-select of the packed wire
    simp only [outAssigns, List.mem_map] at hO
    obtain ⟨o, ho, rfl⟩ := hO
    have hok := (outsOk o ho).2
    simp only [outNameOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    simp only [Sparkle.IR.ZeroWidth.dzStmt, hagree o.name hok.2 hok.1.2, outEntry o ho]
    have := (outsOk o ho).1
    split
    · rename_i h; simp at h; omega
    · simp [fieldRhs, Sparkle.IR.ZeroWidth.dzExpr]

/-- The register of slot `k`. -/
theorem mem_registers (rk : ResetKind) :
    ∀ (ps : List Port) (fs : List SlotField) (k : Nat) (p : Port) (f : SlotField),
      ps[k]? = some p → fs[k]? = some f →
      Stmt.register p.name "clk" ("rst", rk) (.ref (nextName p.name)) (Int.ofNat f.init) ∈
        registers rk ps fs
  | q :: ps, g :: fs, 0, p, f, hp, hf => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hp hf
    subst hp hf; simp [registers]
  | q :: ps, g :: fs, k + 1, p, f, hp, hf => by
    simp only [List.getElem?_cons_succ] at hp hf
    simp only [registers]
    exact List.mem_cons_of_mem _ (mem_registers rk ps fs k p f hp hf)
  | [], _, _, _, _, hp, _ => by simp at hp
  | _ :: _, [], _, _, _, _, hf => by simp at hf

/-- Every statement of `registers` is a slot's register. -/
theorem registers_mem (rk : ResetKind) :
    ∀ (ps : List Port) (fs : List SlotField) (st : Stmt), st ∈ registers rk ps fs →
      ∃ (k : Nat) (p : Port) (f : SlotField), ps[k]? = some p ∧ fs[k]? = some f ∧
        st = Stmt.register p.name "clk" ("rst", rk) (.ref (nextName p.name)) (Int.ofNat f.init)
  | q :: ps, g :: fs, st, h => by
    simp only [registers, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, q, g, rfl, rfl, rfl⟩
    · obtain ⟨k, p, f, hp, hf, he⟩ := registers_mem rk ps fs st h
      exact ⟨k + 1, p, f, by simpa using hp, by simpa using hf, he⟩
  | [], _, _, h => by simp [registers] at h
  | _ :: _, [], _, h => by simp [registers] at h

/-- **The cleanup keeps a closed transition, with or without slots.** -/
theorem closeMachine_cleanup {t : Module} {lay : Layout} {B : List Stmt} {w : String}
    (hbody : t.body = B ++ [.assign "out" (.ref w)])
    (typed : TypedStmts (weOf t) t.body)
    (names : ∀ p ∈ t.wires, Allocated p.name)
    (inWires : ∀ p ∈ t.inputs, p ∈ t.wires)
    (inNodup : (t.inputs.map Port.name).Nodup)
    (wiresNodup : (t.wires.map Port.name).Nodup)
    (slots : Zip₂ (SlotOk (weOf t))
      (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots)
    (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (lay.outs.map (·.name)).Nodup)
    (outTy : ∀ o ∈ lay.outs, o.ty.bitWidth = o.width) :
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule (closeMachine lay t)).body =
        (closeMachine lay t).body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule (closeMachine lay t)) =
        weOf (closeMachine lay t) ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule (closeMachine lay t)).inputs =
        (closeMachine lay t).inputs ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule (closeMachine lay t)).outputs =
        (closeMachine lay t).outputs := by
  have hfix := closeMachine_fixed hbody typed names inWires inNodup wiresNodup slots outsOk
    outsNodup outTy _ (fun _ _ _ => rfl)
  have hpw : packedWire? t.body = some w := by simp [packedWire?, hbody]
  have hndM : ((closeMachine lay t).wires.map Port.name).Nodup :=
    (closeMachine_wiresNodup hbody names inNodup wiresNodup)
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨Tools.ShippingPostSoundness.filterMap_eq_self _ hfix,
    Tools.ShippingPostSoundness.weOf_dropWires _ hndM, rfl, rfl⟩

theorem nextAssigns_mem (w : String) :
    ∀ (ps : List Port) (fs : List SlotField) (st : Stmt), st ∈ nextAssigns w ps fs →
      ∃ (p : Port) (f : SlotField), st = .assign (nextName p.name) (fieldRhs w f.lo f.width)
  | q :: ps, g :: fs, st, h => by
    simp only [nextAssigns, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨q, g, rfl⟩
    · exact nextAssigns_mem w ps fs st h
  | [], _, _, h => by simp [nextAssigns] at h
  | _ :: _, [], _, h => by simp [nextAssigns] at h

/-- **No statement of a closed machine assigns the clock or the reset.** -/
theorem closeMachine_noClkRst {t : Module} {lay : Layout} {B : List Stmt} {w : String}
    (hbody : t.body = B ++ [.assign "out" (.ref w)])
    (typed : TypedStmts (weOf t) t.body)
    (names : ∀ p ∈ t.wires, Allocated p.name)
    (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true) :
    ∀ x r, Stmt.assign x r ∈ (closeMachine lay t).body → x ≠ "rst" ∧ x ≠ "clk" := by
  have hpw : packedWire? t.body = some w := by simp [packedWire?, hbody]
  have hdrop : t.body.dropLast = B := by simp [hbody]
  intro x r hx
  have hM : (closeMachine lay t).body = B ++
      nextAssigns w (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots ++
      registers lay.resetKind (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots ++
      outAssigns w lay.outs := by
    simp [closeMachine, hpw, hdrop]
  rw [hM] at hx
  simp only [List.mem_append] at hx
  rcases hx with ((hB | hN) | hR) | hO
  · obtain ⟨l, e, n, he, ht, hl⟩ := typed _ (by rw [hbody]; exact List.mem_append_left _ hB)
    cases he
    rcases hl with hl | rfl
    · have hpos : 0 < weOf t x := by rw [hl]; exact ht.positive
      have halloc : Allocated x := by
        unfold weOf at hpos
        cases hf : t.wires.find? (fun p => p.name == x) with
        | none => rw [hf] at hpos; simp at hpos
        | some p =>
          have hx := List.find?_some hf
          simp only [beq_iff_eq] at hx
          exact hx ▸ names p (List.mem_of_find?_eq_some hf)
      exact ⟨fun h => Tools.ShippingRegisterSoundness.not_allocated_rst (h ▸ halloc),
        fun h => not_allocated_clk (h ▸ halloc)⟩
    · exact ⟨by decide, by decide⟩
  · obtain ⟨p, f, he⟩ := nextAssigns_mem w _ _ _ hN
    cases he
    exact ⟨nextName_ne_rst _, nextName_ne_clk _⟩
  · obtain ⟨k, p, f, _, _, he⟩ := registers_mem _ _ _ _ hR
    cases he
  · simp only [outAssigns, List.mem_map] at hO
    obtain ⟨o, ho, he⟩ := hO
    cases he
    have hok := (outsOk o ho).2
    simp only [outNameOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
    exact ⟨hok.1.2, hok.2⟩

/-! ## Modules with instances -/

/-- A fold over ports decides the entry of a name it contains, whatever the
start. -/
theorem wmFold_indep (ports : List Port) :
    ∀ (acc acc' : Sparkle.IR.Optimize.WidthMap) (x : String), x ∈ ports.map (·.name) →
      (ports.foldl (fun acc p => acc.insert p.name p.ty.bitWidth) acc).get? x =
        (ports.foldl (fun acc p => acc.insert p.name p.ty.bitWidth) acc').get? x := by
  induction ports with
  | nil => intro _ _ _ h; cases h
  | cons q rest ih =>
    intro acc acc' x hx
    simp only [List.foldl_cons]
    by_cases hr : x ∈ rest.map (·.name)
    · exact ih _ _ x hr
    · rw [Tools.ShippingPostSoundness.wmFold_notin rest _ x hr,
        Tools.ShippingPostSoundness.wmFold_notin rest _ x hr]
      have hq : x = q.name := by
        rcases List.mem_cons.mp (by simpa using hx : x ∈ q.name :: rest.map (·.name)) with h | h
        · exact h
        · exact absurd h hr
      subst hq
      simp

/-- **Width maps of a module and its closed transition agree off the clock and
reset**, when they share wires and outputs and the module's inputs are the
transition's (some dropped) and the clock and reset. -/
theorem buildWidthMap_agree {M m : Module} (hw : m.wires = M.wires) (ho : m.outputs = M.outputs)
    (hin : ∀ p ∈ m.inputs, p ∈ M.inputs ∨ p.name = "clk" ∨ p.name = "rst")
    (hinW : ∀ p ∈ M.inputs, p ∈ M.wires ∨ p.name = "clk" ∨ p.name = "rst") :
    ∀ x, x ≠ "clk" → x ≠ "rst" →
      (Sparkle.IR.Optimize.buildWidthMap m).get? x =
        (Sparkle.IR.Optimize.buildWidthMap M).get? x := by
  intro x hc hr
  simp only [Sparkle.IR.Optimize.buildWidthMap]
  rw [hw, ho]
  by_cases hxw : x ∈ M.wires.map (·.name)
  · exact wmFold_indep M.wires _ _ x hxw
  · rw [Tools.ShippingPostSoundness.wmFold_notin M.wires _ x hxw,
      Tools.ShippingPostSoundness.wmFold_notin M.wires _ x hxw]
    by_cases hxo : x ∈ M.outputs.map (·.name)
    · exact wmFold_indep M.outputs _ _ x hxo
    · rw [Tools.ShippingPostSoundness.wmFold_notin M.outputs _ x hxo,
        Tools.ShippingPostSoundness.wmFold_notin M.outputs _ x hxo]
      have hxM : x ∉ M.inputs.map (·.name) := by
        intro hm
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
        rcases hinW p hp with h | h | h
        · exact hxw (List.mem_map_of_mem h)
        · exact hc h
        · exact hr h
      have hxm : x ∉ m.inputs.map (·.name) := by
        intro hm
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
        rcases hin p hp with h | h | h
        · exact hxM (List.mem_map_of_mem h)
        · exact hc h
        · exact hr h
      rw [Tools.ShippingPostSoundness.wmFold_notin m.inputs _ x hxm,
        Tools.ShippingPostSoundness.wmFold_notin M.inputs _ x hxM]

/-- An instance statement connected by plain wires is kept by the cleanup. -/
theorem dz_inst_refs (wm : Sparkle.IR.Optimize.WidthMap) (mn i : String)
    (conns : List (String × Expr)) (h : ∀ c ∈ conns, ∃ w, c.2 = .ref w) :
    Sparkle.IR.ZeroWidth.dzStmt wm (.inst mn i conns) = some (.inst mn i conns) := by
  simp only [Sparkle.IR.ZeroWidth.dzStmt, Option.some.injEq, Stmt.inst.injEq, true_and]
  conv => rhs; rw [← List.map_id conns]
  apply List.map_congr_left
  intro c hc
  obtain ⟨w, hw⟩ := h c hc
  obtain ⟨k, e⟩ := c
  simp only at hw
  subst hw
  simp [Sparkle.IR.ZeroWidth.dzExpr]

/-- **The cleanup keeps a module with instances**: its statements are its
closed transition's (each kept under any width map agreeing off the clock and
reset) and instance statements connected by plain wires. -/
theorem calls_cleanup {M m : Module}
    (hfixM : ∀ wm : Sparkle.IR.Optimize.WidthMap, (∀ x, x ≠ "clk" → x ≠ "rst" →
      wm.get? x = (Sparkle.IR.Optimize.buildWidthMap M).get? x) →
      ∀ st ∈ M.body, Sparkle.IR.ZeroWidth.dzStmt wm st = some st)
    (L : List Stmt) (hL : ∀ st ∈ L, ∃ mn i conns, st = .inst mn i conns ∧
      ∀ c ∈ conns, ∃ w, c.2 = .ref w)
    (hperm : (M.body ++ L).Perm m.body) (hw : m.wires = M.wires) (ho : m.outputs = M.outputs)
    (hin : ∀ p ∈ m.inputs, p ∈ M.inputs ∨ p.name = "clk" ∨ p.name = "rst")
    (hinW : ∀ p ∈ M.inputs, p ∈ M.wires ∨ p.name = "clk" ∨ p.name = "rst")
    (hndM : (M.wires.map Port.name).Nodup) :
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).inputs = m.inputs ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).outputs = m.outputs := by
  have hagree := buildWidthMap_agree hw ho hin hinW
  have hnd : (m.wires.map Port.name).Nodup := by rw [hw]; exact hndM
  unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨?_, Tools.ShippingPostSoundness.weOf_dropWires _ hnd, rfl, rfl⟩
  apply Tools.ShippingPostSoundness.filterMap_eq_self
  intro st hst
  rcases List.mem_append.mp (hperm.mem_iff.mpr hst) with h | h
  · exact hfixM _ hagree st h
  · obtain ⟨mn, i, conns, rfl, hc⟩ := hL st h
    exact dz_inst_refs _ mn i conns hc

end Tools.ShippingMachineCleanup
