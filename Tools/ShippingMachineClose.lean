import Tools.ShippingRegisterSoundness
import Sparkle.IR.Machine

/-! # One cycle of a closed machine

`Sparkle.IR.Machine.closeMachine` turns a combinational transition module —
slot values in, packed output-and-next-values out — into the sequential
module with one register per slot. This file proves what one cycle of the
closed module does, from what the transition module computes: if the
transition's assignments evaluate with packed value `P`, the closed module
steps every slot register to its field of `P` and drives `out` with the
output field. The statement is about the IR semantics only. -/
namespace Tools.ShippingMachineClose
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingTypedExprSoundness
open Tools.ShippingTypedPostSoundness Tools.ShippingRegisterSoundness
open Sparkle.IR.NameHints (Allocated)

/-- Two lists related element by element. -/
inductive Zip₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Zip₂ R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → Zip₂ R as bs → Zip₂ R (a :: as) (b :: bs)

theorem Zip₂.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {as : List α} {bs : List β}, Zip₂ R as bs → Zip₂ S as bs
  | _, _, .nil => .nil
  | _, _, .cons hab rest => .cons (h _ _ hab) (Zip₂.imp h rest)

theorem Zip₂.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Zip₂ R as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ rest => by simp [rest.length_eq]

theorem Zip₂.get {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Zip₂ R as bs →
      ∀ (i : Nat) (a : α) (b : β), as[i]? = some a → bs[i]? = some b → R a b
  | _, _, .cons hab _, 0, a, b, ha, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb
    subst ha; subst hb; exact hab
  | _, _, .cons _ rest, i + 1, a, b, ha, hb => by
    simp only [List.getElem?_cons_succ] at ha hb
    exact rest.get i a b ha hb
  | _, _, .nil, _, _, _, ha, _ => by simp at ha

theorem Zip₂.of_get {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, as.length = bs.length →
      (∀ (i : Nat) (a : α) (b : β), as[i]? = some a → bs[i]? = some b → R a b) → Zip₂ R as bs
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, h, hr =>
    .cons (hr 0 a b rfl rfl)
      (Zip₂.of_get (by simpa using h) (fun i a' b' ha hb => hr (i + 1) a' b' (by simpa using ha)
        (by simpa using hb)))

theorem Zip₂.map_left {α β γ : Type} {R : γ → β → Prop} (f : α → γ) :
    ∀ {as : List α} {bs : List β}, Zip₂ (fun a b => R (f a) b) as bs → Zip₂ R (as.map f) bs
  | _, _, .nil => .nil
  | _, _, .cons hab rest => .cons hab (Zip₂.map_left f rest)

/-- A written name of an assignment-only body is the target of one of its
assignments. -/
theorem assign_of_writes {z : String} :
    ∀ {body : List Stmt}, (∀ st ∈ body, ∃ l r, st = .assign l r) →
      z ∈ Sparkle.IR.Reorder.writesOf body → ∃ r, Stmt.assign z r ∈ body
  | [], _, h => by simp [Sparkle.IR.Reorder.writesOf] at h
  | st :: rest, hs, h => by
    obtain ⟨l, r, rfl⟩ := hs st List.mem_cons_self
    simp only [Sparkle.IR.Reorder.writesOf, List.flatMap_cons,
      Sparkle.IR.Reorder.stmtWrites, List.cons_append, List.nil_append,
      List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨r, List.mem_cons_self⟩
    · obtain ⟨r', hr'⟩ := assign_of_writes (fun st hm => hs st (List.mem_cons_of_mem _ hm))
        (by simpa [Sparkle.IR.Reorder.writesOf] using h)
      exact ⟨r', List.mem_cons_of_mem _ hr'⟩

/-! ## Names -/

theorem nextName_not_allocated (s : String) : ¬ Allocated (nextName s) := by
  intro h
  have hd := h.2
  have : (nextName s).toList.head? = some 'n' := by
    simp [nextName, String.toList_append]
  rw [this] at hd
  cases hd

theorem nextName_inj {a b : String} (h : nextName a = nextName b) : a = b := by
  unfold nextName at h
  exact String.append_right_inj _ |>.mp h

theorem nextName_ne_out (s : String) : nextName s ≠ "out" := by
  intro h
  have : (nextName s).toList.head? = some 'n' := by
    simp [nextName, String.toList_append]
  rw [h] at this
  revert this
  decide

/-! ## Widths of the closed module -/

/-- A name with a positive width is a declared wire, and appending wires
does not change what it is declared as. -/
theorem weOf_wires_append {m m' : Module} {extra : List Port} {x : String}
    (hw : m'.wires = m.wires ++ extra) (hx : 0 < weOf m x) : weOf m' x = weOf m x := by
  unfold weOf at hx ⊢
  rw [hw, List.find?_append]
  cases h : m.wires.find? (fun p => p.name == x) with
  | none => rw [h] at hx; simp at hx
  | some p => simp

/-- Width environments agreeing on every referenced name evaluate an
assignment-only body identically. -/
theorem evalAssigns_we_congr_assigns {we we' : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt}, (∀ st ∈ body, ∃ l r, st = .assign l r) →
      (∀ l r, Stmt.assign l r ∈ body → ∀ n ∈ Sparkle.IR.Reorder.refsOf r, we n = we' n) →
      ∀ env, evalAssigns we mems body env = evalAssigns we' mems body env
  | [], _, _, _ => rfl
  | st :: rest, hs, hw, env => by
    obtain ⟨l, r, rfl⟩ := hs st List.mem_cons_self
    have hr : evalExpr we env r = evalExpr we' env r :=
      Tools.ConeFold.evalExpr_we_congr we we' env r (hw l r List.mem_cons_self)
    show (evalExpr we env r).bind _ = (evalExpr we' env r).bind _
    rw [hr]
    cases evalExpr we' env r with
    | none => rfl
    | some v =>
      simp only [Option.bind_some]
      exact evalAssigns_we_congr_assigns (fun st hm => hs st (List.mem_cons_of_mem _ hm))
        (fun l r hm => hw l r (List.mem_cons_of_mem _ hm)) _

/-! ## The appended statements -/

/-- The relation between the slot ports and their fields: the register's
declared width is the field's width, and fields are not empty. -/
def SlotOk (we : WEnv) (p : Port) (f : SlotField) : Prop :=
  we p.name = f.width ∧ 0 < f.width

theorem fieldRhs_eval (we : WEnv) (env : Env) (w : String) (lo width : Nat) (hw : 0 < width) :
    evalExpr we env (fieldRhs w lo width) = some (mask width (env w >>> lo)) := by
  have h : lo + width - 1 - lo + 1 = width := by omega
  simp [fieldRhs, evalExpr, h]

/-- The values the slot registers step to: each slot's field of `P`. -/
def slotNexts (P : Nat) : List Port → List SlotField → List (String × Nat)
  | p :: ps, f :: fs => (p.name, mask f.width (P >>> f.lo)) :: slotNexts P ps fs
  | _, _ => []

/-- Reading the next values off the packed wire: every `next` wire holds its
field, and nothing else changes. -/
theorem nextAssigns_eval {we : WEnv} {mems : MEnv} {w : String} :
    ∀ {ps : List Port} {fs : List SlotField} (env : Env),
      Zip₂ (SlotOk we) ps fs → (ps.map Port.name).Nodup →
      (∀ p ∈ ps, nextName p.name ≠ w) →
      ∃ env', evalAssigns we mems (nextAssigns w ps fs) env = some env' ∧
        (∀ z, (∀ p ∈ ps, z ≠ nextName p.name) → env' z = env z) ∧
        Zip₂ (fun p f => env' (nextName p.name) = mask f.width (env w >>> f.lo)) ps fs
  | [], [], env, _, _, _ => ⟨env, rfl, fun _ _ => rfl, .nil⟩
  | p :: ps, f :: fs, env, .cons hpf hrest, hnd, hw => by
    have hnd' : (ps.map Port.name).Nodup := (List.nodup_cons.mp hnd).2
    have hnotin : p.name ∉ ps.map Port.name := (List.nodup_cons.mp hnd).1
    have hwp : nextName p.name ≠ w := hw p List.mem_cons_self
    obtain ⟨env', hev, hframe, hvals⟩ := nextAssigns_eval (we := we) (mems := mems) (w := w)
      (fun n => if n = nextName p.name then mask f.width (env w >>> f.lo) else env n)
      hrest hnd' (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    refine ⟨env', ?_, ?_, ?_⟩
    · simp only [nextAssigns, evalAssigns, fieldRhs_eval we env w f.lo f.width hpf.2, bind,
        Option.bind]
      exact hev
    · intro z hz
      rw [hframe z (fun q hq => hz q (List.mem_cons_of_mem _ hq))]
      simp [hz p List.mem_cons_self]
    · refine .cons ?_ ?_
      · rw [hframe (nextName p.name) (fun q hq heq => hnotin (by
          rw [nextName_inj heq]; exact List.mem_map_of_mem hq))]
        simp
      · exact hvals.imp (fun q g h => by rw [h]; simp [Ne.symm hwp])

theorem nextAssigns_assigns (w : String) :
    ∀ (ps : List Port) (fs : List SlotField),
      ∀ st ∈ nextAssigns w ps fs, ∃ l r, st = .assign l r
  | [], _, st, h => by cases h
  | _ :: _, [], st, h => by cases h
  | p :: ps, f :: fs, st, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, _, rfl⟩
    · exact nextAssigns_assigns w ps fs st h

/-- The registers step each slot to the value of its `next` wire. -/
theorem registers_nexts {we : WEnv} {mems : MEnv} {rk : ResetKind} {env : Env} {P : Nat}
    {tail : List Stmt} (hrst : env "rst" = 0) (htail : regNexts we mems tail env = some []) :
    ∀ {ps : List Port} {fs : List SlotField}, Zip₂ (SlotOk we) ps fs →
      Zip₂ (fun p f => env (nextName p.name) = mask f.width (P >>> f.lo)) ps fs →
      regNexts we mems (registers rk ps fs ++ tail) env = some (slotNexts P ps fs)
  | [], [], _, _ => by simpa [registers, slotNexts] using htail
  | p :: ps, f :: fs, .cons hpf hrest, .cons hv hvs => by
    have ih := registers_nexts (we := we) (mems := mems) (rk := rk) (P := P) hrst htail hrest hvs
    simp only [registers, List.cons_append, regNexts, evalExpr, bind, Option.bind, ih, hrst,
      ne_eq, not_true_eq_false, if_false, slotNexts, hpf.1, hv]
    simp [mask]

theorem registers_evalAssigns {we : WEnv} {mems : MEnv} {rk : ResetKind} :
    ∀ (ps : List Port) (fs : List SlotField) (tail : List Stmt) (env : Env),
      evalAssigns we mems (registers rk ps fs ++ tail) env = evalAssigns we mems tail env
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: ps, _ :: fs, tail, env => registers_evalAssigns ps fs tail env

theorem registers_seq (rk : ResetKind) :
    ∀ (ps : List Port) (fs : List SlotField), SeqBody (registers rk ps fs)
  | [], _, st, h => by cases h
  | _ :: _, [], st, h => by cases h
  | p :: ps, f :: fs, st, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr ⟨_, _, _, _, _, rfl⟩
    · exact registers_seq rk ps fs st h

/-! ## The output ports -/

/-- An accepted output name is none of the closed module's own names. -/
theorem outNameOk_facts {s : String} (h : outNameOk s = true) :
    ¬ Allocated s ∧ s ≠ "rst" ∧ ∀ x, s ≠ nextName x := by
  simp only [outNameOk, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hhead, hnext⟩, hrst⟩, _⟩ := h
  refine ⟨fun ha => hhead ha.2, hrst, ?_⟩
  intro x heq
  have : ("next".toList).isPrefixOf s.toList = true := by
    rw [heq, nextName, String.toList_append]
    exact List.isPrefixOf_iff_prefix.mpr (List.prefix_append _ _)
  rw [this] at hnext
  cases hnext

/-- Driving the output ports: every port holds its field, and nothing else
changes. -/
theorem outAssigns_eval {we : WEnv} {mems : MEnv} {w : String} :
    ∀ (outs : List OutField) (env : Env),
      (∀ o ∈ outs, 0 < o.width ∧ o.name ≠ w) → (outs.map (·.name)).Nodup →
      ∃ env', evalAssigns we mems (outAssigns w outs) env = some env' ∧
        (∀ z, z ∉ outs.map (·.name) → env' z = env z) ∧
        ∀ o ∈ outs, env' o.name = mask o.width (env w >>> o.lo)
  | [], env, _, _ => ⟨env, rfl, fun _ _ => rfl, fun o ho => by cases ho⟩
  | o :: outs, env, hok, hnd => by
    have hnd' : (outs.map (·.name)).Nodup := (List.nodup_cons.mp hnd).2
    have hnotin : o.name ∉ outs.map (·.name) := (List.nodup_cons.mp hnd).1
    obtain ⟨hpos, hne⟩ := hok o List.mem_cons_self
    obtain ⟨env', hev, hframe, hvals⟩ := outAssigns_eval (we := we) (mems := mems) (w := w) outs
      (fun n => if n = o.name then mask o.width (env w >>> o.lo) else env n)
      (fun q hq => hok q (List.mem_cons_of_mem _ hq)) hnd'
    refine ⟨env', ?_, ?_, ?_⟩
    · simp only [outAssigns, List.map_cons, evalAssigns, fieldRhs_eval we env w o.lo o.width hpos,
        bind, Option.bind]
      exact hev
    · intro z hz
      simp only [List.map_cons, List.mem_cons, not_or] at hz
      rw [hframe z hz.2]
      simp [hz.1]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [hframe _ hnotin]; simp
      · rw [hvals q hq]
        simp [Ne.symm hne]

theorem outAssigns_assigns (w : String) (outs : List OutField) :
    ∀ st ∈ outAssigns w outs, ∃ l r, st = .assign l r := by
  intro st hs
  simp only [outAssigns, List.mem_map] at hs
  obtain ⟨o, _, rfl⟩ := hs
  exact ⟨_, _, rfl⟩

/-! ## The closed module -/

/-- **One cycle of the closed machine.** The transition module `t` ends in
`assign out = w` and, on the cycle's environment, its assignments evaluate
to `result` — so the packed transition value is `result "out"`. Then the
closed module, on the same environment with reset low, steps every slot
register to its field of that value and drives `out` with the output
field. -/
theorem closeMachine_step {t : Module} {lay : Layout} {B : List Stmt} {w : String}
    {env0 result : Env} {mems : MEnv}
    (hbody : t.body = B ++ [.assign "out" (.ref w)])
    (typed : TypedStmts (weOf t) t.body)
    (names : ∀ p ∈ t.wires, Allocated p.name)
    (inWires : ∀ p ∈ t.inputs, p ∈ t.wires)
    (inNodup : (t.inputs.map Port.name).Nodup)
    (slots : Zip₂ (SlotOk (weOf t))
      (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots)
    (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (lay.outs.map (·.name)).Nodup)
    (hres : evalAssigns (weOf t) mems t.body env0 = some result)
    (hrst : env0 "rst" = 0) :
    ∃ envF, stepModule (weOf (closeMachine lay t)) (closeMachine lay t).body env0 mems =
        some (envF,
          slotNexts (result "out") (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots,
          mems) ∧
      (∀ o ∈ lay.outs, envF o.name = mask o.width (result "out" >>> o.lo)) ∧
      -- every other wire keeps the transition's value
      ∀ z, z ≠ "out" → (∀ x, z ≠ nextName x) → z ∉ lay.outs.map (·.name) →
        envF z = result z := by
  -- Shape of the closed module.
  have hpw : packedWire? t.body = some w := by
    simp [packedWire?, hbody]
  have hdrop : t.body.dropLast = B := by simp [hbody]
  generalize hps : t.inputs.drop (t.inputs.length - lay.slots.length) = ps at slots ⊢
  have hbodyM : (closeMachine lay t).body = B ++ nextAssigns w ps lay.slots ++
      registers lay.resetKind ps lay.slots ++ outAssigns w lay.outs := by
    simp [closeMachine, hpw, hdrop, hps]
  have hwiresM : (closeMachine lay t).wires =
      t.wires ++ ps.map fun p => { name := nextName p.name, ty := p.ty } := by
    simp [closeMachine, hpw, hps]
  -- Facts about the transition's assignments.
  have hBassign : ∀ st ∈ B, ∃ l r, st = .assign l r := by
    intro st hs
    obtain ⟨l, e, n, rfl, _⟩ := typed st (by rw [hbody]; exact List.mem_append_left _ hs)
    exact ⟨l, e, rfl⟩
  have hBseq : SeqBody B := fun st hs => Or.inl (hBassign st hs)
  have hpos : ∀ l r, Stmt.assign l r ∈ B → ∀ n ∈ Sparkle.IR.Reorder.refsOf r, 0 < weOf t n := by
    intro l r hs n hn
    obtain ⟨l', e, k, heq, ht, _⟩ := typed _ (by rw [hbody]; exact List.mem_append_left _ hs)
    cases heq
    exact ht.refs_positive n hn
  have hwpos : 0 < weOf t w := by
    obtain ⟨l', e, k, heq, ht, _⟩ := typed (.assign "out" (.ref w)) (by rw [hbody]; simp)
    cases heq
    exact ht.refs_positive w (by simp [Sparkle.IR.Reorder.refsOf])
  have wireOf : ∀ x, 0 < weOf t x → ∃ p ∈ t.wires, p.name = x := by
    intro x hx
    unfold weOf at hx
    cases h : t.wires.find? (fun p => p.name == x) with
    | none => rw [h] at hx; simp at hx
    | some p =>
      exact ⟨p, List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩
  have allocOf : ∀ x, 0 < weOf t x → Allocated x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := wireOf x hx
    exact names p hp
  -- The transition's evaluation splits at the final assignment.
  rw [hbody, evalAssigns_append hBseq] at hres
  cases hB : evalAssigns (weOf t) mems B env0 with
  | none => rw [hB] at hres; cases hres
  | some envB =>
    rw [hB] at hres
    have hresult : result = fun n => if n = "out" then envB w else envB n := by
      have : evalAssigns (weOf t) mems [.assign "out" (.ref w)] envB =
          some (fun n => if n = "out" then envB w else envB n) := by
        simp [evalAssigns, evalExpr]
      simp only [Option.bind_some] at hres
      rw [this] at hres
      exact (Option.some.inj hres).symm
    have hP : result "out" = envB w := by rw [hresult]; simp
    -- Same evaluation under the closed module's widths.
    have hBM : evalAssigns (weOf (closeMachine lay t)) mems B env0 = some envB := by
      rw [← hB]
      symm
      apply evalAssigns_we_congr_assigns hBassign
      intro l r hs n hn
      exact (weOf_wires_append hwiresM (hpos l r hs n hn)).symm
    -- Slot facts under the closed module's widths.
    have psWires : ∀ p ∈ ps, p ∈ t.wires := by
      intro p hp
      exact inWires p (List.mem_of_mem_drop (hps ▸ hp))
    have slotsM : Zip₂ (SlotOk (weOf (closeMachine lay t))) ps lay.slots := by
      refine slots.imp (fun p f h => ?_)
      have hp : 0 < weOf t p.name := by rw [h.1]; exact h.2
      exact ⟨by rw [weOf_wires_append hwiresM hp]; exact h.1, h.2⟩
    have psNodup : (ps.map Port.name).Nodup := by
      rw [← hps, List.map_drop]
      exact inNodup.sublist (List.drop_sublist _ _)
    have nextNeW : ∀ p ∈ ps, nextName p.name ≠ w := by
      intro p _ heq
      exact nextName_not_allocated p.name (heq ▸ allocOf w hwpos)
    obtain ⟨envN, hN, frameN, valsN⟩ := nextAssigns_eval (we := weOf (closeMachine lay t))
      (mems := mems) (w := w) envB slotsM psNodup nextNeW
    have hNw : envN w = envB w :=
      frameN w (fun p hp heq => nextNeW p hp heq.symm)
    -- Reset is not written by the transition.
    have hBrst : envB "rst" = env0 "rst" := by
      apply evalAssigns_preserved hBseq hB
      intro hmem
      have := assign_of_writes hBassign hmem
      obtain ⟨r, hr⟩ := this
      obtain ⟨l', e, k, heq, ht, hl⟩ := typed _ (by rw [hbody]; exact List.mem_append_left _ hr)
      cases heq
      rcases hl with hl | hl
      · exact not_allocated_rst (allocOf "rst" (by rw [hl]; exact ht.positive))
      · exact absurd hl (by decide)
    have hNrst : envN "rst" = 0 := by
      rw [frameN "rst" (fun p _ heq => by
        have : (nextName p.name).toList.head? = some 'n' := by
          simp [nextName, String.toList_append]
        rw [← heq] at this
        revert this
        decide), hBrst, hrst]
    -- The output ports.
    have outsW : ∀ o ∈ lay.outs, 0 < o.width ∧ o.name ≠ w := fun o ho =>
      ⟨(outsOk o ho).1, fun heq =>
        (outNameOk_facts (outsOk o ho).2).1 (heq ▸ allocOf w hwpos)⟩
    obtain ⟨envF, hF, frameF, valsO⟩ := outAssigns_eval (we := weOf (closeMachine lay t))
      (mems := mems) (w := w) lay.outs envN outsW outsNodup
    refine ⟨envF, ?_, fun o ho => by rw [valsO o ho, hNw, hP], fun z hz hnx hzo => ?_⟩
    rotate_left
    · rw [frameF z hzo, frameN z (fun p _ heq => hnx p.name heq), hresult]
      simp [hz]
    have nextSeq : SeqBody (nextAssigns w ps lay.slots) :=
      fun st hs => Or.inl (nextAssigns_assigns w ps lay.slots st hs)
    have evalM : evalAssigns (weOf (closeMachine lay t)) mems (closeMachine lay t).body env0 =
        some envF := by
      rw [hbodyM, List.append_assoc, List.append_assoc, evalAssigns_append hBseq, hBM]
      simp only [Option.bind_some]
      rw [evalAssigns_append nextSeq, hN]
      simp only [Option.bind_some]
      rw [registers_evalAssigns]
      exact hF
    have notNext : ∀ x, nextName x ∉ lay.outs.map (·.name) := by
      intro x hmem
      obtain ⟨o, ho, heq⟩ := List.mem_map.mp hmem
      exact (outNameOk_facts (outsOk o ho).2).2.2 x heq
    have valsF : Zip₂ (fun p f =>
        envF (nextName p.name) = mask f.width (result "out" >>> f.lo)) ps lay.slots := by
      refine valsN.imp (fun p f h => ?_)
      rw [frameF _ (notNext p.name), h, hP]
    have hFrst : envF "rst" = 0 := by
      rw [frameF "rst" (fun hmem => by
        obtain ⟨o, ho, heq⟩ := List.mem_map.mp hmem
        exact (outNameOk_facts (outsOk o ho).2).2.1 heq), hNrst]
    have regsM : regNexts (weOf (closeMachine lay t)) mems (closeMachine lay t).body envF =
        some (slotNexts (result "out") ps lay.slots) := by
      rw [hbodyM, List.append_assoc, List.append_assoc,
        regNexts_skip_assigns hBassign,
        regNexts_skip_assigns (nextAssigns_assigns w ps lay.slots)]
      refine registers_nexts hFrst ?_ slotsM valsF
      have := regNexts_skip_assigns (we := weOf (closeMachine lay t)) (mems := mems) (env := envF)
        (b2 := []) (outAssigns_assigns w lay.outs)
      rw [List.append_nil] at this
      rw [this]; rfl
    have seqM : SeqBody (closeMachine lay t).body := by
      rw [hbodyM]
      intro st hs
      simp only [List.mem_append] at hs
      rcases hs with ((hs | hs) | hs) | hs
      · exact hBseq st hs
      · exact nextSeq st hs
      · exact registers_seq _ _ _ st hs
      · exact Or.inl (outAssigns_assigns w lay.outs st hs)
    unfold stepModule
    simp [evalM, regsM, memNexts_seq seqM, bind]

/-! ## Hardware `let`s -/

open Tools.ShippingSettledSoundness in
theorem acyclic_last_fresh {l : String} {e : Expr} :
    ∀ {B : List Stmt}, Acyclic (B ++ [.assign l e]) → l ∉ Sparkle.IR.Reorder.writesOf B
  | [], _ => by simp [Sparkle.IR.Reorder.writesOf]
  | _ :: rest, h => by
    cases h with
    | cons target reads tail =>
      have ih := acyclic_last_fresh tail
      intro hm
      simp only [Sparkle.IR.Reorder.writesOf, List.flatMap_cons,
        Sparkle.IR.Reorder.stmtWrites, List.cons_append, List.nil_append, List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact target (by simp [Sparkle.IR.Reorder.writesOf, Sparkle.IR.Reorder.stmtWrites])
      · exact ih (by simpa [Sparkle.IR.Reorder.writesOf] using hm)

theorem mem_aliasesOf {aliases : List (Port × String)} {st s : Stmt}
    (h : s ∈ aliasesOf aliases st) : ∃ pa ∈ aliases, s = aliasStmt pa.1 pa.2 := by
  cases st with
  | assign l r =>
    simp only [aliasesOf, List.mem_map, List.mem_filter] at h
    obtain ⟨pa, ⟨hpa, _⟩, rfl⟩ := h
    exact ⟨pa, hpa, rfl⟩
  | _ => simp [aliasesOf] at h

theorem mem_insertAliases {aliases : List (Port × String)} {s : Stmt} :
    ∀ {B : List Stmt}, s ∈ insertAliases aliases B →
      s ∈ B ∨ ∃ pa ∈ aliases, s = aliasStmt pa.1 pa.2
  | [], h => by simp [insertAliases] at h
  | st :: rest, h => by
    simp only [insertAliases, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact Or.inl List.mem_cons_self
    · exact Or.inr (mem_aliasesOf h)
    · rcases mem_insertAliases h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

theorem insertAliases_keeps {aliases : List (Port × String)} {s : Stmt} :
    ∀ {B : List Stmt}, s ∈ B → s ∈ insertAliases aliases B
  | st :: rest, h => by
    simp only [insertAliases, List.mem_cons, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (insertAliases_keeps h))

/-- Every alias is placed: in front when no statement drives its operand
wire, after the driving statement otherwise. -/
theorem alias_placed {aliases : List (Port × String)} {pa : Port × String}
    (hpa : pa ∈ aliases) {B : List Stmt} (hB : ∀ st ∈ B, ∃ l r, st = .assign l r) :
    aliasStmt pa.1 pa.2 ∈ frontAliases aliases B ++ insertAliases aliases B := by
  by_cases hw : pa.2 ∈ Sparkle.IR.Reorder.writesOf B
  · refine List.mem_append_right _ ?_
    obtain ⟨r, hr⟩ := assign_of_writes hB hw
    clear hw hB
    induction B with
    | nil => cases hr
    | cons st rest ih =>
      simp only [insertAliases, List.mem_cons, List.mem_append]
      rcases List.mem_cons.mp hr with rfl | hr
      · refine Or.inr (Or.inl ?_)
        simp only [aliasesOf, List.mem_map, List.mem_filter]
        exact ⟨pa, ⟨hpa, by simp⟩, rfl⟩
      · exact Or.inr (Or.inr (ih hr))
  · refine List.mem_append_left _ ?_
    simp only [frontAliases, List.mem_map, List.mem_filter]
    exact ⟨pa, ⟨hpa, by simpa using hw⟩, rfl⟩

theorem mem_frontAliases {aliases : List (Port × String)} {B : List Stmt} {s : Stmt}
    (h : s ∈ frontAliases aliases B) : ∃ pa ∈ aliases, s = aliasStmt pa.1 pa.2 := by
  simp only [frontAliases, List.mem_map, List.mem_filter] at h
  obtain ⟨pa, ⟨hpa, _⟩, rfl⟩ := h
  exact ⟨pa, hpa, rfl⟩

theorem weOf_eq_wireWidth (t : Module) : weOf t = wireWidth t.wires := rfl

theorem eq_dropLast_append {α : Type} : ∀ (l : List α) (a : α), l.getLast? = some a →
    l = l.dropLast ++ [a]
  | [], _, h => by simp at h
  | [x], a, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    simp [h]
  | x :: y :: rest, a, h => by
    have ih := eq_dropLast_append (y :: rest) a (by simpa [List.getLast?_cons_cons] using h)
    simp only [List.dropLast_cons₂, List.cons_append]
    rw [← ih]

theorem mem_writesOf_of_assign {l : String} {r : Expr} :
    ∀ {body : List Stmt}, Stmt.assign l r ∈ body → l ∈ Sparkle.IR.Reorder.writesOf body
  | st :: rest, h => by
    simp only [Sparkle.IR.Reorder.writesOf, List.flatMap_cons, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl (by simp [Sparkle.IR.Reorder.stmtWrites])
    · exact Or.inr (by simpa [Sparkle.IR.Reorder.writesOf] using mem_writesOf_of_assign h)

set_option maxHeartbeats 1000000 in
open Tools.ShippingSettledSoundness in
/-- **Closing the `let`s.** The transition module `t`, evaluated on an
environment `envS` whose `let` ports already hold the values of their
fields' operand wires, gives `R`. Then the module with the `let` ports
driven by those wires, evaluated on ANY environment that agrees with `envS`
off the `let` ports, gives the same values, with `out` carrying the wire of
what remains after the `let` fields. -/
theorem closeLets_eval {t t' : Module} {K : Nat} {env0 envS R : Env} {mems : MEnv}
    {w : String} {aliases : List (Port × String)} {core : String}
    (hK : K ≠ 0)
    (hclose : closeLets K t = some t')
    (hpw : packedWire? t.body = some w)
    (hops : letOperands t.body (t.inputs.drop (t.inputs.length - K)) w = some (aliases, core))
    (acyclic : Acyclic t.body)
    (typed : TypedStmts (weOf t) t.body)
    (outZero : weOf t "out" = 0)
    (hrun : evalAssigns (weOf t) mems t.body envS = some R)
    (hpre : ∀ z, (∀ pa ∈ aliases, z ≠ pa.1.name) → envS z = env0 z)
    (hfix : ∀ pa ∈ aliases, envS pa.1.name = mask pa.1.ty.bitWidth (R pa.2)) :
    t'.inputs = t.inputs.take (t.inputs.length - K) ∧ t'.wires = t.wires ∧
    (∃ B', t'.body = B' ++ [.assign "out" (.ref core)]) ∧
    Acyclic t'.body ∧
    ∃ R', evalAssigns (weOf t') mems t'.body env0 = some R' ∧ R' "out" = R core ∧
      ∀ z, z ≠ "out" → R' z = R z := by
  -- The shape of the result.
  unfold closeLets at hclose
  simp only [hK, if_false, hpw, hops] at hclose
  split at hclose
  rotate_left
  · cases hclose
  rename_i hchk
  cases hclose
  simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    decide_eq_true_eq, Bool.not_eq_true'] at hchk
  obtain ⟨⟨hal, hcore⟩, hord⟩ := hchk
  obtain ⟨w', hlast⟩ : ∃ w', t.body = t.body.dropLast ++ [.assign "out" (.ref w')] := by
    refine ⟨w, ?_⟩
    unfold packedWire? at hpw
    split at hpw
    · rename_i w0 hl
      cases hpw
      exact eq_dropLast_append _ _ hl
    · cases hpw
  generalize hB : t.body.dropLast = B at hlast hord ⊢
  have hBsub : ∀ st ∈ B, st ∈ t.body := fun st hs => by
    rw [hlast]; exact List.mem_append_left _ hs
  have hBassign : ∀ st ∈ B, ∃ l r, st = .assign l r := by
    intro st hs
    obtain ⟨l, e, n, rfl, _⟩ := typed st (hBsub st hs)
    exact ⟨l, e, rfl⟩
  have acyclic' := (assignmentOrderCheck_iff _).mp hord
  have eqR := assign_equations acyclic hrun
  have frameR := assign_frame acyclic hrun
  have outFresh : "out" ∉ Sparkle.IR.Reorder.writesOf B := by
    rw [hlast] at acyclic
    exact acyclic_last_fresh acyclic
  refine ⟨rfl, rfl, ⟨_, by rw [List.append_assoc]⟩, by rw [List.append_assoc] at acyclic'; simpa using acyclic', ?_⟩
  -- The solution: `R`, with `out` moved to the remaining wire.
  refine ⟨fun z => if z = "out" then R core else R z, ?_, by simp, fun z hz => by simp [hz]⟩
  show evalAssigns (weOf t) mems _ env0 = _
  apply equations_eval acyclic'
  · -- every equation holds
    intro l r hm
    have aliasEq : ∀ pa ∈ aliases, l = pa.1.name → r = .slice (.ref pa.2) (pa.1.ty.bitWidth - 1) 0 →
        evalExpr (weOf t) (fun z => if z = "out" then R core else R z) r =
          some ((fun z => if z = "out" then R core else R z) l) := by
      intro pa hpa hl hr
      obtain ⟨⟨⟨⟨hwid, hpos⟩, hnameOut⟩, hsrcOut⟩, hfresh⟩ := hal pa hpa
      subst hl; subst hr
      have h1 : pa.1.ty.bitWidth - 1 - 0 + 1 = pa.1.ty.bitWidth := by omega
      have hRname : R pa.1.name = envS pa.1.name := frameR _ (by
        intro hmem
        have : (Sparkle.IR.Reorder.writesOf t.body).contains pa.1.name = true := by
          simpa using hmem
        rw [hfresh] at this
        cases this)
      simp only [evalExpr, hsrcOut, if_false, bind, Option.bind, h1, Nat.shiftRight_zero,
        hnameOut, hRname, hfix pa hpa]
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | hm
    · obtain ⟨pa, hpa, heq⟩ := mem_frontAliases hm
      cases heq
      exact aliasEq pa hpa rfl rfl
    · rcases mem_insertAliases hm with hm | ⟨pa, hpa, heq⟩
      · -- a statement of the transition
        have hlne : l ≠ "out" := fun h => outFresh (h ▸ mem_writesOf_of_assign hm)
        have hrefs : ∀ x ∈ Sparkle.IR.Reorder.refsOf r, x ≠ "out" := by
          intro x hx hxo
          obtain ⟨l', e, n, heq, ht, _⟩ := typed _ (hBsub _ hm)
          cases heq
          have := ht.refs_positive x hx
          rw [hxo, outZero] at this
          exact Nat.lt_irrefl _ this
        rw [Sparkle.IR.Reorder.evalExpr_congr (weOf t) _ R r (fun x hx => by
          simp [hrefs x hx])]
        simp only [hlne, if_false]
        exact eqR l r (hBsub _ hm)
      · cases heq
        exact aliasEq pa hpa rfl rfl
    · cases hm
      simp [evalExpr, hcore]
  · -- names nothing drives keep their value
    intro z hz
    have hzout : z ≠ "out" := by
      intro h
      apply hz
      rw [h]
      apply mem_writesOf_of_assign (r := .ref core)
      simp
    have hzB : z ∉ Sparkle.IR.Reorder.writesOf B := by
      intro hmem
      obtain ⟨r, hr⟩ := assign_of_writes hBassign hmem
      apply hz
      apply mem_writesOf_of_assign (r := r)
      exact List.mem_append_left _ (List.mem_append_right _ (insertAliases_keeps hr))
    have hzal : ∀ pa ∈ aliases, z ≠ pa.1.name := by
      intro pa hpa heq
      apply hz
      rw [heq]
      apply mem_writesOf_of_assign (r := .slice (.ref pa.2) (pa.1.ty.bitWidth - 1) 0)
      exact List.mem_append_left _ (alias_placed hpa hBassign)
    simp only [hzout, if_false]
    rw [frameR z (by
      rw [hlast]
      intro hmem
      simp only [Sparkle.IR.Reorder.writesOf, List.flatMap_append, List.mem_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil,
        Sparkle.IR.Reorder.stmtWrites, List.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · exact hzB (by simpa [Sparkle.IR.Reorder.writesOf] using hmem)
      · exact hzout hmem)]
    exact hpre z hzal

/-- The chain of concatenations `letOperands` walks: `w = {a₁, w₁}`,
`w₁ = {a₂, w₂}`, …, ending in the wire of what remains. -/
inductive LetChain (body : List Stmt) : List (Port × String) → String → String → Prop
  | nil {w : String} : LetChain body [] w w
  | cons {p : Port} {a b w : String} {rest : List (Port × String)} {core : String} :
      Stmt.assign w (.concat [.ref a, .ref b]) ∈ body → LetChain body rest b core →
      LetChain body ((p, a) :: rest) w core

theorem concatParts?_mem {body : List Stmt} {w a b : String}
    (h : concatParts? body w = some (a, b)) :
    Stmt.assign w (.concat [.ref a, .ref b]) ∈ body := by
  obtain ⟨st, hst, hf⟩ := List.exists_of_findSome?_eq_some h
  split at hf
  · rename_i l a' b'
    split at hf
    · rename_i hl
      cases hf
      have : l = w := by simpa using hl
      subst this
      exact hst
    · cases hf
  · cases hf

theorem letOperands_chain {body : List Stmt} :
    ∀ (ps : List Port) (w : String) {al : List (Port × String)} {core : String},
      letOperands body ps w = some (al, core) →
      LetChain body al w core ∧ al.map (·.1) = ps
  | [], w, al, core, h => by
    simp only [letOperands, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.nil, rfl⟩
  | p :: ps, w, al, core, h => by
    unfold letOperands at h
    split at h
    · rename_i a b hc
      split at h
      · rename_i rest core' hr
        cases h
        obtain ⟨hchain, hmap⟩ := letOperands_chain ps b hr
        exact ⟨.cons (concatParts?_mem hc) hchain, by simp [hmap]⟩
      · cases h
    · cases h

/-- What a successful `closeLets` checked. -/
theorem closeLets_some {K : Nat} {t t' : Module} (hK : K ≠ 0) (h : closeLets K t = some t') :
    ∃ w aliases core, packedWire? t.body = some w ∧
      letOperands t.body (t.inputs.drop (t.inputs.length - K)) w = some (aliases, core) ∧
      (∀ pa ∈ aliases, wireWidth t.wires pa.2 = pa.1.ty.bitWidth ∧ 0 < pa.1.ty.bitWidth) ∧
      core ≠ "out" ∧
      (∀ pa ∈ aliases, pa.1.name ≠ "out" ∧
        pa.1.name ∉ Sparkle.IR.Reorder.writesOf t.body) := by
  unfold closeLets at h
  simp only [hK, if_false] at h
  split at h
  · cases h
  · rename_i w hpw
    split at h
    · cases h
    · rename_i aliases core hops
      split at h
      · rename_i hchk
        simp only [Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
          decide_eq_true_eq, Bool.not_eq_true'] at hchk
        refine ⟨w, aliases, core, hpw, hops, fun pa hpa => ⟨(hchk.1.1 pa hpa).1.1.1.1,
          (hchk.1.1 pa hpa).1.1.1.2⟩, hchk.1.2, fun pa hpa => ⟨(hchk.1.1 pa hpa).1.1.2, ?_⟩⟩
        have := (hchk.1.1 pa hpa).2
        simpa using this
      · cases h

/-- The statements of the closed module are typed: the transition's, the
aliases (part-selects of declared operand wires), the final `out`. -/
theorem closeLets_typed {t t' : Module} {K : Nat} {w : String}
    {aliases : List (Port × String)} {core : String}
    (hK : K ≠ 0) (hclose : closeLets K t = some t')
    (hpw : packedWire? t.body = some w)
    (hops : letOperands t.body (t.inputs.drop (t.inputs.length - K)) w = some (aliases, core))
    (typed : TypedStmts (weOf t) t.body)
    (hport : ∀ pa ∈ aliases, weOf t pa.1.name = pa.1.ty.bitWidth)
    (hcore : 0 < weOf t core) :
    TypedStmts (weOf t') t'.body := by
  obtain ⟨w0, al0, core0, hpw0, hops0, hwid, _⟩ := closeLets_some hK hclose
  rw [hpw] at hpw0; cases hpw0
  rw [hops] at hops0; cases hops0
  unfold closeLets at hclose
  simp only [hK, if_false, hpw, hops] at hclose
  split at hclose
  rotate_left
  · cases hclose
  cases hclose
  have aliasTyped : ∀ pa ∈ aliases, ∃ l e n, aliasStmt pa.1 pa.2 = .assign l e ∧
      TypedExpr (weOf t) e n ∧ (weOf t l = n ∨ l = "out") := by
    intro pa hpa
    obtain ⟨hw, hpos⟩ := hwid pa hpa
    have hwa : weOf t pa.2 = pa.1.ty.bitWidth := hw
    refine ⟨pa.1.name, _, pa.1.ty.bitWidth - 1 - 0 + 1, rfl,
      TypedExpr.slice pa.2 (pa.1.ty.bitWidth - 1) 0 (Nat.zero_le _) (by rw [hwa]; omega),
      Or.inl (by rw [hport pa hpa]; omega)⟩
  intro st hs
  show ∃ l e n, st = .assign l e ∧ TypedExpr (weOf t) e n ∧ (weOf t l = n ∨ l = "out")
  simp only [List.mem_append, List.mem_singleton] at hs
  rcases hs with (hs | hs) | hs
  · obtain ⟨pa, hpa, rfl⟩ := mem_frontAliases hs
    exact aliasTyped pa hpa
  · rcases mem_insertAliases hs with hs | ⟨pa, hpa, rfl⟩
    · exact typed st ((List.dropLast_sublist _).subset hs)
    · exact aliasTyped pa hpa
  · subst hs
    exact ⟨"out", .ref core, weOf t core, rfl, TypedExpr.ref core hcore, Or.inr rfl⟩

/-- The wire that remains after at least one `let` field is an operand of a
typed concatenation: it has a positive width. -/
theorem chain_core_pos {we : WEnv} {body : List Stmt} (typed : TypedStmts we body)
    {al : List (Port × String)} {w core : String} (chain : LetChain body al w core)
    (hne : al ≠ []) : 0 < we core := by
  induction chain with
  | nil => exact absurd rfl hne
  | @cons p a b w rest core hmem hrest ih =>
    cases hrest with
    | nil =>
      obtain ⟨l, e, n, heq, ht, _⟩ := typed _ hmem
      cases heq
      cases ht with
      | cat _ _ _ hb => exact hb
    | cons h2 r2 => exact ih (by simp)

end Tools.ShippingMachineClose
