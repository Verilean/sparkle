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
    (hout : 0 < lay.outWidth)
    (hres : evalAssigns (weOf t) mems t.body env0 = some result)
    (hrst : env0 "rst" = 0) :
    ∃ envF, stepModule (weOf (closeMachine lay t)) (closeMachine lay t).body env0 mems =
        some (envF,
          slotNexts (result "out") (t.inputs.drop (t.inputs.length - lay.slots.length)) lay.slots,
          mems) ∧
      envF "out" = mask lay.outWidth (result "out" >>> lay.outLo) := by
  -- Shape of the closed module.
  have hpw : packedWire? t.body = some w := by
    simp [packedWire?, hbody]
  have hdrop : t.body.dropLast = B := by simp [hbody]
  generalize hps : t.inputs.drop (t.inputs.length - lay.slots.length) = ps at slots ⊢
  have hbodyM : (closeMachine lay t).body = B ++ nextAssigns w ps lay.slots ++
      registers lay.resetKind ps lay.slots ++ [.assign "out" (fieldRhs w lay.outLo lay.outWidth)] := by
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
    -- The final environment.
    refine ⟨fun n => if n = "out" then mask lay.outWidth (envN w >>> lay.outLo) else envN n,
      ?_, by simp [hP, hNw]⟩
    have nextSeq : SeqBody (nextAssigns w ps lay.slots) :=
      fun st hs => Or.inl (nextAssigns_assigns w ps lay.slots st hs)
    have evalM : evalAssigns (weOf (closeMachine lay t)) mems (closeMachine lay t).body env0 =
        some (fun n => if n = "out" then mask lay.outWidth (envN w >>> lay.outLo) else envN n) := by
      rw [hbodyM, List.append_assoc, List.append_assoc, evalAssigns_append hBseq, hBM]
      simp only [Option.bind_some]
      rw [evalAssigns_append nextSeq, hN]
      simp only [Option.bind_some]
      rw [registers_evalAssigns]
      simp only [evalAssigns, fieldRhs_eval _ envN w lay.outLo lay.outWidth hout, bind,
        Option.bind]
    have valsF : Zip₂ (fun p f =>
        (fun n => if n = "out" then mask lay.outWidth (envN w >>> lay.outLo) else envN n)
          (nextName p.name) = mask f.width (result "out" >>> f.lo)) ps lay.slots := by
      refine valsN.imp (fun p f h => ?_)
      simp only [nextName_ne_out, if_false]
      rw [h, hP]
    have regsM : regNexts (weOf (closeMachine lay t)) mems (closeMachine lay t).body
        (fun n => if n = "out" then mask lay.outWidth (envN w >>> lay.outLo) else envN n) =
        some (slotNexts (result "out") ps lay.slots) := by
      rw [hbodyM, List.append_assoc, List.append_assoc,
        regNexts_skip_assigns hBassign,
        regNexts_skip_assigns (nextAssigns_assigns w ps lay.slots)]
      exact registers_nexts (by simpa using hNrst) rfl slotsM valsF
    have seqM : SeqBody (closeMachine lay t).body := by
      rw [hbodyM]
      intro st hs
      simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with ((hs | hs) | hs) | hs
      · exact hBseq st hs
      · exact nextSeq st hs
      · exact registers_seq _ _ _ st hs
      · exact Or.inl ⟨_, _, hs⟩
    unfold stepModule
    simp [evalM, regsM, memNexts_seq seqM, bind]

end Tools.ShippingMachineClose
