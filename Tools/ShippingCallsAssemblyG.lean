import Tools.ShippingCallsAssembly
import Tools.ShippingCallsStmtsG
import Tools.ShippingConnsG
import Tools.ShippingCloseChecksG

/-! # `closeInstsG` returns a module: the general closing, assembled (pure)

From facts about a transition `t` (as a harness run gives them), its `let`
closing, the calls' children and the shape: `closeInstsG` on the
register-closed module returns a module — calls with SEVERAL outputs and
calls of SEQUENTIAL children, one instance per call group.

The pieces: the instance statements (`stmtsG_some`), the rank for instances
with several writes (`rank_of_facts_G`, `rank_of_names_K`; `clk` / `rst`
left out of the rank), the body's static checks, the linked view
(`connsG_instOuts`, `linkedOk_ordered_G` through `closeChecksG_of`), distinct
instance names, no self-feed.

What is asked of the children, per entry: as many non-clock inputs as
arguments, distinct; the entry's field an output port; output ports distinct
and none named as an input, `clk` or `rst`; a name other than the parent's.
What is asked of the DESIGN is left as the three checks `closeInstsG` itself
evaluates on `designWith children d` (resolution, memory children, no
instance of the parent): they are facts about the children's designs,
discharged separately. Conditions on the shape that stay: two entries of one
call read different fields, no output port is named as an instance. -/
namespace Tools.ShippingCallsAssemblyG
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingSettledSoundness (Acyclic)
open Tools.ShippingTopoBody Tools.ShippingTopoChecks Tools.ShippingTopoLinked
open Tools.ShippingCloseInstsSome Tools.ShippingCloseChecks Tools.ShippingCloseMachineFacts
open Tools.ShippingInstStmt Tools.ShippingGateChildComb Tools.ShippingKidsComb
open Tools.ShippingCallsParent Tools.ShippingCallsStmts Tools.ShippingDesignWith
open Tools.ShippingRankRun Tools.ShippingRankNames Tools.ShippingCallsRank
open Tools.ShippingClosedOrder Tools.ShippingMachineCloses
open Tools.ShippingCloseLetsSplit (closedBody)
open Tools.ShippingMachineClose (concatParts?_mem mem_frontAliases mem_insertAliases
  nextName_not_allocated outNameOk_facts)
open Tools.ShippingCallsAssembly Tools.ShippingCallsStmtsG Tools.ShippingConnsG
open Tools.ShippingCloseChecksG Tools.ShippingInstStmtG Tools.ShippingCallGroups
open Tools.ShippingRankG

/-! ## Small facts -/

/-- The writes kept in the rank: not the clock, not the reset. -/
def keepW (x : String) : Bool := x != "clk" && x != "rst"

theorem keep_of_alloc {x : String} (h : Allocated x) : keepW x = true := by
  have h1 : x ≠ "clk" := fun e => clk_not_allocated (e ▸ h)
  have h2 : x ≠ "rst" := fun e => Tools.ShippingRegisterSoundness.not_allocated_rst (e ▸ h)
  simp [keepW, h1, h2]

theorem nextName_ne_clk (s : String) : nextName s ≠ "clk" ∧ nextName s ≠ "rst" := by
  have hh : (nextName s).toList.head? = some 'n' := by
    simp [nextName, String.toList_append]
  constructor <;> intro h <;> rw [h] at hh <;> revert hh <;> decide

theorem outName_ne_clk {s : String} (h : outNameOk s = true) : s ≠ "clk" ∧ s ≠ "rst" := by
  simp only [outNameOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.2, h.1.2⟩

theorem flatMap_map_flatten {α β : Type} (φ : α → β) :
    ∀ (gs : List (List α)), (gs.flatMap fun g => g.map φ) = gs.flatten.map φ
  | [] => rfl
  | g :: gs => by
    rw [List.flatMap_cons, List.flatten_cons, List.map_append, flatMap_map_flatten φ gs]

theorem withClockFor_clk {children : List (Module × Design)} {m : Module} {c : Module × Design}
    (hc : c ∈ children) (hs : isSeqChild c.1 = true) :
    (∃ p ∈ (withClockFor children m).inputs, p.name = "clk") ∧
    ∃ p ∈ (withClockFor children m).inputs, p.name = "rst" := by
  have hany : children.any (fun c => c.1.inputs.any (fun p => p.name == "clk" || p.name == "rst")) =
      true := List.any_eq_true.mpr ⟨c, hc, hs⟩
  unfold withClockFor
  dsimp only
  rw [hany, Bool.true_and]
  cases hh : (m.inputs.any (·.name == "clk") && m.inputs.any (·.name == "rst")) with
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    rw [Bool.and_eq_true] at hh
    obtain ⟨p, hp, he⟩ := List.any_eq_true.mp hh.1
    obtain ⟨q, hq, hqe⟩ := List.any_eq_true.mp hh.2
    exact ⟨⟨p, hp, by simpa using he⟩, ⟨q, hq, by simpa using hqe⟩⟩
  | false =>
    simp only [Bool.not_false, if_true]
    exact ⟨⟨_, List.mem_append_right _ (List.mem_cons_self ..), rfl⟩,
      ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl⟩⟩

theorem withClockFor_sub (children : List (Module × Design)) (m : Module) :
    ∀ p ∈ (withClockFor children m).inputs, p ∈ m.inputs ∨ p.name = "clk" ∨ p.name = "rst" := by
  intro p hp
  unfold withClockFor at hp
  dsimp only at hp
  split at hp
  · rcases List.mem_append.mp hp with h | h
    · exact Or.inl h
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  · exact Or.inl hp

/-! ## The assembly -/

set_option maxHeartbeats 8000000 in
/-- **`closeInstsG` returns a module** (calls with several outputs, calls of
sequential children), from the facts of the transition's run, its `let`
closing, the children, and the design checks. -/
theorem closeInstsG_of_facts {P : String → Prop} {bnd : Lean.FVarId → Option String}
    {t t' : Module} {lay : Layout} {d : Design} {bodyB : List Stmt} {w : String}
    {PI ls : List Port} {kI n K : Nat} {cs : List Nat} {insts : List (List Nat)}
    {fields : List String} {children : List (Module × Design)}
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
    (outsNodup : (lay.outs.map (·.name)).Nodup)
    (hkI : insts.length = kI) (hchL : children.length = kI)
    (hargsK : ∀ (k : Nat) (args : List Nat), insts[k]? = some args → ∀ a ∈ args, a < K)
    (hcsK : ∀ j, j < kI → ∃ c, cs[j]? = some c ∧ c ≤ K)
    (hcsA : ∀ (k : Nat) (args : List Nat) (c : Nat), insts[k]? = some args → cs[k]? = some c →
      ∀ a ∈ args, a < c)
    (hchild : ∀ (k : Nat) (c : Module × Design), children[k]? = some c →
      (∀ args : List Nat, insts[k]? = some args → (inPortsOf c.1).length = args.length) ∧
      ((inPortsOf c.1).map (·.name)).Nodup ∧
      (∃ p ∈ c.1.outputs, p.name = fields.getD k "") ∧
      (∀ p ∈ c.1.outputs, (∀ q ∈ inPortsOf c.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst") ∧
      (c.1.outputs.map (·.name)).Nodup ∧
      c.1.name ≠ t.name)
    (hcons : ∀ a ∈ children, ∀ b ∈ children, a.1.name = b.1.name → a.1 = b.1)
    (hfieldsNd : ∀ (k k' : Nat) (key : String × List Nat),
      (keysOf insts children)[k]? = some key → (keysOf insts children)[k']? = some key →
      fields.getD k "" = fields.getD k' "" → k = k')
    (hfreshOuts : ∀ (gi : Nat) (c : Module × Design), c ∈ children →
      ∀ o ∈ lay.outs, o.name ≠ s!"inst{gi}_{c.1.name}")
    (hmemChk : children.all (fun c => Sparkle.Compiler.MachMemory.memSelf
      (moduleByName (designWith children d).modules) c.1) = true)
    (hnames : children.all (fun c =>
      decide (moduleByName (designWith children d).modules c.1.name = some c.1) &&
      c.2.modules.all (fun g =>
        decide (moduleByName (designWith children d).modules g.name = some g))) = true)
    (hnoD : (designWith children d).modules.all (fun g => noInstOfB t.name g.body) = true) :
    (closeInstsG PI.length kI n (t.inputs.map (·.name)) insts fields children
      (closeMachine lay t', d)).isSome = true := by
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
  obtain ⟨hname, hwsub, hwsup, hinsub, houts⟩ := closeMachine_parts (lay := lay) hbody'
  generalize hM : closeMachine lay t' = M at hMbody hname hwsub hwsup hinsub houts ⊢
  have hres : ∀ c ∈ children,
      moduleByName (designWith children d).modules c.1.name = some c.1 := by
    intro c hc
    have := List.all_eq_true.mp hnames c hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  -- the clocked module
  obtain ⟨hcn, hco, hcw, hcb⟩ := withClockFor_same children M
  -- the instance statements
  obtain ⟨stmts, hst, hslen, hcalls, houtWs⟩ := stmtsG_some (PI := PI) (ls := ls)
    (kI := kI) (n := n) (K := K) (insts := insts) (fields := fields) (children := children)
    (m := withClockFor children M) (d' := designWith children d)
    hkI hchL hlsLen hlsNd hargsK
    (fun k c hc => by
      obtain ⟨h1, h2, h3, h4, _, _⟩ := hchild k c hc
      obtain ⟨p, hp, he⟩ := h3
      obtain ⟨g1, g2, g3⟩ := h4 p hp
      exact ⟨hres c (List.mem_of_getElem? hc), h1, h2, ⟨p, hp, he⟩,
        fun q hq => he ▸ g1 q hq, he ▸ g2, he ▸ g3⟩)
    hcons hfieldsNd
    (fun p hp => ⟨p, by rw [hcw]; exact hwsub p (htw ▸ hinW p (hlsMem p hp)), rfl⟩)
    (fun c hc hs => withClockFor_clk hc hs)
    (by
      intro gi c hc hmem
      simp only [List.mem_append, List.mem_map] at hmem
      rcases hmem with (⟨p, hp, he⟩ | ⟨p, hp, he⟩) | ⟨p, hp, he⟩
      · rcases withClockFor_sub children M p hp with h | h | h
        · rcases hinsub p h with h | h | h
          · exact instName_not_allocated gi c.1.name
              (he ▸ hwAlloc p (hinW p (List.mem_of_mem_take (hti ▸ h))))
          · exact instName_ne_clk gi c.1.name (he.symm.trans h)
          · exact instName_ne_rst gi c.1.name (he.symm.trans h)
        · exact instName_ne_clk gi c.1.name (he.symm.trans h)
        · exact instName_ne_rst gi c.1.name (he.symm.trans h)
      · rw [hco, houts] at hp
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hp
        exact hfreshOuts gi c hc o ho he
      · rw [hcw] at hp
        rcases hwsup p hp with h | ⟨x, hx⟩
        · exact instName_not_allocated gi c.1.name (he ▸ hwAlloc p (htw ▸ h))
        · exact instName_ne_next gi c.1.name x (he.symm.trans hx))
  have hG := callGroups_spec (keysOf insts children)
  have hklen : (keysOf insts children).length = kI := by simp [keysOf, hkI]
  have hflatNd : (callGroups (keysOf insts children)).flatten.Nodup :=
    hG.perm.nodup_iff.mpr List.nodup_range
  have hflatLt : ∀ k ∈ (callGroups (keysOf insts children)).flatten, k < kI := by
    intro k hk
    have := List.mem_range.mp (hG.perm.subset hk)
    omega
  have hinstAll : stmts.all isInst = true := by
    rw [List.all_eq_true]
    intro st hs
    obtain ⟨gi, hgi⟩ := List.mem_iff_getElem?.mp hs
    obtain ⟨g, k0, args, c, _, _, _, _, _, rfl⟩ := hcalls gi st hgi
    rfl
  -- the body, in the form the classification is stated for
  have hTa : ∀ st ∈ bodyB.reverse, ∃ l r, st = Stmt.assign l r := Acyclic.assign hT
  have hcombC := closed_comb (T := bodyB.reverse) (al := al) (core := core) (ps := ps) (lay := lay)
    (R := registers lay.resetKind ps lay.slots) (stmts := stmts) hTa hR outsOk
  have hkeys : (nextKeys (registers lay.resetKind ps lay.slots)).Nodup :=
    nextKeys_registers_nodup _ ps lay.slots psNd
  have hform : ∀ (X N R O : List Stmt), (X ++ N) ++ (R ++ O) = X ++ (N ++ (R ++ O)) :=
    fun X N R O => List.append_assoc ..
  obtain ⟨hwo, hcombEq, hregs, hwn, hnk⟩ := static_checks
    (X := (frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
      nextAssigns core ps lay.slots)
    (R := registers lay.resetKind ps lay.slots) (Y := outAssigns core lay.outs) (stmts := stmts)
    (by rw [List.append_assoc]; exact hMacy) hR hkeys hinstAll
  rw [hform] at hwo hcombEq hregs hwn hnk
  have hasgAll : ∀ st ∈ (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        nextAssigns core ps lay.slots) ++ outAssigns core lay.outs), ∃ l r, st = Stmt.assign l r :=
    Acyclic.assign (by rw [List.append_assoc]; exact hMacy)
  -- what the assignments of the body drive
  have hAeq : byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts) = writesOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        nextAssigns core ps lay.slots) ++ outAssigns core lay.outs) := by
    show writesOf (combOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) = _
    rw [hcombEq, Tools.ShippingTopoChecks.writesOf_append, writesOf_insts stmts hinstAll,
      List.append_nil]
  have hAnot : ∀ x ∈ byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts), x ≠ "clk" ∧ x ≠ "rst" := by
    intro x hx
    rw [hAeq, Tools.ShippingTopoChecks.writesOf_append,
      Tools.ShippingTopoChecks.writesOf_append] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨r, hr⟩ := mem_of_writes (Acyclic.prefix hMacy) hx
        have ha := (named' x r hr).1
        exact ⟨fun e => clk_not_allocated (e ▸ ha),
          fun e => Tools.ShippingRegisterSoundness.not_allocated_rst (e ▸ ha)⟩
      · obtain ⟨q, _, e⟩ := writesOf_nextAssigns core ps lay.slots x hx
        exact e ▸ nextName_ne_clk q.name
    · rw [writesOf_outAssigns] at hx
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
      exact outName_ne_clk (outsOk o ho).2
  have hAargs : ∀ (a : Nat) (p : Port), ls[kI + n + a]? = some p →
      p.name ∈ byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts) := by
    intro a p hp
    obtain ⟨_, pa, hpa, rfl⟩ := letAt a p hp
    exact mem_byAssign (l := pa.1.name) (r := .slice (.ref pa.2) (pa.1.ty.bitWidth - 1) 0)
      (List.mem_append_left _ (List.mem_append_left _ (alias_mem hT hpa)))
  have hAout : ∀ (k : Nat) (p : Port), k < kI → ls[k]? = some p →
      p.name ∉ byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts) := by
    intro k p hk hp hmem
    unfold byAssignOf at hmem
    obtain ⟨st, hs, hw⟩ := List.mem_flatMap.mp hmem
    have hpl := List.mem_of_getElem? hp
    rcases hcombC st hs with ⟨l, r, rfl, hm⟩ | ⟨a, pa, hpa, rfl⟩ | ⟨l, lo, wd, rfl, hna⟩ | h
    · have : p.name = l := by simpa [stmtWrites] using hw
      exact notDriven _ (hPls p hpl) (this ▸ mem_writes_assign hm)
    · have he : p.name = pa.1.name := by simpa [aliasStmt, stmtWrites] using hw
      have hpa1 : (al.map (·.1))[a]? = some pa.1 := by rw [List.getElem?_map, hpa]; rfl
      rw [hal, List.getElem?_drop] at hpa1
      have := nodup_index hlsNd hp hpa1 he
      omega
    · have : p.name = l := by simpa [stmtWrites] using hw
      exact hna (this ▸ hlsAlloc p hpl)
    · obtain ⟨gi, hgi⟩ := List.mem_iff_getElem?.mp h
      obtain ⟨g, k0, args, c, _, _, _, _, _, rfl⟩ := hcalls gi st hgi
      simp [stmtWrites] at hw
  -- the wire of an entry
  have houtW : ∀ (k : Nat), k < kI → ∃ p, ls[k]? = some p ∧ outWOf ls k = p.name := by
    intro k hk
    have hlt : k < ls.length := by omega
    exact ⟨ls[k], List.getElem?_eq_getElem hlt, by simp [outWOf, List.getElem?_eq_getElem hlt]⟩
  have houtInj : ∀ a, a < kI → ∀ b, b < kI → outWOf ls a = outWOf ls b → a = b := by
    intro a ha b hb he
    obtain ⟨p, hp, e1⟩ := houtW a ha
    obtain ⟨q, hq, e2⟩ := houtW b hb
    exact nodup_index hlsNd hp hq (e1 ▸ e2 ▸ he)
  have instAt : ∀ (k : Nat), k < kI → ((ls.take kI).map (·.name))[k]? = some (outWOf ls k) := by
    intro k hk
    obtain ⟨p, hp, e⟩ := houtW k hk
    rw [List.getElem?_map, List.getElem?_take, if_pos hk, hp, e]
    rfl
  -- each instance, by its group: the order's view and the linked view
  have hgrp : ∀ (gi : Nat) (st : Stmt), stmts[gi]? = some st →
      ∃ (g : List Nat) (k0 : Nat) (args : List Nat) (c : Module × Design),
        (callGroups (keysOf insts children))[gi]? = some g ∧ k0 ∈ g ∧
        insts[k0]? = some args ∧ children[k0]? = some c ∧
        (∀ k ∈ g, k < kI ∧ insts[k]? = some args ∧ ∃ c', children[k]? = some c' ∧ c'.1 = c.1) ∧
        st = .inst c.1.name s!"inst{gi}_{c.1.name}"
          (callConnsG (inPortsOf c.1) (argWsOf ls kI n args) (isSeqChild c.1)
            (g.map fun k => fields.getD k "") (g.map (outWOf ls))) ∧
        (∀ x, x ∈ combWrites (byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) st ↔
          (isSeqChild c.1 = true ∧ (x = "clk" ∨ x = "rst")) ∨ x ∈ g.map (outWOf ls)) ∧
        (∀ x ∈ combReads (byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) st,
          ∃ a ∈ args, ∃ p, ls[kI + n + a]? = some p ∧ x = p.name) ∧
        (linkW (moduleByName (designWith children d).modules) st).Nodup ∧
        (∀ x, x ∈ linkW (moduleByName (designWith children d).modules) st ↔
          x ∈ g.map (outWOf ls)) := by
    intro gi st hgst
    obtain ⟨g, k0, args, c, hg, h0, hargs, hc, hmem, rfl⟩ := hcalls gi st hgst
    have hk0 : k0 ∈ g := List.mem_of_mem_head? h0
    have hargsIn : ∀ a ∈ args, ∃ p, ls[kI + n + a]? = some p ∧
        ((ls[kI + n + a]?).map (·.name)).getD "" = p.name := by
      intro a ha
      have hlt : kI + n + a < ls.length := by
        have := hargsK k0 args hargs a ha
        omega
      exact ⟨_, List.getElem?_eq_getElem hlt, by rw [List.getElem?_eq_getElem hlt]; rfl⟩
    obtain ⟨hcw, hrd⟩ := connsG_comb (A := byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) (mn := c.1.name)
      (i := s!"inst{gi}_{c.1.name}") (ins := inPortsOf c.1) (argWs := argWsOf ls kI n args)
      (seq := isSeqChild c.1) (g := g) (f := fun k => fields.getD k "") (h := outWOf ls)
      (by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        obtain ⟨p, hp, he⟩ := hargsIn a ha
        rw [he]
        exact hAargs a p hp)
      (by
        intro k hk
        obtain ⟨p, hp, e⟩ := houtW k (hmem k hk).1
        rw [e]
        exact hAout k p (hmem k hk).1 hp)
      (fun hm => (hAnot _ hm).1 rfl) (fun hm => (hAnot _ hm).2 rfl)
    obtain ⟨_, _, _, hio, hond, _⟩ := hchild k0 c hc
    obtain ⟨k0', key, _, hkeyAll⟩ := hG.head g (List.mem_of_getElem? hg)
    obtain ⟨hlnd, hlmem⟩ := connsG_instOuts (outs := c.1.outputs) (ins := inPortsOf c.1)
      (argWs := argWsOf ls kI n args) (seq := isSeqChild c.1) (g := g)
      (f := fun k => fields.getD k "") (h := outWOf ls) hio hond
      (fun a ha b hb he => hfieldsNd a b key (hkeyAll a ha).2 (hkeyAll b hb).2 he)
      (fun a ha b hb he => houtInj a (hmem a ha).1 b (hmem b hb).1 he)
      (by
        intro k hk
        obtain ⟨_, _, c', hc', hcc⟩ := hmem k hk
        obtain ⟨_, _, ho, _⟩ := hchild k c' hc'
        rw [hcc] at ho
        exact ho)
    have hlw : ∀ conns, linkW (moduleByName (designWith children d).modules)
        (.inst c.1.name s!"inst{gi}_{c.1.name}" conns) = instOuts c.1.outputs conns := by
      intro conns
      simp only [linkW, stmtOuts, hres c (List.mem_of_getElem? hc)]
    refine ⟨g, k0, args, c, hg, hk0, hargs, hc, hmem, rfl, hcw, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (hrd x hx)
      obtain ⟨p, hp, he⟩ := hargsIn a ha
      exact ⟨a, ha, p, hp, he⟩
    · rw [hlw]
      exact hlnd
    · rw [hlw]
      exact hlmem
  have hstComb : ∀ st ∈ stmts, st ∈ combOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts) := by
    intro st hs
    rw [hcombEq]
    exact List.mem_append_right _ hs
  -- an instance of the body is one of the statements
  have hinstMem : ∀ mn i conns, Stmt.inst mn i conns ∈ ((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts →
      Stmt.inst mn i conns ∈ stmts := by
    intro mn i conns hm
    rcases List.mem_append.mp hm with h | h
    · exfalso
      have h' : Stmt.inst mn i conns ∈ (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        nextAssigns core ps lay.slots) ++ outAssigns core lay.outs) ∨
          Stmt.inst mn i conns ∈ registers lay.resetKind ps lay.slots := by
        simp only [List.mem_append] at h ⊢
        rcases h with h | h | h | h
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
      rcases h' with h' | h'
      · obtain ⟨l, r, e⟩ := hasgAll _ h'
        cases e
      · have := hR _ h'
        simp [isReg] at this
    · exact h
  -- the driven names, by kind
  have hD : ∀ x ∈ drivenOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts), x ∈ writesOf bodyB.reverse ∨
      x ∈ al.map (·.1.name) ∨ x ∈ (ls.take kI).map (·.name) ∨ ¬ Allocated x := by
    intro x hx
    obtain ⟨st, hs, hw⟩ := mem_driven hx
    rcases hcombC st hs with ⟨l, r, rfl, hm⟩ | ⟨a, pa, hpa, rfl⟩ | ⟨l, lo, wd, rfl, hna⟩ | h
    · have : x = l := by simpa [combWrites, stmtWrites] using hw
      exact Or.inl (this ▸ mem_writes_assign hm)
    · have : x = pa.1.name := by simpa [aliasStmt, combWrites, stmtWrites] using hw
      exact Or.inr (Or.inl (this ▸ List.mem_map.mpr ⟨pa, List.mem_of_getElem? hpa, rfl⟩))
    · have : x = l := by simpa [combWrites, stmtWrites] using hw
      exact Or.inr (Or.inr (Or.inr (this ▸ hna)))
    · obtain ⟨gi, hgi⟩ := List.mem_iff_getElem?.mp h
      obtain ⟨g, k0, args, c, _, _, _, _, hmem, _, hcw, _, _, _⟩ := hgrp gi st hgi
      rcases (hcw x).mp hw with ⟨_, rfl | rfl⟩ | hm
      · exact Or.inr (Or.inr (Or.inr clk_not_allocated))
      · exact Or.inr (Or.inr (Or.inr Tools.ShippingRegisterSoundness.not_allocated_rst))
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
        exact Or.inr (Or.inr (Or.inl (List.mem_of_getElem? (instAt k (hmem k hk).1))))
  -- the rank
  obtain ⟨pres, hρ⟩ := rank_of_facts_G (P := P) (bnd := bnd) (t := t) (bodyB := bodyB)
    (w := w) (ls := ls) (kI := kI) (n := n) (cs := cs) (al := al) (es := es) (ws := ws)
    (core := core) (stmts := stmts) (comb := combOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts))
    (A := byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) (D := drivenOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) keepW
    hbody hacy hnamed hnw hPls hlsAlloc hlsNd hal hfacts
    (fun j hj => by
      obtain ⟨c, h1, h2⟩ := hcsK j hj
      exact ⟨c, h1, hKal ▸ h2⟩)
    hcoreA
    (by
      intro st hs
      refine ⟨List.all_eq_true.mp hinstAll st hs, ?_⟩
      intro outW hw hkeep
      obtain ⟨gi, hgi⟩ := List.mem_iff_getElem?.mp hs
      obtain ⟨g, k0, args, c, _, _, _, _, hmem, _, hcw, hrd, _, _⟩ := hgrp gi st hgi
      rcases (hcw outW).mp hw with ⟨_, rfl | rfl⟩ | hm
      · simp [keepW] at hkeep
      · simp [keepW] at hkeep
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
        obtain ⟨hkI', hargsk, _⟩ := hmem k hk
        obtain ⟨cc, hcc, _⟩ := hcsK k hkI'
        refine ⟨k, cc, instAt k hkI', hcc, fun x hx => ?_⟩
        obtain ⟨a, ha, p, hp, rfl⟩ := hrd x hx
        exact ⟨a, (letAt a p hp).1, hcsA k args cc hargsk hcc a ha⟩)
    hcombC hD
  -- every combinational statement drives a kept name, and reads allocated names
  have hreadsAlloc : ∀ st ∈ combOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts),
      ∀ r ∈ combReads (byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) st, Allocated r := by
    intro st hs r hr
    rcases hcombC st hs with ⟨l, r', rfl, hm⟩ | ⟨a, pa, hpa, rfl⟩ | ⟨l, lo, wd, rfl, hna⟩ | h
    · exact (hnamed l r' hm).2 r hr
    · have : r = pa.2 := by simpa [aliasStmt, combReads, stmtReads, refsOf] using hr
      exact this ▸ halloc2 pa (List.mem_of_getElem? hpa)
    · have : r = core := by simpa [combReads, stmtReads, fieldRhs, refsOf] using hr
      exact this ▸ hcoreA
    · obtain ⟨gi, hgi⟩ := List.mem_iff_getElem?.mp h
      obtain ⟨g, k0, args, c, _, _, _, _, _, _, _, hrd, _, _⟩ := hgrp gi st hgi
      obtain ⟨a, _, p, hp, rfl⟩ := hrd r hr
      exact hlsAlloc p (List.mem_of_getElem? hp)
  have hne : ∀ st ∈ combOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts),
      (combWrites (byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) st).filter keepW ≠ [] := by
    intro st hs
    have hasgKeep : ∀ l r, st = Stmt.assign l r →
        (combWrites (byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) st).filter keepW ≠ [] := by
      intro l r e
      subst e
      have hmemB : Stmt.assign l r ∈ ((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts := by
        rw [combOf_eq] at hs
        exact (List.mem_filter.mp hs).1
      obtain ⟨h1, h2⟩ := hAnot l (mem_byAssign hmemB)
      have : keepW l = true := by simp [keepW, h1, h2]
      simp [combWrites, stmtWrites, this]
    rcases hcombC st hs with ⟨l, r, e, _⟩ | ⟨a, pa, _, e⟩ | ⟨l, lo, wd, e, _⟩ | h
    · exact hasgKeep l r e
    · exact hasgKeep _ _ e
    · exact hasgKeep _ _ e
    · obtain ⟨gi, hgi⟩ := List.mem_iff_getElem?.mp h
      obtain ⟨g, k0, args, c, _, hk0, _, _, hmem, _, hcw, _, _, _⟩ := hgrp gi st hgi
      obtain ⟨p, hp, e⟩ := houtW k0 (hmem k0 hk0).1
      have hw : outWOf ls k0 ∈ combWrites (byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) st :=
        (hcw _).mpr (Or.inr (List.mem_map.mpr ⟨k0, hk0, rfl⟩))
      have hk : keepW (outWOf ls k0) = true :=
        keep_of_alloc (e ▸ hlsAlloc p (List.mem_of_getElem? hp))
      intro hnil
      have := List.mem_filter.mpr ⟨hw, hk⟩
      rw [hnil] at this
      cases this
  have hrank := rank_of_names_K (body := ((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts) keepW
    (rho bodyB.reverse pres (al.map (·.1.name)) ((ls.take kI).map (·.name)) cs) hne
    (fun st hs r hr _ => keep_of_alloc (hreadsAlloc st hs r hr))
    (fun st hs l hl hk r hr hd => hρ st hs l hl hk r hr hd)
  -- the linked view of the statements
  have hlink := nodup_flatMap_index (linkW (moduleByName (designWith children d).modules))
    (fun g : List Nat => g.map (outWOf ls)) stmts (callGroups (keysOf insts children)) hslen
    (by
      rw [flatMap_map_flatten]
      exact nodup_map_on _ _ hflatNd
        (fun a ha b hb he => houtInj a (hflatLt a ha) b (hflatLt b hb) he))
    (by
      intro gi st g hst' hg'
      obtain ⟨g2, k0, args, c, hg2, _, _, _, _, _, _, _, hlnd, hlmem⟩ := hgrp gi st hst'
      rw [hg'] at hg2
      cases hg2
      exact ⟨hlnd, fun x hx => (hlmem x).mp hx⟩)
  obtain ⟨hlinkNd, hlinkSub⟩ := hlink
  have hlinkOut : ∀ x ∈ stmts.flatMap (linkW (moduleByName (designWith children d).modules)),
      ∃ k, k < kI ∧ x = outWOf ls k := by
    intro x hx
    have := hlinkSub x hx
    rw [flatMap_map_flatten] at this
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp this
    exact ⟨k, hflatLt k hk, rfl⟩
  have hbw : bodyWrites (moduleByName (designWith children d).modules)
      (combOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) =
      writesOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        nextAssigns core ps lay.slots) ++ outAssigns core lay.outs) ++ stmts.flatMap (linkW (moduleByName (designWith children d).modules)) := by
    rw [hcombEq, bodyWrites_eq, List.flatMap_append, linkW_assigns _ _ hasgAll]
  obtain ⟨body, htopo, hchk⟩ := closeChecksG_of (portNames := (PI ++ ls).map (·.name))
    (children := children) (mname := M.name) (d' := designWith children d)
    (mb := ((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs)))) (stmts := stmts)
    hinstAll (hin ▸ hnd) hwo (rankMinK keepW _ (rho bodyB.reverse pres (al.map (·.1.name))
      ((ls.take kI).map (·.name)) cs))
    hrank hregs hwn hnk
    (by
      rw [hbw, List.nodup_append]
      refine ⟨Acyclic.nodup (by rw [List.append_assoc]; exact hMacy), hlinkNd, ?_⟩
      intro a ha b hb e
      subst e
      obtain ⟨k, hk, rfl⟩ := hlinkOut _ hb
      obtain ⟨p, hp, e⟩ := houtW k hk
      exact hAout k p hk hp (by rw [← e, hAeq]; exact ha))
    (by
      intro x hx
      rw [hbw] at hx
      unfold drivenOf
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (by rw [hAeq]; exact h)
      · refine List.mem_append_right _ ?_
        obtain ⟨st, hs, hxl⟩ := List.mem_flatMap.mp h
        obtain ⟨gi, hgi⟩ := List.mem_iff_getElem?.mp hs
        obtain ⟨g, k0, args, c, _, _, _, _, _, _, hcw, _, _, hlmem⟩ := hgrp gi st hgi
        exact List.mem_flatMap.mpr ⟨st, hstComb st hs,
          (hcw x).mpr (Or.inr ((hlmem x).mp hxl))⟩)
    (by
      intro mn i conns hm
      have hs := hinstMem mn i conns hm
      obtain ⟨gi, hgi⟩ := List.mem_iff_getElem?.mp hs
      obtain ⟨g, k0, args, c, _, _, _, hc, hmem, he, hcw, _, _, hlmem⟩ := hgrp gi _ hgi
      cases he
      have hlw : linkW (moduleByName (designWith children d).modules)
          (.inst c.1.name s!"inst{gi}_{c.1.name}"
            (callConnsG (inPortsOf c.1) (argWsOf ls kI n args) (isSeqChild c.1)
              (g.map fun k => fields.getD k "") (g.map (outWOf ls)))) =
          instOuts c.1.outputs (callConnsG (inPortsOf c.1) (argWsOf ls kI n args)
            (isSeqChild c.1) (g.map fun k => fields.getD k "") (g.map (outWOf ls))) := by
        simp only [linkW, stmtOuts, hres c (List.mem_of_getElem? hc)]
      rw [hlw] at hlmem
      refine ⟨c.1, hres c (List.mem_of_getElem? hc), ?_, ?_, connsG_refs⟩
      · intro x hx
        exact (hcw x).mpr (Or.inr ((hlmem x).mp hx))
      · intro x hx hno hb
        rcases (hcw x).mp hx with ⟨_, hx'⟩ | hx'
        · rw [hbw] at hb
          rcases List.mem_append.mp hb with hb | hb
          · have := hAnot x (by rw [hAeq]; exact hb)
            rcases hx' with e | e
            · exact this.1 e
            · exact this.2 e
          · obtain ⟨k, hk, e⟩ := hlinkOut x hb
            obtain ⟨p, hp, e'⟩ := houtW k hk
            have ha : Allocated x := by
              rw [e, e']
              exact hlsAlloc p (List.mem_of_getElem? hp)
            rcases hx' with e | e
            · exact clk_not_allocated (e ▸ ha)
            · exact Tools.ShippingRegisterSoundness.not_allocated_rst (e ▸ ha)
        · exact hno ((hlmem x).mpr hx'))
    (by
      rw [List.filterMap_append]
      have hmb : (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs)))).filterMap instNameOf = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro st hs
        cases st with
        | inst mn i conns =>
          have := hinstMem mn i conns (List.mem_append_left _ hs)
          exfalso
          have h' : Stmt.inst mn i conns ∈ (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        nextAssigns core ps lay.slots) ++ outAssigns core lay.outs) ∨
              Stmt.inst mn i conns ∈ registers lay.resetKind ps lay.slots := by
            simp only [List.mem_append] at hs ⊢
            rcases hs with h | h | h | h
            · exact Or.inl (Or.inl (Or.inl h))
            · exact Or.inl (Or.inl (Or.inr h))
            · exact Or.inr h
            · exact Or.inl (Or.inr h)
          rcases h' with h' | h'
          · obtain ⟨l, r, e⟩ := hasgAll _ h'
            cases e
          · have := hR _ h'
            simp [isReg] at this
        | _ => rfl
      rw [hmb, List.nil_append]
      refine (instNames_nodup stmts 0 (fun gi st hgi => ?_)).1
      obtain ⟨g, k0, args, c, _, _, _, _, _, rfl⟩ := hcalls gi st hgi
      exact ⟨_, c.1.name, _, by rw [Nat.zero_add]⟩)
    (by
      refine noSelfFeed_of (fun mn i conns c0 hm hfind cn hcn hno x hx hin' => ?_)
      have hs := hinstMem mn i conns hm
      obtain ⟨gi, hgi⟩ := List.mem_iff_getElem?.mp hs
      obtain ⟨g, k0, args, c, _, _, hargs, hc, hmem, he, hcw, hrd, _, hlmem⟩ := hgrp gi _ hgi
      cases he
      rw [hres c (List.mem_of_getElem? hc)] at hfind
      cases hfind
      have hlw : linkW (moduleByName (designWith children d).modules)
          (.inst c.1.name s!"inst{gi}_{c.1.name}"
            (callConnsG (inPortsOf c.1) (argWsOf ls kI n args) (isSeqChild c.1)
              (g.map fun k => fields.getD k "") (g.map (outWOf ls)))) =
          instOuts c.1.outputs (callConnsG (inPortsOf c.1) (argWsOf ls kI n args)
            (isSeqChild c.1) (g.map fun k => fields.getD k "") (g.map (outWOf ls))) := by
        simp only [linkW, stmtOuts, hres c (List.mem_of_getElem? hc)]
      rw [hlw] at hlmem
      obtain ⟨k, hk, hxe⟩ := List.mem_map.mp ((hlmem x).mp hin')
      obtain ⟨p, hp, e⟩ := houtW k (hmem k hk).1
      have hxA : x ∉ byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts) := by
        rw [← hxe, e]
        exact hAout k p (hmem k hk).1 hp
      have hxAl : Allocated x := by
        rw [← hxe, e]
        exact hlsAlloc p (List.mem_of_getElem? hp)
      rcases mem_connsG hcn with ⟨_, _, _, w', hw', he⟩ | ⟨_, he | he⟩ | ⟨k', hk', he⟩
      · rw [he] at hx
        have hxw : w' = x := by simpa using hx
        obtain ⟨a, ha, hae⟩ := List.mem_map.mp hw'
        have hlt : kI + n + a < ls.length := by
          have := hargsK k0 args hargs a ha
          omega
        have := hAargs a ls[kI + n + a] (List.getElem?_eq_getElem hlt)
        apply hxA
        rw [← hxw, ← hae, List.getElem?_eq_getElem hlt]
        exact this
      · rw [he] at hx
        have hxw : "clk" = x := by simpa using hx
        exact clk_not_allocated (by rw [hxw]; exact hxAl)
      · rw [he] at hx
        have hxw : "rst" = x := by simpa using hx
        exact Tools.ShippingRegisterSoundness.not_allocated_rst (by rw [hxw]; exact hxAl)
      · apply hno
        rw [he]
        obtain ⟨_, _, c', hc', hcc⟩ := hmem k' hk'
        obtain ⟨_, _, ⟨q, hq, hqe⟩, _⟩ := hchild k' c' hc'
        rw [hcc] at hq
        exact List.mem_map.mpr ⟨q, hq, hqe⟩)
    hmemChk hnames
    (by
      unfold noInstOfB
      rw [List.all_eq_true]
      intro st hs
      cases st with
      | inst mn i conns =>
        have hs' := hinstMem mn i conns hs
        obtain ⟨gi, hgi⟩ := List.mem_iff_getElem?.mp hs'
        obtain ⟨g, k0, args, c, _, _, _, hc, _, he, _, _, _, _⟩ := hgrp gi _ hgi
        cases he
        have := (hchild k0 c hc).2.2.2.2.2
        simpa [hname, htn] using this
      | _ => rfl)
    (by rw [hname, htn]; exact hnoD)
  rw [hin]
  exact closeInstsG_some_of (m0 := M) (d := d) hst houtWs (by rw [hMbody]; exact htopo)
    (by rw [hMbody]; exact hchk)

end Tools.ShippingCallsAssemblyG
