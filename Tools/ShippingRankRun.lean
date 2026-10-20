import Tools.ShippingCallsRank
import Tools.ShippingTransitionFields

/-! # From the per-field facts of a run to the rank's hypotheses

`Facts` (what `letOperands_facts` gives about each `let`'s operand, from the
per-field facts `LP` of a harness run) as the list of body PREFIXES the rank
`rho` is defined from, with what `rank_closed` asks of each: the prefix is a
prefix of the transition's statements, its statements read protected names
only as the field's rule allows, and the operand is driven in it or is a
protected name the rule allows. -/
namespace Tools.ShippingRankRun
open Lean Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Tools.ShippingUnifiedSpine Tools.ShippingMachineCloses
open Tools.ShippingSettledSoundness (Acyclic)
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingClosedOrder Tools.ShippingRankNames Tools.ShippingCallsRank Tools.ShippingTopoBody
open Tools.ShippingMachineClose (concatParts?_mem mem_frontAliases mem_insertAliases outNameOk_facts
  nextName_not_allocated)
open Tools.ShippingMachineCleanup (nextAssigns_mem)
open Tools.ShippingTopoChecks (combOf_eq isComb isReg)

/-- **The prefixes of the fields.** -/
theorem facts_pres {P : String → Prop} {bnd : FVarId → Option String} {Vk : Nat → String → Prop}
    {wires : List Port} {body bodyB : List Stmt} :
    ∀ (al : List (Port × String)) (es : List Lean.Expr) (ws : List Nat) (i : Nat),
      Facts P bnd Vk wires body bodyB i al es ws →
      ∃ pres : List (List Stmt), pres.length = al.length ∧
        ∀ (k : Nat) (pa : Port × String), al[k]? = some pa →
          ∃ pre, pres[k]? = some pre ∧ pre <+: bodyB.reverse ∧
            (∀ l r, Stmt.assign l r ∈ pre → ReadsOK P (Vk (i + k)) r) ∧
            ((∃ rhs, Stmt.assign pa.2 rhs ∈ pre) ∨ P pa.2) ∧ (P pa.2 → Vk (i + k) pa.2) ∧
            ∃ x b, concatParts? body x = some (pa.2, b)
  | [], [], [], _, _ => ⟨[], rfl, fun k pa h => by simp at h⟩
  | pa0 :: al, e :: es, m :: ws, i, hf => by
    obtain ⟨_, hcp, ⟨pre, hsuf, hsrc, hrd⟩, hv, hrest⟩ := hf
    obtain ⟨pres, hlen, hall⟩ := facts_pres al es ws (i + 1) hrest
    refine ⟨pre.reverse :: pres, by simp [hlen], ?_⟩
    intro k pa hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      refine ⟨pre.reverse, rfl, List.reverse_prefix.mpr hsuf,
        fun l r hm => hrd l r (List.mem_reverse.mp hm), ?_, hv, hcp⟩
      rcases hsrc with ⟨_, rhs, hm⟩ | ⟨id, _, _, hp⟩
      · exact Or.inl ⟨rhs, List.mem_reverse.mpr hm⟩
      · exact Or.inr hp
    | succ k =>
      obtain ⟨pre', h1, h2, h3, h4, h5, h6⟩ := hall k pa (by simpa using hk)
      refine ⟨pre', by simpa using h1, h2, ?_, h4, ?_, h6⟩
      · rw [show i + (k + 1) = i + 1 + k by omega]
        exact h3
      · rw [show i + (k + 1) = i + 1 + k by omega]
        exact h5
  | [], _ :: _, _, _, hf => by cases hf
  | [], [], _ :: _, _, hf => by cases hf
  | _ :: _, [], _, _, hf => by cases hf
  | _ :: _, _ :: _, [], _, hf => by cases hf

/-- Which tail port (index `idx` among the calls' outputs, the slots, the
`let`s) field `i` may read: a call's output once the bound `c` of its
argument `let`s is passed; a `let` port only of an earlier `let`. -/
def okRule (kI n : Nat) (cs : List Nat) (i idx : Nat) : Prop :=
  (idx < kI → ∃ c, cs[idx]? = some c ∧ c ≤ i) ∧ (kI + n ≤ idx → idx - (kI + n) < i)

set_option maxHeartbeats 1000000 in
/-- **The rank orders the closed body of a real transition** — from the
run's facts (`transition_fields`, `letOperands_facts`) about the transition
`t`: its body, the tail ports `ls` (the calls' outputs, the slots, the
`let`s), the aliases `al` with their `Facts` under `okRule`. What remains as
hypotheses is about the closed body's statements: which they are (`hcomb`),
the driven names (`hD`), the remaining wire, the instances. -/
theorem rank_of_facts {P : String → Prop} {bnd : FVarId → Option String} {t : Sparkle.IR.AST.Module}
    {bodyB : List Stmt} {w : String} {ls : List Port} {kI n : Nat} {cs : List Nat}
    {al : List (Port × String)} {es : List Lean.Expr} {ws : List Nat}
    {core : String} {stmts comb : List Stmt} {A D : List String}
    (hbody : t.body = bodyB.reverse ++ [.assign "out" (.ref w)])
    (hacy : Acyclic t.body)
    (hnamed : ∀ l r, Stmt.assign l r ∈ bodyB.reverse → Allocated l ∧ ∀ x ∈ refsOf r, Allocated x)
    (hnw : ∀ l r, Stmt.assign l r ∈ bodyB → ¬ P l)
    (hPls : ∀ p ∈ ls, P p.name) (hlsAlloc : ∀ p ∈ ls, Allocated p.name)
    (hlsNd : (ls.map Port.name).Nodup)
    (hal : al.map (·.1) = ls.drop (kI + n))
    (hfacts : Facts P bnd
      (fun i x => ∀ (idx : Nat) (p : Port), ls[idx]? = some p → x = p.name → okRule kI n cs i idx)
      t.wires t.body bodyB 0 al es ws)
    (hcsK : ∀ j, j < kI → ∃ c, cs[j]? = some c ∧ c ≤ al.length)
    (hcore : Allocated core)
    (hinst : ∀ st ∈ stmts, ∃ (j : Nat) (outW : String) (c : Nat),
      ((ls.take kI).map Port.name)[j]? = some outW ∧ cs[j]? = some c ∧
      combWrites A st = [outW] ∧
      ∀ x ∈ combReads A st, ∃ a : Nat, (al.map (·.1.name))[a]? = some x ∧ a < c)
    (hcomb : ∀ st ∈ comb, (∃ l r, st = Stmt.assign l r ∧ Stmt.assign l r ∈ bodyB.reverse) ∨
      (∃ (a : Nat) (pa : Port × String), al[a]? = some pa ∧ st = aliasStmt pa.1 pa.2) ∨
      (∃ l lo wd, st = Stmt.assign l (fieldRhs core lo wd) ∧ ¬ Allocated l) ∨ st ∈ stmts)
    (hD : ∀ x ∈ D, x ∈ writesOf bodyB.reverse ∨ x ∈ al.map (·.1.name) ∨
      x ∈ (ls.take kI).map Port.name ∨ ¬ Allocated x) :
    ∃ pres : List (List Stmt),
      (∀ st ∈ comb, ∃ l, combWrites A st = [l]) ∧
      ∀ st ∈ comb, ∀ l, combWrites A st = [l] → ∀ r ∈ combReads A st, r ∈ D →
        rho bodyB.reverse pres (al.map (·.1.name)) ((ls.take kI).map Port.name) cs r <
          rho bodyB.reverse pres (al.map (·.1.name)) ((ls.take kI).map Port.name) cs l := by
  have hT : Acyclic bodyB.reverse := Acyclic.prefix (hbody ▸ hacy)
  obtain ⟨pres, hlen, hall⟩ := facts_pres al es ws 0 hfacts
  -- the `let` ports and the calls' output ports, as tail ports
  have hletEq : al.map (·.1.name) = (ls.drop (kI + n)).map Port.name := by
    rw [← hal, List.map_map]
    rfl
  have letAt : ∀ (a : Nat) (x : String), (al.map (·.1.name))[a]? = some x →
      ∃ p, ls[kI + n + a]? = some p ∧ p.name = x := by
    intro a x h
    rw [hletEq, List.getElem?_map, List.getElem?_drop] at h
    cases hp : ls[kI + n + a]? with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      exact ⟨p, rfl, by simpa using h⟩
  have instAt : ∀ (j : Nat) (x : String), ((ls.take kI).map Port.name)[j]? = some x →
      j < kI ∧ ∃ p, ls[j]? = some p ∧ p.name = x := by
    intro j x h
    rw [List.getElem?_map, List.getElem?_take] at h
    by_cases hj : j < kI
    · rw [if_pos hj] at h
      cases hp : ls[j]? with
      | none => rw [hp] at h; cases h
      | some p =>
        rw [hp] at h
        exact ⟨hj, p, rfl, by simpa using h⟩
    · rw [if_neg hj] at h
      cases h
  have notDriven : ∀ x, P x → x ∉ writesOf bodyB.reverse := by
    intro x hp hw
    obtain ⟨r, hr⟩ := mem_of_writes hT hw
    exact hnw x r (List.mem_reverse.mp hr) hp
  have hsplit : ls.map Port.name =
      (ls.take kI).map Port.name ++ (ls.drop kI).map Port.name := by
    rw [← List.map_append, List.take_append_drop]
  have hpre : ∀ pre ∈ pres, pre <+: bodyB.reverse := by
    intro pre hp
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
    have hkl : k < al.length := hlen ▸ (List.getElem?_eq_some_iff.mp hk).1
    obtain ⟨pre', h1, h2, _⟩ := hall k _ (List.getElem?_eq_getElem hkl)
    rw [hk] at h1
    cases h1
    exact h2
  refine ⟨pres, rank_closed (cs := cs) hT hnamed ?_ ?_ ?_ ?_ hlen hpre ?_ ?_ ?_ hcore hinst hcomb hD⟩
  · -- the ports are undriven and allocated
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hx
      obtain ⟨p, hp, rfl⟩ := letAt a x ha
      exact ⟨notDriven _ (hPls p (List.mem_of_getElem? hp)), hlsAlloc p (List.mem_of_getElem? hp)⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
      obtain ⟨_, p, hp, rfl⟩ := instAt j x hj
      exact ⟨notDriven _ (hPls p (List.mem_of_getElem? hp)), hlsAlloc p (List.mem_of_getElem? hp)⟩
  · rw [hletEq, List.map_drop]
    exact hlsNd.sublist (List.drop_sublist _ _)
  · rw [List.map_take]
    exact hlsNd.sublist (List.take_sublist _ _)
  · intro x hx hx'
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hx
    obtain ⟨p, hp, hpn⟩ := letAt a x ha
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx'
    obtain ⟨hjk, q, hq, hqn⟩ := instAt j x hj
    have := nodup_index hlsNd hp hq (hpn.trans hqn.symm)
    omega
  · -- what a statement of field `i`'s prefix reads
    intro i pre hi l r hm x hx
    have hil : i < al.length := hlen ▸ (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨pre', h1, _, h3, _⟩ := hall i _ (List.getElem?_eq_getElem hil)
    rw [hi] at h1
    cases h1
    rw [Nat.zero_add] at h3
    have hv := h3 l r hm x hx
    refine ⟨fun a ha => ?_, fun j c hj hc => ?_⟩
    · obtain ⟨p, hp, hpn⟩ := letAt a x ha
      have := (hv (hpn ▸ hPls p (List.mem_of_getElem? hp)) (kI + n + a) p hp hpn.symm).2 (by omega)
      omega
    · obtain ⟨hjk, p, hp, hpn⟩ := instAt j x hj
      obtain ⟨c', hc', hle⟩ := (hv (hpn ▸ hPls p (List.mem_of_getElem? hp)) j p hp hpn.symm).1 hjk
      rw [hc] at hc'
      cases hc'
      exact hle
  · intro j x hj
    exact hcsK j (instAt j x hj).1
  · -- the aliases
    intro a pa hpa
    obtain ⟨pre, h1, _, _, hsrc, hv, x', b', hcp⟩ := hall a pa hpa
    rw [Nat.zero_add] at hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hm := concatParts?_mem hcp
      rw [hbody] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact (hnamed _ _ hm).2 pa.2 (by simp [refsOf, refsOf.refsList])
      · simp at hm
    · intro hw
      rcases hsrc with ⟨rhs, hm⟩ | hp
      · exact ⟨pre, h1, mem_writes_assign hm⟩
      · exact absurd hw (notDriven _ hp)
    · intro b hb
      obtain ⟨p, hp, hpn⟩ := letAt b pa.2 hb
      have := (hv (hpn ▸ hPls p (List.mem_of_getElem? hp)) (kI + n + b) p hp hpn.symm).2 (by omega)
      omega
    · intro j c hj hc
      obtain ⟨hjk, p, hp, hpn⟩ := instAt j pa.2 hj
      obtain ⟨c', hc', hle⟩ := (hv (hpn ▸ hPls p (List.mem_of_getElem? hp)) j p hp hpn.symm).1 hjk
      rw [hc] at hc'
      cases hc'
      exact hle

/-! ## The closed body's statements and driven names -/

/-- **The combinational statements of the closed body, by kind** (no fact
about the instances needed). -/
theorem closed_comb {T : List Stmt} {al : List (Port × String)} {core : String}
    {ps : List Port} {lay : Layout} {R stmts : List Stmt}
    (hTa : ∀ st ∈ T, ∃ l r, st = Stmt.assign l r)
    (hR : ∀ st ∈ R, isReg st = true)
    (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true) :
    ∀ st ∈ combOf (((frontAliases al T ++ insertAliases al T) ++
        (nextAssigns core ps lay.slots ++ (R ++ outAssigns core lay.outs))) ++ stmts),
      (∃ l r, st = Stmt.assign l r ∧ Stmt.assign l r ∈ T) ∨
      (∃ (a : Nat) (pa : Port × String), al[a]? = some pa ∧ st = aliasStmt pa.1 pa.2) ∨
      (∃ l lo wd, st = Stmt.assign l (fieldRhs core lo wd) ∧ ¬ Allocated l) ∨ st ∈ stmts := by
  intro st hs
  rw [combOf_eq] at hs
  obtain ⟨hm, hc⟩ := List.mem_filter.mp hs
  have aliasCase : ∀ pa ∈ al, st = aliasStmt pa.1 pa.2 →
      ∃ (a : Nat) (pa : Port × String), al[a]? = some pa ∧ st = aliasStmt pa.1 pa.2 := by
    intro pa hpa he
    obtain ⟨a, ha⟩ := List.mem_iff_getElem?.mp hpa
    exact ⟨a, pa, ha, he⟩
  simp only [List.mem_append] at hm
  rcases hm with ((h | h) | h | h | h) | h
  · obtain ⟨pa, hpa, he⟩ := mem_frontAliases h
    exact Or.inr (Or.inl (aliasCase pa hpa he))
  · rcases mem_insertAliases h with h | ⟨pa, hpa, he⟩
    · obtain ⟨l, r, rfl⟩ := hTa st h
      exact Or.inl ⟨l, r, rfl, h⟩
    · exact Or.inr (Or.inl (aliasCase pa hpa he))
  · obtain ⟨p, f, he⟩ := nextAssigns_mem core ps lay.slots st h
    exact Or.inr (Or.inr (Or.inl ⟨_, _, _, he, nextName_not_allocated p.name⟩))
  · have := hR st h
    cases st <;> simp_all [isReg, isComb]
  · simp only [outAssigns, List.mem_map] at h
    obtain ⟨o, ho, he⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨_, _, _, he.symm, (outNameOk_facts (outsOk o ho).2).1⟩))
  · exact Or.inr (Or.inr (Or.inr h))

/-- **The combinational statements of the closed body, by kind**, and the
names they drive: a transition statement, the alias of a `let`, a next-value
or output assignment (a name that is not allocated), an instance. -/
theorem closed_classes {T : List Stmt} {al : List (Port × String)} {core : String}
    {ps : List Port} {lay : Layout} {R stmts : List Stmt} {instNames : List String}
    (hTa : ∀ st ∈ T, ∃ l r, st = Stmt.assign l r)
    (hR : ∀ st ∈ R, isReg st = true)
    (outsOk : ∀ o ∈ lay.outs, 0 < o.width ∧ outNameOk o.name = true)
    (hinst : ∀ st ∈ stmts, ∃ outW, outW ∈ instNames ∧
      combWrites (byAssignOf (((frontAliases al T ++ insertAliases al T) ++
        (nextAssigns core ps lay.slots ++ (R ++ outAssigns core lay.outs))) ++ stmts)) st = [outW]) :
    let body0 := ((frontAliases al T ++ insertAliases al T) ++
        (nextAssigns core ps lay.slots ++ (R ++ outAssigns core lay.outs))) ++ stmts
    (∀ st ∈ combOf body0, (∃ l r, st = Stmt.assign l r ∧ Stmt.assign l r ∈ T) ∨
      (∃ (a : Nat) (pa : Port × String), al[a]? = some pa ∧ st = aliasStmt pa.1 pa.2) ∨
      (∃ l lo wd, st = Stmt.assign l (fieldRhs core lo wd) ∧ ¬ Allocated l) ∨ st ∈ stmts) ∧
    (∀ x ∈ drivenOf body0, x ∈ writesOf T ∨ x ∈ al.map (·.1.name) ∨ x ∈ instNames ∨
      ¬ Allocated x) := by
  intro body0
  have hcls := closed_comb (al := al) (core := core) (ps := ps) (lay := lay) (stmts := stmts)
    hTa hR outsOk
  refine ⟨hcls, ?_⟩
  intro x hx
  obtain ⟨st, hs, hw⟩ := mem_driven hx
  rcases hcls st hs with ⟨l, r, rfl, hm⟩ | ⟨a, pa, hpa, rfl⟩ | ⟨l, lo, wd, rfl, hna⟩ | h
  · have : x = l := by simpa [combWrites, stmtWrites] using hw
    exact Or.inl (this ▸ mem_writes_assign hm)
  · have : x = pa.1.name := by simpa [aliasStmt, combWrites, stmtWrites] using hw
    exact Or.inr (Or.inl (this ▸ List.mem_map.mpr ⟨pa, List.mem_of_getElem? hpa, rfl⟩))
  · have : x = l := by simpa [combWrites, stmtWrites] using hw
    exact Or.inr (Or.inr (Or.inr (this ▸ hna)))
  · obtain ⟨outW, ho, hcw⟩ := hinst st h
    rw [hcw] at hw
    have : x = outW := by simpa using hw
    exact Or.inr (Or.inr (Or.inl (this ▸ ho)))

end Tools.ShippingRankRun
