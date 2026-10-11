import Tools.ShippingCallsStmts

/-! # `closeInsts` returns a module: the one-output closing, assembled (pure)

From facts about a transition `t` (as a harness run gives them), its `let`
closing, the calls' children (as their own full-entry runs give them) and the
shape: `closeInsts` on the register-closed module returns a module. The
pieces: the instance statements (`instStmts_some`), the rank
(`rank_of_facts`, `closed_classes`, `rank_of_names`), the body's static
checks (`closeMachine_body`, `static_checks`), the linked view and
`kidsCombB` of the instances, name resolution (`designWith_resolves`).

Stated for `K ≠ 0` `let`s (a call with arguments has `let`s) and one-output
gate children whose own designs are empty. Premises that are real conditions
and stay: the children are name-consistent, no child is named as the parent,
no output port is named as an instance. -/
namespace Tools.ShippingCallsAssembly
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
open Tools.ShippingMachineClose (concatParts?_mem mem_frontAliases mem_insertAliases)

/-! ## Small facts -/

theorem alias_in_insert (al : List (Port × String)) {pa : Port × String} (hpa : pa ∈ al) :
    ∀ (T : List Stmt) {r : Expr}, Stmt.assign pa.2 r ∈ T →
      aliasStmt pa.1 pa.2 ∈ insertAliases al T
  | st :: rest, r, h => by
    simp only [insertAliases, List.mem_cons, List.mem_append]
    rcases List.mem_cons.mp h with e | h
    · subst e
      refine Or.inr (Or.inl ?_)
      simp only [aliasesOf, List.mem_map, List.mem_filter]
      exact ⟨pa, ⟨hpa, by simp⟩, rfl⟩
    · exact Or.inr (Or.inr (alias_in_insert al hpa rest h))

/-- Every `let` has its alias in the closed body. -/
theorem alias_mem {al : List (Port × String)} {T : List Stmt} (hT : Acyclic T)
    {pa : Port × String} (hpa : pa ∈ al) :
    aliasStmt pa.1 pa.2 ∈ frontAliases al T ++ insertAliases al T := by
  by_cases hw : pa.2 ∈ writesOf T
  · obtain ⟨r, hr⟩ := mem_of_writes hT hw
    exact List.mem_append_right _ (alias_in_insert al hpa T hr)
  · refine List.mem_append_left _ ?_
    simp only [frontAliases, List.mem_map, List.mem_filter]
    exact ⟨pa, ⟨hpa, by simpa using hw⟩, rfl⟩

theorem mem_byAssign {body : List Stmt} {l : String} {r : Expr} (h : Stmt.assign l r ∈ body) :
    l ∈ byAssignOf body := by
  unfold byAssignOf
  refine List.mem_flatMap.mpr ⟨Stmt.assign l r, ?_, by simp [stmtWrites]⟩
  rw [combOf_eq]
  exact List.mem_filter.mpr ⟨h, rfl⟩

/-- A list of singletons, index by index. -/
theorem flatMap_singleton_index {α β : Type} (f : α → List β) :
    ∀ (L : List α) (M : List β), L.length = M.length →
      (∀ (k : Nat) (a : α) (b : β), L[k]? = some a → M[k]? = some b → f a = [b]) →
      L.flatMap f = M
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: L, b :: M, h, hall => by
    rw [List.flatMap_cons, hall 0 a b rfl rfl,
      flatMap_singleton_index f L M (by simpa using h)
        (fun k a' b' ha hb => hall (k + 1) a' b' (by simpa using ha) (by simpa using hb))]
    rfl

theorem linkW_assigns (ch : String → Option Module) :
    ∀ (X : List Stmt), (∀ st ∈ X, ∃ l r, st = Stmt.assign l r) →
      X.flatMap (linkW ch) = writesOf X
  | [], _ => rfl
  | st :: X, h => by
    obtain ⟨l, r, rfl⟩ := h _ (List.mem_cons_self ..)
    rw [List.flatMap_cons, linkW_assigns ch X (fun s hs => h s (List.mem_cons_of_mem _ hs))]
    rfl

/-! ## The assembly -/

set_option maxHeartbeats 4000000 in
/-- **`closeInsts` returns a module** (one-output calls of gate children),
from the facts of the transition's run, its `let` closing, and the children. -/
theorem closeInsts_of_facts {P : String → Prop} {bnd : Lean.FVarId → Option String}
    {t t' : Module} {lay : Layout} {d : Design} {bodyB : List Stmt} {w : String}
    {PI ls : List Port} {kI n K : Nat} {cs : List Nat} {insts : List (List Nat)}
    {children : List (Module × Design)}
    (hK : K ≠ 0) (hcl : closeLets K t = some t')
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
    (hd : d.modules = [])
    (hchild : ∀ (k : Nat) (c : Module × Design), children[k]? = some c → ChildComb c.1 ∧
      c.2.modules = [] ∧
      (∀ args : List Nat, insts[k]? = some args → c.1.inputs.length = args.length) ∧
      c.1.name ≠ t.name)
    (hcons : ∀ a ∈ children, ∀ b ∈ children, a.1.name = b.1.name → a.1 = b.1)
    (hfreshOuts : ∀ (k : Nat) (c : Module × Design), children[k]? = some c →
      ∀ o ∈ lay.outs, o.name ≠ s!"inst{k}_{c.1.name}") :
    (closeInsts PI.length kI n (t.inputs.map (·.name)) insts children
      (closeMachine lay t', d)).isSome = true := by
  obtain ⟨w0, al, core, hpw, hops, ht', hord⟩ := closeLets_eq hK hcl
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
  -- name resolution
  obtain ⟨hres, hmods⟩ := designWith_resolves hd
    (fun c hc => by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
      exact (hchild k c hk).2.1) hcons
  -- the instance statements
  obtain ⟨stmts, hst, hslen, hcalls, outWs, houtWs⟩ := instStmts_some (PI := PI) (ls := ls)
    (kI := kI) (n := n) (K := K) (insts := insts) (children := children) (m := M) (d := d)
    hkI hchL hlsLen hlsNd hargsK
    (fun k c hc => ⟨(hchild k c hc).1, (hchild k c hc).2.2.1, hres c (List.mem_of_getElem? hc)⟩)
    (fun p hp => ⟨p, hwsub p (htw ▸ hinW p (hlsMem p hp)), rfl⟩)
    (by
      intro k c hc hmem
      simp only [List.mem_append, List.mem_map] at hmem
      rcases hmem with (⟨p, hp, he⟩ | ⟨p, hp, he⟩) | ⟨p, hp, he⟩
      · rcases hinsub p hp with h | h | h
        · exact instName_not_allocated k c.1.name
            (he ▸ hwAlloc p (hinW p (List.mem_of_mem_take (hti ▸ h))))
        · exact instName_ne_clk k c.1.name (he.symm.trans h)
        · exact instName_ne_rst k c.1.name (he.symm.trans h)
      · rw [houts] at hp
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hp
        exact hfreshOuts k c hc o ho he
      · rcases hwsup p hp with h | ⟨x, hx⟩
        · exact instName_not_allocated k c.1.name (he ▸ hwAlloc p (htw ▸ h))
        · exact instName_ne_next k c.1.name x (he.symm.trans hx))
  have hcallOf : ∀ st ∈ stmts, ∃ k, k < kI ∧ IsCall ls kI n insts children k st := by
    intro st hs
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hs
    exact ⟨k, hslen ▸ (List.getElem?_eq_some_iff.mp hk).1, hcalls k st hk⟩
  have hinstAll : stmts.all isInst = true := by
    rw [List.all_eq_true]
    intro st hs
    obtain ⟨k, _, args, c, outPort, outP, _, _, _, _, rfl⟩ := hcallOf st hs
    rfl
  -- the body, in the form the classification is stated for
  have hTa : ∀ st ∈ bodyB.reverse, ∃ l r, st = Stmt.assign l r := Acyclic.assign hT
  have hcombC := closed_comb (T := bodyB.reverse) (al := al) (core := core) (ps := ps) (lay := lay)
    (R := registers lay.resetKind ps lay.slots) (stmts := stmts) hTa hR outsOk
  -- what the assignments of the body drive
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
    · obtain ⟨k', _, args, c, outPort, outP, _, _, _, _, rfl⟩ := hcallOf st h
      simp [stmtWrites] at hw
  -- each instance: what it drives and reads
  have hcallFacts : ∀ (k : Nat) (st : Stmt), stmts[k]? = some st →
      ∃ (args : List Nat) (c : Module × Design) (outPort outP : Port),
      k < kI ∧ insts[k]? = some args ∧ children[k]? = some c ∧
      ls[k]? = some outPort ∧ c.1.outputs = [outP] ∧
      st = .inst c.1.name s!"inst{k}_{c.1.name}"
        (callConns c.1.inputs (argWsOf ls kI n args) outP outPort.name) ∧
      combWrites (byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) st = [outPort.name] ∧
      ∀ x ∈ combReads (byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) st,
        ∃ a ∈ args, ∃ p, ls[kI + n + a]? = some p ∧ x = p.name := by
    intro k st hkst
    have hk : k < kI := hslen ▸ (List.getElem?_eq_some_iff.mp hkst).1
    obtain ⟨args, c, outPort, outP, hargs, hc, hop, hout, rfl⟩ := hcalls k st hkst
    have hargsIn : ∀ a ∈ args, ∃ p, ls[kI + n + a]? = some p ∧
        ((ls[kI + n + a]?).map (·.name)).getD "" = p.name := by
      intro a ha
      have hlt : kI + n + a < ls.length := by
        have := hargsK k args hargs a ha
        omega
      exact ⟨_, List.getElem?_eq_getElem hlt, by rw [List.getElem?_eq_getElem hlt]; rfl⟩
    obtain ⟨hcw, hrd⟩ := conns_comb (mn := c.1.name) (iname := s!"inst{k}_{c.1.name}")
      (ins := c.1.inputs) (outP := outP) (argWs := argWsOf ls kI n args) (outW := outPort.name)
      (by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        obtain ⟨p, hp, he⟩ := hargsIn a ha
        rw [he]
        exact hAargs a p hp)
      (hAout k outPort hk hop)
    refine ⟨args, c, outPort, outP, hk, hargs, hc, hop, hout, rfl, hcw, fun x hx => ?_⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (hrd x hx)
    obtain ⟨p, hp, he⟩ := hargsIn a ha
    exact ⟨a, ha, p, hp, he⟩
  have instAt : ∀ (k : Nat) (p : Port), k < kI → ls[k]? = some p →
      ((ls.take kI).map (·.name))[k]? = some p.name := by
    intro k p hk hp
    rw [List.getElem?_map, List.getElem?_take, if_pos hk, hp]
    rfl
  -- the classification of the driven names, then the rank
  obtain ⟨_, hD⟩ := closed_classes (T := bodyB.reverse) (al := al) (core := core) (ps := ps)
    (lay := lay) (R := registers lay.resetKind ps lay.slots) (stmts := stmts)
    (instNames := (ls.take kI).map (·.name)) hTa hR outsOk
    (by
      intro st hs
      obtain ⟨k, hkst⟩ := List.mem_iff_getElem?.mp hs
      obtain ⟨args, c, outPort, outP, hk, _, _, hop, _, _, hcw, _⟩ := hcallFacts k st hkst
      exact ⟨outPort.name, List.mem_of_getElem? (instAt k outPort hk hop), hcw⟩)
  obtain ⟨pres, hsingle, hρ⟩ := rank_of_facts (P := P) (bnd := bnd) (t := t) (bodyB := bodyB)
    (w := w) (ls := ls) (kI := kI) (n := n) (cs := cs) (al := al) (es := es) (ws := ws)
    (core := core) (stmts := stmts) hbody hacy hnamed hnw hPls hlsAlloc hlsNd hal hfacts
    (fun j hj => by
      obtain ⟨c, h1, h2⟩ := hcsK j hj
      exact ⟨c, h1, hKal ▸ h2⟩)
    hcoreA
    (by
      intro st hs
      obtain ⟨k, hkst⟩ := List.mem_iff_getElem?.mp hs
      obtain ⟨args, c, outPort, outP, hk, hargs, _, hop, _, _, hcw, hrd⟩ := hcallFacts k st hkst
      obtain ⟨cc, hcc, _⟩ := hcsK k hk
      refine ⟨k, outPort.name, cc, instAt k outPort hk hop, hcc, hcw, fun x hx => ?_⟩
      obtain ⟨a, ha, p, hp, rfl⟩ := hrd x hx
      exact ⟨a, (letAt a p hp).1, hcsA k args cc hargs hcc a ha⟩)
    hcombC hD
  -- the static facts of the body
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
  -- the linked view
  have hlinkAt : ∀ (k : Nat) (st : Stmt), stmts[k]? = some st → ∀ p : Port, ls[k]? = some p →
      linkW (moduleByName (designWith children d).modules) st = [p.name] := by
    intro k st hk p hp
    obtain ⟨args, c, outPort, outP, hargs, hc, hop, hout, rfl⟩ := hcalls k st hk
    rw [hp] at hop
    cases hop
    obtain ⟨hcomb, _, _, _⟩ := hchild k c hc
    simp only [linkW, stmtOuts, hres c (List.mem_of_getElem? hc), hout]
    exact conns_instOuts (fun q hq e => by
      obtain ⟨ty, hty⟩ := hcomb.output
      rw [hout] at hty
      have : outP.name = "out" := by
        have := congrArg (fun l => l.map (·.name)) hty
        simpa using this
      exact out_not_allocated ((e.trans this) ▸ hcomb.inputAlloc q hq))
  have hlinkStmts : stmts.flatMap (linkW (moduleByName (designWith children d).modules)) =
      (ls.take kI).map (·.name) := by
    refine flatMap_singleton_index _ stmts _ (by simp [hslen]; omega) ?_
    intro k st b hk hb
    have hkk : k < kI := hslen ▸ (List.getElem?_eq_some_iff.mp hk).1
    rw [List.getElem?_map, List.getElem?_take, if_pos hkk] at hb
    cases hp : ls[k]? with
    | none => rw [hp] at hb; cases hb
    | some p =>
      rw [hp] at hb
      cases hb
      exact hlinkAt k st hk p hp
  have hasgAll : ∀ st ∈ (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        nextAssigns core ps lay.slots) ++ outAssigns core lay.outs), ∃ l r, st = Stmt.assign l r :=
    Acyclic.assign (by rw [List.append_assoc]; exact hMacy)
  have hAsub : ∀ x ∈ writesOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        nextAssigns core ps lay.slots) ++ outAssigns core lay.outs), x ∈ byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts) := by
    intro x hx
    show x ∈ writesOf (combOf _)
    rw [hcombEq, Tools.ShippingTopoChecks.writesOf_append]
    exact List.mem_append_left _ hx
  have hbw : bodyWrites (moduleByName (designWith children d).modules) (combOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) =
      writesOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        nextAssigns core ps lay.slots) ++ outAssigns core lay.outs) ++ (ls.take kI).map (·.name) := by
    rw [hcombEq, bodyWrites_eq, List.flatMap_append, hlinkStmts, linkW_assigns _ _ hasgAll]
  have takeAt : ∀ x ∈ (ls.take kI).map (·.name), ∃ (k : Nat) (p : Port), k < kI ∧
      ls[k]? = some p ∧ x = p.name := by
    intro x hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_map, List.getElem?_take] at hk
    by_cases hkk : k < kI
    · rw [if_pos hkk] at hk
      cases hp : ls[k]? with
      | none => rw [hp] at hk; cases hk
      | some p =>
        rw [hp] at hk
        exact ⟨k, p, hkk, hp, by simpa using hk.symm⟩
    · rw [if_neg hkk] at hk
      cases hk
  have hinstMem : ∀ mn i conns, Stmt.inst mn i conns ∈
      ((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts → Stmt.inst mn i conns ∈ stmts := by
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
  -- an instance of the body, with its child
  have hinstChild : ∀ mn i conns, Stmt.inst mn i conns ∈ (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts) →
      ∃ (k : Nat) (args : List Nat) (c : Module × Design) (outPort outP : Port),
        children[k]? = some c ∧ mn = c.1.name ∧
        moduleByName (designWith children d).modules mn = some c.1 ∧ c.1.outputs = [outP] ∧
        c.1.inputs.length = (argWsOf ls kI n args).length ∧
        conns = callConns c.1.inputs (argWsOf ls kI n args) outP outPort.name ∧
        combWrites (byAssignOf (((frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
        (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
          outAssigns core lay.outs))) ++ stmts)) (.inst mn i conns) = [outPort.name] := by
    intro mn i conns hm
    obtain ⟨k, hkst⟩ := List.mem_iff_getElem?.mp (hinstMem mn i conns hm)
    obtain ⟨args, c, outPort, outP, hk, hargs, hc, hop, hout, he, hcw, _⟩ := hcallFacts k _ hkst
    cases he
    exact ⟨k, args, c, outPort, outP, hc, rfl, hres c (List.mem_of_getElem? hc), hout,
      by rw [(hchild k c hc).2.2.1 args hargs]; simp [argWsOf], rfl, hcw⟩
  obtain ⟨body, htopo, hchk⟩ := closeChecks_of (portNames := (PI ++ ls).map (·.name))
    (children := children) (mname := M.name) (d' := designWith children d)
    (mb := (frontAliases al bodyB.reverse ++ insertAliases al bodyB.reverse) ++
      (nextAssigns core ps lay.slots ++ (registers lay.resetKind ps lay.slots ++
        outAssigns core lay.outs))) (stmts := stmts)
    hinstAll (hin ▸ hnd) hwo (rankOf _ (rho bodyB.reverse pres (al.map (·.1.name))
      ((ls.take kI).map (·.name)) cs))
    (rank_of_names _ hsingle hρ) hregs hwn hnk
    (by
      rw [hbw, List.nodup_append]
      refine ⟨Acyclic.nodup (by rw [List.append_assoc]; exact hMacy), ?_, ?_⟩
      · rw [List.map_take]
        exact hlsNd.sublist (List.take_sublist _ _)
      · intro a ha b hb e
        subst e
        obtain ⟨k, p, hkk, hp, rfl⟩ := takeAt _ hb
        exact hAout k p hkk hp (hAsub _ ha))
    (by
      intro x hx
      rw [hbw] at hx
      unfold drivenOf
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (hAsub x h)
      · refine List.mem_append_right _ ?_
        obtain ⟨k, p, hkk, hp, rfl⟩ := takeAt _ h
        obtain ⟨st, hst'⟩ : ∃ st, stmts[k]? = some st :=
          ⟨_, List.getElem?_eq_getElem (hslen ▸ hkk)⟩
        obtain ⟨args, c, outPort, outP, _, _, _, hop, _, _, hcw, _⟩ := hcallFacts k st hst'
        rw [hp] at hop
        cases hop
        refine List.mem_flatMap.mpr ⟨st, ?_, by rw [hcw]; exact List.mem_singleton.mpr rfl⟩
        rw [hcombEq]
        exact List.mem_append_right _ (List.mem_of_getElem? hst'))
    (by
      intro mn i conns hm
      obtain ⟨k, args, c, outPort, outP, hc, rfl, hr, hout, _, rfl, hcw⟩ := hinstChild mn i conns hm
      obtain ⟨hcomb, _, _, _⟩ := hchild k c hc
      refine ⟨c.1, hr, ?_, fun cn hcn => ?_⟩
      · rw [hcw, hout]
        exact conns_instOuts (fun q hq e => by
          obtain ⟨ty, hty⟩ := hcomb.output
          rw [hout] at hty
          have : outP.name = "out" := by
            have := congrArg (fun l => l.map (·.name)) hty
            simpa using this
          exact out_not_allocated ((e.trans this) ▸ hcomb.inputAlloc q hq))
      · obtain ⟨wv, he, _⟩ := conns_refs cn hcn
        exact ⟨wv, he⟩)
    (by
      rw [List.all_eq_true]
      intro c hc
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
      simp [hres c hc, (hchild k c hk).2.1])
    (by
      unfold noInstOfB
      rw [List.all_eq_true]
      intro st hs
      cases st with
      | inst mn i conns =>
        obtain ⟨k, args, c, outPort, outP, hc, rfl, _, _, _, _, _⟩ := hinstChild mn i conns hs
        have := (hchild k c hc).2.2.2
        simpa [hname, htn] using this
      | _ => rfl)
    (by
      rw [List.all_eq_true]
      intro g hg
      obtain ⟨c, hc, rfl⟩ := hmods g hg
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
      have hasg := (hchild k c hk).1.assigns
      unfold noInstOfB
      rw [List.all_eq_true] at hasg ⊢
      intro st hs
      have := hasg st hs
      cases st <;> simp_all [Sparkle.IR.RegDedup.isAssign])
    (kidsCombB_of (by
      intro mn i conns hm
      obtain ⟨k, args, c, outPort, outP, hc, rfl, hr, _, hlen, rfl, _⟩ := hinstChild mn i conns hm
      exact ⟨c.1, hr, (hchild k c hc).1, _, outP, outPort.name, hlen, rfl⟩))
  rw [hin]
  exact closeInsts_some_of (m := M) (d := d) hst houtWs (by rw [hMbody]; exact htopo)
    (by rw [hMbody]; exact hchk)

end Tools.ShippingCallsAssembly
