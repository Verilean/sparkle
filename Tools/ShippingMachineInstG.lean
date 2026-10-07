import Tools.ShippingMachineInst
import Sparkle.IR.MachineInstG

/-! # The instance statements `closeInstsG` adds

A call whose result is a structure, or whose child is sequential, is tied by
`closeInstsG` (Sparkle.IR.MachineInstG): the entries of one call (the same
child and argument `let`s) are ONE instance, its input ports connected to the
argument wires, for a sequential child its `clk`/`rst` to the module's, and
each entry's output port (field) to the entry's transition input. This file
states the shape of those statements (`CallStmtG`) and that every instance
statement of the closed module is one of them (`closeInstsG_insts`). -/
namespace Tools.ShippingMachineInstG
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineInst (mapM_some)

/-- The instance statement of one call group: entries `outs` (index, field),
argument `let`s `args`, child `mc`. -/
def CallStmtG (nIn kI n : Nat) (portNames : List String) (args : List Nat)
    (outs : List (Nat × String)) (mc : Module) (st : Stmt) : Prop :=
  ∃ outWs argWs iname,
    outs.mapM (fun (k, _) => portNames[nIn + k]?) = some outWs ∧
    args.mapM (fun j => portNames[nIn + kI + n + j]?) = some argWs ∧
    (mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").length = argWs.length ∧
    ((mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").map (·.name)).Nodup ∧
    (outs.map (·.2)).all (fun f => mc.outputs.any (·.name == f)) = true ∧
    (outs.map (·.2)).Nodup ∧
    (outs.map (·.2)).any (fun f =>
      (mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").any (·.name == f)) = false ∧
    ¬ (outs.map (·.2)).contains "clk" ∧ ¬ (outs.map (·.2)).contains "rst" ∧
    outWs.any (fun w => argWs.contains w) = false ∧ outWs.Nodup ∧
    st = .inst mc.name iname
      (((mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").zip argWs).map
          (fun (p, w) => (p.name, Expr.ref w)) ++
        (if mc.inputs.any (fun p => p.name == "clk" || p.name == "rst") then
          [("clk", Expr.ref "clk"), ("rst", Expr.ref "rst")] else []) ++
        ((outs.map (·.2)).zip outWs).map (fun (f, w) => (f, Expr.ref w)))

theorem instStmtG_some {nIn kI n : Nat} {portNames : List String} {gi : Nat} {args : List Nat}
    {outs : List (Nat × String)} {mc m : Module} {st : Stmt}
    (h : instStmtG nIn kI n portNames gi args outs mc m = some st) :
    CallStmtG nIn kI n portNames args outs mc st := by
  unfold instStmtG at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨outWs, hout, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨argWs, hargs, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  rename_i hlen
  split at h
  · cases h
  rename_i hnd
  split at h
  · cases h
  rename_i hfields
  split at h
  · cases h
  rename_i hdisj
  split at h
  · cases h
  rename_i houtWs
  split at h
  · cases h
  rename_i hwires
  split at h
  · cases h
  split at h
  · cases h
  cases h
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.not_eq_true, Bool.or_eq_true,
    not_or, Bool.not_eq_false] at hlen hnd hfields hdisj houtWs
  refine ⟨outWs, argWs, _, hout, hargs, by simpa using hlen, by simpa using hnd, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, rfl⟩
  · simpa using hfields.1
  · simpa using hfields.2
  · simpa using hdisj.1.1
  · simpa using hdisj.1.2
  · simpa using hdisj.2
  · simpa using houtWs.1
  · simpa using houtWs.2

/-! ## The groups of `callGroups` -/

theorem mem_modify {α : Type} {f : α → α} {l : List α} {i : Nat} {x : α}
    (h : x ∈ l.modify i f) : x ∈ l ∨ ∃ y, l[i]? = some y ∧ x = f y := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  have hg := List.getElem?_modify f i l j
  rw [List.getElem?_eq_getElem hj] at hg
  by_cases hij : i = j
  · subst hij
    cases hl : l[i]? with
    | none => rw [hl] at hg; simp at hg
    | some y =>
      rw [hl] at hg
      simp only [if_true, Option.map_eq_map, Option.map_some, Option.some.injEq] at hg
      exact Or.inr ⟨y, rfl, hg⟩
  · cases hl : l[j]? with
    | none => rw [hl] at hg; simp at hg
    | some y =>
      rw [hl] at hg
      simp only [if_neg hij, Option.map_eq_map, Option.map_some, Option.some.injEq] at hg
      exact Or.inl (by rw [hg]; exact List.mem_of_getElem? hl)

/-- What the grouping keeps: every group is non-empty and its entries share
the key of its first entry. -/
def GroupsOk {κ : Type} (keys : List κ) (gs : List (List Nat)) : Prop :=
  ∀ g ∈ gs, ∃ k0 rest, g = k0 :: rest ∧ ∀ k ∈ g, keys[k]? = keys[k0]?

theorem mem_modify_append {l : List (List Nat)} {i k : Nat} {x : List Nat}
    (h : x ∈ l.modify i (· ++ [k])) : x ∈ l ∨ ∃ y, l[i]? = some y ∧ x = y ++ [k] :=
  mem_modify h

/-- One step of `callGroups`. -/
def groupStep (keys : List (String × List Nat)) (gs : List (List Nat))
    (p : (String × List Nat) × Nat) : List (List Nat) :=
  match gs.findIdx? (fun g => (g.head? >>= fun k0 => keys[k0]?) == some p.1) with
  | some gi => gs.modify gi (· ++ [p.2])
  | none => gs ++ [[p.2]]

theorem callGroups_eq (keys : List (String × List Nat)) :
    callGroups keys = keys.zipIdx.foldl (groupStep keys) [] := rfl

theorem callGroups_fold (keys : List (String × List Nat)) :
    ∀ (L : List ((String × List Nat) × Nat)) (gs : List (List Nat)),
      (∀ p ∈ L, keys[p.2]? = some p.1) → GroupsOk keys gs →
      GroupsOk keys (L.foldl (groupStep keys) gs) ∧
        (∀ p ∈ L, ∃ g ∈ L.foldl (groupStep keys) gs, p.2 ∈ g) ∧
        (∀ g ∈ gs, ∀ k ∈ g, ∃ g' ∈ L.foldl (groupStep keys) gs, k ∈ g')
  | [], gs, _, hok => ⟨hok, fun _ hp => absurd hp List.not_mem_nil, fun g hg k hk => ⟨g, hg, hk⟩⟩
  | (key, k) :: L, gs, hL, hok => by
    have hk : keys[k]? = some key := hL (key, k) List.mem_cons_self
    -- one step
    let gs1 := groupStep keys gs (key, k)
    have hstep : GroupsOk keys gs1 ∧ (∃ g ∈ gs1, k ∈ g) ∧
        (∀ g ∈ gs, ∀ k' ∈ g, ∃ g' ∈ gs1, k' ∈ g') := by
      cases hf : gs.findIdx? (fun g => (g.head? >>= fun k0 => keys[k0]?) == some key) with
      | none =>
        simp only [gs1, groupStep, hf]
        refine ⟨?_, ⟨[k], by simp, by simp⟩, fun g hg k' hk' => ⟨g, by simp [hg], hk'⟩⟩
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hok g hg
        · simp at hg; subst hg; exact ⟨k, [], rfl, by simp⟩
      | some gi =>
        simp only [gs1, groupStep, hf]
        obtain ⟨hgi, hsat⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
        have hsat := hsat.1
        refine ⟨?_, ⟨gs[gi] ++ [k], ?_, by simp⟩, ?_⟩
        · intro g hg
          rcases mem_modify_append hg with hg | ⟨y, hy, rfl⟩
          · exact hok g hg
          · have hy' : y = gs[gi] := by
              rw [List.getElem?_eq_getElem hgi] at hy; exact (Option.some.inj hy).symm
            subst hy'
            obtain ⟨k0, rest, hg0, hall⟩ := hok gs[gi] (List.getElem_mem hgi)
            refine ⟨k0, rest ++ [k], by rw [hg0]; rfl, ?_⟩
            intro k' hk'
            rcases List.mem_append.mp hk' with hk' | hk'
            · exact hall k' hk'
            · simp at hk'; subst hk'
              rw [hk]
              rw [hg0] at hsat
              exact (by simpa using hsat : keys[k0]? = some key).symm
        · have : (gs.modify gi (· ++ [k]))[gi]? = some (gs[gi] ++ [k]) := by
            rw [List.getElem?_modify_eq, List.getElem?_eq_getElem hgi]; rfl
          exact List.mem_of_getElem? this
        · intro g hg k' hk'
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
          by_cases hij : gi = j
          · subst hij
            refine ⟨gs[gi] ++ [k], ?_, List.mem_append_left _ hk'⟩
            have : (gs.modify gi (· ++ [k]))[gi]? = some (gs[gi] ++ [k]) := by
              rw [List.getElem?_modify_eq, List.getElem?_eq_getElem hgi]; rfl
            exact List.mem_of_getElem? this
          · refine ⟨gs[j], ?_, hk'⟩
            have : (gs.modify gi (· ++ [k]))[j]? = some gs[j] := by
              rw [List.getElem?_modify_ne _ _ hij, List.getElem?_eq_getElem hj]
            exact List.mem_of_getElem? this
    obtain ⟨hok1, ⟨gk, hgk, hkg⟩, hkeep⟩ := hstep
    obtain ⟨hok', hcov, hkeep'⟩ := callGroups_fold keys L gs1
      (fun p hp => hL p (List.mem_cons_of_mem _ hp)) hok1
    refine ⟨hok', ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hkeep' gk hgk k hkg
      · exact hcov p hp
    · intro g hg k' hk'
      obtain ⟨g1, hg1, hk1⟩ := hkeep g hg k' hk'
      exact hkeep' g1 hg1 k' hk1

/-- **The groups of the calls.** Every group is non-empty and its entries
share its first entry's key; every entry is in a group. -/
theorem callGroups_ok (keys : List (String × List Nat)) :
    GroupsOk keys (callGroups keys) ∧ ∀ k, k < keys.length → ∃ g ∈ callGroups keys, k ∈ g := by
  rw [callGroups_eq]
  have h := callGroups_fold keys keys.zipIdx [] (fun p hp => by
    obtain ⟨x, i⟩ := p
    exact List.mk_mem_zipIdx_iff_getElem?.mp hp) (fun g hg => by cases hg)
  refine ⟨h.1, fun k hk => ?_⟩
  obtain ⟨g, hg, hkg⟩ := h.2.1 (keys[k], k) (List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [hk]))
  exact ⟨g, hg, hkg⟩

/-! ## Every instance statement of the closed module -/

/-- The keys of the entries: entry `k` is a call of `children[k]` on `insts[k]`. -/
theorem keys_get {insts : List (List Nat)} {children : List (Module × Design)}
    {keys : List (String × List Nat)}
    (h : (List.range insts.length).mapM (fun k => do
      let args ← insts[k]?
      let child ← children[k]?
      pure (child.1.name, args)) = some keys) :
    keys.length = insts.length ∧ ∀ k, k < insts.length → ∃ args child,
      insts[k]? = some args ∧ children[k]? = some child ∧ keys[k]? = some (child.1.name, args) := by
  obtain ⟨hlen, hget⟩ := mapM_some _ _ keys h
  refine ⟨by simpa using hlen, fun k hk => ?_⟩
  obtain ⟨y, hy, hky⟩ := hget k (by simpa using hk)
  simp only [List.getElem_range, Option.bind_eq_bind] at hy
  obtain ⟨args, hargs, hy⟩ := Option.bind_eq_some_iff.mp hy
  obtain ⟨child, hchild, hy⟩ := Option.bind_eq_some_iff.mp hy
  simp only [pure, Option.some.injEq] at hy
  subst hy
  exact ⟨args, child, hargs, hchild, hky⟩

/-- **The instance statements `closeInstsG` adds.** Every instance statement
of the closed module is one of the original's or the statement of a call
group: `CallStmtG` for the group's child, every entry of the group a call of
that child on the group's arguments, reading the entry's field. -/
theorem closeInstsG_insts {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {fields : List String}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)) :
    ∀ st ∈ m.body, isInst st = true → st ∈ m₀.body ∨
      ∃ (args : List Nat) (outs : List (Nat × String)) (child : Module × Design) (mc : Module), CallStmtG nIn kI n portNames args outs mc st ∧
        moduleByName d.modules child.1.name = some mc ∧ outs ≠ [] ∧
        ∀ e ∈ outs, insts[e.1]? = some args ∧ (children[e.1]?).map (·.1.name) = some child.1.name ∧
          fields.getD e.1 "" = e.2 := by
  intro st hst _
  unfold closeInstsG at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨stmts, hstmts, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨outWs, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨body, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hperm⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
    cases h
    have hbd := (withClockFor_same children m₀).2.2.2
    have hmem : st ∈ (withClockFor children m₀).body ++ stmts :=
      (Sparkle.IR.Reorder.isPermOf_sound hperm).mem_iff.mpr hst
    rw [hbd] at hmem
    rcases List.mem_append.mp hmem with h0 | hs
    · exact Or.inl h0
    · right
      unfold stmtsG at hstmts
      simp only [Option.bind_eq_bind] at hstmts
      obtain ⟨keys, hkeys, hstmts⟩ := Option.bind_eq_some_iff.mp hstmts
      obtain ⟨hklen, hkget⟩ := keys_get hkeys
      obtain ⟨hgok, _⟩ := callGroups_ok keys
      obtain ⟨hlen, hget⟩ := mapM_some _ _ stmts hstmts
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
      obtain ⟨st', hst', hsti⟩ := hget i (by rw [← hlen]; exact hi)
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hsti
      subst hsti
      have hi' : i < (callGroups keys).zipIdx.length := by rw [← hlen]; exact hi
      obtain ⟨⟨g, gi⟩, hgz⟩ : ∃ p, (callGroups keys).zipIdx[i]? = some p :=
        ⟨_, List.getElem?_eq_getElem hi'⟩
      have hgmem : g ∈ callGroups keys := by
        have := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_getElem? hgz)
        exact List.mem_of_getElem? this
      obtain ⟨_, hgi⟩ := List.getElem_of_getElem? hgz
      rw [hgi] at hst'
      simp only [Option.bind_eq_bind] at hst'
      obtain ⟨k0, hk0, hst'⟩ := Option.bind_eq_some_iff.mp hst'
      obtain ⟨args, hargs, hst'⟩ := Option.bind_eq_some_iff.mp hst'
      obtain ⟨child, hchild, hst'⟩ := Option.bind_eq_some_iff.mp hst'
      obtain ⟨mc, hmc, hst'⟩ := Option.bind_eq_some_iff.mp hst'
      refine ⟨args, g.map (fun k => (k, fields.getD k "")), child, mc, instStmtG_some hst', hmc,
        ?_, ?_⟩
      · obtain ⟨k0', rest, hg, _⟩ := hgok g hgmem
        simp [hg]
      · intro e he
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
        obtain ⟨k0', rest, hg, hall⟩ := hgok g hgmem
        have hk0' : k0 = k0' := by rw [hg] at hk0; simpa using hk0.symm
        subst hk0'
        have hkk0 := hall k hk
        have hk0lt : k0 < insts.length := by
          have := List.getElem?_eq_some_iff.mp hargs; exact this.1
        obtain ⟨a0, c0, ha0, hc0, hkey0⟩ := hkget k0 hk0lt
        rw [hargs] at ha0; cases ha0
        rw [hchild] at hc0; cases hc0
        have hklt : k < keys.length := by
          rcases Nat.lt_or_ge k keys.length with hlt | hge
          · exact hlt
          · rw [List.getElem?_eq_none hge, hkey0] at hkk0; cases hkk0
        obtain ⟨a1, c1, ha1, hc1, hkey1⟩ := hkget k (by omega)
        rw [hkk0, hkey0] at hkey1
        simp only [Option.some.injEq, Prod.mk.injEq] at hkey1
        obtain ⟨hn, ha⟩ := hkey1
        refine ⟨by rw [ha1, ha], by rw [hc1, Option.map_some, hn], rfl⟩
  · cases h

/-- **Every call is an instance's output.** For each entry `k` there is the
instance statement of its group in the closed module, reading the entry's
field into the entry's transition input. -/
theorem closeInstsG_calls {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {fields : List String}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)) :
    ∀ k, k < insts.length → ∃ st ∈ m.body, ∃ (args : List Nat) (outs : List (Nat × String))
      (child : Module × Design) (mc : Module), CallStmtG nIn kI n portNames args outs mc st ∧
      moduleByName d.modules child.1.name = some mc ∧ (k, fields.getD k "") ∈ outs ∧
      insts[k]? = some args ∧ (children[k]?).map (·.1.name) = some child.1.name := by
  intro k hk
  unfold closeInstsG at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨stmts, hstmts, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨outWs, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨body, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hperm⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
    cases h
    have hbd := (withClockFor_same children m₀).2.2.2
    unfold stmtsG at hstmts
    simp only [Option.bind_eq_bind] at hstmts
    obtain ⟨keys, hkeys, hstmts⟩ := Option.bind_eq_some_iff.mp hstmts
    obtain ⟨hklen, hkget⟩ := keys_get hkeys
    obtain ⟨hgok, hcov⟩ := callGroups_ok keys
    obtain ⟨g, hgmem, hkg⟩ := hcov k (by omega)
    obtain ⟨gi, hgi, hgget⟩ := List.getElem_of_mem hgmem
    obtain ⟨hlen, hget⟩ := mapM_some _ _ stmts hstmts
    have hgi' : gi < (callGroups keys).zipIdx.length := by simpa using hgi
    obtain ⟨st, hst, hsti⟩ := hget gi hgi'
    have hz : (callGroups keys).zipIdx[gi] = ((callGroups keys)[gi], gi) := by simp
    rw [hz] at hst
    simp only [Option.bind_eq_bind] at hst
    obtain ⟨k0, hk0, hst⟩ := Option.bind_eq_some_iff.mp hst
    obtain ⟨args, hargs, hst⟩ := Option.bind_eq_some_iff.mp hst
    obtain ⟨child, hchild, hst⟩ := Option.bind_eq_some_iff.mp hst
    obtain ⟨mc, hmc, hst⟩ := Option.bind_eq_some_iff.mp hst
    rw [hgget] at hk0 hst
    -- `st` is in the closed module
    have hstm : st ∈ m₀.body ++ stmts := List.mem_append_right _ (List.mem_of_getElem? hsti)
    rw [← hbd] at hstm
    refine ⟨st, (Sparkle.IR.Reorder.isPermOf_sound hperm).mem_iff.mp hstm, args,
      g.map (fun k => (k, fields.getD k "")), child, mc, instStmtG_some hst, hmc,
      List.mem_map.mpr ⟨k, hkg, rfl⟩, ?_⟩
    -- entry `k` shares the group's key
    obtain ⟨k0', rest, hg, hall⟩ := hgok g hgmem
    have hk0' : k0 = k0' := by rw [hg] at hk0; simpa using hk0.symm
    subst hk0'
    have hkk0 := hall k hkg
    have hk0lt : k0 < insts.length := (List.getElem?_eq_some_iff.mp hargs).1
    obtain ⟨a0, c0, ha0, hc0, hkey0⟩ := hkget k0 hk0lt
    rw [hargs] at ha0; cases ha0
    rw [hchild] at hc0; cases hc0
    obtain ⟨a1, c1, ha1, hc1, hkey1⟩ := hkget k hk
    rw [hkk0, hkey0] at hkey1
    simp only [Option.some.injEq, Prod.mk.injEq] at hkey1
    obtain ⟨hn, ha⟩ := hkey1
    exact ⟨by rw [ha1, ha], by rw [hc1, Option.map_some, hn]⟩
  · cases h

/-- The closed module's instances have distinct names and none feeds itself
(`closeInstsG`'s checks). -/
theorem closeInstsG_names {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {fields : List String}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)) :
    (m.body.filterMap instNameOf).Nodup ∧ noSelfFeed (moduleByName d.modules) m.body = true ∧
      ∀ c ∈ children, Sparkle.Compiler.MachMemory.memSelf (moduleByName d.modules) c.1 = true := by
  unfold closeInstsG at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨stmts, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨outWs, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨body, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨_, hnames⟩, hfeed⟩, hmem⟩ := hc
    cases h
    exact ⟨hnames, hfeed, List.all_eq_true.mp hmem⟩
  · cases h

/-! ## The memory children's module -/

open Sparkle.Compiler.MachMemory in
theorem portKey_inj : ∀ {a b : List Port}, portKey a = portKey b → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [portKey] at h
  | _ :: _, [], h => by simp [portKey] at h
  | ⟨n, t⟩ :: as, ⟨n', t'⟩ :: bs, h => by
    simp only [portKey, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    rw [portKey_inj (a := as) (b := bs) (by simpa [portKey] using h)]

open Sparkle.Compiler.MachMemory in
/-- The recognizer is exact: a module it accepts IS the built memory module. -/
theorem isMemModule_eq {cb : Bool} {aw dw : Nat} {m : Module} (h : isMemModule cb aw dw m = true) :
    m = (memModule cb aw dw).1 := by
  obtain ⟨name, params, ins, outs, wires, body, asserts, prim⟩ := m
  unfold isMemModule at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, hp⟩, hi⟩, ho⟩, hw⟩, ha⟩, hpr⟩, hb⟩ := h
  split at hb
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := hb
    subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    subst hp ha hpr
    rw [portKey_inj hi, portKey_inj ho, portKey_inj hw, hn]
    rfl
  · cases hb

open Sparkle.Compiler.MachMemory in
theorem memParams_memModule (cb : Bool) (aw dw : Nat) :
    memParams? (memModule cb aw dw).1 = some (cb, aw, dw) := rfl

open Sparkle.Compiler.MachMemory in
/-- A memory child's name finds the built memory module, in a design passing
`closeInstsG`'s check. -/
theorem find_memModule {find : String → Option Module} {cb : Bool} {aw dw : Nat} {mc : Module}
    (hs : memSelf find (memModule cb aw dw).1 = true)
    (hf : find (memModule cb aw dw).1.name = some mc) : mc = (memModule cb aw dw).1 := by
  unfold memSelf at hs
  rw [memParams_memModule, hf] at hs
  exact isMemModule_eq (by simpa using hs)

open Sparkle.Compiler.MachMemory in
theorem memChild_eq {c : Lean.Name} {md : Module × Design} (h : memChild? c = some md) :
    ∃ cb aw dw, md = memModule cb aw dw := by
  unfold memChild? at h
  split at h
  · split at h
    · cases h; exact ⟨_, _, _, rfl⟩
    · split at h
      · cases h; exact ⟨_, _, _, rfl⟩
      · cases h
  · cases h

end Tools.ShippingMachineInstG
