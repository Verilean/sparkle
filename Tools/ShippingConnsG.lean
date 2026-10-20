import Tools.ShippingInstStmtG
import Tools.ShippingInstNames
import Tools.ShippingTopoBody

/-! # The connections of a call group's instance, in the views of the checks

`callConnsG` on a group `g` of entries (entry `k` reads field `f k` on wire
`h k`), as the checks of `closeInstsG` read it:

* the order's view (`combWrites` / `combReads`): the connected wires no
  assignment drives are the entries' wires and, for a sequential child,
  `clk` / `rst`; the reads are argument wires;
* the linked view (`instOuts`): exactly the entries' wires, distinct — when
  the child's output ports are distinct and none is named as an input, a
  clock or a reset, and the entries read different fields;
* no self-feed; instance names of different groups differ.

Pure lists. -/
namespace Tools.ShippingConnsG
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Tools.ShippingInstStmtG Tools.ShippingInstStmt Tools.ShippingInstNames

theorem zip_maps {α β γ : Type} (f : α → β) (h : α → γ) :
    ∀ (g : List α), (g.map f).zip (g.map h) = g.map fun k => (f k, h k)
  | [] => rfl
  | k :: g => by simp [zip_maps f h g]

theorem filterMap_congr' {α β : Type} {φ ψ : α → Option β} : ∀ (l : List α),
    (∀ x ∈ l, φ x = ψ x) → l.filterMap φ = l.filterMap ψ
  | [], _ => rfl
  | a :: l, h => by
    have ih := filterMap_congr' l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.filterMap_cons, h a (List.mem_cons_self ..), ih]

theorem nodup_of_map {α β : Type} (f : α → β) : ∀ (l : List α), (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp h
    exact List.nodup_cons.mpr ⟨fun hm => h1 (List.mem_map_of_mem hm), nodup_of_map f l h2⟩

theorem instOutWires_eq (outs : List Port) (conns : List (String × Expr)) :
    instOutWiresOf outs conns = instOuts outs conns := by
  unfold instOutWiresOf instOuts
  refine filterMap_congr' _ (fun p _ => ?_)
  cases conns.lookup p.name with
  | none => rfl
  | some e => cases e <;> rfl

/-- The connections, the fields and wires of a group spelled out. -/
theorem connsG_eq (ins : List Port) (argWs : List String) (seq : Bool) (g : List Nat)
    (f h : Nat → String) :
    callConnsG ins argWs seq (g.map f) (g.map h) =
      (ins.zip argWs).map (fun (x : Port × String) => (x.1.name, Expr.ref x.2)) ++
        (if seq then [("clk", Expr.ref "clk"), ("rst", Expr.ref "rst")] else []) ++
        g.map (fun k => (f k, Expr.ref (h k))) := by
  unfold callConnsG
  rw [zip_maps, List.map_map]
  rfl

theorem mem_connsG {ins : List Port} {argWs : List String} {seq : Bool} {g : List Nat}
    {f h : Nat → String} {c : String × Expr}
    (hc : c ∈ callConnsG ins argWs seq (g.map f) (g.map h)) :
    (∃ p ∈ ins, c.1 = p.name ∧ ∃ w ∈ argWs, c.2 = Expr.ref w) ∨
    (seq = true ∧ (c = ("clk", Expr.ref "clk") ∨ c = ("rst", Expr.ref "rst"))) ∨
    ∃ k ∈ g, c = (f k, Expr.ref (h k)) := by
  rw [connsG_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · left
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    obtain ⟨h1, h2⟩ := List.of_mem_zip hx
    exact ⟨x.1, h1, rfl, x.2, h2, rfl⟩
  · right; left
    cases seq with
    | false => simp at hc
    | true =>
      simp only [if_true, List.mem_cons, List.mem_nil_iff, or_false] at hc
      exact ⟨rfl, hc⟩
  · right; right
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
    exact ⟨k, hk, rfl⟩

theorem field_mem_connsG {ins : List Port} {argWs : List String} {seq : Bool} {g : List Nat}
    {f h : Nat → String} {k : Nat} (hk : k ∈ g) :
    (f k, Expr.ref (h k)) ∈ callConnsG ins argWs seq (g.map f) (g.map h) := by
  rw [connsG_eq]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨k, hk, rfl⟩)

/-! ## The order's view -/

theorem mem_combWrites_inst {A : List String} {mn i : String} {conns : List (String × Expr)}
    {w : String} : w ∈ combWrites A (.inst mn i conns) ↔ w ∉ A ∧ ∃ p, (p, Expr.ref w) ∈ conns := by
  simp only [combWrites, List.mem_filterMap]
  constructor
  · rintro ⟨⟨p, e⟩, hc, he⟩
    cases e <;> simp only [] at he <;> try cases he
    split at he
    · cases he
    · cases he
      exact ⟨by simp_all, p, hc⟩
  · rintro ⟨hA, p, hc⟩
    exact ⟨(p, Expr.ref w), hc, by simp [hA]⟩

theorem mem_combReads_inst {A : List String} {mn i : String} {conns : List (String × Expr)}
    {x : String} (h : x ∈ combReads A (.inst mn i conns)) :
    x ∈ A ∧ ∃ c ∈ conns, x ∈ refsOf c.2 := by
  simp only [combReads, List.mem_flatMap, List.mem_filter] at h
  obtain ⟨c, hc, hx, hA⟩ := h
  exact ⟨by simpa using hA, c, hc, hx⟩

/-- **The order's view of a group's instance.** -/
theorem connsG_comb {A : List String} {mn i : String} {ins : List Port} {argWs : List String}
    {seq : Bool} {g : List Nat} {f h : Nat → String}
    (hargs : ∀ w ∈ argWs, w ∈ A) (hout : ∀ k ∈ g, h k ∉ A)
    (hclk : "clk" ∉ A) (hrst : "rst" ∉ A) :
    (∀ w, w ∈ combWrites A (.inst mn i (callConnsG ins argWs seq (g.map f) (g.map h))) ↔
      (seq = true ∧ (w = "clk" ∨ w = "rst")) ∨ w ∈ g.map h) ∧
    ∀ x ∈ combReads A (.inst mn i (callConnsG ins argWs seq (g.map f) (g.map h))), x ∈ argWs := by
  refine ⟨fun w => ?_, fun x hx => ?_⟩
  · rw [mem_combWrites_inst]
    constructor
    · rintro ⟨hA, p, hc⟩
      rcases mem_connsG hc with ⟨_, _, _, w', hw', he⟩ | ⟨hs, he | he⟩ | ⟨k, hk, he⟩
      · simp only [Expr.ref.injEq] at he
        exact absurd (hargs w (he ▸ hw')) hA
      · simp only [Prod.mk.injEq, Expr.ref.injEq] at he
        exact Or.inl ⟨hs, Or.inl he.2⟩
      · simp only [Prod.mk.injEq, Expr.ref.injEq] at he
        exact Or.inl ⟨hs, Or.inr he.2⟩
      · simp only [Prod.mk.injEq, Expr.ref.injEq] at he
        exact Or.inr (List.mem_map.mpr ⟨k, hk, he.2.symm⟩)
    · rintro (⟨hs, rfl | rfl⟩ | hm)
      · refine ⟨hclk, "clk", ?_⟩
        rw [connsG_eq, hs]
        simp
      · refine ⟨hrst, "rst", ?_⟩
        rw [connsG_eq, hs]
        simp
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
        exact ⟨hout k hk, f k, field_mem_connsG hk⟩
  · obtain ⟨hA, c, hc, hxc⟩ := mem_combReads_inst hx
    rcases mem_connsG hc with ⟨_, _, _, w', hw', he⟩ | ⟨_, he | he⟩ | ⟨k, hk, he⟩
    · rw [he] at hxc
      have : x = w' := by simpa [refsOf] using hxc
      exact this ▸ hw'
    · rw [he] at hxc
      have : x = "clk" := by simpa [refsOf] using hxc
      exact absurd (this ▸ hA) hclk
    · rw [he] at hxc
      have : x = "rst" := by simpa [refsOf] using hxc
      exact absurd (this ▸ hA) hrst
    · rw [he] at hxc
      have : x = h k := by simpa [refsOf] using hxc
      exact absurd (this ▸ hA) (hout k hk)

/-- Every connection of a group's instance is a wire. -/
theorem connsG_refs {ins : List Port} {argWs : List String} {seq : Bool} {g : List Nat}
    {f h : Nat → String} :
    ∀ c ∈ callConnsG ins argWs seq (g.map f) (g.map h), ∃ w, c.2 = Expr.ref w := by
  intro c hc
  rcases mem_connsG hc with ⟨_, _, _, w', _, he⟩ | ⟨_, he | he⟩ | ⟨k, _, he⟩
  · exact ⟨w', he⟩
  · exact ⟨"clk", by rw [he]⟩
  · exact ⟨"rst", by rw [he]⟩
  · exact ⟨h k, by rw [he]⟩

/-! ## The linked view -/

theorem lookup_fields (f h : Nat → String) (x : String) :
    ∀ (g : List Nat), (g.map fun k => (f k, Expr.ref (h k))).lookup x =
      (g.find? fun k => x == f k).map fun k => Expr.ref (h k)
  | [] => rfl
  | k :: g => by
    simp only [List.map_cons, List.lookup_cons, List.find?_cons]
    cases hx : x == f k with
    | true => rfl
    | false => exact lookup_fields f h x g

theorem lookup_connsG {ins : List Port} {argWs : List String} {seq : Bool} {g : List Nat}
    {f h : Nat → String} {x : String} (hin : ∀ p ∈ ins, p.name ≠ x) (hclk : x ≠ "clk")
    (hrst : x ≠ "rst") :
    (callConnsG ins argWs seq (g.map f) (g.map h)).lookup x =
      (g.find? fun k => x == f k).map fun k => Expr.ref (h k) := by
  have h2 : (if seq then [("clk", Expr.ref "clk"), ("rst", Expr.ref "rst")] else []).lookup x =
      none := by
    have e1 : (x == "clk") = false := by simpa using hclk
    have e2 : (x == "rst") = false := by simpa using hrst
    cases seq <;> simp [List.lookup_cons, e1, e2]
  rw [connsG_eq, List.lookup_append, List.lookup_append, lookup_zip_none ins argWs x hin, h2,
    lookup_fields]
  rfl

/-- The wire the instance drives through output port `p`. -/
def outWireOf (g : List Nat) (f h : Nat → String) (p : Port) : Option String :=
  (g.find? fun k => p.name == f k).map h

theorem instOuts_connsG {outs ins : List Port} {argWs : List String} {seq : Bool} {g : List Nat}
    {f h : Nat → String}
    (hio : ∀ p ∈ outs, (∀ q ∈ ins, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧ p.name ≠ "rst") :
    instOuts outs (callConnsG ins argWs seq (g.map f) (g.map h)) =
      outs.filterMap (outWireOf g f h) := by
  unfold instOuts
  refine filterMap_congr' _ (fun p hp => ?_)
  obtain ⟨h1, h2, h3⟩ := hio p hp
  rw [lookup_connsG h1 h2 h3]
  unfold outWireOf
  cases g.find? fun k => p.name == f k <;> rfl

theorem nodup_filterMap {α β : Type} (φ : α → Option β) : ∀ (l : List α), l.Nodup →
    (∀ a ∈ l, ∀ b ∈ l, ∀ x, φ a = some x → φ b = some x → a = b) → (l.filterMap φ).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hnd, hinj => by
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp hnd
    have ih := nodup_filterMap φ l h2
      (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    cases ha : φ a with
    | none => rw [List.filterMap_cons_none ha]; exact ih
    | some x =>
      rw [List.filterMap_cons_some ha]
      refine List.nodup_cons.mpr ⟨fun hm => ?_, ih⟩
      obtain ⟨b, hb, he⟩ := List.mem_filterMap.mp hm
      exact h1 (hinj a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) x ha he ▸ hb)

theorem port_of_name : ∀ (l : List Port), (l.map (·.name)).Nodup → ∀ a ∈ l, ∀ b ∈ l,
    a.name = b.name → a = b
  | [], _, a, ha, _, _, _ => by simp at ha
  | p :: l, hnd, a, ha, b, hb, he => by
    rw [List.map_cons] at hnd
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp ha with hpa | ha
    · rcases List.mem_cons.mp hb with hpb | hb
      · rw [hpa, hpb]
      · exact absurd (by rw [← hpa, he]; exact List.mem_map_of_mem hb) h1
    · rcases List.mem_cons.mp hb with hpb | hb
      · exact absurd (by rw [← hpb, ← he]; exact List.mem_map_of_mem ha) h1
      · exact port_of_name l h2 a ha b hb he

/-- **The linked view of a group's instance**: the wires it drives are
entries' wires, distinct, and every entry's wire is driven. -/
theorem connsG_instOuts {outs ins : List Port} {argWs : List String} {seq : Bool} {g : List Nat}
    {f h : Nat → String}
    (hio : ∀ p ∈ outs, (∀ q ∈ ins, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧ p.name ≠ "rst")
    (hond : (outs.map (·.name)).Nodup)
    (hf : ∀ a ∈ g, ∀ b ∈ g, f a = f b → a = b) (hh : ∀ a ∈ g, ∀ b ∈ g, h a = h b → a = b)
    (hfo : ∀ k ∈ g, ∃ p ∈ outs, p.name = f k) :
    (instOuts outs (callConnsG ins argWs seq (g.map f) (g.map h))).Nodup ∧
    ∀ w, w ∈ instOuts outs (callConnsG ins argWs seq (g.map f) (g.map h)) ↔ w ∈ g.map h := by
  rw [instOuts_connsG hio]
  have hfind : ∀ (p : Port) (w : String), outWireOf g f h p = some w →
      ∃ k ∈ g, p.name = f k ∧ w = h k := by
    intro p w hw
    unfold outWireOf at hw
    cases hk : g.find? (fun k => p.name == f k) with
    | none => rw [hk] at hw; cases hw
    | some k =>
      rw [hk] at hw
      exact ⟨k, List.mem_of_find?_eq_some hk, by simpa using List.find?_some hk,
        by simpa using hw.symm⟩
  refine ⟨nodup_filterMap _ outs (nodup_of_map _ outs hond) ?_, fun w => ⟨?_, ?_⟩⟩
  · intro a ha b hb x hxa hxb
    obtain ⟨k, hk, hak, hxk⟩ := hfind a x hxa
    obtain ⟨k', hk', hbk, hxk'⟩ := hfind b x hxb
    have : k = k' := hh k hk k' hk' (hxk ▸ hxk')
    subst this
    exact port_of_name outs hond a ha b hb (hak.trans hbk.symm)
  · intro hm
    obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp hm
    obtain ⟨k, hk, _, rfl⟩ := hfind p w hp
    exact List.mem_map.mpr ⟨k, hk, rfl⟩
  · intro hm
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hm
    obtain ⟨p, hp, hpn⟩ := hfo k hk
    refine List.mem_filterMap.mpr ⟨p, hp, ?_⟩
    unfold outWireOf
    cases hk' : g.find? (fun k => p.name == f k) with
    | none =>
      have := List.find?_eq_none.mp hk' k hk
      simp [hpn] at this
    | some k' =>
      have h1 : p.name = f k' := by simpa using List.find?_some hk'
      have : k' = k := hf k' (List.mem_of_find?_eq_some hk') k hk (h1.symm.trans hpn)
      rw [this]
      rfl

/-! ## Lists of statements by index -/

theorem nodup_flatMap_index {α β γ : Type} (f : α → List β) (h : γ → List β) :
    ∀ (l : List α) (l' : List γ), l.length = l'.length → (l'.flatMap h).Nodup →
      (∀ (i : Nat) (a : α) (b : γ), l[i]? = some a → l'[i]? = some b →
        (f a).Nodup ∧ ∀ x ∈ f a, x ∈ h b) →
      (l.flatMap f).Nodup ∧ ∀ x ∈ l.flatMap f, x ∈ l'.flatMap h
  | [], [], _, _, _ => ⟨List.nodup_nil, fun x hx => by simp at hx⟩
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl
  | a :: l, b :: l', hl, hnd, hall => by
    rw [List.flatMap_cons] at hnd
    obtain ⟨_, hnd2, hdisj⟩ := List.nodup_append.mp hnd
    obtain ⟨ih1, ih2⟩ := nodup_flatMap_index f h l l' (by simpa using hl) hnd2
      (fun i a' b' ha hb => hall (i + 1) a' b' (by simpa using ha) (by simpa using hb))
    obtain ⟨h1, h2⟩ := hall 0 a b rfl rfl
    refine ⟨?_, ?_⟩
    · rw [List.flatMap_cons]
      refine List.nodup_append.mpr ⟨h1, ih1, fun x hx y hy e => ?_⟩
      exact hdisj x (h2 x hx) y (ih2 y hy) e
    · intro x hx
      rw [List.flatMap_cons] at hx ⊢
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (h2 x hx)
      · exact List.mem_append_right _ (ih2 x hx)

/-- **Instance names of statements named by their index are distinct.** -/
theorem instNames_nodup : ∀ (l : List Stmt) (off : Nat),
    (∀ (i : Nat) (st : Stmt), l[i]? = some st →
      ∃ (mn nm : String) (conns : List (String × Expr)),
        st = Stmt.inst mn s!"inst{off + i}_{nm}" conns) →
    (l.filterMap instNameOf).Nodup ∧
    ∀ x ∈ l.filterMap instNameOf, ∃ (i : Nat) (nm : String), off ≤ i ∧ x = s!"inst{i}_{nm}"
  | [], _, _ => ⟨List.nodup_nil, fun x hx => by simp at hx⟩
  | st :: l, off, hall => by
    obtain ⟨mn, nm, conns, rfl⟩ := hall 0 st rfl
    obtain ⟨ih1, ih2⟩ := instNames_nodup l (off + 1) (fun i st hi => by
      obtain ⟨mn', nm', conns', e⟩ := hall (i + 1) st (by simpa using hi)
      exact ⟨mn', nm', conns', by rw [e, show off + (i + 1) = off + 1 + i by omega]⟩)
    have hfm : (Stmt.inst mn s!"inst{off + 0}_{nm}" conns :: l).filterMap instNameOf =
        s!"inst{off + 0}_{nm}" :: l.filterMap instNameOf := rfl
    rw [hfm]
    refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, ih1⟩, fun x hx => ?_⟩
    · obtain ⟨i, nm', hi, he⟩ := ih2 _ hm
      have := instName_inj he
      omega
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨off + 0, nm, by omega, rfl⟩
      · obtain ⟨i, nm', hi, he⟩ := ih2 x hx
        exact ⟨i, nm', by omega, he⟩

/-- `noSelfFeed`, from a fact about each instance's input connections. -/
theorem noSelfFeed_of {find : String → Option Module} {body : List Stmt}
    (h : ∀ mn i conns c, Stmt.inst mn i conns ∈ body → find mn = some c →
      ∀ cn ∈ conns, cn.1 ∉ c.outputs.map (·.name) → ∀ w, cn.2 = Expr.ref w →
        w ∉ instOuts c.outputs conns) :
    noSelfFeed find body = true := by
  unfold noSelfFeed
  rw [List.all_eq_true]
  intro st hs
  cases st with
  | inst mn i conns =>
    simp only []
    cases hc : find mn with
    | none => rfl
    | some c =>
      simp only []
      rw [List.all_eq_true]
      intro cn hcn
      obtain ⟨hm, hf⟩ := List.mem_filter.mp hcn
      have hno : cn.1 ∉ c.outputs.map (·.name) := by simpa using hf
      cases he : cn.2 with
      | ref w =>
        have := h mn i conns c hs hc cn hm hno w he
        rw [instOutWires_eq]
        simpa using this
      | _ => rfl
  | _ => rfl

end Tools.ShippingConnsG
