import Tools.ShippingCallsStmts
import Tools.ShippingInstStmtG
import Tools.ShippingCallGroups

/-! # The instance statements of a real parent (several outputs, sequential children)

`stmtsG` succeeds — one statement per CALL GROUP (the entries of one child
with the same argument `let`s), the group's instance with the child's
non-clock inputs on the argument wires, `clk` / `rst` for a sequential child
and each entry's field on the entry's wire — from facts about the parent's
ports (the tail ports `ls`), the children (each resolved by name to itself;
as many non-clock inputs as arguments, distinct; the entry's field an output
port and no input), the entries (two entries of one call read different
fields), and the closed module (the wires declared, a clock for a sequential
child, the instance names fresh). Pure. -/
namespace Tools.ShippingCallsStmtsG
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Tools.ShippingCallsParent Tools.ShippingCallsStmts Tools.ShippingInstStmtG
open Tools.ShippingCallGroups

/-- The key of every entry: its child's module name and its argument `let`s. -/
def keysOf (insts : List (List Nat)) (children : List (Module × Design)) :
    List (String × List Nat) :=
  (List.range insts.length).map fun k =>
    (((children[k]?).map (·.1.name)).getD "", (insts[k]?).getD [])

/-- The wire of entry `k`: its tail port. -/
def outWOf (ls : List Port) (k : Nat) : String := ((ls[k]?).map (·.name)).getD ""

theorem keys_some {insts : List (List Nat)} {children : List (Module × Design)}
    (hlen : children.length = insts.length) :
    ((List.range insts.length).mapM fun k => do
      let args ← insts[k]?
      let child ← children[k]?
      pure (child.1.name, args)) = some (keysOf insts children) := by
  refine mapM_some_of _ _ _ (fun k hk => ?_)
  have hk' := List.mem_range.mp hk
  rw [List.getElem?_eq_getElem hk', List.getElem?_eq_getElem (hlen ▸ hk')]
  rfl

theorem keys_get {insts : List (List Nat)} {children : List (Module × Design)}
    (hlen : children.length = insts.length) {k : Nat} {key : String × List Nat}
    (h : (keysOf insts children)[k]? = some key) :
    ∃ args c, insts[k]? = some args ∧ children[k]? = some c ∧ key = (c.1.name, args) := by
  unfold keysOf at h
  have hk : k < insts.length := by
    have := (List.getElem?_eq_some_iff.mp h).1
    simpa using this
  rw [List.getElem?_map, List.getElem?_range hk] at h
  refine ⟨insts[k], children[k]'(hlen ▸ hk), List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem (hlen ▸ hk), ?_⟩
  simp only [Option.map_some, Option.some.injEq] at h
  rw [← h, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (hlen ▸ hk)]
  rfl

theorem nodup_map_on {α β : Type} (f : α → β) : ∀ (l : List α), l.Nodup →
    (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hnd, hinj => by
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨?_, nodup_map_on f l h2
      (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    intro hm
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    exact h1 (hinj a (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb) he.symm ▸ hb)

theorem nodup_of_flatten {α : Type} : ∀ (gs : List (List α)), gs.flatten.Nodup →
    ∀ g ∈ gs, g.Nodup
  | [], _, g, hg => by simp at hg
  | g0 :: gs, h, g, hg => by
    rw [List.flatten_cons] at h
    obtain ⟨h1, h2, -⟩ := List.nodup_append.mp h
    rcases List.mem_cons.mp hg with rfl | hg
    · exact h1
    · exact nodup_of_flatten gs h2 g hg

/-- Statement `st` is the instance of call group `gi`. -/
def IsCallG (ls : List Port) (kI n : Nat) (insts : List (List Nat)) (fields : List String)
    (children : List (Module × Design)) (gi : Nat) (st : Stmt) : Prop :=
  ∃ (g : List Nat) (k0 : Nat) (args : List Nat) (c : Module × Design),
    (callGroups (keysOf insts children))[gi]? = some g ∧ g.head? = some k0 ∧
    insts[k0]? = some args ∧ children[k0]? = some c ∧
    (∀ k ∈ g, k < kI ∧ insts[k]? = some args ∧ ∃ c', children[k]? = some c' ∧ c'.1 = c.1) ∧
    st = .inst c.1.name s!"inst{gi}_{c.1.name}"
      (callConnsG (inPortsOf c.1) (argWsOf ls kI n args) (isSeqChild c.1)
        (g.map fun k => fields.getD k "") (g.map (outWOf ls)))

set_option maxHeartbeats 1000000 in
/-- **The instance statements of the call groups.** -/
theorem stmtsG_some {PI ls : List Port} {kI n K : Nat} {insts : List (List Nat)}
    {fields : List String} {children : List (Module × Design)} {m : Module} {d' : Design}
    (hkI : insts.length = kI) (hchL : children.length = kI)
    (hlsLen : ls.length = kI + n + K)
    (hlsNd : (ls.map (·.name)).Nodup)
    (hargsK : ∀ (k : Nat) (args : List Nat), insts[k]? = some args → ∀ a ∈ args, a < K)
    (hchild : ∀ (k : Nat) (c : Module × Design), children[k]? = some c →
      moduleByName d'.modules c.1.name = some c.1 ∧
      (∀ args : List Nat, insts[k]? = some args → (inPortsOf c.1).length = args.length) ∧
      ((inPortsOf c.1).map (·.name)).Nodup ∧
      (∃ p ∈ c.1.outputs, p.name = fields.getD k "") ∧
      (∀ p ∈ inPortsOf c.1, p.name ≠ fields.getD k "") ∧
      fields.getD k "" ≠ "clk" ∧ fields.getD k "" ≠ "rst")
    (hcons : ∀ a ∈ children, ∀ b ∈ children, a.1.name = b.1.name → a.1 = b.1)
    (hfieldsNd : ∀ (k k' : Nat) (key : String × List Nat),
      (keysOf insts children)[k]? = some key → (keysOf insts children)[k']? = some key →
      fields.getD k "" = fields.getD k' "" → k = k')
    (hwire : ∀ p ∈ ls, ∃ q ∈ m.wires, q.name = p.name)
    (hclk : ∀ c ∈ children, isSeqChild c.1 = true →
      (∃ p ∈ m.inputs, p.name = "clk") ∧ ∃ p ∈ m.inputs, p.name = "rst")
    (hfresh : ∀ (gi : Nat) (c : Module × Design), c ∈ children →
      s!"inst{gi}_{c.1.name}" ∉
      m.inputs.map (·.name) ++ m.outputs.map (·.name) ++ m.wires.map (·.name)) :
    ∃ stmts, stmtsG PI.length kI n ((PI ++ ls).map (·.name)) insts fields children m d' =
        some stmts ∧
      stmts.length = (callGroups (keysOf insts children)).length ∧
      (∀ gi st, stmts[gi]? = some st → IsCallG ls kI n insts fields children gi st) ∧
      (List.range insts.length).mapM (fun k => ((PI ++ ls).map (·.name))[PI.length + k]?) =
        some ((List.range insts.length).map (outWOf ls)) := by
  have hchL' : children.length = insts.length := hchL.trans hkI.symm
  have hport : ∀ i, ((PI ++ ls).map (·.name))[PI.length + i]? = (ls[i]?).map (·.name) := by
    intro i
    rw [List.getElem?_map, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
  have hG := callGroups_spec (keysOf insts children)
  have hklen : (keysOf insts children).length = kI := by simp [keysOf, hkI]
  have hflatNd : (callGroups (keysOf insts children)).flatten.Nodup :=
    hG.perm.nodup_iff.mpr List.nodup_range
  have hstep : ∀ x ∈ (callGroups (keysOf insts children)).zipIdx, ∃ st,
      (do
        let k0 ← x.1.head?
        let args ← insts[k0]?
        let child ← children[k0]?
        let mc ← moduleByName d'.modules child.1.name
        instStmtG PI.length kI n ((PI ++ ls).map (·.name)) x.2 args
          (x.1.map fun k => (k, fields.getD k "")) mc m) = some st ∧
      IsCallG ls kI n insts fields children x.2 st := by
    rintro ⟨g, gi⟩ hx
    have hgi : (callGroups (keysOf insts children))[gi]? = some g := by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      rw [List.getElem?_zipIdx] at hi
      cases hg : (callGroups (keysOf insts children))[i]? with
      | none => rw [hg] at hi; cases hi
      | some g' =>
        rw [hg] at hi
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        simpa using hg
    have hgm := List.mem_of_getElem? hgi
    obtain ⟨k0, key, h0, hall⟩ := hG.head g hgm
    have hk0 : k0 ∈ g := List.mem_of_mem_head? h0
    obtain ⟨args, c, hargs, hc, rfl⟩ := keys_get hchL' (hall k0 hk0).2
    have hmem : ∀ k ∈ g, k < kI ∧ insts[k]? = some args ∧
        ∃ c', children[k]? = some c' ∧ c'.1 = c.1 := by
      intro k hk
      obtain ⟨hlt, hkey⟩ := hall k hk
      obtain ⟨args', c', ha', hc', he⟩ := keys_get hchL' hkey
      simp only [Prod.mk.injEq] at he
      refine ⟨hklen ▸ hlt, by rw [ha', he.2], c', hc', ?_⟩
      exact hcons c' (List.mem_of_getElem? hc') c (List.mem_of_getElem? hc) he.1.symm
    have hgNd : g.Nodup := nodup_of_flatten _ hflatNd g hgm
    obtain ⟨hres, hfit, hinNd, _, _, _, _⟩ := hchild k0 c hc
    have hargWs : args.mapM (fun j => ((PI ++ ls).map (·.name))[PI.length + kI + n + j]?) =
        some (argWsOf ls kI n args) := by
      refine mapM_some_of _ _ args (fun a ha => ?_)
      have hlt : kI + n + a < ls.length := by
        have := hargsK k0 args hargs a ha
        omega
      rw [show PI.length + kI + n + a = PI.length + (kI + n + a) by omega, hport,
        List.getElem?_eq_getElem hlt]
      rfl
    have houts : (g.map fun k => (k, fields.getD k "")).mapM
        (fun (x : Nat × String) => ((PI ++ ls).map (·.name))[PI.length + x.1]?) =
        some (g.map (outWOf ls)) := by
      have := mapM_some_of (fun (x : Nat × String) => ((PI ++ ls).map (·.name))[PI.length + x.1]?)
        (fun x => outWOf ls x.1) (g.map fun k => (k, fields.getD k "")) (by
          intro x hx
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
          have hlt : k < ls.length := by
            have := (hmem k hk).1
            omega
          show ((PI ++ ls).map (·.name))[PI.length + k]? = _
          rw [hport, List.getElem?_eq_getElem hlt]
          simp [outWOf, List.getElem?_eq_getElem hlt])
      rw [this, List.map_map]
      rfl
    have hfmap : (g.map fun k => (k, fields.getD k "")).map (·.2) =
        g.map fun k => fields.getD k "" := by
      rw [List.map_map]
      rfl
    have hinst := instStmtG_some (nIn := PI.length) (kI := kI) (n := n) (gi := gi)
      (portNames := (PI ++ ls).map (·.name)) (args := args)
      (outs := g.map fun k => (k, fields.getD k "")) (mc := c.1) (m := m)
      (outWs := g.map (outWOf ls)) (argWs := argWsOf ls kI n args)
      houts hargWs (by rw [hfit args hargs]; simp [argWsOf]) hinNd
      (by
        rw [hfmap]
        intro f hf
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hf
        obtain ⟨_, _, c', hc', hcc⟩ := hmem k hk
        obtain ⟨_, _, _, ho, _⟩ := hchild k c' hc'
        rw [hcc] at ho
        exact ho)
      (by
        rw [hfmap]
        refine nodup_map_on _ g hgNd (fun a ha b hb he => ?_)
        exact hfieldsNd a b _ (hall a ha).2 (hall b hb).2 he)
      (by
        rw [hfmap]
        intro f hf
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hf
        obtain ⟨_, _, c', hc', hcc⟩ := hmem k hk
        obtain ⟨_, _, _, _, hi, h1, h2⟩ := hchild k c' hc'
        rw [hcc] at hi
        exact ⟨hi, h1, h2⟩)
      (by
        intro w hw hmemA
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
        obtain ⟨a, ha, he⟩ := List.mem_map.mp hmemA
        have hlt : kI + n + a < ls.length := by
          have := hargsK k0 args hargs a ha
          omega
        have hkl : k < ls.length := by
          have := (hmem k hk).1
          omega
        simp only [outWOf, List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hkl,
          Option.map_some, Option.getD_some] at he
        have := Tools.ShippingMachineCloses.nodup_index hlsNd (List.getElem?_eq_getElem hlt)
          (List.getElem?_eq_getElem hkl) he
        have := (hmem k hk).1
        omega)
      (by
        refine nodup_map_on _ g hgNd (fun a ha b hb he => ?_)
        have hal : a < ls.length := by
          have := (hmem a ha).1
          omega
        have hbl : b < ls.length := by
          have := (hmem b hb).1
          omega
        simp only [outWOf, List.getElem?_eq_getElem hal, List.getElem?_eq_getElem hbl,
          Option.map_some, Option.getD_some] at he
        exact Tools.ShippingMachineCloses.nodup_index hlsNd (List.getElem?_eq_getElem hal)
          (List.getElem?_eq_getElem hbl) he)
      (by
        intro w hw
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hw
        have hkl : k < ls.length := by
          have := (hmem k hk).1
          omega
        obtain ⟨q, hq, hn⟩ := hwire ls[k] (List.getElem_mem hkl)
        exact ⟨q, hq, by simp [outWOf, List.getElem?_eq_getElem hkl, hn]⟩)
      (hclk c (List.mem_of_getElem? hc))
      (hfresh gi c (List.mem_of_getElem? hc))
    rw [hfmap] at hinst
    refine ⟨_, ?_, g, k0, args, c, hgi, h0, hargs, hc, hmem, rfl⟩
    simp only [h0, hargs, hc, hres, bind, Option.bind]
    exact hinst
  obtain ⟨stmts, hst, hlen, hall⟩ := mapM_exists _
    (fun (x : List Nat × Nat) st => IsCallG ls kI n insts fields children x.2 st)
    (callGroups (keysOf insts children)).zipIdx hstep
  refine ⟨stmts, ?_, by rw [hlen, List.length_zipIdx], ?_, ?_⟩
  · unfold stmtsG
    have hk := keys_some hchL'
    simp only [Option.bind_eq_bind] at hk ⊢
    rw [hk]
    exact hst
  · intro gi st hk
    have hgl : gi < (callGroups (keysOf insts children)).length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      rw [hlen, List.length_zipIdx] at this
      exact this
    exact hall gi ((callGroups (keysOf insts children))[gi], gi) st
      (by rw [List.getElem?_zipIdx, List.getElem?_eq_getElem hgl]; simp) hk
  · refine mapM_some_of _ _ _ (fun k hk => ?_)
    have hk' : k < ls.length := by
      have := List.mem_range.mp hk
      omega
    rw [hport, List.getElem?_eq_getElem hk']
    simp [outWOf, List.getElem?_eq_getElem hk']

end Tools.ShippingCallsStmtsG
