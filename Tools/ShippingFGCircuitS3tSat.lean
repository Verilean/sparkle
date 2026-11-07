import Tools.ShippingFGCircuitS3tSpec
set_option autoImplicit false
-- FG circuit pilot S3t, step 1 (example): the four seed premises of `RootShowsAt` — `(a)` the input ports, by the claimed names, carry the source's inputs, `(b)` a register reads the state, `(c)` reset is 0, `(d)` the initial value of register k is its slot's init — are SIMULTANEOUSLY SATISFIABLE, for every per-cycle source values, run length, and every register list `regs` that is distinct and lies in the claimed names' register range.  A statement about the premises, not about any IR.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §69.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3tSat
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingFGCircuitS3tSpec


/-- the value an association list gives a name, or the default -/
def lk (P : List (String × Nat)) (n : String) (d : Nat) : Nat :=
  match P.find? (fun p => p.1 == n) with
  | some p => p.2
  | none => d

theorem lk_mem : ∀ (P : List (String × Nat)), (P.map Prod.fst).Nodup → ∀ p ∈ P, ∀ d, lk P p.1 d = p.2
  | [], _, p, hp, _ => by simp at hp
  | q :: rest, hnd, p, hp, d => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [lk]
    · have hne : q.1 ≠ p.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hp)
      have := lk_mem rest hnd.2 p hp d
      simp only [lk, List.find?_cons] at this ⊢
      have hb : (q.1 == p.1) = false := by simpa using hne
      simp [hb, this]

theorem lk_not_mem : ∀ (P : List (String × Nat)) (n : String), n ∉ P.map Prod.fst → ∀ d, lk P n d = d
  | [], n, _, d => by simp [lk]
  | q :: rest, n, h, d => by
    rw [List.map_cons, List.mem_cons, not_or] at h
    have := lk_not_mem rest n h.2 d
    simp only [lk, List.find?_cons] at this ⊢
    have hb : (q.1 == n) = false := by simpa using (Ne.symm h.1)
    simp [hb, this]


theorem idxOf_getElem_nodup : ∀ (l : List String), l.Nodup → ∀ (k : Nat) (hk : k < l.length), l.idxOf l[k] = k
  | [], _, k, hk => by simp at hk
  | a :: rest, hnd, 0, _ => by simp
  | a :: rest, hnd, k + 1, hk => by
    rw [List.nodup_cons] at hnd
    have hk' : k < rest.length := by simpa using hk
    have ih := idxOf_getElem_nodup rest hnd.2 k hk'
    have hne : a ≠ rest[k] := fun h => hnd.1 (h ▸ List.getElem_mem hk')
    have hb : (a == rest[k]) = false := by simpa using hne
    simp [List.idxOf_cons, hb, ih]


/-- the initial state: register `k` holds the `k`-th initial value -/
theorem st0_exists (regs : List String) (hrn : regs.Nodup) (inits : List Nat) :
    ∃ st0 : String → Nat, ∀ (k : Nat) (r : String) (n : Nat), regs[k]? = some r → inits[k]? = some n → st0 r = n := by
  refine ⟨fun r => (inits[regs.idxOf r]?).getD 0, ?_⟩
  intro k r n hr hn
  have hk : k < regs.length := (List.getElem?_eq_some_iff.mp hr).1
  have hr' : regs[k] = r := (List.getElem?_eq_some_iff.mp hr).2
  have : regs.idxOf r = k := by
    rw [← hr']
    exact idxOf_getElem_nodup regs hrn k hk
  simp [this, hn]

/-- the facts `SourceData.ok` gives about the claimed names -/
theorem ok_names {S : SourceData} (h : S.ok = true) :
    S.portNames.Nodup ∧ "rst" ∉ S.portNames ∧ S.kD ≤ S.portNames.length := by
  unfold SourceData.ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hnd⟩, hrst⟩, hkD⟩, -⟩, -⟩, -⟩ := h
  refine ⟨hnd, ?_, by simpa using hkD⟩
  intro hm
  have : S.portNames.contains "rst" = true := List.contains_iff_mem.mpr hm
  rw [this] at hrst
  cases hrst

/-- the value premise (a) gives an input port FITS the width the port is declared with (`kindTy`/`kindW`): `posEnc` of a `bits n` binder is `< 2^n`, of a `bool` binder is `< 2`, so the seed premise is consistent with the declared width of `srcInPorts` -/
theorem posEnc_fits (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (pos : Nat)
    (k : Sparkle.Compiler.Elab.MixedGateBinder) (hk : k ≠ .domain) :
    Tools.ShippingMachineEntry.posEnc bools bits pos k < 2 ^ kindW k := by
  cases k with
  | domain => exact absurd rfl hk
  | bits n => exact (bits pos n).isLt
  | bool => cases h : bools pos <;> simp [Tools.ShippingMachineEntry.posEnc, ShippingMuxLoweringSoundness.encodeBool, kindW, h]

/-- **the seed premises are simultaneously satisfiable.**  For every data accepted by `SourceData.ok`, every distinct `regs` in the claimed names' register range (after the root's own inputs), and every per-cycle source value `val t q` of the root's input `q`: there are `seed` and `st0` with `(a)` the claimed input port of input `q` carries `val t q` at every cycle and state, `(b)` a register reads the state, `(c)` reset is 0, `(d)` register `k`'s initial value is slot `k`'s init. -/
theorem premises_satisfiable (S : SourceData) (hok : S.ok = true) (regs : List String) (hrn : regs.Nodup)
    (hreg : ∀ r ∈ regs, r ∈ S.portNames.drop (S.portNames.length - S.d.shape.layout.lets - S.d.shape.layout.slots.length))
    (hpos : S.kD ≤ S.portNames.length - S.d.shape.layout.lets - S.d.shape.layout.slots.length)
    (val : Nat → Nat → Nat) :
    ∃ (seed : Nat → (String → Nat) → Env) (st0 : String → Nat),
      (∀ (t : Nat) (st : String → Nat) (q : Nat) (nm : String), q < S.kD → S.portNames[q]? = some nm →
        seed t st nm = val t q) ∧
      (∀ (t : Nat) (st : String → Nat) (r : String), r ∈ regs → seed t st r = st r) ∧
      (∀ (t : Nat) (st : String → Nat), seed t st "rst" = 0) ∧
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → S.d.shape.layout.slots[k]? = some f →
        st0 r = f.init) := by
  obtain ⟨hnd, hrst, hkD⟩ := ok_names hok
  have hsplit : S.portNames = S.portNames.take S.kD ++ S.portNames.drop S.kD := (List.take_append_drop _ _).symm
  have hdisj := (List.nodup_append.mp (hsplit ▸ hnd)).2.2
  have hnd5 : (S.portNames.take S.kD).Nodup := (List.nodup_append.mp (hsplit ▸ hnd)).1
  have hlen5 : (S.portNames.take S.kD).length = S.kD := by simp; omega
  have hfst : ∀ t, ((S.portNames.take S.kD).zip ((List.range S.kD).map (val t))).map Prod.fst = S.portNames.take S.kD := by
    intro t
    apply List.map_fst_zip
    simp [hlen5]
  obtain ⟨st0, hst0⟩ := st0_exists regs hrn (S.d.shape.layout.slots.map (·.init))
  refine ⟨fun t st n => if n = "rst" then 0 else
      lk ((S.portNames.take S.kD).zip ((List.range S.kD).map (val t))) n (st n), st0, ?_, ?_, ?_, ?_⟩
  · intro t st q nm hq hnm
    have hne : nm ≠ "rst" := fun h => hrst (h ▸ List.mem_of_getElem? hnm)
    have hmem : (nm, val t q) ∈ (S.portNames.take S.kD).zip ((List.range S.kD).map (val t)) := by
      apply List.mem_of_getElem? (i := q)
      rw [List.getElem?_zip_eq_some]
      refine ⟨?_, ?_⟩
      · rw [List.getElem?_take, if_pos hq]; exact hnm
      · rw [List.getElem?_map, List.getElem?_range hq]; rfl
    simp only [hne, if_false]
    exact lk_mem _ (by rw [hfst t]; exact hnd5) _ hmem _
  · intro t st r hr
    have hr' : r ∈ S.portNames.drop S.kD := by
      have h := hreg r hr
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hpos
      rw [hj, ← List.drop_drop] at h
      exact List.mem_of_mem_drop h
    have hrne : r ≠ "rst" := fun h => hrst (h ▸ List.mem_of_mem_drop hr')
    have hr5 : r ∉ S.portNames.take S.kD := fun h => hdisj r h r hr' rfl
    simp only [hrne, if_false]
    exact lk_not_mem _ _ (by rw [hfst t]; exact hr5) _
  · intro t st; simp
  · intro k r f hr hf
    exact hst0 k r f.init hr (by simp [List.getElem?_map, hf])

/-- **simultaneous satisfaction for the concrete root**: for every distinct `regs` in the claimed names' register range and every per-cycle input values, the four seed premises of `RootShowsAt` hold together for some `seed`, `st0` -/
theorem rootS_premises (regs : List String) (hrn : regs.Nodup)
    (hreg : ∀ r ∈ regs, r ∈ rootS.portNames.drop (rootS.portNames.length - rootS.d.shape.layout.lets - rootS.d.shape.layout.slots.length))
    (val : Nat → Nat → Nat) :
    ∃ (seed : Nat → (String → Nat) → Env) (st0 : String → Nat),
      (∀ (t : Nat) (st : String → Nat) (q : Nat) (nm : String), q < rootS.kD → rootS.portNames[q]? = some nm →
        seed t st nm = val t q) ∧
      (∀ (t : Nat) (st : String → Nat) (r : String), r ∈ regs → seed t st r = st r) ∧
      (∀ (t : Nat) (st : String → Nat), seed t st "rst" = 0) ∧
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r → rootS.d.shape.layout.slots[k]? = some f →
        st0 r = f.init) :=
  premises_satisfiable rootS rootS_ok regs hrn hreg (by decide +kernel) val

end Tools.ShippingFGCircuitS3tSat
