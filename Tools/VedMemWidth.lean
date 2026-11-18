import Tools.VedMemOrder

/-!
# A kernel-cheap `WidthStmt` (`sparkle-ved-memory-rest`, unit ved-memr5)

`Tools.VedU1Contract.WidthStmt c m` is decided at the entry by `decide +kernel`; its first and last conjuncts are
`(m.wires.map (·.name)).Nodup` and `∀ r ∈ regsOf m.body, ∃ p ∈ m.wires, p.name = r.1 ∧ scalar p.ty = true`, which on
a module with ~2400 wires are String-quadratic in the kernel (measured in the ved-memr5 report: the wire-name
`Nodup` alone is 29 s / 12 GB at N = 300 and is killed at N = 1000).

`WidthOk' c m` has the same meaning and uses the Nat name codes (`ncode`) and the search tree of
`Tools/VedMemOrder.lean`: the wires are entered ONCE in a table (code, width, scalar flag), every entry is looked up
again (`chkE`: the codes are then pairwise distinct, i.e. the wire names are `Nodup`), and the data-input widths and the
registers' wires are lookups.  `WidthStmt_of_ok : WidthOk' c m = true → WidthStmt c m`.  No axiom, no `native_decide`.
-/

namespace Tools.VedMemWidth

open Sparkle.IR.AST Sparkle.IR.Type Tools.VedU1Contract Tools.VedMemOrder

/-- `declWidth`'s reading of a wire type -/
def dw : HWType → Nat
  | .bitVector k => k
  | .bit => 1
  | _ => 0

def scN (t : HWType) : Nat := if scalar t then 1 else 0

/-- (code, declared width, scalar flag) of every wire, numbered -/
def rawW (m : Module) : List (Nat × Nat × Nat) := m.wires.map (fun p => (ncode p.name, dw p.ty, scN p.ty))

def wentsOf (m : Module) : List Ent := numberE 0 (rawW m)

/-- the table entry of a name (its code is checked) -/
def wLook (T : NT Ent) (n : String) : Option Ent :=
  match T.find (skey (ncode n)) with
  | none => none
  | some e => if Nat.beq e.code (ncode n) then some e else none

/-- the wire table is consistent: every wire is looked up again at its own place (so the wire names are distinct) -/
def WidthTab (m : Module) : Bool := chkE (NT.build Ent.key (wentsOf m)) 0 (wentsOf m)

/-- the rest of `WidthStmt`, by lookups -/
def WidthRest (c : Contract) (m : Module) : Bool :=
  c.dataInputs.all (fun p => scalar p.ty && (match wLook (NT.build Ent.key (wentsOf m)) p.name with
    | none => false
    | some e => Nat.beq e.kind p.ty.bitWidth)) &&
  c.outputs.all (fun p => scalar p.ty) &&
  (regsOf m.body).all (fun r => match wLook (NT.build Ent.key (wentsOf m)) r.1 with
    | none => false
    | some e => Nat.beq e.sidx 1)

def WidthOk' (c : Contract) (m : Module) : Bool := WidthTab m && WidthRest c m

/-! ## Soundness -/

theorem wLook_mem (m : Module) (n : String) (e : Ent) (h : wLook (NT.build Ent.key (wentsOf m)) n = some e) :
    ∃ p ∈ m.wires, p.name = n ∧ dw p.ty = e.kind ∧ scN p.ty = e.sidx := by
  unfold wLook at h
  cases hf : (NT.build Ent.key (wentsOf m)).find (skey (ncode n)) with
  | none => rw [hf] at h; simp at h
  | some e' =>
    rw [hf] at h
    simp only at h
    split at h
    · rename_i hb
      have he : e' = e := Option.some.inj h
      subst he
      have hc : e'.code = ncode n := Nat.eq_of_beq_eq_true hb
      have hmem := NT.vals_build _ _ _ (NT.find_mem _ _ _ hf)
      have h3 := numberE_mem_to (rawW m) 0 e' hmem
      simp only [rawW, List.mem_map] at h3
      obtain ⟨p, hp, hp2⟩ := h3
      simp only [Prod.mk.injEq] at hp2
      obtain ⟨a1, a2, a3⟩ := hp2
      exact ⟨p, hp, ncode_inj (a1.trans hc), a2, a3⟩
    · simp at h

theorem WidthTab_nodup (m : Module) (h : WidthTab m = true) : (m.wires.map (·.name)).Nodup := by
  have hn := (chkE_sound _ _ _ h).2.2
  unfold wentsOf at hn
  rw [numberE_code] at hn
  simp only [rawW, List.map_map] at hn
  exact nodup_of_map' ncode _ (by rw [List.map_map]; exact hn)

theorem find_wire (n : String) : ∀ (l : List Port), (l.map (·.name)).Nodup → ∀ p ∈ l, p.name = n →
    l.find? (fun q => q.name == n) = some p := by
  intro l
  induction l with
  | nil => intro _ p hp; simp at hp
  | cons q rest ih =>
    intro hnd p hp hpn
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [hpn]
    · by_cases hq : q.name = n
      · exact (hnd.1 (by rw [hq, ← hpn]; exact List.mem_map_of_mem hp)).elim
      · have : (q.name == n) = false := by simpa using hq
        rw [this]
        exact ih hnd.2 p hp hpn

theorem declWidth_eq (m : Module) (hnd : (m.wires.map (·.name)).Nodup) (p : Port) (hp : p ∈ m.wires) (n : String)
    (hn : p.name = n) : declWidth m n = dw p.ty := by
  unfold declWidth
  rw [find_wire n m.wires hnd p hp hn]
  rcases p with ⟨_, ty⟩
  cases ty <;> rfl

theorem WidthStmt_of_ok (c : Contract) (m : Module) (h : WidthOk' c m = true) : WidthStmt c m := by
  simp only [WidthOk', WidthRest, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hT, ⟨hin, hout⟩, hreg⟩ := h
  have hnd := WidthTab_nodup m hT
  refine ⟨hnd, ?_, ?_, ?_⟩
  · intro p hp
    have h1 := hin p hp
    obtain ⟨hs, h2⟩ := h1
    refine ⟨hs, ?_⟩
    cases hl : wLook (NT.build Ent.key (wentsOf m)) p.name with
    | none => rw [hl] at h2; simp at h2
    | some e =>
      rw [hl] at h2
      have hk : e.kind = p.ty.bitWidth := Nat.eq_of_beq_eq_true h2
      obtain ⟨q, hq, hqn, hqw, _⟩ := wLook_mem m _ e hl
      rw [declWidth_eq m hnd q hq p.name hqn, hqw, hk]
  · intro p hp
    exact hout p hp
  · intro r hr
    have h1 := hreg r hr
    cases hl : wLook (NT.build Ent.key (wentsOf m)) r.1 with
    | none => rw [hl] at h1; simp at h1
    | some e =>
      rw [hl] at h1
      have hk : e.sidx = 1 := Nat.eq_of_beq_eq_true h1
      obtain ⟨q, hq, hqn, _, hqs⟩ := wLook_mem m _ e hl
      refine ⟨q, hq, hqn, ?_⟩
      rw [hk] at hqs
      unfold scN at hqs
      split at hqs
      · assumption
      · simp at hqs

/-- the two parts, for the entry to check them in separate kernel runs -/
theorem WidthStmt_of_parts (c : Contract) (m : Module) (h1 : WidthTab m = true) (h2 : WidthRest c m = true) :
    WidthStmt c m :=
  WidthStmt_of_ok c m (by simp [WidthOk', h1, h2])

end Tools.VedMemWidth
