import Tools.ShippingMachineCommand
import Tools.ShippingReaderInputs
set_option autoImplicit false
-- NOT BUILT by an issue-linked clean build (DG-DATAOF pure units U-D, U-E; scripts/gen5/DG_DATAOF_FREEZE.md rev2). No sorry / axiom / native_decide.

/-! # DG-DATAOF pure units, second file (no READKINDS, no `Laws`, no `T1Hyp*`)

* U-D: the position lists `readMachine` builds (`ShippingMachineCommand.lean:512-514`) are `posB 0 / posV 0 / widV`.
* U-E: inversions of `splitLets` / `splitFields` / `unField`, and what they do NOT say.
  `unField (.bits n)` IGNORES `n` (`ShippingMachineCommand.lean:267`), so the statement
  "a field that survives the re-pack has the binder's sort" is FALSE for `.bits` binders; the declared width
  comes from rows of `MachineData.ok` (`ok_K_nexts`, `ok_letsTyped`, `ok_outsFit` below), not from the re-pack.
* The `ok` rows that give the sorts / widths, as projections of `MachineData.ok = true`. -/
namespace Tools.ShippingGen5DataOfPure2
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineCommand
open Tools.ShippingMachineEntry Tools.ShippingReaderInputs
open Sparkle.Core Sparkle.IR.Machine Sparkle.Compiler.Elab

/-! ## U-D -/

/-- `readMachine` :512 (the Bool binder positions), counted from `o`. -/
theorem bposL_aux (ks : List MixedGateBinder) : ∀ (o : Nat),
    (((List.range' o ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) =>
      if pk.2 == .bool then some pk.1 else none) = posB o ks := by
  induction ks with
  | nil => intro o; rfl
  | cons k ks ih =>
    intro o
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.filterMap_cons]
    cases k <;> simp_all [posB]

theorem vposL_aux (ks : List MixedGateBinder) : ∀ (o : Nat),
    (((List.range' o ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) =>
      match pk.2 with | .bits _ => some pk.1 | _ => none) = posV o ks := by
  induction ks with
  | nil => intro o; rfl
  | cons k ks ih =>
    intro o
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.filterMap_cons]
    cases k <;> simp [posV, ih]

theorem vwL_aux (ks : List MixedGateBinder) : ∀ (o : Nat),
    (((List.range' o ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) =>
      match pk.2 with | .bits w => some w | _ => none) = widV ks := by
  induction ks with
  | nil => intro o; rfl
  | cons k ks ih =>
    intro o
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.filterMap_cons]
    cases k <;> simp [widV, ih]

theorem bposL_eq (ks : List MixedGateBinder) :
    (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) =>
      if pk.2 == .bool then some pk.1 else none) = posB 0 ks := by
  rw [List.range_eq_range']; exact bposL_aux ks 0

theorem vposL_eq (ks : List MixedGateBinder) :
    (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) =>
      match pk.2 with | .bits _ => some pk.1 | _ => none) = posV 0 ks := by
  rw [List.range_eq_range']; exact vposL_aux ks 0

theorem vwL_eq (ks : List MixedGateBinder) :
    (((List.range ks.length).zip ks).filterMap fun (pk : Nat × MixedGateBinder) =>
      match pk.2 with | .bits w => some w | _ => none) = widV ks := by
  rw [List.range_eq_range']; exact vwL_aux ks 0

/-! ## U-E: `splitLets` / `splitFields` -/

theorem splitLets_some : ∀ {n : Nat} {t : Σ w : Nat, Term (.bits w)} {fs : List (Σ w : Nat, Term (.bits w))}
    {core : Σ w : Nat, Term (.bits w)},
    splitLets n t = some (fs, core) → fs.length = n ∧ t = packLets fs core.2
  | 0, t, fs, core, h => by
    simp only [splitLets, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | n + 1, ⟨w, t⟩, fs, core, h => by
    cases t with
    | concat a rest =>
      simp only [splitLets, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨fs', core', hrec, rfl, rfl⟩ := h
      obtain ⟨hl, ht⟩ := splitLets_some hrec
      refine ⟨by simp [hl], ?_⟩
      show (⟨_, Term.concat a rest⟩ : Σ w : Nat, Term (.bits w)) = ⟨_, Term.concat a (packLets fs' core'.2).2⟩
      have : (⟨_, rest⟩ : Σ w : Nat, Term (.bits w)) = packLets fs' core'.2 := ht
      obtain ⟨hw, hr⟩ := Sigma.mk.inj this
      subst hw
      rw [eq_of_heq hr]
    | _ => simp [splitLets] at h

/-- Auxiliary: `splitFields (n+1)` as a `packList`. -/
theorem splitFields_aux : ∀ {n : Nat} {t : Σ w : Nat, Term (.bits w)} {fs : List (Σ w : Nat, Term (.bits w))},
    splitFields (n + 1) t = some fs →
      fs.length = n + 1 ∧ ∃ (f : Σ w : Nat, Term (.bits w)) (rest : List (Σ w : Nat, Term (.bits w))),
        fs = f :: rest ∧ t = packList f rest
  | 0, t, fs, h => by
    simp only [splitFields, Option.some.injEq] at h
    subst h
    exact ⟨rfl, t, [], rfl, rfl⟩
  | n + 1, ⟨w, t⟩, fs, h => by
    cases t with
    | concat a rest =>
      simp only [splitFields, Option.map_eq_some_iff] at h
      obtain ⟨fs', hrec, rfl⟩ := h
      obtain ⟨hl, g, gs, rfl, ht⟩ := splitFields_aux hrec
      refine ⟨by simp [hl], ⟨_, a⟩, g :: gs, rfl, ?_⟩
      show (⟨_, Term.concat a rest⟩ : Σ w : Nat, Term (.bits w)) = ⟨_, Term.concat a (packList g gs).2⟩
      have : (⟨_, rest⟩ : Σ w : Nat, Term (.bits w)) = packList g gs := ht
      obtain ⟨hw, hr⟩ := Sigma.mk.inj this
      subst hw
      rw [eq_of_heq hr]
    | _ => simp [splitFields] at h

theorem splitFields_some {n : Nat} {t : Σ w : Nat, Term (.bits w)} {fs : List (Σ w : Nat, Term (.bits w))}
    (h : splitFields n t = some fs) : 0 < n ∧ fs.length = n ∧ t = packAll fs := by
  cases n with
  | zero => simp [splitFields] at h
  | succ n =>
    obtain ⟨hl, f, rest, rfl, ht⟩ := splitFields_aux h
    exact ⟨Nat.succ_pos n, hl, ht⟩

/-! ## U-E: `unField`

`unField .bool` keeps only the condition of a `mux` (any width, any branches); `unField (.bits n)` ignores `n`. -/

theorem unField_bool {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s} (h : unField .bool f = some t) :
    ∃ (w : Nat) (c : Term .bool) (a b : Term (.bits w)), f = ⟨w, .mux c a b⟩ ∧ t = ⟨.bool, c⟩ := by
  obtain ⟨w, u⟩ := f
  cases u <;> simp [unField] at h
  case mux c a b =>
    exact ⟨w, c, a, b, rfl, h.symm⟩

theorem unField_bits {n w : Nat} {u : Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField (.bits n) ⟨w, u⟩ = some t) : t = ⟨.bits w, u⟩ := by
  simp only [unField, Option.some.injEq] at h
  exact h.symm

theorem unField_domain {f : Σ w : Nat, Term (.bits w)} : unField .domain f = none := by
  obtain ⟨w, u⟩ := f
  rfl

/-- Sort of a `.bool`-field result. -/
theorem unField_bool_sort {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s} (h : unField .bool f = some t) :
    sortOf .bool = some t.1 := by
  obtain ⟨w, c, a, b, -, rfl⟩ := unField_bool h
  rfl

/-- A `.bits n` binder: the result's sort is `.bits f.1`, whatever `n` is. -/
theorem unField_bits_sort {n : Nat} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField (.bits n) f = some t) : t.1 = .bits f.1 := by
  obtain ⟨w, u⟩ := f
  rw [unField_bits h]

/-- A `.bits` binder's field always survives the re-pack: the re-pack alone says nothing about `n`. -/
theorem unField_bits_toField {n : Nat} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField (.bits n) f = some t) : toField t.1 t.2 = f := by
  obtain ⟨w, u⟩ := f
  rw [unField_bits h]
  rfl

/-- The CORRECT statement that replaces the false `toField_unField`: for a `.bits n` binder the result has the
binder's sort **iff** the field's width is `n`. The width equality is therefore a separate fact (see `ok_K_nexts`,
`ok_letsTyped`, `ok_outsFit`). -/
theorem unField_bits_sortOf_iff {n : Nat} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField (.bits n) f = some t) : sortOf (.bits n) = some t.1 ↔ f.1 = n := by
  rw [unField_bits_sort h]
  simp [sortOf, eq_comm]

/-- Any binder kind: the declared width hypothesis (`hw`, for `.bits` binders only) is exactly what is missing. -/
theorem unField_sortOf {k : MixedGateBinder} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField k f = some t) (hw : ∀ n, k = .bits n → f.1 = n) : sortOf k = some t.1 := by
  cases k with
  | domain => rw [unField_domain] at h; cases h
  | bool => exact unField_bool_sort h
  | bits n => exact (unField_bits_sortOf_iff h).2 (hw n rfl)

/-- The width **of a `.bits n` binder** is recovered from the sort (the converse direction). -/
theorem unField_width_of_sortOf {n : Nat} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField (.bits n) f = some t) (hs : sortOf (.bits n) = some t.1) : f.1 = n :=
  (unField_bits_sortOf_iff h).1 hs

/-- Output ports: `outKind o` is `.bool` or `.bits o.width`; with `o.width = (toField t.1 t.2).1` (the row of `outsFitB`)
the result has the kind's sort. -/
theorem unField_outKind_sort {o : OutField} {f : Σ w : Nat, Term (.bits w)} {t : Σ s : SType, Term s}
    (h : unField (outKind o) f = some t) (hw : o.width = (toField t.1 t.2).1) : sortOf (outKind o) = some t.1 := by
  by_cases hb : o.ty = Sparkle.IR.Type.HWType.bit
  · have hk : outKind o = .bool := by simp [outKind, hb]
    rw [hk] at h ⊢
    exact unField_bool_sort h
  · have hk : outKind o = .bits o.width := by
      unfold outKind; split <;> simp_all
    rw [hk] at h ⊢
    refine (unField_bits_sortOf_iff h).2 ?_
    have := unField_bits_toField h
    rw [this] at hw
    exact hw.symm

/-! ## The `ok` rows that supply sorts and widths (projections of `MachineData.ok = true`)

`readMachine` does not run `MachineData.ok`; these rows are what `dataOfAt`'s guard `d.ok` provides. -/

theorem ok_K_nexts {d : MachineData} (h : d.ok = true) :
    ∀ i, i < d.ss.length → d.K (d.nIn + i) = d.ss[i]? := by
  unfold MachineData.ok at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ok_letsTyped {d : MachineData} (h : d.ok = true) :
    LetsTyped d.bpos d.vpos d.kb d.kv d.vw d.K (d.nIn + d.ss.length) d.ls := by
  unfold MachineData.ok at h
  simp only [Bool.and_eq_true] at h
  exact of_decide_eq_true h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ok_outsFit {d : MachineData} (h : d.ok = true) :
    outsFitB d.kb d.kv d.vw d.fields d.shape.layout.outs d.outs = true := by
  unfold MachineData.ok at h
  simp only [Bool.and_eq_true] at h
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end Tools.ShippingGen5DataOfPure2
