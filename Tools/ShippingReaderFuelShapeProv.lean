import Tools.ShippingReaderFuelProv
import Tools.ShippingReaderFuelShapeR1

/-! # Wrapper-level call-entry PROVENANCE for the fuel CANDIDATE `machineShapeF`

STATUS 2026-10-19 (worker O, branch `par/o-cand`): WRITTEN, NOT BUILT against
the patched compiler (explicit call-entry origin, `MachRead.instOrigins`).
New (stored tag): `OriginTAt`, `machineShapeF_final_instProv`,
`machineShapeF_instOrigins_length`, `instOrigins_getD_eq`,
`machineShapeF_originT`, `machineShapeF_tag_exists`, `machineShapeF_tag_mem`,
`machineShapeF_tag_ord`, `machineShapeF_tag_field`, `originAt_of_originTAt`;
`machineShapeF_origin` (old statement) kept, re-derived through
`InstProv.origin`.

BUILT as written: run `p2` exit 0 (poc 6f216c4e); axioms run `axp`: [propext, Classical.choice, Quot.sound] (worker S-PROV, branch par/s-prov, from poc 3a1938a3;
reviewer milestone 1). No `sorry`, no axiom, no `native_decide`. No compiler
change.

SCOPE. Statements about the fuel candidate wrapper `machineShapeF` only; NOT
about the old `machineShape?` (O1/O2 outside).

The phases of `machineShapeF_steps` (`Tools/ShippingReaderFuelShapeR5.lean`)
keep `InstProv` (`Tools/ShippingReaderFuelProv.lean`), exactly as they keep
`InstR1` in `Tools/ShippingReaderFuelShapeR1.lean`: `{}` has no entries,
`machReserve` writes none of `insts` / `instFields` / `instStruct`, the
root-let fold, the body and the readers keep it (`readF_goodP`). `shapePost`
copies `st.insts` (`shapePost_insts`) and sets
`instFields := if st.instStruct then st.instFields.toList else []`
(`shapePost_instFields`).

* `machineShapeF_origin` — for EVERY entry index `k` of a successful
  candidate result, `sp.insts[k]? = some e → OriginAt senv e sp.instFields[k]?`:
  the entry is an ordinary one-Signal call (port `out`, or no field list), a
  structure field call (with its field index/name/kind, and the field list
  present: `sp.instFields[k]? = some nm`), or a memory placeholder call
  (port `out` or no field list).
* `machineShapeF_origin_mem` — the same by membership.

Premises: NONE beyond the candidate run (no `MemR1`, no `SigDisj`). -/
namespace Tools.ShippingReaderFuelShapeProv
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingReaderFuel
open Tools.ShippingReaderLenOk
open Tools.ShippingMachineShapeUnfold
open Tools.ShippingShapeDecomp
open Tools.ShippingReaderFuelShapeR5
open Tools.ShippingReaderFuelProv
open Tools.ShippingReaderFuelShapeR1 (shapePost_insts)

/-- **The origin of entry `e` read off a SHAPE**: `nm?` is the shape's
`instFields[k]?` (`none` when the shape carries no field list). -/
def OriginAt (senv : StructEnv) (e : Name × List Nat × MixedGateBinder)
    (nm? : Option String) : Prop :=
  (OrdOrigin senv e.1 e.2.2 ∧ (nm? = some "out" ∨ nm? = none)) ∨
  (∃ nm : String, StructOrigin senv e.1 e.2.2 nm ∧ nm? = some nm) ∨
  (MemOrigin e.1 e.2.2 ∧ (nm? = some "out" ∨ nm? = none))

/-! ## The shape's field list is the final state's (when a structure call or a
memory was read) -/

/-- `shapePost` (5132–5185) sets the shape's `instFields` from the final
state (same unfolding as `shapePost_insts`). -/
theorem shapePost_instFields {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead}
    {v : Lean.Expr} {sp : MachineShape} (h : shapePost ai p m st v = some sp) :
    sp.instFields = if st.instStruct then st.instFields.toList else [] := by
  unfold shapePost at h
  try dsimp only at h
  repeat' first
    | (replace h := ite_none_inv h)
    | (replace h := bind_inv h; obtain ⟨_, _, h⟩ := h)
    | (replace h := Option.bind_eq_some_iff.mp h; obtain ⟨_, _, h⟩ := h)
    | (split at h)
  all_goals first
    | (cases h; done)
    | skip
  all_goals
    try (replace h := ite_else_none_inv h)
    have hsp := Option.some.inj h
    subst hsp
    first
      | rfl
      | simp_all
      | (split <;> simp_all)

/-! ## The phases keep `InstProv` -/

section Phases
variable {senv : StructEnv} {n : Nat}

theorem shapeStart_instProv {m : ShapeMid} {st0 : MachRead}
    (hr : (shapeStart senv m).run (wtab senv n) = some (some st0)) : InstProv senv st0 := by
  rcases shapeStart_inv hr with ⟨_, h0⟩ | ⟨_, _, _, _, _, _, _, _, _, hres⟩
  · rw [h0]
    exact instProv_init
  · exact machReserve_instProv instProv_init hres

theorem shapeRootLet_instProv :
    ∀ (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
      (s' : List MachVal × MachRead),
      InstProv senv s.2 → (shapeRootLet senv s a).run (wtab senv n) = some (some s') →
        InstProv senv s'.2 := by
  rintro ⟨env, st⟩ ⟨nm, ty, v⟩ s' hst hr
  have hst' : InstProv senv st := hst
  first
    | (simp only [shapeRootLet] at hr)
    | (unfold shapeRootLet at hr; try dsimp only at hr)
  split at hr
  · -- a `Signal.loop` root
    obtain ⟨⟨mv, st2⟩, hl, hr⟩ := bindO_some_inv hr
    have h2 : InstProv senv st2 :=
      readF_goodP senv n (Call.loopRoot env v st) True.intro hst' (mv, st2) hl
    try dsimp only at hr
    have e := okO_run_inv hr
    subst e
    exact h2
  · split at hr
    · -- an ordinary root `let`
      obtain ⟨⟨v', st2⟩, hc, hr⟩ := bindO_some_inv hr
      have h2 : InstProv senv st2 :=
        readF_goodP senv n (Call.conv env 0 v st) True.intro hst' (v', st2) hc
      try dsimp only at hr
      revert hr
      first
        | (intro hr; have e := okO_run_inv hr; subst e; exact instProv_same h2 (by rfl) (by rfl) (by rfl) (by rfl))
        | (split <;> (intro hr; have e := okO_run_inv hr; subst e; exact instProv_same h2 (by rfl) (by rfl) (by rfl) (by rfl)))
        | ((repeat' split) <;> (intro hr; have e := okO_run_inv hr; subst e; exact instProv_same h2 (by rfl) (by rfl) (by rfl) (by rfl)))
    · exact (failO_run_inv hr).elim

theorem rootLets_instProv
    {l : List (Name × Lean.Expr × Lean.Expr)} {env env' : List MachVal} {st0 st1 : MachRead}
    (hr : (foldO (shapeRootLet senv) (env, st0) l).run (wtab senv n) = some (some (env', st1)))
    (h0 : InstProv senv st0) : InstProv senv st1 :=
  foldO_inv (fun s : List MachVal × MachRead => InstProv senv s.2)
    (shapeRootLet_instProv (senv := senv) (n := n)) l (env, st0) (env', st1) h0 hr

theorem shapeBody_instProv {m : ShapeMid}
    {env : List MachVal} {st1 st : MachRead} {v : Lean.Expr}
    (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v)))
    (h1 : InstProv senv st1) : InstProv senv st := by
  rcases shapeBody_inv hr with ⟨_, _, _, _, ws, v0, st2, _, hc, hst⟩ | ⟨_, hc⟩
  · rw [hst]
    exact instProv_same (machChainF_instProv hc h1) (by rfl) (by rfl) (by rfl) (by rfl)
  · exact machConvF_instProv hc h1

end Phases

/-! ## The whole wrapper -/

section Wrapper
variable {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
  {senv : StructEnv} {ai : Bool} {sp : MachineShape}

/-- **Provenance of every call entry of a successful candidate result, per
index** (no hypothesis on `senv`). -/
theorem machineShapeF_origin (h : machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder),
      sp.insts[k]? = some e → OriginAt senv e sp.instFields[k]? := by
  obtain ⟨p, en, st0, env, st1, st, v, _, _, h0, h1, h2, h3⟩ := machineShapeF_steps h
  have l0 : InstProv senv st0 := shapeStart_instProv h0
  have l1 : InstProv senv st1 := rootLets_instProv h1 l0
  have l2 : InstProv senv st := shapeBody_instProv h2 l1
  have hsz : st.insts.size = st.instFields.size := l2.1
  have H := InstProv.origin l2
  intro k e hk
  rw [shapePost_insts h3] at hk
  rw [shapePost_instFields h3]
  have hlt : k < st.instFields.toList.length := by
    obtain ⟨hk', _⟩ := List.getElem?_eq_some_iff.mp hk
    rw [Array.length_toList] at hk'
    rw [Array.length_toList, ← hsz]
    exact hk'
  cases hnm : st.instFields.toList[k]? with
  | none => exact absurd (List.getElem?_eq_none_iff.mp hnm) (Nat.not_le.mpr hlt)
  | some nm =>
    have hz : (st.insts.toList.zip st.instFields.toList)[k]? = some (e, nm) :=
      List.getElem?_zip_eq_some.mpr ⟨hk, hnm⟩
    rcases H k e nm hz with ⟨ho, hn⟩ | ⟨ho, hbt⟩ | ⟨ho, hn⟩
    · refine Or.inl ⟨ho, ?_⟩
      by_cases hb : st.instStruct = true
      · rw [if_pos hb, hnm, hn]
        exact Or.inl rfl
      · rw [if_neg hb]
        exact Or.inr List.getElem?_nil
    · rw [if_pos hbt, hnm]
      exact Or.inr (Or.inl ⟨nm, ho, rfl⟩)
    · refine Or.inr (Or.inr ⟨ho, ?_⟩)
      by_cases hb : st.instStruct = true
      · rw [if_pos hb, hnm, hn]
        exact Or.inl rfl
      · rw [if_neg hb]
        exact Or.inr List.getElem?_nil

/-- Provenance by membership (the field name forgotten). -/
theorem machineShapeF_origin_mem (h : machineShapeF n sm ps ci senv ai = some (some sp))
    {e : Name × List Nat × MixedGateBinder} (he : e ∈ sp.insts) :
    OrdOrigin senv e.1 e.2.2 ∨ (∃ nm : String, StructOrigin senv e.1 e.2.2 nm) ∨
      MemOrigin e.1 e.2.2 := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  rcases machineShapeF_origin h k e hk with ⟨ho, _⟩ | ⟨nm, ho, _⟩ | ⟨ho, _⟩
  · exact Or.inl ho
  · exact Or.inr (Or.inl ⟨nm, ho⟩)
  · exact Or.inr (Or.inr ho)

/-- An ORDINARY entry's kind is its signature's result (R1 for that entry,
from provenance; no `MemR1`, no `SigDisj`). -/
theorem originAt_ord_kind {e : Name × List Nat × MixedGateBinder}
    {kinds : List MixedGateBinder} {r : MixedGateBinder}
    (ho : OrdOrigin senv e.1 e.2.2) (hi : senv.inst e.1 = some (kinds, r)) : e.2.2 = r := by
  obtain ⟨kinds', hi'⟩ := ho
  rw [hi] at hi'
  exact ((Prod.mk.inj (Option.some.inj hi')).2).symm

/-! ## The STORED tag (patched compiler: `MachineShape.instOrigins`) -/

/-- **The origin of entry `e` read off a SHAPE by its stored tag** `o`
(`nm?` the shape's `instFields[k]?`). -/
def OriginTAt (senv : StructEnv) (e : Name × List Nat × MixedGateBinder)
    (nm? : Option String) : Sparkle.Compiler.MachInstOrigin.InstOrigin → Prop
  | .ord => OrdOrigin senv e.1 e.2.2 ∧ (nm? = some "out" ∨ nm? = none)
  | .field i => ∃ nm : String, StructOriginI senv e.1 e.2.2 nm i ∧ nm? = some nm
  | .mem combo aw dw => MemOriginI e.1 e.2.2 combo aw dw ∧ (nm? = some "out" ∨ nm? = none)

/-- The final reader state of a successful candidate run satisfies `InstProv`
(the three phases). -/
theorem machineShapeF_final_instProv (h : machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (m : ShapeMid) (st : MachRead) (v : Lean.Expr),
      InstProv senv st ∧ shapePost ai p m st v = some sp := by
  obtain ⟨p, en, st0, env, st1, st, v, _, _, h0, h1, h2, h3⟩ := machineShapeF_steps h
  have l0 : InstProv senv st0 := shapeStart_instProv h0
  have l1 : InstProv senv st1 := rootLets_instProv h1 l0
  have l2 : InstProv senv st := shapeBody_instProv h2 l1
  exact ⟨p, _, st, v, l2, h3⟩

/-- **Alignment**: a reader-produced shape has ONE origin tag per call entry
(so `MachineShape.instTagged`'s `getD k .ord` never supplies a missing tag). -/
theorem machineShapeF_instOrigins_length
    (h : machineShapeF n sm ps ci senv ai = some (some sp)) :
    sp.instOrigins.length = sp.insts.length := by
  obtain ⟨p, m, st, v, l2, h3⟩ := machineShapeF_final_instProv h
  rw [shapePost_instOrigins h3, shapePost_insts h3, Array.length_toList, Array.length_toList]
  exact l2.2.1

/-- **`getD` never hides a missing tag**: below the number of entries, the
default `.ord` of `MachineShape.instTagged` is never used. -/
theorem instOrigins_getD_eq (h : machineShapeF n sm ps ci senv ai = some (some sp)) {k : Nat}
    (hk : k < sp.insts.length) :
    sp.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord =
      sp.instOrigins[k]'(by rw [machineShapeF_instOrigins_length h]; exact hk) := by
  have hk' : k < sp.instOrigins.length := by
    rw [machineShapeF_instOrigins_length h]
    exact hk
  first
    | exact List.getD_eq_getElem hk'
    | exact List.getD_eq_getElem _ _ hk'
    | (rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; rfl)
    | simp [List.getD_eq_getElem?_getD, hk']

/-- **Provenance by the STORED tag, per index** (no hypothesis on `senv`): for
every entry `k` of a successful candidate result, its tag exists and the facts
of the arm the tag names hold — `.ord`: an ordinary signature, port `out` (or
no field list); `.field i`: field `i` of the callee's structure signature
(index, name, kind), the shape's field list present with that name;
`.mem combo aw dw`: `c = memChildName combo aw dw`, `r = .bits dw`, both
widths positive, port `out` (or no field list). -/
theorem machineShapeF_originT (h : machineShapeF n sm ps ci senv ai = some (some sp)) :
    ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder)
      (o : Sparkle.Compiler.MachInstOrigin.InstOrigin),
      sp.insts[k]? = some e → sp.instOrigins[k]? = some o →
        OriginTAt senv e sp.instFields[k]? o := by
  obtain ⟨p, m, st, v, l2, h3⟩ := machineShapeF_final_instProv h
  obtain ⟨hsz, _, H⟩ := l2
  intro k e o hk ho
  rw [shapePost_insts h3] at hk
  rw [shapePost_instOrigins h3] at ho
  rw [shapePost_instFields h3]
  have hlt : k < st.instFields.toList.length := by
    obtain ⟨hk', _⟩ := List.getElem?_eq_some_iff.mp hk
    rw [Array.length_toList] at hk'
    rw [Array.length_toList, ← hsz]
    exact hk'
  cases hnm : st.instFields.toList[k]? with
  | none => exact absurd (List.getElem?_eq_none_iff.mp hnm) (Nat.not_le.mpr hlt)
  | some nm =>
    have hz : (st.insts.toList.zip st.instFields.toList)[k]? = some (e, nm) :=
      List.getElem?_zip_eq_some.mpr ⟨hk, hnm⟩
    have HT := H k e nm o hz ho
    cases o with
    | ord =>
      obtain ⟨ho', hn⟩ := HT
      refine ⟨ho', ?_⟩
      by_cases hb : st.instStruct = true
      · rw [if_pos hb, hnm, hn]
        exact Or.inl rfl
      · rw [if_neg hb]
        exact Or.inr List.getElem?_nil
    | field i =>
      obtain ⟨ho', hbt⟩ := HT
      rw [if_pos hbt, hnm]
      exact ⟨nm, ho', rfl⟩
    | mem combo aw dw =>
      obtain ⟨ho', hn⟩ := HT
      refine ⟨ho', ?_⟩
      by_cases hb : st.instStruct = true
      · rw [if_pos hb, hnm, hn]
        exact Or.inl rfl
      · rw [if_neg hb]
        exact Or.inr List.getElem?_nil

/-- Every entry index of a reader-produced shape HAS a tag. -/
theorem machineShapeF_tag_exists (h : machineShapeF n sm ps ci senv ai = some (some sp))
    {k : Nat} {e : Name × List Nat × MixedGateBinder} (hk : sp.insts[k]? = some e) :
    ∃ o, sp.instOrigins[k]? = some o := by
  have hlt : k < sp.instOrigins.length := by
    rw [machineShapeF_instOrigins_length h]
    obtain ⟨hk', _⟩ := List.getElem?_eq_some_iff.mp hk
    exact hk'
  exact ⟨sp.instOrigins[k], List.getElem?_eq_getElem hlt⟩

/-- **Memory tag**: an entry tagged `.mem combo aw dw` IS the memory call of
exactly those parameters. -/
theorem machineShapeF_tag_mem (h : machineShapeF n sm ps ci senv ai = some (some sp))
    {k : Nat} {e : Name × List Nat × MixedGateBinder} {combo : Bool} {aw dw : Nat}
    (hk : sp.insts[k]? = some e) (ho : sp.instOrigins[k]? = some (.mem combo aw dw)) :
    e.1 = Sparkle.Compiler.MachMemory.memChildName combo aw dw ∧
      e.2.2 = MixedGateBinder.bits dw ∧ aw ≠ 0 ∧ dw ≠ 0 :=
  (machineShapeF_originT h k e _ hk ho).1

/-- **Ordinary tag**: an entry tagged `.ord` has its callee's one-Signal
signature with result `e.2.2`. -/
theorem machineShapeF_tag_ord (h : machineShapeF n sm ps ci senv ai = some (some sp))
    {k : Nat} {e : Name × List Nat × MixedGateBinder}
    (hk : sp.insts[k]? = some e) (ho : sp.instOrigins[k]? = some .ord) :
    OrdOrigin senv e.1 e.2.2 :=
  (machineShapeF_originT h k e _ hk ho).1

/-- **Field tag**: an entry tagged `.field i` is field `i` of its callee's
structure signature, and the shape's field list names it. -/
theorem machineShapeF_tag_field (h : machineShapeF n sm ps ci senv ai = some (some sp))
    {k i : Nat} {e : Name × List Nat × MixedGateBinder}
    (hk : sp.insts[k]? = some e) (ho : sp.instOrigins[k]? = some (.field i)) :
    ∃ nm : String, StructOriginI senv e.1 e.2.2 nm i ∧ sp.instFields[k]? = some nm :=
  machineShapeF_originT h k e _ hk ho

/-- The tagged form gives the pre-tag `OriginAt` (the old theorem
`machineShapeF_origin` re-derived through the tag). -/
theorem originAt_of_originTAt {e : Name × List Nat × MixedGateBinder} {nm? : Option String}
    {o : Sparkle.Compiler.MachInstOrigin.InstOrigin} (h : OriginTAt senv e nm? o) :
    OriginAt senv e nm? := by
  cases o with
  | ord => exact Or.inl h
  | field i =>
    obtain ⟨nm, hs, hn⟩ := h
    exact Or.inr (Or.inl ⟨nm, structOrigin_of_I hs, hn⟩)
  | mem combo aw dw => exact Or.inr (Or.inr ⟨memOrigin_of_I h.1, h.2⟩)

end Wrapper

end Tools.ShippingReaderFuelShapeProv
