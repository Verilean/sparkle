import Tools.ShippingGen5T2Tie
import Tools.ShippingGen2FitChain
set_option autoImplicit false
-- NOT BUILT: written without running Lean (unit rule: no lake/lean in this worker). No sorry / axiom / native_decide.

/-! # T2-SRCRANGE, T2-RANGE, T2-UNIQ (DGEN_FREEZE.md §7, rev2.1 at `par/gen5-t2` 59889446, + rev2.2 review notes)

Suppliers of the T2-TIE hypothesis `hDG_SEM_range : CallOutRange p q k hk` (Tools/ShippingGen5T2Tie.lean), which
stays an UNSUPPLIED intermediate interface until DG-HPOINT / T2-TIE consume this file. Not the FG, not M5; no FG
premise, no `T1Hyp` field and no shared definition is changed.

* **T2-SRCRANGE** (unconditional): `Pkg.src_range` — every source output of a package lies below `2 ^ o.width` of its
  own layout field, for all three arms `.gen` / `.loop` / `.comb`. Route per arm: the arm's source/result facts
  (`GenFacts.source`+`result`, `LoopFacts.hsrc`+`hres`, `CombFacts.hres`) give `f τ = enc t.1 (…)` for `t = d.outs[k']`,
  `enc_lt` bounds it by `2 ^ t.1.width`, and `outsFitB` inside `MachineData.ok` (via `Pkg`'s own `ok` field) gives
  `o.width = (toField t.1 t.2).1 = t.1.width`. No arm needs a premise.
* **T2-RANGE**: `outRange_of_bitWidth` (unconditional), `CallOutWidthAt` (the M3 result-width obligation re-indexed;
  NOT supplied here), `callOutRange_of_widths` (CONDITIONAL on `houtTy` — the `o.ty.bitWidth = o.width` row of the
  CALLEE — and on `CallOutWidthAt`; both explicit inputs), and the pure bridges `callOutWidthAt_of_oneOut` (from
  G-ONEOUT-WID's `OneOutWidth`) and `callOutWidthAt_of_kidW` (from the group `hkidW`, with the served child's `hy` /
  `hout` as EXPLICIT inputs; the caller obtains them for the same served `y`/`q`/`k` after `intro i`).
* **T2-UNIQ** (unconditional): `callField_unique_of_ok` from `MachineData.ok`'s `outs` names `Nodup`, and the collapse
  lemmas `genExtAtCall_iff_selected` / `callOutRange_iff_selected`: given T2-FIELD's per-`i` selection, the universal
  `∀ k' o f` forms are equivalent to the single selected output.

**Open (not supplied here):** `houtTy` for the callee (no current FG / `T1Hyp` field gives it: `T1Hyp`'s `DataOk` is an
abstract parameter), `CallOutWidthAt` coverage (G-ONEOUT-WID / `hkidW`, `sparkle-gen3-data-supply`), `GenExtAtCall`
(DG-SEM), and the `hy`/`hout` supply from `ClosingRun`. -/
namespace Tools.ShippingGen2
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

variable {ι : Type} {dom : ι → DomainConfig}

/-! ## T2-SRCRANGE -/

/-- `outsFitB` of a package's data, from `MachineData.ok` (the conjunct `ok_outs_length` uses). -/
theorem t2r_ok_outsFit (d : Tools.ShippingMachineAuto.MachineData) (ok : d.ok = true) :
    Tools.ShippingMachineAuto.outsFitB d.kb d.kv d.vw d.fields d.shape.layout.outs d.outs = true := by
  simp only [Tools.ShippingMachineAuto.MachineData.ok, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, houts, _⟩ := ok
  exact houts

theorem t2r_toField_fst : ∀ (s : Tools.ShippingUnifiedSource.SType) (tm : Tools.ShippingUnifiedSource.Term s),
    (Tools.ShippingMachineDenote.toField s tm).1 = s.width
  | .bool, _ => rfl
  | .bits _, _ => rfl

/-- A layout output's width is its data term's sort width (`outsFitB`), so a bound in the term's width transfers. -/
theorem t2r_width_of_out (d : Tools.ShippingMachineAuto.MachineData) (hok : d.ok = true) {k : Nat}
    {o : Sparkle.IR.Machine.OutField}
    {t : Σ s : Tools.ShippingUnifiedSource.SType, Tools.ShippingUnifiedSource.Term s}
    (ho : d.shape.layout.outs[k]? = some o) (ht : d.outs[k]? = some t) {x : Nat}
    (hx : x < 2 ^ t.1.width) : x < 2 ^ o.width := by
  have hw := (Tools.ShippingMachineAuto.outsFit_get (t2r_ok_outsFit d hok) ho ht).2.1
  rw [hw, t2r_toField_fst]
  exact hx

/-- The common step of the three arms: a source list whose values at `τ` are the `E`-images of the data terms, with
`E` bounded by the sort width, is bounded at every index. -/
theorem t2r_lt_of_map_eq {L : List (Nat → Nat)}
    {outs : List (Σ s : Tools.ShippingUnifiedSource.SType, Tools.ShippingUnifiedSource.Term s)} {τ : Nat}
    {E : (Σ s : Tools.ShippingUnifiedSource.SType, Tools.ShippingUnifiedSource.Term s) → Nat}
    (h : L.map (fun g => g τ) = outs.map E) (hE : ∀ o, E o < 2 ^ o.1.width) {k : Nat} {f : Nat → Nat}
    (hf : L[k]? = some f) : ∃ t, outs[k]? = some t ∧ f τ < 2 ^ t.1.width := by
  have h1 : (L.map (fun g => g τ))[k]? = some (f τ) := by
    simp only [List.getElem?_map, hf, Option.map_some]
  rw [h, List.getElem?_map] at h1
  revert h1
  cases ht : outs[k]? with
  | none => intro h1; first | cases h1 | simp at h1
  | some t =>
    intro h1
    have h2 : E t = f τ := by
      first
        | exact Option.some.inj h1
        | simpa using h1
    refine ⟨t, rfl, ?_⟩
    rw [← h2]
    exact hE t

/-- `.gen` arm. -/
theorem t2r_srcRange_gen (p : SrcPkg ι dom) : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (k' : Nat) (o : Sparkle.IR.Machine.OutField)
    (f : Nat → Nat),
    p.d.shape.layout.outs[k']? = some o → (p.src i bools bits)[k']? = some f →
    ∀ τ, f τ < 2 ^ o.width := by
  intro i bools bits k' o f ho hf τ
  letI := p.inh
  rw [p.gen.source i bools bits] at hf
  obtain ⟨t, ht, hlt⟩ := t2r_lt_of_map_eq (p.gen.result i bools bits _ τ)
    (fun o => Tools.ShippingQuadCalls.enc_lt o.1 _) hf
  exact t2r_width_of_out p.d p.gen.ok ho ht hlt

/-- `.loop` arm. -/
theorem t2r_srcRange_loop (p : Tools.ShippingGen2Loop.SrcPkgL ι dom) : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (k' : Nat) (o : Sparkle.IR.Machine.OutField)
    (f : Nat → Nat),
    p.d.shape.layout.outs[k']? = some o → (p.src i bools bits)[k']? = some f →
    ∀ τ, f τ < 2 ^ o.width := by
  intro i bools bits k' o f ho hf τ
  letI := p.inh
  rw [p.facts.hsrc i bools bits] at hf
  obtain ⟨t, ht, hlt⟩ := t2r_lt_of_map_eq (p.facts.hres i bools bits _ τ)
    (fun o => Tools.ShippingQuadCalls.enc_lt o.1 _) hf
  exact t2r_width_of_out p.d p.facts.ok ho ht hlt

/-- `.comb` arm. -/
theorem t2r_srcRange_comb (p : CombPkg ι dom) : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (k' : Nat) (o : Sparkle.IR.Machine.OutField)
    (f : Nat → Nat),
    p.d.shape.layout.outs[k']? = some o → (p.src i bools bits)[k']? = some f →
    ∀ τ, f τ < 2 ^ o.width := by
  intro i bools bits k' o f ho hf τ
  obtain ⟨t, ht, hlt⟩ := t2r_lt_of_map_eq (p.facts.hres i bools bits τ)
    (fun o => Tools.ShippingQuadCalls.enc_lt o.1 _) hf
  exact t2r_width_of_out p.d p.facts.ok ho ht hlt

/-- **T2-SRCRANGE** (DGEN §7.1, frozen type): every source output of a package lies in the range of its OWN layout
field width. Unconditional, all three arms. -/
theorem Pkg.src_range (q : Pkg ι dom) : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) (k' : Nat) (o : Sparkle.IR.Machine.OutField)
    (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → (q.src i bools bits)[k']? = some f →
    ∀ τ, f τ < 2 ^ o.width := by
  cases q with
  | gen p => exact t2r_srcRange_gen p
  | loop p => exact t2r_srcRange_loop p
  | comb p => exact t2r_srcRange_comb p

/-! ## T2-RANGE -/

/-- **`outRange_of_bitWidth`** (DGEN §7.3): a stream below `2 ^ (kindTy κ).bitWidth` is in `κ`'s range. -/
theorem outRange_of_bitWidth (κ : Sparkle.Compiler.Elab.MixedGateBinder) (f : Nat → Nat)
    (h : ∀ τ, f τ < 2 ^ (Tools.ShippingMachineEntry.kindTy κ).bitWidth) : OutRange κ f := by
  cases κ with
  | domain => exact True.intro
  | bool =>
    intro τ
    have h1 := h τ
    first
      | exact h1
      | simpa [Tools.ShippingMachineEntry.kindTy, Sparkle.IR.Type.HWType.bitWidth] using h1
  | bits w =>
    intro τ
    have h1 := h τ
    first
      | exact h1
      | simpa [Tools.ShippingMachineEntry.kindTy, Sparkle.IR.Type.HWType.bitWidth] using h1

/-- **`CallOutWidthAt`** (DGEN §7.2, frozen text): call `k` of `p` to `q`: every `CallField`-selected output of `q`
has the bit width of `p`'s binder at `p.kD + k`. The existing M3 result-width obligation re-indexed (NOT a new
obligation, NOT supplied here). -/
def CallOutWidthAt (p q : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o → CallField p q k o →
    (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
      some o.ty.bitWidth

/-- **`callOutRange_of_widths`** (DGEN §7.3): `Pkg.src_range` + the callee's `houtTy` row + `CallOutWidthAt` give the
T2-TIE range row. CONDITIONAL on `houtTy` and `hW` (explicit inputs). -/
theorem callOutRange_of_widths (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hW : CallOutWidthAt p q k) : CallOutRange p q k hk := by
  intro i bools bits k' o f ho hcf hf
  have hr := Pkg.src_range q i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits) k' o f
    ho hf
  have hty : o.ty.bitWidth = o.width := houtTy o (List.mem_iff_getElem?.mpr ⟨k', ho⟩)
  cases hb : (p.d.bsIn.drop p.kD)[k]? with
  | none =>
    show OutRange .domain f
    exact True.intro
  | some b =>
    have hlen : k < (p.d.bsIn.drop p.kD).length := (List.getElem?_eq_some_iff.mp hb).1
    have hbb : p.d.shape.binders[p.kD + k]? = some b := by
      rw [Tools.ShippingGen2Fit.binders_drop_at p.d p.kD k hlen]
      exact hb
    have hw := hW k' o ho hcf
    rw [hbb] at hw
    have hwe : (Tools.ShippingMachineEntry.kindTy b.2).bitWidth = o.ty.bitWidth := by
      simpa only [Option.map_some, Option.some.injEq] using hw
    show OutRange b.2 f
    refine outRange_of_bitWidth b.2 f (fun τ => ?_)
    rw [hwe, hty]
    exact hr τ

/-- **One-output bridge** (DGEN §7.2): G-ONEOUT-WID's `OneOutWidth` at call `k` gives `CallOutWidthAt`. Pure. -/
theorem callOutWidthAt_of_oneOut (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hq : P (p.d.shape.insts[k]).1 = some q) (h1 : p.d.shape.instFields = [])
    (hW : OneOutWidth P p k) : CallOutWidthAt p q k := by
  intro k' o _ hcf
  exact hW hk q hq o ((callField_one (p := p) (q := q) (k := k) (o := o) h1).mp hcf)

/-- **Group bridge** (DGEN §7.2): the group `hkidW` premise, at the served child `y` of call `k` whose outputs are
`q`'s layout outputs (`hout`), gives `CallOutWidthAt`. PURE: `hy` and `hout` are explicit inputs; the caller obtains
them for the same served `y`/`q`/`k` after `intro i` (no witness is taken out of `ChildShips` outside `∀ i`). -/
theorem callOutWidthAt_of_kidW {mref cref} (O : Tools.ShippingChildInvA.RefLawsAOps
      Tools.ShippingChildFresh.MkRefd mref cref) (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hG : p.d.shape.instFields ≠ []) {y : Tools.ShippingChildInv.Res}
    (hy : Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y)
    (hout : y.1.outputs = q.d.shape.layout.outs.map
      (fun o => ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port)))
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth) :
    CallOutWidthAt p q k := by
  intro k' o ho hcf
  have hn : o.name = p.d.shape.instFields.getD k "" :=
    (callField_group (p := p) (q := q) (k := k) (o := o) hG).mp hcf
  have hmem : ({ name := o.name, ty := o.ty } : Sparkle.IR.AST.Port) ∈ y.1.outputs := by
    rw [hout]
    exact List.mem_map.mpr ⟨o, List.mem_iff_getElem?.mpr ⟨k', ho⟩, rfl⟩
  exact hkidW k hk y hy _ hmem hn

/-! ## T2-UNIQ -/

/-- Index injectivity on a duplicate-free list (the proof of `Tools.ShippingSrm17Ran.nodup_idx`, restated here because
that module is not imported). -/
theorem t2r_nodup_idx : ∀ {l : List String} {i j : Nat} {r : String},
    l.Nodup → l[i]? = some r → l[j]? = some r → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | a :: l, i, j, r, hnd, hi, hj => by
    have hn := List.nodup_cons.mp hnd
    rcases i with _ | i <;> rcases j with _ | j
    · rfl
    · exfalso
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hi hj
      exact hn.1 (hi ▸ List.mem_of_getElem? hj)
    · exfalso
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hi hj
      exact hn.1 (hj ▸ List.mem_of_getElem? hi)
    · simp only [List.getElem?_cons_succ] at hi hj
      exact congrArg Nat.succ (t2r_nodup_idx hn.2 hi hj)

/-- The `outs` names `Nodup` conjunct of `MachineData.ok` (ShippingMachineAuto.lean:227). -/
theorem t2r_ok_outNames_nodup (d : Tools.ShippingMachineAuto.MachineData) (h : d.ok = true) :
    (d.shape.layout.outs.map (·.name)).Nodup := by
  simp only [Tools.ShippingMachineAuto.MachineData.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, -, -, -, -, -, -, hnd, -⟩ := h
  exact hnd

theorem t2r_idx_zero_of_singleton {o₁ o₂ : Sparkle.IR.Machine.OutField} :
    ∀ {k : Nat}, [o₁][k]? = some o₂ → k = 0
  | 0, _ => rfl
  | _ + 1, h => by simp at h

/-- **T2-UNIQ** (DGEN §7.4 (b), frozen type): at one call `k`, the `CallField` selection of `q`'s output is unique
(one-output: `outs = [o]`; group: names `Nodup` from `q.ok`). Unconditional. -/
theorem callField_unique_of_ok (p q : Pkg ι dom) (k : Nat) {k₁ k₂ : Nat} {o₁ o₂ : Sparkle.IR.Machine.OutField}
    (h₁ : q.d.shape.layout.outs[k₁]? = some o₁) (h₂ : q.d.shape.layout.outs[k₂]? = some o₂)
    (hc₁ : CallField p q k o₁) (hc₂ : CallField p q k o₂) : k₁ = k₂ ∧ o₁ = o₂ := by
  by_cases h1 : p.d.shape.instFields = []
  · have e1 := (callField_one (p := p) (q := q) (k := k) (o := o₁) h1).mp hc₁
    have e2 := (callField_one (p := p) (q := q) (k := k) (o := o₂) h1).mp hc₂
    have eo : o₁ = o₂ := (List.cons.inj (e1.symm.trans e2)).1
    rw [e1] at h₁ h₂
    exact ⟨(t2r_idx_zero_of_singleton h₁).trans (t2r_idx_zero_of_singleton h₂).symm, eo⟩
  · have n1 := (callField_group (p := p) (q := q) (k := k) (o := o₁) h1).mp hc₁
    have n2 := (callField_group (p := p) (q := q) (k := k) (o := o₂) h1).mp hc₂
    have g1 : (q.d.shape.layout.outs.map (·.name))[k₁]? = some o₁.name := by
      simp only [List.getElem?_map, h₁, Option.map_some]
    have g2 : (q.d.shape.layout.outs.map (·.name))[k₂]? = some o₁.name := by
      rw [n1, ← n2]
      simp only [List.getElem?_map, h₂, Option.map_some]
    have hkk : k₁ = k₂ := t2r_nodup_idx (t2r_ok_outNames_nodup q.d q.ok) g1 g2
    subst hkk
    rw [h₁] at h₂
    exact ⟨rfl, Option.some.inj h₂⟩

/-- **Collapse (GenExtAtCall)** (DGEN §7.4): with T2-FIELD's per-`i` selection, the universal `GenExtAtCall` is
equivalent to the `SigAt` fact at the single selected output (`callField_unique_of_ok` + `Option.some.inj`). The
selection is used after `intro i`; no `Nonempty ι`. -/
theorem genExtAtCall_iff_selected (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o) :
    GenExtAtCall p q k hk ↔
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
        ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
          q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o ∧
          (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f ∧
          SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
            (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f := by
  constructor
  · intro h i bools bits
    obtain ⟨k', o, ho, hc⟩ := hT2_FIELD i
    obtain ⟨f, hf⟩ := Pkg.src_get q i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits)
      k' o ho
    exact ⟨k', o, f, ho, hc, hf, h i bools bits k' o f ho hc hf⟩
  · intro h i bools bits k' o f ho hc hf
    obtain ⟨k₀, o₀, f₀, ho₀, hc₀, hf₀, hs⟩ := h i bools bits
    obtain ⟨rfl, rfl⟩ := callField_unique_of_ok p q k ho ho₀ hc hc₀
    rw [hf] at hf₀
    cases hf₀
    exact hs

/-- **Collapse (CallOutRange)** (DGEN §7.4): as `genExtAtCall_iff_selected`, for the range row. -/
theorem callOutRange_iff_selected (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hT2_FIELD : ∀ i : ι,
      ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField), q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o) :
    CallOutRange p q k hk ↔
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
        ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
          q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o ∧
          (q.src i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits))[k']? = some f ∧
          OutRange (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f := by
  constructor
  · intro h i bools bits
    obtain ⟨k', o, ho, hc⟩ := hT2_FIELD i
    obtain ⟨f, hf⟩ := Pkg.src_get q i (decA p q k hk i bools bits) (Tools.ShippingGen2.decB p q k hk i bools bits)
      k' o ho
    exact ⟨k', o, f, ho, hc, hf, h i bools bits k' o f ho hc hf⟩
  · intro h i bools bits k' o f ho hc hf
    obtain ⟨k₀, o₀, f₀, ho₀, hc₀, hf₀, hs⟩ := h i bools bits
    obtain ⟨rfl, rfl⟩ := callField_unique_of_ok p q k ho ho₀ hc hc₀
    rw [hf] at hf₀
    cases hf₀
    exact hs

end Tools.ShippingGen2

#print axioms Tools.ShippingGen2.Pkg.src_range
#print axioms Tools.ShippingGen2.outRange_of_bitWidth
#print axioms Tools.ShippingGen2.callOutRange_of_widths
#print axioms Tools.ShippingGen2.callOutWidthAt_of_oneOut
#print axioms Tools.ShippingGen2.callOutWidthAt_of_kidW
#print axioms Tools.ShippingGen2.callField_unique_of_ok
#print axioms Tools.ShippingGen2.genExtAtCall_iff_selected
#print axioms Tools.ShippingGen2.callOutRange_iff_selected
