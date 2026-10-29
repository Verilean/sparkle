import Tools.ShippingGen2CallField
import Tools.ShippingGen2T2Probe
set_option autoImplicit false
-- Built: g5td-ca10ee64 (clean snapshot, exit 0, standard axioms). No sorry / axiom / native_decide.

/-! # T2-DEC: `HPointG` ⇔ `CallOutG`, and ⇔ `CallOutF` on the decoded argument families

Issue `sparkle-gen5-t2-tie`, the T2-DEC part. Design-to-code of scripts/gen5/T2COVER_FREEZE.md §0 (the `CallField`
form, rev1 R3) and scripts/gen5/M5_INDEP_STUDIES.md §A.3/§A.4 (both approved at `par/gen5-t2` c398021c). This is NOT
the FG and changes no FG premise; it is a standalone equivalence about existing texts.

* `decA` / `decB`: the DECODED argument families of call `k` (the parent's let observations at the call's argument
  lets, decoded with the callee `q`'s port list `q.d.bsIn.take q.kD`).
* `letTie_dec`: `LetTie` (Tools/ShippingGen2T2Probe.lean) holds for `decA`/`decB` by `rfl` (t2 is by definition).
* `CallOutF`: `CallOut` (T2Probe) with the name conjunct replaced by `CallField p q k o` (Tools/ShippingGen2Defs.lean),
  i.e. route-aware: one-output AND group parents.
* `pkgBsC_of`, `pkgOutsC_of`, `pkgSrc_of`: the three dispatch equations at `P c = some q`, factored out of
  `hPointAt_of_ties` (T2Probe).
* (1) `hPointG_iff_callOutG`: `HPointG P p q k ↔ CallOutG P p q k` for EVERY `P p q k` (no `hP`). → by `subst` of the
  two decoding equations and `pkgS_dispatch` (Tools/ShippingGen2CallDec.lean); ← as `hPointAt_of_callFactF_at`
  (Tools/ShippingGen2Adapt.lean) with `CallField` passed through.
* (2) `hPointG_iff_callOutDec`: under `hP : P (insts[k]'hk).1 = some q`,
  `HPointG P p q k ↔ CallOutF p q k (decA p q k hk) (decB p q k hk)` (the T2-DEC statement, both routes).
* (3) `hPointAt_iff_callOutDec`: the group corollary on the OLD texts (`HPointAt`, `CallOut`), under
  `instFields ≠ []`, through the group adapters of Tools/ShippingGen2CallField.lean and `callField_group`.

Not supplied here: `CallOutF` itself for any package (T2-POSENC + T2-FIELD + DG-GENPKG). The equivalences say only that
`HPointG`'s existential families are forced to be the decoded ones. -/
namespace Tools.ShippingGen2
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

variable {ι : Type} {dom : ι → DomainConfig}

/-! ## Decoded families and `LetTie` -/

/-- The decoded Bool argument family of call `k` (callee port list of `q`). -/
noncomputable def decA (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) : ArgFamB ι dom :=
  fun i bools bits => Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD)
    (Tools.ShippingMachineCallsLinkedT.valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1)

/-- The decoded bit-vector argument family of call `k` (callee port list of `q`). -/
noncomputable def decB (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) : ArgFamV ι dom :=
  fun i bools bits => Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD)
    (Tools.ShippingMachineCallsLinkedT.valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1)

/-- t2 on the decoded families: by definition. -/
theorem letTie_dec (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) :
    LetTie p q k hk (decA p q k hk) (decB p q k hk) := by
  intro i bools bits
  exact ⟨rfl, rfl⟩

/-! ## The route-aware `CallOut` -/

/-- `CallOut` (Tools/ShippingGen2T2Probe.lean) with the route-aware selection `CallField p q k o` in the name slot
(one-output and group parents). -/
def CallOutF (p q : Pkg ι dom) (k : Nat) (A : ArgFamB ι dom) (B : ArgFamV ι dom) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
      q.d.shape.layout.outs[k']? = some o ∧ CallField p q k o ∧
      (q.src i (A i bools bits) (B i bools bits))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (p.extBS i bools bits r).val τ)
          (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

/-! ## The three dispatch equations at `P c = some q` (factored out of `hPointAt_of_ties`) -/

theorem pkgBsC_of {P : Pkgs ι dom} {c : Lean.Name} {q : Pkg ι dom} (hP : P c = some q) :
    pkgBsC P c = q.d.bsIn.take q.kD := by
  have h := congrArg (fun o : Option (Pkg ι dom) => (o.map fun q' => q'.d.bsIn.take q'.kD).getD []) hP
  exact h

theorem pkgOutsC_of {P : Pkgs ι dom} {c : Lean.Name} {q : Pkg ι dom} (hP : P c = some q) :
    pkgOutsC P c = q.d.shape.layout.outs := by
  have h := congrArg (fun o : Option (Pkg ι dom) => (o.map fun q' => q'.d.shape.layout.outs).getD []) hP
  exact h

theorem pkgSrc_of {P : Pkgs ι dom} {c : Lean.Name} {q : Pkg ι dom} (hP : P c = some q) (i : ι)
    (A : Nat → Signal (dom i) Bool) (B : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    pkgSrc P i c A B = q.src i A B := by
  have h := congrArg (fun o : Option (Pkg ι dom) => (o.map fun q' => q'.src i A B).getD []) hP
  exact h

/-! ## (1) `HPointG` ⇔ `CallOutG`, every `P p q k` -/

/-- **(1)** No `hP`: `HPointG`'s families are forced to the decoded ones, and `pkgS` is `pkgSrc` on them. -/
theorem hPointG_iff_callOutG (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat) :
    HPointG P p q k ↔ CallOutG P p q k := by
  constructor
  · intro h i bools bits hk
    obtain ⟨A, B, hA, hB, k', o, f, ho, hcf, hf, hpos⟩ := h i bools bits hk
    subst hA
    subst hB
    refine ⟨k', o, f, ho, hcf, ?_, hpos⟩
    rw [pkgS_dispatch]
    exact hf
  · intro h i bools bits hk
    obtain ⟨k', o, f, ho, hcf, hf, hpos⟩ := h i bools bits hk
    refine ⟨_, _, rfl, rfl, k', o, f, ho, hcf, ?_, hpos⟩
    rw [← pkgS_dispatch]
    exact hf

/-! ## (2) T2-DEC: `HPointG` ⇔ `CallOutF` on `decA`/`decB` -/

/-- **(2) T2-DEC** (both routes): at `hP`, `HPointG` is `CallOutF` on the decoded families. -/
theorem hPointG_iff_callOutDec (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]'hk).1 = some q) :
    HPointG P p q k ↔ CallOutF p q k (decA p q k hk) (decB p q k hk) := by
  constructor
  · intro h i bools bits
    obtain ⟨A, B, hA, hB, k', o, f, ho, hcf, hf, hpos⟩ := h i bools bits hk
    have hP' : P (p.d.shape.insts[k]'hk).1 = some q := hP
    rw [pkgBsC_of hP'] at hA hB
    subst hA
    subst hB
    rw [pkgOutsC_of hP'] at ho
    rw [pkgSrc_of hP'] at hf
    exact ⟨k', o, f, ho, hcf, hf, hpos⟩
  · intro h i bools bits hk'
    have hP' : P (p.d.shape.insts[k]'hk').1 = some q := hP
    obtain ⟨k', o, f, ho, hcf, hf, hpos⟩ := h i bools bits
    refine ⟨decA p q k hk i bools bits, decB p q k hk i bools bits, ?_, ?_, k', o, f, ?_, hcf, ?_, hpos⟩
    · rw [pkgBsC_of hP'] <;> rfl
    · rw [pkgBsC_of hP'] <;> rfl
    · rw [pkgOutsC_of hP'] <;> exact ho
    · rw [pkgSrc_of hP'] <;> exact hf

/-! ## (3) The group corollary on the old texts -/

/-- **(3)** Under `instFields ≠ []`: the old `HPointAt` is the old (group-only) `CallOut` on `decA`/`decB`. It does NOT
cover one-output parents (`instFields = []`); (2) does. -/
theorem hPointAt_iff_callOutDec (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hG : p.d.shape.instFields ≠ []) :
    Tools.ShippingQuadHPoint.HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k ↔
      CallOut p q k (decA p q k hk) (decB p q k hk) := by
  constructor
  · intro h
    have h2 := (hPointG_iff_callOutDec P p q k hk hP).mp
      (hPointG_of_hPointAt_group (P := P) (p := p) (q := q) (k := k) hG h)
    intro i bools bits
    obtain ⟨k', o, f, ho, hcf, hf, hpos⟩ := h2 i bools bits
    exact ⟨k', o, f, ho, (callField_group (q := q) (k := k) (o := o) hG).mp hcf, hf, hpos⟩
  · intro h
    apply hPointAt_of_hPointG_group (P := P) (p := p) (q := q) (k := k) hG
    apply (hPointG_iff_callOutDec P p q k hk hP).mpr
    intro i bools bits
    obtain ⟨k', o, f, ho, hon, hf, hpos⟩ := h i bools bits
    exact ⟨k', o, f, ho, (callField_group (q := q) (k := k) (o := o) hG).mpr hon, hf, hpos⟩

end Tools.ShippingGen2

#print axioms Tools.ShippingGen2.letTie_dec
#print axioms Tools.ShippingGen2.hPointG_iff_callOutG
#print axioms Tools.ShippingGen2.hPointG_iff_callOutDec
#print axioms Tools.ShippingGen2.hPointAt_iff_callOutDec
