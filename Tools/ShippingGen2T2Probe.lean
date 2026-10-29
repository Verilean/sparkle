import Tools.ShippingGen2CallDec
set_option autoImplicit false

/-! # Gen5 t2 probe: `LetTie` (t2), `CallOut` (t1+t3) and the sufficiency lemma `hPointAt_of_ties`
(scripts/gen2/T2_PROBE_FREEZE.md rev2 §3, approved at fff35a35, with the reviewer corrections)

* `ArgFamB` / `ArgFamV`: the argument families of ONE ordinary call (the generator's `A` / `B`,
  Tools/ShippingMachineDepthCommandR.lean:765-778), taken as a PARAMETER.
* `LetTie p q k hk A B` (t2): the parent's let observations at call `k`'s argument lets
  `(p.d.shape.insts[k]'hk).2.1`, decoded with the CALLEE's port list `q.d.bsIn.take q.kD`, are `A` / `B`.
* `CallOut p q k A B` (t1+t3): on `A` / `B`, the callee's source has the output named by the call's field (explicit
  index / name / existence witnesses `k'`, `o`, `f`; no `getD` hides a missing output), and the parent's value at the
  call-output position `p.kD + k` is that output.
* `hPointAt_of_ties`: `LetTie ∧ CallOut ⇒ HPointAt … k` for an assignment `P` with `P (insts[k]'hk).1 = some q`.
  This is SUFFICIENCY ONLY. The converse (that an `HPointAt … k` comes from some, or from the generator's, `A` / `B`
  with `LetTie ∧ CallOut`) is NOT stated and NOT proved here.

The arity (`args.length = q.ports.length`) is not part of `LetTie`; it stays `CallDec`'s conjunct.
Nothing here supplies `LetTie` or `CallOut` for any package: both are hypotheses. No sorry / axiom / native_decide. -/
namespace Tools.ShippingGen2
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

variable {ι : Type} {dom : ι → DomainConfig}

/-- The Bool argument family of an ordinary call, per index / input families (the generator's `A`). -/
abbrev ArgFamB (ι : Type) (dom : ι → DomainConfig) :=
  (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Nat → Signal (dom i) Bool

/-- The bit-vector argument family of an ordinary call, per index / input families (the generator's `B`). -/
abbrev ArgFamV (ι : Type) (dom : ι → DomainConfig) :=
  (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)

/-- **t2 (`LetTie`)**: the parent's let observations at call `k`'s argument lets, decoded with the CALLEE package
`q`'s port list, are the call's argument families (the shape of the generated `gfHb` / `gfHv`,
Tools/ShippingMachineDepthCommandR.lean:406, and of SR19's `Hb0` / `Hv0`, Tools/ShippingSeqParentGenD2MSG.lean:126). -/
def LetTie (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) (A : ArgFamB ι dom)
    (B : ArgFamV ι dom) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD)
        (Tools.ShippingMachineCallsLinkedT.valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1) =
      A i bools bits ∧
    Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD)
        (Tools.ShippingMachineCallsLinkedT.valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1) =
      B i bools bits

/-- **t1+t3 (`CallOut`)**: on the call's argument families, the callee `q`'s source has the output named by the
call's field, with an explicit index / name / existence witness, and the parent's call-result value is it. -/
def CallOut (p q : Pkg ι dom) (k : Nat) (A : ArgFamB ι dom) (B : ArgFamV ι dom) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    ∃ (k' : Nat) (o : Sparkle.IR.Machine.OutField) (f : Nat → Nat),
      q.d.shape.layout.outs[k']? = some o ∧ o.name = p.d.shape.instFields.getD k "" ∧
      (q.src i (A i bools bits) (B i bools bits))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun r => (p.extBS i bools bits r).val τ)
          (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

/-- **The conditional generic lemma (full telescope), SUFFICIENCY ONLY.** For every `i bools bits hk'`, the
existential witnesses of `HPointAt` are `A i bools bits` / `B i bools bits`; `h2` gives the two decoding equations
after `pkgBsC P c = q.d.bsIn.take q.kD` (at `hP`), `h13` the output conjuncts through `pkgOutsC` / `pkgSrc` at `hP`.
`hP` is stated at `(p.d.shape.insts[k]'hk).1`, the form `HPointAt` uses (`dP.shape.insts[k]` under its `hk`). -/
theorem hPointAt_of_ties (P : Pkgs ι dom) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hP : P (p.d.shape.insts[k]'hk).1 = some q)
    (A : ArgFamB ι dom) (B : ArgFamV ι dom)
    (h2 : LetTie p q k hk A B) (h13 : CallOut p q k A B) :
    Tools.ShippingQuadHPoint.HPointAt p.d p.kD dom p.lsrc p.extS p.extBS (pkgOutsC P) (pkgBsC P) (pkgSrc P) k := by
  intro i bools bits hk'
  have hP' : P (p.d.shape.insts[k]'hk').1 = some q := hP
  -- the three dispatch equations at `hP` (each `congrArg` is elaborated without an expected type, then
  -- matched against the `pkg*` definition by `exact`)
  have hB : pkgBsC P (p.d.shape.insts[k]'hk').1 = q.d.bsIn.take q.kD := by
    have h := congrArg (fun o : Option (Pkg ι dom) => (o.map fun q' => q'.d.bsIn.take q'.kD).getD []) hP'
    exact h
  have hO : pkgOutsC P (p.d.shape.insts[k]'hk').1 = q.d.shape.layout.outs := by
    have h := congrArg (fun o : Option (Pkg ι dom) => (o.map fun q' => q'.d.shape.layout.outs).getD []) hP'
    exact h
  have hS : ∀ (A' : Nat → Signal (dom i) Bool) (B' : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      pkgSrc P i (p.d.shape.insts[k]'hk').1 A' B' = q.src i A' B' := by
    intro A' B'
    have h := congrArg (fun o : Option (Pkg ι dom) => (o.map fun q' => q'.src i A' B').getD []) hP'
    exact h
  obtain ⟨hA, hBv⟩ := h2 i bools bits
  obtain ⟨k', o, f, ho, hon, hf, hpos⟩ := h13 i bools bits
  refine ⟨A i bools bits, B i bools bits, ?_, ?_, k', o, f, ?_, hon, ?_, hpos⟩
  · rw [hB]; exact hA
  · rw [hB]; exact hBv
  · rw [hO]; exact ho
  · rw [hS]; exact hf

end Tools.ShippingGen2

#print axioms Tools.ShippingGen2.hPointAt_of_ties
