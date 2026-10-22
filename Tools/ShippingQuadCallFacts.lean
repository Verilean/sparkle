import Tools.ShippingQuadCalls
-- BUILT (unit SR17): c8 exit 0 (Tools.ShippingQuadCallFacts c3; QuadCallFactsTest c8); final-SHA rebuild in REPORT-SR17.md.
-- SCOPE (binding, ledger L8aw): NARROWS `CallFactF` (SR16).  What the generated `machineExt` / `machineExtB` are: `machineExt := fun i bools bits S => extendBits (… (extendBits bits (nDecl+0) w₀ c₀) …) (nDecl+k) wₖ cₖ`
-- (`Tools/ShippingMachineCommand.lean`, `instExtension`), `cₖ` the call's SIGNAL read off the user's source; the callee's `machineSource` is the observation list of the callee's own call result.
-- PROVED here (generic): `callFactF_of_fam` — `CallFactF` follows from (i) a DISPATCH equation `hS` for the callee-source table (PROVED for the QUAD tables `quadSrcF_eq` and the leaf-callee tables `leafSrcC_eq`),
-- (ii) the two DECODING equations (inside `hPoint`: the decoded Bool / bit-vector families of the call's argument `let`s are the families `A` / `B` the generated extension builds; these are the generator's
-- own kernel-checked `gfHb*` / `gfHv*` facts, extracted typed by `oldGroupFact%`), and (iii) the OUTPUT DEFEQ (also in `hPoint`): the callee source at `(A, B)` has, at the field the call reads, an entry
-- whose value is the extension at the call-output position.  (iii) is a definitional equality of GENERATED definitions (the call signal `cₖ` IS the callee's observation); it holds by `rfl` in an
-- instance and has no statement over an abstract class without the structure of `cₖ`.  So `CallFactF` is NOT derived from the data bundles alone: the exact residue is `hPoint` (decoding equations + output defeq, per call).
-- Also PROVED: `extendBits_of_ne` / `extendBools_of_ne` (the extension does not change other positions), the building blocks of `hext` / `hextB` (positions of declared inputs < nDecl).
-- PREMISES are unchanged in kind: GenFacts, LeafSeqRunN, the residue above.  No sorry / axiom / native_decide.  RealChildA/ServedRealA are histories, not freshness.
namespace Tools.ShippingQuadCallFacts
open Tools.ShippingQuadCalls Tools.ShippingQuadComposed
open Tools.ShippingMachineAuto Tools.ShippingMachineChild
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Machine Sparkle.Compiler.Elab Lean

/-- **`CallFactF` from the decoding equations and the output defeq.**  `D i` is the domain the callee source is read at; `src i n A B` the callee `n`'s source on decoded families; `bsOf n` its binder table. -/
theorem callFactF_of_fam (dP : MachineData) (nP : Nat) {ι : Type} {dom : ι → DomainConfig} (D : ι → DomainConfig)
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {outsC : Name → List OutField}
    {S : ι → Name → (Nat → List Nat) → List (Nat → Nat)}
    (bsOf : Name → List (Name × MixedGateBinder))
    (src : (i : ι) → Name → (Nat → Signal (D i) Bool) → ((j : Nat) → (n : Nat) → Signal (D i) (BitVec n)) → List (Nat → Nat))
    (hS : ∀ (i : ι) (n : Name) (vals : Nat → List Nat),
      S i n vals = src i n (boolsOf (D := D i) (bsOf n) vals) (bitsOf (D := D i) (bsOf n) vals))
    (hPoint : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (k : Nat) (hk : k < dP.shape.insts.length),
      ∃ (A : Nat → Signal (D i) Bool) (B : (j : Nat) → (n : Nat) → Signal (D i) (BitVec n)),
        boolsOf (D := D i) (bsOf (dP.shape.insts[k]).1)
          (Tools.ShippingMachineCallsLinkedT.valsOf (lsrc i bools bits) (dP.shape.insts[k]).2.1) = A ∧
        bitsOf (D := D i) (bsOf (dP.shape.insts[k]).1)
          (Tools.ShippingMachineCallsLinkedT.valsOf (lsrc i bools bits) (dP.shape.insts[k]).2.1) = B ∧
        ∃ (k' : Nat) (o : OutField) (f : Nat → Nat),
          (outsC (dP.shape.insts[k]).1)[k']? = some o ∧ o.name = dP.shape.instFields.getD k "" ∧
          (src i (dP.shape.insts[k]).1 A B)[k']? = some f ∧
          ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => ((extB i bools bits) p).val τ) (fun p n => ((ext i bools bits) p n).val τ)
            (nP + k) (((dP.bsIn.drop nP)[k]?.map (·.2)).getD .domain) = f τ) :
    CallFactF dP nP lsrc ext extB outsC S := by
  intro i bools bits k hk
  obtain ⟨A, B, hA, hB, k', o, f, h1, h2, h3, h4⟩ := hPoint i bools bits k hk
  refine ⟨k', o, f, h1, h2, ?_, h4⟩
  rw [hS, hA, hB]
  exact h3

/-- The QUAD callee-binder table by name (the one `quadSrcF` decodes with). -/
def quadBsOf (c₁ c₂ : Name) (d₁ d₂ : MachineData) (n₁ n₂ : Nat) (n : Name) : List (Name × MixedGateBinder) :=
  if n = c₁ then List.take n₁ d₁.bsIn else List.take n₂ d₂.bsIn

/-- The QUAD callee source on decoded families. -/
def quadSrcA {ι : Type} (c₁ c₂ : Name)
    (src₁ src₂ : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat))
    (_i : ι) (n : Name) (A : Nat → Signal defaultDomain Bool) (B : (j : Nat) → (n : Nat) → Signal defaultDomain (BitVec n)) : List (Nat → Nat) :=
  if n = c₁ then src₁ defaultDomain A B else if n = c₂ then src₂ defaultDomain A B else []

/-- **The dispatch equation `hS` for the QUAD tables, PROVED** (`quadSrcF` is `quadSrcA` on the decoded families), for callees named `c₁ ≠ c₂`-agnostically. -/
theorem quadSrcF_eq {ι : Type} (c₁ c₂ : Name) (d₁ d₂ : MachineData) (n₁ n₂ : Nat)
    (src₁ src₂ : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat))
    (i : ι) (n : Name) (vals : Nat → List Nat) :
    quadSrcF c₁ c₂ d₁ d₂ n₁ n₂ src₁ src₂ i n vals =
      quadSrcA c₁ c₂ src₁ src₂ i n (boolsOf (D := defaultDomain) (quadBsOf c₁ c₂ d₁ d₂ n₁ n₂ n) vals)
        (bitsOf (D := defaultDomain) (quadBsOf c₁ c₂ d₁ d₂ n₁ n₂ n) vals) := by
  unfold quadSrcF quadSrcA quadBsOf
  by_cases h1 : n = c₁
  · simp [h1]
  · by_cases h2 : n = c₂
    · subst h2; simp [h1]
    · simp [h1, h2]

/-- The callee-source table of a leaf-callee on decoded families. -/
def leafSrcA (G : Name)
    (srcG : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat))
    (i : DomainConfig) (n : Name) (A : Nat → Signal i Bool) (B : (j : Nat) → (n : Nat) → Signal i (BitVec n)) : List (Nat → Nat) :=
  if n = G then srcG i A B else []

/-- **The dispatch equation `hS` for the leaf-callee tables, PROVED.** -/
theorem leafSrcC_eq (G : Name) (dG : MachineData)
    (srcG : (i : DomainConfig) → (Nat → Signal i Bool) → ((j : Nat) → (n : Nat) → Signal i (BitVec n)) → List (Nat → Nat))
    (i : DomainConfig) (n : Name) (vals : Nat → List Nat) :
    leafSrcC G dG srcG i n vals = leafSrcA G srcG i n (boolsOf (D := i) dG.bsIn vals) (bitsOf (D := i) dG.bsIn vals) := by
  unfold leafSrcC leafSrcA
  by_cases h : n = G <;> simp [h]

/-- Other positions are unchanged by an extension (the declared inputs `j < nDecl` of the generated `machineExt`). -/
theorem extendBits_of_ne {D : DomainConfig} (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) {pos w j : Nat}
    (sig : Signal D (BitVec w)) (h : j ≠ pos) (n : Nat) : extendBits bits pos w sig j n = bits j n := by
  unfold extendBits; rw [dif_neg (fun h' => h h'.1)]

theorem extendBools_of_ne {D : DomainConfig} (bools : Nat → Signal D Bool) {pos j : Nat}
    (sig : Signal D Bool) (h : j ≠ pos) : Tools.ShippingMachineCausal.extendBools bools pos sig j = bools j := by
  unfold Tools.ShippingMachineCausal.extendBools; rw [if_neg h]

end Tools.ShippingQuadCallFacts

#print axioms Tools.ShippingQuadCallFacts.callFactF_of_fam
#print axioms Tools.ShippingQuadCallFacts.quadSrcF_eq
#print axioms Tools.ShippingQuadCallFacts.leafSrcC_eq
#print axioms Tools.ShippingQuadCallFacts.extendBits_of_ne
#print axioms Tools.ShippingQuadCallFacts.extendBools_of_ne
