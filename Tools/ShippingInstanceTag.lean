import Sparkle.Compiler.Elab

/-! # The tag of an instance root, from the ROUTE reading (round par/b-37)

WRITTEN, NOT BUILT. PURE: about the gate's Boolean functions only, no run.

The mixed gate takes a parent whose body is a designated call only under the
instance predicate of the environment the entry read (`isInst :=
instancePredicate envR`). This file reads the tag back out of that
acceptance:

* `instancePredicate_const`: `instancePredicate env e = true` at an
  expression whose head is the constant `mn` gives
  `isHardwareModule env mn = true`, or `mn` is a structure projection in
  `env` (the predicate's second disjunct: a projection of a tagged record).
* `unifiedInstanceRoot_isInst`, `hierInstRoot_isInst`: the two ROOT
  disjuncts of `mixedCertifiedShape?` whose body is itself a call imply
  `isInst body = true`.
* `root_tag`: together — for the environment `envR` the entry read.

What this does NOT give (and nothing built gives; `docs/parallel/
B-slotless-parents-2.md` §11): the same about the environment the instance
arm reads LATER in the run (`instArmEnv`, a second `getEnv`). -/
namespace Tools.ShippingInstanceTag
open Lean Sparkle.Compiler.Elab

/-- The instance predicate at a constant-headed expression: the head is
tagged, or it is a structure projection of the environment. -/
theorem instancePredicate_const {env : Environment} {e : Lean.Expr} {mn : Name}
    {us : List Level} (hfn : e.getAppFn = .const mn us)
    (h : instancePredicate env e = true) :
    Sparkle.Compiler.isHardwareModule env mn = true ∨
      (env.getProjectionStructureName? mn).isSome = true := by
  unfold instancePredicate at h
  rw [hfn] at h
  dsimp only at h
  rw [Bool.or_eq_true] at h
  rcases h with ht | hp
  · exact Or.inl ht
  · right
    cases hs : env.getProjectionStructureName? mn with
    | some s => rfl
    | none =>
      rw [hs] at hp
      simp at hp

/-- The canonical instance root is designated by the predicate. -/
theorem unifiedInstanceRoot_isInst {isInst : Lean.Expr → Bool}
    {kinds : Array MixedGateBinder} {e : Lean.Expr}
    (h : unifiedInstanceRoot isInst kinds e = true) : isInst e = true := by
  unfold unifiedInstanceRoot at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- The pipeline root is designated by the predicate. -/
theorem hierInstRoot_isInst {isInst : Lean.Expr → Bool}
    {kinds : Array MixedGateBinder} {e : Lean.Expr}
    (h : hierInstRoot isInst kinds e = true) : isInst e = true := by
  unfold hierInstRoot at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- **The tag of an instance root, from the gate's acceptance**: a body the
gate accepts as an instance root (either root disjunct) under the instance
predicate of `envR`, with the constant `mn` at its head, has `mn` tagged in
`envR` — or `mn` is a structure projection of `envR`. -/
theorem root_tag {envR : Environment} {kinds : Array MixedGateBinder} {e : Lean.Expr}
    {mn : Name} {us : List Level} (hfn : e.getAppFn = .const mn us)
    (h : unifiedInstanceRoot (instancePredicate envR) kinds e = true ∨
      hierInstRoot (instancePredicate envR) kinds e = true) :
    Sparkle.Compiler.isHardwareModule envR mn = true ∨
      (envR.getProjectionStructureName? mn).isSome = true := by
  rcases h with h | h
  · exact instancePredicate_const hfn (unifiedInstanceRoot_isInst h)
  · exact instancePredicate_const hfn (hierInstRoot_isInst h)

end Tools.ShippingInstanceTag
