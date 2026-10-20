import Tools.ShippingLegacySemEntryIn
import Tools.ShippingLegacySemBinderList
import Tools.ShippingLegacySemLeaves
import Tools.ShippingLegacySemLeaf
import Tools.ShippingLegacySemHarnessLeaf

variable {tenv : Lean.Environment}

/-! # The legacy entry on a declaration with a LIST of scalar binders and a scalar result

`one_binder_entry_output_bound` (`Tools/ShippingLegacySemEntryBound.lean`)
lifted from one `bits n` binder to a list of `bits n` / `bool` binders.

**Defined here**: `ListScope B leafOf mctx xs inner` — what the entry needs of
the telescope's hand-over: variables `ids`, the body `leafOf ids`, and the
declarations of the variables in the continuation's context, with the names
and declared types of `B` (`DeclsAt … 0 B ids`).

**Proved here**: `list_entry_output` — for a definition that the three gates
decline (or with the front end off), whose telescope hands over
`ListScope B leafOf`, whose binders satisfy `BinderOracle` (not a domain
binder; the type oracle returns the kind's port type and has no catchable
failure on the declared type) and whose result is a non-lambda with a
Signal-headed type: a successful run of the entry is a memo hit, or the
module's `out` carries the leaf's value for every admissible valuation at
which the leaf is in `LeafDom … "out" true`.

Composition: `legacy_entry_walk_in` (the entry in the telescope's context),
`splitReturnLeaves_scalar`, `bindInputsLegacy_prepare` (the walk inverted to
the prepared setup), `harness_sound_leaf`, `leaf_translate_spec` /
`leaf_translate_order`.

**Premises, classified**: as `one_binder_entry_output_bound`, per binder —
`htele` (Meta-library fact + the body's shape; see
`Tools/ShippingLegacySemTelescopeN.lean`), `BinderOracle` (binder-type
oracle: returning and failing runs), `SignalTyped` (result-type oracle);
`old` / `mixed` / `hmach` (environment, front end on only). The Signal
test's frame is proved (`isSignalBinderType_frame`). `MemoHit` stays. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)

/-- What the telescope hands over for a declaration with the binders `B` and
the result `leafOf ids`. -/
def ListScope (B : List (Name × MixedGateBinder × Lean.Expr))
    (leafOf : List FVarId → Lean.Expr)
    (mctx : Meta.Context) (xs : Array Lean.Expr) (inner : Lean.Expr) : Prop :=
  ∃ ids : List FVarId, inner = leafOf ids ∧ DeclsAt mctx xs 0 B ids

/-- **The output of a legacy-route declaration with scalar binders and a
scalar Signal result.** -/
theorem list_entry_output {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {B : List (Name × MixedGateBinder × Lean.Expr)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {cfe : Bool}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (ListScope B leafOf))
    (horacle : ∀ q, q ∈ B → BinderOracle q)
    (hleaf : ∀ ids : List FVarId, (leafOf ids).isLambda = false ∧ SignalTyped (leafOf ids))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire tenv e hint top named)
      logProf declName [] false cfe (.defnInfo dv) isInst) (m, d)) :
    MemoHit declName m d ∨
    ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.length = B.length ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
        ((bindersOf B).zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl declName)) →
      ∀ v : Value, 0 < v.kind.width →
      LeafDom tenv (setupOf declName (bindersOf B) ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName (bindersOf B) ids cache bools bits).bools
          (setupOf declName (bindersOf B) ids cache bools bits).bits)
        "out" true (leafOf ids) v →
      Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width (bindersOf B) m initial mems
        v.toNat := by
  rcases legacy_entry_walk_in old mixed hmach htele hr with hit |
    ⟨body0, mctx, xs, inner, leaves, cache, returned, st, hopen,
      ⟨ids, hinner, hdecls⟩, hsplit, run, hm, legal⟩
  · exact Or.inl hit
  · refine Or.inr ⟨ids, cache, DeclsAt.length B ids 0 hdecls, ?_⟩
    -- the leaves: one, `("out", leafOf ids)`
    rw [hinner] at hsplit
    have hl : leaves.toList = [("out", leafOf ids)] :=
      splitReturnLeaves_scalar (hleaf ids).1 (hleaf ids).2 hsplit
    rw [hl] at run
    intro bools bits initial mems values v pos dom
    -- the binder walk, inverted to the prepared setup
    have leaf := bindInputsLegacy_prepare (bools := bools) (bits := bits) B ids 0
      (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
        (Sparkle.IR.ModuleName.ofDecl declName)) hdecls horacle run
    exact harness_sound_leaf (bs := bindersOf B) (ids := ids) hm legal bools bits initial mems
      values leaf v pos (leaf_translate_spec dom) (leaf_translate_order dom)

end Tools.ShippingLegacySem
