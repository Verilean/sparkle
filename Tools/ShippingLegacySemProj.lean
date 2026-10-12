import Tools.ShippingLegacySemTelescopeLams
import Tools.ShippingLegacySemInputAt
import Tools.ShippingLegacySemBeta

/-! # The projection class of the legacy route, as ONE theorem

The census (`Tests/Compiler/LegacyArmCensusTest.lean`): of the 90
Signal-valued definitions of the examined IP modules on which the shipping
entry RETURNS through the legacy arm, 45 are structure projection functions.
After `openRecordInputs` each of them is

```
fun dom x₁ … xₖ => (fun dom self => self.i) dom ⟨dom, x₁, …, xₖ⟩
```

`k` scalar Signal binders and one domain binder (`k ∈ {1, 2, 3, 4, 6, 9}`),
the leaf a lambda-headed application whose reducible `whnf` is one of the
input variables. Round 21 proved ONE of them by hand (`SHA256Out.done`,
`k = 2`). Here: one statement over the declaration, the binder list and the
field's position.

**Proved here**

* `list_entry_outputDN` — `list_entry_outputD` with (1) the distinctness of
  the variables in its conclusion (from `ListScopeDN`) and (2) its leaf
  premise asked only for variable lists of the binders' length. Its proof is
  `list_entry_outputD`'s.
* `proj_entry_output` — THE PROJECTION CLASS: for a declaration whose
  stripped value is `lams sp b` over binders `bs` (any of the three kinds)
  with a non-domain binder `(nm, k)` at position `i`, whose leaf is a
  lambda-headed application of fallback kind `other` with reducible `whnf`
  the variable at position `i`: a successful run of the SHIPPING entry
  (certified front end on, the three gates declining) is a memo hit, or the
  module's `out` carries the value of the input bound for that binder
  (`RawValueAt (kindValue bools bits k x).kind.width bs m … (kindValue bools
  bits k x).toNat`, `x` the variable at position `i`).

**Premises of `proj_entry_output`, classified**

| Premise | Class |
|---|---|
| `old`, `mixed`, `hmach` | reflection of the environment (closed computations on the constant) |
| `htel : LamTelescopeND` | Meta-library fact (`LamTelescopeN` + distinct variables) |
| `hbody`: `stripMemoizeWrappers body0 = lams sp b`, `b.isLambda = false` | reflection (the value's shape) through `openRecordInputs` and the `partial` `stripMemoizeWrappers` |
| `hbody`: `TypesOkFrom sp bs #[]` | binder-type oracle on each declared type, for every choice of the earlier variables (`InfersNothing` for a domain binder; `InfersHW` + `InfersNoCatch` otherwise), and the binder names |
| `hbody`: the leaf equation | reflection through the opaque `instantiateRevRange` |
| `hfield`, `hk`, `hpos` | closed facts of the binder list (the field's position, not a domain binder, positive width) |
| `hshape`, `hkind` | closed computations on the leaf |
| `hwhnf` | oracle: the leaf's reducible `whnf` |
| `hres` | result-type oracle |
| `hr` | the run |

Not premises: that the variable is found by the lookup (from the invariant),
and the input fact (`prepare_inputValue`, from `ids.Nodup`).

**Width one.** For a `Signal dom (BitVec 1)` binder the real type oracle
returns `.bit` (round 17), so `TypeOk (.bits 1)` cannot be met; such a field
is outside (the statement stays true). `TypeOk .bool` CAN be met on it — the
theorem then speaks of a Bool value at a `.bit` port, which is not the
source's `BitVec 1` value: the census reports such declarations as
non-fitting. -/
namespace Tools.ShippingLegacySem
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingEntrySoundness
open Tools.ShippingUnifiedMeaning (Value)

/-- **`list_entry_outputD` with distinct variables**, the leaf premise asked
at the binders' length only. -/
theorem list_entry_outputDN {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {cfe : Bool}
    (old : cfe = true → certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : cfe = true → mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : cfe = true → ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (ListScopeDN bs leafOf))
    (hleaf : ∀ ids : List FVarId, ids.length = bs.length →
      (leafOf ids).isLambda = false ∧ SignalTyped (leafOf ids))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false cfe (.defnInfo dv) isInst) (m, d)) :
    MemoHit declName m d ∨
    ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.length = bs.length ∧ ids.Nodup ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          declName.toString) →
      ∀ v : Value, 0 < v.kind.width →
      LeafDom (setupOf declName bs ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName bs ids cache bools bits).bools
          (setupOf declName bs ids cache bools bits).bits)
        "out" true (leafOf ids) v →
      Tools.ShippingMixedEntrySoundness.RawValueAt v.kind.width bs m initial mems v.toNat := by
  rcases legacy_entry_walk_in old mixed hmach htele hr with hit |
    ⟨body0, mctx, xs, inner, leaves, cache, returned, st, hopen,
      ⟨ids, hinner, hdecls, hnd⟩, hsplit, run, hm, legal⟩
  · exact Or.inl hit
  · have hlen : ids.length = bs.length := DeclsAtD.length bs ids 0 hdecls
    refine Or.inr ⟨ids, cache, hlen, hnd, ?_⟩
    rw [hinner] at hsplit
    have hl : leaves.toList = [("out", leafOf ids)] :=
      splitReturnLeaves_scalar (hleaf ids hlen).1 (hleaf ids hlen).2 hsplit
    rw [hl] at run
    intro bools bits initial mems values v pos dom
    have leaf := bindInputsLegacy_prepareD (bools := bools) (bits := bits) bs ids 0
      (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
        declName.toString) hdecls run
    exact harness_sound_leaf (bs := bs) (ids := ids) hm legal bools bits initial mems
      values leaf v pos (leaf_translate_spec dom) (leaf_translate_order dom)

/-- **The projection class**: the output of a legacy-route declaration whose
leaf is a lambda-headed application reducing to the input variable of the
binder at position `i`, in the shipping configuration. -/
theorem proj_entry_output {logProf : String → IO Unit} {declName : Name}
    {dv : DefinitionVal} {isInst : Lean.Expr → Bool}
    {bs : List (Name × MixedGateBinder)} {leafOf : List FVarId → Lean.Expr}
    {m : Sparkle.IR.AST.Module} {d : Design} {i : Nat} {nm : Name} {k : MixedGateBinder}
    (old : certifiedShape? false [] (.defnInfo dv) = none)
    (mixed : mixedCertifiedShape? false [] (.defnInfo dv) isInst = none)
    (hmach : ∀ projs, machineShape? false [] (.defnInfo dv) projs = none)
    (htel : LamTelescopeND)
    (hbody : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      ∃ (sp : List (Name × Lean.Expr × BinderInfo)) (b : Lean.Expr),
        stripMemoizeWrappers body0 = lams sp b ∧
        b.isLambda = false ∧
        TypesOkFrom sp bs #[] ∧
        ∀ ids : List FVarId, ids.length = bs.length →
          b.instantiateRevRange 0 (ids.map Lean.Expr.fvar).toArray.size
            (ids.map Lean.Expr.fvar).toArray = leafOf ids)
    (hfield : AtIdx bs i (nm, k)) (hk : k ≠ MixedGateBinder.domain)
    (hpos : 0 < kindWidth k)
    (hshape : ∀ ids : List FVarId, ids.length = bs.length →
      ∃ (f a : Lean.Expr) (n : Name) (ty b : Lean.Expr) (bi : BinderInfo),
        leafOf ids = Lean.Expr.app f a ∧
        (Lean.Expr.app f a).getAppFn = Lean.Expr.lam n ty b bi)
    (hkind : ∀ ids : List FVarId, ids.length = bs.length →
      fallbackKind (leafOf ids) = .other)
    (hwhnf : ∀ (ids : List FVarId) (x : FVarId), ids.length = bs.length → AtIdx ids i x →
      WhnfIsVar (leafOf ids) x)
    (hres : ∀ ids : List FVarId, ids.length = bs.length → SignalTyped (leafOf ids))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named)
      logProf declName [] false true (.defnInfo dv) isInst) (m, d)) :
    MemoHit declName m d ∨
    ∃ (ids : List FVarId) (x : FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.length = bs.length ∧ ids.Nodup ∧ AtIdx ids i x ∧
      ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
        (initial : Env) (mems : MEnv),
      Tools.ShippingMixedEntrySoundness.Admissible bools bits initial (bs.zip ids)
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          declName.toString) →
      Tools.ShippingMixedEntrySoundness.RawValueAt (kindValue bools bits k x).kind.width bs m
        initial mems (kindValue bools bits k x).toNat := by
  have htele : ∀ body0, MReturns (openRecordInputs dv.value) body0 →
      TelescopeIn (stripMemoizeWrappers body0) (ListScopeDN bs leafOf) := by
    intro body0 hopen
    obtain ⟨sp, b, hb, hl, hT, hi⟩ := hbody body0 hopen
    exact telescopeIn_of_lamsN htel hb hl hT hi
  have hleaf : ∀ ids : List FVarId, ids.length = bs.length →
      (leafOf ids).isLambda = false ∧ SignalTyped (leafOf ids) := by
    intro ids hlen
    obtain ⟨f, a, n, ty, b, bi, he, _⟩ := hshape ids hlen
    refine ⟨?_, hres ids hlen⟩
    rw [he]
    first | done | rfl
  rcases list_entry_outputDN (cfe := true) (bs := bs) (leafOf := leafOf)
      (fun _ => old) (fun _ => mixed) (fun _ => hmach) htele hleaf hr with
    hit | ⟨ids, cache, hlen, hnd, H⟩
  · exact Or.inl hit
  · obtain ⟨x, hx⟩ := AtIdx.transfer bs ids i (nm, k) hlen hfield
    refine Or.inr ⟨ids, x, cache, hlen, hnd, hx, ?_⟩
    intro bools bits initial mems values
    obtain ⟨f, a, n, ty, b, bi, he, hfnL⟩ := hshape ids hlen
    have hk' := hkind ids hlen
    have hw := hwhnf ids x hlen hx
    rw [he] at hk'
    rw [he] at hw
    have hin : Tools.ShippingUnifiedMeaning.inputValues
        (setupOf declName bs ids cache bools bits).bools
        (setupOf declName bs ids cache bools bits).bits x =
        some (kindValue bools bits k x) :=
      prepare_inputValue (bools := bools) (bits := bits) bs ids i
        (Tools.ShippingMixedEntrySoundness.start (entryCompilerState false cache)
          declName.toString) nm k x hnd hfield hx hk
    have dom : LeafDom (setupOf declName bs ids cache bools bits).context
        (Tools.ShippingUnifiedMeaning.inputValues
          (setupOf declName bs ids cache bools bits).bools
          (setupOf declName bs ids cache bools bits).bits)
        "out" true (leafOf ids) (kindValue bools bits k x) := by
      rw [he]
      exact leafDom_betaWire hfnL hk' hw hin
    have pos : 0 < (kindValue bools bits k x).kind.width := by
      rw [kindValue_width]
      exact hpos
    exact H bools bits initial mems values (kindValue bools bits k x) pos dom

end Tools.ShippingLegacySem
