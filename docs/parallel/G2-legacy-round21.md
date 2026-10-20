# G2 — worker B2, round 21 (branch `par/g2-legacy-21`, base `fix/cache-rollback` = `4a75aaa3`)

Nothing here was built (no Lean run from a worker). To be folded into
`docs/parallel/G2-legacy.md` as §86–§92.

## 86. The round-20 result (integrator's build, recorded)

The shipping entry on the 128 legacy-route candidates: RETURNED 90, THREW 38
(all 22 `Signal.register` heads throw). Of the 90: every one has exactly one
domain binder; 45 have a `<lambda>` head (a beta-redex) whose `headBeta` is a
structure projection — the structures' own field projection functions, on
`k` scalar Signal binders + the domain (`k` = 1, 2, 3, 4, 6, 9); 39 are
`Signal.fst` chains over ONE structured Signal + the domain
(`RV32.SoC.SoCState.*`); 3 `Signal.mux`, 1 `Signal.beq`, 1 `<let>`, 1 user
definition. So `list_entry_output` (round 17) covered 0 of 90.

## 87. Item 1 — the domain-binder skip (`Tools/ShippingLegacySemBinderListD.lean`, new)

Read: what the walk does on `{dom : DomainConfig}` (`Elab.lean` 2110–2146).
The `isSignalBinderType` result is NOT consulted when `symbolicMode = false`
(line 2127 tests `symbolicMode && isSignalArg`). The skip is decided by the
`try` at 2135–2138: `inferHWTypeFromSignal binderType` throws (for
`DomainConfig`: `inferHWType`'s structure arm finds a `Nat` field without a
hardware type → `none` → `throwError "Cannot infer hardware type …"`), the
handler yields `false`, line 2144 continues the walk.

The premise, exactly: **`InfersNothing T`** — the hardware-type oracle has no
returning run on `T`. Then a returning `try` went through the handler
(`returns_tryCatch`; `Throws` is not needed).

* `TypeOk k T`: `.domain ↦ InfersNothing T`; `.bool ↦ InfersHW T .bit ∧
  InfersNoCatch T`; `.bits n ↦ InfersHW T (.bitVector n) ∧ InfersNoCatch T`.
* `DeclsAtD mctx xs i bs ids` — as `DeclsAt`, with `TypeOk q.2 d0.type` at
  each declaration in place of a fixed declared type: in a real telescope the
  type of a later binder mentions the domain VARIABLE.
* `bindInputsLegacy_step_skip`, `bindInputsLegacy_prepareD` (three kinds; the
  `.domain` step of `prepare` is the identity, as in the certified walk).
* `Tools/ShippingLegacySemEntryListD.lean` (new): `ListScopeD`,
  `list_entry_outputD` (`list_entry_output` is kept), `fv2p`, `fv3`,
  `telescopeIn_of_lam3`.

## 88. Item 2 — the projection class (`Tools/ShippingLegacySemBeta.lean`, new)

Read: `openRecordInputs` (1990–2051) on a projection function
`fun dom self => self.i`: the record parameter `self` is opened into its
Signal fields `x₁ … xₖ` (2025–2046), the result is
`fun dom x₁ … xₖ => (fun dom self => self.i) dom ⟨dom, x₁, …, xₖ⟩`
(`inner := mkAppN body params`, the substitution, `mkLambdaFVars`). So after
the telescope the leaf is an APPLICATION whose head is a lambda.

The translator on it — table with line numbers in the file's header: the
core declines; `fallbackKind = other`; the instance arm sees a non-constant
head and goes to the shim without reading the environment; `isNamed = true`
→ the body; both name-guarded blocks are skipped (the head is not a
constant); `isBetaRedex` is true, so the body REPLACES the expression by
`withTransparency .reducible (whnf e)` (7606–7609); the result is matched
(7613–): for a variable, the arm at 7738–7744 — `lookupVar`, a hit returns
the wire, a miss throws.

* `WhnfIsVar e x` — the oracle premise: every successful reducible `whnf` of
  `e` returns `.fvar x`.
* `impl_betaRedex`, `betaRedex_step`: the run returns the wire bound for `x`
  and leaves the builder state.
* `handlerCase_wire`: a `HandlerCase` with no sub-expression, for
  `inputs x = some v` — frame, outcome and order are the input binder's
  proofs (`input_contract`, `input_order`) with the run fact above.
* `leafDom_betaWire`.

**What selects the first disjunct (the hit).** Not an oracle and not a
premise about the `Meta` context: this variable arm is the POST-`whnf` one
(7738–7744), which has only two outcomes — hit or throw — and does not read
the local context (the three-way `impl_fvar` is the PRE-`whnf` arm at 6903).
That the hit's wire is the input's port follows from `inputs x = some v`
through the invariant (`h.inputs.lookup`), and `inputs x = some v` is proved
from `prepare` per declaration (`sha256Out_done_input`:
`inputValues_bool (if_pos rfl)`).

## 89. The declaration: `SHA256Out_done_output` (test)

`Sparkle.IP.Crypto.SHA256.SHA256Out.done` in the SHIPPING configuration
(`certifiedFrontEnd = true`, the three gates declining — the first of this
line's instances that is not a legacy-front-end test declaration). Binders
`dom` (`.domain`), `hash` (`.bits 256`), `done` (`.bool`). Conclusion:
`MemoHit ∨ out carries the Bool input bound for done`
(`RawValueAt (Value.bool (bools id3)).kind.width … (Value.bool (bools id3)).toNat`).

The instance test names the constant by a name LITERAL and does not import
the SHA256 module (the statement is about any `dv` satisfying the premises).
The link to the real constant is the evidence line `PROJECTION EVIDENCE` in
`Tests/Compiler/LegacyArmCensusTest.lean` (which imports it): the gates
decline on the entry's constant; three nested lambdas named `dom`, `hash`,
`done`; the three declared types and the leaf equal the premise's
`instantiateRevRange` results; the leaf is an application with a lambda head
of kind `other`; its reducible `whnf` is the third variable; the type oracle
on the three declared types (expected `THREW | bitVector 256 | bit`); the
Signal head of the leaf's type.

## 90. Premises of `SHA256Out_done_output`, classified

| Premise | Class |
|---|---|
| `old`, `mixed`, `hmach` | reflection of the environment (closed computations on the constant) |
| `htel : LamTelescopeN` | Meta-library fact |
| `hbody` | reflection (the value's shape) through `openRecordInputs`, the `partial` `stripMemoizeWrappers`, the opaque `instantiateRevRange` |
| `hshape`, `hkind` | closed computations on the leaf |
| `hdom : InfersNothing domTy` | binder-type oracle (no returning run) |
| `hhash`, `hdone` | binder-type oracle (returning and failing runs), for every domain variable |
| `hwhnf` | oracle: the leaf's reducible `whnf` |
| `hres` | result-type oracle |
| `hr` | the run |

No `hmap` / `hplain` / `hnosub` / `hunfE`: this leaf does not go through the
inline arm. `MemoHit` stays.

## 91. Coverage after this round, against the census

Of the 90 RETURNED declarations: the 45 projections have the SHAPE this
round's theorems cover (`k` scalar Signal binders + one domain binder, a
beta-redex leaf reducing to a field's variable) — proved for the instance
`k = 2`; another arity needs `telescopeIn_of_lamN` for `N = k + 1` (the
three-binder proof is mechanical; a generic one needs a lemma on
`(ids.map .fvar).toArray` indexing) and its `…_input` fact. Width-one
`BitVec` fields, if any, are outside (round 17). The 39 `Signal.fst` chains
need the packed-product value model; the remaining 6 are other arms.

## 92. Spots most likely not to elaborate, in order of risk

1. `Tools/ShippingLegacySemBeta.lean`, `impl_betaRedex`: after
   `rw [hfnL] at k4`, `Returns.bind k4` must see through two `match`es on the
   lambda head (join points included) to `getCompilerState >>= …`; then
   `returns_ite_pos k8 (betaTest _)` (the flag `e.isApp && lam.isLambda`
   evaluating to `true` inside the unifier), and `Returns.bind k9` reducing
   the seven-way `match` on `.fvar x`.
2. Same file, `notCore_of_lamHead.core` (four alternatives around
   `simp only [translateCore, hfnL]`) and `arm_to_shim_lam`.
3. Same file, `handlerCase_wire`: `rw [ht, ← hz]` then the `Outcome` tuple of
   `input_contract`.
4. `Tools/ShippingLegacySemBinderListD.lean`: `TypeOk` as a two-argument
   `match` definition and its unfolding after `cases kind`; the three
   `exact ih …` steps.
5. `Tools/ShippingLegacySemEntryListD.lean`, `telescopeIn_of_lam3`: the
   five-way `rcases ids`; the index facts on `fv3`.
6. Test: `sha256Out_done_input` (`inputValues_bool (if_pos rfl)` through
   three `extend`s), the list destructuring, `rw [he] at hw` under the
   definition `WhnfIsVar`.
7. Census test: `hwOf` and the evidence `run_cmd` (compiled code).
