# G2 — worker B2, round 18 (branch `par/g2-legacy-18`, base `fix/cache-rollback` = `8c563a6f`)

Nothing here was built (no Lean run from a worker). To be folded into
`docs/parallel/G2-legacy.md` as §70–§75.

## 70. Item 1 — evidence for the two-binder premises (test, `run_cmd`, logs only)

For `useDbl2` and `useAdd2`: the stripped value's shape (two nested lambdas?
binder names? is the inner body a lambda?); inside `lambdaTelescope`: two
variables and the body `==` the stated leaf; the premise's THREE
`instantiateRevRange` results (written exactly as `hbody` writes them:
`(#[]).size`, `fv1`, `fv2`) equal the two declared types and the leaf; the
declared user names; `inferHWTypeFromSignal` on each declared type; the head
of the `whnf` of the leaf's inferred type. Line: `TWO-BINDER EVIDENCE for …`.

## 71. Item 2 — a leaf that uses both inputs

`add2 a b := a + b` (untagged), `useAdd2 x y := add2 x y` (test).

* `callE2`, the name lemmas of `add2` (`add2_head`, `add2_kind`,
  `add2_notCore`, `add2_glue`, `add2_notBitVecOp`, `add2_suffixes`,
  `add2_plainName`, `add2_plainName2`, `add2_implName`) — generated from
  `dbl`'s by renaming; same proof text. They are closed computations on the
  NAME (`decide` on name literals, the candidate renderings for the suffix
  tests) and on the expression's spine: not provable for a variable name, so
  there is nothing generic to state about them. What IS generic:
* `PlainCallee n` (bundle) and `plainCallee_leaf`
  (`Tools/ShippingLegacySemLeafHandled.lean`): a plain call is in the leaf
  domain when its unfoldings are. A further declaration costs: the name
  block (mechanical copy), one `PlainCallee` instance, the unfolding's
  membership.
* `add2_unfold_dom`: `LegacyDom.cert` at `kb = 0`, `kv = 2`
  (`vE = sel2 (.fvar x) (.fvar y)`), value `x + y`.
* `useAdd2_input1` / `useAdd2_input2`: the prepared setup maps each binder
  to its value (also when the two variables coincide).
* `useAdd2_output`: `MemoHit ∨ out carries (bits id1 8 + bits id2 8)`.
* Evidence line `THIRD DECLARATION`: compiles with the legacy front end;
  `unfoldDefinition? (add2 x y)` against the quoted term.

## 72. Item 3a — inventory of the fallback's arms

`translateFallback` (`Sparkle/Compiler/Elab.lean` 8750–8791) dispatches on
`fallbackKind e` (8705–8748). Status columns: **walk** = a proved statement
about the arm's successful runs in this line or the certified development;
**domain** = reachable as a `LegacyDom` / `LeafDom` derivation.
The "smallest declaration" column is a source shape, NOT compiled in this
round unless marked (test) — a guess at what reaches the arm, to be checked
with a compile probe before it is relied on. Line ranges of whole
definitions are exact (start of the `def` to the line before the next one);
ranges INSIDE `translateInstanceOrFallback` and `translateExprToWireImpl`
are approximate.

### A. The fourteen canonical kinds (certified lowerings behind `translateControlCachedWith`)

| Arm (`FallbackKind`) | Lines | Walk | Domain | Smallest declaration |
|---|---|---|---|---|
| `boolControl` (`translateBoolUncachedWith`) | 8753–8757 | certified (`fuel_contract_leaves`) | `LegacyDom.cert` (`Term.compare`, `boolBinary`, `boolNot`, `boolEq`, `mux` at Bool, `appCompare`, `appBool`, `appBool2`) | `f x y := x === y` |
| `vectorMux n` | 8758–8761 | certified | `LegacyDom.cert` (`Term.mux`) | `f c a b := Signal.mux c a b` |
| `setWidth ws wt` | 8762–8764 | certified | `LegacyDom.cert` (`Term.setw`) | `f x := x.map (BitVec.setWidth 16)` |
| `slice ws start len` | 8780–8781 | certified | `LegacyDom.cert` (`Term.slice`) | `f x := x.map (BitVec.extractLsb' 0 4 ·)` |
| `concat m n` | 8782–8783 | certified | `LegacyDom.cert` (`Term.concat`) | `f a b := a ++ b` |
| `concatLit hi k v w` | 8784–8785 | certified | `LegacyDom.cert` (`Term.concatLitHi` / `concatLitLo`) | `f a := 0#4 ++ a` |
| `zextMap ws k` | 8786–8788 | certified | `LegacyDom.cert` (`Term.zextMap`) | `f a := a.map (fun v => BitVec.append (0#4) v)` |
| `sliceF ws start len` | 8789–8790 | certified | `LegacyDom.cert` (`Term.sliceF`) | `f x := (BitVec.extractLsb' 0 4 ·) <$> x` |
| `register w v` | 8765–8768 | certified elsewhere (S4, machine route) | NOT in `LegacyDom` / `LeafDom` (sequential: the flat `RawValueAt` conclusion does not apply) | `f x := Signal.register 0 x` |
| `registerEnable w v` | 8769–8770 | as above | no | `Signal.registerWithEnable` |
| `loopRegister w v` | 8771–8772 | as above | no | `Signal.loop fun s => …register…` |
| `circuitDo w v` | 8773–8774 | machine route | no | a one-slot `circuit do` |
| `circuitDo2 w v0 v1 ret` | 8775–8777 | machine route | no | a two-slot `circuit do` |
| `memory aw dw` | 8778–8779 | certified elsewhere (S5) | no | `Signal.memory …` |

(The core, tried BEFORE the fallback — `translateCore`, 8163–8180: a bound
variable, `Signal.pure` literal, a canonical Signal binary operator — is
`LegacyDom.input` / `LegacyDom.cert` (`Term.binary`, `bitsLit`, `bitsNum`).)

### B. `other` → `translateInstanceOrFallback` (8638–8679)

| Arm | Lines | Walk | Domain | Smallest declaration |
|---|---|---|---|---|
| tagged head, ONE output (`translateInstanceUncachedWith`) | 8643–8650 | `Tools.ShippingInstanceLeaf.inst_leaf_fuel`: a `Contract` at every fuel, over the hierarchical context (`HierCtx`) | NO: no `ActionOrder` for it; output statement is hierarchical, not `RawValueAt` | `@[hardware_module] def c x := x + 1`; `f x := c x` |
| projection of a tagged MULTI-output call (`translateProjInstanceUncachedWith`) | 8654–8672 | `synthesizeMixedCertified_instanceProj_sound` (entry level) | no | `f x := (c2 x).fst` for a tagged record-valued `c2` |
| anything else → the shim `Rec.translateExprToWireCached` (7914–7950) | 8651, 8673–8679 | `arm_to_shim` (plain head); `legacyShim_returns`, `shimAt_of_uncacheable` (named / top / variable), `shimAt_of_noCache` | part of `inlineAt` at the entry flags; at the CACHEABLE flags the hit is not validated → a legacy call UNDER a certified node is uncovered | `f x y := dbl x + y` |

### C. The body `Rec.translateExprToWireImpl` (6852–7913), reached from the shim

| Arm | Lines | Walk | Domain | Smallest declaration |
|---|---|---|---|---|
| prefix: trace, call counter, limit, profile tick | 6853–6900 | `pre_plain` (application), `impl_fvar` (variable) | — | — |
| variable arm (lookup / zeta of a `let` value / `reduce`) | 6903–6955 | `impl_fvar` (three-way disjunction) | no: the targets of its recursion are read from the `Meta` local context (`RunsIn` needed) | `f x := let y := dbl x; y` (the variable is met inside the `let` handler) |
| early operator interception (Signal binary operator, `HAppend`) | after 6957 | DECLINE only (`pre_plain`, from `ImplName.binOp` / `.hAppend`) | no | `f (x : Signal d (BitVec 8)) := x + 1` when not canonical for the core |
| fourteen name-guarded inline arms (`OfNat.ofNat`, `Bool.true/false`, `OfNat.mk`, `Signal.mk` / `.val` / `BitVec.ofFin` …, `Signal.pure` / `lit`, `bundle2`, `Signal.map`, `ite` / `dite`, `Decidable.rec/casesOn`, `Prod.rec/casesOn`, `Seq.seq`, `Functor.map`) | within 6957–7900 | DECLINE only (`pre_plain`, from `ImplName`) | no | `f x := if c then x else 0` (Lean `ite`), `f x := x.map (· + 1)` |
| the `whnf` branch (no mapped variable, or a beta-redex head) | — | none: the expression is replaced by an oracle's result | no | any call with no mapped variable |
| lambda / `let` / other non-application shapes after the test | — | none | no | `f x := let y := x + x; y` |
| → `Rec.translateExprToWireApp` (6726–6842): the handler chain | | `chain_plain` (the chain on a plain name) | | |
| `handleErrorPatterns` | 5629–5646 | `handleErrorPatterns_frame` (leaves the state) | — | — |
| `handleTupleProjections` | 5647–5761 | DECLINE (`handleTupleProjections_none`) | no | `f x := (pair x).1` |
| `handleApplicative` | 5762–5784 | DECLINE (`handleApplicative_none`) | no | `f a b := g <$> a <*> b` |
| `handleBitVecOps` | 5807–5896 | DECLINE (`handleBitVecOps_none`) | no | `f x := x.map (· >>> 1)` |
| `handleRegister` | 5897–5931 | DECLINE (`handleRegister_none`) | no | a non-canonical `Signal.register` |
| `handleMux` | 5932–5971 | DECLINE (`handleMux_none`) | no | a non-canonical `Signal.mux` / `lutMuxTree` |
| `handleMemory` | 5972–6046 | DECLINE (`handleMemory_none`) | no | `Signal.memoryComboRead` |
| `handleLoop` | 6047–6161 | DECLINE (`handleLoop_none`) | no | a non-canonical `Signal.loop` |
| `handleCircuitMonad` | 6162–6253 | DECLINE (`handleCircuitMonad_none`) | no | a `circuit do` outside the machine shape |
| `handleDefinitionUnfold`: the inline attempt `tryInlineUnfold` | 6267–6322 (attempt), 6323–6725 (handler) | `tryInlineUnfold_returns`, `unfoldSpec_plain`, `plain_call_reaches` | **`LeafDom.inlineAt` / `handled`** (entry flags), `LegacyDom.inline` under `ReachesUnfold` | `useDbl x := dbl x` (test), `useAdd2 x y := add2 x y` (test) |
| `handleDefinitionUnfold`: the attempt returned no wire → sub-module synthesis and instance | 6323–6725 | statement only (`UnfoldOutcome`'s second disjunct; excluded by the premise `NoSubModule`) | no | an untagged call whose unfolding fails to translate |

**Reading.** Positive (accepting) walks exist for: the canonical kinds and
the core (certified), the tagged single-output instance (certified,
hierarchical), the inline attempt, the variable arm. Every `handle*_none`
lemma is a DECLINE walk on a plain name — the path to the inline attempt,
already consumed by `plain_call_reaches`. No accepting walk exists for any
`handle*` handler.

## 73. Item 3b — the constructor added: `LeafDom.handled`

The request was one more constructor for the most common uncovered arm with
an existing walk. By §72 there is NO such arm: the only accepting walks not
yet in the domain are the tagged instance (needs an order statement and a
hierarchical conclusion) and `impl_fvar` (needs the run's context). Adding a
constructor for either would be a hypothesis in disguise.

What was added instead is the constructor that makes "handlers as cases" a
type (`Tools/ShippingLegacySemLeaf.lean`, EDITED):

* `HandlerCase ctx inputs hint named e v subs` — two implications: `spec`
  (sub-expressions' `ActionSpec` at fuel `f` ⟹ the node's at `f + 1`) and
  `order` (those and the sub-expressions' `ActionOrder` ⟹ the node's).
* `LeafDom.handled subs : HandlerCase … e v subs → (∀ e' v', subs e' v' →
  LeafDom … e' v') → LeafDom … e v`.
* `leaf_fuel_spec`, `leaf_fuel_order`: one new case each, using the two
  implications as they are. Statements unchanged; `leaf_output`, the entry
  theorems and the tests are unaffected.

And in `Tools/ShippingLegacySemLeafHandled.lean` (new): `handlerCase_inline`
(the inline arm is a proved `HandlerCase`), `LeafDom.inline_handled`
(`inlineAt` through `handled`), `PlainCallee`, `plainCallee_leaf`.

**What `LeafDom` now claims differently**: nothing was removed; the domain
grew by expressions for which a `HandlerCase` is PROVED. The constructor has
no premise about the compiler other than the two implications, which are
exactly what the consumers need — it cannot make the theorems unsound, and it
proves nothing by itself: a new arm is covered when its `HandlerCase` is
proved.

## 74. Next for G2b, in order of expected yield

1. The tagged single-output instance as a `HandlerCase`: `inst_leaf_fuel`
   gives `spec`; `order` needs an `ActionOrder` proof of
   `translateInstanceUncachedWith` (new, the size of `inst_leaf_contract`'s
   frame part), and the entry conclusion over `HierCtx` instead of the flat
   `RawValueAt`.
2. `handleBitVecOps` / `handleApplicative` ACCEPTING walks (`x.map (· >>> k)`,
   `g <$> a <*> b`): the most common non-canonical leaves in the corpus are
   maps; each is a new handler walk (program-shape work as in rounds 5–9).
3. The validated shim hit (compiler change, proposal in
   `docs/parallel/G2-legacy.md`): makes a legacy call under a certified node
   (`dbl x + y`) a `LegacyDom` member.

## 75. Spots most likely not to elaborate, in order of risk

1. Test: `add2_unfold_dom` (`Meaning.input rfl …` on `sel2 … 0` / `… (0+1)`,
   the `show` in `hval`, the `rw [setWidth_eq, setWidth_eq]`), `add2_kind` /
   `add2_notCore` by `rfl` on a two-argument spine, `useAdd2_output`'s final
   `plainCallee_leaf` application.
2. Test: the evidence `run_cmd` (compiled code: the nested `.lam` pattern,
   the three-line Boolean, the `for … try … catch`).
3. `Tools/ShippingLegacySemLeaf.lean` (EDITED, built before): the new
   constructor and the two `handled` cases (`hc.spec fuel we mems initial …`
   needs the theorem's `we mems initial` by name; the `induction` binder
   lists). A failure here breaks everything downstream of `…Leaf`.
4. `Tools/ShippingLegacySemLeafHandled.lean`: `handlerCase_inline` (the
   `inlineAt` cases' text under `where spec := … order := …`),
   `plainCallee_leaf` (`rfl` for the flag fact).
