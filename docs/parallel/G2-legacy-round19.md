# G2 — worker B2, round 19 (branch `par/g2-legacy-19`, base `fix/cache-rollback` = `2b8cfae8`)

Nothing here was built (no Lean run from a worker). To be folded into
`docs/parallel/G2-legacy.md` as §76–§80.

**This round delivers item 1 (the census, as a test) and item 3 (the prefix
and the exact text of the candidate arm). Item 2 — an accepting walk as a
`HandlerCase` and a fourth declaration — is NOT done**, for two reasons
stated in §77: the census is compiled evidence and its counts exist only
after a build (a worker cannot run it), and the reading of the candidate arm
shows that its `HandlerCase` needs three pieces that do not exist.

## 76. Item 1 — the census (`Tests/Compiler/LegacyArmCensusTest.lean`, new)

No iterator over real declarations exists in the Lean tests (the corpus
measurement is a script). The test enumerates the environment itself: the
definitions of the imported `IP` / `Examples` / `Tests` modules whose result
type is syntactically a `Signal`, in name order, at most `cap = 400`.
Imports: `Sparkle` and eight `IP` modules that other tests already import
(`IP.Net.IPv4`, `.TCP`, `.Ethernet`, `.HTTP`, `IP.BitNet.SignalHelpers`,
`IP.Crypto.SHA256`, `IP.Video.H264.Quant`, `IP.RV32.SoC`).

Per declaration, from the compiler's own pure functions:

* ROUTE under the shipping configuration: the entry's gates on the entry's
  constant (`entryConst true false [] ci …`; `certifiedShape?`,
  `mixedCertifiedShape?`, `machineShape?`) → `certified` / `mixed` /
  `machine` / `legacy`;
* for `legacy`: the top leaf (the body after `openRecordInputs`,
  `stripMemoizeWrappers`, `lambdaTelescope`), its head, its `fallbackKind`,
  and for a `Signal.map` / `Functor.map` head the head of the mapped
  function's body.

Five log lines, all starting `LEGACY ARM CENSUS`. **Counts: none yet** — the
lines of the next build are the result.

What it does not measure: which handler accepts at run time (that needs
instrumenting the translator, a compiler file); sub-expressions of the leaf;
structure- / product-valued declarations; declarations outside the imports.
The test needs a `lakefile.lean` entry if tests are not globbed, and it may
be slow (the entry's inliner runs on up to 400 declarations; `cap` is one
constant). `maxHeartbeats 0`: a heartbeat exception is not catchable, and
the block must not throw.

## 77. Item 2 — not done, and why

1. **The choice depends on counts that do not exist yet.** Walking an arm
   before the census is the guess this round was meant to replace.
2. **Reading the expected candidate (the `Signal.map` arm) shows three
   missing pieces** — independent of the census:
   * *Semantics of the emitted operator.* The simplest sub-arm emits
     `.op op [.ref wireS]` with `op ∈ {.not, .neg}` at the vector's width.
     The certified development has the typing and evaluation facts for
     `.op .not` at width ONE only (`Tools/ShippingUnifiedRecursion.lean`
     2028–2034, the Bool negation). A `HandlerCase.spec` needs `evalExpr` /
     `TypedExpr` for the vector operator, the invariant's preservation over
     `makeWire` + `emitAssign`, and a SOURCE meaning for the mapped
     expression: `Meaning` (and `Term`) have no constructor for a vector
     complement or negation.
   * *Order.* `HandlerCase.order` needs the `ActionOrder` of the same
     emission (the certified nodes prove it from the children's contract,
     protection and order).
   * *The hint of the sub-translation.* `HandlerCase.subs` gives the
     sub-expressions at the NODE's hint and name flag; this arm translates
     its argument at `("s", isTopLevel := false, isNamed := false)` — the
     cacheable flags. So the argument cannot come through `subs`; it has to
     come with a `Contract` at every flag (`LegacyDom`, e.g. an input
     variable). That is expressible today (the case's proof uses
     `legacy_fuel_contract` for the argument), but it restricts the first
     instance to arguments in `LegacyDom`.
3. **A caution about the arm the request expected.** `Signal.map` is NOT
   handled by `handleApplicative` or `handleBitVecOps`. `handleApplicative`
   accepts only `Signal.ap` (line 5763). `handleBitVecOps` is dispatched on
   BitVec-level names (`BitVec.extractLsb'`, shifts, `isPrimitive`). A
   Signal-typed `Signal.map f s` is taken by a NAME-GUARDED INLINE ARM of the
   body itself (line 7102), before `translateExprToWireApp` and its handler
   chain are reached. And three map shapes never reach the body at all:
   `fallbackKind` is `setWidth` / `slice` / `zextMap` for
   `Signal.map (BitVec.setWidth w)`, `(BitVec.extractLsb' s l ·)`,
   `(fun v => 0#k ++ v)` — certified, already in `LegacyDom.cert`. The census
   line "map leaves, by the head of the mapped function's body" separates
   these.

## 78. Item 3 — the path to the `Signal.map` arm, and its text

For `e = Signal.map f s` (five-argument spine, head constant
`Sparkle.Core.Signal.Signal.map`), `fallbackKind e = .other`, translated at
the entry flags (`isNamed = true`).

**Before the body** (built lemmas apply unchanged, with `Signal.map` as the
head name):

| Stage | Lines | Lemma | Premise |
|---|---|---|---|
| core declines | 8163–8180 | `step_run_fallback` from a `NotCore e` (closed computation) | — |
| fallback → instance arm | 8750–8791 | `fallback_eq_arm` | `fallbackKind e = .other` (closed) |
| instance arm → shim | 8638–8679 | `arm_to_shim` | `PlainHead ``Signal.map` (environment) |
| shim → body | 7914–7950 | `shimAt_of_uncacheable` | `isNamed = true` |

**The body's prefix** (`Rec.translateExprToWireImpl`, 6852–; the steps of the
built `pre_plain`, `Tools/ShippingLegacySemPre.lean`):

| Step | Lines | In `pre_plain` | For `Signal.map` |
|---|---|---|---|
| trace, call counter, limit, tick | 6853–6900 | `k0 … k4` | same |
| not a variable; head constant | 6903, 6965 | `rw [hfn]` | same |
| operator interception (`signalBinOpOf`, `HAppend`) | 6965–7010 | `hi.binOp`, `hi.hAppend` | same facts for `Signal.map` (closed name tests) |
| `OfNat.ofNat` | 7012 | `hi.ofNat` | decline (closed) |
| `Bool.true` / `Bool.false` | 7022, 7026 | `hi.boolTrue`, `hi.boolFalse` | decline |
| `OfNat.mk` | 7032 | `hi.ofNatMk` | decline |
| `Signal.mk` / `.val` / `BitVec.ofFin` / … and three name SUFFIX tests | 7037 | `hi.sigMk … hi.sufToNat` | decline; the suffix tests through the candidate renderings (`endsWith_false_of`) |
| `Signal.pure` / `Signal.lit` | 7047 | `hi.sigPure`, `hi.sigLit` | decline |
| `bundle2` | 7092 | `hi.bundle2` | decline |
| **`Signal.map && args.size >= 2`** | **7102** | `hi.sigMap` (decline) | **ACCEPT: the walk leaves `pre_plain` here** |

`ImplName` cannot be reused as it is (its field `sigMap` says the name is NOT
`Signal.map`); the facts above it in the structure are the ones needed. No
handler of `translateExprToWireApp`'s chain is passed: the arm is inside the
body, before the chain.

**Inside the arm**, for `f = fun p => op p` with `op` a unary primitive
(`getOperator opName = some .not` or `.neg`):

| Step | Lines | Outcome |
|---|---|---|
| `let f := args[args.size-2]!`, `let s := args[args.size-1]!`, `let fFn := f.getAppFn` | 7103–7105 | — |
| `if fFn.isConstOf ``Prod.fst` | 7106 | decline (`f` is a lambda) |
| `if fFn.isConstOf ``Prod.snd` | 7124 | decline |
| `if let .lam _ _ body _ := f` | 7137 | taken |
| `let bodyFn := body.getAppFn`; `if let .const opName _ := bodyFn` | 7138–7139 | taken |
| `opName == ``BitVec.extractLsb'` | 7141 | decline |
| `opName == ``BitVec.zeroExtend || … setWidth` | 7152 | decline |
| `opName == ``BitVec.signExtend` | 7160 | decline |
| `opName == ``BitVec.sshiftRight` | 7183 | decline |
| `if let some op := getOperator opName` / `if isUnary` | 7203–7205 | **taken** |

Each declining `if` there has no `else` and is followed by more code, and
some of their bodies return only under an inner `if`: every one is a join
point, nested.

**The accepting text** (7206–7211, verbatim):

```
7206   let wireS ← translateExprToWire s "s" (isTopLevel := false)
7207   let exprType ← cachedInferType e
7208   let hwType ← inferHWTypeFromSignal exprType
7209   let resWire ← CompilerM.makeWire hint hwType (named := isNamed)
7210   CompilerM.emitAssign resWire (.op op [.ref wireS])
7211   return resWire
```

Oracles in it: `cachedInferType e` (1123–: reads and writes
`sparkleTypeCache`, an `IO.Ref`; lifted, leaves the builder state) and
`inferHWTypeFromSignal exprType` — on a type the run does not fix in
`Returns` form (the result of `cachedInferType` is any `Expr` some run
returned): the premise has to be "for every type the type oracle returns for
`e`, the hardware-type oracle returns `.bitVector n`", like `SignalTyped` +
`InfersHW` composed.

**The statement the walk should prove** (decomposed, so that the arm's tail
need not be quoted): from
`Returns (Rec.translateExprToWireImpl rec e hint top named) ctx s w t` and
the closed facts above,

```
∃ wireS s1 hw,
  Returns (rec sExpr "s" false false) ctx s wireS s1 ∧
  (∃ exprType s', Returns (inferHWTypeFromSignal exprType) ctx s1 hw s') ∧
  w = (CircuitM.makeWire hint hw named s1').1 ∧
  t = (CircuitM.emitAssign w (.op op [.ref wireS]) (CircuitM.makeWire hint hw named s1').2).2
```

(with `s1' = s1` once the oracle's frame is a premise). That lemma is
program-shape work of the size of `pre_plain`; the `HandlerCase` on top of
it needs the three pieces of §77.

## 79. What the next round should start from

1. The five `LEGACY ARM CENSUS` lines.
2. If the commonest uncovered head is a map with a unary primitive body:
   the walk of §78 (first build will show the join-point nest), then the IR
   facts for `.op .not` / `.neg` at width `n`, a `Meaning` for the mapped
   expression (a new constructor of `Meaning`/`Term` is a SHARED change — the
   alternative that stays inside this line is a `HandlerCase` whose `spec`
   states the outcome directly at the source value `~~~x`, with the
   invariant's record clause discharged because a named leaf is not
   recorded; to be checked against `Outcome`'s definition).
3. If it is a user definition (an inline call): it is ALREADY covered
   (`plainCallee_leaf`); the work is then per declaration, not a new arm.
4. If it is `<let>` / `<lambda>` / a `match`: the body's non-application
   shapes (§72 C), for which there is no walk at all.

## 80. Risk (unverified)

Only compiled code this round: `Tests/Compiler/LegacyArmCensusTest.lean`.
Spots: `env.constants.fold` with the three-argument function;
`env.header.moduleNames[idx.toNat]?` (the form `Elab.lean` 3307 uses);
`Array.qsort` with an explicit comparison; the `let mut` updates inside
`try` inside `for`; the fifteen-way `match` on `FallbackKind`. Runtime: the
entry's inliner over up to 400 declarations of large IP modules — if it is
too slow, lower `cap`.
