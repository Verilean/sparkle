# Reader invariants of the call-kind agreement: what is now a theorem (round 4)

Worker B, branch `par/b-5` (base poc `6a20c9a7`). **Nothing here was built
or run by the author: every proof below is UNVERIFIED until the integrator
builds it.** Continues `docs/parallel/B-callkinds.md` §7 (the decomposition
R1–R4 / P1–P5 / T1–T2 of proposition A, "the real reader's call kinds are
the child's"). Line numbers: `Sparkle/Compiler/Elab.lean` at `6a20c9a7`.

Files: `Tools/ShippingInstSignature.lean` (P1),
`Tools/ShippingReaderResultKind.lean` (P2),
`Tools/ShippingMachineShapeUnfold.lean` (P4 + compositions),
`Tests/Compiler/ReaderInvariantsTest.lean` (throwing axiom audit, one log
line `READER INVARIANTS: 16 theorems … standard axioms only`).

## 1. Statements

### P1 — `Tools/ShippingInstSignature.lean`

    theorem instSignature?_some
        (h : instSignature? env n = some (kinds, res)) :
        Sparkle.Compiler.isHardwareModule env n = true ∧
        ∃ ci, env.find? n = some ci ∧ telescopeKinds ci.type = some kinds ∧
          machResultKind? ci.type = some res

    theorem instSignatureS?_some
        (h : instSignatureS? env n = some (kinds, ty)) :
        Sparkle.Compiler.isHardwareModule env n = true ∧
        ∃ ci, env.find? n = some ci ∧ telescopeKinds ci.type = some kinds ∧ ty = ci.type ∧
          machResultKind? ci.type = none

    theorem structEnv_inst  (env) : (structEnv env).inst  = instSignature?  env := rfl
    theorem structEnv_instS (env) : (structEnv env).instS = instSignatureS? env := rfl

### P2 — `Tools/ShippingReaderResultKind.lean` (in full, not a fragment)

`machOuts?` (3852), `machResultKind?` (4312), `machTupleKinds?` (3828),
`telescopeKinds` (4353), `mixedGateBinderKind?` (2333) and
`canonicalNatLitValue?` (1385) are all structural recursions or plain
matches on `Lean.Expr` — none is `partial`, none calls an `opaque`
function (`Expr.isConstOf`, `Expr.getAppFn` are definitions). So P2 holds
for every type expression and every structure environment:

    theorem machOuts?_of_resultKind (senv : StructEnv) (ty : Lean.Expr) :
        ∀ k, machResultKind? ty = some k →
          machTupleKinds? ty = none ∧ machOuts? senv ty = some (none, [("out", k)])

with the lemmas it is made of:

    theorem kind_inv (h : mixedGateBinderKind? ty = some k) (hk : k ≠ .domain) :
        (∃ us dom us', ty = .app (.app (.const ``Signal us) dom) (.const ``Bool us') ∧ k = .bool) ∨
        (∃ us dom us' wE n, ty = .app (.app (.const ``Signal us) dom)
            (.app (.const ``BitVec us') wE) ∧ k = .bits n)
    theorem machOuts?_signal (senv us dom α) :
        machOuts? senv (Signal us dom α) = outsOfKind senv (Signal us dom α)
    theorem outs_of_kind (senv) (h : mixedGateBinderKind? ty = some k) (hk : k ≠ .domain) :
        machTupleKinds? ty = none ∧ machOuts? senv ty = some (none, [("out", k)])
    theorem machResultKind?_inv (h : machResultKind? ty = some k)
        (hnf : ∀ n d b bi, ty ≠ .forallE n d b bi) :
        mixedGateBinderKind? ty = some k ∧ k ≠ .domain
    theorem machResultKind?_ne_domain (ty) : ∀ k, machResultKind? ty = some k → k ≠ .domain
    theorem machOutFields_single (W nm k) :
        machOutFields W [(nm, k)] = [{ name := nm, lo := W, width := machWidth k, ty := machHWType k }]

(`outsOfKind` is the text of `machOuts?`'s last alternative as a function of
its own; the one step that EVALUATES the reader — that a `Signal` head is
not the `Prod` pattern — is `machOuts?_signal`, by `rfl`.)

### P4 — `Tools/ShippingMachineShapeUnfold.lean`

    def declOuts? (senv) (ty) := match machTupleKinds? ty with
      | some ks => some (none, [("out", .bits (ks.map machWidth).sum)])
      | none => machOuts? senv ty
    def instBinders (insts) := ((List.range insts.length).zip (insts.map (·.2.2))).map
      fun (j, kind) => (Name.mkSimple s!"inst{j}", kind)

    theorem machineShape?_some
        (h : machineShape? sym params (.defnInfo d) senv allow = some sp) :
        ∃ bs e ctor? outs slotB letB W,
          mixedGatePeel (MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
          declOuts? senv d.type = some (ctor?, outs) ∧
          sp.binders = bs ++ instBinders sp.insts ++ slotB ++ letB ∧
          sp.layout.outs = machOutFields W outs ∧
          sp.layout.lets = letB.length

    theorem instBinders_kinds (insts) : (instBinders insts).map (·.2) = insts.map (·.2.2)

    theorem machineShape?_callBinder
        (h : machineShape? sym params (.defnInfo d) senv allow = some sp) :
        ∃ bs e, mixedGatePeel (MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
          ∀ k, k < sp.insts.length →
            (sp.binders.map (·.2))[bs.length + k]? = (sp.insts.map (·.2.2))[k]?

Compositions:

    theorem machineShape?_single_out                       -- P2 + P4
        (h : machineShape? sym params (.defnInfo d) senv allow = some sc)
        (hres : machResultKind? d.type = some k) :
        ∃ W, sc.layout.outs = [{ name := "out", lo := W, width := machWidth k, ty := machHWType k }]

    theorem callee_single_out                              -- P1 + P2 + P4
        (hinst : (structEnv env).inst c = some (kinds, res))
        (hfind : env.find? c = some (.defnInfo d))
        (hc : machineShape? sym params (.defnInfo d) senvC allow = some sc) :
        ∃ W, sc.layout.outs = [{ name := "out", lo := W, width := machWidth res, ty := machHWType res }]

`machineShape?_single_out` also closes the item left open in
`B-callkinds.md` §4 ("that the layout has NO other output … not proved").

## 2. The boundary of P4 — where a `partial` result enters `machineShape?`

`machineShape?` (5056–5186) is a `def`. The `MachRead` state `st` whose
fields become `shape.insts`, `shape.instFields`, the slot binders
(`st.names`, `st.kinds`), the `let` binders (`st.lets`), the reset values
(`st.inits`), `runs`, `loops` is produced by these calls, in order:

| line | call | kind |
|---|---|---|
| 5074 | `machNorm senv e` — the body before any reading | `partial def` (4954) |
| 5098 | `machConv senv … 0 dom st` — the enclosing run's domain | `partial def` (3881, in the `mutual` block 3871–4230) |
| 5099 | `machReserve senv.natOf dom' αs initsE body st` | `def` (3696), not unfolded here |
| 5106 | `machLoopRoot senv env v st` — a root `Signal.loop` | `partial def` (4190) |
| 5111 | `machConv senv env 0 v st` — a root `let` | `partial def` |
| 5121 | `machChain senv (.regs 0 :: env) body st` — the body | `partial def` (4121) |
| 5127 | `machConv senv env 0 root st` — a root expression | `partial def` |

The call entries are pushed only by `machInstance` (4042–4074) and
`machInstanceS` (4076–4115), both `partial`, reached from inside `machConv`
/ `machChain` (also via `machNested` 4013, `machLoopBody` 4168). After 5127
the wrapper is pure again (`machDom?`, `machField`, `machClose`,
`machResults?`, `machPack`, `machCanonAp`, `unifiedGateRoot` — all `def`s),
and `machineShape?_some` covers it.

So P4 says where `binders[bs.length + k]` comes FROM (`insts[k].2.2`), and
does not say:

* what `insts[k]` is (R1, R2), what its argument `let`s are (R3);
* that `bs.length` is the `nDecl` the closing computes
  (`closeInstsM` 5199: `binders.length - kI - n - layout.lets`). With the
  theorem, `nDecl = bs.length + slotB.length - layout.slots.length`, so it
  is `bs.length` iff the slot-binder list (`st.names.zip st.kinds`) is as
  long as the layout's slot list (`machSlotFields (… .zip st.inits)`), i.e.
  `min names kinds = min kinds inits` — a fact about the `MachRead` the
  `partial` readers return (new invariant **R5**; `machReserve`, a `def`,
  pushes the three together, the loop readers are `partial`).

## 3. P3 and P5 — kernel-opaque, read in the toolchain source

`~/.elan/toolchains/leanprover--lean4---v4.32.1/src/lean/Lean/`:

| function | declaration | in the logic |
|---|---|---|
| `Expr.instantiate1` | `Expr.lean` 1446–1447: `@[extern "lean_expr_instantiate1"] opaque instantiate1 (e subst : @& Expr) : Expr` | **`opaque`: no definition, no equation** — only that the type is inhabited. Same for `instantiate` (1430), `instantiateRev` (1461), the `Range` forms, `abstract` (1495), `lowerLooseBVars` / `liftLooseBVars` (1358, 1363), `hasLooseBVar` (1331) |
| `Meta.instantiateForall` | `Meta/Basic.lean` 2140, through `private partial def instantiateForallAux` (2130) | `partial` (and monadic): no equation. Not used by the readers — only at 2026 of `Elab.lean`, in the legacy translator |
| `Expr.replace` | `Util/ReplaceExpr.lean` 19: `@[inline] def replace f? e := replaceImpl f? e`, and 16–17: `@[extern "lean_replace_expr"] opaque replaceImpl` | unfolds to an **`opaque`** constant. (`replaceNoCache`, 23, is a real structural definition — it is not what `replace` is.) |
| `BEq Lean.Expr` (`e' == e`) | `Expr.lean` 809–813: `opaque eqv`, `instance : BEq Expr := ⟨Expr.eqv⟩` | **`opaque`** |
| `Expr.headBeta` | `Expr.lean` 1658, a `def`, through `betaRev` (1593): `partial def` | `partial`: no equation |

This is the case "`@[extern]` on an `opaque`": not the case "`@[extern]`
on a `def` with a logical body" (e.g. `Expr.isConstOf` 878, `getAppFn`
1126, which unfold and are what P2 uses).

Consequences:

* **P3** (`machOuts?` of the type instantiated at the call = of the type):
  `machInstanceS`'s local `inst` (4082–4085) calls `b.instantiate1 a`.
  Nothing relates `machOuts? senv (b.instantiate1 a)` to `machOuts? senv b`
  in the logic. NOT provable as it stands — and this is independent of
  `machInstanceS` being `partial`.
* **P5** (`userInliner` does not change the kinds of a type): `userInliner`
  (3383) ends in `inlFoldNat (inlAbbrevs env 4 …)`, and `inlAbbrevs`
  (3372) is `let e' := e.replace …; if e' == e then e else inlAbbrevs env n
  e'.headBeta` — an `opaque` rewrite, compared by an `opaque` equality,
  followed by a `partial` function. Even `userInliner env e = e` for a
  closed type with no user constant is not derivable. NOT provable as it
  stands. (`inlinedConst` rewrites the TYPE too, 3407, so the child's
  entry constant, when it is the unfolding, has a type the logic knows
  nothing about. `machineShape?_single_out` is stated on whatever constant
  the shape was read from, with `machResultKind?` of ITS type as the
  hypothesis: for the unfolding that hypothesis is a run fact.)

## 4. Proposition A after this round

Result side, one-Signal callee `c` compiled on the machine route from the
constant `.defnInfo d`:

    kind of the parent's binder of entry k
      = sp.insts[k].2.2                           -- THEOREM (machineShape?_callBinder; position bs.length + k)
      = ((structEnv env).inst c).2                 -- R1: inside `partial` machInstance. OPEN
      = machResultKind? ci.type, ci = env.find? c  -- THEOREM (P1)
      ⇒ the child's layout is ONE output `out` of that kind's hardware type
                                                   -- THEOREM (P2 + P4), if the child's shape was read from ci itself
                                                   -- (declared constant); from the unfolding: P5, OPEN (opaque)

| part | status |
|---|---|
| P1, P2, P4 (R4 as far as the wrapper goes) | theorems of this round (UNVERIFIED until built) |
| R1, R2, R3, R5 | facts about results of `partial` functions: no equations. Believed true by reading; 93 known call entries with 0 differences in the shadow census |
| P3 | blocked by `opaque instantiate1` (not by `partial`) |
| P5 | blocked by `opaque replaceImpl` / `opaque eqv` / `partial betaRev` |
| T1, T2 | the kernel's typing of the callee's definition and of the call; kernel-checked per declaration where an endpoint is generated (`B-callkinds.md` §7), not a lemma |

"Hard because `partial`" versus "false": nothing found in this round makes
A false. The two places where the two sides read DIFFERENT expressions
remain T1 (`telescopeKinds ci.type` against `mixedGatePeel` of the VALUE)
and P3/P5 (the type after `instantiate1` / after `userInliner`).

### What a non-`partial` twin plus validation would cost

*Twin.* The mutual block 3871–4230 (seven functions, ≈360 lines) plus
`machNorm` (4954), `machLiftScalarN` (4638), `machBoolMap` (4817): a
fuel-indexed copy with equations. On it R1 and R5 are inductions over the
fuel with an invariant on `MachRead` ("every `insts` entry `(c, js, kd)`
pushed with field `out` has `senv.inst c = some (_, kd)`"; "`names`,
`kinds`, `inits` have one length"); R3 needs in addition the kind recorded
by `machLetIndex` (3736, a `def`); R2 needs P3, hence a pure `instantiate1`
in the twin (`instFVars` 2897 is such a function). Estimate: the copy
≈ 450 lines, the invariants ≈ 600–1000 lines of proof. It proves nothing
about the REAL reader: a `partial def` and its fuel copy are unrelated
constants in the logic.

*Validation* is what would relate them, per run: accept the real reader's
`some shape` only if a pure re-check agrees. Two re-checks are possible —
(a) `twin = some shape` (the whole shape), or (b) the much smaller check of
the shape's call entries against the callee constant's SYNTACTIC signature
(what `Tools/ShippingCallShadow.lean` computes; with P1, P2, P4 a `true`
there now implies the result-side agreement with a declared-constant
child's layout, without any reader equation).

The question is what happens when the re-check FAILS:

* decline (`none`) — forbidden: a reader returning `none` where it
  returned `some` can lose an input (ruling (i); `B-callkinds.md` point 1);
* fall back to the legacy route — the same thing under another name;
* keep the shape and LOG — allowed, changes nothing; but then no run fact
  "the check held" exists for a theorem to use, so there is no general
  theorem, only the census.

So validation yields a theorem only CONDITIONAL on the check, and the check
can be discharged in exactly one place without a behaviour change: per
declaration, on the REFLECTED shape of a generated endpoint, by `decide`
(the form `callWidthsOk` / `callWidthsStrict` have today — the reader's
result is data there, so `partial` does not matter). A statement for every
compiled source needs either the decline (forbidden), or the twin REPLACING
the reader (a compiler replacement whose equality with today's reader on
all inputs cannot be proved — the fuel bound against a `partial` function —
only measured by a shadow run of both), or a formal typing judgment (T1,
T2).

Recommendation (no decision taken): keep the shadow census as the general
evidence; state the per-endpoint strict condition on reflected data (round
3) as the kernel-checked part; and, if a general statement is wanted, the
unit that removes most is making the two sides read the SAME expression for
the result kind (the parent already reads `machResultKind? ci.type` — P1 —
and by P2 + P4 the child reads the same from the same type), which leaves
only R1/R5 (twin) and P5 (the unfolded constant's type).

## 5. Not done / unverified

* Nothing was built. In risk order: (1) `machineShape?_some` — a generic
  walk (`repeat' first | cases h | bind | split at h`) over a 130-line
  `Option` `do` block; it assumes `split` takes the outermost `match`/`if`
  (read in `Meta/Tactic/SplitIf.lean`: pre-order, candidates need
  discriminants without loose bound variables) and that the final
  `some {…} = some sp` closes by `rfl` on `binders` / `layout.outs`;
  (2) `machOuts?_signal`, `machTupleKinds?_bool/_bits` by `rfl` (name
  literals compared by evaluation, as `mixed_binder_bool` does today);
  (3) `kind_inv` / `machResultKind?_inv` (`split at h` on a variable
  discriminant must substitute it in the goal); (4) list lemma names
  (`List.map_snd_zip`, `List.getElem?_append_right/left`), each with a
  `simp` fallback; (5) `instSignature?_some` (`simp … at h` shapes).
* R1–R3, R5, P3, P5, T1, T2: not proved (see §4).
* No theorem connects `bs.length` to the closing's `nDecl` (R5).
* The argument side (R3 / T2) was not touched.

## 6. Repair after the first build (round 4b)

Integrator build of `aa720730` on poc: `Tools.ShippingInstSignature` (P1)
and `Tools.ShippingReaderResultKind` (P2) BUILT unchanged (poc `02b1b6de`).
`Tools.ShippingMachineShapeUnfold` failed in `machineShape?_some` only: the
generic walk (`repeat' first | cases h | bind | split at h | …`) did not
move at the outer `if`, and the closing `rfl`s then met the untouched goal.
The other theorems of that file reported no error.

What the failed build showed of the elaborated block (after `unfold` and
`dsimp only`), and what the repair is written against:

* pair patterns are projections (`__x.snd`, `(machRoot …).2.2.fst`);
* a `match` in the middle of the block carries its continuation in EVERY
  alternative (join points inlined): `match machTupleKinds? d.type with
  | some ks => do let __x_1 ← some (none, …); if … | none => …`;
* the binds are `>>=` of the `Option` monad.

The repair, in two files so that the first half survives a failure of the
second:

* `Tools/ShippingMachineShapeUnfold.lean` — the one-step inversions
  `ite_none_inv`, `ite_else_none_inv`, `bind_inv` (small lemmas, applied to
  the hypothesis; no `split`, no rewriting of the big term), and

      theorem machineShape?_prefix
          (h : machineShape? sym params (.defnInfo d) senv allow = some sp) :
          ∃ x o, mixedGatePeel (MachTupleIn.packTupleInputs d.value) = some x ∧
            declOuts? senv d.type = some o
      theorem declOuts?_of_resultKind (senv) (hres : machResultKind? ty = some k) :
          declOuts? senv ty = some (none, [("out", k)])

  by named steps: the outer `if`, the bind of the peel, `generalize hk :
  machTupleKinds? d.type = tup at h; cases tup`, the bind of the output
  list. Plus the list facts (`instBinders_kinds`, `getElem?_mid`).
  `instBinders` is now written with projections.
* `Tools/ShippingMachineShapeTail.lean` — `machineShape?_some` (statement
  as in §1 WITHOUT the last conjunct `sp.layout.lets = letB.length`, which
  nothing used), `machineShape?_callBinder`, `machineShape?_single_out`,
  `callee_single_out` (statements unchanged). After the prefix: the test on
  the output names (`ite_none_inv`); `generalize hrun : Option.bind _
  machRunApp? = run at h` and one case split (this decides BOTH matches on
  the enclosing run; the second match on `machTupleKinds?` was decided by
  the prefix); then the program is a straight line, inverted by
  `ite_none_inv` / `bind_inv` until neither applies; then explicitly the
  gate (`ite_else_none_inv`), `Option.some.inj`, `subst`, and the
  conclusion with the two equations by `rfl` on the literal.

**Where this departs from "one named step per line".** The straight-line
stretch is a loop over two unification-only lemmas. Reason: the number of
binds there cannot be read off the source (an inlined join point may leave
a `pure v >>= …`), no equation of that stretch is used, and the steps
cannot branch. If it stalls, the explicit step after it fails and prints
the head it stalled on — that is the information needed to write the
stretch out line by line in the next round. If the integrator prefers, the
second file can be left out: P1, P2 and the prefix do not depend on it;
what is lost without it is `machineShape?_callBinder` (R4) and the two
compositions.

Tests: `Tests/Compiler/ReaderInvariantsTest.lean` (18 names, first half),
`Tests/Compiler/ReaderInvariantsTailTest.lean` (4 names, second half).

## 7. Round 5 (`par/b-6`): the three states, R5, and what `callee_single_out` does and does not replace

### The three states, per theorem

"target-built": built by the integrator on poc. "written": written, not
built — until the integrator has built a file, its theorems are WRITTEN,
not proved (wherever this note says "theorem" of such a file, read
"written statement"). "connected": used by a generated endpoint or by a
theorem an endpoint uses. **Nothing of this line is connected to an
endpoint.**

| theorem (file) | built | connected to an endpoint |
|---|---|---|
| `instSignature?_some`, `instSignatureS?_some`, `structEnv_inst(S)` (`ShippingInstSignature`) — P1 | **target-built** (poc `02b1b6de`) | no |
| `machOuts?_of_resultKind`, `kind_inv`, `machOuts?_signal`, `outs_of_kind`, `machResultKind?_inv`, `machResultKind?_ne_domain`, `machOutFields_single` (`ShippingReaderResultKind`) — P2 | **target-built** (poc `02b1b6de`) | no |
| `ite_none_inv`, `ite_else_none_inv`, `bind_inv`, `machineShape?_prefix`, `declOuts?_of_resultKind`, `instBinders_kinds`, `getElem?_mid` (`ShippingMachineShapeUnfold`, repaired) — P4 prefix | written, not built (`f8762e4c`, queued) | no |
| `machineShape?_some`, `machineShape?_callBinder`, `machineShape?_single_out`, `callee_single_out` (`ShippingMachineShapeTail`) — P4 | written, not built (`f8762e4c`, queued) | no |
| `machineShape?_decomp`, `ShapeDecomp.slots_length / r5_of_lengths / nDecl / callBinder_bs / callBinder / single_out` (`ShippingShapeDecomp`) — the bundle, R5 as a hypothesis | written, not built (round 5) | no |
| `entryStrict`, `callWidthsStrict_of_entries`, `entryStrict_of_single`, `r1_of_kind`, `entryStrict_declared` (`ShippingCallWidthsDeclared`) | written, not built (round 5) | no |

(The table with round 6 is §8.1.)

### R5: what is pure and what is not

The closing's `nDecl` (5199, 5218) is `binders.length - insts.length -
layout.slots.length - layout.lets`. The wrapper text gives (all fields of
`ShapeDecomp`, by `rfl` on the structure literal):

* `binders = bs ++ instBinders insts ++ names.zip kinds ++ letB` (5165–5168);
* `layout.slots = machSlotFields ((kinds.map machWidth).zip inits)` (5173);
* `layout.lets = letB.length` (5176; the conjunct dropped in the repair of
  round 4b is BACK, as the field `lets`).

PURE consequences: `(instBinders insts).length = insts.length`;
`layout.slots.length = min kinds.length inits.length`
(`ShapeDecomp.slots_length`); the slot binders are `names.zip kinds`.
NOT pure: `(names.zip kinds).length = layout.slots.length`, i.e. `min
names.length kinds.length = min kinds.length inits.length`. The two lists
are zips of `kinds` with two DIFFERENT arrays of the reader state
(`st.names`, `st.inits`); nothing in the wrapper relates their sizes. So
R5 is a hypothesis of `ShapeDecomp.nDecl` and `ShapeDecomp.callBinder`,
and `r5_of_lengths` reduces it to `names.length = kinds.length ∧
inits.length = kinds.length` — an invariant of `MachRead` kept by the
readers that push slots (`machReserve`, a `def`; `machLoopRoot` /
`machLoopBody`, `partial`).

The correction to round 4: `machineShape?_callBinder` (position
`bs.length + k`) is NOT the closing's position. `ShapeDecomp.callBinder`
is the statement at `nDecl + k`, under R5.

### Corrected claim about `callee_single_out`

`callee_single_out` covers the child's half of the RESULT side for a
one-Signal callee read from its DECLARED constant, and nothing else. It
does not remove the data premise `callWidthsStrict` / `callWidthsOk`, and
it says nothing about `callArgsOk`. Still open: R1 (the parent's
`insts[k]` kind is `(structEnv env).inst c`'s kind), R5, P5 (a child whose
entry constant is its unfolding), the argument side R3 / T2.

**Which existing endpoint's which `decide` can it replace today? None.**
By `grep` on poc, a call-width condition is decided in exactly these
places, all `callWidthsOk` (not the strict form):

* `Tests/Compiler/ChecksRawTest.lean` 362–364 `parent_callWidths`
  (`parent` against `cnt`);
* `Tests/Compiler/PortsMatchRawLeafChainedTest.lean` 36 (`chained`);
* the generators `Tools/ShippingNoPortsCommand.lean` 221,
  `Tools/ShippingNoDesignCommand.lean` 155,
  `Tools/ShippingShipsFreeCommand.lean` 159 (generated for `parent`,
  `chained`).

None is replaceable by this line as it stands, for three independent
reasons:

1. their callee `cnt` returns a STRUCTURE (`n`, `hit`): the entries come
   from `machInstanceS` (R2, with `Expr.instantiate1` — P3), not from the
   one-Signal path;
2. the one-Signal parents (`caller`, `callerTwice`, `callerNested`,
   `callerD`) have NO width theorem and hence no `decide` to replace
   (`B-callkinds.md` §6);
3. the decided conditions are about REFLECTED shapes
   (`f.machineData.shape`), while this line speaks of `machineShape? … =
   some sp`; the link is `MachineDefines` (the entry constant, possibly
   the unfolding: P5).

**The first consumer — WITHDRAWN, corrected in §8.4.** Round 5 named the
one-output form of `ShippingMachineInstTest.caller` (`hkidW_one`) here.
That was wrong: `caller`'s child `pick` is a GATE-route child; its shape is
not a `machineShape?` result, so neither `callee_single_out` nor
`entryStrict_declared` applies to it (`pick` needs a gate output-type
lemma — worker A's). The round-5 sentence "the `decide` becomes R1 and R5
per parent plus the two `machineShape?` equations" was also incomplete
(`DP`, `hc`, `hkid`, the callee's identity and the common environment were
not counted), and "bundle + `nDecl` under R5" is a DECOMPOSITION of the
obligation, not its discharge. The full list of what is left, for ONE
fitting example, is §8.4.

## 8. Round 6 (`par/b-7`): the length invariant, the corrected consumer, the boundary

Base `9e7f8100`. Lines of `Sparkle/Compiler/Elab.lean` as in that tree.
**Everything of this round is WRITTEN, not built.** The endpoint premise
reduction of this line is still 0.

### 8.1 The three states

| statements (file) | state | connected to an endpoint |
|---|---|---|
| P1 `instSignature?_some`, `instSignatureS?_some`, `structEnv_inst(S)` (`ShippingInstSignature`) | **target-built** (poc `02b1b6de`) | no |
| P2 `machOuts?_of_resultKind` and its lemmas (`ShippingReaderResultKind`) | **target-built** (poc `02b1b6de`) | no |
| P4 prefix: `ite_none_inv`, `ite_else_none_inv`, `bind_inv`, `machineShape?_prefix`, `declOuts?_of_resultKind`, `instBinders_kinds`, `getElem?_mid` (`ShippingMachineShapeUnfold`) | written (`f8762e4c`; queued for its own build; NOT touched this round) | no |
| P4 tail: `machineShape?_some`, `machineShape?_callBinder`, `machineShape?_single_out`, `callee_single_out` (`ShippingMachineShapeTail`) | written (`f8762e4c`, queued; untouched by the first three commits of this round; the consolidated version is the LAST commit, §8.5) | no |
| `machineShape?_decomp`, `ShapeDecomp.*` (`ShippingShapeDecomp`) | written (round 5) | no |
| `entryStrict`, `callWidthsStrict_of_entries`, `entryStrict_of_single`, `r1_of_kind`, `entryStrict_declared` (`ShippingCallWidthsDeclared`) | written (round 5; `entryStrict_declared` tidied in the last commit) | no |
| `MachRead.LenOk`, `lenOk_init`, `lenOk_append`, `lenOk_bareRegister`, `lenOk_loopRoot`, `lenOk_reserved`, the nine frame lemmas (`ShippingReaderLenOk`) | written (this round); imports the compiler only — independent of every queued file | no |
| `machReserve_eq_spec`, `machReserve_some`, `machReserve_lenOk`, `machInits_length`, `machSlotNames_length`, `mapM_option_length`, `loopRoot_inits_length` (`ShippingReaderLenOkReserve`) | written (this round); imports `ShippingReaderLenOk` only | no |
| `shapeR5Ok`, `MachineData.r5Ok`, `binders_length`, `r5_of_count`, `count_of_r5`, `r5_of_r5Ok` (`ShippingR5Check`) | written (this round); needs `ShippingShapeDecomp` | no |
| `machineShape?_defn`, `link_of_defines`, `entryStrict_of_child`, `entryStrict_of_links`, `callWidthsStrict_of_links`, `R1At`, `resC_of_declared`, `entryStrict_of_links_declared` (`ShippingCallWidthsEntry`) | written (this round); needs `ShippingCallWidthsDeclared`, `ShippingR5Check` | no |
| `callerL_strict_decide`, `callerL_r5Ok`, `callerL_instKinds`, `callerL_callee`, `callerL_strict_links`, `callerL_entry_declared` (`Tests/Compiler/CallWidthsEntryExampleTest`) | written (this round) | no |

### 8.2 The length invariant, split

`MachRead` (3559): `kinds : Array MixedGateBinder`, `inits : Array Nat`,
`names : Array Name`. `MachRead.LenOk st` is `st.names.size =
st.kinds.size ∧ st.inits.size = st.kinds.size` (a structure with the fields
`names`, `inits`; `lenOk_iff`).

**(i) Initial state.** `let st : MachRead := {}` (5092): `lenOk_init`.

**(ii) `machReserve`** (3696–3710, a `def`). It appends `kinds` (from
`machSlotKinds`) to `st.kinds`, `inits` (from `machInits natOf kinds`) to
`st.inits`, and `machSlotNames st.runs.size body kinds base` to `st.names`;
`machInits_length` and `machSlotNames_length` say both lists are as long as
`kinds`; `machReserve_lenOk : st.LenOk → machReserve … st = some (base,
st') → st'.LenOk`.

**(iii) Every expression that builds a `MachRead`** — 23 record updates and
the literal `{}`. Found by `grep` for `with` in 3871–4230 and 5056–5186 and
for `MachRead` in the file; no other file under `Sparkle/` mentions
`MachRead`.

| lines | function | writes | preserved? | lemma |
|---|---|---|---|---|
| 3705–3710 | `machReserve` | `kinds ++`, `inits ++`, `names ++`, `dom`, `runs` | yes (three lists of one length) | `lenOk_reserved`, `machReserve_lenOk` |
| 3924–3927 | `machConv`, bare `Signal.register` | `kinds.push`, `inits.push`, `names.push`, `dom`, `bareRegs` | yes | `lenOk_bareRegister` |
| 4216–4223 | `machLoopRoot` | `kinds ++`, `inits ++`, `names ++` (`(List.range n).map …`, `n = kinds.length`), `dom`, `loops`, `nestedLoops`, `loopDepth` | yes, given `inits.length = kinds.length` — the two `mapM`s of 4199–4200, `loopRoot_inits_length` | `lenOk_loopRoot` |
| 3929, 4183, 4208, 4209, 5125 | `machConv`, `machLoopBody`, `machLoopRoot`, wrapper | `ws` | yes (arrays untouched) | `lenOk_ws` |
| 3953, 4051 | `machConv` (memory), `machInstance` | `instStruct` | yes | `lenOk_instStruct` |
| 4003, 4064, 4100, 4161, 4176, 5116 | `machConv`, `machInstance`, `machInstanceS`, `machChain`, `machLoopBody`, wrapper | `lets` | yes | `lenOk_lets` |
| 4033 | `machNested` | `inInner` | yes | `lenOk_inInner` |
| 4036 | `machNested` | `ws`, `inInner`, `nested` | yes | `lenOk_nestedClose` |
| 4061, 4096 | `machInstance`, `machInstanceS` | `dom` | yes | `lenOk_dom` |
| 4068 | `machInstance` | `insts`, `instFields` | yes | `lenOk_instPush` |
| 4110–4113 | `machInstanceS` | `insts`, `instFields`, `instStruct` | yes | `lenOk_instS` |
| 4228 | `machLoopRoot` | `loopWs`, `loopDepth` | yes | `lenOk_loopClose` |

**NOT preserved: none.** No site writes one or two of the three arrays; the
invariant is never false or temporarily broken, so there is no declaration
to exhibit. (Sites that hand back an OLDER or ANOTHER state — `machNested`'s
`shared` 4022–4031, `machLoopRoot`'s `shared` 4206–4213 — hand back states
returned by reader calls, updated only in `ws`.)

### 8.3 The boundary (iv)

"The state `machineShape?` ends with satisfies `LenOk`" is NOT derivable.

* A `partial def` is added to the kernel as `DefKind.opaque` with the value
  `mkInhabitantFor` (toolchain `Lean/Elab/PreDefinition/Main.lean` 20–36,
  `addAndCompilePartial`); the source text is compiled separately
  (`addAndCompilePartialRec`) and attached as the implementation. The
  kernel constant has NO equation — no unfolding lemma, not even a
  propositional one; its hidden value is some inhabitant of the type, not
  the reader. `ReadersKeepLenOk` (`ShippingReaderLenOk`, a definition used
  by nothing) is therefore neither provable nor refutable.
* The constants: `Sparkle.Compiler.Elab.machConv`, `machNested`,
  `machInstance`, `machInstanceS`, `machChain`, `machLoopBody`,
  `machLoopRoot` (one `mutual` block, 3871–4230).
* Where the chain stops in the wrapper, exactly:

  | wrapper step | state in | what is known of the state out |
  |---|---|---|
  | 5092 `{}` | — | `LenOk` (`lenOk_init`) |
  | 5098 `machConv … dom st` (run case) | `{}` | NOTHING — the first opaque constant; in the run case the chain stops HERE |
  | 5099 `machReserve … st` | 5098's | `LenOk` IF 5098's has it (`machReserve_lenOk`) |
  | 5103–5117 `foldlM` over the root `let`s: `machLoopRoot` 5106, `machConv` 5111, then `{ st with lets }` 5116 | previous | nothing (opaque); with no root `let` the state is unchanged |
  | 5121 `machChain` (run case) / 5127 `machConv` (no run) | previous | NOTHING — one of the two is always executed: every path ends in an opaque constant |
  | 5125 `{ st with ws }` | 5121's | `LenOk` if 5121's has it (`lenOk_ws`) |

  In the no-run case with no root `let` the state is `{}` up to 5127, and
  5127 is opaque. No path is pure.
* What a kernel proof would need: equations for the seven readers — a
  compiler change (fuel, `partial_fixpoint`, or well-founded recursion),
  outside this round. No axiom was added for it.

**The alternative without a compiler change and without an axiom: R5
checked on the returned shape.** R5 is `(names.zip kinds).length =
sp.layout.slots.length`. It is NOT a function of the shape alone
(`ShippingR5Check` header: one shape, two decompositions, R5 true in one
and false in the other — the shape does not record how many of its binders
are the declaration's). With the number of declaration binders it is a
count: `shapeR5Ok sp nB := sp.binders.length = nB + insts + slots + lets`,
EQUIVALENT to R5 at `nB = bs.length` (`r5_of_count`, `count_of_r5`). On
reflected data: `MachineData.r5Ok d` (the count at `d.nIn`), one `decide`
per declaration, and `r5_of_r5Ok` needs the explicit link `hnIn : d.nIn =
bs.length + d.shape.insts.length`. The generator already enforces exactly
this count when it builds the data (`ShippingMachineCommand` 437–442,
`throwError "binder count"`), at the meta level. **So R5 stays a
per-declaration decidable data condition plus the link `hnIn`; it is not a
general theorem and this round does not make it one.**

### 8.4 The corrected consumer: `callerL → pickByteH`

`entryStrict_declared` / `callee_single_out` apply when the CHILD's shape
is a `machineShape?` result. Candidates checked:

| | `caller → pick` (round 5's choice) | `callerL → pickByteH` | `hftByte → httpGetByte` |
|---|---|---|---|
| child's route | GATE — does NOT fit | machine (slotless leaf; `#machine_endpoint pickByteH`) | machine (slotless leaf; `#machine_endpoint` in `ShippingMachineCombTest`) |
| child's result | — | one Signal, `BitVec 8` | one Signal, `BitVec 8`; an implicit `{dom : DomainConfig}` binder |
| parent's closing | — | one-output: a `.bits` result goes through `machInstance` without `instStruct` (4050), so `instFields = []` (5180); `callerL_instFields` states it on the reflected data | by reading the same; NOT checked on reflected data here; the call sits in a sub-machine of the IP library's `hftStrategy` (telescope endpoint, `ShippingMachineTeleTest`) |
| parent sees the child's DECLARED signature | — | yes | yes |
| existing commands | — | `#machine_endpoint`, `#machine_child pickByteH`, `#machine_linked`, `#machine_composed`, `#machine_closes_at`, `#machine_ships_hierH`, `#machine_design_svHR` | `#machine_child`, `#machine_endpoint`, `#machine_linked` |

Chosen: **`callerL → pickByteH`** (both in one test file, monomorphic,
depth 1, both reflected).

**Declared or inlined (P5) — the same answer for both pairs.**

* Parent side: the signature the parent's reader uses is ALWAYS the
  declared constant's. `machInstCall?` (3714) reads `senv.inst c`;
  `structEnv_inst : (structEnv env).inst = instSignature? env` (`rfl`);
  `instSignature?` reads `env.find? n` and its type (P1, target-built).
  `userInliner` is not involved.
* Child side: the child's shape in `MachineDefines` is read from the ENTRY
  constant `entryConst true false [] ci …` (5248–5258), which is
  `inlinedConst (userInliner env) ci` whenever both gates miss on `ci` and
  `machineShape?` accepts the unfolding — the normal case of a
  machine-route child, `pickByteH` and `httpGetByte` included (by reading;
  which branch is taken is not decidable in the kernel: `userInliner` goes
  through `opaque` rewrites, §3). `inlinedConst` rewrites the TYPE too
  (3406). So `callee_single_out` / `entryStrict_declared`, which take the
  child's shape from the definition `env.find? c` holds, do NOT match what
  `MachineDefines` provides. What matches is `machineShape?_single_out` /
  `entryStrict_of_child` with `ResC : machResultKind? dC.type = some res`
  for the entry constant `dC` — and for an unfolded `dC` that is a fact
  about `userInliner` on a type (P5), provided by nothing.

**Data condition ↦ remaining obligations**
(`Tests/Compiler/CallWidthsEntryExampleTest.lean`):

    callWidthsStrict callerL.machineData (closingNDecl callerL.machineData.shape)
        (fun _ => pickByteH.machineData.shape.layout.outs) = true

| | obligation | status for `callerL → pickByteH` |
|---|---|---|
| way 1 | the condition itself | ONE `decide` (`callerL_strict_decide`) |
| way 2 | `R5ok : callerL.machineData.r5Ok = true` | `decide` (`callerL_r5Ok`) |
| | `R1all`: every call entry's kind is `.bits 8` | `decide` (`callerL_instKinds`). As a reader fact (R1, `R1At`): the result of the `partial` `machInstance`, open |
| | `LinkP : machineShape? … (.defnInfo dP) … = some callerL.machineData.shape` | hypothesis. From `MachineDefines` of `callerL` and its three run facts by `link_of_defines`, with `dP` the entry constant. `MachineDefines` is itself an ASSUMPTION of the endpoints (the reflected shape was evaluated at generation time), so this is not a closed fact |
| | `LinkC`: the same for `pickByteH.machineData.shape` | hypothesis, same source |
| | `NIN : d.nIn = bs.length + insts.length` for the peel `bs` of `dP.value` | hypothesis. The generator's meta-level knowledge only; no kernel statement (the peel goes through `packTupleInputs`, a `partial def`) |
| | `ResC : machResultKind? dC.type = some (.bits 8)` | hypothesis. P1 if `dC` is the declared constant (`resC_of_declared`); P5 for the unfolding |
| | (declared form only) `hcallee` | `rfl` (`callerL_callee`) |
| | (declared form only) `hinst`, `hfind` in the SAME `env` as `LinkP`'s `structEnv env`; `R1At env … 0` | hypotheses |

**Is this a reduction worth having? No.** It replaces one `decide` by two
`decide`s, two links that `MachineDefines` gives under run facts, and two
obligations nothing provides (`NIN`; `ResC` when the child's entry constant
is its unfolding). The single place where a lemma replaces an evaluation is
the child side (`entryStrict_of_child`: the layout is one output `out` of
`machHWType res`), and that fact is itself one `decide` on the child's
reflected shape. An endpoint that took these hypotheses would assume R1 /
R5 under other names: its gap would NOT be empty.

What would make it a real reduction:

1. R1 as a theorem — needs equations for `machInstance` (a compiler
   change) or a validated twin (§4);
2. `MachRead.LenOk` of the returned state — then `R5ok` AND `NIN` go at
   once (`ShapeDecomp.r5_of_lengths` needs neither); needs the same
   equations, and a decomposition that keeps the reader state (the walk of
   `machineShape?_decomp` drops those equations today);
3. the reflection links as closed facts — they are premises of every
   endpoint today (`MachineDefines`); this line cannot remove them;
4. `ResC` for an unfolded entry constant (P5) — blocked by `opaque`
   rewrites; or a child read from its declared constant.

"If R1 gives the same kind the width proposition holds" is the content of
`entryStrict_of_links`; it is NOT a proof that the reader agrees for an
arbitrary call.

### 8.5 Consolidation (the LAST commit of this round, separate)

Rounds 4b/5 left the same unfold/walk twice (`machineShape?_some` in the
tail, `machineShape?_decomp`). The last commit makes the tail's four
statements corollaries of `machineShape?_decomp` (the tail then imports
`ShippingShapeDecomp`; the prefix file is untouched and keeps its own
build) and tidies `entryStrict_declared`. It is to be applied AFTER the
queued tail (`f8762e4c`) has been built or has returned its stall head, so
that the diagnostic of the queued walk is not lost. The walk itself is not
changed by the consolidation; a repair found on the queued tail goes into
`machineShape?_decomp`, once.

`entryStrict_declared`, tidied: the comment's `hp` was the argument `DP`
(a `ShapeDecomp`: the parent link already decomposed); the binders `symP` /
`paramsP` / `allowP`, used neither in a hypothesis nor in the conclusion,
are gone; new hypothesis `hcallee` (the entry's callee is `c`), and `R1` is
taken in its reader form (callee and signature ↦ kind), instantiated by
`hcallee` and `hinst`. Its hypotheses are ALL unconnected: `DP`, `hcallee`,
`hinst`, `hfind`, `hc`, `hkid`, `R5`, `R1`. A consumer must additionally
secure that the parent's shape was read with the signature table of the
same `env` (`entryStrict_of_links_declared` states this through `LinkP` at
`structEnv env`) and that the child's shape was read from the constant
`env` holds for `c` — which `MachineDefines` does not give for an unfolded
entry constant.

### 8.6 Not done

* Nothing built. No endpoint premise removed.
* `ReadersKeepLenOk`: not proved (not provable today).
* The wrapper's own steps as a state transformer (5092–5127 → the final
  `st`) are not stated: `machineShape?_decomp` gives `names`, `kinds`,
  `inits` existentially, without the state they come from.
* `hftByte → httpGetByte`: no instance written; its closing was not checked
  on reflected data.
* The argument side (R3 / T2) and P3 remain untouched.
