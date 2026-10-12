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
