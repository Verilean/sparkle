# Reader generalisation, units 1 (gap) to 4: progress of the 15 `partial` functions

Branch `par/h-1` (base poc `df990315`).
**WRITTEN, NOT BUILT.** Nothing here was compiled or run. "READ" = read in
the tree of this branch (line numbers of that tree) or in the toolchain's
sources (`~/.elan/toolchains/leanprover--lean4---v4.32.1/src/lean`).
"PREDICTED" = from reading. "BUILT" appears only for what the integrator's
record in `docs/parallel/F-reader-unit.md` states.

Continues the ruling of 2026-10-14, item 5, and `F-reader-unit.md` (the map
of the 15 functions, unit 1). What is NOT done: the reader is not replaced,
not edited, not narrowed; no strict reader; no fuel; no file under `Sparkle/`
is touched; nothing is wired; `lakefile.lean`, `Tests/AllTests.lean` and the
built `Tools/` files are not edited. No `sorry`, no axiom, no
`native_decide`.

## 0. Files

| file | content |
|---|---|
| `Tools/ShippingReaderProjChainFold.lean` | unit 1, the gap: `projChainW = projChainT`, `projChainP_eq` |
| `Tools/ShippingReaderMatcherArity.lean` | unit 2: `walkT`, `leafT`, `goT`, `prodMatcherArityG/T/S`, success, congruence |
| `Tools/ShippingReaderMatcherArityUnique.lean` | unit 2, fragile proofs: `GoEq`, `goT_sol`, `go_unique`, characterisations, two links to the compiler's text |
| `Tools/ShippingReaderSweepCommon.lean` | what the shadows share (imports unit 1's shadow) |
| `Tools/ShippingReaderMatcherArityShadow.lean`, `Tests/Compiler/ReaderMatcherArityShadowTest.lean` | unit 2, measured |
| `Tools/ShippingReaderInstTy.lean` | unit 3: `instW`, `instG`, `instT`, equation, uniqueness, success |
| `Tools/ShippingReaderInstTyShadow.lean`, `Tests/Compiler/ReaderInstTyShadowTest.lean` | unit 3: the call-site theorem (imports the compiler) and the measurement |
| `Tools/ShippingReaderBoolMap.lean` | unit 4: `machBoolMapT`, the recursive arm |
| `Tools/ShippingReaderBoolMapLeaf.lean` | unit 4, fragile: the equality arm |
| `Tools/ShippingReaderBoolMapShadow.lean`, `Tests/Compiler/ReaderBoolMapShadowTest.lean` | unit 4, measured |

## 1. Unit 1, the provable gap: `projChainW = projChainT`

`F-reader-unit.md` §3a item 3 left this kernel statement unproved (both
sides total). `Tools/ShippingReaderProjChainFold.lean`:

```lean
theorem projChainW_eq_projChainT (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool) :
    projChainW regs tys j last = projChainT regs tys j last

def projChainP (tail : Nat → Option Lean.Expr) (regs : Lean.Expr) (tys : List Lean.Expr)
    (j : Nat) (last : Bool) : Option Lean.Expr      -- the compiler's text, `tail` a parameter

theorem projChainP_eq (tail : Nat → Option Expr) (regs : Expr) (tys : List Expr) (j : Nat)
    (last : Bool) (h : TailEq tys tail) :
    projChainP tail regs tys j last = projChainT regs tys j last

theorem projChainP_callSite (tail : Nat → Option Expr) (regs : Expr) (tys : List Expr)
    (j : Nat) (h : TailEq tys tail) (hj : j < tys.length) :
    ∃ r, projChainP tail regs tys j (j + 1 == tys.length) = some r
```

`projChainP_eq` is the statement the task names: the compiler's text over
ANY function satisfying the recursion equation of its local `tail` is the
structural definition. Exactly one item stays outside the kernel: the
compiled `partial` `tail` satisfies its own source equation (`TailEq`).

The route, and which `forIn` / range facts it uses (none is missing in the
core library, READ):

1. `projChainW_form` — the `do` block is
   `(forIn [0:j] regs (loopBody tys)).bind (finStep tys last j)`. By `rfl`.
   The ONLY step that depends on the `do` elaborator's output. READ
   (`Lean/Elab/BuiltinDo/For.lean`, `Lean/Elab/Do/Basic.lean`
   `bindMutVarsFromTuple`; `backward.do.legacy` defaults to `false`): the new
   elaborator emits `forIn xs init (fun i s => let cur := s; …)` bound to
   `fun s => let cur := s; …`, with one mutable variable as the state itself.
2. `forIn_range_list` — `Std.Legacy.Range.forIn_eq_forIn_range'`
   (`Init/Data/Range/Lemmas.lean` 88) and `(j - 0 + 1 - 1) / 1 = j`.
3. `forIn_list_foldO` — `List.forIn_nil`, `List.forIn_cons`
   (`Init/Data/List/Monadic.lean` 301): a list loop whose body always yields
   is the fold `foldO`.
4. `loop_chain` — induction on the number of rounds with unit 1's
   `drop_cases`: the fold over `range' s k`, then `finStep` at `s + k`, is
   `chainGo last cur (tys.drop s) k`.

The restatement without `forIn` asked for as a fall-back was not needed:
`projChainW` itself is used; `foldO` is an intermediate form and is proved
equal to the `forIn` text (steps 1–3).

## 2. Unit 2: `prodMatcherArity?` (MachRawSurface.lean 26–51)

### 2a. The decision about `==`

The last test of `go` is `args.toList == expected.map Lean.Expr.bvar`:
`List.beq` over `BEq Lean.Expr`, i.e. `Lean.Expr.eqv`
(`@[extern "lean_expr_eqv"] opaque`, `Lean/Expr.lean` 809).

DONE AS RULED: the test is a parameter `eqv : Expr → Expr → Bool`; nothing
about the extern is assumed. The definition is split so that the parameter
enters in one place that is not recursive:

```lean
def walkT (e : Expr) (subj : Nat) (vars : List Nat) (depth : Nat) : Option LeafData
    -- structural on `e`; no fuel; no opaque function; `termination_by structural e`
def leafT (eqv : Expr → Expr → Bool) (hIdx : Nat) (args : List Expr) (subj : Nat)
    (vars : List Nat) (depth : Nat) : Option Nat          -- not recursive
def goT (eqv) (e subj vars depth) : Option Nat := (walkT e subj vars depth).bind (leafD eqv)
def prodMatcherArityG (eqv) (env : Environment) (n : Name) : Option Nat
def prodMatcherArityT := prodMatcherArityG exprEqv      -- exprEqv a b = (a == b): the compiler's test
def prodMatcherArityS := prodMatcherArityG bvarEqv      -- a structural test
```

What can be proved with `==` opaque: EVERYTHING except the truth value of
that one Boolean —

* the walk (the whole recursion) does not contain the test, so its
  equations, its success on canonical inputs and the uniqueness of its
  equation's solution are premise-free;
* the result is characterised exactly (`goT_some_iff`, `leafT_some_iff`:
  `some k` iff the walk reaches a leaf whose head index is the depth, whose
  arguments pass `listEqv eqv` against the expected bound variables, and `k`
  is the number of arguments);
* success needs ONE premise about the test, `∀ i, eqv (.bvar i) (.bvar i) =
  true`. At `exprEqv` this is a statement about the extern: NOT proved, NOT
  assumed, an explicit hypothesis of `prodMatcherArityT_canon`.

Would a structural test be extensionally the same on the reader's inputs?
By READING: yes — the right-hand side of every comparison is `.bvar i`, and
`Expr.eqv` is equality up to binder names and binder information, so
`a == .bvar i` should hold exactly when `a` is `.bvar i` (`bvarEqv`). That
is a statement about the extern (the runtime's source is not in this tree):
not provable, and NOT USED. Nothing is narrowed: `prodMatcherArityS` is a
second candidate; `prodMatcherArityT_eq_S` proves the two candidates equal
under the single hypothesis
`∀ a i, (a == Expr.bvar i) = bvarEqv a (.bvar i)`; the shadow measures `old`
against both and reports a difference of `S` without failing.

### 2b. Correspondence old ↔ new

No kernel equation with `prodMatcherArity?` or its `go` can be proved (both
`partial`); none is assumed. Proved about the new definition:

```lean
theorem walkT_sol (e subj vars depth) :
    walkT e subj vars depth = step leafW walkT e subj vars depth       -- every e
abbrev GoEq (eqv) (g : Expr → Nat → List Nat → Nat → Option Nat) : Prop :=
  ∀ e subj vars depth, g e subj vars depth = step (leafT eqv) g e subj vars depth
theorem goT_sol (eqv) : GoEq eqv (goT eqv)                               -- existence
theorem go_unique (eqv) (g) (hg : GoEq eqv g) :
    ∀ e subj vars depth, g e subj vars depth = goT eqv e subj vars depth -- uniqueness
theorem goT_shape … / goT_bvar …                                        -- the two arms
theorem listEqv_exprEqv : ∀ l1 l2, listEqv exprEqv l1 l2 = (l1 == l2)
theorem headT_eq_getAppFn : ∀ e, headT e = e.getAppFn
```

`step (leafT eqv) g` is one unfolding of the compiler's `go` with the
recursive call `g`, in STRUCTURAL form:

| the compiler's text | here |
|---|---|
| `e.getAppFn` | `headT e` (PROVED equal, `headT_eq_getAppFn`) |
| `e.getAppArgs` and an array pattern `#[_, _, _, .bvar t, .lam _ _ (.lam _ _ rest _) _]` | a constructor pattern of five `.app`; `argsT e` at the leaf (NOT proved equal: see boundary 2) |
| the name pattern ``` ``Prod.casesOn ``` | `c = ``Prod.casesOn` (decidable equality) |
| `args.toList == …` | `listEqv eqv args …` (PROVED equal at `exprEqv`, `listEqv_exprEqv`) |
| `args.size` | `args.length` |

The BOUNDARY, precisely:

1. the compiled `go` satisfies its own source equation — the meaning of
   `partial`; not a kernel statement;
2. the source equation (array form) is the structural form `GoEq`: both
   sides total, provable in principle, NOT proved — `Lean.Expr.getAppArgs`
   is defined through `getAppArgsAux`, a `private` definition of a `module`
   (`Lean/Expr.lean` 1189): it cannot be named from a file outside. MEASURED
   per node (`PIECES`: `headT` / `argsT` against `getAppFn` / `getAppArgs`);
3. `Expr.eqv`: a parameter (2a).

With (1) and (2), `go_unique` gives: the compiler's `go` is `goT exprEqv`.

Unlike unit 1 there is no "`W`" (the compiler's text with only the recursive
part replaced): the recursive call's argument comes out of the array, so the
text cannot be kept and made structural at once.

### 2c. Well-typedness premises

None. `go` inspects constructors only; no expression is typed or reduced.

### 2d. Successful inputs are preserved

```lean
def chainE : List Deco → Nat → List Nat → Nat → Expr   -- the canonical body: levels, then the leaf
def matcherE (m0 m1 m2 : Name × Expr × BinderInfo) (dcs : List Deco) : Expr

theorem walkT_chain : ∀ (dcs : List Deco) (subj : Nat) (vars : List Nat) (depth : Nat),
    ∃ d : LeafData, walkT (chainE dcs subj vars depth) subj vars depth = some d ∧
      d.hIdx = d.depth ∧ d.args = (d.vars ++ [d.subj]).map Expr.bvar ∧
      d.args.length = vars.length + 1 + dcs.length                    -- NO premise

theorem goT_chain (eqv) (hrefl : ∀ i, eqv (.bvar i) (.bvar i) = true) (dcs subj vars depth) :
    goT eqv (chainE dcs subj vars depth) subj vars depth = some (vars.length + 1 + dcs.length)

theorem prodMatcherArityG_canon (eqv) (hrefl) (env n d m0 m1 m2 dcs)
    (hf : env.find? n = some (.defnInfo d)) (hv : d.value = matcherE m0 m1 m2 dcs) :
    prodMatcherArityG eqv env n = some (dcs.length + 1)
theorem prodMatcherArityS_canon …   -- the structural test: NO premise about a test
theorem prodMatcherArityT_canon (hrefl : ∀ i : Nat, ((Expr.bvar i) == (Expr.bvar i)) = true) …
```

`chainE` / `matcherE` are the shape of a pair matcher's value BY READING the
compiler's comment (`fun motive x h => Prod.casesOn x (fun v₁ s₁ => … h v₁ …
sₖ₋₁)`), with every decoration free (`Deco`: levels, the three leading
arguments of `Prod.casesOn`, binder names, types and information). Whether
every matcher the elaborator generates for `let (a, …, z) := x` has exactly
this value is NOT proved (it is the elaborator's output); the sweep measures
it for every constant of the environment through `old`.

NOT stated: the converse (outside the canonical shape the result is `none`
— false in general: `goT` accepts whatever the compiler's text accepts).

## 3. Unit 3: `machInstanceS.inst` (Elab.lean 4084–4087)

Structural as written (the argument list shrinks); `partial` by position.

```lean
def instW : Expr → List Expr → Option Expr            -- the compiler's three clauses, a `def`
def instG (subst : Expr → Expr → Expr) (e : Expr) (args : List Expr) : Option Expr
def instT (e args) := instG inst1 e args              -- inst1 b a = b.instantiate1 a

theorem instW_eq_instT : ∀ (as : List Expr) (e : Expr), instW e as = instT e as
abbrev InstEq (subst) (r) : Prop := ∀ e args, r e args = instStep subst r e args
theorem instG_sol (subst) : InstEq subst (instG subst)
theorem inst_unique (subst) (r) (h : InstEq subst r) : ∀ args e, r e args = instG subst e args
abbrev InstEqW (r) : Prop := ∀ e args, r e args = instStepW r e args   -- the compiler's text as an equation
theorem inst_uniqueW (r) (h : InstEqW r) (e args) : r e args = instW e args

def piDepth : Expr → Nat                              -- leading binders, syntactically
theorem instG_some (subst) (hsub : ∀ b a, piDepth b ≤ piDepth (subst b a)) :
    ∀ (args : List Expr) (e : Expr), args.length ≤ piDepth e → ∃ r, instG subst e args = some r
theorem instG_none_of_not_forall (subst) (e a as) (h : piDepth e = 0) :
    instG subst e (a :: as) = none

-- Tools/ShippingReaderInstTyShadow.lean (imports the compiler)
theorem telescopeKinds_length : ∀ (ty : Expr) (kinds : List MixedGateBinder),
    telescopeKinds ty = some kinds → kinds.length = piDepth ty
theorem instG_callSite (subst) (hsub) (ty kinds args)
    (hk : telescopeKinds ty = some kinds) (hl : args.length = kinds.length) :
    ∃ r, instG subst ty args = some r
```

Here the correspondence is as strong as unit 1's: `InstEqW` IS the compiler's
text (same patterns, same `instantiate1`), so by `inst_uniqueW` the only item
outside the kernel is "the compiled function satisfies its own equation".

Premise of the success theorem: `hsub`, "the substitution does not remove
leading binders". At `instantiate1` (an extern) it is not proved and not
assumed. It is not a typing premise. That the reader's call satisfies `hk` /
`hl` is READ (`instSignatureS?` 4373: `kinds` is `telescopeKinds ci.type`;
`machInstCallS?` 3727: `args.length == kinds.length`), not proved.

## 4. Unit 4: `machBoolMap` (Elab.lean 4819–4837)

Structural as written (the operand of `!` is a pattern subterm); `partial`
because it calls `machLiftScalarN`.

```lean
def machBoolMapT (lift : Lean.Expr → Option (Nat × Lean.Expr)) (dom : Lean.Expr) :
    Lean.Expr → Option Lean.Expr       -- the compiler's text; the two calls of machLiftScalarN are `lift`

theorem machBoolMapT_not (lift dom c us x) :
    machBoolMapT lift dom (.app (.const c us) x) =
      if isNot c then (machBoolMapT lift dom x).bind fun x' => some (complE dom x') else none
theorem machBoolMapT_not_isSome (lift dom c us x) (hc : isNot c = true) :
    (machBoolMapT lift dom (.app (.const c us) x)).isSome = (machBoolMapT lift dom x).isSome
theorem machBoolMapT_nots_isSome (lift dom x) : ∀ cs, (∀ p, p ∈ cs → isNot p.1 = true) →
    (machBoolMapT lift dom (notsE cs x)).isSome = (machBoolMapT lift dom x).isSome
theorem machBoolMapT_not_some / _not_none / _other
-- Tools/ShippingReaderBoolMapLeaf.lean
theorem machBoolMapT_beq_some (lift dom us ty inst x y w x' y')
    (h1 : machBits? ty = some w) (h2 : inst.isAppOf ``instBEqOfDecidableEq = true)
    (hx : lift x = some (w, x')) (hy : lift y = some (w, y')) :
    machBoolMapT lift dom (beqE us ty inst x y) = some (beqOut ty dom w x' y')
```

Correspondence: the text is the compiler's (READ: identical but for
`lift`); no kernel equation with the `partial` function. NOT proved:
uniqueness of the solution of the recursion equation (provable by induction
on the term; not attempted — the fall-through of the three-clause match
needs the case-split technique of unit 2's `Unique` file, and `lift` stays
opaque either way).

Success preservation: the recursive arm is transparent
(`machBoolMapT_nots_isSome`); the equality arm returns under its four tests
(`machBoolMapT_beq_some`), two of which are results of `lift` — at the
compiler's instance, of a `partial` function: premises, not theorems.

STOPPED HERE. Next on the map: `machLiftScalarN` (see §5).

## 5. The reader-progress table

Kinds as in `F-reader-unit.md` §1 (S structural in substance, W measure not
exposed, O recursion through an opaque `Expr` operation, G genuinely
partial). "PROVED" = written here, to be built. "MEASURED": the numbers are
the integrator's; the grep gives the log lines.

| # | function | kind | total counterpart (file) | PROVED about the counterpart | MEASURED (grep) | a switch-over would need | remaining boundary |
|---|---|---|---|---|---|---|---|
| 1 | `MachTupleIn.packTupleInputs` | O | none | — | — | a formulation that recurses on the ORIGINAL lambda body (lift once), then a statement about `liftLooseBVars` / `instantiate1` | the externs |
| 2 | `machNorm` | O + a rewrite that does not decrease | none | — | — | 3, 4, 5, 6 total first; a size measure through `rawNode`'s output | externs; `rawNode` rewriting |
| 3 | `MachRawSurface.projChain` | W | `projChainT` (`Tools/ShippingReaderProjChain.lean`, `…ProjChainFold.lean`) | `tailAt_eq`, `tail_unique`, `projChainT_some`, `projChainT_callSite` (BUILT, `[propext, Quot.sound]`); `projChainW_eq_projChainT`, `projChainP_eq`, `projChainP_callSite` (WRITTEN) | BUILT (F's record): grid 198 calls 0 disagreements; sweep 27964 definitions, 634 with a pair matcher, 1416 sites, 3521 calls, 0 disagreements. `grep -E '^PROJCHAIN (GRID|SWEEP|:)'` | the six lines of `tail` replaced by `tailAt tys`, `partial` removed (a ruling: an edit under `Sparkle/`) | "the compiled `tail` satisfies its equation" — and nothing else |
| 4 | `MachRawSurface.prodMatcherArity?` | S | `prodMatcherArityT` / `prodMatcherArityS` (`Tools/ShippingReaderMatcherArity.lean`, `…Unique.lean`) | `walkT_sol`, `walkT_chain`, `goT_chain`, `prodMatcherArityG_canon`, `…S_canon`, `…G_congr`, `…T_eq_S`; `goT_sol`, `go_unique`, `goT_some_iff`, `leafT_some_iff`, `listEqv_exprEqv`, `headT_eq_getAppFn` | to fill: `grep -E '^PRODARITY (GRID|SWEEP|PIECES|:)'`; misses and differences: `grep -E '^PRODARITY (DISAGREE|STRUCTURAL|MISS|NOT COMPARED)'` | `go` rewritten over a constructor pattern (the text of `walkT` + `leafT`); a decision on the test (`==` kept: no proof obligation changes; structural: needs the hypothesis of `prodMatcherArityT_eq_S`, a ruling) | (1) the compiled `go` satisfies its equation; (2) array form ↔ structural form (`getAppArgs`, private aux); (3) `Expr.eqv` |
| 5 | `machLiftScalarN` | S but one arm (4727) | none | — | — | the `ashr` arm as a non-recursive pre-step; then the text is structural; its callees `machBits?`, `senv.natOf` (`Kernel.whnf`, extern) stay | `senv.natOf`; the size of the function (≈ 170 lines of arms) |
| 6 | `machBoolMap` | S | `machBoolMapT` (`Tools/ShippingReaderBoolMap.lean`, `…BoolMapLeaf.lean`) | `machBoolMapT_not`, `_not_isSome`, `_nots_isSome`, `_not_some`, `_not_none`, `_other`, `_beq_some` | to fill: `grep -E '^BOOLMAP (GRID|SWEEP|:)'`; `grep -E '^BOOLMAP (DISAGREE|MISS|NOT COMPARED)'` | 5 total first (else the callee is still `partial`); then delete the word `partial` | the compiled function satisfies its equation; `machLiftScalarN` |
| 7 | `MachRawSurface.rootFloat` | O | none | — | — | collect the `let`s structurally, lift once; then a statement about `liftLooseBVars` | the externs |
| 8 | `MachRawSurface.zetaAll` | O | none | — | — | as 7, with `instantiate1` | the externs |
| 9 | `machConv` | mutual; S through extraction helpers; `let` arm O | none | — | — | 12's `inst` out of the block; a size measure through `machRunApp?` / `machInstCall?` / `memCall?`; the `let` re-association without recursion on the rebuilt term | externs; the mutual block |
| 10 | `machNested` | mutual, S | none | — | — | with 9 | with 9 |
| 11 | `machInstance` | mutual, not recursive itself | none | — | — | with 9 | with 9 |
| 12 | `machInstanceS` (local `inst`) | mutual; `inst` S on the list | for `inst`: `instT` / `instW` (`Tools/ShippingReaderInstTy.lean`); for `machInstanceS`: none | `instW_eq_instT`, `instG_sol`, `inst_unique`, `inst_uniqueW`, `instG_some`, `instG_none_of_not_forall`, `telescopeKinds_length`, `instG_callSite` | to fill: `grep -E '^INSTTY (GRID|SWEEP|:)'`; `grep -E '^INSTTY (DISAGREE|MISS|NOT COMPARED)'` | `inst` lifted out of the mutual block as a `def` (the text of `instW`) | the compiled `inst` satisfies its equation; `instantiate1` (what it returns) |
| 13 | `machChain` | mutual; `let` arm O | none | — | — | with 9 | with 9 |
| 14 | `machLoopBody` | mutual, S | none | — | — | with 9 | with 9 |
| 15 | `machLoopRoot` | mutual, S through `inlSpine` / `machLetTail` | none | — | — | with 9 | with 9 |

Counts: 4 of 15 have a total counterpart (3, 4, 6, and the local function of
12); 11 have none. NO endpoint premise is removed by any of this: nothing is
wired, and `machineShape?` still calls `partial` functions.

## 6. Build order and `lakefile.lean` lines (for the integrator)

```
lean_lib «Tools.ShippingReaderProjChainFold» where
  roots := #[`Tools.ShippingReaderProjChainFold]

lean_lib «Tools.ShippingReaderMatcherArity» where
  roots := #[`Tools.ShippingReaderMatcherArity]

lean_lib «Tools.ShippingReaderMatcherArityUnique» where
  roots := #[`Tools.ShippingReaderMatcherArityUnique]

lean_lib «Tools.ShippingReaderSweepCommon» where
  roots := #[`Tools.ShippingReaderSweepCommon]

lean_lib «Tools.ShippingReaderMatcherArityShadow» where
  roots := #[`Tools.ShippingReaderMatcherArityShadow]

lean_lib «Tools.ShippingReaderInstTy» where
  roots := #[`Tools.ShippingReaderInstTy]

lean_lib «Tools.ShippingReaderInstTyShadow» where
  roots := #[`Tools.ShippingReaderInstTyShadow]

lean_lib «Tools.ShippingReaderBoolMap» where
  roots := #[`Tools.ShippingReaderBoolMap]

lean_lib «Tools.ShippingReaderBoolMapLeaf» where
  roots := #[`Tools.ShippingReaderBoolMapLeaf]

lean_lib «Tools.ShippingReaderBoolMapShadow» where
  roots := #[`Tools.ShippingReaderBoolMapShadow]
```

The three tests are under `Tests/Compiler/` (the `Tests` library); they are
TARGET-ONLY (each imports `Tests.AllTests`) and are not added to it.

Order (each independent of the later ones; the light ones first):

1. `Tools.ShippingReaderProjChainFold` (imports unit 1 only). Then
   `#print axioms` of `projChainW_eq_projChainT`, `projChainP_eq`.
2. `Tools.ShippingReaderMatcherArity` (imports `Lean`). `#print axioms` of
   `walkT_chain`, `prodMatcherArityG_canon`, `prodMatcherArityT_eq_S`.
3. `Tools.ShippingReaderInstTy` (imports `Lean`). `#print axioms` of
   `inst_uniqueW`, `instG_some`.
4. `Tools.ShippingReaderMatcherArityUnique` (fragile; independent of 5–9).
   `#print axioms` of `go_unique`.
5. `Tools.ShippingReaderSweepCommon`, `Tools.ShippingReaderMatcherArityShadow`,
   then `Tests.Compiler.ReaderMatcherArityShadowTest` (keep the `PRODARITY`
   lines).
6. `Tools.ShippingReaderInstTyShadow` (imports the compiler), then
   `Tests.Compiler.ReaderInstTyShadowTest` (`INSTTY`).
7. `Tools.ShippingReaderBoolMap` (imports the compiler).
8. `Tools.ShippingReaderBoolMapLeaf` (fragile; nothing depends on it).
9. `Tools.ShippingReaderBoolMapShadow`, then
   `Tests.Compiler.ReaderBoolMapShadowTest` (`BOOLMAP`).

PREDICTED axioms: `propext`, `Quot.sound` for 1–3 (`omega`, `funext`); for
4, 6, 8 possibly also `Classical.choice` (`simp`, `split`, `simp_all`).

## 7. PREDICTED log lines

```
PRODARITY START grid (0 to 6 levels, the canonical body and eleven variants)
PRODARITY GRID: calls=79 old returned=7 disagreements=0 structural test differs=0 prediction misses=0 pieces nodes=<n> pieces disagreements=0
PRODARITY START collect (every constant of the environment)
PRODARITY COLLECT: constants=<n>
PRODARITY START constants from 0            (then every 20000)
PRODARITY HIT <constant under the roots>: arity=some <k>
PRODARITY SWEEP: constants=<n> old returned=<h> under the roots=<r> disagreements=0 structural test differs=0 arities 0=0 1=<…> 2=<…> … 9=<…>
PRODARITY START pieces (the definitions under the roots that use a pair matcher)
PRODARITY START pieces <declaration>
PRODARITY PIECES: definitions=<m> nodes=<n> disagreements=0 not compared=0
PRODARITY: grid agree=T sweep agree=T pieces agree=T structural test agree=T

INSTTY START grid (60 calls: binders against arguments, mdata, a lambda, exposed binders)
INSTTY GRID: calls=60 old returned=27 disagreements=0 prediction misses=0
INSTTY COLLECT: definitions=<n>
INSTTY START <declaration>
INSTTY DECL <declaration>: real sites=<n> wide sites=<n>
INSTTY SWEEP: definitions=<n> with a hardware module=<m> real sites=<s> wide sites=<w> old returned=<…> disagreements=0 not compared=0
INSTTY: grid agree=T sweep agree=T real call sites compared=<s>

BOOLMAP START grid (27 bodies: six bases under 0 to 3 nots, three more wrappers)
BOOLMAP GRID: calls=27 old returned=4 disagreements=0 prediction misses=0
BOOLMAP COLLECT: definitions=<n>
BOOLMAP START <declaration>
BOOLMAP DECL <declaration>: sites=<n> Bool sites=<n>
BOOLMAP SWEEP: definitions=<n> with a map=<m> sites=<s> Bool sites=<b> old returned=<…> disagreements=0 not compared=0
BOOLMAP: grid agree=T sweep agree=T sites compared=<s>
```

Counted from the texts: `79` = 7 canonical + 6 leaf variants × 7 + 5 level
variants × 6; `7` = the canonical bodies; `60` = 48 + 4 + 3 + 5; `27` (INSTTY
returned) = 21 + 1 + 1 + 4; `27` (BOOLMAP calls) = 6 × 4 + 3; `4` = the first
base under 0 … 3 `!`. `<n>` of `COLLECT: definitions` is unit 1's set (27964
in F's run, if the environment is the same). Everything else in `<…>` is not
predicted.

The ONE conditional prediction: the seven `mdata` rows of the `PRODARITY`
grid are refused if `Expr.eqv` does not look through `mdata`. If it does:
`old returned=14 … structural test differs=7 prediction misses=7`, with
`disagreements=0` still (the candidate `T` uses the same `==`), and the
command does not throw. That outcome is a finding about the extern.

## 8. Risks, in order

1. **`projChainW_form` (`rfl` on the `do` block).** If the elaborator's
   output is not what was READ, the four alternatives after `rfl` may fail
   too. Fix: `#print projChainW`, adapt `loopBody` / `finStep` to the term;
   every later lemma uses their statements only.
2. **Structural recursion of `walkT`** (a deep pattern inside the catch-all
   arm of a `match` on `headT e`; `termination_by structural e`) and of
   `machBoolMapT` (name-literal patterns). If `walkT` is refused: move the
   `match headT e` inside. `walkT_sol` relies on `walkT.eq_def`.
3. **The compiled local functions as constants**:
   `Sparkle.Compiler.MachRawSurface.prodMatcherArity?.go : Expr → Nat → List
   Nat → Nat → Option Nat` and `Sparkle.Compiler.Elab.machInstanceS.inst :
   Expr → List Expr → Option Expr` (PREDICTED names and types: neither uses a
   variable of its enclosing definition). If one has more parameters, `oldGo`
   / `oldInst` need them; if `inst` is not reachable, drop `old` from that
   shadow (then it compares `W` and `T` only — a kernel theorem already).
4. **`Tools/ShippingReaderMatcherArityUnique.lean`**: `casesArm_congr` and
   `casesArm_bind` (`unfold casesArm; repeat' split; all_goals first | …`),
   written without seeing a goal; the `sizeOf` goal after `apply h`
   (`Lean.Expr.app.sizeOf_spec`, `Lean.Expr.lam.sizeOf_spec`, `omega`);
   `leafT_some_iff` (`cases … <;> simp`); `headT_eq_getAppFn` (it needs the
   body of `Expr.getAppFn`, a non-exposed `def` of a `module`, to unfold in a
   file that is not a module — PREDICTED visible; if not, delete the theorem
   and move the link to "measured").
5. **Blind `simp`**: `machBoolMapT_beq_some`; `telescopeKinds_length`
   (`absurd h' (by simp)`).
6. **Term-mode chains** (`congrArg … |>.trans`): each relies on a
   definitional unfolding at the join (`pair2`, `Option.bind` at `some`,
   `stepH` at a constructor). The pattern is unit 1's, which built.
7. **Cost of the tests**: `PRODARITY` calls three functions on EVERY constant
   of the environment and scans the definitions that use a pair matcher;
   `INSTTY` scans every node of the definitions that use a hardware module;
   none measured. Use the cgroup runner.
8. `natBne_self` (`bne_self_eq_false`), `List.Mem.head` / `.tail`,
   `Option.bind_eq_some_iff`, `MData.empty`, `Array.modify` — names READ in
   the toolchain's sources.

## 9. NOT determined by reading

* Whether any file elaborates.
* Every `<…>` of §7; whether `real sites` of `INSTTY` and `Bool sites` of
  `BOOLMAP` are positive in the suite's environment.
* Whether `Expr.eqv` looks through `mdata`, and more generally whether
  `a == .bvar i` holds only for `a = .bvar i` (the runtime's C++ source is
  not in the tree).
* Whether every pair matcher the elaborator generates has the value
  `matcherE …` (the shape of `walkT_chain`); the sweep shows which constants
  `old` accepts, not their shape.
* Whether ``` ``not ``` and ``` ``Bool.not ``` resolve in the new files as
  in `Elab.lean` (same text; a difference would show in `BOOLMAP GRID`).
* Whether a non-`module` file sees the bodies of the non-exposed definitions
  of `Lean/Expr.lean` (risk 4).

## Integrator's build record (2026-10-14) — MEASURED

BUILT on poc cfe107ab + these files, cgrun 3 GiB swap 0, run `h1` (exit 0, peak 0.86 GB), worker's files
UNCHANGED, FIRST ATTEMPT: all ten `Tools/ShippingReader*` files and the three shadow tests (target-only).
Axioms (`#print axioms`, run `h1ax`): `projChainW_eq_projChainT`, `projChainP_eq`,
`prodMatcherArityG_canon` — `[propext, Classical.choice, Quot.sound]`; `go_unique`, `goT_chain`,
`instG_callSite`, `machBoolMapT_beq_some` — `[propext, Quot.sound]`; `instW_eq_instT`, `inst_unique`,
`machBoolMapT_nots_isSome` — `[propext]`.

Shadow comparisons over the AllTests environment (compiled old function vs the total counterparts):
```
PRODARITY GRID: calls=79 old returned=7 disagreements=0 structural test differs=0 prediction misses=0 pieces nodes=3341 pieces disagreements=0
PRODARITY PIECES: definitions=638 nodes=442777 disagreements=0 not compared=0
PRODARITY SWEEP: constants=260090 old returned=1890 under the roots=592 disagreements=0 structural test differs=0
INSTTY GRID: calls=60 old returned=27 disagreements=0 prediction misses=0
INSTTY SWEEP: definitions=28070 with a hardware module=269 real sites=673 wide sites=110212 old returned=110824 disagreements=0 not compared=0
BOOLMAP GRID: calls=27 old returned=4 disagreements=0 prediction misses=0
BOOLMAP SWEEP: definitions=28072 with a map=447 sites=2751 Bool sites=40 old returned=10 disagreements=0 not compared=0
```
(The conditional prediction about `mdata` came out on the "does not look through" side: old returned=7,
structural test differs=0.)

Reader progress: 4 of the 15 `partial` functions on the machine reader's path have a total counterpart
(`projChain`, `prodMatcherArity?`, `machInstanceS.inst`, `machBoolMap`). For `projChain` and
`machInstanceS.inst` the compiler's own text form is kernel-equal to the structural definition and the
recursion equation has a unique solution, so the only item outside the kernel is "the compiled `partial`
function satisfies its own source equation". NOTHING is wired into the compiler; the reader is unchanged;
no endpoint lost its reflection premise (`MachineDefines`). Agreement with the compiled functions is
MEASURED, not proved.
