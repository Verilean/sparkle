# Reader generalisation, first unit: the `partial` group mapped, one function made total

Branch `par/f-1` (base poc `f1ed620f` + the finding-I candidate files).
**WRITTEN, NOT BUILT.** Nothing here was compiled or run. "READ" = read in
the tree of this branch; line numbers are of that tree. "PREDICTED" = from
reading. Earlier record of the same goal: `docs/parallel/G3-reader.md`
(strict term reader, shadow-only by ruling) — not repeated, not extended.

Ruling this unit answers (2026-10-14, item 5): prefer reader generalisation
to more examples; from the dependencies of the `partial` group pick the
smallest function that can be made structural / total; state the
correspondence old ↔ new, the well-typedness premises, and the obligation
that successful inputs are preserved; no fixed fuel bound, no strict reader
in place of the reader; where no kernel equation with the old `partial`
exists, do not close it with an axiom — report the boundary and the
validation; do not replace the seven functions at once.

What is NOT done here: the reader is not replaced, not edited, not narrowed;
no strict reader; no file under `Sparkle/` is touched.

## 1. The `partial` group

`machineShape?` (`Sparkle/Compiler/Elab.lean` 5058) is the reader: a pure
function (`Option MachineShape`, no `MetaM`) of the entry constant and the
structure facts `StructEnv`. Every endpoint carries
`MachineDefines … f f.machineData.shape` (`Tools/ShippingMachineEntry.lean`
2261) because `machineShape?` calls `partial` functions: a `partial def` is
an opaque constant for the kernel (its body is attached by
`implemented_by`), so `machineShape? … = some shape` cannot be evaluated or
unfolded in a proof.

NONE of the functions below is monadic in `MetaM`, and none calls `whnf` of
the elaborator. (`senv.natOf` = `kernelNat`, Elab 4328, calls
`Lean.Kernel.whnf` — an extern, opaque to proofs, but not `partial`.)

Why a function is `partial` — four different reasons:

* **(S)** structural in substance: every recursive call is on a proper
  subterm (or a smaller list / fuel), but not in a form the equation
  compiler sees (subterms taken through `getAppFn` / `getAppArgs` array
  patterns, a `let rec` inside a `partial def`, a `do` block);
* **(W)** terminating by a measure the text does not expose;
* **(O)** the recursive call is on the result of an OPAQUE `Lean.Expr`
  operation (`instantiate1`, `liftLooseBVars`, `lowerLooseBVars`, `beta` —
  `@[extern] opaque` in `Lean/Expr.lean`): it terminates, but no measure of
  the argument can be proved in the kernel;
* **(G)** genuinely not terminating on every `Lean.Expr`: only on
  well-typed ones (beta reduction), or bounded by fuel the compiler already
  has.

### 1a. On the path of `machineShape?`

| function | file:line | recurses on | called by | calls (partial) | why partial |
|---|---|---|---|---|---|
| `MachTupleIn.packTupleInputs` | `MachTupleIn.lean` 79 | the body of a `.lam`, AFTER `(b.liftLooseBVars 1 1).instantiate1 …` | `machineShape?` 5064 | — | (O) |
| `machNorm` | `Elab.lean` 4956 | `f`, `a`, lambda body (subterms); the OUTPUT of `rawNode` (4971); `b.instantiate1 v` (4977, 4980) | `machineShape?` 5076 | via `rawNode` (a `def`): `projChain`; via `machNormNode` (a `def`): `machLiftScalarN`, `machBoolMap` | (O), and 4971 is a rewrite that is not size-decreasing (a `forM` over a literal list is expanded, a matcher becomes `let`s) |
| `MachRawSurface.projChain` (local `tail`) | `MachRawSurface.lean` 56 (59–64) | `i + 1` | `rawNode` 160 | — | **(W)**: stops because `tys[i + 1]? = some _`; no `Expr` inspected |
| `MachRawSurface.prodMatcherArity?` (`go`) | `MachRawSurface.lean` 26 (39–51) | `rest`, a subterm of `e` taken by an `#[…]` pattern on `e.getAppArgs` | `structEnv` 4385 (`senv.prodMatch`) → `rawNode` 139 | — | (S); its last test is `==` on `Expr` (`Expr.eqv`, extern) |
| `machLiftScalarN` | `Elab.lean` 4640 | the operands `x`, `y` (pattern subterms); ONE arm (4727) on a term it builds (`ashr` → `sshiftRight … toNat`) | `machNormMap`, `machNormApLift`, `machBoolMap` | itself | (S) but for the one rewriting arm |
| `machBoolMap` | `Elab.lean` 4819 | `x` (pattern subterm) | `machNormMap` 4899 | `machLiftScalarN` | (S) |
| `MachRawSurface.rootFloat` | `MachRawSurface.lean` 210 | the body of a `let`; a `let` it re-associates (212–213, built with `liftLooseBVars`); `.app (f.liftLooseBVars 0 1) b` (217) | `machineShape?` 5074, `machConv` 3985, `machChain` 4143 | — | (O) |
| `MachRawSurface.zetaAll` | `MachRawSurface.lean` 231 | `b.instantiate1 v`; `f`, `a` | `machReserve` 3700, 3702 | — | (O) |
| `machConv` | `Elab.lean` 3883 | subterms `f`, `a`, binder type and body; a re-associated `let` (3987–3988); `dom`, `x` of a register taken by `getAppArgs` | `machineShape?` 5100, 5113, 5129; the six below | all seven | mutual; (S) through extraction helpers (`machRunApp?`, `machInstCall?`, `memCall?` return subterms as values, not as patterns); the `let` arm (O) |
| `machNested` | 4015 | `body` (handed over by `machRunApp?`) | `machConv` 3938 | `machConv`, `machChain` | mutual, (S) through `machRunApp?` |
| `machInstance` | 4044 | the argument list (a `foldlM`) | `machConv` 3942, 3953 | `machConv` | mutual; not recursive itself |
| `machInstanceS` (local `inst`) | 4078 (4084–4087) | the argument list; `inst` on `b.instantiate1 a` with the LIST shrinking | `machConv` 3946 | `machConv` | mutual; `inst` is (S) on the list |
| `machChain` | 4123 | `rest`, `b` (pattern subterms); a re-associated `let` (4145–4146) | `machineShape?` 5123, `machNested` 4026, 4035 | `machConv`, `machLoopRoot`, itself | mutual; the `let` arm (O) |
| `machLoopBody` | 4170 | the body `b` of a `let` | `machLoopRoot` 4210, 4228 | `machConv`, itself | mutual, (S) |
| `machLoopRoot` | 4192 | `body` taken by `inlSpine e []` | `machineShape?` 5108, `machConv` 3992, `machChain` 4150 | `machConv`, `machLoopBody` | mutual, (S) through `inlSpine` / `machLetTail` |

Dependency order (an arrow: "calls"):

```
machineShape? ─► packTupleInputs
              ─► machNorm ─► rawNode(def) ─► projChain            ◄── leaf
              │           │              └► senv.prodMatch = prodMatcherArity?   ◄── leaf
              │           └► machNormNode(def) ─► machBoolMap ─► machLiftScalarN
              ─► rootFloat                                         ◄── leaf
              ─► machConv ⇄ machNested ⇄ machChain ⇄ machLoopRoot ⇄ machLoopBody,
                 machInstance, machInstanceS        (ONE mutual block, 3873–4232)
                    └► rootFloat, machReserve(def) ─► zetaAll      ◄── leaf
```

### 1b. Before the reader (the entry constant: `entryConst`, `userInliner` 3385)

`MachRecUnfold.lean`: `headBetaM` 54 (G: `f.beta` loops on an ill-typed
redex), `betaAll` 142 (G), `iota` 62 and `reduceHead` 127 (fuelled by the
COMPILER already — 256 and 64 — and `partial` only because `fuel - 1` is not
a pattern; they call `headBetaM`), `listLit?` 172 ((O): `b.instantiate1 v`;
the rest (S)), `passM` 243 (G: it unfolds user recursion while literal data
lasts; memoised in a `StateM`), `relevantClosure` 283 (its `go` is ALREADY
structural on a fuel of 100000 that the compiler has; `partial` only by
position). `Elab.lean` 2077 `stripMemoizeWrappers` ((S); the legacy arm, not
the machine reader).

### 1c. Not the compiler

`Tools/ShippingMachineCommand.lean`: `unq` 91 and eleven more `partial`
functions of the endpoint GENERATOR (`readMachine` 418 calls
`machineShape?` and `unq`). Unchecked by design: what they produce is
kernel-checked per declaration. Out of scope.

## 2. The choice: `MachRawSurface.projChain`

It is the smallest function of 1a that can be made total with the same
result on EVERY input:

* a leaf: it calls no other `partial` function;
* 18 lines; its only recursion is the six-line local `tail`;
* reason (W): no `Lean.Expr` is inspected and no opaque `Expr` operation is
  called — the arguments are used as opaque pieces (`mkApp2`, `mkApp3`,
  list indexing). Every lemma about it is a fact about lists and `Nat`;
* the total definition needs no fuel and no bound.

The other leaves, and why not first:

| leaf | why not the first |
|---|---|
| `prodMatcherArity?` | (S), a structural rewrite exists (nested `.app` patterns for the five `Prod.casesOn` arguments). But its acceptance test `args.toList == expected.map Expr.bvar` is `Expr.eqv`, an extern: a structural definition must either keep the opaque `==` (nothing provable about that test) or compare bound-variable indices directly (then "the same result" is a statement about the extern). The NEXT unit, with that boundary. |
| `rootFloat`, `zetaAll`, `packTupleInputs` | (O): the recursion goes through `liftLooseBVars` / `instantiate1`; no termination measure is provable in the kernel. They need a reformulation that recurses on the ORIGINAL term (e.g. collect the `let`s structurally, lift once), and the equality of results is then a statement about the externs. |
| `relevantClosure` | already structural; the change is to delete the word `partial` — an edit under `Sparkle/`, on the entry path, not the reader. |

What depends on `projChain`: `rawNode` (a `def`) → `machNorm` →
`machineShape?` → every `MachineDefines`. It is reached only for a body
written on the raw `runCircuitH` surface with `let (r₀, …, rest) := regs`.

## 3. What is implemented

`Tools/ShippingReaderProjChain.lean` (imports `Lean` only; namespace
`Tools.ShippingReaderProjChain`):

```lean
def tailTy : List Expr → Option Expr          -- structural on the list
def tailAt (tys : List Expr) (i : Nat) : Option Expr := tailTy (tys.drop (i + 1))
def chainGo (last : Bool) (cur : Expr) (ts : List Expr) (j : Nat) : Option Expr   -- structural on j
def projChainT (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool) : Option Expr :=
  chainGo last regs tys j
def projChainW …   -- the compiler's text, its local `tail` replaced by `tailAt tys`
```

### 3a. Correspondence old ↔ new (the strongest obtainable)

**No kernel equation with `MachRawSurface.projChain` can be proved**: it is
`partial`, an opaque constant. None is assumed (no axiom, no `sorry`, no
`native_decide`). Proved instead, about the only recursive part:

```lean
abbrev TailEq (tys : List Expr) (tail : Nat → Option Expr) : Prop :=
  ∀ i : Nat, tail i =
    if i + 1 == tys.length - 1 then tys[tys.length - 1]?
    else (tys[i + 1]?).bind fun a => (tail (i + 1)).bind fun b => some (prodE a b)

theorem tailAt_eq (tys : List Expr) : TailEq tys (tailAt tys)                 -- existence
theorem tail_unique (tys : List Expr) (tail : Nat → Option Expr)
    (h : TailEq tys tail) : ∀ i : Nat, tail i = tailAt tys i                   -- uniqueness
```

`TailEq` is the source text of the compiler's `tail` (MachRawSurface 59–64;
its `do` block is these two binds of `Option`). So: the compiler's equation
has exactly one solution, and it is the total function.

The BOUNDARY, precisely:

1. "the compiled `tail` satisfies its own source equation" — the meaning of
   `partial`; not a kernel statement, not provable, not assumed;
2. the rest of `projChain` (a fold over `[0:j]`, two binds) is not
   recursive: with (1) and `tail_unique`, the compiler's function is
   `projChainW` by reading — the same text;
3. `projChainW = projChainT` (the range fold against the structural
   recursion) is a kernel statement that is NOT proved here; both are total
   definitions, so it is provable (it needs the unfolding of `forIn` over a
   `Std.Range` in the `Option` monad). MEASURED only (below).

### 3b. Well-typedness premises

None. The lemmas need a length fact only. `projChain` never inspects an
expression, so no premise about the typing of `regs` or `tys` enters.
(The first functions where one WOULD enter are `headBetaM` / `betaAll`:
their termination is normalisation of well-typed terms, and the development
has no typing judgment for `Lean.Expr` — `G3-reader.md` §3.)

### 3c. Successful inputs are preserved

Stated about the NEW definition:

```lean
def Accepts : Bool → Nat → Nat → Prop
  | true, n, j => j = 0 ∨ j + 1 ≤ n
  | false, n, j => j + 2 ≤ n

theorem projChainT_some (regs : Expr) (tys : List Expr) (j : Nat) :
    ∀ (last : Bool), Accepts last tys.length j → ∃ r, projChainT regs tys j last = some r

theorem projChainT_callSite (regs : Expr) (tys : List Expr) (j : Nat) (hj : j < tys.length) :
    ∃ r, projChainT regs tys j (j + 1 == tys.length) = some r
```

`Accepts` is the set of inputs on which the compiler's function returns a
result, BY READING its text (with `last`: no projection, or `j` `snd`s over
at least `j + 1` components; without: `j` `snd`s and a `fst` over at least
`j + 2`). `projChainT_callSite` is the reader's own use: `rawNode` calls it
for component `j < k` of the `k = tys.length` binders of a pair matcher, with
`last = (j + 1 == k)` (MachRawSurface 160–164) — the total function returns
a result at EVERY such call, a theorem with no premise about the source.

NOT stated: the converse (outside `Accepts` the total function returns
`none`), and the equality of the RESULTS with the old ones. Both are
measured: the grid compares `isSome` of the old and of the new function with
`acceptsB`, and the results with `Expr.equal`.

Acceptance is not narrowed by construction: the reader does not call any of
this.

## 4. Validation that does not narrow acceptance

`Tools/ShippingReaderProjChainShadow.lean`: the command
`#reader_projchain_shadow` runs, by compiled code, `old`, `projChainW` and
`projChainT` and compares results with `Expr.equal`:

* GRID — every `(length, j, last)`, length `0 … 8`, `j` `0 … 10`: 198
  inputs over distinct marker constants, accepted and refused alike; also
  `isSome` = `acceptsB` for the old and the new function. Since the function
  uses its expression arguments as opaque pieces (READ), its behaviour is a
  function of these three numbers.
* SWEEP — every definition of the environment under `Sparkle`, `Tests`,
  `IP`, `Examples`, `Tools`: at each pair-matcher node (the nodes where
  `rawNode` calls `projChain`) the arguments are computed as `rawNode` does
  (a copy of eleven lines) and the three functions compared per component;
  and the `j`-th `let` value of the REAL `rawNode`'s result is compared with
  `projChainT` — which checks the copy as well.

The sweep never throws (an exception while scanning a declaration is logged
`NOT COMPARED`); the command throws only on a measured disagreement.

`Tests/Compiler/ReaderProjChainShadowTest.lean` — TARGET-ONLY (it imports
`Tests.AllTests`): the command over the suite's environment.

PREDICTED lines:

```
PROJCHAIN START grid (lengths 0 to 8, j 0 to 10, both values of last)
PROJCHAIN GRID: calls=198 old returned=65 disagreements=0
PROJCHAIN START collect (…)
PROJCHAIN COLLECT: definitions=<n>
PROJCHAIN START Sparkle.Tests.RunCircuitHTest.counterH
PROJCHAIN DECL Sparkle.Tests.RunCircuitHTest.counterH: sites=1 calls=2
…
PROJCHAIN SWEEP: definitions=<n> with a pair matcher=<m> sites=<s> calls=<c> old returned=<c> disagreements=0 not compared=0
PROJCHAIN: grid agree=T sweep agree=T real call sites compared=<s>
```

(`65` = 37 with `last` + 28 without, counted from `Accepts`. `<m>`, `<s>`,
`<c>` are not predicted; the six `regs`-destructuring declarations of
`Tests/RunCircuitHTest.lean` are in the suite's environment. At a real site
every call returns, so `old returned` = `calls` there.)

## 5. What a later switch-over would need (NOT done)

1. A compiler edit (ruling needed): `tailTy` in a small file under
   `Sparkle/Compiler/`, the six lines of `tail` in `projChain` replaced by
   `tailAt tys`, the word `partial` removed — i.e. `projChainW`. By
   `tail_unique` this changes no result, modulo boundary (1).
2. Then `projChain` unfolds in the kernel; `projChain = projChainT` (item 3
   of §3a) becomes a provable theorem and `projChainT_callSite` transfers.
3. The measured agreement (this test, green) and the usual text comparison
   (`compare_outputs.py`) before and after.

What it buys alone: one `partial` fewer, and a pattern. It removes NO
endpoint premise: `rawNode` still calls `liftLooseBVars` / `lowerLooseBVars`
/ `beta` (externs), and `machNorm` above it is still `partial`.

## 6. The NEXT function, and the order after it

1. `prodMatcherArity?` (the other leaf under `rawNode`): structural `go`
   over nested `.app` patterns. Boundary to decide first: keep `==` on
   `Expr` (opaque) or test the bound-variable indices structurally. After
   it, `rawNode` calls no `partial` function.
2. `machInstanceS.inst` (structural on the list as written — lift it out of
   the mutual block as a `def`), `machBoolMap`, `machLiftScalarN` (isolate
   the one arm that recurses on a built term: translate `ashr` in a
   non-recursive pre-step).
3. `rootFloat`, `zetaAll`, `packTupleInputs`: need a formulation that does
   not recurse on the result of an extern; the agreement with the present
   ones is then a statement about `instantiate1` / `liftLooseBVars`
   (measured, or trusted as "the externs implement substitution").
4. `machNorm`, then the mutual block: a size measure through the extraction
   helpers (`machRunApp?`, `inlSpine`, `machLetTail` return subterms) and a
   `let` re-association that does not recurse on the rebuilt term. Not
   before 1–3.

Fuel: `iota` / `reduceHead` / `relevantClosure` carry fuel the COMPILER
already has (256, 64, 100000); a total version must keep exactly those
numbers (the same refusals), not add any.

## 7. Risks

* The proofs are blind. Most fragile: `tailAt_eq` and `tail_unique` (`rw`
  chains with `if_pos` / `if_neg`, then `all_goals exact …` / `all_goals
  rfl` in case `rw` closes the goal itself); the typed `have h' : … := h`
  steps (they rely on `[].length`, `[a].length`, `(a :: b :: l).length`
  reducing by `whnf`); `chainGo_step` (a `trans` chain whose last step is a
  beta step); `intro i` through the `abbrev TailEq`.
* `drop_cases` relies on `List.drop_nil`, and on `rfl` for
  `(x :: xs)[0]?`, `(x :: xs)[n + 1]?`, `[][n]?` and `drop (n + 1) (x :: xs)`
  (each is `rfl` in the core library of Lean 4.32.1, READ).
* The shadow: `Expr.forEach`, `env.constants.fold`, `getModuleIdxFor?`,
  `Expr.equal`, `List.zipIdx` as used elsewhere in the tree; the `elab`
  command lifts `MetaM` into `TermElabM`.
* Cost of the test: it imports `Tests.AllTests` and calls
  `getUsedConstants` on every definition under the five roots (not
  measured).
* The sweep's site computation is a copy of `rawNode`'s; if the copy were
  wrong the comparison with the real `rawNode`'s `let` values fails loudly
  (a false disagreement, not a false agreement).

## 8. Build order and `lakefile.lean` lines (for the integrator)

```
lean_lib «Tools.ShippingReaderProjChain» where
  roots := #[`Tools.ShippingReaderProjChain]

lean_lib «Tools.ShippingReaderProjChainShadow» where
  roots := #[`Tools.ShippingReaderProjChainShadow]
```

1. `lake build Tools.ShippingReaderProjChain` (imports `Lean` only), then
   `#print axioms` of `tailAt_eq`, `tail_unique`, `projChainT_some`,
   `projChainT_callSite` (PREDICTED: `propext`, `Quot.sound` at most —
   `omega`).
2. `lake build Tools.ShippingReaderProjChainShadow` (imports
   `Sparkle.Compiler.MachRawSurface`).
3. `lake build Tests.Compiler.ReaderProjChainShadowTest` — target-only, NOT
   in `Tests/AllTests.lean`; keep the `PROJCHAIN` lines.

## 9. NOT determined by reading

* Whether the files elaborate.
* The number of real call sites in the suite's environment, and whether any
  is outside `Tests/RunCircuitHTest.lean`, `ShippingMachineRawTest`,
  `LeafSweepRawTest`.
* Whether `Expr.equal` (binder names count) is the right strictness for the
  `W` / `T` comparison — the three functions build the same applications
  from the same pieces, so equality is PREDICTED under either comparison.
* Whether the structural-recursion elaborator accepts `tailTy` and
  `chainGo` as written (if it falls back to well-founded recursion the
  `rfl` equation lemmas fail; the definitions stay total either way).

## Integrator's build record (2026-10-14) — MEASURED

BUILT on poc after 826418d3, cgrun 3 GiB swap 0, runs `f-reader`, `f-reader2`, `f-reader3`.
Integrator fixes (no statement changed): `chainGo_zero_true` is not `rfl` (the recursion is structural on
the list, so the equation at index 0 needs `cases ts`), and its one use; two pushed `s!` strings inside
`{ t with disagree := … }` needed parentheses (parse error).
Axioms (`#print axioms`): `tailAt_eq`, `tail_unique`, `projChainT_some`, `projChainT_callSite` —
`[propext, Quot.sound]` (no `Classical.choice`).
Shadow comparison (`ReaderProjChainShadowTest`, target-only, imports AllTests): see the PROJCHAIN lines
quoted in the commit message / log of run `f-reader3`.
STATE: `projChain` has a total counterpart `projChainT` (not wired into the compiler), with existence and
uniqueness of the compiler's own recursion equation and success on every call site's argument shape
proved; agreement with the compiled `partial` function is MEASURED (grid + environment sweep), not
proved — no kernel equation with a `partial def` exists, and none is assumed. The reader is unchanged;
no endpoint lost its reflection premise.
