# R-4 — replacing the partial machine reader by a total one without shrinking acceptance

Worker B (reader coverage), branch `par/r-4` from poc `c1c651a0`. Docs plus one
generic Lean file, `Tools/ReaderFuelGeneric.lean` (UNVERIFIED: not built;
core only, no `sorry` / axiom / `native_decide`; not in `lakefile.lean`).
No compiler change. Worker A owns the fuel-indexed definitions; this document
only states what they must satisfy and what can then be proved.

Line numbers: `Sparkle/Compiler/Elab.lean` at `c1c651a0` unless a file is named.

## 0. Summary

* **Option (i), a measure computable from the input, is not available in the
  kernel.** 41 of the 51 recursive call sites (34 of 41 in the block, 7 of 10 in
  `machNorm`) pass a strict subterm of the input, and a `sizeOf` measure would
  work for those. The others pass terms built by `opaque` primitives
  (`Expr.instantiate1`, `Expr.liftLooseBVars`, `Expr.beta`) or by other
  `partial` functions (`rootFloat`, `rawNode`'s callees). Those terms have no
  provable size. `machInstanceS` (4105–4107) reads terms that come from the
  **environment** (`senv.instS`), so no measure of the input can bound them
  even outside the kernel.
* **Recommended route: (ii) + (iii).** Fuel iteration of the same body with
  a three-valued result `ok / fail / out`. The kernel proves:
  * monotonicity and fuel independence, so the certificate is just a number `n`;
  * soundness against the old reader, under the old reader's own source
    equation as a hypothesis (`IsFix`). That hypothesis is never an axiom.

  A compiler-side driver doubles the fuel on `out` and never turns `out` into
  `none`/legacy. The derivation relation of (iii) is
  `Reads c r := ∃ n, F n c = ofOpt r`, the least fixpoint. A separate
  per-arm inductive adds nothing that induction on `n` does not already give.
* **What the kernel can never give** (`fixpoint_not_complete`, proved
  generically): "the old reader returned `some r` ⟹ some fuel returns
  `.ok r`". The fixpoint equation does not imply it. It is a fact about the
  compiled `partial` code (it computes the least fixpoint where it
  terminates), and only shadows can measure it. This is coverage obligation
  **O1** (§5).

## 1. Recursive call sites

Measure candidate notation: `|e|` is `sizeOf e` (Lean's structural size on
`Lean.Expr`: `|app f a| = 1 + |f| + |a|`). A callee's measure is the `sizeOf` of
the expression(s) it reads, with `List.sizeOf` for argument lists
(`sizeOf [a] = 2 + |a|`, so `machInstance` → `machConv a` still decreases).
"kernel ✓" means a lemma about a non-`partial`, transparent helper is enough.
"✗" means no syntactic measure the kernel can see.

### 1.1 `machConv` (3884)

| line | call | argument | measure? |
|---|---|---|---|
| 3922 | `machConv dom` | `dom` from `e.getAppArgs` = `#[dom, α, init, x]` of a `Signal.register` | kernel ✓ (`getAppArgs` element < `e`) |
| 3931 | `machConv x` | `x`, same spine | kernel ✓ |
| 3939 | `machNested dom αs initsE body` | `machRunApp?` (3671): `inlSpine` arguments, `body` under the `.lam` | kernel ✓ (`inlSpine` lemma; the sum of the four is < `|e|`) |
| 3943 | `machInstance … args` | `machInstCall?` (3717): `inlSpine` args | kernel ✓ (`sizeOf args < |e|`: the head `const` has size ≥ 3) |
| 3947 | `machInstanceS … ty args` | args as above; `ty` from `senv.instS c` (environment) | edge ✓ (args); see S2 |
| 3954 | `machInstance … (dom :: ops)` | `memCall?` (`MachMemory.lean` 25): `getAppArgs` `a[0]!, a[3..6]!` under `isAppOfArity … 7` | kernel ✓ (indices in range) |
| 3961, 3963 | `machConv f`, `machConv a` | the two children of `.app f a` | kernel ✓ structural |
| 3970/3972, 3977/3979 | `t`, `b` of `.lam` / `.forallE` | children | kernel ✓ structural |
| **3986–3989** | `machConv (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2)` | rebuilt from `rootFloat v = .letE n2 t2 v2 w nd2` | **✗**. `rootFloat` is `partial` (`MachRawSurface.lean` 198) and `liftLooseBVars` is `opaque`. Outside the kernel the measure would be lex (`|e|`, size of the root `let` value): the rebuilt term has the same size, and `v2` is a proper part of `rootFloat v`, assuming `|rootFloat v| = |v|` and `|lift x| = |x|` |
| **3993** | `machLoopRoot v̂` | `v̂` = `rootFloat v` (the shadowed `v`) | **✗** (`rootFloat` output); outside the kernel `|v̂| = |v| < |e|` |
| 3994, 3998, 4001, 4006 | `machConv … b` | the `let` body (env extended) | kernel ✓ |
| **4003** | `machConv v̂` | `rootFloat v` | **✗**, as 3993 |

### 1.2 `machNested` (4016)

| line | call | argument | measure? |
|---|---|---|---|
| 4021 | `machConv dom` | own argument | kernel ✓ |
| 4027 | `machChain (.regs base :: env) body st` | own argument; a **sharing probe**, once per entry of `st.nested` (`findSome?`) | kernel ✓ (fuel rule R2) |
| 4034 | `machReserve` (a `def`) | not recursive, but calls `partial` `zetaAll` (3702/3704 → `MachRawSurface.lean` 219) | no recursion into the block |
| 4036 | `machChain … body` | own argument | kernel ✓ |

### 1.3 `machInstance` (4045) / `machInstanceS` (4079)

| line | call | argument | measure? |
|---|---|---|---|
| 4059 | `machConv arg` (`foldlM` over `kinds.zip args`) | an element of `args` | kernel ✓ |
| 4087 | local `let rec inst` | `b.instantiate1 a`, structural on the list | needs no fuel; `opaque` value |
| 4094 | `machConv arg` | an element of `args` | kernel ✓ |
| **4105–4107** (S2) | `machConv p` for `p ∈ resTy.getAppArgs`, `resTy = inst ty args` | `ty` = the callee's declared type from `senv.instS c`, instantiated with the call's args | **✗ for any input measure.** `ty` is environment data, and `instantiate1` is `opaque`. Outside the kernel, termination holds for well-typed input (a `p` is a structure parameter, e.g. the domain, that cannot contain another structure-result call), but that is a property of the environment, not of the input |

### 1.4 `machChain` (4124)

| line | call | argument | measure? |
|---|---|---|---|
| 4127 | `machConv v` (`Circuit.pure'`) | child | kernel ✓ |
| 4133 | `machConv rhs` | child. Evaluated **even when** `machHandleV h = none` (`match a, b with`) | kernel ✓ (rule R4) |
| 4136 | `machChain rest` | body of the continuation `.lam` | kernel ✓ |
| **4144–4147** | float, as 3986 | `rootFloat` output | **✗** |
| **4151** | `machLoopRoot v̂` | `rootFloat` output | **✗** |
| 4152, 4156, 4159, 4164 | `machChain … b` | `let` body | kernel ✓ |
| **4161** | `machConv v̂` | `rootFloat` output | **✗** |

### 1.5 `machLoopBody` (4171) / `machLoopRoot` (4193)

| line | call | argument | measure? |
|---|---|---|---|
| 4174 | `machConv v` | `let` value (no `rootFloat` here) | kernel ✓ |
| 4179 | `machLoopBody … b` | `let` body | kernel ✓ |
| 4184 | `machConv nx` | `nx` from `machLoopRegs tail` (3786) | kernel ✓ (`machLoopRegs` lemma) |
| 4195 | (`inlSpine e`) | `dom`, `body` under the `.lam` | — |
| 4203 | `machConv dom` | spine arg | kernel ✓ |
| 4211 | `machLoopBody … body` (probe, once per `st.loopWs` entry) | subterm | kernel ✓ (rule R2) |
| 4229 | `machLoopBody … body` | subterm | kernel ✓ |

### 1.6 `machNorm` (4957)

| line | call | argument | measure? |
|---|---|---|---|
| 4967 | `machNorm x`, `machNorm y` (`Signal.ashr`) | `getAppArgs` elements | kernel ✓ |
| **4972** | `machNorm e'`, `e' = rawNode … e` (`MachRawSurface.lean` 70) | **built** term: `read`/`bind`/`pure` head rewrites (the size can grow: new type arguments), the `List.forM` unrolling (`f.beta`, `liftLooseBVars`; size × list length), and the matcher → `let` chain of `projChain` | **✗**. `beta`/`liftLooseBVars`/`lowerLooseBVars` are `opaque`. Even outside the kernel there is no single size measure, because unrolling duplicates `f`, which may itself contain raw nodes |
| 4973 | `machNorm f`, `machNorm a` | children | kernel ✓ |
| 4974 | `machNorm b` | child | kernel ✓ |
| **4978, 4981** | `machNorm (b.instantiate1 v)` (`Nat` / closed `BitVec` `let`) | substitution | **✗**. `instantiate1` is `opaque`, and the size grows. Outside the kernel this terminates (zeta of a let-tree) under a multiset measure, not a syntactic one |
| 4982 | `machNorm v`, `machNorm b` | children | kernel ✓ |

### 1.7 Other `partial` functions the block and `machineShape?` call

They are not in A's scope. Old and new call them identically, so they do not
affect compatibility. They stay `opaque` (§5, O4).

| function | recursion | measure |
|---|---|---|
| `rootFloat` (`MachRawSurface.lean` 198) | 201 rebuilt `let` (`liftLooseBVars`), 203 body, 207 `app (f.lift) b` | ✗ kernel; outside it, lex (size, size of the root value) |
| `zetaAll` (219) | `b.instantiate1 v` | ✗ (zeta) |
| `packTupleInputs` (`MachTupleIn.lean` 79) | `(b.lift).instantiate1 …` | ✗ kernel; outside it, the length of the `.lam` spine |
| `machLiftScalarN` (4641) | children, except 4728 (`ashr` → `sshiftRight` rebuilt) | ✓ after unfolding that one step |
| `machBoolMap` (4820) | children | ✓ structural |

### 1.8 Tally

* `machConv` / `machChain` / `machLoopBody` / `machLoopRoot` /
  `machNested` / `machInstance` / `machInstanceS`: 41 call sites. 34 are
  kernel ✓. The 7 ✗ are 3986, 3993, 4003, 4144, 4151, 4161 (all `rootFloat`)
  and S2 (4105–4107).
* `machNorm`: 10 calls on 7 lines. 3 calls are ✗ (4972 `rawNode`,
  4978, 4981 `instantiate1`).

## 2. Feasibility per option

| function | (i) measure | (ii) fuel witness | (iii) certificate |
|---|---|---|---|
| `machConv` | ✗ (`rootFloat` arms; S2 through `machInstanceS`) | ✓ | ✓ (= ∃ n) |
| `machChain` | ✗ (`rootFloat` arms) | ✓ | ✓ |
| `machLoopBody` | ✓ by itself, but mutual with `machConv` | ✓ | ✓ |
| `machLoopRoot` | ✓ by itself (reached only through ✗ edges) | ✓ | ✓ |
| `machNested` | ✓ by itself | ✓ | ✓ |
| `machInstance` | ✓ by itself | ✓ | ✓ |
| `machInstanceS` | ✗ (S2: environment data, not input) | ✓ | ✓ |
| `machNorm` | ✗ (`rawNode`, `instantiate1`) | ✓ | ✓ |

The block is one mutual recursion, so (i) needs **every** edge, and it fails.
To unblock (i) would take:

1. transparent re-implementations of `liftLooseBVars` / `instantiate1` /
   `beta` with size lemmas. This changes the function, and agreement with the
   C implementations would be a new outside-kernel fact;
2. a total `rootFloat` and a total `rawNode` with size lemmas;
3. for S2, a hypothesis on the environment ("no structure-result type mentions
   a structure-result call"). Enforcing it as a check could refuse inputs the
   old reader accepted, which is **forbidden**.

So (i) is not the route. (ii) and (iii) need no measure at all.

**Cheapest overall: (ii) + (iii) with one fuel argument for the whole block
plus `machNorm`, threaded through a fuel version of `machineShape?`.**
The certificate is the number `n`.

## 3. What A's definitions must satisfy (fidelity rules)

These rules make `Mono` provable. `Mono` is exactly the kernel form of "no
fuel artefact can change an answer".

* **R1** The result type is three-valued: `Fu α = ok α | fail | out`.
  `fail` is the old `none`, and `out` is fuel exhaustion. For `machNorm`,
  which never refuses, `fail` is unreachable (or use `Option Expr` with
  `none = out`).
* **R2** `out` is absorbing everywhere, **including the two sharing probes**:
  * `machNested` 4024–4030 (`st.nested.findSome?` around `machChain`);
  * `machLoopRoot` 4209–4214 (`st.loopWs.findSome?` around `machLoopBody`).

  A probe's `fail` means "not this one, try the next / allocate". A probe's
  `out` must make the **whole call** `out`. If `out` is read as "not shared",
  small fuel allocates a fresh sub-machine (other slots, other text) where
  more fuel shares one. That is non-monotone and changes the **output**, not
  just acceptance.
* **R3** Laziness: never evaluate a recursive call the old code does not
  evaluate. `findSome?` stops at the first `some`, `foldlM` in `Option` stops
  at the first `none`, and guards `if … then none else` short-circuit. An
  extra call could be `out` (or diverge) where the old one returned.
* **R4** Strictness: mirror the old evaluation exactly. At 4133 the old code
  evaluates `machConv rhs` even when `machHandleV h = none`. Evaluating less
  would not hurt acceptance, but it would break the transcription equation
  `IsFix` (§4, T3).
* **R5** The non-recursive helpers and the still-`partial` helpers
  (`rootFloat`, `zetaAll` via `machReserve`, `machLiftScalarN`,
  `machBoolMap`) are called unchanged.
* **R6** Fuel is decremented once per call into the block. The local
  `let rec bundle` (3897) and `inst` (4085) are structural and need none.
* **R7** `machineShape?` (5059) gets a fuel version that threads ONE `n` to
  its six reader calls (5076 `machNorm`, 5101, 5109, 5114, 5124, 5130) and
  propagates `out` separately from its own `none`s.

## 4. Theorem statements

Generic part, in `Tools/ReaderFuelGeneric.lean` (UNVERIFIED, all proofs
written):

```lean
inductive Fu (α : Type) | ok (a : α) | fail | out
inductive Fu.Le : Fu α → Fu α → Prop | out (b) : Fu.Le .out b | refl (a) : Fu.Le a a
def ofOpt : Option α → Fu α            -- some ↦ ok, none ↦ fail
abbrev Body (ι) (R : ι → Type) := ((x : ι) → Fu (R x)) → (x : ι) → Fu (R x)
def iter (B : Body ι R) : Nat → (x : ι) → Fu (R x)   -- 0 ↦ out, n+1 ↦ B (iter B n)
def Mono (B) := ∀ g h, (∀ x, Fu.Le (g x) (h x)) → ∀ x, Fu.Le (B g x) (B h x)
def IsFix (B) (f : (x : ι) → Option (R x)) := ∀ x, ofOpt (f x) = B (fun y => ofOpt (f y)) x
def Guarded (μ : ι → Nat) (B) := ∀ g x, (∀ y, μ y < μ x → g y ≠ .out) → B g x ≠ .out

theorem Fu.bind_le  : Fu.Le x x' → (∀ a, Fu.Le (k a) (k' a)) → Fu.Le (x.bind k) (x'.bind k')
theorem iter_mono   : Mono B → n ≤ m → Fu.Le (iter B n x) (iter B m x)
theorem iter_det    : Mono B → iter B n x ≠ .out → iter B m x ≠ .out → iter B n x = iter B m x
theorem iter_le_fix : Mono B → IsFix B f → ∀ n x, Fu.Le (iter B n x) (ofOpt (f x))
theorem agree_ok    : Mono B → IsFix B f → iter B n x = .ok r → f x = some r
theorem agree_fail  : Mono B → IsFix B f → iter B n x = .fail → f x = none
theorem iter_total  : Mono B → Guarded μ B → ∀ x, iter B (μ x + 1) x ≠ .out
theorem fixpoint_not_complete :
  ∃ (B : Body Unit (fun _ => Unit)) f, Mono B ∧ IsFix B f ∧ f () = some () ∧ ∀ n, iter B n () ≠ .ok ()
```

Instance for the block. The names are placeholders for A's.
`ReaderCall` is the sum of the seven argument tuples (with `senv` fixed), and
`ReaderRes` gives each its result type:

```lean
-- T0 (definition shape): the fuel block IS the iteration of one body
def machBlockBody (senv : StructEnv) : Body ReaderCall ReaderRes := …  -- A, rules R1–R6
def machBlockF (senv) : Nat → (c : ReaderCall) → Fu (ReaderRes c) := iter (machBlockBody senv)
--   (or seven mutual fuel functions with `machBlockF n (.conv …) = machConvF n …` by rfl)

-- T1 (kernel, A's main obligation)
theorem machBlockBody_mono (senv) : Mono (machBlockBody senv)

-- T2 (kernel, free from T1): fuel independence → the certificate is `n`
theorem machBlock_det (senv) : machBlockF senv n c ≠ .out → machBlockF senv m c ≠ .out →
    machBlockF senv n c = machBlockF senv m c

-- T3 (kernel, CONDITIONAL): soundness w.r.t. the old partial reader
def oldBlock (senv) : (c : ReaderCall) → Option (ReaderRes c)   -- dispatch to the 7 partial constants
def OldBlockIsFix (senv) : Prop := IsFix (machBlockBody senv) (oldBlock senv)   -- NOT provable/refutable
theorem machBlock_sound (senv) (h : OldBlockIsFix senv) :
    (machBlockF senv n c = .ok r → oldBlock senv c = some r) ∧
    (machBlockF senv n c = .fail → oldBlock senv c = none)

-- T4 (the coverage claim: NOT a kernel theorem; see O1)
--   "for every c on which the COMPILED old code returns v, ∃ n, machBlockF senv n c = ofOpt v"

-- T5 (only if a guarding measure existed; §2 shows it does not)
--   Guarded μ (machBlockBody senv) → ∀ c, machBlockF senv (μ c + 1) c ≠ .out
--   and with T3: OldBlockIsFix senv → ∀ c, machBlockF senv (μ c + 1) c = ofOpt (oldBlock senv c)

-- The same T0–T3 for machNorm (its own body, `fail` unreachable) and for the fuel
-- version `machineShapeF n` of `machineShape?`, whose Mono follows from T1, the
-- machNorm Mono, and `Fu.bind_le`.

-- T6 (payoff: invariants by induction on fuel, no partial equations needed), e.g.
theorem machConvF_keepsLenOk : machBlockF senv n (.conv env d e st) = .ok (r, st') →
    st.LenOk → st'.LenOk
--   This replaces the unprovable `Tools.ShippingReaderLenOk.ReadersKeepLenOk` for the
--   total reader, using the existing per-update lemmas of that file.
```

### The certificate and the driver (option (ii), compiler side, later)

```text
start n := n₀ (e.g. 2^16)
loop: match machineShapeF n … with
      | .ok s   => machine route with s; record n (the certificate)
      | .fail   => legacy route, exactly as today's `none`
      | .out    => n := 2 n; loop          -- NEVER legacy, NEVER a refusal
```

The driver is `partial`. It is a liveness device, not a reader, and it
diverges only if every fuel gives `out`, which under O1 means the old reader
diverges too. A fixed `FUEL` with `out → none → legacy` is excluded by the
ruling. A fixed huge `FUEL` with `out →` hard error at least never changes an
output silently, but it still depends on a physical bound argument; the
doubling driver does not. The recorded `n` lets an endpoint carry the premise
`machineShapeF n … = .ok shape` (a statement about a **definition**) in place
of `machineShape? … = some shape` (about an `opaque`).

## 5. What stays outside the kernel, even on the best route

Before the switch (shadow phase, real path unchanged):

* **O1 — coverage / adequacy.** The compiled `partial` code computes the
  least fixpoint on the inputs where it terminates. So an old success
  `some r` (or refusal `none`) is reached by some fuel, the depth of the old
  call tree. `fixpoint_not_complete` shows this does not follow from the
  source equation. Evidence: shadows only.
* **O2 — the old implementation satisfying its own source equation**
  (`OldBlockIsFix`, and the same for `machNorm`). The `partial def`s are
  `opaque` constants with no equation in the kernel. This is a
  transcription-fidelity fact (A's body versus the old source) plus Lean's
  `partial` compilation, measured only by shadows. It is a `Prop` used as a
  hypothesis, never an axiom.

Permanent (also after the compiler calls the total reader):

* **O3 — the `opaque` `Expr` primitives inside the body:**
  * `Expr.instantiate1` (4087, 4978, 4981);
  * `liftLooseBVars` (3988, 4146);
  * `lowerLooseBVars` / `beta` / `instantiate` (through `rawNode`);
  * `Expr.eqv` (`==` / `!=` on `Expr`: 3917, 3924, 4026, 4028, 4063, 4098, 4205, 4212, and inside `machLetIndex` / `machBindLet`).

  Their values are the C runtime's. The kernel cannot evaluate the total
  reader on a concrete input either, so a premise `machineShapeF n … = .ok
  shape` is still discharged by compiled evaluation (reflection), as
  `MachineDefines` is today. What changes is that it is about a definition
  with equations, so T6-style invariants become theorems.
* **O4 — still-`partial` helpers** called by the body: `rootFloat`, `zetaAll`
  (via `machReserve`), `packTupleInputs`, `machLiftScalarN`, `machBoolMap`.
  They are opaque values, and divergence inside them is still possible (as
  a hang, not a wrong answer). `machBoolMap` and `machLiftScalarN` are cheap
  to make structural. The other three need the same fuel scheme.
* **O5 — environment reads** (`StructEnv`: `proj`, `fields`, `inst`,
  `instS`, `natOf` = `kernelNat`, `prodMatch`). These are parameters, already
  isolated as `EntryDefines` / `MachineDefines`.
* **O6 — driver termination** (liveness only).
* **O7 — compiled evaluation = kernel semantics of `def`s.** This is the
  standard trust, the same as every reflection premise in the project.

## 6. Open obligations, in order

1. A: `machBlockBody` / `machNormF` / `machineShapeF` under rules R1–R7, and
   **T1 `Mono`** (with `Fu.bind_le`, and a `findSome` lemma for the two
   probes that passes `out` through).
2. Integrator: build `Tools/ReaderFuelGeneric.lean` (UNVERIFIED), then
   instantiate T2/T3.
3. Shadow (compatibility evidence; the real path stays):
   * on every corpus declaration (`scripts/shipping-coverage`), compare
     `machineShape?` with the driver over `machineShapeF`. Require the same
     `Option MachineShape` (and the same emitted text), with a ruling for any
     mismatch;
   * record the minimal finishing fuel and the number of doublings (expected
     zero at `n₀`);
   * also count `out` at `n₀`, so that a too-small `n₀` is visible, not
     silent.
4. Optional payoff: T6 (`LenOk`) for the total reader, which retires
   `ReadersKeepLenOk` as a boundary.
5. Switch the compiler only after step 3 is complete with zero mismatches
   (user decision).

## Integration (integrator, 2026-10-15) — BUILT as written
Base poc abdc891f. `lean_lib «Tools.ReaderFuelGeneric»` added. Run `b1` (cgrun, 3 GiB, swap 0, `-j 1`):
`Tools.ReaderFuelGeneric` exit 0, no fix. Axioms: `iter_mono`, `iter_det`, `iter_total` [propext, Quot.sound];
`agree_ok`, `agree_fail`, `fixpoint_not_complete`, `Fu.bind_le`: no axioms.
Kernel-checked counterexample (`fixpoint_not_complete`): `∃ B f, Mono B ∧ IsFix B f ∧ f () = some () ∧
∀ n, iter B n () ≠ .ok ()` — a function satisfying the source equation can succeed where no fuel does, so
"every old success is reached at some fuel" does NOT follow from the source equation: coverage is not a
kernel theorem (O1, measured by shadows only). The recommended route (three-valued fuel result, doubling
driver that never turns `out` into `none`/legacy) is NOT implemented in the compiler; the real path is
unchanged.
