# Proposal: kernel-visible definitions for the seven `machineShape?` readers (unit LC8)

Status: PROPOSAL + isolated PROTOTYPE. Nothing under `Sparkle/Compiler/*` is changed; no production function is
switched. Lean v4.32.1. Every number below is from a build run named in `REPORT-LC8.md`.

## 0. What exists now (PROVED in the prototype, all axioms = propext, Classical.choice, Quot.sound)

| file | content |
|---|---|
| `Tools/Prototype/ReaderFixpointLfp.lean` | **Reviewer route.** `lfpBlock senv := Lean.Order.fix` of the EXISTING body `step senv` (no copy of the seven readers). `lfp_unfold` (`lfp c = (Φ c).run lfp`), `lfpBlock_iff` : `lfpBlock senv c = some r ↔ ∃ n, readF senv n c = some r` (**the acceptance condition**, outer `none` = ⊥ / `some none` = refusal / `some (some v)` = success kept apart), via `lfp_iff : lfp Φ c = some r ↔ EvalG Φ c r` (`compact_step`, `evalG_fuel`, `fuel_evalG` reused). `protoLoopBody_post` : LC3's `machLoopBodyF_post` transported to the fixpoint. |
| `Tools/Prototype/ReaderFixpoint.lean` | ONE reader copied: `machLoopBody` as `partial_fixpoint` in the production type (`Option`). Unfolding equations, `loopBodyP_lets_mono` (success invariant by `partial_correctness`). |
| `Tools/Prototype/ReaderFixpointTwin.lean` | `loopBodyP` against the fuel twin: `twin_sound`, `twin_complete` (both directions, relative to a bridge on the partner reader). |
| `Tools/Prototype/ReaderFixpointMutual.lean` | A 3-member MUTUAL group (`convR`, `loopBodyM`, `loopRootR`; the last is a verbatim copy of `machLoopRoot`) accepted by `partial_fixpoint` in `Option (Option _)`; `joint_lets_mono` = ONE induction (`mutual_partial_correctness`) over the group, covering the `foldlM` and the `findSomeM?` probe. Also records what Lean REJECTS (§3). |

Why `machLoopBody` was the representative copy: smallest of the seven (2 arms), self-recursion on the `let` body, and a
`foldlM` over a closure that calls the partner `machConv` — the pattern of `machChain`, `machInstance`, `machInstanceS`.
The two readers with a recursion pattern it lacks (`findSome?` probe over earlier results: `machNested`,
`machLoopRoot`) are covered by the 3-member group.

**Scope caveat (reviewer).** `ReaderFixpoint.lean` / `…Twin.lean` take the partner reader `conv` as a FIXED
argument of one-layer type `Option`: that does not distinguish a diverging callback from a refusal, and it is NOT coverage
of the whole real reader. `loopBodyP_lets_mono` needs the hypothesis on `conv`; `twin_sound` / `twin_complete` take, for each
callback success, its own twin evidence (`hc`). Only `ReaderFixpointLfp` (whole block, ⊥/refusal/success kept apart) and
`ReaderFixpointMutual` (a group, no hypothesis on partners) are about a whole recursive structure.

## 1. Which monads support `partial_fixpoint` in v4.32.1

Checked in `Init/Internal/Order/Basic.lean`: `Option`, `ExceptT`/`OptionT` over such a monad, `ReaderT`, `StateT`,
`StateRefT'`, `EST`/`EIO`/`IO` (with `Nonempty ε`) have `MonoBind`/`CCPO` instances. `MetaM`/`CoreM` are stacks of
`ReaderT`/`StateRefT'`/`EIO`, so they are in principle covered; **not tested here**, because the seven readers are NOT
`MetaM`: they are pure `Option` functions with an explicit `MachRead` state (`Elab 3888-4244`). No `MetaM` is involved
in this proposal. (The `Meta`-level readers of other units are out of scope.)

## 2. Meaning of non-termination / refusal / success, per reader — before and after

Notation: B = today's `partial def` (kernel: opaque constant whose value is `default = none`; compiled: the recursive
code). A1 = proposed switch S1 below (mutual `partial_fixpoint` group in `Option (Option _)`).

All seven return `Option _`. None of them throws; there is no `MetaM`, `try`, or exception in the group.

| reader (Elab line) | success | refusal (`none` today) | non-termination (where it COULD arise; not proved either way) | calls inside the group | A1 |
|---|---|---|---|---|---|
| `machConv` (3888) | `some (e', st')` | `mdata`/`proj` arms; `d ≠ 0` guards; any callee's `none`; `bundle` mismatch | possible only through the `letE` arm that re-assembles the term from `rootFloat` (size not structurally smaller; LC6 proved `rootFloatS` terminates, `rootFloat` itself is still `partial`) | `machNested`, `machInstance`, `machInstanceS`, `machLoopRoot`, itself | success ↦ `some (some _)`, refusal ↦ `some none`, ⊥ ↦ outer `none` (never produced by the compiled code) |
| `machNested` (4020) | `some (v, st')` | `st.inInner`; callee `none` | via `machConv`/`machChain` | `machConv`, `machChain`; **`st.nested.findSome?` probe calling `machChain`** | same; probe becomes `findSomeM?` |
| `machInstance` (4049) | `some (machInstOut k, st')` | result kind not `bits`/`bool`; callee `none`; domain mismatch | via `machConv` in the `foldlM` | `machConv` | same |
| `machInstanceS` (4087) | `some (ctor …, st')` | `st.inInner`; `machOuts?` none; `fields.any .domain`; callee `none` | via `machConv` | `machConv`; local `let rec inst` (structural on `args`) | same; local `let rec` lifted (untested, §4 item 6) |
| `machChain` (4135) | `some (ws, v, st')` | final `| _, _, _ => none`; callee `none` | its `letE` arm re-assembles through `rootFloat` (as `machConv`) | `machConv`, `machLoopRoot`, itself | same |
| `machLoopBody` (4182) | `some st'` | `machLoopRegs tail = none`; callee `none` | only via `machConv` | `machConv`, itself | **PROTOTYPED** (`loopBodyP`; `Option` is enough for this one reader) |
| `machLoopRoot` (4204) | `some (mv, st')` | `st.inInner`; `machLoopRegs`/`machSlotKind?`/`machInit?` none; domain mismatch; callee `none` | via `machConv`/`machLoopBody` | `machConv`, `machLoopBody`; **`st.loopWs.findSome?` probe calling `machLoopBody`** | **PROTOTYPED** (`loopRootR`, `Option (Option _)`) |

Mutual structure: ONE strongly connected component (`machConv → machNested → machConv`, `machConv → machLoopRoot →
machLoopBody → machConv`, `machChain ↔ machConv`, `machInstance`/`machInstanceS → machConv → …`). `partial_fixpoint`
for a mutual group is accepted in v4.32.1 (prototype: 3 members) and generates `mutual_partial_correctness`.

### What a kernel value means after the switch
`some (some v)` : a FINITE derivation exists (proved: `lfp_iff`). `some none` : a finite derivation of a refusal.
Outer `none` : no finite derivation — the abstract bottom; **the compiled code never returns it** (IR of a
`partial_fixpoint` def is the direct recursion — checked on a toy def by IR trace, run `lc8j`; a diverging input diverges,
exactly as with `partial def`).

## 3. What Lean 4.32.1 REJECTS (recorded finding)

1. The production shape `Option` with refusal = `none` and
   `st.loopWs.findSome? (fun … => match machLoopBody … with | some st' => … | none => none)` (the sharing probe of
   `machLoopRoot`; `st.nested.findSome?` of `machNested` is the same): the monotonicity tactic fails
   ("Cannot eliminate recursive call … enclosed in `Array.findSome?`"). This is not a tactic weakness: with a flat order
   where `none` means both "refused" and "diverged", `findSome?` is **not monotone** — if the probe moves from `none`
   (⊥) to `some _`, the answer moves from the NEXT element's to its own, which is not an information increase. So
   **plain `partial_fixpoint` in `Option` is not available for the group**; the refusal/⊥ distinction is forced.
2. `match <recursive call> with | some … | none => none` directly on a recursive call is rejected; the same program
   written with `do`/bind is accepted. This is a semantics-preserving rewrite (`match o with | some x => k x | none =>
   none` is `o.bind k`).
Accepted (prototype `ReaderFixpointMutual`): `Option (Option _)`, `do` + inner `match` on the bound result,
`List.foldlM`, `List.findSomeM?` (outer `none` of a probe = ⊥ of the whole search, as `findSomeO` of the fuel twin).

## 4. A1 = the production switch, and what it changes (NOT done)

A1: replace the seven `partial def` by one `mutual … partial_fixpoint … end` whose members return `Option (Option _)`,
and `machineShape?` reads `match … with | some (some x) => … | _ => none`.

Call sites (grep over `Sparkle/ Tests/ Tools/`): the seven names are used only inside `Elab.lean`:
inside the group (3888-4244) and in `machineShape?` at 5114 (`machConv`), 5122 (`machLoopRoot`), 5127 (`machConv`),
5137 (`machChain`), 5143 (`machConv`); `machineShape?` is called at 5280 and 5314 (and `Tests`/`Tools` mention the readers
only as the fuel twins `…F`, the local `machInstanceS.inst` shadow in `Tests/Compiler/ReaderInstTyShadowTest.lean`, and
comments). Behaviour of each: terminating input — same value (the unfolding equation is the old text); refusal — `none` as
before; diverging input — diverges as before. **No new refusal, no new acceptance is introduced by A1.**

Verification items for a production switch (A1), each OPEN:
1. Port all seven bodies to `do`-with-inner-`match` and `findSomeM?`; prove `machineShape?` (a `Option`-valued wrapper)
   gives the old result on every input where the old one terminates (a unit test on `Tests.AllTests` data is not a proof).
2. Compile-time: `partial_fixpoint` mutual group of 7 with ~250 lines of bodies — the 3-member prototype builds in ≈2 s
   beyond imports; the 7-member group is UNTESTED.
3. Local `let rec bundle` (machConv) and `let rec inst` (machInstanceS) inside a `partial_fixpoint` body: UNTESTED; plan:
   lift to top-level structural `def`s.
4. `rootFloat` (MachRawSurface), `zetaAll` (inside `machReserve`), `rawNode`, `machNormNode` and their `partial` callees
   stay opaque constants: a reader theorem still takes `RootFloatRange`-type premises until each is switched (`rootFloat`
   has the verified WF model `rootFloatS`, LC6).
5. Runtime fit: code size/stack depth of the generated recursion vs `partial def` (IR check on a toy only).
6. The `extern`/`opaque` `Expr` primitives (`instantiate1`, `liftLooseBVars`, …) are untouched.

## 5. Alternatives and why not

* **Well-founded recursion on a measure**: no measure is known for the group (state-dependent sharing probes re-read
  `body` in a new environment; the `letE` arms re-assemble the term via `rootFloat`). Not attempted.
* **Fuel with a cutoff**: NOT equivalent. A cutoff `N` makes every input needing more than `N` unfoldings answer
  `none` (refusal) where today it answers `some _`: this changes the compiler's acceptance set (legacy fallback instead of
  the machine route), i.e. behaviour. Only "fuel + proof that the answer equals the least fixpoint" (the existing
  `readF` twin, `lfpBlock_iff`) is equivalent, and that is a model, not production code.
* **Status quo + premise** (`TwinCoverAt`): what LC6/LC7 have; OPEN.

## 6. What the prototype does NOT prove — correspondence with the old implementation (separate list)

`lfpBlock` is a *model*. It is not a theorem about the shipped `partial def`s.
* **O1**: when the compiled `partial def` returns, a finite derivation exists. Fact about the runtime. After A1 the
  new group IS the fixpoint (unfolding equation by construction) and O1 is no longer needed for the new group — but it
  is for today's `partial def`.
* **O2** (transcription): `step senv` is the hand transcription of the old text. After A1 it becomes a THEOREM: the new
  group satisfies the equations `OldEq senv G` (`Tools/ShippingReaderFuelOldEq.lean`) per arm, hence is a solution
  (`fuel_agree`: `readF n c = some r → G c = r`); the reverse (`G c = some r → ∃ n, readF n c = some r`, i.e.
  `TwinCoverAt`) needs minimality of the new group = a `mutual_partial_correctness` induction over all seven bodies —
  the three-member `joint_lets_mono` and `twin_complete` (one reader) are the templates; per-arm effort, not free.
* `realFns`/`TwinCoverAt` (LC6/LC7) are not changed here.
