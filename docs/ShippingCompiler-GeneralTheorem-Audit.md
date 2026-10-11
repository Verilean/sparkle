# The general theorem: what it would say, and what stands between it and today

Status 2026-10-12, branch `poc/roundtrip-proof`. This is an audit, not a
result. The "12 remaining theorems" counted earlier are WORK PACKAGES on the
route being built; finishing them does not by itself give a theorem about
every successful compile. The gaps that are not among the 12 are registered
here as G-items.

## 0. Current status (2026-10-12)

Verification record: snapshot `ffad8424`, `Tests.AllTests` 881 jobs green
(every Lean / lake run under the cgroup runner, 3 GiB cap, one job; peak
0.42 GiB); `704d44d5` adds three modules (worker B, G2), each built.

**Reading the tables**: the twelve work packages (§6) are a decomposition of
ONE compile route's premises. "Done" for a package means its premise is
removed from the endpoints of the declarations in its stated domain — not
that every input the compiler accepts is covered. What every accepted input
would need is the gaps G1–G5 and N1 below, which are open.

| Item | State | Domain actually covered | What stays |
|---|---|---|---|
| A1–A7 (`closeLets`) | done | machines whose `let`s pass `letsOk` (per-declaration data check) | S2 / reader correspondence under G3 |
| B1 (`closeInsts`, one output) | done as `MachineClosesAt` | parents whose calls are one-output calls of **gate children** or **slotless machine children** (`let`s, no register, no call); callees may repeat in any order; with or without `let`s (no real K = 0 instance with calls exists: such a parent is not a machine shape) | name separation N1 as premises; child's reflection (`EntryDefines` / `MachineDefines`) |
| B2 (`closeInstsG`: several outputs, sequential children) | **done for machine children without calls** (`machineClosesAt_of_seqKids`; pure core `closeInstsG_of_facts`: one instance per call group, write SETS in the rank, `clk` / `rst` in the linked order, distinct instance names, no self-feed; run level with the cache pin; child interface `ChildIfaceG` from the child's own run) | parents whose calls go through `closeInstsGM` over machine children WITHOUT calls and without memory children: `parent`, `chained` closed at depth 1 (`f.machine_design_svNR1_closed`) | per-declaration data conditions (S3, field-is-output, distinct fields within a call — G3b); N1 name premise; children with calls (B3): `mixD1`, `grandH`, `topD2`, `mid2`, R0 parents keep `MachineClosesAt`; memory children |
| Machine children with calls of their own | open | `ChildIface` asks an empty design and an assign-only body, so it does not extend to a child with calls; `closeInsts` itself asks `kidsCombB` of every child | — |
| C1–C3 | see §6 | — | — |
| R0 / NR heads | migrated to `MachineClosesAt` | all R0 / NR test endpoints; `midH`'s closing DISCHARGED at depth | parents of sequential children (B2) |
| G1 output checks | open | — | the decidable checks on the result are obligations of the endpoints |
| G2 / C3 legacy route semantics | open — contract layer proved, CONDITIONAL (`legacy_translate_contract`; `Tools/ShippingLegacySem*`, `docs/parallel/G2-legacy.md`) | no real fallback declaration end to end | `ReachesInline` (dispatch to the inline attempt; blocked by legacy cache hits not validated against the builder state — a suspected stale-hit defect, not reproduced yet); a deep source for legacy syntax (SEM0); the entry-level legacy arm |
| G3 reader coverage (S3, `letsAliasOk`, `gateCallsOk` evaluated per declaration) | open | — | no theorem about the shape reader |
| G4 | open | — | — |
| G5 runtime laws | **conditional** | `quiet` / `Diag` / `OkMsg` / `OkEnv` laws; exception provenance by value; law audit from 22 endpoints | no runtime model; `profLog` one constructor; elaborator primitives unconditional; T3 trusted |
| N1 name separation | open | `Name.toString` (escaping) does not reduce in the kernel; no bridge to the unescaped renderer | premises of every closed endpoint |

Closed SV endpoints today (`f.machine_design_svHR_closed`): `caller`,
`callerTwice`, `callerNested`, `callerD`, `midH`, `callerMix`, `callerRep`,
`callerABA` (gate children); `callerL`, `callerLN`, `hftByte` (slotless
machine children). Closed depth endpoints (`f.machine_design_svNR1_closed`,
the general closing): `parent`, `chained` (sequential two-output child `cnt`).

## 1. The target statement

For every source `f` in the Signal DSL and every successful run of the real
entry on `f` returning a design `D`:

1. **source correspondence** — the top module's outputs, cycle by cycle, are
   the source streams' values;
2. **closed SV execution exists** — for every finite `T`, the emitted
   objects' semantics has a run of length `T` from an admissible start;
3. **all runs agree** — every such run has those outputs.

Two kinds of premise are legitimate in that statement, and only these:

- **use conditions** (the environment's): input values within their declared
  widths, `rst = 0` after the start, registers starting at their reset
  values, the start state within widths;
- **the trusted base**: Lean's kernel and standard axioms, the generic
  runtime laws (`RefLaws`, §5), reflection of the environment (§3), the
  printer's bytes (the SV conclusion is about the emitted OBJECTS' formal
  semantics; the text is trusted, TrustBase §6c).

Everything else about the artifact the compiler produced is a PROOF
OBLIGATION. It may be discharged by a theorem about every run, or by a check
the compiler itself runs (then "the run succeeded" gives it). A check that
only the proof generator evaluates on one declaration is neither.

## 2. Today's endpoints, premise by premise

The 20 derived endpoints are instances of `ships_design_svH_all` /
`ships_design_svN_all` for 20 declarations, generated per declaration. Their
premises (`scripts/shipping-coverage/endpoint_premises.lean` prints them;
its counts are distinct syntactic occurrences, NOT logical premises):

| Premise | What it is | Run by the compiler? | Status |
|---|---|---|---|
| inputs / `rst` / start-state bounds, `SourceInputs`, reset values | use conditions | — | legitimate premises |
| `ChildBnd` = `Nonempty RefLaws ∧ StartW` | runtime laws + start world | — | trusted (§5); no compiler-specific condition left inside |
| `MachineDefines`, `EntryDefines` | what the declaration is, as read | — | reflection (§3); asked once per child, context-independent (proved) |
| `MachineCloses` (parent's own; children with `let`s or calls) | the machine route was taken, not the legacy fallback | NO (it is the outcome of `closeLets` / `closeInsts`, which the compiler runs, but success of the ENTRY does not imply it: the entry also succeeds through the fallback) | obligation; **derived for shapes without calls that pass `letsOk`** (A1–A7; `f.machine_closes`); still a premise for shapes with calls (B1/B2) |
| `designCheck`, `outsCheck` | internal structure of the emitted design (text checks, children pass) | NO — defined in `Tools/`, 0 uses in `Sparkle/` | **obligation, not a use condition**; evaluated by `decide` per declaration; not derived for arbitrary runs (G1) |
| `shipsHierCheck` / `shipsHierHCheck`, `kidsMixed`, `kidsMem`, `kidsMaskedN`, `kidsComb` | structure of the closed module and its children | NO (same) | obligation; same status (G1) |
| `kidsCombB` | children combinational, local, wired | YES (`closeInsts`) | a runtime check — but one that NARROWED what the machine route accepts (C3) |
| per-call source facts (`hcalls`) | the call's arguments are the source's | — | generated by `rfl` / `decide` per declaration (G3) |

So an endpoint today reads: *for THIS declaration, whose shape was read and
whose checks evaluated true at generation time, under reflection and the
closing premises, the run's outputs are the source's.* It is not yet a
statement about every source or every run.

## 3. What `MachineDefines` does and does not carry (G3)

Four different things, only the first is the reflection principle:

1. **reflection**: the constant read by `getConstInfo` in the run is the
   declaration (the environment is fixed). Premise by design.
2. **reader soundness**: `machineShape?` applied to that constant gives a
   shape whose `Term` means the source. NOT proved in general; per
   declaration the generator checks `quote`'s image and the source equation
   by `rfl` (`#machine_endpoint`).
3. **source ↔ `MachineData`**: the family `src` in the conclusion is the
   declaration's meaning. Per declaration, by `rfl` / generated proof.
4. **coverage**: for every successful run a shape, its data and the
   generated proofs EXIST. Not established: nothing says the generator
   succeeds on every declaration the compiler accepts.

Until 2 and 4 are theorems, the guarantee is "validated per declaration"
(translation validation by the kernel), not a general theorem. Item C1 below
(context transfer of nested `Defines`) addresses none of 2–4.

## 4. What `LegacyRel` / `BodyRel` proved (G2)

`legacyRel` and `bodyRel` are `Keeps` statements for the invariant `J`: the
legacy translator and the body preserve the child-cache invariant on every
outcome. They say NOTHING about the meaning of what the legacy route emits.
A compile that succeeds on the legacy route has no source theorem.

- The corpus measurement "legacy-only 0 / 391" is a measurement of those
  391 declarations, not a coverage proof.
- Each endpoint excludes the legacy route for its own declaration by
  premise (`MachineDefines` for the top, `MachineCloses` for the closing).
- General statement would need: either a source theorem for the legacy
  route (not planned), or "the entry's success + a decidable condition on
  the source implies the certified/machine route" with that condition part
  of the theorem's stated domain.

## 5. `RefLaws` and `StartW`, unfolded

`RefLaws` fields (about Lean's runtime, the three refs and the listed side
refs; one `Framed` constructor names the compiler's logger — see (a) below): `val`, `sval`,
`dval` (the three refs' values per world); `cacheGet/Set/Modify`,
`synthGet`, `depthGet/Set/Modify` (what a successful operation does);
`frame` (every `Framed` operation leaves the three values, on every
outcome); `telescope`, `lamTelescope`, `localDecl`, `letDecl` (a combinator
leaves the values and runs its continuation in some contexts).

**G5 audit, 2026-10-11 — the laws WERE inconsistent; fixed.**

(b) Consistency. `Framed` had `ioFlush (h : IO.FS.Stream)`: a frame law for
the `flush` of ANY stream. `IO.FS.Stream` is a structure of closures, so that
is a frame law for an arbitrary `IO Unit`. With `cacheSet` it is a
contradiction: for the stream whose `flush` is `sparkleChildCache.set v`, the
frame says the cache value is unchanged and `cacheSet` says it is `v`, for
every `v`. A probe proved `RefLaws mref cref → False` (standard axioms;
`~/sparkle-work/probes/laws1.lean`). Consequence: **until the fix, every
theorem with a `ChildBnd` / `ChildLaws` premise — the 20 derived endpoints,
`childKeeps`, `bodyRel`, `legacyRel` — was vacuous.** The axiom audits could
not see this.

Fix: the compiler's four `(← IO.getStderr).flush` are the named action
`Sparkle.Compiler.flushStderr` (same behaviour), and the constructor is
`stderrFlush : Framed (liftM flushStderr)` — a law about THAT action. It is
an assumption about the environment (the process's stderr stream does not
write the three refs), not derivable, and no longer refutable from inside:
`IO.getStderr` is opaque. A test (`ShippingChildBoundaryTest`, "FRAMED")
rejects any `Framed` constructor taking a stream or an action as an
argument.

Not shown: that the remaining laws have a model. What was checked is that
the one known contradiction is gone and that no constructor quantifies over
caller-supplied actions. Remaining generic arguments, by kind: pure
functions (`sideModify f`, `metaModify f`, `coreModifyTrace f`); opaque
handles (`IO.FS.Handle`); refs restricted to the listed side refs or to
run-local TYPES (`LocalRefType`: other types than the three tracked refs');
Lean expressions. One stated assumption of the same flavour remains:
`msgToString (m : MessageData)` — a message can carry a lazy thunk
(`MessageData.ofLazy`, a `BaseIO` closure) that rendering runs.

**`msgToString`, `ppExpr`, stderr — checked 2026-10-11 (second pass).** The
same shape of counterexample as `ioFlush` was tried for `msgToString`: a
message `ofLazy (fun _ => do sparkleChildCache.set v; …)`
(`~/sparkle-work/probes/laws4.lean`). It does NOT go through:
`MessageData.formatAux` is `opaque` in the kernel (a `partial def`), so no
theorem relates rendering to the thunk; `RefLaws → False` is not derivable
this way. So the laws are not shown inconsistent by it — but the law is
FALSE of the runtime for such a message, and likewise `ppExpr` (it runs the
environment's registered delaborators / printers, arbitrary code) and
`ioEprintln` (the installed stderr stream). Where they are used: the
translator renders the message of a CAUGHT exception on an error path
(`Elab.lean`, "Inline expansion failed with"), and pretty-prints
expressions in diagnostics; the invariant must hold on failing runs too,
because callers catch. The messages there are whatever Lean or the
translator threw, including Lean's own lazy `ofExpr` messages, so their
safety cannot be derived from the compiler's construction: it depends on
the environment's printers. Status: three ENVIRONMENT ASSUMPTIONS — no
registered printer, no thrown message's thunk and not the installed stderr
stream writes the three refs. They are premises of every `ChildBnd`
theorem, stated generically (for every message / expression), which is
stronger than what a run needs. Not kernel-refutable; not derived; a model
of the laws is not exhibited, so "consistent" is NOT claimed — only that
the one derivable contradiction is removed. The surface-type test on
`Framed` constructors does not see callbacks inside structures and is not a
consistency audit.

(a) Compiler-specific constructors. "None mentions a compiler function" was
wrong: `profLog (b) (msg) : Framed (liftM (profLogIO b msg))` names the
entry's logger (a copy in `Tools/`, the entry's closure by `rfl`). Its parts
all have constructors of their own (`ioEprintln`, `stderrFlush`,
`ioHandleMk`, `ioHandlePutStrLn`, `ioHandleFlush`), so it should be
derivable; it is NOT derived: `vc` has no rule to push the `IO → MetaM` lift
through `>>=` / `if`, and the lift-of-bind equation was not closed in the
time spent (the instance's auxiliary definitions do not unfold by `simp`).
Status: one compiler-named constructor, redundant in content, kept as a law.
`ioEprintln` / `ioGetStderr` are fixed Lean actions whose frame is likewise
an environment assumption.

`StartW w`: the synthesis ref reads `synthesizeChild`, and depth 0 or the
cache invariant — the first is true after the compiler's `initialize`, which
is outside the kernel.

Model scope of the SV conclusion: one clock, `rst` low throughout the run,
registers at reset values at the start; the emitted objects' cycle
semantics; no timing, no X/Z, no multi-clock.

### G5 — the diagnostic laws: what is wrong and the design to fix it (2026-10-11, third pass)

**Status 2026-10-11 (fifth pass): parts 1 (`quiet`) and 2 (message
provenance) IMPLEMENTED, every dependent re-verified. Still conditional
theorems: the laws are assumptions, no runtime model shows them satisfiable.**

Part 2, as implemented (`Tools/ShippingChildInv.lean`, `…Keeps`, `…VC`):

* `OkMsg : MessageData → Prop`, an inductive over the message tree: text
  (`stringToMessageData`), formats, `compose` / `nest` / `group` / `tagged` /
  context wrappers / originating syntax — and two lazy leaves, the TRUSTED
  list (pinned by a test): `ofExpr e`, `ofConstName n` (their thunks call the
  environment's printers: covered by `quiet`). No constructor for an arbitrary
  `ofLazy`. `OkExc e := OkMsg e.toMessageData`.
* The rendering law is `Diag.msgToString m : OkMsg m → …` — no frame law for
  every message is left.
* **`Keeps` tracks the thrown exception**: from an invariant world a program
  ends in one AND, if it throws, the exception is `OkExc` (`ErrOk`). `Triple`'s
  error clause takes the exception. So `tryCatch` hands its handler an `OkExc`
  exception — this covers the runs that fail and continue. A plain `throw e`
  needs `OkExc e`; `throwError msg` needs `OkMsg msg`.
* Trusted law T3 is ONE field, `RefLaws.excOk`: an exception thrown from a
  quiet world by a generic primitive, a diagnostic, a `throwError` of a message
  in the class (it adds context wrappers), or a cell operation is `OkExc`.
  `throwError` of an ARBITRARY message has only its value frame (`Throws`,
  `frameT`) and is not a tracked operation.
* The compiler's own messages are PROVED in the class by the closure tactic
  `okmsg`, called by `vc` at every `throw` / `throwError` side goal: all sites
  of the harness, the translator, the fallback and the legacy block close (the
  one lazy form met was `ofConstName`).
* **The rendered exception's provenance is a VALUE, not a heap cell** (sixth
  pass; the fifth pass used a law "every `IO.Ref (Option Exception)` holds an
  in-class exception" folded into `quiet` — a condition on the whole heap,
  not a provenance; removed). The compiler's inline attempt is the top-level
  `Rec.tryInlineUnfold`, which RETURNS the caught exception with its result
  (same messages and control flow; the cell `lastInlineFail` is gone).
  `tryInlineUnfold_tripleC` proves the returned exception is none or `OkExc`
  (`TripleC.tryCatchQ`: a `catch` with a postcondition), and the bind on its
  result hands that to the continuation (`KeepsC.bindCaught`), where the ONE
  rendering site is. No law about any ref of type `Option Exception` exists;
  `quiet` is a condition on the diagnostic environment only.
* **Captured contexts** (checked against Lean's `MessageData.formatAux`):
  `MessageData.toString` formats with NO context; a lazy leaf then prints text
  and calls nothing. Under `withContext ctx` a lazy leaf calls the printer
  functions stored in `ctx.env` (`ppExt.getState ctx.env`) — the CAPTURED
  environment's, which `quiet` (a world predicate) does not cover. So
  `OkMsg.withContext c` requires `OkEnv c.env`, defined semantically: in any
  printing context over that environment, `ppExprWithInfos` and
  `ppConstNameWithInfos` leave what the three tracked refs read (`Inert`),
  from every world. `FormatWithInfos` contributes its format only (no
  callback); a naming context only shortens names.

Trusted in part 2, explicitly: the two lazy leaves under a context with
inert printers; `excOk` (T3), which INCLUDES that the context a run's own
error captures (its current environment) is `OkEnv` — an assumption about the
environments the compile runs in. NOT done: `profLog` is still one
constructor (not derived from `eprintln` / `flushStderr` / the file handle);
the elaborator primitives remain in the unconditional class. Witnesses: the
value-level invariant, the start condition and `J` are each about ONE
witness; `invW_of_invV L` packs `L` itself, `invV_of_invW` returns a witness
with its own invariant, and `withAux` changes none of `val` / `sval` / `dval`
/ `quiet` (`Tools/ShippingCallsSame.lean`, by `rfl`). An audit FROM the 19
generated endpoints (closed HR, R0, NR at every depth; definitions and
inductive constructors unfolded) checks: `ChildBnd` reached, no unconditional
frame law about a diagnostic or a throw, the conditioned laws' shapes, no
exception-cell law, and that the cache-pinning auxiliary predicate is
constrained by no law and no start condition
(`Tests/Compiler/ShippingCallsCloseTest.lean`, `LAW AUDIT FROM THE
ENDPOINTS`). No runtime model: all endpoints stay conditional theorems.

(Previous status line: part 1 implemented, part 2 not done.)

Part 1, as implemented (`Tools/ShippingChildInv.lean`):

* `Framed` no longer contains the diagnostic operations. They are the
  separate class `Diag`: `ppExpr`, `IO.eprintln`, `msgToString`,
  `IO.getStderr`, `flushStderr`, `Handle.mk` / `putStrLn` / `flush`,
  `profLog`.
* `RefLaws` has a field `quiet : world → Prop`. `frame` (the generic
  operations) is unchanged and unconditional. `diag` is asked ONLY in quiet
  worlds: values left and the end world quiet, on every outcome. The
  generic operations and the tracked refs' writes keep quietness
  (`frameQ`, `cacheSetQ`, `cacheModifyQ`, `depthSetQ`, `depthModifyQ` — the
  trusted condition T2); the telescope laws' closure premise carries it.
* `quiet` is a conjunct of the invariant (`InvV`, `J`, `InvC`), so every
  `Keeps` theorem (`bodyRel`, `legacyRel`, `translateRel`, `harnessRel_of`)
  is re-proved under the new laws — no proof of them uses a diagnostic frame
  outside a quiet world.
* `ChildBnd w := ∃ L, StartV L w ∧ L.quiet w`: ONE witness, whose start
  condition and quietness are about the run's start world. It is no longer
  `Nonempty RefLaws ∧ StartW w`.
* The law-free invariant `InvW` (what `RealChild`, `MachineClosesAt` and the
  depth premises speak of) carries `∃ L, L.quiet w`: a child's world is quiet
  for a witness, and the laws used from that world on are that witness's
  (`invV_of_invW` returns it). `MachineClosesAt` lost its separate
  `ChildLaws` premise for that reason. The witness at a child's world is
  DERIVED from the parent's (the parent's invariant, by `invW_of_invV`), not
  assumed; but it is existentially re-packed there, so the statement "the
  same `L` throughout" holds along one entry's own run, and per child world
  "some `L` quiet here".
* This is not vacuous by `quiet := False` (the endpoint asks `L.quiet w₀`),
  and `quiet := True` is the old, stronger assumption as a special case.

What part 1 does NOT do: (i) `Diag.msgToString m` is still for EVERY message
`m` (in quiet worlds) — a lazy message carries code, which no world
predicate covers; (ii) `profLog` is still one constructor naming the whole
logger, not derived from its parts (`eprintln`, `flushStderr`, the file
handle), which are in `Diag` separately; (iii) the elaborator primitives
(`whnf`, `inferType`, `reduce`, `unfoldDefinition?`, `mkAppM`, …) stay in
the unconditional class — trusted (they evaluate terms, but `whnf` can run
compiled code through `reduceBool` / `reduceNat`); (iv) no runtime model
shows the laws satisfiable: these remain conditional theorems.

Part 2 design, with what it needs concretely (not started in code):
`OkMsg : MessageData → Prop` as an INDUCTIVE (composition constructors
provable; leaves `ofFormat`, `ofExpr`, `ofName`, … an explicit trusted list),
`OkExc`; a law `excOk` (T3: an exception a primitive throws from a quiet
world is `OkExc`); the message law only for `OkMsg m`; `Keeps` / `Triple`
gain "the thrown exception is `OkExc`" (so `tryCatch` hands its handler an
`OkExc` exception, including runs that fail and continue); the content of
`lastInlineFail` tracked by generic laws of run-local refs of type
`Option Exception` (`mkRef` / `get` / `set` values) with "holds an `OkExc`"
in the invariant; an `OkMsg` side goal at each of the compiler's 61
`throwError` sites and 19 `throw (Exception.error …)` sites, closed by
closure lemmas.

Earlier text (third pass): **NOT fixed.** `msgToString (m : MessageData)` is a frame law for
EVERY message; it is false of the runtime (a lazy message's thunk can write
the cache). That the kernel cannot refute it (`formatAux` is opaque) does
not make it true. `ppExpr`, `ioEprintln`, `stderrFlush`, `profLog` and the
file-handle writes are false in an environment with a hostile printer /
stderr stream. Every `ChildBnd`-premised theorem — all derived endpoints —
is stated under these over-general laws. They are NOT to be counted as
soundness-established until the laws below replace them.

The two kinds of over-generality need different repairs:

1. **Data arguments, environment-dependent behaviour** (`ppExpr e`,
   `IO.eprintln s`, `flushStderr`, `profLog`, handle writes): the argument
   carries no code; what runs is the environment's printers / the installed
   stream, i.e. state of the WORLD. Repair: a world predicate `quiet`
   (a field of the laws) with
   * `diag : Diag p → quiet w → values kept ∧ quiet (endW p w)`;
   * every tracked operation and every `Framed` primitive preserves `quiet`
     (the compile does not register printers or replace stderr) — trusted;
   * `quiet` becomes a conjunct of the invariant (`InvV`), and of the start
     condition: the endpoint's premise is `quiet w₀` at the run's start
     world, for the same `RefLaws` (so `ChildBnd w := ∃ L, StartV L w ∧
     L.quiet w`, not `Nonempty RefLaws ∧ StartW w`).
   Trusted conditions then read: (T1) at the start world no registered
   printer and not the installed stderr writes the three refs; (T2) the
   compile's own operations do not change that. Mechanically: `Framed`
   splits into `Framed` (refs, Lean's elaboration primitives) and `Diag`;
   the frame law's conclusion and the telescope laws' closure premise gain
   the `quiet` clause; `J_same` and the `vc` side-goal rule follow. All
   `Keeps` theorems are re-proved under the new invariant.
2. **A code-carrying argument** (`msgToString m`): no world predicate
   helps — the thunk is in the message. Repair: PROVENANCE. A predicate
   `okMsg` on messages (a field of the laws), the law only for `okMsg m`,
   and
   * (T3) an exception a `Framed` Lean primitive throws from a quiet world
     has an `okMsg` message (Lean's own lazy messages call the
     environment's printers: covered by `quiet`);
   * the compiler's own `throwError` messages are `okMsg` by construction
     (strings, names, `ofExpr`) — to be PROVED from closure rules of
     `okMsg`, of which `okMsg (ofExpr e)` is trusted (T4);
   * the calculus gains an exceptional postcondition carrying the thrown
     exception (`Triple`'s error clause takes the exception), `tryCatch`'s
     handler receives an `okMsg` exception, and the content of the
     translator's failure ref (`lastInlineFail : IO.Ref (Option
     Exception)`) is tracked: "holds an `okMsg` exception" joins the
     invariant, with get/set laws for that run-local ref.
   The one rendering site (`Elab.lean`, "Inline expansion failed with")
   then renders an exception that is `okMsg` by the invariant.

Neither is a rename: (1) changes the laws from "in every world" to "in
quiet worlds", (2) from "every message" to "messages this run produced".
Cost: the invariant and the frame laws (`ShippingChildInv`,
`ShippingChildKeeps`), the `vc` rules, and for (2) the error clause of
every `Triple` rule and the failure ref's tracking — the VC layer's five
files, then every dependent re-verified. Not started.

## 6. The twelve work packages, with stable IDs

`removes` = the premise that disappears from the endpoints when done.

| ID | Package | Removes | State |
|---|---|---|---|
| A1 | `closeLets` (1) final assign, (2) spine | part of `MachineCloses` (let, no call) | **proved** for every harness run (`transition_spine`) |
| A2 | (4) ports undriven | 〃 | **proved** |
| A3 | (5) core ≠ `out`, (3) operands ≠ `out` | 〃 | **proved** |
| A4 | (3) operand declared at the field's width | 〃 | **proved**; shape-side "port width = field width, positive" to be taken from the entry theorem's facts |
| A5 | (6a) positional invariant: readers of a `let` port after its operand's driver | 〃 | **proved** on the builder state: `fuel_spine` (statements only added in front; every arm's result made and driven; statements read, among protected names, only wires bound to variables the term `Uses`) and `spine_links` (`Tools/ShippingSpineOrder.lean`: for each field of a packed body, a suffix of the builder's body in which the field's wire is driven and which reads only what the fields before it may read; cache hits included). Its instantiation on the harness' module (protected = names in use at the start; `Vk k` = not a `let` port ≥ `k`) is part of A6/A7 |
| A6 | (6b) shape-side scoping condition + soundness; (6c) order of the closed body | 〃 | (6c) **proved** as a statement about lists (`closed_acyclic`, `Tools/ShippingClosedOrder.lean`): the let-closed body is `Acyclic` given the ordered transition body, distinct undriven ports, operands that are no port and not `out`, and "every reader of a port comes after the driver of its operand" — no assumption that the check passed. (6b) **proved**: `harness_links_at` instantiates A5 on the harness' module, `transition_closes` assembles the six conditions for EVERY run of the harness, under two conditions on the shape: (S1) field `k` uses only variables bound before `let` `k` — this is the endpoint check's own `LetsScoped`, nothing new; (S2) a field that is the variable of `let` `j` requires field `j` to be a variable — NEW, part of the stated domain (`MachineData.letsOk`), not a compiler gate. "No field is a `let` variable" is NOT asked |
| A7 | assembly: the six conditions ⇒ `MachineCloses` for let-only shapes; generators | `MachineCloses` for let-only children and parents | **done and connected**: `machineCloses_of_lets` (shape premises only) → `closes_of_data` (premises = the endpoint's `ok` + body equation + `letsOk`, all kernel-evaluated on generated data) → generated `f.machine_closes`. `#machine_endpoint` adds `f.machine_sound_closed` / `machine_ships_closed` / `machine_ships_wired_closed` (no `MachineCloses` in the type) where the data give it; the three R generators discharge a no-call child's `MachineCloses` by it. NOT covered: shapes with calls (B1/B2); the S2-refused shape (below) |
| B1 | `closeInsts` (one output) from the child-run facts | `MachineCloses` with calls | **derived** (as `MachineClosesAt`) for one-output calls of gate children and of slotless machine children, any repetition of callees, with or without `let`s; name separation (N1) left as premises. Current state: §0. History of this row: Appendix A. |
| B2 | `closeInstsG` (general) | 〃 | not started |
| C1 | lift grandchildren's `Defines` out of nested boundaries | bound `Defines` occurrences | not started; does NOT address §3.2–3.4 |
| C2 | depth / fuel limits | — (they are behaviour changes) | see G4 |
| C3 | `kidsCombB` narrowing | — | open: designs it rejects go to the legacy route (§4) |

### `let`s of `let`s and of inputs (checked 2026-10-13)

What the shape reader does, on real sources (`~` the probe is in the session
log; the reader's code is `machBindLet` / `machBindLetAlias` /
`machBindLetNamed`):

| Source | Hardware `let`s kept | Operands |
|---|---|---|
| `let a := x` (an input), `let b := a` | none (bare variables are substituted) | — |
| `let a := x + rs; let b := a; let c := b + a` | `a`, `c` (`b` is resolved to `a`) | both driven |
| `let a := x + rs; let b := x + rs` | one (same value → same `let`) | driven |
| `let a := x; let c := a + rs` | `c` | driven |

So on these the kept fields are compound and every operand is driven. The
reader CAN keep a field that is a bare variable (`machBindLetNamed`: a `let`
whose value is a slot; `machLetIndex`: a call's argument), and a bare `let`
variable only in a fall-through branch of `machBindLetAlias`. The reader is
`partial`, so none of this is a theorem.

What the real `closeLets` does with a `let` whose operand is another `let`'s
port, on hand-built modules (regression in `ShippingReflectCtxTest`):
`let0 := input; let1 := let0` — ACCEPTED (both aliases at the front, in
order); `let0 := x + x; let1 := let0` — REFUSED (the front alias reads a port
driven later), so the entry takes the legacy fallback there.

`closed_acyclic` follows the real behaviour: an operand may be an EARLIER
alias' port provided that alias' operand is driven by nothing. It does not
ask "no field is a `let` variable". The refused case stays outside
(`MachineCloses` is false of it); it is not hidden by a scoping condition.

### What A7's domain is, case by case (regressions in `ShippingMachineClosesTest`)

| Case | Reader's shape | In the guaranteed domain? |
|---|---|---|
| field that is an input (`let a := x`) | no hardware `let` on the source tried (`closesInputLet`, lets=0); as data: field = input variable | YES (`aliasOk` true; real endpoint closed) |
| `let` that is an earlier `let` whose field is a variable | data only | YES (`aliasOk` true; the real `closeLets` accepts) |
| `let b := a` after an operation (`closesOpAlias`, `reflAliasLet`) | ONE hardware `let` (reader resolves `b`) | YES for what the reader produces (real endpoints closed). The DATA shape `let0 := x + x; let1 := let0` is NOT: `aliasOk` false, and the real `closeLets` refuses it — `MachineCloses` is false there, the entry falls back to the legacy route. Registered as a refused case, not hidden |
| shared subexpression (`reflSharedLet`, cache hit) | 2 `let`s | YES (real endpoint closed) |
| `let`s chained under operations (`closesChain`) | 3 `let`s | YES |
| any shape with calls | — | `MachineCloses` (every world, every logger) is not derivable; `MachineClosesAt` is derived for one-output calls of distinct gate children (B1), otherwise stays a premise (B1/B2) |

`letsOk` is sufficient, not shown necessary: S2 mirrors the one refusal
observed; no claim that every shape outside it is refused. That the reader
never produces an S2-violating shape is NOT a theorem (the reader is
`partial`, G3) — for such a declaration `f.machine_closes` is simply not
generated and the premise stays.

### Effect on the 20 derived endpoints (`endpoint_premises.lean`, 2026-10-11)

Distinct `MachineCloses` occurrences (own contexts, bound contexts):

| Endpoints | Before | After |
|---|---|---|
| `callerLN`, `hftByte`, `callerL` (HR; children with `let`s, no call) | (6, 6), 1 context quantifier, 2 `ChildRanIn` guards | (6, 0), 0, 0 |
| the other 17 | unchanged | unchanged |

What remains everywhere is the PARENT's own `MachineCloses` (a shape with
calls: B1/B2) and, at depth ≥ 1, the children's (shapes with calls). The
counts are syntactic occurrences, not logical premises.

### Name separation (obligation N1, open) — 2026-10-11

The closed endpoints of B1 (`f.machine_design_svHR_closed`, …) are NOT
premise-free: they state conditions on the printed names of the compiler's
modules (`m.name = declName.toString`, proved from the run):

| Condition | When asked | Status |
|---|---|---|
| no callee prints as the parent (`c.toString ≠ f.toString`) | always | premise |
| different called declarations print differently (`c.toString = c'.toString → c = c'`) | ≥ 2 called declarations (`callerMix`) | premise; with one called declaration proved (kernel `decide` on `Name` equality) |
| no output port is named `inst{k}_{c}` | only if an output port's name starts with `i` | otherwise proved from the head character |

Why they are premises: `Name.toString` with escaping (the default, what the
compiler uses) does not reduce in the kernel — `decide`, `decide +kernel`,
`rfl`, `with_unfolding_all rfl` all get stuck in the escape test
(`toStringWithToken`, private, well-founded string scans). The UNESCAPED
renderer (`Name.toString (escape := false)` = `toStringWithSep "." false`) is
structural and does reduce (`decide` proves `≠` on literals), but no theorem
in this Lean relates the two, so it gives no bridge. That is a fact about
evaluation, not a proof that the separation is unprovable: a bridge
("for a name whose components need no escape the two renderers agree")
would discharge all three by kernel evaluation. NOT done; no `native_decide`,
no axiom. The test evaluates the conditions true with compiled code
(evidence) and checks that the closed endpoints state them.

Repeated callees (2026-10-11, restriction removed): several instances of one
declaration are ONE module by the child cache, derived from the order the
closing's `mapM` runs — not from an assumption that two real compiles agree,
and with ANY calls between (`Tools/ShippingCallsSame.lean`):

* `synthesizeChild_post`: a run of the memoised entry leaves its result in
  the cache under the declaration's name, and returns the cached value on a
  hit;
* `synthesizeChild_pin`: from a world of POSITIVE synthesis depth a run of
  the memoised entry keeps every entry the cache has (any fixed key and
  value). It is the invariance theorem at a law witness whose AUXILIARY
  predicate is "the cache holds `y0` under `c0`": `RefLaws.aux` is a proof
  parameter of the bundle, not a runtime law (`withAux` gives any witness any
  such predicate; its one condition, `auxInsert`, is that a miss inserts
  under an absent key). The depth-0 clear is kept SEPARATE: the entry
  theorems ask `D = 0 → aux {}`, vacuous at a positive depth and false of a
  pin at depth 0 (a top-level entry does clear the cache);
* `mapM_loop_all` / `closeInstsM_run_all`: two calls of one declaration get
  the same child;
* the depth is positive where the machine synthesis runs: `MachineClosesAt`
  asks its worlds to be inside an entry (`DepthPos`), which its users derive
  from the entry's own depth bump (`core_reads_inv` tracks it) — not a new
  premise of any endpoint.

`callerRep` (pick, pick) and `callerABA` (pick, pickD, pick) are closed
through the SV endpoint; the `sepB` restriction and its refusal are gone.

## Appendix A. History of the B1 row (superseded statuses, oldest last)

Kept for the record; where it contradicts §0, §0 is current.

**DERIVED 2026-10-11 for one-output calls of GATE children, at invariant worlds (`MachineClosesAt`), with name premises left** — `machineClosesAt_of_gateKids` (`Tools/ShippingCallsGate.lean`): from ONE harness run `transition_calls_facts` gives the port split, body shape, per-`let` facts under `okRule`, empty design and module name; `closeInsts_of_facts` assembles instance statements, Kahn order, the order checks, `linkedOk`, `designWith` resolution and `kidsCombB`; each child is read off the `RealChild` witness the run's closing returns (`childFull_of_real` = `gate_child_fullFacts` at the child's own run, reflection moved by `EntryDefines.ctx`). Generated as `f.machine_closes_at` (`#machine_closes_at`), and the HR endpoints lose the premise (`f.machine_design_svHR_closed`, `…ships_hierHR_closed`, `…composedRA_closed`): `caller`, `callerTwice`, `callerNested`, `callerD`, `midH`, `callerMix` (`Tests/Compiler/ShippingCallsCloseTest.lean` audits that the closed statement and every definition under it reach none of `MachineCloses` / `MachineClosesAt` / `CallsPure` / `CallsClose` / `LetsClose`). `CallsPure` is proved inside, it is not a premise. **What replaced the premise**: (i) each callee's `EntryDefines` (already asked by the endpoint); (ii) NAME conditions the kernel cannot evaluate because `Name.toString` does not reduce — no callee's name is the parent's (always), the callees' names are distinct (several callees), no output port is named `inst{k}_{callee}` (asked only if an output port's name starts with `i`; otherwise proved from the head character). They are evaluated true by compiled code in the test: evidence, not proof. (iii) kernel-evaluated data checks: the endpoint's `ok`, `letsAliasOk`, `gateCallsOk` (= S3 `callsOk` + slots are the layout's + tail binders have ports + a `let` exists + no several-output call), no memory child, argument counts. **Slotless machine-route children DERIVED (2026-10-12)**: a child that is a combinational body with hardware `let`s, no register and no call (`pickByteH`, the IP library's `httpGetByte`) is compiled by the machine route; its module `closeMachine (closeLets t)` has the child-side facts — order from `closeLets`' own `assignmentOrderCheck`, membership of EVERY read (input port or driven) from the transition's closure, the alias statements and the packed concatenations (`closed_of_acyclic` needs that membership; acyclicity alone does not exclude an undefined read), through the zero-width cleanup and the checked merge (`Tools/ShippingMachineChildComb.lean`), from ONE run of the child's full entry and the child's own (proved) closing (`Tools/ShippingMachineChildRun.lean`: `machineChild_iface`, `machineChild_of_real`). The parent's child contract is the interface `ChildIface` (gate children give it by `ChildFull.iface`). `callerL`, `callerLN`, `hftByte` are closed through the SV endpoint; their child premise is `MachineDefines` of the child. Data conditions of such a child, kernel-evaluated: `ok`, `gateCallsOk`, no call, no slot, one output `out`, output types of their widths. **Not covered (premise stays)**: machine children with calls of their own or without a `let`, several-output / sequential children (`closeInstsG`, B2). **Parents without a `let` (K = 0)**: the theorem no longer asks a `let` (`closeLets_eq'`; `closeInsts_of_facts`, `transition_calls_facts` and `gateCallsOk` have no `K ≠ 0`), but no real machine-route parent with calls and no `let` was found — a call's arguments are `let`s, and the zero-argument caller tried (`callerK`) is not a machine shape (legacy route) — so no positive endpoint is shown for that branch. R0 (sequential / memory children, depth 0) is migrated: `machine_ships_hierC` is generic in the closing premise, `f.machine_composedTRA` / `f.machine_ships_hierR` / `f.machine_design_svR0` ask the parent's `MachineClosesAt` and no all-worlds `MachineCloses` (test-audited); that premise is NOT derived for them (B2). NR (depth ≥ 1) is migrated too (2026-10-11): `MachineRunNC`, `seqChildRunN_of_composedC`, `composedN0/Nn_of_HR` and `machineRunNC_of_real` use `MachineClosesAt`; the NR endpoints are built from the `…RA` heads and `machine_ships_hierC`. **Discharged at depth** (not only migrated): a child with calls whose `c.machine_closes_at` exists gets its closing from its OWN boundary (its children's `EntryDefines`, in the contexts and world of the child's own run — `machineRunNC_of_real`'s `hcl`), so `midH`'s closing is no longer a premise of `mixD1.machine_design_svNR1`, `grandH.machine_design_svNR1`, `topD2.machine_design_svNR2` (test `CLOSING AT DEPTH`: no closing premise about `midH`; no all-worlds `MachineCloses` at all); `midH`'s name separation (N1) is asked instead. What stays at depth: the `MachineClosesAt` of every parent of SEQUENTIAL children (`mixD1`, `grandH`, `topD2`, `mid2`) — B2, not derived. Leaf children without calls keep `MachineCloses` only where `machine_closes` is not derived (none in the tests). Conditional on the generic laws (G5 unchanged); S3 / `letsAliasOk` are per-declaration evaluations, not reader theorems (G3). Earlier status of the parts — reduced, not derived: `machineCloses_iff` (`Tools/ShippingClosesSplit.lean`): `MachineCloses ↔ LetsClose ∧ (insts ≠ [] → CallsClose)`; `LetsClose` is proved from the data for shapes WITH calls too (`letsClose_of_data`; checked on `caller`, `callerTwice`, `callerNested`). What is left is `CallsClose` = every run of `closeInstsM`/`closeInstsGM` after an accepted transition returns a module. It is NOT substituted into the endpoints (it would be a smaller premise under a new name, not a discharge). Its conditions, read off `closeInsts`: child synth installed; `instStmt` per call (port counts, names, the output wire declared); `topoBody` succeeds; `woCheck` ×2, `isPermOf`, `seqOf`, key/memory names distinct; `linkedOk`; every child found by its own name in the merged design (name collisions); `noInstOfB`; `kidsCombB` (false for a one-output SEQUENTIAL child — a real fallback, `useCtr1`). None proved for every run. **Finding (2026-10-11):** `MachineCloses` as the endpoints state it — every run from EVERY world, with EVERY logger — is not derivable for a shape with calls: the closing reads `sparkleChildSynth` and returns nothing where it is not installed, and an arbitrary logger is an arbitrary `IO` action. The derivable statement is `MachineClosesAt` (worlds satisfying `InvV`, the compiler's `profLogIO`), `Tools/ShippingCallsClose.lean`: `closeInstsM_run` / `closeInstsGM_run` (a run from an invariant world is the PURE closing of `ChildrenReal` children, module or nothing) and `machineClosesAt_of_pure` (`LetsClose` + `CallsPure` ⇒ `MachineClosesAt`, under `RefLaws` only). **State 2026-10-11 (later):** (B1-1) DONE for one line and its siblings: `MachineClosesAt` (now `ChildLaws → ∀ b w, InvW w → …`, `Tools/ShippingChildRun.lean`) is what the R base theorems and the six R trace heads take (`…RA`; the old names are wrappers), `machine_ships_hierHC` is generic in the closing premise, and the HR generator builds on them: the nine HR endpoints (`caller`, `midH`, `callerNested`, `callerLN`, `hftByte`, `callerMix`, `callerTwice`, `callerD`, `callerL`) ask `MachineClosesAt`, not `MachineCloses`. R0 and NR generators not migrated. `MachineClosesAt` is still a PREMISE of those nine. (B1-2) `closeInsts` success, pure side DONE (`ShippingTopoBody`, `ShippingTopoChecks`, `ShippingTopoLinked`, `ShippingCloseInstsSome`, `ShippingCloseChecks`, `ShippingCloseMachineFacts`): four steps ⇒ a module; Kahn's loop does not get stuck given a rank; `woCheck` / `isPermOf` / `seqOf` / `linkedOk` of its result; the closed machine's body statically. OPEN, run side, for the minimal parent `caller` → `pick` (a one-output combinational gate child): (i) the rank on names for a real transition — needs the per-field read facts (`LP`) extended to call outputs and a new shape condition S3 "a field uses call j's output only if all of j's argument `let`s come before it"; (ii) `instStmtsOf` — the child's interface from its reflection (inputs = its binders' ports, one output, no clk/rst), a fresh instance name (a naming invariant of the harness); (iii) each instance agrees with its child's ports; (iv) `designWith` name resolution (a name collision is a real failure and stays one), `noInstOfB`, `kidsCombB` (false for a one-output sequential child: stays a counterexample). `CallsPure` as stated quantifies the harness run and the children independently; it will be replaced by a contract on the real run's children when (i)–(iv) are in. **State after the third pass (2026-10-11):** per condition of `closeInsts`, what is derived from a REAL run and what is not — (a) `topoBody` succeeds, `woCheck` ×2, `isPermOf`, `seqOf`, key names: derived from facts about the closed body (`closeChecks_of`, `static_checks`, `closeMachine_body`), GIVEN a rank; (b) the rank: derived from the run's per-field read facts (`transition_fields` → `letOperands_facts` → `rank_of_facts`, `closed_classes`), GIVEN the instance statements' form and the shape condition S3 (`FieldsOK` with the rule `okRule`: a field uses a call's output only once the call's argument `let`s are passed) — S3 is a decidable check on the data (`MachineData.callsOk`, sound for the premise by `fieldsOK_of_B`); it is kernel-evaluated to `true` on `caller`, `callerTwice`, `callerNested` (`ShippingMachineClosesTest`); its relation to the shape reader is NOT proved (G3); (c) the instance statements (`instStmtsOf`), `linkedOk`'s instance/child agreement: NOT derived — need the child's interface at the FULL entry (ports kept by `dropZeroWidthModule` / `mergeChecked`: lemmas exist) from the child's reflection (`gate_core_facts` gives the core module's ports); (d) `kidsCombB` (five conditions: assign-only, read closure, outputs driven, outputs not inputs, inputs connected by wires): **child side DERIVED 2026-10-11** — K1 `harness_closed` / `transition_closed` (every harness run's module reads only its input ports and names driven earlier; `Cl` threaded through all translator arms, the cache hit/miss, the step; no closed-reads premise), K2 `mergeChecked_closed` (the duplicate merge keeps closure and the driven names, from `validateMerge`'s own step state), and `gate_child_comb`: a gate child's FULL-entry module (core → zero-width cleanup → checked merge, the entry's actual path, no optimizer) is assignment-only, closed over its inputs, drives its one output `out`, with distinct allocated input names — from the run and `EntryDefines`. Still open for `kidsCombB` as a whole: the fifth condition (every input connected by a wire — the instance statement's form), `out` not an input (from allocated names; trivial, not assembled), and that the module an instance resolves to IS the child (`designWith` name resolution). The original design note follows: (K1) a new parameter `W` of the spine invariant, dual to `V`: `W x → x is protected or driven in the current body`, every emitted statement reads only `W` names, a bind extends `W` with the wire its first action returns (from the existing `Src` / `Drives` / record-invariant results, cache hits included), and with `V := "is an input port's name"` (bound wires are port names) a protected read is an input port — not merely a name in use; reversed builder order ⇒ "driven earlier" in the finalized order; (K2) preservation through the FULL entry: `dropZeroWidthModule` (body unchanged on typed modules), `mergeChecked` = `mergeDuplicates` on assign-only bodies — closure of the merged body from `validateMerge`'s step state (an alias points at a name already defined), to be extracted from `validateStep`; the optimizer is not applied to a child at the full entry (`synthesizeCombinational_checked` gives the two forms only — to be re-checked when K2 is written); (K3) the other four conditions from `PrintBaseAt` (one output `out`, inputs distinct, allocated names) and the instance statement's form. Previous wording — `readsClosedB` asks that every name a child statement reads is an input or driven EARLIER; the translator's proved order invariant (`Acyclic`) says only "not driven later". A new invariant through the 21 translator arms (and its preservation by the duplicate merge) is needed; (e) name resolution in `designWith`, `noInstOfB`: NOT derived. `closeInsts_some_of` is a decomposition (it assumes the four steps), not a derivation. `rank_of_names` / `rank_closed` assume one driven name per statement: B1 only

## 7. Gaps not among the twelve

| ID | Gap | Why it blocks a general theorem |
|---|---|---|
| G1 | `designCheck`, `outsCheck`, `shipsHier(H)Check`, `kids*` are obligations evaluated per declaration, not derived from the run | they are conclusions about the compiler's output; "true on the tested declarations" is not derivation. Each must be proved of every machine-route output, or run by the compiler (without rejecting what it accepts today), or stay a stated premise |
| G2 | legacy route has no source theorem | a successful compile may be outside every theorem; needs a stated domain (§4) |
| G3 | reader soundness, source ↔ `MachineData`, generator coverage | endpoints exist per declaration by generation; no theorem quantifies over sources |
| G4 | fuel / depth: (a) monotonicity `fuelFix k ⊑ fuelFix (k+1)`; (b) equivalence with the former `partial` definitions | (a) is provable by a relational walk; (b) cannot be stated in the kernel — a `partial` definition has no unfolding equation. Adding one as a law would be an assumption, not a proof. Honest form: the total fuel-bounded definition IS the compiler now; "same as before on runs that used to succeed" is tracked as untested-in-general, with the depth-1024 and fuel-2^20 rejections listed as behaviour changes |
| G5 | `RefLaws` audit: compiler-specific constructors in `Framed`; satisfiability | audited 2026-10-11 (§5): an INCONSISTENCY found and removed (`ioFlush` of any stream); `profLog` is compiler-named and not derived; `msgToString` is an assumption; a model is not exhibited |
| G6 | final statement shape: existence + uniqueness over every finite `T` is proved per endpoint; the quantification "for every source and run" is not a Lean statement yet | the target of §1 has no formal counterpart to check progress against |
| G7 | printer | trusted by design (TrustBase §6c); listed so it is not forgotten |

## 8. What is claimed

- Proved for every run: the child-cache invariant (`childKeeps`), the
  translator's order / value contract on quoted terms (earlier work), and
  `closeLets`' six conditions on packed machine bodies under S1/S2, hence
  `MachineCloses` for every shape without calls whose data pass `ok` and
  `letsOk`.
- Validated per declaration (kernel-checked, generated): the 20 endpoints.
- Not claimed: a theorem over all sources; anything about the legacy route;
  that the per-declaration checks hold of every output.
