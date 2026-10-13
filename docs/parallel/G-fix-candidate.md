# Finding G: fix candidate (save / restore the sub-instance port map around a nested entry)

Worker B, branch `par/b-12` from `fix/nested-let-cache-build` (`83b2faf9`), plus the six
finding-G files of poc `f5f24c9a`. **ISOLATED CANDIDATE, not integrated. WRITTEN, NOT BUILT:
no `lean`, `lake` or `iverilog` was started; every log line below is a PREDICTION.** Line
numbers are this branch's.

Kinds of statement: **READ** (what the code says), **PREDICTED** (what a run should print),
**GUESS** (a proof edit whose elaboration I could not check), **NOT ESTABLISHED**.

## 1. The change (`Sparkle/Compiler/Elab.lean`, `synthesizeCombinationalCoreWith`)

Same style as the finding-F change of `83b2faf9`, one more ref:

| Line | Text | When |
|---|---|---|
| 5489–5491 | `let savedSubInstanceOutputs ← if depth == 0 then pure {} else sparkleSubInstanceOutputs.get` | every entry (a `pure` at depth 0) |
| 5515 | `sparkleSubInstanceOutputs.set {}` in the `else` (nested) block | nested only |
| 5540 | `sparkleSubInstanceOutputs.set savedSubInstanceOutputs` inside `if depth != 0` of the `finally` | nested only |
| 5443–5444 | the old comment "relies on … persisting across nested synths … so we ONLY snapshot the fvar-value map" replaced (it described the behaviour removed) | comment |

+15 / −5 lines, 3 of them code. No `throw` added, no source refused. At depth 0 the executed
operations are the old ones plus one `pure {}` (no ref read, no ref write): the depth-0 clear
block 5492–5504 is untouched, the `finally` does nothing more at depth 0.

Effect: a nested entry starts with the port map EMPTY (as an outermost entry does at 5498) and
its parent gets back, on return OR throw, exactly the map it had when it called the child.

## 2. Decisions

### (a) Does the PARENT legitimately depend on entries a child wrote? — No.

Reader sites of `sparkleSubInstanceOutputs` (READ):

1. projection shortcut, `Rec.handleDefinitionUnfold` 6456–6459 (hit ⇒ `return some w`, no
   declaration check) and its re-read after translating the call 6464–6467;
2. instance-emit branch 6682–6736 (`alreadyEmitted`; if the wire is not declared in the
   current builder it RE-DECLARES the cached names and emits a new instance);
3. certified projection arm, `translateProjInstanceUncachedWith` 8633–8642 via
   `instArmOutGet` 8458 (hit ⇒ `return w`, no check; "first output present" ⇒ legacy);
4. `restoreWireCaches` snapshot 5635 / 5651 (inline catch); 5. debug print 6376.

Argument. An entry is `(callee, argument WIRE NAMES, port) ↦ WIRE NAME`. A wire name means
something only inside the builder that allocated it; a child has its own builder
(`CircuitM.init`). So an entry written by a child can be USED by the parent only as a name:

* through readers 1 and 3 the parent would get a name it never declared, or one it declared for
  something else — that is finding G with the roles swapped, never a wanted result;
* through reader 2 the parent re-declares the child's NAMES and emits its own instance. This is
  the "cross-module reuse" of commit `ae779e57`. Its message says what it is: a repair for
  sibling wrappers that "returned the cached wire name without ever declaring it" — a
  work-around for the leak, not a feature. No hardware is shared: one instance per module either
  way. With the candidate the second module misses and allocates its own wires for its own
  instance.

The performance reason in the comment 5410–5424 (do not wipe on re-entry or every projection of
`let engine := kvHw …` re-walks `kvHw`) is not touched: (i) the re-walk is prevented by
`sparkleSubModuleCache` / `sparkleChildCache`, which are not changed; (ii) the PARENT's own
entries are what later projections of the same call hit, and they are written after the child's
entry has returned (6741; `instOutWires` 8608) and are restored after any later nested entry.

So same-style is right; the alternative (module name in the key) was not written.

What DOES change (PREDICTED, by reading): in a module that, before, met a foreign entry at
reader 2, the output-port wires of that instance now carry the module's own fresh names instead
of the other module's names. Same statements, same function, possibly different TEXT. The
re-declare branch stays reachable (same builder name after a declined machine arm, or after a
`catch` that rolled back the builder but not the ref); it is not removed.

### (b) The legacy single-output map (`sparkleSingleOutInstanceCache`) — not treated.

Its key is `parent module name # child module name # connections` (6640, 8583): a
child and its parent, or two siblings, never share a key, so a nested entry cannot hand the
parent's or a sibling's wire to another module. The hole B-11 recorded (same parent NAME, second
builder: the legacy arm after a declined machine arm) is inside ONE entry; a save/restore around
nested entries does not reach it. `SingleOutHitTest` shows only an injected state. Unchanged.

### (c) Refs still neither cleared nor restored around a nested entry after this change

| Ref | Why it is left |
|---|---|
| `sparkleSingleOutInstanceCache` | (b): key carries the module being built |
| `sparkleFvarZetaVisited` | cleared at NO entry; can only cause a throw (B-11 §3) |
| `sparkleSubModuleCache`, `sparkleChildCache` | run-wide by design: declaration name ↦ compiled module |
| `sparkleTypeCache` (+ hit/miss counters) | run-wide: `Expr` ↦ type, no wire names |
| `sparkleCallCounter` | never reset; only a limit |
| profile counters | diagnostics |

Cleared on nested entry AND restored: fvar value map, wire widths, let wires, loop wires, alias
map, and now the sub-instance port map.

## 3. Proof patches (statements unchanged)

Every proof under `Tools/` that unfolds the entry (`grep synthesizeCombinationalCoreWith`): five.

| File | Lemma | Edit | Confidence |
|---|---|---|---|
| `Tools/ShippingMemoLaws.lean:198` | `outer_reset_reaches` | one more `RunsTo.bind` (the 6th `pure`) | mechanical copy of the `83b2faf9` patch |
| `Tools/ShippingMemoLawsWith.lean:82` | `outer_reset_reaches_with` | same | same |
| `Tools/ShippingChildKeeps.lean:340–368` | `fin_triple` | new argument `m6 : Std.HashMap (UInt64 × String) String`, one more `ST.Ref.set` in the stated program, one more frame step `Framed.sideSet _ .subInstOut` | **GUESS** (see below) |
| `Tools/ShippingChildKeeps.lean:401–447` | `core_keeps` | `body` takes `m6`; 6th `tpure` (depth 0); 6th `tget` and 6th `tset` (nested); `body _ _ _ _ _ _` | **GUESS** |
| `Tools/ShippingEntrySoundness.lean:1102` | `synthesizeCombinationalCore_reads` | NONE — `iterate 40 (peel_bind / peel_ite)`; 83b2faf9 did not touch it either | expected to pass unchanged |
| `Tools/ShippingChildRun.lean:144` | `core_reads_inv` | NONE — `iterate 40 (peel_inv …)`; a `get`/`set` of a `SideRef` goes through `inv_framed` | expected to pass unchanged |

`fin_triple` is not exported with its arguments anywhere else (`grep fin_triple`: only
`core_keeps`); its statement is an internal helper, the theorem statements (`core_keeps`,
`outer_reset_reaches*`) are unchanged.

Why the `ChildKeeps` edits are guesses: (1) the stated program must be syntactically what
`unfold` + `simp only` leave — I wrote `ST.Ref.set sparkleSubInstanceOutputs m6` by analogy with
the three lines above it; (2) `SideRef.subInstOut` exists (`Tools/ShippingChildInv.lean:74`) so
`tget` / `tset`'s `constructor` should find it, not checked; (3) the order: the new save is the
LAST `pure`/`get`, the new nested `set {}` the LAST of the nested block, the new restore the
LAST of the `finally` — the tactic counts follow that order.

## 4. Test edit (`Tests/Compiler/SubInstanceKeyTest.lean`)

`fixedProbe` (223): seed the port map with one entry (key hash 0), run `synthesizeChild hW` at
depth 1 (`hW` writes entries of its own), read the map back; `fixed` = the nested run returned
and the map is exactly the seed. New first line `SUBINSTKEY FIXED: …`, new last line
`SUBINSTKEY: fixed=…; collisions […]`; when `fixed=T` and any collision flag is `T` it throws.
All existing log lines keep their text (including the last old one, "nothing is asserted",
which is true of the unfixed trees). Still not in `Tests.AllTests`.

## 5. Predicted lines on this branch

```
SUBINSTKEY FIXED: nested entry ran=T restores sub-instance port map=T (entries left=1, the seed is 1) => fixed=T …
SUBINSTKEY WR DETECT: … [] => collision=F
SUBINSTKEY RW DETECT: … [] => collision=F
SUBINSTKEY hWR CHILD …hW: nested==alone T kSD instances nested=1 alone=1 undeclared nested=[]
SUBINSTKEY hWR CHILD …hR: nested==alone T kSD instances nested=2 alone=2 undeclared nested=[]
SUBINSTKEY hWR DETECT: … [] => collision=F
SUBINSTKEY: collision WR=F RW=F hWR=F (logged only; nothing is asserted)
SUBINSTKEY: fixed=T; collisions []
SUBINSTKEYSIM …hTopWR: command==source T nofe==source T command==nofe T x-cycles command=0 nofe=0 cycles=94
SUBINSTKEYSIM …gTopWR / gTopRW / gW / gR: command==source T (as on poc)
```

On poc / `83b2faf9` the same file: `fixed=F` (entries left=3 PREDICTED), `hWR … collision=T`,
no throw. Why `hR nested==alone T`: with the map empty at its entry, nested `hR` differs from
alone `hR` only in refs that hold no wire names of another module (table (c)); on poc that
difference was already invisible for `hW`, `gW`, `gR` (measured `T`).

NOT ESTABLISHED: all of §5; the leftover-keys text of the `top` lines (it changes: after the
candidate only the TOP's own entries remain); `SINGLEOUT` lines (expected unchanged).

## 6. Corpus scan by reading (no runs)

Pattern: two `@[hardware_module]` parents synthesised in ONE top-level run, each projecting
directly (no `let`) a call of the same multi-output `@[hardware_module]` child over argument
wires of equal names.

Strategy (`Sparkle/ Examples/ IP/ Tests/`):

1. `grep -A5 '@[…hardware_module…]'` → the tagged definitions (165); by their result type the
   multi-output ones (record / tuple results: `kvHw`, `memcachedServer`, `wMul*`, `wSponge`,
   `wRx`, `wTx`, `wSignCore`, `regFile`, `ladderEngine`, `opCtrl`, `signCtrl`, `wSha*`,
   `wKeccakF`, `wHmac`, `wBlock`, `wRfc`, `wKf1600`, `wPointOp`, `wScalarMul`, `wInv`, `wSign`,
   `sign*SmallDemo`, `signCoreSmall`, `pe`, `eng2`, `cnt`, `mid*`, `acc`, `childTwo`, `kTwo`,
   `kTri`, `kAlias`, `kPair`, `rcH`, `ctr1`, `kSD`);
2. `grep -E '\((ns\.)?(<those names>) '` — a parenthesised call (the head of a direct
   projection, also when the call spans lines), and `|>.` on the same names;
3. every other call site of those names (`:=`, `←`, line start) to see the binding form.

Direct projections of a tagged multi-output call found:

| Site | Parents | In one run? |
|---|---|---|
| `IP/Net/MemcachedServer.lean:495`, `:502` | `memcachedServerByte`, `memcachedServerValid`, both TAGGED, both `(memcachedServer inByte inValid).<field>` — same callee, same argument names | **No declaration in the four trees calls either wrapper** (`grep`: only their definitions and comments). No top synthesises both. This is the exact G shape waiting for a top (it is the shape `ae779e57` worked around). |
| `Tests/Compiler/ShippingHierarchySoundnessTest.lean:68, :71, :170, :173` | `parentLo`, `parentHi`, `parentProjLeaf`, `parentProjArg` — NOT tagged; each is synthesised as its own top (depth 0) | no: one module per run |
| `Tests/Compiler/SubInstanceKeyTest.lean` `hW` / `hR` / `hTopWR` | the constructed finding | yes (the finding) |

Look-alikes excluded: `Tests/IP/Net/UsbWebServerJITTest.lean:42–65` (five tagged wrappers in one
top, two of them projecting the same call `slipDeframerHW wireByte wireValid`) — the callees
(`slipDeframerHW`, `ipv4RxParser`, `tcpRxParser`, `httpRequestParser`) are NOT tagged, so no
instance and no port-map entry; `IP/Net/HFTQuote.lean:112–124` — wrappers and `quoteEngine`
untagged. All other call sites of multi-output tagged children are `let`-bound (≈70 sites, most
inside `circuit do`).

Result: **no declaration with the finding-G pattern in a run of the corpus, by reading.**

Cannot be decided without running:

* `let`-bound projections outside the machine route. Measured on poc only for `gTopWR` /
  `gTopRW` (equal to the source); whether another `let` shape reaches reader 1 or 3 with a
  foreign entry depends on the route and on front-end unfolding. Candidates of the shape "two
  modules of one run call the same multi-output child": `ShippingChildBoundaryTest.lean:282–283`
  and `ShippingDesignSVTest.lean:38, :47` (`mid2 en` and `midH en`, `mid2` itself calls
  `midH en`), the `EcdsaSign*` / `PolicySign*` / `Fido2Demo` tops (`wRx`, `wSignCore`, `wMul`
  called from several tagged modules, argument names differ at most sites). All `circuit do`:
  by reading the machine route does not use this ref for its calls.
* Whether any measured declaration's TEXT changes under the candidate (decision (a), last
  paragraph). The 84-declaration legacy digest and the 361-declaration digest against
  `83b2faf9` decide it; a changed digest is not by itself a defect (names of port wires), but
  each changed declaration then needs its function re-checked (simulation).
* Whether two different calls can share a key through `Expr.hash` (unchanged by the candidate).

## 7. Build order for the integrator (under `cgrun.sh`, serial)

1. `lake build Sparkle.Compiler.Elab`
2. `lake build Tools.ShippingMemoLaws Tools.ShippingMemoLawsWith Tools.ShippingChildKeeps`
   (then `Tools.ShippingEntrySoundness`, `Tools.ShippingChildRun` — unpatched, must still pass)
3. `lake build Tests.Compiler.SubInstanceKeyTest` → `SUBINSTKEY` lines (§5)
4. `scripts/shipping-coverage/subinst_key_sim.sh` (after 3, not next to a build)
5. `lake build Tests.Compiler.SingleOutHitTest`, `Tests.Compiler.NestedLetCacheTest`
   (`fixed=T` and its digests against `83b2faf9`)
6. `lake build Tests.AllTests`; then the corpus digests / `status.txt` diff.

## 8. What may not elaborate, most likely first

1. `core_keeps` (`ShippingChildKeeps`): tactic counts / the shape of `body` against the unfolded
   entry.
2. `fin_triple`: the stated program's last line, `.subInstOut` as an anonymous constructor.
3. `fixedProbe` in the test: the `Std.HashMap (UInt64 × String) String` literal and `==` on its
   `toList`; `synthesizeChild hWName` at depth 1 from reset refs.
4. `outer_reset_reaches`, `outer_reset_reaches_with`: one line each; low.
5. `Elab.lean`: the type ascription of the saved map; low.
6. Not an elaboration risk but a result risk: a `Tests.AllTests` test that pins the TEXT of a
   module which used to re-declare a sibling's wire names.

## Verification of this candidate in isolation (integrator, 2026-10-13)

Tree: `fix/subinst-key-build` = par/b-12 e027a8df + ONE integrator change (`set_option maxHeartbeats 1600000 in`
on `synthesizeCombinationalCore_reads` in `Tools/ShippingEntrySoundness.lean`: the first build timed out
there at 200000 heartbeats; statement unchanged). Worker patches of `ShippingMemoLaws`, `ShippingMemoLawsWith`,
`ShippingChildKeeps` built as written. All runs through cgrun (3 GiB, swap 0, one job).

Measured on this tree:
- `Tests.AllTests`: Build completed successfully (1172 jobs — this tree's base is 85ebb9fd, not poc's head).
- `SubInstanceKeyTest`: `fixed=T; collisions []` (hWR collision was T on poc and on 83b2faf9).
- `subinst_key_sim.sh`: hTopWR, gTopWR, gTopRW, gW, gR all `command==source T`, x-cycles 0 (hTopWR was got 14 / want 24).
- `nested_let_sim.sh`: fTop, fMid, lPlain `command==source T`, x-cycles 0.
- `writer_sim.sh`: 7/7 `new==source T`.
- Combined digests equal to poc's and 83b2faf9's runs: 361 declarations 11874691237837614088; 84 declarations 2141260620024790681.

Not established: equality for all successful inputs; a corpus declaration that had the Finding-G pattern
(none found by reading); the per-declaration digest lines were compared only through the combined values;
NOT integrated into poc — integration is the user's decision, and would be re-verified on the integrated tree.

Run records:
- `20261013-035121-gfix-tools`: result=exit-code, exit=1, memory_peak_file=1325568000
- `20261013-040044-gfix-tools2`: result=success, exit=0, memory_peak_file=1991503872
- `20261013-042102-gfix-all`: result=success, exit=0, memory_peak_file=1515905024
