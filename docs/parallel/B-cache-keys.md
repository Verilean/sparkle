# B-11: the cache keys finding F did not cover

Worker B, branch `par/b-11` from `85ebb9fd` (`poc/roundtrip-proof`).
**Everything here is WRITTEN, NOT BUILT. Nothing was run** (no `lean`, no
`lake`, no `iverilog`). Line numbers are `Sparkle/Compiler/Elab.lean` at
`85ebb9fd`. Three kinds of statement are kept apart:

* **READ** — what the code at `85ebb9fd` says, with the line;
* **PREDICTED** — what I expect a run to print, derived from READ;
* **NOT ESTABLISHED** — open.

No "wrong output" is claimed anywhere below: there is no log. A stale cache
entry is not by itself a wrong output; the candidates are sources for which
I predict one, and the probes that would show it.

Trees: "poc" = `85ebb9fd`; "fix" = `fix/nested-let-cache-build` (`83b2faf9`),
whose whole diff under `Sparkle/` is: the nested entry also saves (after
5465) and restores (after 5509) `sparkleLetWireCache`, `sparkleLoopWireCache`,
`sparkleWireCanon`. It touches no other ref, so every statement below about
another ref holds for both trees.

## Summary

| Item | Verdict | Trees | Files |
|---|---|---|---|
| 1 `sparkleSubInstanceOutputs` | **candidate G**, constructed real-entry source, silent wrong wiring PREDICTED | poc and fix | `Tests/Compiler/SubInstanceKeyTest.lean`, `scripts/shipping-coverage/subinst_key_sim.{sh,lean}` |
| 2 legacy one-output hit | lookup is unvalidated (READ); reachability of a stale entry bounded to ONE hole, NOT ESTABLISHED | poc and fix | `Tests/Compiler/SingleOutHitTest.lean` (seeded rows + the constructed parent for the hole) |
| 3 zeta marks | bounded: a mark can only cause a throw; a stale mark is unreadable inside one Lean process | poc and fix | size logged in `SingleOutHitTest.lean` |
| 4 full ref table | below; two refs are reset at NO entry (`sparkleFvarZetaVisited`, `sparkleCallCounter`) | — | this note |

## 4. The table (READ)

Entry = `synthesizeCombinationalCoreWith` (5389–5509). "depth 0" = the block
5466–5478; "nested" = the block 5479–5488; "saved/restored" = 5448/5463 and
the `finally` 5504–5509; "inline catch" = `restoreWireCaches` (5612–5623)
called from `Rec.tryInlineUnfold` (6282, 6298); "declined arm" = between
`synthesizeMachineCertified` returning `none` (5294, 5301) and the legacy
arm's `CircuitM.init` (5357), where the code does nothing to any ref.

| Ref (declared) | Key ↦ value | Written | Read | Cleared at depth 0 | Cleared on nested entry | Saved / restored around a nested entry | Restored at the inline catch | Reset at a declined arm | Restored when a nested entry THROWS |
|---|---|---|---|---|---|---|---|---|---|
| `sparkleWireWidthCache` (162) | wire name ↦ width | 181, 200, 208, 233, 251, 275, 283, 6698 | 217 | yes 5475 | yes 5485 | yes 5463 / 5509 | yes 5621 | no | yes (`finally`) |
| `sparkleFvarValueMap` (983) | fvar name ↦ value | 7843 | 6378 | yes 5474 | yes 5484 | yes 5448 / 5508 | yes 5622 | no | yes (`finally`) |
| `sparkleLetWireCache` (990) | canon key ↦ wire name | 7835 | 7806 | yes 5476 | yes 5486 | **poc: no** (finding F); fix: yes | yes 5616 | no | poc: no; fix: yes |
| `sparkleLoopWireCache` (1007) | canon key ↦ wire name | 6143 | 6120, 1277 | yes 5477 | yes 5487 | **poc: no**; fix: yes | yes 5617 | no | poc: no; fix: yes |
| `sparkleWireCanon` (1013) | wire name ↦ wire name | 6142 | 1220 | yes 5478 | yes 5488 | **poc: no**; fix: yes | yes 5618 | no | poc: no; fix: yes |
| `sparkleSubInstanceOutputs` (1051) | (hash of canon call key, port name) ↦ wire name | 6710, 8432 (from 8577) | 6425, 6433, 6651, 8428 (from 8603); 6345 debug | yes 5472 | **no** | **no** | yes 5620 | no | **no** |
| `sparkleSingleOutInstanceCache` (1077) | `parent#child#conns` ↦ wire name | 6615, 8424 (from 8560) | 6610, 8420 (from 8553) | yes 5473 | **no** | **no** | yes 5619 | no | **no** |
| `sparkleFvarZetaVisited` (975) | set of fvar names | 6930/6932, 6942/6944 | 6922, 6938 | **no** | **no** | **no** | yes 5623 | no | **no** |
| `sparkleSubModuleCache` (1021) | declaration name ↦ (module, design) | 5273, 5280, 5299, 5364 | 5311 (legacy arm only) | yes 5470 | no | no | no | no | no (written on success only) |
| `sparkleChildCache` (1029) | declaration name ↦ (module, design) | 8848 | 8846 | yes 5471 | no | no | no | no | no (written on success only) |
| `sparkleTypeCache` (1086) | `Expr` ↦ type | 1137 | 1125 | yes 5467 | no | no | no | no | no |
| `sparkleSynthDepth` (960) | Nat | 5489, 5505 | 5430 | — | — | `finally` 5505 decrements | — | — | yes (`finally`) |
| `sparkleCallCounter` (949) | Nat | 6855 | 6855 (limit, 6868), 2159/2167 (profile) | **no** | no | no | no | no | no |
| `sparkleChildSynth` (1037) | the child entry | 8850, once | 5545, 5192, 5209 | constant | | | | | |
| per-builder expression cache (`IO.mkRef` at 2936, 2961, 5353) | `Expr` ↦ wire name | 2175, 7949, 7992 | 7932, 7975 | a fresh ref per arm run | — | — | yes 5613 | fresh ref | — |
| profile counters: `sparkleCacheHits` (950), `sparkleTypeCacheHits/Miss` (1091–1092, reset 5468–5469), `sparkleWhnf*/Infer*/UnfoldDef*` (1099–1104), `sparkleHWInfer*` (756–757), `sparkleHandlerCalls/Ms` (1142–1143) | Nat | various | only in the profile tick (6872 ff.) and `emitLeaves`' profile lines | | | | | | |

Not refs: `CompilerState` / `CircuitState` (wires, `usedNames`, counters,
`translateRecord`) are the state of `CompilerM`; a `catch` rolls them back
and each entry arm starts from `CircuitM.init` (2940, 2965, 5357).

Against the earlier notes:

* "eight" (`WireCaches`, 5581–5590): confirmed — let, loop, canon,
  single-out, sub-instance, wire width, fvar value, zeta marks, plus the
  expression cache.
* "six module-local" (`fix/wire-refs-build`, `restoreModuleWireRefs`): let,
  loop, canon, wire width, fvar value, zeta marks; the two instance caches
  are left out there with the reason "an entry of
  `sparkleSubInstanceOutputs` is honoured by its reader only together with a
  re-declaration of its wires in the module being built". **By reading
  `85ebb9fd` that sentence holds for ONE of the three readers only**: the
  instance-emit branch (6651–6705) re-declares; the projection shortcut
  (6425–6428) and the certified projection arm (8603–8605) return the cached
  name at once. This is item 1.
* `B-callkinds.md` §5 ("the two instance caches are deliberately NOT cleared
  on nested entry"): confirmed (5443–5447 is the comment, 5479–5488 the
  code).
* New relative to those notes: `sparkleFvarZetaVisited` and
  `sparkleCallCounter` are cleared at no entry, depth 0 included (the only
  `set` of the first is 5623; the second has none in `Sparkle/` or `Tools/`).

## 1. `sparkleSubInstanceOutputs` — candidate G

### READ

* The key (6424, 6644, 8585–8589) is `hash (canonHardwareKey callExpr)`
  paired with the output port name. `canonHardwareKey` (1295–1299) is
  `toString (canonHardwareExpr e).hash`; `canonHardwareExprStep` (1218–1293)
  substitutes the values of wire-less `let` fvars, replaces already
  translated `Signal.loop` sub-expressions by `«wire:NAME»`, and replaces
  every remaining fvar by the constant `«wire:NAME»` of the wire it denotes
  (`lookupVar`, 1287–1289).
* So the key CONTAINS the callee (the head constant of the call) and the
  argument wires' NAMES. It does NOT contain the module being built. The
  task's "lacks the module name" is true of the PARENT module, not of the
  callee.
* Written: legacy emit 6710; certified arm `instOutWires` 8577 → 8432.
* Read, hit returned WITHOUT checking that the current builder declares the
  wire: the projection shortcut 6425–6428 (`return some w`), and
  `translateProjInstanceUncachedWith` 8603–8605 (`| some w => return w`).
  The surrounding `translateControlCachedWith` (8014–8021) validates only
  the EXPRESSION cache; on its miss it runs the arm and records whatever
  name comes back.
* Read with a declaration check: the emit branch 6651–6705
  (`alreadyDeclared`, else re-declare the wires and emit one instance). It
  is reached only when the CALL itself is translated — after a field miss
  (6432), or when the first output's key is present but the projected
  field's is not (8610–8611) — not when the projected field is in the map.
* Cleared at depth 0 only (5472). A nested entry neither clears nor restores
  it (5479–5488, 5504–5509); the comment 5443–5447 says this is intended.
* The machine route does not use it for the calls of a machine body (they
  are binders, closed by `closeInsts*`, 5189–5225); the gate, mixed and
  legacy routes all reach the two readers through the same translator
  (`translateInstanceOrFallback`, 8639–8681).

### The three questions

* **Two different callees.** They differ in the head constant, so the
  canonical expressions differ; a collision needs equal `Expr.hash` values
  (`toString` of it, hashed again): a hash collision, unvalidated when it
  happens, not constructible by hand. Bounded to that.
* **The same callee at two nesting levels / a child and the parent's own
  call.** Collide whenever the argument wires have the same NAMES in both
  modules — e.g. both pass their inputs `x`, `y`. This is the candidate.
* **Within one module.** Equal key ⇒ same callee, same argument wires of one
  builder ⇒ the same hardware; sound up to the hash.

### The constructed source (real entry, no seeding)

`Tests/Compiler/SubInstanceKeyTest.lean`:

```lean
@[hardware_module] def kSD (x y) : SumDiff dom := { sm := x + y, df := x - y }
@[hardware_module] def gW (x y) := let p := kSD x y; let q := kSD x y; p.sm + q.df
@[hardware_module] def gR (x y) := let p := kSD y x; let q := kSD x y; p.sm + q.df
def gTopWR (x y) := gW x y + gR x y
def gTopRW (x y) := gR x y + gW x y
```

(`hW` / `hR` / `hTopWR`: the same with `(kSD x y).sm` written directly.)

### PREDICTED, both trees

`gTopWR`, one top-level run:

1. `gW` is synthesised (nested entry). Its first projection misses, the
   instance of `kSD x y` is emitted with two fresh wires — call them
   `_tmp_sub_call_sm_i`, `_tmp_sub_call_df_j` — and the map gets
   `(K, sm) ↦ …sm_i`, `(K, df) ↦ …df_j`, `K` the key of `kSD x y` over
   `_gen_x`, `_gen_y`. Its second projection hits its own entry. Correct.
2. `gR` is synthesised (nested entry; the map is NOT cleared). Its walk is
   `gW`'s walk up to the order of the first call's arguments, so its first
   projection (`kSD y x`, key `K'`, a miss) allocates THE SAME NAMES
   `…sm_i`, `…df_j` in `gR`'s builder, connected to `kSD y x`.
3. `gR`'s second projection is `(kSD x y).df`: key `K` again (`gR`'s inputs
   are also `_gen_x`, `_gen_y`) → the hit `…df_j` written by `gW`. In `gR`
   that name is declared — it is the `df` port of `kSD y x`.

Emitted `gR`, schematically (numbers NOT ESTABLISHED):

```
kSD inst (._gen_x(_gen_y), ._gen_y(_gen_x), .sm(_tmp_sub_call_sm_i), .df(_tmp_sub_call_df_j));
assign out… = (_tmp_sub_call_sm_i + _tmp_sub_call_df_j);
```

ONE instance where the source has two different calls; no undeclared name,
no self-assignment, nothing a structural check sees. Meaning: emitted
`gR = (y + x) + (y − x) = 2y`; source `gR = (y + x) + (x − y) = 2x`
(mod 32). `gTopWR`: emitted `2x + 2y`, source `4x`. `gR` compiled as its
own top (depth 0, empty map) is predicted correct: two instances.

`gTopRW`: `gR` first, correct (both keys miss). Then `gW`: its first
projection is a HIT on `gR`'s `K` entries, names `gW`'s builder never
declared; `gW` emits no instance and reads two undeclared wires. Whether a
later stage refuses that text is NOT ESTABLISHED (`runDesignDRC`, 8878, is
the registered-output warning only; `getWireWidth` answers 8 for an unknown
name, 235).

### NOT ESTABLISHED

* All of the above as an observation: nothing was run.
* That `gW` and `gR` allocate identical names. It rests on "the two bodies
  differ only in the order of two bound input variables, and translating a
  bound input allocates nothing". If a route normalises the two bodies
  differently, step 2 gives other names and step 3 returns an UNDECLARED
  name instead of a wrong one (still a defect of the text, not a silent
  one). The probe prints both.
* Which route `gW` / `gR` / the tops take (gate, mixed, legacy); the
  argument does not depend on it, the probe prints it.
* That the order of synthesis follows the order of the operands of `+`.
  Both orders are in the probe.
* Whether any measured declaration (the 391 corpus, the 84 legacy-route
  runs) has two modules projecting the same multi-output call over
  equally named wires. Not looked for. The machine route is unaffected by
  reading.

### How to observe

`lake build Tests.Compiler.SubInstanceKeyTest`, lines `SUBINSTKEY …`; per
top a `DETECT … collision=<T/F>` line (a child's nested module differs from
the module the same entry builds for it alone, or reads undeclared names).
PREDICTED `collision=T` for `WR`, `RW`, `hWR` on both trees. Then
`scripts/shipping-coverage/subinst_key_sim.sh`: PREDICTED
`gTopWR: command==source F` with numbers (not x), `gW`, `gR`: `T`.

## 2. The legacy one-output hit

### READ

* The lookup: 6606–6612, in the `[singleOut]` branch of
  `Rec.handleDefinitionUnfold`. Key
  `"{parent module name}#{child module name}#{port=connection;…}"`, the
  connections being clk/rst and the argument wires in port order. A hit:
  `return some cachedW`.
* Compared (through the key): the NAME of the module being built, the NAME
  of the child module, the port names and the connected wire NAMES.
* Not compared: that the wire was made by THIS builder for THIS expression.
  The certified arm does compare it: `translateInstanceUncachedWith`
  8553–8558 filters the hit with `instHitValid cs0.translateRecord e`
  (8520–8524). Also not compared, in either reader: the result type (taken
  from the child both times).
* Who reaches the legacy branch for a one-output child: NOT a call whose
  head is tagged `@[hardware_module]` — `fallbackKind` gives `.other`
  (8706–8747), `translateInstanceOrFallback` (8639–8652) takes every tagged
  head, and with one output always the certified arm. What remains is the
  second half of 6505–6532: an UNTAGGED definition whose inline attempt
  returned no wire, then promoted to a sub-module by
  `synthesizeCombinational name` (6521). By reading, an `@[irreducible]`
  helper is such a definition (`unfoldDefinition?` at default transparency
  returns `none`, so `tryInlineUnfold` returns `(none, none)`, 6270–6301),
  and the front end does not unfold it either (`userDefinition?`, 3335).
* Not cleared on a nested entry, but the key starts with the module being
  built, so a parent and a child never share a key.

### The bound

A stale hit needs an entry under the SAME parent module name whose wire the
current builder did not make. Within one top-level run a module name gets a
second builder only as follows:

1. a rolled-back attempt in the same builder — `tryInlineUnfold` restores
   the ref (5619); the other `catch`es of the translator (6331, 6396, 6510,
   6522, 6943–6948, 7080–7086, 7258, 7752, 7858) either re-throw or wrap a
   read / a literal extraction that allocates no wire;
2. a child synthesised twice — excluded by `sparkleChildCache` (8846–8848:
   every child entry from the translator and from `closeInsts*` goes through
   `synthesizeChild`); a child that THREW leaves its entries, but its
   exception is re-thrown (6510, 6522) and the only `catch` that goes on
   after it is (1);
3. **the legacy arm after a declined machine arm** — the harness
   (`synthesizeMixedCertified`, 5234) builds under the same name
   (`CircuitM.init declName.toString`, 2965 and 5357) and nothing resets the
   ref in between.

So the unvalidated hit can hand out a foreign wire only if the machine
harness itself reached 6615, i.e. the machine body contains a call of an
untagged, non-inlinable, one-output definition, `machineShape?` accepts the
body, and `closeLets` / `closeInsts*` then declines. **NOT ESTABLISHED**
whether `machineShape?` accepts such a body (I did not trace `machConv` for
an unknown head). If it does, the legacy arm's lookup returns the harness's
wire name: no instance emitted, the name undeclared or naming another wire
of the legacy builder.

Inside one builder the hit is sound: equal key ⇒ same child, same argument
wires.

### Probe (`Tests/Compiler/SingleOutHitTest.lean`)

* §1, SEEDED (an injected state, not a finding): the keys a real run of
  `sIrr` (`hIrr x y - x`, `hIrr` irreducible) leaves are mapped to a seed
  name and the entry is run again at depth 1. PREDICTED: the legacy handler
  returns the seed name (`honoured=T`), the certified arm on the tagged twin
  `sTag` does not (`honoured=F`). If `sIrr` shows no instance, the reading
  "an irreducible helper reaches the legacy branch" is wrong and the row
  says NOT APPLICABLE.
* §2, real entry: `sMach`, the declining register machine of finding F with
  `hIrr x y` in the body; `machine shape=<T/F>`, the `hIrr` instance count
  of the real run against the clean legacy run. No prediction. On poc
  finding F can disturb both rows (same `let rs` as its child).

## 3. Zeta marks (`sparkleFvarZetaVisited`)

### READ

* Written only at 6930/6932 (around the translation of a `let`-fvar's value)
  and 6942/6944 (around `Meta.reduce`, itself inside `try … catch`). The
  erase is a plain statement after the call, not a `finally`: an exception
  from the value's translation leaves the mark.
* Read only at 6922 and 6938, and each read can only `throwError`.
* Cleared at no entry; restored only by `restoreWireCaches` (5623).
* This is the only "zeta / visited / mark" state among the refs. The `seen`
  set of `canonHardwareExprStep` (1254) is local.

### The bound

1. A mark never selects a wire or an expression; its only effect is an
   exception. So it cannot by itself make the emitted text differ in
   meaning; it can make a compilation fail, or make an enclosing `catch`
   take another path.
2. The enclosing `catch`es that go on translating are those of
   `tryInlineUnfold`, and they put the set back to the snapshot (5623).
3. A mark left by an exception that escapes is on an fvar NAME. The names
   come from the name generator of the elaboration, which is not rewound by
   `try`/`catch` or `saveState`, and a declined machine arm / a legacy
   fallback re-opens the body with fresh fvars (5335, 2933, 2958). So inside
   one Lean process started by `lake build` a stale mark is never looked up
   again.
4. Not covered by (3): a long-lived process whose command state is rewound
   while the `IO.Ref` is not (the language server re-elaborating a file from
   a snapshot). There a re-issued fvar name can meet a stale mark and a
   valid source can fail with "circular zeta-reduction". A refusal, not a
   wrong output. NOT ESTABLISHED, not constructible in a build.

The same shape of argument for `sparkleCallCounter` (never reset, 949):
it only ever makes the translator throw (6868), after 32 000 000 calls
summed over ALL syntheses of the process; the tests that run populations
reset it by hand (`NestedLetCacheTest.runIsolated`).

`SingleOutHitTest.lean` logs the size of the mark set after each run
(expected 0).

## Files, and the order to build

1. `lake build Tests.Compiler.SubInstanceKeyTest` (imports
   `Tests.Compiler.NestedLetCacheTest`), poc and fix; keep the `SUBINSTKEY`
   lines.
2. `scripts/shipping-coverage/subinst_key_sim.sh` after (1) (not next to a
   build); needs `iverilog`.
3. `lake build Tests.Compiler.SingleOutHitTest`, poc and fix; the
   `SINGLEOUT` lines.

None is in `Tests.AllTests`; `lakefile.lean` is untouched.

## What in the Lean is most likely not to elaborate

* `SubInstanceKeyTest`: the record literal of `kSD` at a generic domain
  (`x - y` needs the `HSub` instance for `Signal dom (BitVec 5)`); `p.sm`
  on a `let`-bound `SumDiff defaultDomain`; `m!` interpolation of
  `List String` / `Nat` inside long strings; `mN == mA` (`BEq` of
  `Module`, used the same way in `NestedLetCacheTest`).
* `SingleOutHitTest`: `@[irreducible] def hIrr` followed by `circuit do`
  with `let h := hIrr x y`; `open … (cleanLegacy allReads undeclared
  undriven)` (names taken from `MachineFallThroughCensusTest`);
  `z.size` on `Std.HashSet`; the `foldl` building the seeded map.
* `subinst_key_sim.lean`: a mechanical copy of `nested_let_sim.lean` (rows
  and sources replaced, the `en` input dropped); the stimulus index of `x`,
  `y` is now 0, 1.
