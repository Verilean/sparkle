# B — `getWireWidth` and the global width cache (branch `par/b-2`)

**Nothing here was built.** Line numbers: `Sparkle/Compiler/Elab.lean` at
`d160afd4` (unchanged by `par/b-1`). User ruling implemented: reproduce first;
then candidate fixes (builder-local lookup, or validation of the cached
entry); verify the cases where ignoring the cache changes the inference for
undeclared intermediate wires.

The candidate is a SEPARATE commit on top of this branch's main commit (the
last commit of `par/b-2`): the integrator can take or leave it. Without it,
everything else of this branch is unaffected.

## 1. What the cache is

`sparkleWireWidthCache : IO.Ref (Std.HashMap String Nat)` (161): wire NAME →
width.

* **Writers** (all "write-through at declaration", only for a concrete type —
  `legacyCacheWidth?` 167–171 returns `none` for `bitVectorDim`):
  `CompilerM.makeWire` 180, `addInput` 199, `addOutput` 207, `emitRegister`
  250, `emitMemory` 274, `emitMemoryComboRead` 282, the cross-module instance
  wire 6697; and `getWireWidth` itself on its fallback path 232.
* **Reader**: `getWireWidth` 210–233 — the cache FIRST; on a miss a linear
  scan of the builder's `wires ++ inputs ++ outputs`; on a miss there too:
  `8`. (`getWireWidthDim` 261 reads the builder only.)
* **Resets**: `set {}` at depth 0 (5474) AND at every nested entry (5484);
  the parent's map is put back when a nested entry leaves (5508, from the
  snapshot 5462–5464). So the cache IS reset per entry run — parent and
  child, and sibling children, do not see each other's entries.
  `restoreWireCaches` (5611–5620) puts it back in the two catches of
  `tryInlineUnfold` (6281, 6297).
* **Names**: `CircuitM.freshName` — `_tmp_{hint}_{counter}` / `_gen_{hint}`,
  the counter and `usedNames` are fields of `CircuitState`. The same names
  recur in every builder state by construction.

## 2. When can the cache disagree with the current builder state?

Not across entry runs (reset / restore). Inside ONE entry run:

1. **Rollback**: a `catch` in `CompilerM` restores the builder state (counter
   included), not the `IO.Ref`. Covered for the inline attempts
   (`restoreWireCaches`). The other catches of the translator block: 6330,
   6395, 6942–6947, 7257, 7751, 7857 wrap an oracle or a literal extraction
   (no wire allocation); 7079–7084 wrap `extractBitVecLiteral`; 6509, 6521
   re-throw. By reading, none goes on translating after a wire was allocated
   inside its `try`.
2. **A second builder in the same entry run**: the legacy arm starts from
   `CircuitM.init` (5356) with NO reset when the machine arm ran its harness
   (`synthesizeMixedCertified`, its own `CircuitM.init`, 2964) and then
   declined (5239). The cache then holds the harness's names.
3. After (1) or (2) a stale entry is READ only for a name that is not
   re-written at its declaration: a wire declared with a symbolic width
   (`bitVectorDim`: no write), or a name the current builder does not declare
   at all. A wire declared with a concrete type overwrites its entry.

**FINDING (E), by reading, not reproduced:** case (2) is not specific to the
width cache. Between the machine harness's builder and the legacy arm's
builder NONE of the wire-naming refs is reset: `sparkleLetWireCache`,
`sparkleLoopWireCache`, `sparkleWireCanon`, `sparkleSingleOutInstanceCache`,
`sparkleSubInstanceOutputs`, `sparkleFvarValueMap`, `sparkleWireWidthCache`
(the expression cache is fresh: 5352). If the harness's translator run
populated them, the legacy arm can be handed a wire NAME of the first
builder. `LegacyArmCensusTest` does not run machine-route declarations that
fall through ("those are not run here"). `MemoHitCensusTest` now runs the
machine-route candidates and reports assignment reads of undeclared names
(`WIREWIDTH UNDECLARED`), which is where such a name would show.

## 3. (a) Reproduction — `Tests/Compiler/WireWidthStaleTest.lean`

With the real helpers, each sequence from `CircuitM.init`:

* **R1** (the assertion): a failed attempt allocates `t : bitVector 16` and
  is rolled back by a real `catch`; the same name is allocated again as
  `bitVectorDim N`; the cache still says 16 for a name the builder declares
  symbolic. ASSERTED: that state. LOGGED: `getWireWidth` — today `returned
  16` (the stale read; the scan would have thrown "symbolic width").
* **R2**: a name of builder A asked in a fresh builder B — today the cache's
  16 where B declares nothing (fallback 8).
* **R3**: rollback, then the same name with `bitVector 4` — `returned 4`
  (write-through heals it).

Expected log lines (no candidate):

```
WIREWIDTH STALE R1: … allocated _tmp_t_0 … the name allocated next is _tmp_t_0, declared …bitVectorDim… ; the cache holds some 16 for it; getWireWidth _tmp_t_0: returned 16 …
WIREWIDTH STALE R2: … getWireWidth _tmp_t_0 there: returned 16 …
WIREWIDTH STALE R3: … getWireWidth _tmp_t_0: returned 4 …
```

With the candidate: R1 `THREW`, R2 `returned 16` (unchanged — see §5), R3
`returned 4`. The assertion (the cache's STATE) holds in both.

**The stale state was not reached through a real run of the entry.** What
prevents it (by reading, §2): write-through at every declaring helper for a
concrete type; the reset at every entry and the restore at a nested exit;
`restoreWireCaches` in the inline catches; symbolic mode never attempts the
machine arm (5287), so the only second builder (§2.2) has concrete types.
What is left is the undeclared-name read after a machine-arm fall-through
(finding E), which needs a declaration that the machine gate accepts and the
closings decline — none is exhibited.

## 4. (b) The candidate — builder state first

One edit, the body of `CompilerM.getWireWidth` (the name is kept, so all nine
callers switch and no statement that mentions `CompilerM.getWireWidth`
changes):

```lean
def getWireWidth (wireName : String) : CompilerM Nat := do
  let cs ← get
  let allPorts := cs.module.wires ++ cs.module.inputs ++ cs.module.outputs
  match allPorts.find? (fun p => p.name == wireName) with
  | some p =>
    match legacyCacheWidth? p.ty with
    | some width => return width
    | none => liftMetaM $ throwError
        s!"Wire '{wireName}' has a symbolic width; this operation requires a concrete width"
  | none =>
    let cache ← liftMetaM (sparkleWireWidthCache.get : IO _)
    match cache.get? wireName with
    | some w => return w
    | none => return 8
```

* a name the builder DECLARES: its declared width — the cache is not
  consulted (and not written: the read path no longer modifies the ref);
* a name the builder does NOT declare: exactly today's answer (the cache,
  else 8).

**Callers that switch** (all of them; each asks for `wireS`, the wire
`translateExprToWire s "s" (isTopLevel := false)` just returned):

| Line | Arm | Use of the width |
|---|---|---|
| 5672 | `handleTupleProjections`, `Signal.fst` | `min wireWidth typeTotal`, slice `[total-1 : total-width]` (5680–5682) |
| 5691 | `handleTupleProjections`, `Signal.snd` | `min width wireWidth`, slice `[w-1 : 0]` (5697–5698) |
| 5725 | `handleTupleProjections`, `Signal.map Prod.fst` | as 5672 |
| 5747 | `handleTupleProjections`, `Signal.map Prod.snd` | as 5691 |
| 7108 | the application translator's second copy, `map Prod.fst` | as 5672 |
| 7126 | the same, `map Prod.snd` | as 5691 |
| 7166 | `map (BitVec.signExtend …)` | `extBits := target - srcWidth`, MSB slice |
| 7188 | `map (BitVec.sshiftRight …)` | the result wire's and the shift constant's width |
| 7225 | composite-body lambda fallback | `srcWidth` of the parameter wire |

Not switched: `getWireWidthDim` (862; already builder-only).

**Cost.** The cache exists because the scan is linear (`wires ++ inputs ++
outputs`, a fresh list per call; the comment at 211–215 names an O(n²) walk
on FSM-shape circuits). The candidate reintroduces that scan on every call.
`Tests/Compiler/LegacyCacheFixCostTest.lean` is the place to measure it. The
O(1) form of the same idea — a `widths : Std.HashMap String HWType` field of
`CircuitState`, maintained by `addWire` / `addInput` / `addOutput`, hence
rolled back with the builder — is the better design, but it edits
`Sparkle/IR/Builder.lean` and every proof about `CircuitState`; NOT done, a
proposal.

**The other candidate, validation of the cached entry** (not implemented): a
cached width is accepted only if the builder declares the name with that
width. It needs the same scan (the builder has `usedNames`, a set of names
without widths), so it costs what the candidate costs and keeps the ref on
the path. A cheap partial validation — accept the entry only if
`cs.usedNames.contains wireName` — is O(1) but fixes only the
undeclared-name read (R2), not R1.

**What may break in the proofs** (not built): the machine route's
`legacyRel` walks the translator block with the `vc` tactic; the new body has
one state read, one `IO.Ref` read (`Framed.sideGetIO .wireWidth`), the same
`throwError`, and no `modify` — fewer operations than before, but whether
`vc` closes the new shape is not known. `Tools/ShippingLegacySemFstArm.lean`
takes `WireWidthReads` as a premise and never unfolds `getWireWidth`.

## 5. (c) Names the builder does not declare ("undeclared intermediate wires")

What can `translateExprToWire s …` return that the current builder does not
declare, and what each lookup answers:

| Source of the name | Today | Candidate | Strictly local (no cache) |
|---|---|---|---|
| a wire of a rolled-back attempt, handed back by a stale `IO.Ref` cache (expression / let-wire / loop-wire / canon) — the gap of `ArgRunsBody`; closed for the inline catches on this branch | the rolled-back wire's width | same | 8 |
| a wire of the FIRST builder after a machine-arm fall-through (finding E) | that wire's width in the first builder | same | 8 |
| `clk` / `rst` (added to the module only when it is finished, 2203–2205), if an expression's wire is one of them | 8 unless an earlier `addInput` of that name wrote the cache | same | 8 |
| a wire of an outer (parent) module | not visible: the nested entry resets the cache (5484) | same | 8 |
| a sub-instance output reused from `sparkleSubInstanceOutputs` | declared before it is returned (6680–6697) — not undeclared | declared width | declared width |

So: ignoring the cache for undeclared names WOULD change the answer (to 8) in
the first two rows; the candidate therefore keeps the cache for exactly those
names and changes nothing there. Neither answer is "right" for an undeclared
name — the emitted statement reads a wire the module does not have. Whether
any real run produces such a read is measured: `WIREWIDTH UNDECLARED` in
`Tests/Compiler/MemoHitCensusTest.lean` counts, in the emitted modules,
assignment reads of names the module does not declare (every one of the nine
callers emits an assignment reading the wire it asked about). Expected: 0.

## 6. The comparison the integrator can run

`Tests/Compiler/MemoHitCensusTest.lean` logs

```
WIREWIDTH DIGEST: R returned declarations, combined digest H
WIREWIDTH DIGEST, per declaration (name=top/design): …
```

Build the test once on `par/b-2` WITHOUT the candidate commit and once WITH
it; diff the two pairs of lines. Expected: identical (`H` equal) — on a
declared wire with a concrete type the cache and the builder agree. A
difference names the declaration.

## 7. (d) `WireWidthReads` as a derived fact (candidate only)

`WireWidthReads ctx s w n := ∀ k t, Returns (CompilerM.getWireWidth w) ctx s
k t → k = n ∧ t = s` is a premise of the tuple class because today the read
goes through the `IO.Ref` first. With the candidate it follows from the
builder state the walk already tracks.

Proved in the candidate commit (`Tools/ShippingLegacySemWireWidthLocal.lean`;
it does not compile without the candidate):

```lean
theorem wireWidthReads_of_declared {ctx : CompilerState} {s : CircuitState} {w : String}
    {n : Nat} {p : Port}
    (hfind : (s.module.wires ++ s.module.inputs ++ s.module.outputs).find?
      (fun p => p.name == w) = some p)
    (hty : p.ty = HWType.bitVector n) : WireWidthReads ctx s w n

theorem wireWidthReads_of_declared_bit … (hty : p.ty = HWType.bit) : WireWidthReads ctx s w 1
```

Proof: unfold, `Returns.bind` / `Returns.get` for the state read, rewrite the
lookup by `hfind` and the type by `hty`; the remaining program is `pure n`
(`Returns.pure`).

**What is still needed to drop the premise from `tuple_entry_output`**
(statements; not done):

1. `Declares s w ty := (s.module.wires ++ s.module.inputs ++
   s.module.outputs).find? (·.name == w) = some ⟨w, ty⟩`, monotone along the
   walk (a later `makeWire` allocates a FRESH name — `makeWire_spec` — so an
   earlier declaration stays the first match);
2. a post-condition of the two arms: `fstArm_run` / `sndArm_run` return a
   state in which the result wire is declared with `hwTypeFromWidth w` (the
   arm's own `makeWire hint hwType`);
3. for the chain's innermost node: the variable's port is declared with
   `bitVector N` in the prepared state (`bindInputsLegacy` → `addInput`; the
   prepared setup `setupOf` already knows the port's name).

With 1–3, `ArgWidthReads tr ctx a M` holds for every node by
`wireWidthReads_of_declared` (width 1: `_bit`), and the field `widthReads`
of `TupleNode` is derived instead of assumed. `ArgRunsBody` (the expression
cache) is a different premise and stays.
