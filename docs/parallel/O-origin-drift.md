# O-origin-drift: the reader copies after the "explicit call-entry origin" compiler change

Worker O, branch `par/o-cand` (from poc `b3104567`), 2026-10-19.
STATUS: WRITTEN, NOT BUILT against the patched compiler. Nothing under `Sparkle/` was edited here.

## Source compared

The PATCHED working tree of the main checkout:
`/home/junji-hashimoto/git/sparkle/Sparkle/Compiler/Elab.lean` (sha256
`13a007fa346a39317b68896ad53e5fee298e095f908d22a7cfae96ae75cb1712`, uncommitted: 31+/10-
relative to blob `233f50e0`) plus the new `Sparkle/Compiler/MachInstOrigin.lean`
(`InstOrigin := ord | field i | mem combo aw dw`, `deriving DecidableEq`).

`python3 scripts/shipping-coverage/oldeqv_drift.py --elab <that file> --diff` reported drift in
four of the nine copied definitions: `machConv`, `machInstance`, `machInstanceS`,
`machineShape?`. `machNested`, `machChain`, `machLoopBody`, `machLoopRoot`, `machNorm`
did not change. After the copies were updated the snapshot was regenerated
(`--update`, worktree `scripts/shipping-coverage/oldeqv_snapshot.txt`); a re-run reports
no drift. The snapshot records the TEXT only. Lean checks the copies against each other
(`step_tot`, `oldEq_of_oldEqV`), not against the compiled `partial` constants (O2).

## What changed, definition by definition

### `machConv`: the two `machInstance` call sites

* Ordinary one-Signal call (`machInstCall?` arm): `machInstance senv env c .ord kinds res args st`.
  The call is tagged `.ord`.
* Memory arm (`memCall?`): `machInstance senv env (memChildName combo aw dw) (.mem combo aw dw) …`.
  The placeholder NAME is still passed as `c`. The tag carries the memory's parameters.
* No other arm changed. The structure-call arm still calls `machInstanceS`, which tags its
  own entries (below).

How the copies match:
* `convStep` (`ShippingReaderFuelDefs.lean`): `cInst env c .ord …` and
  `cInst env (memChildName …) (.mem combo aw dw) …`.
* `oConv` (`ShippingReaderFuelOldEq.lean`): `G.inst env c .ord …` and `G.inst env (memChildName …) (.mem combo aw dw) …`.
* `oConvV` (`ShippingReaderFuelVerbatim.lean`): the same text as `oConv`, character for
  character in these two arms.
* For this the call type `Call.inst` and the tuple field `OldFns.inst` gained an
  `InstOrigin` argument after the callee name, in the position the source uses.

### `machInstance`: new parameter `org`, origin-aware dedup, the tag pushed

* Signature: `(org : InstOrigin)` comes after `c`.
* Dedup: before, the first entry with the same callee and argument lets was reused,
  `st.insts.findIdx? (fun i => i.1 == c && i.2.1 == js)`. Now
  `st.insts.zipIdx.findIdx? (fun (i, k') => i.1 == c && i.2.1 == js && st.instOrigins[k']? == some org)`.
  An entry is reused only if its STORED tag equals the call's tag. So a memory call and a
  call of a declaration that carries the memory's placeholder name stay two entries. This
  was the name-keyed merge that `S-memname-collision.md` §5.1 describes.
* Push: `instOrigins := st.instOrigins.push org` is pushed together with `insts` / `instFields`.

How the copies match:
* `instStep`, `oInst`, `oInstV` take `org` and contain exactly this `match` (the same
  lambda, the same `==` on `Option InstOrigin`) and this record update.
* `instEntry` (the first `match res`) is unchanged.
* `instArg` / `oInstArg` (the `foldlM` function) are unchanged. The argument-let naming
  still uses `k = st.insts.size` taken before the fold.

### `machInstanceS`: dedup keyed on tag `.field 0`, one `.field i` tag per field

* Dedup: `… && st.instOrigins[k']? == some (.field 0)`. A structure call is found by its
  FIRST field entry, and that entry must be tagged `.field 0`.
* Append: `instOrigins := st.instOrigins ++ ((List.range fields.length).map InstOrigin.field).toArray`.
  Entry `k0 + i` is tagged `.field i`, with `instFields[k0+i]` the name of field `i`.

How the copies match: `instSStep` (the `let (k0, st) := match …` distributed over the
two branches, as before), `oInstS`, `oInstSV` (verbatim) contain this dedup and this
append. `instRes` (the lifted `let rec inst`) is unchanged.

### `machineShape?`: one new field in the record

`instOrigins := st.instOrigins.toList`. It is copied unconditionally, even when
`instFields` is `[]` because `instStruct` is false. The copy is `shapePost`
(`ShippingReaderFuelShape.lean`). Nothing before the record changed.

`MachineShape.instTagged` / `closeInstsGM` (the closing's child choice) also changed, but
they are not reader copies and are not part of the drift set (see "Not done" below).

## What is proved about the tags (candidate reader, every fuel)

* Alignment. `MachRead.LenOk` gained `origins : instOrigins.size = insts.size`. The push
  and the append keep it (`lenOk_instPush`, `lenOk_instS`), and every other update leaves
  both arrays alone. So `readF_good` gives it at every fuel: `machConvF_origins`, … (R5
  file). At the wrapper, `machineShapeF_origins_aligned` (ShapeR5) and
  `machineShapeF_instOrigins_length` (ShapeProv) give
  `sp.instOrigins.length = sp.insts.length`. With that, `instOrigins_getD_eq` shows that
  `instTagged`'s `getD k .ord` never supplies a missing tag below `insts.length`.
* Provenance by the stored tag. `InstProv` (ShippingReaderFuelProv) states, per index,
  `OriginT senv e nm instStruct o` for the entry `e`, port `nm` and STORED tag `o`:
  * `.ord`: an ordinary signature, port `out`;
  * `.field i`: field `i` of the callee's structure signature (index, name, kind),
    `instStruct = true`;
  * `.mem combo aw dw`: `c = memChildName combo aw dw`, `r = .bits dw`, `aw ≠ 0`,
    `dw ≠ 0`, port `out`.

  The call-site premise is now per tag (`InstPre`). Wrapper level:
  `machineShapeF_originT`, `machineShapeF_tag_{mem,ord,field}`,
  `machineShapeF_tag_exists`. The old statements (`Origin`, `OriginAt`,
  `machineShapeF_origin`) are kept as corollaries (`origin_of_originT`,
  `InstProv.origin`, `originAt_of_originTAt`).

## Not done (outside the reader copies; flagged for the integrator)

These proofs unfold the PATCHED `closeInstsGM`. Its child choice is now
`shape.instTagged.mapM fun (c, o) => match o.child? …` instead of
`shape.insts.mapM fun (c, _, _) => match memChild? c …`, so they will not build as
written. Their statements are keyed on `memChild?` of the NAME (`MemChildren`, the
`hnomem` premises). After the fix that predicate is no longer true in general: a
declaration with a placeholder name is now compiled. So the statements have to be keyed
on the tag, not just re-proved:

`ShippingCacheCoherentClose.lean:193`, `ShippingCacheCoherentCert.lean:358`,
`ShippingCallsRunFinal.lean:85`, `ShippingCallsClose.lean:65`, `ShippingCallsRunG.lean:70`,
`ShippingChildRun.lean:278`, `ShippingChildKeeps.lean:574`, `ShippingMachineEntry.lean:900`
(`MemChildren`, def at :864), `ShippingMemOnlyAtAll.lean:63` (probably still fine: it only
reads the synthesiser first), `ShippingMemClosesRun.lean:152`.

`ShippingMemDispatch.lean` (the guarded MODEL, `gmChoice` keyed on `memChild?`) still
compiles. It now describes the pre-patch closing.
