# A / the closing of the memory-only parents (round par/a-19)

Branch `par/a-19`, base poc `4bd77170`. NOTHING here was built or run: every
statement about Lean code is "WRITTEN, NOT BUILT"; no premise of any endpoint
counts as removed until the integrator's build. "Read" = the line was read in
the file named; "measured" = a value quoted from a built run's log;
"inferred" = concluded from a neighbouring fact.

## 1. What was read

* `Tools/ShippingMemClosesKids.lean` (BUILT at 710ed31f): `ChildIfaceP`,
  `memIface`, `memKid_iface`, `machineClosesAt_of_kidsDM` (M2), its
  hypotheses verbatim (419–451).
* `Tools/ShippingMemKidCore.lean` 72–116: `Kid`, `Kid.mem`.
* `Tools/ShippingMemOnly.lean` 115–132: `MemOnlyData` (BUILT; the five
  `f_data` theorems exist).
* `Sparkle/Compiler/MachMemory.lean` 41–66: `memChildName`, `memModule`
  (name `SparkleMem_{combo|sync}_{aw}_{dw}`, design `[itself]`), `memChild?`.
* `Tests/Compiler/NoPortsMemOnlyCounterTest.lean` 223–316 (`generateM0`,
  at-form): the endpoint's binders are those of `f.machine_ships_hier` with
  the LAST (`xs[10]`) replaced by `closes : MachineClosesAt …` — so the
  closing is the last binder and `closeLast` applies.
* The measured data: `docs/parallel/B-memkids.md` §8.1 (full probe lines of
  run 20261013-055644-b13b-alltests):

| declaration | call entries | argument lets | instFields | slots | lets |
|---|---|---|---|---|---|
| `memCounter` | `[SparkleMem.combo.4.8]` | `[[1,2,3,0]]` | `[out]` | 2 | 4 |
| `syncNarrow` | `[SparkleMem.sync.3.5]` | `[[1,2,3,0]]` | `[out]` | 2 | 4 |
| `memWide` | `[SparkleMem.combo.6.16]` | `[[1,2,3,0]]` | `[out]` | 2 | 4 |
| `twoMems` | `[SparkleMem.combo.4.8, SparkleMem.combo.4.8]` | `[[1,2,3,0],[0,2,3,4]]` | `[out,out]` | 2 | 5 |
| `mixedMems` | `[SparkleMem.combo.4.8, SparkleMem.sync.4.8]` | `[[1,2,3,0],[1,4,3,0]]` | `[out,out]` | 2 | 5 |

NOT READ / NOT MEASURED: the names of the parents' outputs (the available
log excerpts are cut before them); whether `letsAliasOk` holds of these five
(never evaluated before — evaluated by reading `aliasOk` below).

## 2. What `hfieldsNd` quantifies over (the question of the round)

`machineClosesAt_of_kidsDM`, `Tools/ShippingMemClosesKids.lean` 437–440:

    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')

It is NOT `Nodup` of the field names. It says: two entries with the same
CALLEE, the same ARGUMENT LETS and the same FIELD are one entry. With
`instFields = [out, out]`:

* `twoMems`: callees equal, fields equal, argument lists `[1,2,3,0]` vs
  `[0,2,3,4]` DIFFERENT → the second antecedent is false for `k ≠ k'`: TRUE.
* `mixedMems`: callees DIFFERENT → the first antecedent is false: TRUE.

It would be FALSE for a parent that reads ONE memory module twice on the
SAME four operand `let`s (two entries with one key). None of the five does;
the test's first command throws on such data ("hargsNd is FALSE: STOP").
Whether the front end can produce such data (it copies `let`s, and identical
calls are meant to be one instance) was not read.

The other three places where "the same memory twice" matters:

* `hpair` (two entries of one declaration have ONE child) is not a
  hypothesis of M2 — it is proved inside from `closeInstsGM_run_allM`; for a
  memory entry the child is the pure table value `memModule cb aw dw`.
* `hsep` (`nameK k = nameK k' → callee k = callee k'`): for `twoMems` the
  conclusion holds whatever the names.
* `hdisjD` has the antecedent `callee k ≠ callee k'`: vacuous for `twoMems`.

## 3. WRITTEN this round

    Tools/ShippingMemOnlyCloses.lean                       memNameAt, memNameAt_eq, machineClosesAt_memOnly,
                                                           MemOnlyCloseData, machineClosesAt_of_memOnlyData,
                                                           sep_of_one, parent_of_one
    Tests/Compiler/NoPortsMemOnlyClosedLib.lean            logData, closeIt, allPropsOk, auditClosed (meta only)
    Tests/Compiler/NoPortsMemOnlyClosedMemCounterTest.lean
    Tests/Compiler/NoPortsMemOnlyClosedSyncNarrowTest.lean
    Tests/Compiler/NoPortsMemOnlyClosedMemWideTest.lean
    Tests/Compiler/NoPortsMemOnlyClosedTwoMemsTest.lean
    Tests/Compiler/NoPortsMemOnlyClosedMixedMemsTest.lean

`closeLast`, `gapsOf`, `propBinders` are imported from
`Tests.Compiler.NoPortsMemSeqMemClosedTest`, not copied. No existing file is
changed. No scripted copy of a theorem: `machineClosesAt_memOnly` is ONE
application of M2 with nine short discharges.

The general theorem, verbatim:

    def memNameAt (d : MachineData) (k : Nat) : String :=
      ((memChild? (calleeAt d k)).map fun (md : Res) => md.1.name).getD ""

    theorem machineClosesAt_memOnly {declName : Name} (d : MachineData) (ok : d.ok = true)
        (hbody : d.shape.body = quote d.dom
          (fun j => inputExpr d.shape.binders.length (d.bpos j))
          (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
        (halias : d.letsAliasOk = true)
        {nDecl : Nat} (hC : d.callsOk nDecl = true)
        (hslots : d.ss.length = d.shape.layout.slots.length)
        (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
        (hfne : d.shape.instFields ≠ [])
        (hmem : ∀ (k : Nat) (hk : k < d.shape.insts.length),
          ∃ (cb : Bool) (aw dw : Nat), memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw))
        (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
          (d.shape.insts[k]).2.1.length = 4)
        (hfield : ∀ (k : Nat), k < d.shape.insts.length →
          d.shape.instFields.getD k "" = "out")
        (hargsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
          (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
          (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 → k = k')
        (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
          (hk' : k' < d.shape.insts.length), memNameAt d k = memNameAt d k' →
          (d.shape.insts[k]).1 = (d.shape.insts[k']).1)
        (hparent : ∀ (k : Nat), k < d.shape.insts.length → memNameAt d k ≠ declName.toString)
        (hout : ∀ o ∈ d.shape.layout.outs, o.name.toList.head? ≠ some 'i') :
        MachineClosesAt mctx mref cctx cref declName d.shape

No reflection premise, no child-interface premise, no world premise. Every
hypothesis is a statement about the reader's data `d` and names.

    structure MemOnlyCloseData (d : MachineData) : Prop     -- alias, argsN, field, argsNd, outHead

    theorem machineClosesAt_of_memOnlyData {declName} {d} {nDecl aw dw}
        (D : Tools.ShippingMemOnly.MemOnlyData d nDecl aw dw) (C : MemOnlyCloseData d)
        (hsep : …) (hparent : …) : MachineClosesAt mctx mref cctx cref declName d.shape

    theorem sep_of_one   (h : ∀ k hk, (d.shape.insts[k]).1 = c) : <hsep>
    theorem parent_of_one (h : ∀ k hk, (d.shape.insts[k]).1 = c) (hc : memChild? c = some md)
        (hnot : declName.toString ∉ [md.1.name]) : <hparent>

How the hypotheses of M2 are met (tables `nameK := memNameAt d`,
`nk := fun _ => 4`, `outsK := fun _ => ["out"]`,
`namesK := fun k => [memNameAt d k]`):

| M2 | from |
|---|---|
| `hkid` | `hmem` + `Kid.mem` + `memIface` (through the BUILT `memKid_iface`), `memNameAt_eq` |
| `hargsN`, `hfieldOut` | `hargsN`, `hfield` |
| `hfieldsNd` | `hargsNd` (the field clause is dropped: stronger hypothesis, same on this data since every field is `out`) |
| `hsep`, `hparent` | the same hypotheses |
| `hfresh` | `hout` + `instName_ne_of_head` |
| `hparentD` | `hparent` |
| `hdisjD` | contrapositive of `hsep` |

NOT proved (kept as hypotheses, decided per declaration): `hsep` and
`hparent` in general. A general proof needs "the module names of two
different placeholders differ" (injectivity of
`s!"SparkleMem_{kind}_{aw}_{dw}"` in `(kind, aw, dw)`, i.e. of `Nat.repr`)
and "no declaration prints as a memory module name"; neither is needed for
the five declarations.

## 4. Every hypothesis, per declaration, by hand

T = true by reading/measured data; D = additionally decided by a named
kernel `decide` in the test (a failure names itself); NR = not read.

| hypothesis | `memCounter` | `syncNarrow` | `memWide` | `twoMems` | `mixedMems` |
|---|---|---|---|---|---|
| `ok`, `hbody`, `hC`, `hslots`, `hdomB`, `hfne` | BUILT (`memCounter_data`) | BUILT | BUILT | BUILT | BUILT |
| `hmem` | T: one placeholder `combo.4.8`, `mem_isMem` BUILT | T: `sync.3.5` | T: `combo.6.16` | T: `combo.4.8` at both entries | T: `combo.4.8` / `sync.4.8`, `mem_isMemC` / `mem_isMemS` BUILT |
| `hkid` (M2) | T (`memIface` BUILT, either kind, any widths) | T | T | T | T |
| `hargsN` | T,D: `[1,2,3,0]` | T,D | T,D | T,D: both lists have 4 | T,D |
| `hfield` / `hfieldOut` | T,D: `[out]` | T,D | T,D | T,D: `[out,out]` | T,D: `[out,out]` |
| `hargsNd` / `hfieldsNd` | T,D: one entry | T,D | T,D | T,D: SAME callee and field, argument lists `[1,2,3,0]` ≠ `[0,2,3,4]` | T,D: different callees |
| `hsep` | T: one callee (`sep_of_one`) | T | T | T: one callee — the conclusion holds for the two entries | T,D: `SparkleMem_combo_4_8 ≠ SparkleMem_sync_4_8` (`names_ne`) |
| `hpair` (inside M2) | — | — | — | T: proved in M2; both entries are the table value `memModule true 4 8` | — (no two entries of one callee) |
| `hparent` | T,D: the parent's printed name has `.`, `SparkleMem_combo_4_8` has none (`cands`) | T,D | T,D | T,D | T,D: against both names |
| `hparentD` | T (from `hparent`) | T | T | T | T |
| `hdisjD` | T: vacuous (one callee) | T | T | T: vacuous (one callee) | T: `SparkleMem_combo_4_8 ∉ [SparkleMem_sync_4_8]` and conversely; each design is its own module |
| `hout` / `hfresh` | NR,D | NR,D | NR,D | NR,D | NR,D |
| `halias` | T,D: lets `addr` (slot projection), `wa`, `wd`, `we` (inputs) | T,D | T,D | T,D: + the constant `0#4` (no variable) | T,D: + `Signal.snd st` (slot projection) |

`halias` by reading `aliasOk` (`Tools/ShippingMachineClosesData.lean`
129–136): a `let` field passes when it is no variable, or a variable at a
position `< nIn + slots`, or a variable of a `let` whose field is a
variable. Whether `Signal.fst st` is reflected as a slot variable (position
in `[nIn, nIn + slots)`) or as a term was NOT read; both cases pass.

`hout`: the parents' output names were NOT read. The built `seqMem` (same
front end, a scalar `Signal.loop` result) passed the same condition. The
first command of each test logs the outputs and throws if one starts with
`i`.

No hypothesis is known false on any of the five declarations. Nothing is
blocked.

## 5. Endpoint — premise — predicted state

For each `f` of `memCounter`, `syncNarrow`, `memWide`, `twoMems`,
`mixedMems` (all WRITTEN, NOT BUILT):

| endpoint | premise | predicted state |
|---|---|---|
| `f.machine_design_noPortsR0_closed` (new) | `MachineClosesAt f` (the last binder of `f.machine_design_noPortsR0`, its one NOT-ALLOWED premise) | predicted ABSENT, pending build |
| | binder added | none (`f_closes` has NO premise) |
| | the run (`hr`), `MachineDefines f` | stay |
| | antecedent under the existentials `ChildBnd mref cref w` (allowed) | stays |
| `f.machine_design_noPortsR0_closed_gap` (new) | gap hypotheses | predicted none; premise listing 0 NOT ALLOWED |
| `f.machine_design_noPortsR0` (open) | unchanged | — |

If built: five endpoints with no check premise and no NOT-ALLOWED premise —
the run, the reflection of `f` and `ChildBnd` remain.

## 6. What the closed endpoint is relative to

There is NO base closed endpoint for a memory-only parent:
`#machine_design_svR0` refuses them ("no sequential child", measured, b-14),
and `f.machine_design_sv0` has no `_closed` form — its closing premise is
the all-worlds `MachineCloses f`, which cannot be discharged for a shape
with calls (`Tools/ShippingMemOnlyAtAll.lean`, conditional).

So `f.machine_design_noPortsR0_closed` is a NEW statement, not "an existing
endpoint with a premise removed" in the sense of the earlier rounds. Against
`f.machine_design_sv0`:

1. the four checks `shipsHierCheck (childMap D.modules) b`,
   `kidsMem (childMap D.modules) b.body`,
   `designCheck (childMap D.modules) 0 (checkedOptimize b)`,
   `outsCheck (childMap D.modules) 0 (checkedOptimize b)` — ABSENT;
2. the boundary `True` — is `ChildBnd mref cref w` (ADDED antecedent: the
   child-cache boundary of the run's start world);
3. the all-worlds premise `MachineCloses f` — NONE in its place (the at-form
   closing is proved from reader data, not asked);
4. the run and `MachineDefines f` — the same;
5. the conclusion: the head's `DesignSV …` in both; whether the two print
   the same is LOGGED by the built `auditAt`, not asserted.

The audit asserts 1–4 on the statements (constants found / not found, the
binder lists, the antecedent list); it does not prove an implication between
the old and the new endpoint in either direction.

## 7. Left open

* A general `hsep` / `hparent` for memory placeholders (§3).
* A generator: the five tests are by hand (four from one text template with
  the declaration's names substituted, `mixedMems` separately).
* A parent reading one memory module twice on the same operand `let`s
  (`hargsNd` false): no such declaration in the corpus was looked for.
* Depth ≥ 1 with a memory child; a memory entry beside callees that share a
  descendant: unchanged (A-mem-closing §5).

## 8. Build queue (integrator)

`lakefile.lean`:

    lean_lib «Tools.ShippingMemOnlyCloses» where
      roots := #[`Tools.ShippingMemOnlyCloses]

`Tests/AllTests.lean`:

    import Tests.Compiler.NoPortsMemOnlyClosedMemCounterTest
    import Tests.Compiler.NoPortsMemOnlyClosedSyncNarrowTest
    import Tests.Compiler.NoPortsMemOnlyClosedMemWideTest
    import Tests.Compiler.NoPortsMemOnlyClosedTwoMemsTest
    import Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest

Order: (1) `Tools.ShippingMemOnlyCloses` (imports `ShippingMemClosesKids`,
`ShippingMemOnly`); (2) `Tests.Compiler.NoPortsMemOnlyClosedLib` (imports 1,
`NoPortsMemOnlyAtLib`, `NoPortsMemSeqMemClosedTest`, `ShippingNameSep`);
(3) `NoPortsMemOnlyClosedMemCounterTest` first (the smallest: it exercises
every shared piece), then the other four in any order.

## 9. UNVERIFIED, in risk order

1. `closeLast` (imported, unchanged) on a memory-only endpoint: it compares
   the closing binder's declaration argument with `toExpr f` by `==`
   (syntactic), and takes the LAST binder. Both hold for `seqMem` (BUILT);
   for the memory-only endpoints the binder is built by `generateM0` from
   `f.machine_ships_hier`'s own closing binder (read: `cT.getAppArgs`), the
   same source — inferred, not measured. If `==` fails the error is
   "its last binder is not MachineClosesAt of f".
2. The audit's counts: 3 proposition binders in the open form (measured:
   `hr`, `entry`, `closes`), 2 in the closed; one antecedent, printed the
   same in both; one premise line fewer; `allPropsOk` (`MachineDefines` of
   arity 6 with the declaration at argument 4 — as the built `seqMem` audit
   reads it).
3. Kernel decisions never run before: `f_alias` (`letsAliasOk` of the five),
   `f_outHead` (output names not read), `f_notin` (`cands` of a
   five-component name against the evaluated module name — the built
   `seqMem_notin` is the same shape), `names_ne` (two evaluated module
   names), `f_argsN` / `f_field` / `f_argsNd` (bounded `∀` over the entries,
   as the built `seqMem_argsN` / `_fieldsNd`).
4. `machineClosesAt_memOnly`: the `show` lines after `refine` (goals with
   the tables substituted — beta-reduced or not), `List.mem_singleton`,
   `memNameAt_eq` (a `congrArg` whose sides are `memNameAt d k` and
   `md.1.name` up to unfolding `Option.map` / `Option.getD` on `some`).
5. `machineClosesAt_of_memOnlyData` (`Exists.elim` re-packing `D.mem`), the
   elaboration of `sep_of_one f_entry` / `parent_of_one f_entry mem_isMem
   f_notin` against the expected hypothesis types (the implicit `c`, `md`,
   `declName`).
6. `logData` (meta): `MessageData` of `List (List Nat)`, the duplicate-key
   loop.
