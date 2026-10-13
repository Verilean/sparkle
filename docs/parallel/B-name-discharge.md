# B — name premises after the injective module names: census, general lemmas, one connection (round par/b-29)

Branch `par/b-29` from `poc/roundtrip-proof` b7dc0ec4. Worker B.

**NOTHING HERE IS BUILT.** No `lean`, `lake` or simulator was started. Every
Lean file is WRITTEN, NOT BUILT; no premise is removed and nothing is proved
until the integrator builds it. No existing file was changed.

Marks: **[R]** read in a file of b7dc0ec4; **[B]** built per the commit
message / record of b7dc0ec4 (not re-run); **[I]** inferred, not checked.

## 0. Files

| file | content |
|---|---|
| `Tools/ShippingNameDischarge.lean` | pure lemmas (imports only `Tools.ShippingModuleName`): each name-hypothesis shape from a hypothesis on `Lean.Name`s, or from none |
| `Tools/ShippingMemOnlyNames.lean` | the memory-only closing WITHOUT `hsep` / `hparent`: `memChild_shape`, `memChild_name_of`, `memNameAt_ofMem`, `memOnly_sep`, `memOnly_parent`, `machineClosesAt_memOnly_names`, `machineClosesAt_of_memOnlyData_names` |
| `Tools/ShippingClosesNames.lean` | the three built closing theorems restated about declarations (`…_gateKidsN`, `…_seqKidsN`, `…_kidsDN`); used by no generator |
| `Tests/Compiler/NameDischargeTest.lean` | `mixedMems_closesN`, `mixedMems_closes_any`, `mixedMems.machine_design_noPortsR0_closedN`, the audit |
| `docs/parallel/B-name-discharge.md` | this file |

## 1. The finding that reorders the task

**[R]** No generated endpoint in the built tree has a name premise as a
BINDER. The generators have a binder branch, but it is taken only when the
Boolean check of `Tools.ShippingNameSep` fails at generation time, and no
declaration a closing command is run on makes it fail:

* `Tools/ShippingMachineClosesAtGen.lean` 129–149, `…AtGenG.lean` 55–75,
  `Tools/ShippingChildIfaceGen.lean` 141–160, 190–232, 326–334: `hnames` /
  `hparent` / `hparentD` / `hselfD` / `hdisjD` / `hself` become binders
  (`hnames`, `hparent`, `hN_…_names`, `hN_…_parent`, `hN_…_parentD`,
  `…_selfD`, `…_disjD`, `hN_…_self`) ONLY in the `else` of
  `kids.all … sepB …` / `namesSep`.
* The tests assert the absence: `Tests/Compiler/OneOutTwoCalleeTest.lean`
  90–94 (throws on a binder mentioning `Name.toString` / `ofDecl`),
  `ShippingCallsCloseTest.lean` 172–180 (`auditClosed … 1` / `2`: only
  reflections), `NoPortsKeccakSpongeTest.lean` 124 ("a name-separation
  premise would be a fifth binder").
* The one place the binder branch WAS taken is `mixDeep`
  (`Tests/Compiler/NoPortsMixDeepTest.lean` 21–48): `namesSep` false because
  `midH` is a callee and a descendant of the callee `mid2`; the third binder
  (`hdisjD`) is false by reading, and the file deliberately generates no
  closing. Not touched here.
* The only declarations on which `sepB` is false for a TRUE separation are
  Finding H's (`«#ccp.k»` / `«#ccp».k`, …; `CacheCoherenceProbe.lean`
  86–105). No closing command is run on a parent of them [R: grep of
  `#machine_closes…` / `#machine_no_ports…` / `#machine_oneout…`].

So what the endpoints "still carry" (H-fix-injective-names.md §7) is not a
binder: it is a PER-DECLARATION DECISION inside the closing's proof —
`Tools.ShippingNameSep.Enc.* _ (by decide)` on `sep` / `sepB`, i.e. the
kernel enumerating the candidate renderings of `Name.toString` (2^k strings
for k components, pairwise compared; "one test module peaks at 2.44 GiB",
`ShippingNameSep.lean` header), about a name function the compiler no longer
uses — or `name_not_mem`, or a kernel comparison of two `ofMem` strings. And
a generation-time GUARD of the same check that turns a true separation into
a binder (or, in `#machine_no_ports_memseq`, into a refusal: 257–270).

Progress in this area is therefore "general theorem X lost hypothesis Y" and
"endpoint Z no longer rests on a per-declaration name decision"; the
endpoint's binder list does not get shorter, because it has no name binder.

## 2. Census

"Today" = b7dc0ec4. "Follows" = follows from distinctness of declaration
names (plus `ofDecl_injective` / `ofDecl_ne_ofMem` / `ofMem_injective`).
Lemma names without a prefix are in `Tools.ShippingNameDischarge`.

| # | shape | introduced by | today's treatment | follows? | lemma (WRITTEN) |
|---|---|---|---|---|---|
| 1 | `hsep` / `hnames`: `∀ c ∈ insts.map (·.1), ∀ c' ∈ …, ofDecl c = ofDecl c' → c = c'` | `ShippingCallsGate.machineClosesAt_of_gateKids` 252; `CallsSeqKids` 74; `CallsKidsD` 120; `CallsKidsS` 137, 366, 408; `MemClosesKids` 558 | one callee: `decide` on `Name`s. Several: `Enc.hnames_of _ (by decide)` — the lemma ignores its check since b7dc0ec4 but the generator still evaluates `sepB` at generation time and as a `decide`; `sepB` false → BINDER (`AtGen` 133–141, `AtGenG` 59–67, `ChildIfaceGen` 145–152, `CallsKidsSGen` 54, 80) | YES, with NO hypothesis | `names_inj` |
| 2 | `hparent`: `∀ c ∈ insts, ofDecl c.1 ≠ ofDecl declName` | the same theorems (253, 76, 122, 139/368/410, 560) | `Enc.hparent_of _ _ (by decide)` on `sep` (candidate strings); `sepB` false → BINDER (`AtGen` 144–149, `AtGenG` 70–75, `ChildIfaceGen` 154–160, `CallsKidsSGen` 56, 81) | YES, from `∀ c ∈ insts, c.1 ≠ declName` (reader data, `decide` on `Name`) | `parent_ne` |
| 3 | `hparentD`: `ofDecl declName ∉ namesK k` | `CallsKidsD` 128; `CallsKidsS` 142/371/413; `MemClosesKids` 299, 447, 563 | all children leaves: `by decide` on empty lists. Else `Enc.not_mem_map_of _ _ (by decide)` on `sep`; `namesSep` false → BINDER together with 4 and 5 (`ChildIfaceGen` 190–232) | YES for `namesK k = (declsK k).map ofDecl`, from `declName ∉ declsK k` | `not_mem_map`, `parentD_of` |
| 4 | `hselfD`: `ofDecl insts[k].1 ∉ namesK k` | `CallsKidsD` 129; `CallsKidsS` 143/372/414; `MemClosesKids` 564 | as 3 | YES, from `insts[k].1 ∉ declsK k` | `selfD_of` |
| 5 | `hdisjD`: for different callees, `ofDecl insts[k].1 ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k'` | `CallsKidsD` 131–133; `CallsKidsS` 416–418; `MemClosesKids` 566–568 | as 3 (`Enc.not_mem_map_of` + `Enc.disjoint_map_of`) | ONLY when the declaration form holds: `insts[k].1 ∉ declsK k' ∧ ∀ a ∈ declsK k, a ∉ declsK k'`. FALSE for shared descendants (`mixDeep`) in either form — a cache-coherence question, NOT touched | `disjD_of`, `disjoint_map` (the transfer only) |
| 6 | `hself` / `self`: `ofDecl c ∉ namesOf d namesK` | `KidsChildIface` 150, 378; `ChecksCore` 309, 382; `ChecksRun` 207; `ChecksRun2` 62, 167; `OneOutKid.self` 218; `GenKid.self` 259; `MemClosesKids.toP` 175 | `rw [namesOf_map]; exact Enc.not_mem_map_of _ _ (by decide)` (`NoPortsKidsCommand` 189, `NoPortsDeepCommand` 344, `ChildIfaceGen` 326–329, hand tests `NoPortsGrandTest` 225, `NoPortsGrandHTest` 205, `NoPortsTopD2Test` 248); `sepB` false → BINDER `hN_…_self` (`ChildIfaceGen` 330–334) | YES, from `c ∉ declsOf d declsK` (after the built `namesOf_map`) | `not_mem_map` |
| 7 | nodup of child / descendant module names | not a hypothesis of a closing theorem at b7dc0ec4 [R: grep `Nodup` beside `ofDecl`]; `ChildIfaceD.desNd` is a FIELD proved from the run, not a premise | — | YES, from `L.Nodup` | `nodup_map` (kept for the shared-descendant work) |
| 8 | memory-only `hparent`: `memNameAt d k ≠ ofDecl declName` | `MemOnlyCloses.machineClosesAt_memOnly` 106, `…_of_memOnlyData` 167 | `parent_of_one` + `f.notin{j} : ofDecl f ∉ [(m).1.name]` by `name_not_mem` (`NoPortsMemCommand` 436–440, 501–514; five hand tests). Which branch of `name_not_mem` runs (structural `not_mem_cons_mem`, or `decide` EVALUATING `ofDecl`) is not determinable by reading | YES, with NO hypothesis (from `hmem`, which the theorem already has) | `ShippingMemOnlyNames.memOnly_parent` |
| 9 | memory-only `hsep`: `memNameAt d k = memNameAt d k' → insts[k].1 = insts[k'].1` | `MemOnlyCloses` 103–105, 164–166 | one placeholder: `sep_of_one`. Several: `namesNe{i}_{j}` by `decide` — the kernel EVALUATES two `ofMem` strings and compares them (`NoPortsMemCommand` 71, 452–500; `mixedMems`: `names_ne`) | YES, with NO hypothesis (`ofMem_injective` + `memChild?` read backwards) | `ShippingMemOnlyNames.memOnly_sep`, `memChild_name_of` |
| 10 | memory beside declaration children: `nameK k ≠ ofDecl declName`, `nameK k = nameK k' → …`, `ofDecl f ∉ names`, leaf `∉` memory names | `MemClosesKids.machineClosesAt_of_kidsDM` 293–299 | generated lemmas: `notinP{j}`, `leafNotin{i}_{j}` by `name_not_mem`; `leafNeParent{i}`, `leafNe{i}_{j}` by `Enc.sep_ne (by decide)`; `memNe{i}_{j}` by `decide` on strings (`NoPortsMemSeqCommand` 669–696). Generation-time guards 257–270 REFUSE where `sep` fails | YES: declaration–declaration from `Name` ≠, declaration–memory unconditionally, memory–memory from the parameters | `decl_ne_mem`, `mem_ne_decl`, `not_mem_mems`, `mem_not_mem_decls`, `not_mem_append`, `mems_ne` — pure lemmas only; the connection to the generator is NOT written |
| 11 | `hfresh`: `o.name ≠ s!"inst{k}_{ofDecl c}"` (output port vs instance name) | every closing theorem (`CallsGate` 255, `CallsSeqKids` 77, `CallsKidsD` 123, `CallsKidsS`, `MemClosesKids` 297, 561) | `instName_ne_of_head` when no output name starts with `i` (a `decide` on first characters); else BINDER (`hfresh`, `hN_…_fresh`); the memory generators throw at generation time | NO — ports and instances are different name spaces; nothing about declarations decides it | none (stays) |
| 12 | run-level `c.1.name ≠ ofDecl declName` over the children | `CallsGate` 109, `CallsRunG` 119 | derived inside the closing theorems from `hparent` + the child interface's `name` field | n/a (not a generator-facing premise) | — |
| 13 | a declaration against an ARBITRARY string (`Enc.not_mem_of`, `Enc.fresh_of`) | `ShippingNameSep` 899–906 | `decide` evaluating `ofDecl` | NO | none |

No name hypothesis at all [R: grep `ofDecl|ofMem|Name.toString` gives no hit]:
`Tools/ShippingLeafDesign*.lean` (`#machine_leaf_design`),
`Tools/ShippingFinalGoalCommand.lean` (`#machine_goal_gap_of`), `Tools/ShippingNoPortsCommand.lean`,
`…SlotlessCommand.lean`, the one-out generators' own files (they consume
`f.machine_closes_at`, rows 1–2, and `GenKid.self` / `OneOutKid.self`, row 6).

What I did NOT census: the legacy-route files
(`ShippingRegisterSoundness`, `ShippingInstanceEntrySoundness`,
`ShippingMemoryEntrySoundness`, `ShippingHarness*`, `ShippingLegacySem*`:
≈ 450 occurrences of `ofDecl`). By the H-fix record they are mirrors of
`CircuitM.init (ofDecl declName)` and `m.name = ofDecl declName`
conclusions; I did not check each for a separation hypothesis.
`Tools/ShippingLegacySemSuffix.lean` 18 still has a hypothesis over
`ShippingNameSep.cands` (`endsWith`), about `Name.toString` — a different
function now; not examined.

## 3. The general lemmas (`Tools/ShippingNameDischarge.lean`)

```lean
theorem names_inj (L : List Name) : ∀ c ∈ L, ∀ c' ∈ L, ofDecl c = ofDecl c' → c = c'
theorem parent_ne {α : Type} (insts : List (Name × α)) (parent : Name)
    (h : ∀ c ∈ insts, c.1 ≠ parent) : ∀ c ∈ insts, ofDecl c.1 ≠ ofDecl parent
theorem not_mem_map {c : Name} {L : List Name} (h : c ∉ L) : ofDecl c ∉ L.map (fun n => ofDecl n)
theorem disjoint_map {L L' : List Name} (h : ∀ a ∈ L, a ∉ L') :
    ∀ x ∈ L.map (fun n => ofDecl n), x ∉ L'.map (fun n => ofDecl n)
theorem nodup_map : ∀ (L : List Name), L.Nodup → (L.map (fun n => ofDecl n)).Nodup
theorem parentD_of (n : Nat) (parent : Name) (declsK : Nat → List Name)
    (h : ∀ k, k < n → parent ∉ declsK k) : ∀ k, k < n → ofDecl parent ∉ (declsK k).map …
theorem selfD_of  …  (h : ∀ k hk, (insts[k]).1 ∉ declsK k) : …
theorem disjD_of  …  (h : ∀ k hk k' hk', (insts[k]).1 ≠ (insts[k']).1 →
      (insts[k]).1 ∉ declsK k' ∧ ∀ a ∈ declsK k, a ∉ declsK k') : …
theorem decl_ne_mem / mem_ne_decl / not_mem_mems / mem_not_mem_decls / not_mem_append
theorem mems_inj / mems_ne
```

The hypotheses are statements about `Lean.Name`s of the reader's data.
`decide` on them is `Name.beq` (**[R]** `Init/Prelude.lean` 4782–4787 of the
toolchain, v4.32.1: structural, last component first; `DecidableEq Name` is
`if h : a == b …`, `Init/Meta/Defs.lean` 343) — no enumeration, no rendering.
**[B]** the kernel already decides `Name` equalities in the built generators
(`ShippingMachineClosesAtGen.lean` 131: `by decide : ∀ c ∈ …, c = k0`).

`Tools/ShippingClosesNames.lean` applies them once each:
`machineClosesAt_of_gateKidsN` / `…_seqKidsN` (no `hsep`; `hparentN : ∀ c ∈
d.shape.insts, c.1 ≠ declName`), `machineClosesAt_of_kidsDN` (additionally
`declsK : Nat → List Name` in place of `namesK`, and `hparentDN`, `hselfDN`,
`hdisjDN` about membership of declarations). `hfresh` is passed on verbatim.

**Honest limits.** `disjD_of` / `…_kidsDN` do not make `mixDeep` closable:
its `hdisjDN` is false (shared descendant `midH` / `rcH`). `parent_ne`'s
hypothesis "no call entry is a call of the parent" is true for every
non-recursive declaration but is NOT proved from the reader here — it is a
`decide` on the reflected shape, like the other data conditions. Rows 11 and
13 are untouched.

## 4. The chosen endpoint: `mixedMems.machine_design_noPortsR0_closed`

A memory-only parent with two different memory modules
(`Tests/Compiler/NoPortsMemOnlyClosedMixedMemsTest.lean`, **[B]** in
`Tests.AllTests`). Chosen because it is the built endpoint whose closing
rests on the most per-declaration name work, including a kernel STRING
comparison, and because the general theorem behind it loses its two name
hypotheses outright (rows 8, 9) — no `Name`-level side condition is left.

### BEFORE (quoted from source)

The general theorem, `Tools/ShippingMemOnlyCloses.lean` 162–168:

```lean
theorem machineClosesAt_of_memOnlyData {declName : Name} {d : MachineData} {nDecl aw dw : Nat}
    (D : Tools.ShippingMemOnly.MemOnlyData d nDecl aw dw) (C : MemOnlyCloseData d)
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), memNameAt d k = memNameAt d k' →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1)
    (hparent : ∀ (k : Nat), k < d.shape.insts.length → memNameAt d k ≠ (Sparkle.IR.ModuleName.ofDecl declName)) :
    MachineClosesAt mctx mref cctx cref declName d.shape :=
```

Its header, 38–41: "NOT proved here: that two different placeholder names
give two different module names (`memNameAt` injective on placeholders — it
would need `Nat.repr` injective); `hsep` and `hparent` stay hypotheses and
are decided on each declaration's concrete names."

The per-declaration discharge, `NoPortsMemOnlyClosedMixedMemsTest.lean`
125–139, 161–191, 204–205:

```lean
theorem names_ne : nameC ≠ nameS := by
  first | decide | decide +kernel
theorem mixedMems_notinC :
    (Sparkle.IR.ModuleName.ofDecl (``…mixedMems : Lean.Name)) ∉ [nameC] :=
  (by name_not_mem)
theorem mixedMems_notinS : … ∉ [nameS] := (by name_not_mem)
theorem mixedMems_sep : ∀ (k : Nat) (hk : …) (k' : Nat) (hk' : …),
    memNameAt …machineData k = memNameAt …machineData k' → (…insts[k]).1 = (…insts[k']).1
theorem mixedMems_parent : ∀ (k : Nat), k < … → memNameAt …machineData k ≠ ofDecl ``…mixedMems
…
  Tools.ShippingMemOnlyCloses.machineClosesAt_of_memOnlyData
    mixedMems_data mixedMems_closeData mixedMems_sep mixedMems_parent
```

The closed endpoint's premise list, as its audit asserts it
(`Tests/Compiler/NoPortsMemOnlyClosedLib.lean` 125–131, 193–200, 208–213):
"exactly TWO proposition binders — the run (`RunsTo`) and `MachineDefines …
f …`"; "under the existentials ONE antecedent, allowed … and it is
`ChildBnd`"; "0 NOT ALLOWED". (The statement itself is generated by
`closeLast` from the generated open endpoint; I did not see its text.)

### AFTER (EXPECTED; asserted by `Tests/Compiler/NameDischargeTest.lean`, not built)

```lean
theorem machineClosesAt_of_memOnlyData_names {declName : Name} {d : MachineData}
    {nDecl aw dw : Nat}
    (D : Tools.ShippingMemOnly.MemOnlyData d nDecl aw dw) (C : MemOnlyCloseData d) :
    MachineClosesAt mctx mref cctx cref declName d.shape
```

| | before | expected after |
|---|---|---|
| hypotheses of the general theorem mentioning `ofDecl` / `ofMem` / `memNameAt` / `Name.toString` | 2: `hsep`, `hparent` | 0 |
| complete hypothesis list of the general theorem | `D : MemOnlyData d nDecl aw dw`, `C : MemOnlyCloseData d`, `hsep`, `hparent` | `D`, `C` |
| per-declaration name lemmas under `mixedMems`'s closing | `names_ne` (kernel string comparison), `mixedMems_notinC`, `…_notinS` (`name_not_mem`), `…_atC`, `…_atS`, `…_sep`, `…_parent` | none |
| `Tools.ShippingNameSep` under the closing | `Enc.not_mem_cons_mem` or `Enc.not_mem_of` (the test LOGS which) | none |
| proposition binders of `mixedMems.machine_design_noPortsR0_closed(N)` | the run (`RunsTo`), `MachineDefines mixedMems` | THE SAME TWO |
| antecedent under the existentials | `ChildBnd mref cref w` | THE SAME |
| NOT ALLOWED premises | 0 | 0 |

**The endpoint's own premise list is EXPECTED UNCHANGED** (`…_closedN` is
asserted `isDefEq` to the built `…_closed`). What is expected to disappear:
the hypotheses `hsep` and `hparent` of the general memory-only closing
theorem, and with them the seven per-declaration name lemmas of `mixedMems`.
`mixedMems_closes_any` states the closing for every parent declaration name.

What stays per declaration (conditions, not reductions): `mixedMems_data`,
`mixedMems_closeData` — among them `outHead` (no output starts with `i`,
row 11).

How `hsep` / `hparent` are derived (`Tools/ShippingMemOnlyNames.lean`):
`memNameAt d k = (memModule cb aw dw).1.name` (**[B]** `memNameAt_eq`) `=
ofMem cb aw dw` (`memModule_name`: **[R]** `MachMemory.lean` 51, a `let`);
then `ofDecl_ne_ofMem` for the parent, and for `hsep` `ofMem_injective` plus
`memChild_name_of` — a placeholder with child `memModule cb aw dw` is
`memChildName cb aw dw` (**[R]** `memChild?`, `MachMemory.lean` 65–70).

### Follow-ups this enables (NOT done; no generator output was changed)

* `#machine_no_ports_mem` (`Tools/ShippingNoPortsMemCommand.lean` 436–527):
  call `machineClosesAt_of_memOnlyData_names $(data) $(closeData)`; drop
  `notin{j}`, `at{j}`, `namesNe{i}_{j}`, `sep`, `parent`. Covers the four
  other built memory-only endpoints and `withMemory`.
* `closesAtCore` / `closesAtCoreG` / `closesDeep` / `ifaceDeep`: replace the
  three-way `if` (one callee / `sepB` / binder) by `names_inj _`,
  `parent_ne _ _ (by decide)`, `not_mem_map (by decide)` — the binder branch
  and the `sepB` evaluation go away; `OneOutTwoCalleeTest` 102–105 and
  `ShippingCallsCloseTest` 186–188 assert `Enc.hparent_of` / `Enc.hnames_of`
  in the proof and must be updated in the same change.
* `#machine_no_ports_memseq`: rows 10; the guards at 257–270 can go.

## 5. For the integrator

`lakefile.lean` (not edited):

```lean
lean_lib «Tools.ShippingNameDischarge» where
  roots := #[`Tools.ShippingNameDischarge]

lean_lib «Tools.ShippingMemOnlyNames» where
  roots := #[`Tools.ShippingMemOnlyNames]

lean_lib «Tools.ShippingClosesNames» where
  roots := #[`Tools.ShippingClosesNames]
```

`Tests/AllTests.lean` (not edited), after
`import Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest`:

```lean
import Tests.Compiler.NameDischargeTest
```

Build order (each depends only on built files plus the ones before it):

1. `Tools.ShippingNameDischarge` — imports `Tools.ShippingModuleName` only.
2. `Tools.ShippingMemOnlyNames` — imports `Tools.ShippingMemOnlyCloses`, 1.
3. `Tools.ShippingClosesNames` — imports `Tools.ShippingCallsKidsD`, 1.
   Independent of 2; if it fails, drop its import and block (e) from the test
   and the chosen endpoint is unaffected.
4. `Tests.Compiler.NameDischargeTest` — imports
   `Tests.Compiler.NoPortsMemOnlyClosedMixedMemsTest`, 2, 3.

Expected log lines: `NAMEDISCHARGE [...]`, `NAMEDISCHARGE HYPS …` (2 / 0),
`NAMEDISCHARGE DEPS`, `NAMEDISCHARGE MEASURED` (answers which branch
`name_not_mem` took at b7dc0ec4), `NAMEDISCHARGE BINDERS`,
`NAMEDISCHARGE PREMISES`, three `NAMEDISCHARGE HYPS … ofDecl` lines
(3 → 1, 3 → 1, 6 → 2), `NAMEDISCHARGE AUDIT`.

Only after 1, 2 and 4 are green with standard axioms may the record say:
"`machineClosesAt_of_memOnlyData` lost `hsep` and `hparent`
(`…_names`; remaining hypotheses: `MemOnlyData`, `MemOnlyCloseData`);
`mixedMems`'s closed endpoint no longer rests on a per-declaration name
decision; its premise list is unchanged."

## 6. UNVERIFIED, in risk order

1. `memChild_shape` (`ShippingMemOnlyNames.lean`): `split at h` on the
   `match` of `memChild?` (a string-literal pattern), then on the two `if`s;
   `rename_i hk` for the `if`'s condition; `eq_of_beq hk` (needs `LawfulBEq
   String`), with two fallbacks in a `first`; `cases h`; the witness by
   `⟨true, _, _, rfl, rfl⟩`, where the first `rfl` must see
   `memChildName true aw dw` reduce to the matched pattern (an `if true then
   "combo" else "sync"` under `Name.mkStr`). The built
   `Tools.ShippingMachineInstG.memChild_eq` (437–446) has the same `split`
   skeleton and no naming of the condition.
2. `memModule_name` by `rfl` (through the `let`s of `memModule`); fallbacks
   `unfold` / `simp`.
3. `Tests/Compiler/NameDischargeTest.lean`, `depsOf`: a transitive walk over
   the proofs under the two closings (everything outside `Init` / `Lean` /
   `Std` / `Lake`), run in the interpreter. Cost NOT estimated by anything
   but reading; if too slow, restrict `isCore` to follow only `Tests.*`,
   `Tools.ShippingMemOnly*`, `Tools.ShippingName*`, `Tools.ShippingModuleName`.
   `env.header.moduleNames[i.toNat]!` / `getModuleIdxFor?` as API.
4. The expected counts in the audit: 2 / 0 for the memory-only theorems;
   3 / 1, 3 / 1, 6 / 2 hypotheses mentioning `ofDecl` (counted by reading the
   binders; `s!"inst{k}_{ofDecl …}"` is assumed to keep the constant `ofDecl`
   in the elaborated term).
5. `isDefEq` of `…_closedN` and `…_closed` (both by `closeLast` from one open
   endpoint; expected syntactically equal).
6. The `example`s: `decide` on `Name` disequalities of names with `#` and
   `.` in a component, on `∀ c ∈ [...]` over `Name × Unit`, and on
   `¬ (true = false ∧ 4 = 4 ∧ 8 = 8)`.
7. `ShippingClosesNames.lean`: three applications with 15–25 arguments,
   binders copied from the built statements; `selfD_of` / `disjD_of` at
   `d.shape.insts` (`List (Name × List Nat × MixedGateBinder)`, `α` inferred);
   `namesK` passed as a `fun` (the hypotheses then differ from the built
   ones by a beta step).
8. `e ▸ hc'` in `not_mem_map` / `disjoint_map` (direction of the rewrite).

## 7. What I could not determine by reading

* Which branch `name_not_mem` takes at b7dc0ec4 (structural, or the kernel
  evaluating `ofDecl`) — the test logs it.
* The text of the generated endpoint statements (`…_noPortsR0`,
  `…_noPortsR0_closed`): generated; I rely on the built audit's description.
* Whether any closing command anywhere in `Tests/` takes a binder branch at
  b7dc0ec4: by grep and by the asserting tests none does, but I did not read
  every one of the 239 test files.
* Whether the legacy-route files carry a separation hypothesis (§2, last
  paragraph).
* The kernel cost of `decide` on `Name` (dis)equalities for large call
  lists (expected small: no enumeration; not measured).

## Integrator's build record (2026-10-13)

BUILT on tree `062fdd0085b5e5bf7eb3a427b4a3999d2469f396` (poc b7dc0ec4 + these files), cgrun 3 GiB swap 0:
`b29-tools` (the three Tools files, first attempt, exit 0, peak 0.89 GB), `b29-test` (exit 1: the audit
compared premise lines that begin with the endpoint's own name), `b29-test2` (exit 0 after the integrator
replaced that label in the comparison; peak 0.33 GB), `b29-all` (`Tests.AllTests`, 1292 jobs, exit 0,
peak 0.44 GB). `h-poc` before it: AllTests 1288 jobs at b7dc0ec4 in the poc tree, exit 0, peak 2.38 GB.

Measured by `NameDischargeTest` (asserting): `machineClosesAt_of_memOnlyData` has 2 name hypotheses,
`machineClosesAt_of_memOnlyData_names` 0; `mixedMems.machine_design_noPortsR0_closedN` has the premise
list of the built `…_closed` (the run, `MachineDefines mixedMems`, `ChildBnd`; 0 NOT ALLOWED), standard
axioms, and its closing reaches none of the seven per-declaration name lemmas; restated closings
`…gateKidsN` / `…seqKidsN` / `…kidsDN` mention `ofDecl` in 1 / 1 / 2 hypotheses instead of 3 / 3 / 6.

NO ENDPOINT LOST A PREMISE: the endpoint had no name binder. What went away is under the proof (two
hypotheses of one general theorem, seven per-declaration lemmas for one declaration). No generator uses
the new theorems yet.
