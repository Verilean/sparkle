# A / the closing of a parent with a memory child (round par/a-18)

Branch `par/a-18`, base poc `9f279734`. NOTHING here was built or run: every
statement about Lean code is "WRITTEN, NOT BUILT"; no premise of any endpoint
counts as removed until the integrator's build. "Read" = the line was read in
the file named; "inferred" = concluded from a neighbouring fact.

## 1. What was read

### 1.1 What `MachineClosesAt seqMem` needs

`MachineClosesAt` (`Tools/ShippingChildRun.lean` 444–450): every run of
`synthesizeMachineCertified … seqMem shape` from an invariant world of
positive depth returns `≠ none`. With `instFields ≠ []` the run ends in
`closeInstsGM` (`Sparkle/Compiler/Elab.lean` 5206–5220), i.e. the pure
`closeInstsG` on the children the `mapM` returns; a memory placeholder's
child is `pure md` (5212–5213), not a compile.

`closeInstsG_of_run` (`Tools/ShippingCallsRunG.lean` 97–137) has NO memory
hypothesis. What it asks of the children:

* per child (111–119): argument-port count, distinct argument ports, the
  entry's field is an output, outputs are not inputs / `clk` / `rst`, distinct
  outputs, the module is not named as the parent;
* `hcons` (120): two children of one module name have one module;
* `hfieldsNd` (121–124), `hfreshOuts` (125–126);
* `hdesign` (127–134), on the joined design: `memSelf` for every child (a
  child with a memory-shaped body is found by its name as a module
  `isMemModule` accepts — `MachMemory.lean` 94–97); every child and every
  module of a child's design is found by its name AS ITSELF; no module has
  an instance of the parent.

Not asked anywhere: "no memory", masked outputs / `flat`, instance
acyclicity beyond "no instance of the parent", "a child is not in its own
design".

### 1.2 Uses of `hnomem`, `ChildIfaceD.name`, `.noMem`, `hselfD`

| file:line | use | true of a memory placeholder child? | replacement (this round) |
|---|---|---|---|
| `Tools/ShippingCallsRunG.lean` 58 (binder), 75–81 (consumed) | the `mapM` body is rewritten to `synthesizeChild` so that `mapM_loop_all` (`ShippingCallsSame.lean` 148) applies | the hypothesis is FALSE (`memChild? = some _`) | `mapM_loop_allM`: per element a pure table value OR a memoised entry; `closeInstsGM_run_allM` (M1), children as `Kid` |
| `Tools/ShippingCallsKidsD.lean` 108 (binder), 158 (passed to `closeInstsGM_run_all`) | only passed on | — | gone (M2 uses M1) |
| `ShippingCallsKidsD.lean` 39 `name : b.name = c.toString`; used 191 (`hcons`), 223 / 228 (child vs its design), 240 / 244 (two callees), 269 (`hparent`), 288 (`hfieldsNd`), 299 (`hfresh`) | names the child module by the declaration's printed name | FALSE: the module is `SparkleMem_combo_4_8` (`MachMemory.lean` 47), the placeholder prints `SparkleMem.combo.4.8` (41–43) | `ChildIfaceP.name : b.name = nm`, `nm = nameK k` given per entry; `hsep`, `hparent`, `hfresh`, `hdisjD` restated over `nameK` |
| `ShippingCallsKidsD.lean` 46 `noMem`; used 306 → `design_checks` `hmem` (`ShippingDesignWithG.lean` 86, 101: `memSelf` by `rw [hmem]`) | makes `memSelf` trivially true | FALSE: the body is the memory statement | `ChildIfaceP.memOk : ∀ cb aw dw, memParams? b = some (cb, aw, dw) → isMemModule cb aw dw b = true` (TRUE of the memory module: `isMemModule_memModule`; vacuous for a real child); `design_checksM` |
| `ShippingCallsKidsD.lean` 129–130 `hselfD`; used 224, 229 | a child module and a module of its design never share a name | FALSE: the memory module's design is `[itself]` (`MachMemory.lean` 58) | `ChildIfaceP.self : ∀ g ∈ design.modules, g.name = b.name → g = b` (TRUE of the memory module; from `hselfD` for a real child: `ChildIfaceD.toP`) |
| `ShippingCallsKidsD.lean` 50–51 `resolves` | NOT USED in the proof (98–317) | vacuously true | dropped from `ChildIfaceP` |
| `desNd`, `desNames`, `closed`, the port fields | 230, 222 / 227 / 241 / 245, 314, 257–268 | TRUE: `[m]` has distinct names; `names = [m.name]`; no instance in the body (`mem_noInst`, BUILT); ports by `mem_inPorts`, `mem_outsIn` (BUILT) | kept as they are |
| `Tools/ShippingCallsKidsS.lean` 125, 174; `Tools/ShippingCallsRunFinal.lean` 73, 96 | the relative closing of the shared-descendant round | — | NOT generalised here (§4) |

## 2. WRITTEN this round

    Tools/ShippingMemClosesRun.lean    mapM_loop_allM, closeInstsGM_run_allM (M1), closeInstsGM_run_all_again
    Tools/ShippingMemClosesKids.lean   memSelf_of, design_checksM, design_checks_again, ChildIfaceP,
                                       ChildIfaceD.toP, isMemModule_memModule, memIface, memKid_iface,
                                       closeInstsG_of_kidsP (pure), machineClosesAt_of_kidsDM (M2),
                                       machineClosesAt_of_kidsD_fromM
    Tests/Compiler/NoPortsMemSeqMemClosedTest.lean   seqMem_closes, …_noPortsR0_closed, gap, audit

No scripted copy: `closeInstsGM_run_all`, `design_checks` and
`machineClosesAt_of_kidsD` are RE-DERIVED from the general statements
(`…_again`, `…_fromM`); the old files are unchanged. The run prelude of M2
(opening `synthesizeMachineCertified` down to the closing, 15 lines) is the
one of `machineClosesAt_of_kidsD`; everything after it is the pure
`closeInstsG_of_kidsP`.

Statements (verbatim, binders abbreviated where they are those of the old
theorem):

    theorem mapM_loop_allM (f : α → MetaM Res) (key : α → Name) (mem : Name → Option Res) (L : RefLaws mref cref)
        (hf : ∀ x w y w', InvV L w → L.dval w ≠ 0 → RunsTo (f x) mctx mref cctx cref w y w' →
          InvV L w' ∧ L.dval w' = L.dval w ∧
            (∀ c0 y0, (L.val w).get? c0 = some y0 → (L.val w').get? c0 = some y0) ∧
            (mem (key x) = some y ∨
              (mem (key x) = none ∧ RealChild mref cref (key x) y ∧
                (L.val w').get? (key x) = some y ∧ (∀ y0, (L.val w).get? (key x) = some y0 → y = y0)))) :
        ∀ l acc r w w', InvV L w → L.dval w ≠ 0 → RunsTo (List.mapM.loop f l acc) … w r w' →
          ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
            (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧
              (mem (key l[k]) = some y ∨ (mem (key l[k]) = none ∧ RealChild mref cref (key l[k]) y))) ∧
            (∀ k c y0, (l.map key)[k]? = some c → mem c = none → (L.val w).get? c = some y0 → ys[k]? = some y0) ∧
            (∀ i j c, i < j → (l.map key)[i]? = some c → (l.map key)[j]? = some c → ys[i]? = ys[j]?) ∧ InvV L w'

    theorem closeInstsGM_run_allM (L) (hB) {shape t m₀ d₀ r} {w w'} (hw : InvV L w) (hd : L.dval w ≠ 0)
        (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
        ∃ children, r = closeInstsG (machNIn shape) shape.insts.length shape.layout.slots.length
            (t.inputs.map (·.name)) (shape.insts.map (·.2.1)) shape.instFields children (m₀, d₀) ∧
          (children.length = shape.insts.length ∧
            ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧ Kid mref cref (shape.insts[k]).1 y) ∧
          (∀ i j c, i < j → (shape.insts.map (·.1))[i]? = some c → (shape.insts.map (·.1))[j]? = some c →
            children[i]? = children[j]?) ∧ InvV L w'

    structure ChildIfaceP (nm : String) (nArgs : Nat) (outs names : List String) (b : Module) (design : Design) : Prop
      name : b.name = nm            nIn, inNd, outs, outsIn, outsNd : as ChildIfaceD
      memOk : ∀ cb aw dw, memParams? b = some (cb, aw, dw) → isMemModule cb aw dw b = true
      desNd, desNames : as ChildIfaceD
      self : ∀ g ∈ design.modules, g.name = b.name → g = b
      closed : as ChildIfaceD

    theorem memIface (cb aw dw) : ChildIfaceP (memModule cb aw dw).1.name 4 ["out"] [(memModule cb aw dw).1.name]
        (memModule cb aw dw).1 (memModule cb aw dw).2

    theorem closeInstsG_of_kidsP (d) (ok) (hbody) (hC) (hslots) (hdomB) (run : MReturns …) (hcl) (hlenC)
        (nameK : Nat → String) (nk) (outsK) (namesK)
        (hfull : ∀ k c, children[k]? = some c → ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) c.1 c.2)
        (hpair : ∀ i j hi hj, (d.shape.insts[i]).1 = (d.shape.insts[j]).1 → children[i]? = children[j]?)
        (hcross : ∀ i j hi hj ci cj, children[i]? = some ci → children[j]? = some cj →
          (d.shape.insts[i]).1 ≠ (d.shape.insts[j]).1 →
          ∀ a ∈ ci.1 :: ci.2.modules, ∀ b ∈ cj.1 :: cj.2.modules, a.name = b.name → a = b)
        (hargsN) (hfieldOut) (hfieldsNd)
        (hsep : ∀ k hk k' hk', nameK k = nameK k' → (d.shape.insts[k]).1 = (d.shape.insts[k']).1)
        (hparent : ∀ k, k < d.shape.insts.length → nameK k ≠ declName.toString)
        (hfresh : ∀ gi k, k < d.shape.insts.length → ∀ o ∈ d.shape.layout.outs, o.name ≠ s!"inst{gi}_{nameK k}")
        (hparentD : ∀ k, k < d.shape.insts.length → declName.toString ∉ namesK k) :
        (closeInstsG … children (closeMachine d.shape.layout t', d₀)).isSome = true

    theorem machineClosesAt_of_kidsDM (d) (ok) (hbody) (halias) (hC) (hslots) (hdomB) (hfne)
        (nameK : Nat → String) (nk) (outsK) (namesK)
        (hkid : ∀ k hk (y : Res), Kid mref cref (d.shape.insts[k]).1 y →
          ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2)
        (hargsN) (hfieldOut) (hfieldsNd) (hsep) (hparent) (hfresh) (hparentD)      -- as closeInstsG_of_kidsP
        (hdisjD : ∀ k hk k' hk', (d.shape.insts[k]).1 ≠ (d.shape.insts[k']).1 →
          nameK k ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k') :
        MachineClosesAt mctx mref cctx cref declName d.shape

    theorem machineClosesAt_of_kidsD_fromM   -- the hypotheses and conclusion of machineClosesAt_of_kidsD, verbatim

    theorem seqMem_closes (hRc : MachineDefines mctx mref cctx cref `cnt cnt.machineData.shape) :
        MachineClosesAt mctx mref cctx cref `seqMem seqMem.machineData.shape

## 3. Every hypothesis of M2 on `seqMem`'s data, by hand

Data: `seqMem` (`Tests/Compiler/ShippingChildBoundaryTest.lean` 52–60);
callees `cnt` (leaf register machine, outputs `n`, `hit`) and
`SparkleMem.combo.4.8`; built log `nDecl=3, binders=10`
(`verification-b13.md` 80) — inferred: 3 entries (`k.hit`, `k.n`, `rd`), 1
slot, 3 `let`s. Tables keyed by the callee: `nameOf`, `nkOf`, `outsNOf`,
`namesOf` (`cnt` ↦ `cnt.toString`, its argument-port count, its output
names, `[]`; otherwise ↦ `SparkleMem_combo_4_8`, `4`, `["out"]`,
`[SparkleMem_combo_4_8]`).

| hypothesis | evaluation | verdict |
|---|---|---|
| `hkid`, `cnt` entries | `ChildIfaceG` of a real child of `cnt` (`seqChild_of_real` on `cnt.machine_leafKid`), `.toD` (`names = []`), `.toP` with `cnt.toString ∉ []` | TRUE |
| `hkid`, memory entry | `Kid.mem`: the child IS `memModule true 4 8`; `memIface` — `name` rfl; 4 argument ports `wa wd we ra` (distinct); output `out`, not an input / `clk` / `rst`; `memOk` by `isMemModule_memModule`; design `[m]`: distinct, `m.name ∈ [m.name]`, `self` (`g ∈ [m]`), no instance in the body | TRUE |
| `hargsN` | `cnt`: 1 non-domain declaration binder (`en`) = 1 argument `let`; memory: 4 = 4 operand `let`s (`Elab.lean` 4042–4069) | TRUE by reading; decided |
| `hfieldOut` | `hit`, `n` ∈ `cnt`'s outputs; `"out"` ∈ `["out"]` (`Elab.lean` 4069) | TRUE by reading; decided |
| `hfieldsNd` | the `cnt` entries differ in the field; one memory entry | TRUE by reading; decided |
| `hsep` | `cnt.toString = SparkleMem_combo_4_8` is impossible: every candidate rendering of a five-component name contains `.` | TRUE; decided over `cands` |
| `hparent` | `cnt` / `seqMem` differ in the last component (`sep`); `SparkleMem_combo_4_8` is no candidate of `seqMem` | TRUE; decided |
| `hfresh` | the parent's output names must not start with `i` — the name of the scalar result was NOT read; logged by the test's first command, which throws if it starts with `i` | NOT READ; decided (`seqMem_outHead`) |
| `hparentD` | `seqMem.toString ∉ []`, `∉ [SparkleMem_combo_4_8]` | TRUE; decided |
| `hdisjD` | (`cnt`, memory): `cnt.toString ∉ [SparkleMem_combo_4_8]`, `∀ x ∈ []`; (memory, `cnt`): `∉ []` twice; equal callees: the antecedent is false | TRUE — no shared descendant |
| `halias` | `aliasOk` (`Tools/ShippingMachineClosesData.lean` 129–136): a `let` that is a variable at a position `< nIn + slots` passes; `en`, `wa`, `wd` are declaration inputs | TRUE by reading; decided (`seqMem_alias`) — never evaluated before for `seqMem` |
| `hC`, `hslots`, `hdomB`, `hfne` | decided in the BUILT `NoPortsMemSeqMemTest` 254–257 | BUILT |

No hypothesis is known false. The two not established by reading alone are
`hfresh` (the output's name) and the exact entry data behind the decided
ones; each is a separate small theorem, so a failure names itself.

## 4. Endpoint — premise — predicted state

| endpoint | premise | predicted state |
|---|---|---|
| `seqMem.machine_design_noPortsR0_closed` (new) | `MachineClosesAt seqMem` (binder of `…_noPortsR0`, NOT ALLOWED) | WRITTEN, NOT BUILT — predicted absent |
| | binder `MachineDefines … cnt cnt.machineData.shape` | ADDED (allowed) |
| | the run, `MachineDefines seqMem`, antecedent `ChildBnd ∧ MachineDefines cnt` | stay |
| `…_closedB` | — | predicted NOT generated: the one antecedent is ALLOWED already (`verification-b13.md` 87) and `#machine_boundary_close` reduces not-allowed antecedents only, throwing when nothing changes (`Tools/ShippingBoundaryClose.lean` 140–143, 213–214). The test uses `#machine_boundary_close_try` and logs the line |
| `…_closed_gap` | gap hypotheses | predicted none; 0 NOT ALLOWED |
| `seqMem.machine_design_noPortsR0` (open) | unchanged | — |
| the five memory-only parents | their closing | NOT done here: M1 / M2 apply (all entries memory kids, `hkid` by `memKid_iface`), but their endpoints have no `MachineClosesAt` binder to replace (worker B's unit) |

## 5. Left open

* Callees that share a descendant AND a memory entry: `closes_of_agree`
  (`Tools/ShippingCallsKidsS.lean` 115) keeps `hnomem`. Its generalisation
  is `closeInstsG_of_kidsP` with `hcross` taken from the end cache for two
  REAL entries and from names for a pair with a memory entry (a memory child
  is not in the cache; `closeInstsGM_run_allF`'s clause `hfin` is false of
  it). Not written; the missing statement is
  `closeInstsGM_run_allMF`: M1 plus `∀ k hk, memChild? (insts[k]).1 = none →
  ∃ y, children[k]? = some y ∧ (L.val w').get? (insts[k]).1 = some y`.
* A generator (`#machine_closes_at` refuses a memory child,
  `Tools/ShippingMachineClosesAtGenG.lean` 33–34): the test is by hand.
* Depth ≥ 1 with a memory child: unchanged (B-memkids §5.3).

## 6. Build queue (integrator)

`lakefile.lean`:

    lean_lib «Tools.ShippingMemClosesRun» where
      roots := #[`Tools.ShippingMemClosesRun]

    lean_lib «Tools.ShippingMemClosesKids» where
      roots := #[`Tools.ShippingMemClosesKids]

`Tests/AllTests.lean`:

    import Tests.Compiler.NoPortsMemSeqMemClosedTest

Order: (1) `Tools.ShippingMemClosesRun` (imports `ShippingCallsRunG`,
`ShippingMemKidCore`); (2) `Tools.ShippingMemClosesKids` (imports 1,
`ShippingCallsKidsD`, `ShippingMemKidFacts`); (3)
`Tests.Compiler.NoPortsMemSeqMemClosedTest` (imports 2,
`NoPortsMemSeqMemTest`, `ShippingBoundaryClose`, `ShippingNameSep`). (1)
alone is usable (M1).

## 7. UNVERIFIED, in risk order

1. `isMemModule_memModule` — a `simp` unfolding `isMemModule`, `memModule`,
   `portKey` with symbolic widths (`decide (x = x)`, the body `match`); a
   second alternative splits the read kind.
2. The test's kernel decisions: `cnt_notin` / `seqMem_notin` (`cands` of a
   five-component name against the evaluated module name — `Nat.repr` in the
   kernel), `seqMem_alias`, `seqMem_argsN` / `_fieldOut` / `_fieldsNd`
   (`if c = cnt` on `Name`, `calleeAt`), `seqMem_outHead` (the output name).
3. `closeLast` (the last binder of `…_noPortsR0` is the closing: read off
   `generateR0`, `xs[10]`); the audit's count of 3 proposition binders;
   `#machine_goal_gap_of` on the closed form.
4. `mapM_loop_allM`, the pairing clause for a table key (`hget` at `j`,
   `key xs[j] = key x` from `(xs.map key)[j]?`); the per-element lambda of
   M1 (`cases hmc : memChild? c` abstracting the goal, as
   `closeInstsGM_run` does).
5. `memSelf_of` (`show` through the `match` on `some (cb, aw, dw)`);
   `memIface` (`simp [mem_inPorts]` for the count, `congrArg` projections);
   `closeInstsG_of_kidsP` (the `rw` chains in `hconsV`);
   `_root_.Tools.ShippingCallsKidsD.ChildIfaceD.toP` declared from another
   namespace; `machineClosesAt_of_kidsD_fromM` (`show` over the beta-reduced
   `nameK`).
