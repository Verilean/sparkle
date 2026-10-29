# TopShips contract revision — rev0 (FOR REVIEW — design only; NOTHING APPLIED, nothing built or proved)

- **Issue:** `sparkle-gen2-top-contract`, the `TopShips` specification repair. It is a dependency of T1 assembly.
- **Purpose:** to carry a MEANINGFUL slotless top guarantee to the final root. The repair restores content that the
  current text loses for clock-free modules; it is not a weaker guarantee.
- **What stays unchanged:** shared definitions (`Tools/ShippingGen2Defs.lean`, `scripts/gen2/GEN2_DEFS.lean.txt`),
  FG, `T1Hyp` and the compiler. This file is the revision table that S4_WID_SUPPLY.md §4.1 requires before any shared
  change, in the same format.
- **Bases (every `file:line` is at these SHAs):**
  - `par/gen2-spec` at **db76dd89**. `Tools/` and `Tests/Gen2/` are unchanged since 1b840215 for every file cited
    (`git diff --stat 1b840215..db76dd89` touches only `Tools/ShippingGen3*`, `Tests/Gen3/*`, `lakefile.lean`,
    `scripts/`).
  - `par/gen3-induct` at **96cbd548** (worktree /home/junji-hashimoto/git/.kjob/gen3-induct), marked [G3].
  - `par/gen4-gate` at **b3a72c91** (worktree /home/junji-hashimoto/git/.kjob/gen4-gate), marked [G4].
- **Origin:** S5_SLOTLESS_FREEZE.md rev1 §2.4 and D1 (reviewer-confirmed on fd55bcfc).

## 1. The defect (as read)
- `TopShips` (Defs:273-295) has one antecedent line (Defs:283) with two premises:
  `(∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0)`.
- `seedIn m ins t st n = if n ∈ m.inputs then ins t n else st n` (Tools/ShippingSeqOptSoundness.lean:892-894).
- So when `"clk"` ∉ `b.inputs.map (·.name)`, the clk premise says `∀ st, st "clk" = 0`, which is false at
  `st := fun _ => 1`. The INNER guarantee (`∀ i bools bits T ins st0 mems kids, … → ∃ envsO …`, Defs:278-295) then
  holds for every `ids`/`cache`/`regs`. Only the OUTER existence (Defs:274-277: `ids.Nodup`, lengths, `regs.Nodup`)
  carries information.
- Kernel statement: `topShipsInner_of_noClk` and `topShips_iff_outer_of_noClk` in
  Tools/ShippingGen2TopVacuity.lean:83, :92. That file is untracked, by another agent, "WRITTEN, NOT BUILT" (:7).
- When `"clk"` ∈ `b.inputs`, the clk premise reads `ins t "clk" = 0`. It is satisfiable, and the guarantee is
  meaningful.
- **Which modules lack clk.** For machine-route modules, the wiring adds clk/rst only when `slots ≠ []`
  (`MachineWired`, Tools/ShippingMachineEntry.lean:654; input clause :742, :747). It also adds them for parents of
  clocked children (`withClockFor`, Tools/ShippingMachineInstG.lean:73-78). So the no-clk modules are:
  - slotless leaves;
  - slotless parents of comb children (S5 case C).

## 2. Proposed replacement (candidates)
**R-G (recommended): guard both premises on the module's actual inputs.** Only Defs:283 changes; every other line
is verbatim:
```lean
      ("rst" ∈ b.inputs.map (·.name) → ∀ t, ins t "rst" = 0) →
      ("clk" ∈ b.inputs.map (·.name) → ∀ t, ins t "clk" = 0) →
```
- With both inputs present, R-G is the old text up to `seedIn` unfolding (§3, L2).
- With neither present, both guards are discharged by non-membership, and R-G is `TopShipsNC` (S5 rev1 C2) (§3, L4).
  So R-G is "`TopShipsNC` merged" for clock-free modules and "the old contract" for clocked ones.

**R-C: guard clk only; keep rst unguarded.**
- It is also implied by `TopShipsNC` (an unguarded rst antecedent only weakens the statement).
- But for a module without rst it still restricts an input stream entry that no port reads. Not recommended, for
  uniformity with C2.

**R-N: delete both premises (= `TopShipsNC` in Defs).**
- This is the strongest candidate. Every clocked producer would then have to prove its run without `ins t "rst" = 0`.
- Consumer 1 needs `seed t st "rst" = 0` and `seed t st "clk" = 0` for `H` (`ComposedNWRegsF`, FitChain:698;
  use :1184-1189). TG-level reset irrelevance exists only for clock-free bodies (S5 A2 `NoTouchZ`, which excludes
  any read of rst).
- Not recommended. It is not refuted either: it stays an open stronger target.

## 3. Directions (lemmas to prove in the supply unit U-TOP-DEF; none is proved yet)
Write `TopShipsR` for R-G during the transition. `TopShipsNC` is S5 rev1 C2.

| # | lemma | statement | hypotheses | proof idea |
|---|---|---|---|---|
| L1 | `topShips_of_R` | `TopShipsR … → TopShips …` (new ⇒ old) | none | same witnesses. The old antecedents imply the guarded ones: rst trivially; clk through `seedIn` unfolding (SeqOptSoundness:892-894) when `"clk"` ∈ inputs |
| L2 | `topShipsR_of_old` | `TopShips … → TopShipsR …` (old ⇒ new) | `"rst" ∈ b.inputs.map (·.name)`, `"clk" ∈ b.inputs.map (·.name)` | same witnesses. The guarded premises plus membership give Defs:283 (`seedIn` unfolds to `ins t "clk"`) |
| L3 | `topShipsR_of_NC` | `TopShipsNC … → TopShipsR …` | none | drop two antecedents |
| L4 | `topShipsNC_of_R` | `TopShipsR … → TopShipsNC …` | `"rst" ∉ …`, `"clk" ∉ …` | supply both guards by `fun h => absurd h hn` (a guard's own hypothesis, not an execution premise) |

- **Not claimed:** old ⇒ new when `"clk"` ∉ `b.inputs`. It is neither proved nor refuted, and no counterexample is
  exhibited. By §1, it would mean deriving the execution guarantee from the outer existence alone.
- Mixed membership (rst without clk, or the reverse) is not covered by L2/L4. A1 of S5 (`calls_ports_sl`, both or
  neither) and MachineEntry:742 exclude it on the raw module of a machine-route run, but this is not a lemma about
  `b` yet.

## 4. REVISION TABLE (required before changing shared `TopShips`; nothing applied)
| change | old ↔ new | downstream users (every one; grep `\bTopShips\b` over Tools/, Tests/, scripts/ of all three worktrees) | supply unit | final-FG obligation |
|---|---|---|---|---|
| **`TopShips` Defs:283 → R-G** (doc :268-272 updated: "the conclusion of `machine_ships_hierC_noHstR` with the rst/clk premises guarded on the inputs") | L1 always (new ⇒ old). L2 under both memberships. Old ⇒ new without clk membership NOT claimed (§3) | the definition: Tools/ShippingGen2Defs.lean:273-295; [G3] same lines :273-295 (the two Defs differ only in `CallField`, which gen2-spec has at Defs:92-109 and [G3] lacks, and in `InstClosed`/`ShipsRes`, [G3] :127-136); [G4] :266-288 | U-TOP-DEF: the def, L1-L4 (new file `Tools/ShippingGen2TopContract.lean`, importing Defs and the S5 C2 file, or C2 moved there) | the final root must be stated over the revised `TopShips` (rows below) |
| text copy | must change in the same commit | scripts/gen2/GEN2_DEFS.lean.txt:273 (cmp-identical to Defs on gen2-spec, checked: `cmp` exit 0); [G4] :266 (cmp-identical); [G3] :266. On [G3] the copy is NOT cmp-identical to Defs today (first difference line 127 = `InstClosed`); this pre-existing drift is reported, not caused here | U-TOP-DEF | — |
| statements with `TopShips` in the CONCLUSION: `StepStmt` (Defs:313), `MemParentStmt` (:329), `LeafStmt` (:341), `T1Stmt` (:355); [G3] same lines; [G4] :306, :322, :334, :348; [G3] `StepStmtOld` Tools/ShippingGen2PostFacts.lean:82-95 | text unchanged. The meaning is strengthened: new statement ⇒ old by L1 under the conclusion. The converse is not claimed | [G3] `stepStmt_of_old` PostFacts:118 (both sides read the same `TopShips`: unchanged); [G3] `t1_of_stepPF` Tools/ShippingGen2T1.lean:225-246 passes `hTop` through (:244-246: unchanged text, re-elaborate); `ihAt_stepPF` T1:163-190 drops `TopShips` (`⟨n, -, hCS⟩` :189: unaffected); `t1_of_stepPF'` :251-254; [G3] `t1_of_stepPF_kc` KeepChild.lean:374-380 | re-elaborate only | `T1Stmt` and FG (scripts/gen2/GENERAL_SPEC.md:88-93, which concludes `TopShips`) must be the revised meaning. Proving the current `T1Stmt` for a reached slotless declaration says nothing about its runs (§1) |
| producer: register leaf `leaf_topShips_of_LB` (Tools/ShippingGen2Leaf.lean:150-158), feeding `LeafStmt'` (:53-63) and `leaf_ships` (:271); [G3]/[G4] same file and lines | the statement is equivalent by L1/L2. `slots ≠ []` gives `"clk"` ∈ raw inputs (MachineWired clause, MachineEntry:698), and `"rst"` comes from `hrstIn` (Leaf:162, :174). The meaning is UNAFFECTED | the proof ignores the clk binder (`_` in the `intro`, Leaf:165). rst is used (:179, :202). New proof: the same `intro`, with `hrstZ := guard hrstR` | U-TOP-PROD (re-intro, ~5 lines) | — |
| producer: memory parent `memParent_topShips` (Tools/ShippingGen2MemTop.lean:45-57, `hsl ≠ []` :49; the consumer-1 `key` :84 has the old shape); `memParent_ships` (MemShips:87), `MemParentStmt'` (MemParent:57-69); [G3]/[G4] same | the meaning is UNAFFECTED (clk and rst both inputs: MachineEntry:698; `RunFacts.rst`, GuardsSound:320) | wrap: `topShipsR_of_old hrst hclk key`. Needs `"clk"` ∈ `b.inputs`: MachineEntry:698 on the run's `wired`, then `b.inputs = raw.inputs` (as FitChain:1168-1174) | U-TOP-CLKIN (lemma `clk_in_b_of_slots`: `slots ≠ []` → `"clk"` ∈ `b.inputs`, from `wired` + `hpost`), then U-TOP-PROD | — |
| producers: one-output parents `oneOut_topShips` (Tools/ShippingGen2OneOutTop.lean:340-357, `hsl` :345); `oneOut_topShipsO` (OneOutTopO:334-351, `hsl` :339, `key` :402-415); `oneOut_topShipsO_of_row` (Tests/Gen2/PMem4Check.lean:494-510) | UNAFFECTED (`hsl ≠ []`) | wrap with L2, as for MemTop | U-TOP-CLKIN, U-TOP-PROD | — |
| producer: slotless leaf `slotlessLeaf_topShips_of_LB` (Tools/ShippingGen2SlotlessLeaf.lean:180-191); `SlotlessLeafStmt` (:425-435); `slotlessLeaf_ships` (:438); not on [G3]/[G4] (grep) | **AFFECTED: today's statement is vacuous in its inner part.** The leaf has no clk (insts = [], slots = []; inputs allocated, `slotless_inputs_alloc_ofRun` :397). The new statement is strictly informative | the proof uses `hrstZ` (:202, through `sll_seedZ_rst` :209) and ignores clk. Under R-G, rst is guarded and `"rst"` ∉ `b.inputs`, so the seed fact must come from non-membership (`sllSeedZ` :67-68 already zeroes the state at rst) | **U-TOP-S2**: prove `TopShipsNC` for the slotless leaf from the run (S2-NC), then L3 | the slotless-leaf case of the final root depends on U-TOP-S2 |
| producer (planned, unbuilt): S5 C5a `oneOutSl_topShipsNC`, C5S, C5 (S5_SLOTLESS_FREEZE.md rev1 §5) | C5a ⇒ R-G by L3. C5S ⇒ R-G by L2 (A1 gives both memberships). C5's case-C branch (`topShips_of_NC`) is then replaced by L3 | the S5 stage-C file | U-TOP-S5 (C5 restated as `TopShipsR`; C5a unchanged) | the one-output slotless parent case of the final root depends on U-TOP-S5 |
| compat: `Old.TopShips` (Tests/Gen2/PkgCompat.lean:137); `rfl` pin `TopShips (.gen p) … = Old.TopShips p …` (:252-253); [G3] :134, :251; [G4] :134, :251 | **the `rfl` BREAKS.** `Old` is a frozen pre-Pkg copy and stays unchanged. The pin becomes two lemmas: L1 transported (new ⇒ Old) and L2 transported (Old ⇒ new under both memberships) | `t1Stmt_compat` (:428-431: `T1Stmt (lift) → Old.T1Stmt`, `TopShips` positive): holds via L1. `memParentStmt'_gen` (:372-389), `memParentStmt_gen` (:391-408), `leafStmt_gen` (:410-426): Old ⇒ new transports of a conclusion. They need L2 plus the memberships (from U-TOP-CLKIN on the run they quantify over), or are re-derived positively from the new producers (as UCHILD_PORTTYS_TABLE.md row C6' proposes). [G3] :364, :383, :401; [G4] :355, :374, :392 | U-TOP-COMPAT | — |
| instances (`TopShips` stated through the theorems): Tests/Gen2/LeafInstance.lean:67, MemParentInstance.lean:55, QuantInstance.lean:136 (`q_ships` :125, via `memParent_ships`), SlotlessLeafInstance.lean:57 (`pbh_ships` :45); [G3]/[G4]: LeafInstance:67, MemParentInstance:55, QuantInstance:136 | the text is unchanged. `pbh_ships` gains execution content (after U-TOP-S2); the others keep theirs | re-build only | — | `pbh_ships` is the first real declaration whose top guarantee becomes non-vacuous |
| consumer-1 originals with the old binder in their conclusion: `machine_ships_hierC_noHstR` (Tools/ShippingSrm33Core.lean:24, doc :85-114); `machine_ships_hierC_run` (FitChain:1073-1232, binder :1145) | NOT changed (not `TopShips` users; their conclusions are defeq to the old `TopShips`) | used only through the producers above, which add L2 | — | — |
| vacuity file Tools/ShippingGen2TopVacuity.lean (`TopShipsInner` :52, `topShips_iff_inner` :74, `topShips_iff_outer_of_noClk` :92; untracked, not built) | it states facts about the OLD text. After the change, keep it pinned to a frozen `TopShipsOld` copy (as the history record), and add the positive control P-TOP (below) | that file's owner | U-TOP-CTRL | — |
| docs that quote `TopShips` (scripts/gen2/: GENERAL_SPEC.md (:79 "unchanged `TopShips` from both branches (S3-S5)", :93, :118), STEP_IFACE_FREEZE.md (:57), T1_CONNECT_FREEZE.md, LEAF_FREEZE.md, MEMPARENT_FREEZE.md, MEMPARENT_RESULT.md, LOOPPKG_FREEZE.md, LOOPPKG_RESULT.md, S3_GROUP_FREEZE.md, S4_CONSUMER_FREEZE.md, S4_FIT_FREEZE.md, S4_STAGEA_RESULT.md, S4_STAGEB_FREEZE.md, S4_STAGEB_RESULT.md, STEP_S2C_FREEZE.md, STEP_S2_CLOSED_REPORT.md, ROUTE_CENSUS.md, S5_SLOTLESS_FREEZE.md; scripts/gen3/UCHILD_PORTTYS_TABLE.md) | add a dated note. The GENERAL_SPEC:79 sentence is inaccurate for case (C) and gets a correction note. History entries stay | — | doc | — |

**Controls of U-TOP-CTRL (acceptance of the shared change):**
- **P-TOP (positive, required).** A concrete clock-free module with every R-G antecedent inhabited and the
  conclusion used. S5 rev1 §7 P3-core is reused, restated over `TopShipsR`, together with the `pbh_ships`
  instance after U-TOP-S2.
- **N-TOP.** At the same module, the OLD Defs:283 clk antecedent is refuted (`not_seedIn_clk_zero`, TopVacuity:45).
  The new guarded antecedent is proved there (by non-membership).
- **E-TOP.** For a clocked module (the `leaf16Pkg` instance, LeafInstance:67): L1 and L2 instantiated. This shows that
  the clocked contract is unchanged.

## 5. Final-FG obligation (what must reach the root)
- **The root.** `T1Stmt` (Defs:347-355) and FG (GENERAL_SPEC:88-93) conclude `∃ q n, P c = some q ∧ TopShips q n c b
  raw D`. After U-TOP-DEF this is R-G. For every reached clock-free declaration it then states the execution
  guarantee; today it states only the outer existence.
- **No back door.** A proof of the root must not obtain a clock-free case through `topShips_of_NC` into the OLD
  text. Audit: the closure of the T1 proof must not contain `topShips_of_NC` once U-TOP-DEF lands; it is then deleted
  or kept only beside `TopShipsOld`.
- **Classes and their suppliers:**
  - register leaf: U-TOP-PROD;
  - memory parent: U-TOP-CLKIN + U-TOP-PROD;
  - one-output parent with slots: U-TOP-CLKIN + U-TOP-PROD;
  - slotless leaf: U-TOP-S2;
  - one-output slotless parent: U-TOP-S5;
  - group slotless parent: **RESIDUAL**. S5 D3 keeps it open, blocked with group parents with slots
    (S3_GROUP_FREEZE §5 :364). Coverage stays INCOMPLETE until it is supplied and a real slotless package exists
    (S5 D4).

## 6. Order relative to the other shared edits
- **`InstClosed` (G-POST).** Applied on [G3] at 28476add: `InstClosed` is the third `ShipsRes` conjunct ([G3]
  Defs:127-136). It is not in gen2-spec or [G4].
  - It edits a different definition, so it commutes with R-G semantically.
  - It does touch the same files: Defs, GEN2_DEFS copy, PkgCompat ([G3] PkgCompat lifts take explicit
    `InstClosed`).
  - **Order:** integrate `InstClosed` FIRST (it already exists as a commit), and resolve the [G3] GEN2_DEFS drift
    (§4 row 2) there. Then apply R-G on top, so the copy check is `cmp`-exact once.
- **`ChildShips` (U-CHILD-PORTTYS, `ChildPortWidths`).** It is planned and NOT applied
  (scripts/gen3/UCHILD_PORTTYS_TABLE.md:3-4, §3).
  - It edits `ChildShips`, R-G edits `TopShips`. Statements carrying both
    (`StepStmt`/`MemParentStmt`/`LeafStmt` conclusions `TopShips ∧ ChildShips`) change in independent conjuncts. So
    the two commute semantically.
  - Shared touch points: the producers Leaf, MemShips/MemTop, OneOut/OneOutTop(O), and the PkgCompat compat
    lemmas (:372-426).
  - **Order (recommended):** R-G BEFORE `ChildPortWidths`.
    - R-G is needed for the T1 assembly to carry meaning.
    - Its producer changes are pure wrappers (L2) plus one lemma (U-TOP-CLKIN). `ChildPortWidths` needs new
      producer lemmas (N-A/N-B).
  - Either order is acceptable if the two are never in flight in the same files at once: one commit each, each with
    the `cmp` check of the GEN2_DEFS copy and the re-elaboration of PkgCompat.
- **Sequence:** `InstClosed` (integrate) → U-TOP-DEF + U-TOP-CLKIN + U-TOP-PROD + U-TOP-COMPAT + U-TOP-CTRL (one
  shared commit) → U-TOP-S2, U-TOP-S5 (supplier commits) → `ChildPortWidths`.

## 7. Not claimed
- That R-N is false or unattainable.
- That old ⇒ new holds for clock-free modules.
- That any real slotless parent package exists.
- That the group slotless top is covered.
- Nothing here is built. Shared definitions are unchanged.
