# U-TOP-CTRL freeze — P-TOP, N-TOP, E-TOP and the history pin (rev0; DOCS ONLY; no Lean written for this unit)

- **Issue:** `sparkle-gen2-top-contract` (S2). Unit order: TOP_CONTRACT_REVISION.md rev1.1 note 2: NC suppliers and L1-L4 → U-TOP-DEF → U-TOP-CLKIN/U-TOP-PROD → U-TOP-COMPAT → **U-TOP-CTRL** (this file).
- **Base:** branch `kjob/g2tc-s2` at 21342039 (U-TOP-DEF/PROD/COMPAT committed; its clean build is the coder's, so everything below that
  mentions `TopShips` (R-G) as a *built* fact waits for that evidence). Names used here exist at 21342039 (listed in §1).
- **No Lean is written for U-TOP-CTRL before this freeze is approved.** New Lean goes to NEW files (`Tests/Gen2/TopCtrlCheck.lean`, plus
  its `lean_lib`); nothing in Defs/T1Hyp/T1HypND/Elab is edited; no new TRUSTED boundary, no law, no FG change.
- **Not claimed anywhere below:** that the group slotless top or D4 is covered; that old ⇒ new holds without the clk membership; that a
  pure control exists for P-TOP (§3 says what is and is not found).

## 1. Names at 21342039 (all in namespace `Tools.ShippingGen2` unless noted)
| name | statement (informal) | file |
|---|---|---|
| `TopShips` | R-G: `rst`/`clk` premises guarded by input membership | Tools/ShippingGen2Defs.lean:280 |
| `TopShipsOld` | the pre-R-G text, every line but the rst/clk line verbatim | Tools/ShippingGen2TopContract.lean |
| `TopShipsNC` | rst/clk premises deleted (S5 C2) | Tools/ShippingGen2TopNC.lean |
| `topShips_toOld` (L1) | `TopShips → TopShipsOld`, no hypothesis | TopContract |
| `topShips_ofOld` (L2) | `TopShipsOld → TopShips` given `"rst" ∈` and `"clk" ∈ b.inputs.map (·.name)` | TopContract |
| `topShips_ofOld_wired` | L2 with both memberships from `MachineWired` + `slots ≠ []` + `hpost` | TopContract |
| `topShips_of_NC` (L3) | `TopShipsNC → TopShips`, no hypothesis | TopNC |
| `topShipsNC_of_topShips` (L4) | `TopShips → TopShipsNC` given `"rst" ∉` and `"clk" ∉` inputs | TopNC |
| `topShipsOld_of_NC` | `TopShipsNC → TopShipsOld`: PROJECTION ONLY (inner part vacuous without clk) | TopNC |
| `machineWired_clk_rst_in`, `clk_rst_in_b_of_wired`, `b_inputs_of_hpost` | U-TOP-CLKIN | Tools/ShippingGen2TopClkIn.lean |
| `topShipsOld_iff_inner`, `topShipsOld_iff_outer_of_noClk`, `topShipsInner_of_noClk`, `not_seedIn_clk_zero` | D1 vacuity of the OLD text | Tools/ShippingGen2TopVacuity.lean |
| `slotlessLeaf_topShips_of_LB`, `slotlessLeaf_ships` | R-G for the slotless leaf; premise-free in rst/clk | SlotlessLeaf |
| `slotlessLeaf_topShipsNC(_of_LB)`, `slotlessLeaf_topShips_of_NC` | the NC supplier and L3 of it | TopNC |
| `Tests.Gen2.TopNCControl.{m0,d0,ins0,kids0,s0,p3_*}` | P3-core (A2 only) at a clock-free module | Tests/Gen2/TopNCCheck.lean |
| `Tests.Gen2.LeafInstance.leaf16_ships`, `Tests.Gen2.SlotlessLeafInstance.pbh_ships` | conditional instances (run premises stay hypotheses) | Tests/Gen2/*Instance.lean |

## 2. History pin (statements already built against the old text; this unit only adds the freeze check)
`TopShipsOld` is pinned to the frozen `Old.TopShips` of `Tests/Gen2/PkgCompat.lean` by
`example (p : SrcPkg ι dom) (n c b raw D) : TopShipsOld (.gen p) n c b raw D = Old.TopShips p n c b raw D := rfl`
(committed in PkgCompat). U-TOP-CTRL adds, in `Tests/Gen2/TopCtrlCheck.lean`, **H1** — `checkExpected` of `TopShipsOld`
against an independently written text (that is `ExpTopShipsOld` of TopNCCheck, already built at the NC unit's style) and **H2** — a
check that the closure of the `T1Stmt` proof does not contain `topShips_of_NC`-into-old routes: `topShipsOld_of_NC`, `topShips_toOld`,
`TopShipsOld` are the forbidden constants for any root that is to carry the R-G meaning (the "no back door" audit of
TOP_CONTRACT_REVISION §5; same `ncReach` search with `forb := ncOldForbidden`). The only legitimate users of those constants are
PkgCompat (compat lemmas), TopVacuity, S5Check, TopNCCheck and TopCtrlCheck; H2 states that list as a whitelist **of FILES**, not of
constants, and any other hit fails.

## 3. Controls (complete types)
### N-TOP (negative, executable now): the OLD clk antecedent is refuted at a clock-free module; the guarded one is proved by non-membership
```lean
-- at m0 of Tests.Gen2.TopNCControl (input `a` only)
theorem ntop_old_refuted :
    ¬ (∀ t st, seedIn m0 ins0 t st "clk" = 0)               -- = p3_old_clk_refuted (built)
theorem ntop_guards_hold :
    ("rst" ∈ m0.inputs.map (·.name) → ∀ t, ins0 t "rst" = 0) ∧
    ("clk" ∈ m0.inputs.map (·.name) → ∀ t, ins0 t "clk" = 0) :=
  ⟨fun h => absurd h (by simp [m0]), fun h => absurd h (by simp [m0])⟩
theorem ntop_Old_vs_NC_at_m0 {ι} {dom} (p : Pkg ι dom) (n) (declName) (raw) (D) :
    TopShipsOld p n declName m0 raw D ↔ <the OUTER existence of §D1>     -- topShipsOld_iff_outer_of_noClk m0 (by simp [m0])
```
Reading: at the module without clk the OLD text is exactly its outer existence (built lemma), while the R-G text keeps the inner
guarantee (§P-TOP). Mutant: the guards stated with `∉` swapped (`"rst" ∉ … → …`) is rejected by `checkMutant` (signature/defeq rejection,
not a semantic counterexample).

### E-TOP (clocked module; instance with run premises as hypotheses, as `leaf16_ships`)
```lean
theorem etop_L1 (L : Laws mref cref) … (same binders as leaf16_ships) (n : Nat) :
    TopShipsOld leaf16Pkg n leaf16Pkg.decl b raw D :=
  topShips_toOld _ _ _ _ _ _ (leaf16_ships L … n).1
theorem etop_L2 (L : Laws mref cref) … (same binders as leaf16_ships) (n : Nat)
    (hold : TopShipsOld leaf16Pkg n leaf16Pkg.decl b raw D) :
    TopShips leaf16Pkg n leaf16Pkg.decl b raw D := by
  -- both memberships from the run: trace → `MachineWired` → `clk_rst_in_b_of_wired` (leaf16_slotsNe)
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id (Pkg.trace L.O L.T hA leaf16Pkg ran).toLB
  exact topShips_ofOld_wired _ _ wired leaf16_slotsNe hpost hold
```
These are INSTANCES: their run premises are hypotheses, not evidence that a run exists. They show that the clocked contract is
unchanged (L1 and L2 both instantiate without an extra premise).

### P-TOP (positive; **required by rev1.1 note 1**; the open point of this freeze)
Required content (rev1.1 note 1): a FIXED package; the SAME outer `ids`/`cache`/`regs` witness as the root's `TopShips` (R-G or NC)
conclusion; every execution premise of the inner `∀ i bools bits T ins st0 mems kids …` supplied, **including
`SourceInputs declName (p.d.bsIn.take p.kD) ids cache … (seedIn b ins t st)`**; and the OUTPUT of the root used. Target shape (full type
for review; `Wit` is the extracted outer witness):
```lean
theorem ptop {ι} {dom} (p : Pkg ι dom) (n : Nat) (declName) (b raw : Module) (D : Design)
    (hroot : TopShips p n declName b raw D)               -- OR: TopShipsNC (L3) — the SAME root, not a copy
    (hnoRst : "rst" ∉ b.inputs.map (·.name)) (hnoClk : "clk" ∉ b.inputs.map (·.name)) :
    ∃ ids cache regs, <the witness of hroot> ∧
      ∀ i bools bits T ins st0 mems kids,
        SourceInputs … → (regs passthrough) → (slot inits) → ResetNk n raw D kids → <input fit> → <state fit> →
        ∃ envsO, runModuleTG … = some envsO ∧ envsO.length = T ∧ (∀ j k o f, outs[k]? = some o → (p.src i bools bits)[k]? = some f →
                                                                       (envsO[j]'hj) o.name = f j)
```
For a CONCRETE `p`, `b`, `ins`, `T` the control instantiates the inner telescope at those values and **proves each premise**
(not assumes it), then obtains `envsO` and compares its output with the cross-checked value (as `p3_out`/`p3_cross`, which exist for
A2 only). What this repo has and lacks (a search statement, not an impossibility claim):
- **Found:** `m0`/`d0`/`ins0`/`s0`, the `ResetNk`, input/state-fit, passthrough and slot-init proofs, the A2 run at `slSeedZ` and the
  cross-check of the outputs `[4, 3]` (P3-core, TopNCCheck §3).
- **Not found by this investigation:** a FIXED `Pkg` (with `p.d`, `p.src`, `p.extS`, `p.extBS`, `p.kD`) whose compiled module is `m0`
  (or any module) and for which the `SourceInputs` premise is discharged at concrete `ins`. `pbhPkg` and `leaf16Pkg` are fixed
  packages but their `b`, `raw`, `D`, `ids`, `cache` exist only through a compiler run (hypotheses of `pbh_ships`/`leaf16_ships`).
  `SourceInputs` ties the seed to the source signals through the port names that `ids` and `cache` allocate; for a package with no
  binders in `p.d.bsIn.take p.kD` the premise reads over an empty telescope (not checked here whether it then holds by `trivial`).
- **Candidate routes (to be decided by the review; none is built):**
  - **R1** a synthetic package with an empty binder list whose compiled form is `m0`-like: P-TOP then proves `SourceInputs` over the empty
    telescope, and the output comparison is against `p.src` (to be given). Risk: such a package may not exist as a `Pkg`
    (`GenPkg`/`CombPkg` fields are proofs about a real compilation).
  - **R2** `pbhPkg` with the run premises as hypotheses (the conditional instance, `pbh_ships`) *and* the output of
    `slotlessLeaf_topShipsNC` used at the run's `b`: this is an INSTANCE, not a control (its premises are not supplied); useful as an
    instance row, not as P-TOP.
  - **R3** deliver P-TOP as the conjunction of (a) P3-core (built), (b) an ideal-premise theorem `ptop` above proved ABSTRACTLY from
    `hroot` plus the premises (so the same `hroot` is used and nothing is copied), and (c) R2 as the instance row, and state in
    the result that no fixed package control with all premises supplied was found. This is the fallback if R1 is not available.
- **Acceptance wording** for whichever route is built: "P-TOP is a control only if every premise of the instantiated inner telescope is
  proved for the fixed package; an instance that leaves run premises hypothetical is reported as an instance".

## 4. Build/evidence plan (after approval)
New file `Tests/Gen2/TopCtrlCheck.lean` (+ `lean_lib`), importing TopNCCheck's control definitions only through a shared new file
if needed (no edit of built files except comment headers). Checks: `checkExpected`/`checkMutant` for N-TOP and E-TOP types, H1/H2,
`checkAxioms` standard, no `sorry`. Evidence order: coder's clean build of 21342039 first (U-TOP-DEF/PROD/COMPAT), then this unit.

## 5. Not claimed
Whole-top coverage of the group slotless parent; that the one-output slotless parent case C5 is restated over `TopShips` (that is
U-TOP-S5); that P-TOP exists for a fixed package; final-root (`T1Stmt`) completion.
