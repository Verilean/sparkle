# M4 lead: route census and the first independent route unit — freeze rev1 (FOR REVIEW)

- **Issue:** `sparkle-gen4-routes`.
- **Plan:** LEAD_UNITS_PLAN.md (cf029631).
- **Status:** read-only survey, no Lean. All file:line references are at par/gen2-spec cf029631.

## 1. Every successful path (dispatch `synthesizeFromConst`, Sparkle/Compiler/Elab.lean:5288-5414; constant from `entryConst` :5271-5282)
| # | route | condition / function | soundness family today |
|---|---|---|---|
| 1 | first gate | `certifiedShape? = some` (:5292), `synthesizeCertified` (:2934); off in symbolic mode or with parameters (:2319) | top: `synthesizeCombinationalCore_sound` / `CertifiedOutcome` (EntrySoundness:1117). Child facts (FirstGateChild*, FirstGateKid*) are marked WRITTEN, NOT BUILT |
| 2 | mixed gate (also instance roots) | `mixedCertifiedShape? = some` (:5299), `synthesizeMixedCertified` (:2959) | `GateDefines` (GateDefines:72). Leaf child: `gate_child_fullG` → `ChildFn` (EntryReadsLinked:345), `childFull_of_realA` (CallsGateA:48), `gateChild_ifaceP_of_real` (GateChildIfaceP:174). Gate parents: `gate_parent_run` (GateParentRun:191) on the old `RefLaws`; the G-variants are NOT BUILT |
| 3 | machine | `machineShape? = some` and `synthesizeMachineCertified = some` (:5252-5313) | `MachineTaken`, `machine_ships_hierC_noHstR`, `machine_linkedT_callsServed`, the gen2 `Pkg`/`ChildShips`/`TopShips` |
| 3m | memory child inside route 3 | `closeInstsGM`, `o.child? = some md` (:5236-5239) | `MemDec`/`MemFacts` |
| 4 | machine read, synthesis refused | `closeLets = none` (:5263), or `closeInsts*M = none` (:5209, :5234); falls through to route 5/6 | only excluded by `MachineClosesAtA` (`T1Hyp.closes`) |
| 5 | memo `sparkleSubModuleCache` | not symbolic, and cached (:5334-5338) | `MemoInv`/`KeepsMemo`/`MemoSound` (MemoInv:44, :130, :209); G-MEMO open |
| 6 | legacy | other `defnInfo` (:5340-5412) | `legacy_translate_contract` (LegacySemContract:264, :327): a CONTRACT only (gap G2) |
| 7 | parametric | `synthesizeCombinationalWithParameters` (:8940), symbolic mode | none found. The top is always route 6; its children go through `synthesizeChild` and can take any route |
| 8 | child-cache hit | `synthesizeChild` (:8929-8933) | `RealChildA`/`CacheInvA`, `CacheShips` |

Every non-memory child, whatever the parent's route, is a route-8 result of the full entry (`childSynthEntry`, :8706-8730).

## 2. What the current interface (`Pkg`, A-COMB `ChildShips`, `TopShips`, `T1Hyp`) can express
- **Expressible:** route 3, 3m (through `MemDec`) and 8, for reached machine names.
- **Not expressible:**
  - **Routes 1 and 2** have no `MachineData`/`GenFacts`.
    - `T1Hyp.defines` (Defs:192) requires `MachineDefines`, which requires `certifiedShape? = none ∧ mixedCertifiedShape? = none` (MachineEntry:2345-2357).
    - `T1Hyp.closed` (:203-205) puts every non-memory callee into `Reach`. So under the current `T1Hyp`, a machine parent with a gate child cannot satisfy the hypotheses.
    - **FG is not narrowed by this.** T1 is the M3 deliverable and is explicitly not FG. The coverage obligation is M4.
    - A gate child is always one output `"out"`, assignment-only, with an empty design (`ChildFull`, GateChildComb:165-170). So its interface is `CombChildRunN` with `outsC = [out]`, never `SeqChildRunN`.
  - **Route 4** results are route 5/6 modules; `T1Hyp.closes` removes them from `Reach`.
  - **Route 5** needs a `MemoInv` with a ships-like `Φ`, and so a package for every route that writes the memo (1, 2, 3, 6).
  - **Routes 6 and 7** have no trace and no package; there is a contract only.

## 3. Blocking order for FG (earliest first)
1. Route 2 gate leaf children of machine parents (the G-ONEOUT parents): the S4 consumer exists, but nothing supplies `ChildShips` for these children.
2. Route 1 children: the same consumer; the child facts are NOT BUILT.
3. Route 6 (and route 4 into it): a contract only, which is M4's risk clause.
4. Route 5 (memo): after 1-3.
5. Gate tops (routes 1/2 `TopShips`).
6. Gate parents with instances (old `RefLaws`; G-variants NOT BUILT).
7. Route 7 (parametric).

## 4. Interface finding for M2 (G-ONEOUT; not yet checked in the kernel)
- **The mismatch.** `CallDec` (Defs:102) requires a callee output `o` with `o.name = p.d.shape.instFields.getD k ""`. For a one-output parent (`instFields = []`) that is `""`, but every one-output callee's output is named `"out"`: `instStmt` connects the single `outP`, and gate children's output is `"out"`.
- **The consequence.** If confirmed, `CallDec` as written is unsatisfiable for G-ONEOUT calls, and S4's consumer could not be fed from `CallDec`.
- **Next step.** Check this in the S4 consumer freeze before it is used. The fix would be either a field-name rule for one-output parents (the callee's single output) or a separate one-output decoding. Either is a definition amendment, to be reviewed.

## 5. First independent route unit (proposal): gate leaf child → `CombChildRunN`
It is run level, with no `Pkg` change.
```lean
noncomputable def gateS (bs : List (Name × MixedGateBinder)) {srt : SType} (e : Term srt)
    (bpos vpos : Nat → Nat) : (Nat → List Nat) → List (Nat → Nat) :=
  fun vals => [fun τ => (pack srt (eval (fun j => decB bs (vals τ) (bpos j))
                                    (fun j w => decV bs (vals τ) (vpos j) w) e)).toNat]

theorem gate_combChildRunN (O : RefLawsAOps MkRefd mref cref) {c : Name} {y : Res}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)} {kb kv : Nat} {vw bpos vpos : Nat → Nat}
    {srt : SType} {e : Term srt}
    (entry : EntryDefines mctx mref cctx cref c value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    (h : RealChildA O c y) :
    y.2.modules = [] ∧ ∃ o : OutField, o.name = "out" ∧ y.1.outputs = [{ name := o.name, ty := o.ty }] ∧
      ∀ (dsn : Design) (n : Nat),
        CombChildRunN (childMap dsn.modules) dsn n y.1 bs [o] (gateS bs e bpos vpos)
```
- **Its premises** are those of the existing `childFull_of_realA` / `#gate_child`.
- **Suppliers:**
  - `childFull_of_realA` (CallsGateA:48): assigns, `readsClosedB`, the `out` output, distinct allocated inputs, port types, `modules = []`;
  - `not_alloc_clk`/`not_alloc_rst`/`not_alloc_out` (GateChildIfaceP:78-90);
  - `ChildFull.tys` + `inPortsOf_of_alloc` (:98), for the `argPorts` length;
  - `RealChildA.run` + `gate_child_fullG` (EntryReadsLinked:345): `ChildFn` at `env "rst" = 0`;
  - S1 `runModule_seed_local` (Gen2Comb:28): reset is irrelevant (`"rst"` ∉ inputs, closed);
  - `runModule_assigns_total` (GateDesign:92), `RunOn_instFree`, `instFree_of_assigns`: run existence at every `T` and `n`.
- **Acceptance:**
  - a non-vacuous instance: a concrete gate child, `gateS` ≠ `[]`;
  - a round trip with `childFn_of_combRun` (S4-b) that recovers the same function;
  - standard axioms.
- **Not covered:**
  - a `Pkg` constructor or re-keying `ChildShips`/`CallDec` on an interface record (the follow-on unit, after §4);
  - a route-indexed `T1Hyp`;
  - `ShipsRes`/`CacheShips` for gate names;
  - route-1 children, gate tops, gate parents with instances;
  - repeated callees (`hnodup` in `callsPureA_of_gateKids`, CallsGateA:65);
  - routes 4-7.
- **The plan change it implies, proposed for M3/M4 only, not applied.** `T1Hyp`'s `Reach`/`defines`/`closed` must become route-indexed, so that gate children are reached without `MachineDefines`. The M3 freeze (`sparkle-gen3-induct`) must anticipate this; a route-indexed `T1Hyp` is an amendment, reviewed before use.
