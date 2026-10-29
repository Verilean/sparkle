# M2-a `MemParentStmt`: frozen plan (rev1)

Issue `sparkle-gen2-step-mem` (milestone `sparkle-gen2`).
- **Base:** `par/gen2-spec`. Spec d622ad71, U0, CallDec probe and G3-GEN-CALL plan are all approved.
- **Changes:** new proof/test files and lakefile registrations. No production change.
- **Inputs:**
  - a read-only survey of the existing pieces (summarised in §1, file:line at the current head);
  - `GEN2_DEFS` `MemParentStmt` (Tools/ShippingGen2Defs.lean:321).

## 0. Two findings that change the plan
1. **The top needs no closing proof.** `MemParentStmt` already carries `MachineTaken` (= `MachineRunJQC … (dv w + 1)`).
   - `genTrace` (Tools/ShippingQuadComposed.lean:156) takes that run directly, and is generic in `ι`/`dom`.
   - `machineRanA_of_runJQC` (Tools/ShippingRanABridge.lean:38) turns it into `MachineRanA` without
     `MachineClosesAtA`.
   - So `memCallee_closesA` and the `MemCalleeData` kid tables are NOT used. Nor is `outHead`: its only use is
     `instName_ne_of_head` for `hfresh` in the closing proofs (Tools/ShippingCallsGate.lean:60).
   - Consequence: `outHead` is NOT a `MemParentStmt` row. It moves to G-CLOSES (T1Hyp.closes scope, M3/M4). The U0
     obligation "outHead → N1 lemma" is restated there. No N1 lemma covers it today: they separate MODULE names, while
     `hfresh` compares an output port with an instance wire name `inst{gi}_…`. It remains open, and is not dropped.
2. **The H.264 IP tops are NOT in `SrcPkg` form.** `quantModule` (IP/Video/H264/QuantSynth.lean:95) is a plain `def`
   with a hand-written `Signal.loop`. `#machine_endpoint` builds such declarations through the LOOP head
   `machine_trace_of_loop_causal` (Tools/ShippingMachineCommand.lean:2214; Tools/ShippingMachineCausalCtx.lean:412), with
   different data (`machineSigma`, the loop `f`, `machineRes`, `machine_reset`).
   - `GenFacts`, and so `SrcPkg.body`, has the circuit-do form.
   - No bridge from the loop form exists, and no H.264 `machine_*` declaration exists in the repo.
   - Consequence: M2's acceptance item "an IP top as a non-vacuous `MemParentStmt` instance" needs a LOOP-FORM
     PACKAGE. That is a new unit `sparkle-gen2-loop-pkg` (§5):
     - a `SrcPkgL`, with a bridge from the loop head's facts to the same `TopShips`/`ChildShips`, or a proof that
       loop-form declarations yield a `SrcPkg`;
     - the generator run on `quantModule`.
   - This does not narrow FG: loop-form machine declarations are inside route 3 and stay in scope. It corrects the
     spec, which assumed one package form. GENERAL_SPEC §1.3/§3.1 get a row "loop-form machine declarations".

## 1. The proof of `MemParentStmt` (what exists, what is new)
| piece | supplier | status |
|---|---|---|
| `soundL` | `MachineTraceLBX.toLB` (Tools/ShippingMachineTraceX.lean:863) on `genTrace L.O L.T hA p.d dom p.gen ran` | exists, generic |
| `composed` | C8 (below) = `genTrace` + `machine_linkedT_callsRNA` with `hcalls := Or.inl (memFacts_of_memDec …)`; then `composedNWRegs_of_composedNW` (Tools/ShippingSrm28Regs.lean:77) + `hWd_of_wired` (Tools/ShippingSrm32Width.lean:28) | **C8 NEW** (a `SrcPkg`-generic copy of `memCallee_composedNW`, Tools/ShippingSrm4Run.lean:75, which takes `ran` instead of `closes`) |
| `closes` (consumer 1's `C`) | `True` | — |
| `Bnd` | `mref' = mref ∧ cref' = cref ∧ AdmCtx ∧ MachineRunJQC L.O mctx cctx (dv w + 1) p.decl p.d.shape m D` | defined in the unit |
| `facts` (RunFacts) | `core_runFacts_ranAM` (Tools/ShippingSrm4Core2.lean:601). Its `hkidP` comes from `(memKidTNC_facts ho).outsIn` (Tools/ShippingSrm4Core6.lean:98), with `ho` = `MemDec`'s first conjunct | exists; **C5 NEW** `hkidW_of_memDec` |
| `Bd`/`Inv`/`hBd`/`hRI` (G-BD) | **C1** `memInvN n`; **C2** `memKSn_boundedIn : ∀ n, KSBoundedIn (childMap ms) (KSn (childMap ms) n) body (memInvN n)` (n = 0 from `memKS_boundedIn`, ShipsHier:748; n+1 by `stepModuleTG_instFree`, Tools/ShippingSrm21Lift.lean:169); **C3** `ResetImpliesInv (ResetNk n) (memInvN n)` (from `ResetN`'s third conjunct); a named `instFree` of `memModule` | NEW |
| antecedent `Bd b D` | **C4** `core_kidsMem_ranAM`: `kidsMem (childMap D.modules) b.body = true` from `MachineRanA` and all-memory origins (A-form of `memOnly_kidsMem`, Tools/ShippingMemOnly.lean:185, including an A-form `CallStmtG` / `mem_conns_noRdata` step) | NEW |
| `ChildShips p (n+1) b D` | **C6**: a top variant of `seqChildRunN_of_composedCA` (Tools/ShippingSeqChildDeepRunA.lean:32) that takes this run's `ComposedNW` and derives `NoInstOf`/`ExtendsAway` from `MachineRanA`'s `CloseCalls` via `closeInstsG_acyclic` (Tools/ShippingChildServe.lean:223) | NEW |
| `hext`/`hextB` (the generated `ext` is the input family at declared positions `j < kD`) | **C7**: not in `GenFacts`/`SrcPkg`/`DataOk`; per declaration by `rfl` in tests (Tests/Compiler/Srm4RunTest.lean:44, :49) | see §2 |
| MemDec | the premise of `MemParentStmt` (G-MEMCALLS: per declaration today, the generator's `memTactic`) | premise (unchanged) |

## 2. Amendments (rev1, review b71e6810; applied only after approval)
U0's `DataOkB`, `CallDec`, `StepStmt` and `LeafStmt` are NOT changed. This unit adds its OWN predicates.

### 2.1 `MemParentDataOk` (R1): the concrete data predicate of this consumer
```lean
def MemParentDataOkB (p : SrcPkg ι dom) : Bool :=
  p.d.ok && p.d.callsOk p.kD &&
  decide (p.d.ss.length = p.d.shape.layout.slots.length) &&
  decide (∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width) &&
  decide (∀ b ∈ p.d.shape.binders.drop p.kD, b.2 ≠ .domain)
def MemParentDataOk (p : SrcPkg ι dom) : Prop := MemParentDataOkB p = true
```

| consumer premise | row / supplier | status |
|---|---|---|
| `ok`, `hbody` (`core_runFacts_ranAM`); `hinitW` (consumer 1) | `p.gen.ok`, `p.gen.body_eq`; `hinitW_of_ok` | E (package) / proved |
| `hC` (`callsOk kD`) | row 2 | D, coverage open (G-DATA) |
| `hslots` | row 3 | D, coverage open |
| `outTy` / `houtTy` | row 4 | D, coverage open |
| `hdomB`, consumer 2's `hI` (via `bsIn_drop_nodomain`, QuadComposed:89) | row 5 | D, coverage open |
| `hkD`, `hIlen` | from rows 1-2 (`ok_bsIn_length`, `callsOk_nIn`) | proved (CallDec unit) |
| `hSL`, `hSlen`, `hLlen`, `hNIn` | from `ok` (+ row 3 for `hSlen`): the generic bodies of `c_ok_slotLet`, `ok_len`, `c_parent_hLlen`, `c_parent_hNIn` (Tests/Compiler/C4ComposedTest.lean:130-170) | to be restated generically and proved in this unit. If one does not follow, it becomes a row of `MemParentDataOkB` and is reported (no silent addition) |
| `houtOk` (`outNameOk`, `seqChildRunN_of_composedCA`) | from `ok` (its `outs` conjunct, ShippingMachineAuto.lean:217) | proved in this unit |
| `letsAliasOk`, `outHead` | not used by this consumer | not rows. `outHead` stays an OPEN G-CLOSES obligation |

### 2.2 Case premises (not data): each has a covering route
| premise | excluded case | covering unit |
|---|---|---|
| `p.d.shape.insts ≠ []` (`hins`, and C6's `hI0`) | no call entries: an ordinary leaf | `LeafStmt` (`sparkle-gen2-leaf`) |
| `p.d.shape.instFields ≠ []` (`hfne`/`hfe`) | calls through `closeInsts` (one-output combinational children) | G-ONEOUT (M2-d, `sparkle-gen2-step`). For the surveyed memory parents `fields = insts` (SURVEY_RESULT.md); that is an observation, not a derivation |
| `p.d.shape.layout.slots ≠ []` | slotless (YOLOv8) | G-SLOTLESS (M2-c) |

These are recorded as case restrictions of THIS theorem. FG coverage of the excluded cases is the listed units'
obligation.

### 2.3 `ExtInS` (R2): minimal, typed, on `extS`/`extBS` only
`seqChildRunN_of_composedCA` (Tools/ShippingSeqChildDeepRunA.lean:58-59) needs exactly these, after the state loop:
```lean
def ExtInS (p : SrcPkg ι dom) : Prop :=
  (∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (j : Nat), j < p.kD → p.extBS i bools bits j = bools j) ∧
  (∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (j n' : Nat), j < p.kD → p.extS i bools bits j n' = bits j n')
```
- **Kind.** A functional equality about the generator's output. It is not DATA.
- **Instance supplier.** `leafM_hextB`/`leafM_hext` (Tests/Compiler/Srm4RunTest.lean:44, :49), by `rfl`, or by `delta` +
  `extendBits`/`extendBools` case splits. They are restricted to `Unit` like `genFacts_restrict`.
- **Generic obligation.** Recorded in D-GEN/M5: the generated `machineExt`/`machineExtB` are the
  `extendBits`/`extendBools` extensions of the input families at positions `≥ nDecl`. That is t1's construction. It is
  NOT proved, and it is not claimed true merely because it describes "input plumbing".
- **Scope.** It is added to `MemParentStmt'` only. `StepStmt`/`LeafStmt` are changed only after their own consumers are
  checked, in their own freezes.

### 2.4 `ChildShips` (C6)
`ChildShips` is NOT changed. C6 must derive, for every extending `dsn`:
- `ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules)`. Its first half comes from `ChildShips`' own
  hypotheses (`Dc ⊆ dsn`, `mc ∈ dsn`). Its second half, and `NoInstOf raw.name raw.body`, come from
  `closeInstsG_acyclic` on `MachineRanA`'s `CloseCalls`.

If C6 needs anything more, the proof stops and a reviewed amendment is proposed. It is not absorbed silently.

## 3. Statement after the amendments (exact; `MemParentStmt'`)
```lean
def MemParentStmt' {mref cref} (L : Laws mref cref) : Prop :=
  ∀ (p : SrcPkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    MemParentDataOk p → ExtInS p →
    p.d.shape.insts ≠ [] → p.d.shape.instFields ≠ [] → p.d.shape.layout.slots ≠ [] →
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) →
    ∀ n, TopShips p (n + 1) p.decl b raw D ∧ ChildShips p (n + 1) b D
```
It replaces the frozen `MemParentStmt` (Defs:321) for this unit's theorem. The old def stays for reference until
M2-b's statement review.

## 4. Units of this Issue, in order (each with an exact-head build)
1. C1-C3 + named `instFree` (G-BD, memory, every `n`).
2. C4 (`core_kidsMem_ranAM`).
3. C5 (`hkidW_of_memDec`) and the RunFacts assembly.
4. C8 (generic `composed`) and consumer 1 → `TopShips`.
5. C6 → `ChildShips`.
6. `memParent_ships : MemParentStmt' L DataOk`.
7. **Non-vacuity on `leafM`** (circuit-do, memory-only, slots ≠ []):
   - a `SrcPkg` from `leafM_gen` (restricted to `Unit` by `genFacts_restrict`), `leafM_memcalls` → `MemDec`,
     `leafM_hext`/`hextB` → `ExtIn`, `DataOk` by `decide`;
   - the instance of `memParent_ships`, with the run, `MachineDefines` and `MachineTaken` as hypotheses (they concern
     the compiler run and are not constructible in a test);
   - axioms.

**Acceptance of this Issue:**
- units 1-7 proved;
- §2 reviewed;
- the leafM application is a CONDITIONAL instance: package/data satisfiability with abstract run hypotheses. It is
  not evidence that an actual successful compiler run exists;
- the IP-top instance is NOT part of this Issue. It moves to `sparkle-gen2-loop-pkg`, and M2's acceptance item keeps
  it (§0.2).

## 5. New unit `sparkle-gen2-loop-pkg` (proposal)
- **Goal:** loop-form machine declarations (hand-written `Signal.loop`) get a source package with the same
  `TopShips`/`ChildShips` interface.
- **Route options**, to be decided by a read-only probe:
  - (a) Prove that the loop head's facts (`machine_trace_of_loop_causal`) give a `GenFacts`-equivalent package.
  - (b) Generalise `SrcPkg` to a sum of the circuit-do and loop forms, with `genTrace` replaced by a loop trace.
- **Deliverable:** the generator run on `quantModule` (a test file), its package, and the `MemParentStmt'` instance.
- **Acceptance:** that instance, non-vacuous.
- **Risks:**
  - If the loop head's data cannot meet `TopShips`, a new consumer is planned. That is not a scope change.
  - If the generator refuses `quantModule`, that is a generator coverage finding (M5 G3-GEN coverage), recorded with the
    error.

## 6. Not claimed
- No proof yet. FG/T1/M2 are not complete.
- G-MEMCALLS stays a premise (per declaration today).
- `outHead` is not discharged, only re-homed.
