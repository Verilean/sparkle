# M2-a `MemParentStmt`: frozen plan

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

## 2. Amendments to the frozen statements (for review; applied only after approval)
- **A1, `DataOkB` rows.** Add the rows the consumers need: `fne`, `domB`, `kD ≤ bsIn.length`, `hIlen`, `hSL`, `hSlen`,
  `hLlen`, `hNIn`, as Bool checks over `p.d`/`p.kD`.
  - The `c_parent_*` lemmas derive most of them from `ok`/`callsOk`/`slots`. Those are proved and NOT added.
  - Only the underived ones (`fne`, `domB` if not derived) are added.
  - Each is a D row with coverage open.
- **A2, `hext`/`hextB` (C7).** A new Prop on packages:
  `ExtIn p := ∀ i bools bits S j, j < p.kD → p.extB i bools bits S j = bools j ∧ ∀ n, p.ext i bools bits S j n = bits j n`.
  It is added as a premise of `MemParentStmt` (and `StepStmt`/`LeafStmt` where used).
  - It is a property of the generator's construction of `ext`, the same kind as t1 in G3-GEN-CALL. Its generic supply
    goes to D-GEN/G3-GEN (M5).
  - In instances it is `rfl`.
  - It is NOT a semantic conclusion. It concerns only how the declared inputs enter `ext`.
- **A3, `outHead`.** Removed from `DataOkB` for `MemParentStmt`'s use, and re-homed to G-CLOSES (§0.1). `DataOkB` keeps
  it only if another consumer needs it.

## 3. Statement after A1-A2 (Lean, exact; `MemParentStmt'` replaces `MemParentStmt` after approval)
```lean
def MemParentStmt' {mref cref} (L : Laws mref cref) (DataOk : SrcPkg ι dom → Prop) : Prop :=
  ∀ (p : SrcPkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    DataOk p → ExtIn p → p.d.shape.layout.slots ≠ [] → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) →
    ∀ n, TopShips p (n + 1) p.decl b raw D ∧ ChildShips p (n + 1) b D
```
- `n + 1` is kept. C2 covers every `n`.
- Whether `ChildShips` needs `ExtendsAway` beyond `Dc ⊆ dsn` is checked when C6 is written. If an extra hypothesis
  is needed, it is reported as a deviation.

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
- A1-A3 reviewed;
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
