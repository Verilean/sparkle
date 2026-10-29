# S4 consumer (G-ONEOUT): one-output parents on the A boundary — freeze rev1, FOR REVIEW

- **Issue:** `sparkle-gen2-step` (S4 of STEP_IFACE_FREEZE.md rev3 §4, approved; CALLFIELD_RESULT.md, approved).
- **Branch:** `par/gen2-spec`, at ffd283ce. Read-only survey. No Lean is changed by this document and nothing in it is proved.
- **Scope:** parents with `instFields = []`, `insts ≠ []` and `slots ≠ []`, closed by `closeInsts` (Sparkle/IR/Machine.lean:396-427). Slotless one-output parents belong to S5.

## 1. Selecting the combinational branch (facts of the parent's run)
- **The refusal.** `instStmt` (Machine.lean:272) returns `none` when `mc.inputs.any (fun p => p.name == "clk" || p.name == "rst")` holds (Machine.lean:278). It also requires `mc.outputs = [outP]` (Machine.lean:280).
- **`CallStmt` already records it.** `CallStmt` (Tools/ShippingMachineInst.lean:190-203) has the conjunct `(mc.inputs.any (fun p => p.name == "clk" || p.name == "rst")) = false` and `mc.outputs = [outP]`. `instStmt_some` (:205) proves it, and `closeInsts_calls` (:247) gives a `CallStmt` per call.
- **Where the consumer gets `CallStmt`.** Not from `closeInsts_calls`, whose `portNames` are `t.inputs.map (·.name)`. It comes from `MachineWired`'s one-output clauses (Tools/ShippingMachineEntry.lean:664-669). These use the trace's `machPorts … ids cache` names, the same `CallStmt` as in `Served1P` (Defs:231-240) and `machine_linked_of` (Tools/ShippingMachineCompose.lean:590-595).
- **Assignment-only children.**
  - `closeInsts_kidsComb` (Tools/ShippingChildServe.lean:248) gives `kidsCombB D.modules raw.body = true` from the closing.
  - That closing comes from `core_closeInstsA` (Tools/ShippingParentDesignA.lean:152), on `MachineRanA` from `machineRanA_of_runJQC` (Tools/ShippingRanABridge.lean:38).
  - `kidsComb_of_B` (Tools/ShippingMachineDepthHR.lean:31) converts it to `kidsComb`.
- **C3 / C2.** `not_seq_and_comb` and `childRunN_iff_seq` (Tools/ShippingGen2AComb.lean:23, :28). There is no lemma for the `"clk" ∉` direction.

**Missing (pure, small):**
```lean
theorem callStmt_noClk {nIn kI n : Nat} {names : List String} {k : Nat} {args : List Nat} {mc : Module} {st : Stmt}
    (h : Tools.ShippingMachineInst.CallStmt nIn kI n names k args mc st) :
    "clk" ∉ mc.inputs.map (·.name) ∧ "rst" ∉ mc.inputs.map (·.name)
theorem combChildRunN_of_noClk (hclk : "clk" ∉ mc.inputs.map (·.name)) :
    ChildRunN children dsn n mc bsC outsC S → CombChildRunN children dsn n mc bsC outsC S
  -- fun h => h.elim (fun hs => absurd hs.2.2.1 hclk) id
theorem kidsCombB_assign {ms : List Module} {body : List Stmt} {mn iname : String} {conns} {c : Module}
    (h : kidsCombB ms body = true) (hst : Stmt.inst mn iname conns ∈ body)
    (hc : moduleByName ms mn = some c) : c.body.all Sparkle.IR.RegDedup.isAssign = true
```

## 2. The served consumer
- **Template.** `machine_linked_callsRA` (Tools/ShippingMachineComposeRA.lean:72-125):
  - `hfn` there quantifies over every run of the callee (:102-108).
  - Its proof feeds `machine_linked_of` (Compose.lean:538) a per-instance callback `ChildFn mc (P k) (F k)` (:115-124).
- **The group-parent analogue.** `machine_linkedT_callsServed` (Tools/ShippingGen2Consumer.lean:30-105) takes the child fact from `hx.1` (`ServedGP`'s right disjunct, :101-104).

**Obstruction found (extB).** `machine_linked_of`, `machine_linked_callsRA`, `ComposedH` (Tools/ShippingMachineShipsHierH.lean:33-66) and `composedNWn_of_H` (DepthHR:208) all fix `extB := fun _ bools _ => bools`: the trace at ComposeRA:84, `posEnc (fun p => (bools p).val j)` at :100, and `(bools j).val` at ShipsHierH:49. The package trace instead uses `p.extBS`, which is general (`SrcPkgL.extBS`, Tools/ShippingGen2Loop.lean:207). So do `StepStmt` (Defs:311-312), `CallDec` (Defs:111) and `OneOutCall` (CallField.lean:174).

What is needed is a proof copy with `(bools p).val` replaced by `(extB i bools bits p).val`. The proof of `machine_linked_of` uses `bools` only in those positions (Compose.lean:672 and the trace), so the copy is mechanical but **new**.

**Missing (generic):**
```lean
-- ComposedH with extB (ShipsHierH:33-66, line 49 `(bools j)` → `(extB i bools bits j)`)
def ComposedHB (R : Nat → Module → Prop) (declName : Name) (d : MachineData) (kD : Nat) (m : Module) (dsn : Design)
    {ι} (dom : ι → DomainConfig) (src) (ext) (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool) : Prop
-- machine_linked_of (Compose.lean:538-605) with `extB` in the trace and in `posEnc`; P F unchanged
theorem machine_linked_ofB … (trace : … SourceInputs declName d.bsIn ids cache
      (fun j => (extB i bools bits j).val (T - 1 - t)) …) … (P : Nat → List Nat → Prop) (F : Nat → List Nat → Nat) :
    ∀ i bools bits T seed st0 mems, (SourceInputs … (d.bsIn.take kD) … (extB i bools bits j) …) → … →
      (∀ k args mc st, … CallStmt … → moduleByName dsn.modules mc.name = some mc → ChildFn mc (P k) (F k)) →
      (∀ k args j, (d.shape.insts.map (·.2.1))[k]? = some args → j < T →
        (∀ q ∈ args, q < d.ls.length ∧ q < (lsrc i bools bits).length) ∧
        P k (valsOf (lsrc i bools bits) args j) ∧
        F k (valsOf (lsrc i bools bits) args j) =
          posEnc (fun p => (extB i bools bits p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k)
            (((d.bsIn.drop kD)[k]?.map (·.2)).getD .domain)) →
      ∃ envs, runModuleH (weOf m) (childMap dsn.modules) m.body seed T st0 mems = some envs ∧ … (as :601-605)
-- composedNWn_of_H (DepthHR:208-226) with ComposedHB and ComposedNW … extB
theorem composedNWn_of_HB (n : Nat) (hC : ComposedHB R declName d kD m dsn dom src ext extB)
    (hB : BoundH R declName d m dsn) (hcomb : kidsComb dsn.modules m.body = true) :
    ComposedNW n declName d kD m dsn dom src ext extB
```
(`valsOf` is CallsLinkedT.lean:27; it is definitionally the `args.map …` of Compose.lean:598.)

**The functions per call.** Both are chosen from the CALLEE's package, independent of `mc`. `F` is per `i`, because `ChildShips` holds `∀ i` with `q.S i`, while `machine_linked_of` takes `P F` outside `i`. So the served lemma calls `machine_linked_ofB` after `intro i` (as ComposeRA:112-113 does), with `F i`.
```lean
def oneP (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) (v : List Nat) : Prop :=
  ∃ q, P ((p.d.shape.insts.map (·.1))[k]?.getD .anonymous) = some q ∧ InRange v q.ports
def oneF (P : Pkgs ι dom) (p : Pkg ι dom) (i : ι) (k : Nat) (v : List Nat) : Nat :=
  match P ((p.d.shape.insts.map (·.1))[k]?.getD .anonymous) with
  | some q => ((q.S i (fun _ => v))[0]?.map (· 0)).getD 0
  | none => 0
```
`q.ports = (q.d.bsIn.take q.kD).filter (·.2 != .domain)` (Tools/ShippingGen2Pkg.lean:80-81), which is S4-b's `bsC.filter …` at `bsC := q.d.bsIn.take q.kD`.

**The served consumer (missing):**
```lean
theorem machine_linked_callsServed1 {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Module} {D : Design}
    (h : MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hsimple : p.d.shape.instFields = [])
    (hkD : p.kD ≤ p.d.bsIn.length) (hI : ∀ b ∈ p.d.bsIn.drop p.kD, b.2 ≠ .domain)
    (hIlen : (p.d.bsIn.drop p.kD).length = p.d.shape.insts.length)
    (hSL : ∀ b ∈ p.d.slotBs ++ p.d.letBs, b.2 ≠ .domain)
    (hSlen : p.d.slotBs.length = p.d.shape.layout.slots.length) (hLlen : p.d.letBs.length = p.d.shape.layout.lets)
    (hNIn : machNIn p.d.shape = ((p.d.bsIn.take p.kD).filter (fun b => b.2 != .domain)).length)
    (hkc : kidsCombB D.modules raw.body = true)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) :
    ComposedHB (fun _ _ => True) p.decl p.d p.kD raw D dom p.src p.extS p.extBS
```

**Proof route (per `i`):**
- **`hfn`, per instance `(k, mc, st)`.**
  - `hx.2 hsimple k hk args mc st …` (`Served1P`). The left disjunct contradicts `CallDec`'s `child? = none`, as at ComposeRA:122. The right disjunct gives `ShipsRes L P c (mc, Dc)` (Defs:135): `∃ q' n, P c = some q' ∧ ChildShips q' n mc Dc`, so `q' = q`.
  - Instantiate `ChildShips` (Defs:87-90) at `dsn := D`, using `Served1P`'s `∀ g ∈ Dc.modules, …` and `moduleByName D.modules mc.name = some mc`. This gives `ChildRunN … (q.S i)`.
  - Then `callStmt_noClk` + `combChildRunN_of_noClk` give `CombChildRunN (childMap D.modules) D n mc (q.d.bsIn.take q.kD) [o] (q.S i)`, with `q.d.shape.layout.outs = [o]` from `oneOutCall_of_callDec` (CallField.lean:177).
  - `childFn_of_combRun` (Tools/ShippingGen2CombKid.lean:174) applies with `hA := kidsCombB_assign hkc …`, `hout` from `CallStmt`, and `hS` from `OneOutCall`'s `∀ v, ∃ g, (q.S i (fun _ => v))[0]? = some g`. The result is `ChildFn mc (oneP P p k) (oneF P p i k)`. `oneP` is rewritten with `P c = some q`.
  - The height `n` of each child is arbitrary: S4-b and S4-c hold at every `n`.
- **`hcalls`, per call `k`, `j`.**
  - From `OneOutCall` at `i`: the argument bounds, `InRange (valsOf …) q.ports` (gives `oneP`), and `f` with `(q.S i (valsOf (p.lsrc i bools bits) args))[0]? = some f` and `posEnc (p.extBS …) … = f τ`.
  - `combS_pointwise` (CombKid:205) at `vals := valsOf …`, `τ := j` and `g` from `hS` gives `f j = g 0 = oneF P p i k (valsOf … j)`.
  - The `CombChildRunN` it needs is that of call `k`'s instance. `MachineWired`'s clause (Entry:664-666) gives `(args, mc, st)` with `CallStmt`, and `Served1P` then gives it as above. A `CombChildRunN` exists only through a served instance; `hcalls` does not hold without one.

## 3. To depth n, `TopShips` and the parent's `ChildShips`
- **Depth.** `composedNWn_of_HB n (machine_linked_callsServed1 …) (fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial) (kidsComb_of_B hkc)`. This is `ComposedNW n … p.extBS` at every `n`.
- **`TopShips p n`.** Consumer 1, `machine_ships_hierC_noHstR` (Tools/ShippingSrm33Core.lean:24), as in `memParent_topShips` (Tools/ShippingGen2MemTop.lean:45-102):
  - `Bnd` pins the run (MemTop:82-83).
  - `soundL := (Pkg.trace L.O L.T hA p ran).toLB` (TraceX.lean:863).
  - `composed := composedNWRegs_of_composedNW` (Tools/ShippingSrm28Regs.lean:77) + `hWd_of_wired` (Tools/ShippingSrm32Width.lean:28) on the depth result.
  - `facts : RunFacts (childMap D.modules) b` (Tools/ShippingGuardsSound.lean:314-322):
    - `gate`, `ndB`, `self`, `outs`, `rst` from `core_runFactsHA` (ParentDesignA:494; needs `hsl`, `hf`, `hnomem`);
    - `wfB` from `core_linkedWF_ranA` (Tools/ShippingParentTailsA.lean:197; no `instFields` premise);
    - `wid : instOutWidthsOk …`: **missing** for `instFields = []`, because `core_instOutWidthsOk_ranA` (ParentRunFactsA:566) needs `hfne : instFields ≠ []`.
  - `Bd`/`Inv`: `Inv := fun _ _ => True`, so `hRI` is trivial (ResetImpliesInv, ShipsHier:101). `hBd` needs `KSBoundedIn (childMap D.modules) (KSn … n) b.body (fun _ _ => True)` (HierOptRun:658). The only KSn supplier is `KSn_boundedIn` (Tools/ShippingMachineShipsDepth.lean:171), from `kidsMaskedN` (outputs masked). **No supplier for comb children**: `evalAssigns` does not mask (Sparkle/IR/Semantics.lean:216-218), and `KSBoundedIn` ranges over every `env`, so `CombChildRunN`'s in-range outputs do not suffice.
- **`ChildShips p (n + 1) b D`.** `Or.inl` of `seqChildRunN_of_composedNW_run n` (Tools/ShippingGen2C6.lean:28). It handles `instFields = []` itself (C6:64-72) and needs `hsl` and `ExtInS p` (Tools/ShippingGen2MemParent.lean:46). The `ExtendsAway`/`NoInstOf` steps are as in MemShips:59-82, with `closeInsts_acyclic` (ChildServe:200) on `core_closeInstsA`'s closing.

## 4. The one-output step statement
```lean
def OneOutDataOkB (p : Pkg ι dom) : Bool :=
  MemParentDataOkB p &&                                     -- MemParent.lean:38-42 rows (ok, callsOk, slots, outTy, domB)
  p.d.shape.instTagged.all (fun x => x.2.child?.isNone && (Sparkle.Compiler.MachMemory.memChild? x.1).isNone)  -- hnomem
def OneOutStepStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (DataOk : Pkg ι dom → Prop) : Prop :=
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    P p.decl = some p → DataOk p → OneOutDataOkB p = true → ExtInS p →
    p.d.shape.insts ≠ [] → p.d.shape.instFields = [] → p.d.shape.layout.slots ≠ [] →
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc →
    ∀ n, TopShips p (n + 1) p.decl b raw D ∧ ChildShips p (n + 1) b D
```

**Relation to `StepStmt` (Defs:300-313).**
- The telescope is the same, plus case premises (`insts ≠ []`, `instFields = []`, `slots ≠ []`) and data (`OneOutDataOkB`, `ExtInS`, in the pattern of `MemParentStmt'`).
- The decoding is strengthened from `MemDec ∨ ∃ q, … CallDec` to `∃ q, … CallDec`.
- The conclusion `∀ n` gives StepStmt's `∃ n` at `n + 1 := 1`.
- `OneOutStepStmt` covers StepStmt's one-output-with-slots case only once `oneOut_callDec_of_dec` holds (§5, S4-MEM).

## 5. Missing vs existing; stop conditions
**Existing:**
- `childFn_of_combRun` (CombKid:174), `combS_pointwise` (:205), `evalAssigns_mems_irrel` (:24), `Pkg.src_get` (:79);
- `OneOutCall` / `oneOutCall_of_callDec` (CallField:164, :177); `oneOut_outputs` (:197; output shape only, unused for the choice);
- C1-C3 (AComb);
- `CallStmt`, `instStmt_some`, `closeInsts_calls` (Inst:190, 205, 247);
- `closeInsts_kidsComb`, `closeInsts_acyclic`, `closeInsts_serves` (ChildServe:248, 200, 160);
- `core_closeInstsA`, `core_runFactsHA` (ParentDesignA:152, 494);
- `composedNWn_of_H`, `kidsComb_of_B`, `runModuleTG_KSn_of_H` (DepthHR:208, 31, 183);
- consumer 1 (Srm33Core:24); `seqChildRunN_of_composedNW_run` (C6:28).

**Missing, provable from existing facts:**
- `callStmt_noClk`, `combChildRunN_of_noClk`, `kidsCombB_assign` (§1);
- `ComposedHB`, `machine_linked_ofB`, `composedNWn_of_HB` (proof copies, §2);
- `machine_linked_callsServed1`, `oneP`/`oneF` (§2);
- `oneOut_topShips`, `oneOut_childShips`, and `oneOut_step : OneOutStepStmt L P DataOk` (§3-§4).

**Stop conditions (a needed fact with no supplier; reported, not added silently):**
- **S4-WID.** `RunFacts.wid` for `instFields = []`. The analogue of `hkidW` (ParentRunFactsA:612, `callWidthsOk` on `instFields.getD k`) relates the parent's binder `nDecl + k` to the callee's single output width. That is a relation between `p` and `q`. It is not in `CallDec`, and no per-package `DataOk` can express it. It needs either a one-output `callWidthsOk` row with `kidOuts k := q.d.shape.layout.outs` (and `ChildOutTys` from `CombChildRunN`'s output equation), or a decision.
- **S4-BD.** `KSBoundedIn` of comb children under `KSn`. `kidsMaskedN` (ShipsDepth:163) is not given by `kidsCombB`, by `ChildShips` or by the closing. It needs a new check-derived supplier (masked outputs of the served child) or a decision.
- **S4-MEM / G-ONEOUT-REACH.** `oneOut_callDec_of_dec : (MemDec p k c ∨ ∃ q, P c = some q ∧ CallDec p q k) → ∃ q, …` is not derivable:
  - `closeInstsM` (Sparkle/Compiler/Elab.lean:5206-5218) synthesises `synth c` for EVERY instance regardless of origin. So a memory-origin entry (MemFacts origin `memModule`, CallsLinkedT.lean:37-38) is served by the real child of `c`, not by `memModule`.
  - `Served1P`'s left disjunct (`mc = md.1 = memModule`, which has a `"clk"` input, MachMemory.lean:56) is refuted by `callStmt_noClk`. Its right disjunct then is a `ShipsRes` of a name that `T1Hyp.closed` (Defs:211-212) does not put in `Reach`, and `MemDec`'s `memRead` semantics need not match that child.
  - `core_runFactsHA`'s `hnomem` (in `OneOutDataOkB`) excludes such entries on the data side. But whether `StepStmt`'s `MemDec` branch is vacuous for one-output parents is OPEN. `OneOutStepStmt` therefore takes `CallDec` for every `k`.
- **Integration.** `Served1P (ShipsRes L P)` is a premise here (from G-SERVED, `ServedShipsStmt`, Defs:251, not built).

## 6. Not claimed
- No `TopShips`/`ChildShips` for slotless one-output parents (S5).
- The obstructions S4-WID, S4-BD and S4-MEM are not resolved.
- The `extB` copies are not yet built.
