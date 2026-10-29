# S5 slotless parents and slotless tops — freeze rev0 (FOR REVIEW — design only, nothing built or proved)

- **Issue:** `sparkle-gen2-step` (S5 of STEP_IFACE_FREEZE.md §4, lines 205-208; order §5 item 4).
- **Branch:** `par/gen2-spec`. Frozen source SHA **1b840215**. Every `file:line` below is at that SHA. The files cited
  are unchanged since d603ac07: `git diff d603ac07..1b840215` touches only gen3 files and `lakefile.lean`.
- **What this is:** the exact types for S5 (new files only), the stages, controls, audit and decision items. No Lean
  is changed by this document, and nothing here is proved.

## 1. The existing types (as read)
- `CombChildRunN` (Defs:60-75) excludes `"clk"`/`"rst"` from the inputs (:65) and has no clock/reset premise. It
  takes the run through `RunOn … (seedIn mc ins)` (:73). `ChildRunN` = `Seq ∨ Comb` (Defs:77-81). `ChildShips`
  (Defs:87-91) is quantified over every `dsn` that extends the design.
- `TopShips` (Defs:273-295) has the binders `(∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0)` (:283).
- `SeqChildRunN` (MachineDepth:64-81) requires `"clk"`, `"rst"` ∈ inputs (:67-68). `ResetN` (MachineDepth:52-62)
  constrains only registers, memories and kids.
- `ComposedNW` (MachineDepthRun:34-66): `H` holds for EVERY `seed` with `∀ t st, seed t st "rst" = 0` and the same for
  `"clk"` (:56).
- `seedIn m ins t st n = if n ∈ inputs then ins t n else st n` (SeqOptSoundness:892-894).
- `seqChildRunN_of_composedNW_run` (Gen2C6:29-55) has `hsl : slots ≠ []` (:40). Its only use is
  `calls_ports wired len hsl …` (:59).
- `calls_ports` (MachineDepthChild:41-56) uses `hsl` twice: to pick `extra = []` (:78-80) and to make the
  `slots.isEmpty` branch false (:82-86).
- The input clause of `MachineWired` (MachineEntry:738-750) is `extra = [] ∨ (extra = [clk, rst] ∧ slots = [])`
  (:742), and it adds clk/rst only when `slots ≠ []` (:747).
- Other `MachineWired` clauses used here:
  - no `assign` to `"rst"`/`"clk"` (MachineEntry:729);
  - every register statement belongs to a slot (:755-758). With `slots = []` there is no register.
- `linkedOk` refuses `.memory` (Machine.lean:355). `closeInsts` body = a permutation of `m.body ++ stmts`
  (Machine.lean:396-425, `isPermOf` :412).
- `withClockFor` appends clk/rst to a parent that lacks them when some child has a clk/rst input
  (MachineInstG:73-78). It keeps the body (:80-83). `closeInstsG` applies it (:120) and permutes the body (:128).
- S3:
  - `comb_inst_runN` (GroupComb:111-134) takes clk/rst absence from the child's own `CombChildRunN`;
  - `CombFactsRN` is at GroupComb:270-288 and `calls_hchildRNC` at :295;
  - `group_composedNW` (GroupServed:271-290) and `group_childShips` (:294-341, `hsl` at :297).
- S4:
  - `oneOut_composedNW` (OneOut:260-286; no `hsl`);
  - `oneOut_childShips` (:288-331, `hsl` at :291);
  - `combChildRunN_of_noClk` (:78-83);
  - `oneOut_topShipsO` (OneOutTopO:334-415, `hsl` at :339, used only for `RunFacts.rst` via `core_runFactsHO`).
- `core_runFactsHO` (ParentDesignO:398-418) uses `hsl` only in `rst := core_rst_anyO … hsl …` (:416).
- S1: `runModule_seed_local` (Gen2Comb:28-61). It is FLAT `runModule` only.
- S2:
  - `sllSeedZ` (SlotlessLeaf:67-68) and `runModule_rst_irrel` (:108-131);
  - `slotless_inputs_alloc_ofRun` (:397);
  - S2-c `closeLets_closed` (SlotlessClosed:91), `closeMachine_slotless_closed` (:200), `slotless_closed_full` (:254).
- Consumer 1:
  - `machine_ships_hierC_run` (FitChain:1073-1232) destructures `RunFacts` (GuardsSound:314-322, `rst` :320) at :1164;
  - it uses `hrstIn` at :1186 (to build `H`'s `seed "rst" = 0`) and at :1220 (`hierRefineCheck_linked`, HierOptRun:532-555,
    `hrstIn hrstZ` :543), and `hstR` at :1182/:1221.
- No-reset models:
  - `refineCheck_transfer_noReg` (RefineNoRst:224). It is imported (SlotlessLeaf:4) by the BUILT S2 file (SlotlessLeaf:42);
  - `hierRefineCheck_linkedH_noRst` (HierOptRunHNoRst:56). This one is H-level (`runModuleH`), not KS-level, and its
    header says "WRITTEN, NOT BUILT" (:3). It is used here only as the model for a change rule.
- Old-boundary slotless facts (`ChildBnd`/`MachineClosesAt`, not the A boundary):
  - `SeqKid` (SlotlessClk:76-79);
  - `core_seqKid_inputs` (:150);
  - `core_slotless_seq` (:239);
  - `core_runFactsS` (SlotlessKidFacts:68).
- TG semantics:
  - `evalAssignsKG` (HierStateG:36-56): an `inst` reads only `inConns`, through `KS`, and writes `bindOuts`;
  - `KSLocal` (:30-33), `stepModuleTG`/`runModuleTG` (:59-75), `KSn_local` (:632);
  - `RunOn (n+1) = runModuleTG (KSn children n)` (MachineDepth:27-31).

## 2. Findings (obstructions)
1. **`hsl` in `calls_ports`.**
   - It is only a case selector. With `slots = []` the wiring leaves two cases:
     - **(S)** `extra = [clk, rst]`: the module HAS clk/rst. These are the slotless parents of sequential or memory
       children (`withClockFor`; engineOnce, Tests/Compiler/NoPortsSlotlessEngineOnceTest.lean:10-21).
     - **(C)** `extra = []`: every input is an allocated port, so there is NO clk/rst (`hnClk`/`hnRst`,
       MachineDepthChild:90-93).
   - S5 decides the case from the actual `m.inputs`. It does not assume it, and needs no `SeqKid` premise.
2. **Reset irrelevance at TG level is missing.**
   - In case (C) `seedIn raw ins t st "rst" = st "rst"`, so `ComposedNW`'s `H` cannot be applied at `seedIn`
     (:56 quantifies over all `st`).
   - The S2 route (run at a zeroed seed, then transfer) needs a `runModuleTG` analogue of S1. None exists: grep finds no
     seed-congruence lemma for `runModuleTG`.
   - For the transfer we need a syntactic fact: no statement of `raw.body` reads or writes `"rst"`/`"clk"`.
   - `readsClosedB` is NOT enough: `stmtReads (.inst …) = []` (ReorderInvariance:83-87), but TG reads `inConns`.
     So a new predicate and a run-level supplier are needed (§3 A2, B1).
3. **`RunFacts.rst` (GuardsSound:320).**
   - In case (C) it is false, so consumer 1 cannot be used. It also feeds `hierRefineCheck_linked`, whose no-rst
     variant exists only at the H level (HierOptRunHNoRst:56).
   - A KS-level copy with `refineCheck_transfer_noReg` is needed (C1).
4. **`TopShips` is VACUOUS when `"clk"` ∉ `b.inputs`** (a STOP-class finding, D1).
   - In that case binder Defs:283 `∀ t st, seedIn b ins t st "clk" = 0` is refuted by `st := fun _ => 1`.
     So `TopShips` holds trivially for every case-(C) module, including S2's slotless leaves.
   - S2's proof does not exploit this: the binder is `_` (SlotlessLeaf:202). But the statement carries no information
     there.
   - S5 proves a clock-free `TopShipsNC` (C2) and derives `TopShips` by weakening.
5. **Group slotless parents have no `TopShips` route.** It is blocked exactly as for group parents with slots
   (S3_GROUP_FREEZE §5 :364: `kidP`/`kidW`, StepStmt route). S5 gives the one-output top only.
6. **Hierarchical children.**
   - One-output children are flat (`kidsCombB`, Machine.lean:368ff; `oneOut_composedNW` :280-285).
   - Group children may contain instances. They are consumed at depth `n` through their own `CombChildRunN`/
     `SeqChildRunN` (`comb_inst_runN` → `runKS_RunOn`, MachineDepth:33) inside `group_composedNW`. S5 adds nothing
     there.
   - S5 handles only the PARENT's own run at `n+1`: `RunOn (n+1)` = `runModuleTG (KSn …)` with `KSn_local`.

## 3. Stage A — pure lemmas (new file `Tools/ShippingGen2SlotlessParent.lean`; opens as Gen2C6:11-24 + GroupComb:22-41)

**A1 `calls_ports_sl`.** Copy of `calls_ports` (MachineDepthChild:41-56). Change rules:
- `hsl` becomes `hsl0`, and the conclusion's 2nd/3rd conjuncts become one disjunction;
- in the proof, `hext` is `rcases` on both cases, `hslE : slots.isEmpty = true`, and `hinN` uses `P.take K ++ extra`;
- everything else is verbatim.
```lean
theorem calls_ports_sl {declName : Name} {d : MachineData} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName d.shape ids cache m dsn regs lets)
    (len : ids.length = d.shape.binders.length)
    (hsl0 : d.shape.layout.slots = [])                                                        -- CHANGED
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (kD : Nat) (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain) (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length) :
    (m.inputs.map (·.name)).Nodup ∧
    (("clk" ∈ m.inputs.map (·.name) ∧ "rst" ∈ m.inputs.map (·.name)) ∨
      ("clk" ∉ m.inputs.map (·.name) ∧ "rst" ∉ m.inputs.map (·.name))) ∧                    -- CHANGED
    (∀ x ∈ m.outputs.map (·.name), x ∉ m.inputs.map (·.name)) ∧
    argPorts m = machPorts declName ids cache (d.bsIn.take kD) ∧
    (∀ x ∈ ((machPorts declName ids cache d.shape.binders).map (·.name)).drop
        (((machPorts declName ids cache d.shape.binders).map (·.name)).length -
          d.shape.layout.lets - d.shape.layout.slots.length), x ∉ m.inputs.map (·.name))
```
**A2 `NoTouchZ`, `runModuleTG_seed_offZ`.** New. The TG analogue of S1 / `runModule_rst_irrel`.
- Proof: induction on `T`, using a per-cycle `evalAssignsKG` lemma.
  - Assigns use `evalExpr` congruence on `refsOf`.
  - Instances use `KSLocal` (HierStateG:30). The same `cres`/`ks'` gives the same `bindOuts` off `Z`.
  - `regNexts`/`memNexts` are `[]`/identity, because only assigns and instances occur. So the next state is EQUAL.
```lean
def NoTouchZ (Z : List String) (body : List Stmt) : Prop :=
  ∀ st ∈ body,
    (∃ l r, st = Stmt.assign l r ∧ l ∉ Z ∧ ∀ z ∈ Z, z ∉ Sparkle.IR.Reorder.refsOf r) ∨
    (∃ mn iname conns, st = Stmt.inst mn iname conns ∧ ∀ c ∈ conns, ∀ w, c.2 = .ref w → w ∉ Z)

theorem runModuleTG_seed_offZ {σ : Type} (KS : KStep σ) (hloc : KSLocal KS) (we : WEnv)
    (children : String → Option (Module × WEnv)) {body : List Stmt} {Z : List String}
    (hZ : NoTouchZ Z body) {seed₁ seed₂ : Nat → (String → Nat) → Env}
    (hagree : ∀ t st y, y ∉ Z → seed₁ t st y = seed₂ t st y) :
    ∀ (T : Nat) (s : KState σ) (envs₁ : List Env),
      runModuleTG KS we children body seed₁ T s = some envs₁ →
      ∃ envs₂, runModuleTG KS we children body seed₂ T s = some envs₂ ∧ envs₂.length = envs₁.length ∧
        ∀ j (h₁ : j < envs₁.length) (h₂ : j < envs₂.length) (y : String), y ∉ Z →
          (envs₂[j]'h₂) y = (envs₁[j]'h₁) y
```
- **Proof risk (stated, not hidden):** `inConns`/`bindOuts` must only touch `.ref` conns. `KSLocal` is phrased on
  `.ref` wires (:31). If `bindOuts` can write a non-`.ref` conn, `NoTouchZ` is strengthened to bind all conn names.
  This is a pure change, recorded in rev1.

**A3 `slSeedZ`, `childRunN_of_composedNW_runSl`.** Copy of Gen2C6:29-55. Change rules:
- `hsl` → `hsl0`; one new binder `hZ` (a syntactic premise; B1 discharges it from the run);
- the conclusion `SeqChildRunN` → `ChildRunN`;
- the proof does `rcases (calls_ports_sl …).2.1`. Case (S) is C6:59-137 verbatim (wrapped `Or.inl`).
- Case (C) (`Or.inr`):
  - conjuncts as in C6:83-85, with clk/rst from the case;
  - the run: `H` at `seed := slSeedZ raw ins`; `SourceInputs` via `sourceInputs_of_vals` at the zeroed state (as
    SlotlessLeaf:203-210);
  - `regs = []` (`rlen` + `hslots` + `hsl0`) makes the regs, slot and register premises vacuous;
  - kids `ResetN` as C6:118-126; then `runModuleTG_mono_away` (C6:127);
  - then A2 at `Z := ["rst","clk"]`, `KS := KSn (childMap dsn.modules) n` (`KSn_local`);
  - observation names `∉ Z` by `outName_ne_clk` (CallsAssemblyG:59).
```lean
def slSeedZ (m : Module) (ins : Nat → String → Nat) : Nat → (String → Nat) → Env :=
  fun t st => seedIn m ins t (fun x => if x = "rst" ∨ x = "clk" then 0 else st x)

open Tools.ShippingMachineChild (boolsOf bitsOf) in
theorem childRunN_of_composedNW_runSl (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl0 : d.shape.layout.slots = [])                                                         -- CHANGED
    (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length) (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (hextB : ∀ i bools bits j, j < kD → extB i bools bits j = bools j)
    (hext : ∀ i bools bits j n', j < kD → ext i bools bits j n' = bits j n')
    (i : ι) {mc raw : Module} {D dsn : Design}
    (hcomp : ComposedNW n c d kD raw D dom src ext extB)
    (hpost : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hEA : ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules))
    (hNI : NoInstOf raw.name raw.body)
    (hZ : "rst" ∉ raw.inputs.map (·.name) → NoTouchZ ["rst", "clk"] raw.body) :                -- NEW
    Tools.ShippingGen2.ChildRunN (childMap dsn.modules) dsn (n + 1) mc (d.bsIn.take kD)          -- CHANGED
      d.shape.layout.outs (fun vals => src i (boolsOf (d.bsIn.take kD) vals) (bitsOf (d.bsIn.take kD) vals))
```

## 4. Stage B — run-level supplier and `ChildShips` (new file `Tools/ShippingGen2SlotlessParentRun.lean`; ambient as GroupServed:247-266)

**B1 `slotlessParent_noTouch_ofRun`.** One statement covers both closings.
- **Proof chain on the one `ran`:**
  - `machineRanA_of_runJQC` (RanABridge:38);
  - the closing: `core_closeInstsA` (ParentDesignA:152) when `instFields = []`, else the `closeInstsG` branch of
    `ranA` (as GroupServed:316-322);
  - `transition_closed` (TransitionClosed:35), then `closeLets_closed` (SlotlessClosed:91) and
    `closeMachine_slotless_closed` (:200). Together: `readsClosedB` over the pre-call module's inputs, assigns only;
  - those inputs are allocated (as `slotless_inputs_alloc_ofRun`, SlotlessLeaf:397), so they are not `"rst"`/`"clk"`;
  - every assign of `raw` is one of the pre-call module's (`isPermOf`, Machine.lean:412 / MachineInstG:128);
  - no assign writes Z (MachineEntry:729).
- **Instance conns:**
  - their `.ref` wires are call ports (allocated);
  - or they are `"clk"`/`"rst"` passed to a child that has them (`connsG`). That case contradicts `hrst`: such a child
    makes `withClockFor` add `"rst"` (MachineInstG:73-78). One-output calls refuse such children (`callStmt_noClk`,
    OneOut:60).
- **Reset absence comes from the module's actual inputs (`hrst`)**, never from a premise on children.
```lean
theorem slotlessParent_noTouch_ofRun (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hins : p.d.shape.insts ≠ []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hrst : "rst" ∉ raw.inputs.map (·.name)) :
    NoTouchZ ["rst", "clk"] raw.body
```
**B2 `oneOutSl_childShips`.** Copy of OneOut:288-331. Change rules:
- `hsl` → `hsl0`;
- the last line `Or.inl <| seqChildRunN_of_composedNW_run … hsl …` becomes
  `childRunN_of_composedNW_runSl … hsl0 … acyc.1 (slotlessParent_noTouch_ofRun L p hdata hins hsl0 hA ran)`.
```lean
theorem oneOutSl_childShips (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hext : ExtInS p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])  -- CHANGED
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat) :
    ChildShips p (n + 1) b D
```
**B3 `groupSl_childShips`.** Copy of GroupServed:294-341 with the same two change rules (`hsl` at :297 → `hsl0`;
the last line as in B2). The binders are verbatim from :294-307:
```lean
theorem groupSl_childShips (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hext : ExtInS p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl0 : p.d.shape.layout.slots = [])     -- CHANGED
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc) :
    ChildShips p (n + 1) b D
```
- **Memory children.** A memory module has `clk` (memory-as-submodule), so `withClockFor` gives case (S) (SeqChildRunN,
  C6 verbatim). No `MemDec`-specific work.

## 5. Stage C — slotless one-output TOP (new file `Tools/ShippingGen2SlotlessTop.lean`)
- **C1 `hierRefineCheck_linked_noRst`** (KS-level). Copy of HierOptRun:532-555+proof. Change rules:
  - delete `hrstIn`, `hrstZ` (:543) and `hfitR` (:548-549);
  - add `(hnoR : Sparkle.IR.OptCheck.seqRegs m = [])` last;
  - in the proof, the `hrstIn'`/`hrstZ'` block (:632-637) is removed, and `refineCheck_transfer` (:643) becomes
    `refineCheck_transfer_noReg … hnoR'` with `hnoR' := seqRegs_openFlat ▸ hnoR` (HierOptRunHNoRst:46);
  - this is exactly HierOptRunHNoRst:56's change rule, moved to `KS`.
- **C2 `TopShipsNC`** (new def, in the new file; Defs is not edited). It is the text of Defs:273-295 with line :283
  deleted. Weakening lemma, proved by `intro`/drop:
  ```lean
  theorem topShips_of_NC (p : Pkg ι dom) (n : Nat) (declName : Name) (b raw : Sparkle.IR.AST.Module) (D : Design) :
      TopShipsNC p n declName b raw D → TopShips p n declName b raw D
  ```
- **C3 `RunFactsNR`.** `RunFacts` (GuardsSound:314-322) without `rst`.
- **C4 `machine_ships_hierC_runNR`.** Copy of FitChain:1073-1232. Change rules:
  - `facts : … → RunFacts` → `RunFactsNR`;
  - the conclusion is `TopShipsNC`-shaped, so the rst/clk antecedents are deleted;
  - new binder `(hZ : NoTouchZ ["rst","clk"] raw.body)`;
  - `hrst` (:1185-1187) becomes: `H` at `slSeedZ b ins`, then A2 to `seedIn b ins`;
  - the `hfitB` run tail transfers on names ∉ Z (`openIns`/instance outs are allocated);
  - `hstR` (:1182) is deleted: `seqRegs b = []` follows from MachineEntry:755-758 + `hsl0`;
  - `hierRefineCheck_linked` (:1218) → C1;
  - the full telescope is a mechanical copy, to be expanded in rev1 as S3 rev1 did.
- **C5 `oneOutSl_topShips`.** Binders = `oneOut_topShipsO` (OneOutTopO:334-350) with `hsl` → `hsl0`.
  - Conclusion `TopShips p (n+1) p.decl b raw D`.
  - Proof by cases on `"rst" ∈ b.inputs.map (·.name)`:
    - **yes** (case S): the OneOutTopO body, with `rst := ` that case (no `core_rst_anyO`);
    - **no:** `topShips_of_NC` ∘ C4 with C3's fields from `core_runFactsHO`'s other fields (their lemmas have no
      `hsl`, ParentDesignO:411-417) and `hZ` from B1.
  - `hW` (OneOutWidth) stays a premise, as in OneOutTopO. It is not claimed.

## 6. Staging
- **A** (pure): A1-A3, plus the controls P1/N1.
- **B:** B1-B3. Needs A.
- **C:** C1-C5. Needs A and B1. Each stage is a separate commit, review and build.

## 7. Controls
- **P1 (pure, required).** A toy module `[assign o := ref a]`, `inst k (a→ref x)`: `NoTouchZ` decided, and A2 applied
  to two seeds that differ only at `"rst"`.
- **N1.** `¬ NoTouchZ ["rst","clk"] [assign o := ref "rst"]`. `calls_ports_sl`'s disjunction is not provable as only
  the comb case for a module with clk/rst (a toy with `extra = [clk,rst]`).
- **P2 (real declaration, PROBE FIRST).** New `Tests/Gen2/S5SlotlessProbe.lean`, logs only, modelled on
  Tests/Gen2/S3P2Probe.lean:1-30. Fixtures (plain `def`s, no `Signal.reg`):
  - (a) `s5oneP` calls a slotless one-output machine child (as `pickByteH`);
  - (b) `s5grpP` calls a `Bool`-result child (as `s3parityH`; gives `instFields ≠ []`);
  - (c) the existing `engineOnce` (MultiInstanceTest:58; case S).
  - Logged for each: the route taken, `slots`, `insts`, `instFields`, whether clk/rst are inputs (case S/C), whether the
    machine arm returns the real module, and whether a `Pkg` exists. `Pkg.comb` (CombPkg:8-12) is "call-free step 1";
    the probe checks whether `machine_next`/`machine_result`/`machineSource` are generated for a parent with calls.
- **V1 vacuity.** `MemParentDataOk` is decided on a probe positive.

## 8. AUDIT clause (checked on the built proofs, stated in the file headers)
1. Expected types: `example`s pin A1-A3, B1-B3, C1, C2, C4, C5 against this freeze. A `CheckPair`-style comparison
   (S3GroupCheck:102-153) is run against the originals at 1b840215: only the listed binders may be dropped or changed.
2. Non-reference, over the full closure (`s3Reach`, S3GroupCheck:238-262, with direct and two-helper negative
   controls). No S5 theorem may reach `SeqKid`, `Tools.ShippingSlotlessClk.*` or `Tools.ShippingSlotlessKidFacts.*`.
3. Non-vacuity: no `False.elim`/`absurd` on the clk binder. C4's proof term must not contain the `TopShips` clk binder,
   because `TopShipsNC` has none.
4. `#print axioms` on every new declaration: standard axioms only.

## 9. Size and build plan
- **Size:** A ~420 lines (A1 ~170, A2 ~150, A3 ~100), B ~330, C ~600. Tests ~250.
- **Build:** `kjob -N sparkle-dev run --issue sparkle-gen2-step -m 16Gi -c 6 -- kjob lake build
  Tools.ShippingGen2SlotlessParent` (then `…ParentRun`, `…SlotlessTop`, `Tests.Gen2.S5Check`, `Tests.Gen2.S5SlotlessProbe`).
- Focused targets only; the lakefile entries are added in the same commit as their file. No AllTests run.

## 10. STOPs and decision items
- **STOP rules:**
  - no new semantic premise: `hZ` is only an internal premise of A3/C4, discharged by B1;
  - no `SeqKid`;
  - no narrowing of FG;
  - no compiler change;
  - no Defs edit.
  - If B1 cannot be proved from the run (for example `closeInstsG` rewrites assigns, or a conn reads `"rst"` in case C),
    stop and report.
- **D1 (`TopShips` vacuity, §2.4):**
  - (a, recommended) prove `TopShipsNC` and record that `TopShips` is vacuous for no-clk modules. A Defs amendment
    (`(∀ t, ins t "clk" = 0)` like rst) is a separate unit;
  - (b) keep `TopShips` and accept the vacuity silently. Not recommended.
- **D2:** whether case S for group slotless parents (engineOnce) needs anything beyond B3. It does not, because C6's
  body is reused.
- **D3:** group slotless `TopShips` is deferred to the StepStmt route, together with group parents with slots.
- **D4:** if P2 finds no real slotless parent with a `Pkg`, S5 is lemma-level only. This is the same situation as the
  S2 vacuity report (STEP_S2_VACUITY_REPORT.md).

## 11. Not claimed
- G-LIFT (`ShipsAt` vs `ShipsRes` in B3);
- G-SERVED;
- the one-output `TopShips` width/range (`hW`/OneOutWidth);
- group `TopShips`;
- `StepStmt`;
- that any real declaration is a slotless parent `Pkg`.
- Not M2 done.
