# S5 slotless parents and slotless tops — freeze rev1 (FOR REVIEW — design only, nothing built or proved)

- **Issue:** `sparkle-gen2-step` (S5 of STEP_IFACE_FREEZE.md §4, lines 205-208; order §5 item 4).
- **Branch:** `par/gen2-spec`. Frozen source SHA **1b840215**. Every `file:line` below is at that SHA. The files cited
  are unchanged since d603ac07: `git diff d603ac07..1b840215` touches only gen3 files and `lakefile.lean`. They are
  also unchanged at db76dd89: `git diff --stat 1b840215..db76dd89` touches only `Tools/ShippingGen3*`, `Tests/Gen3/*`,
  `lakefile.lean` and `scripts/` docs.
- **What this is:** the exact types for S5 (new files only), the stages, controls, audit and decision items. No Lean
  is changed by this document, and nothing here is proved.
- **rev1 (review of fd55bcfc):** only these change: §2.4 (D1 wording), §5 (stage C), §6 (stage C list), §7 (P3, N2
  added), §8 (audit items 3, 5), §10 (D1-D4 as decided) and §11 (one line). Stages A and B (§3, §4) are the rev0
  text. Changes in rev1:
  - C2 deletes BOTH the rst and the clk premises (Defs:283 is one line holding both);
  - C1-C5 have complete telescopes;
  - the no-clock branch is published by name as `oneOutSl_topShipsNC` (C5a);
  - the acceptance has a control that inhabits the execution premises (P3).
  - The shared `TopShips` repair is a separate issue, `sparkle-gen2-top-contract`. Its table is
    scripts/gen2/TOP_CONTRACT_REVISION.md. Defs is not edited here.

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
4. **The INNER execution guarantee of `TopShips` is VACUOUS when `"clk"` ∉ `b.inputs`** (a STOP-class finding,
   D1, confirmed by the reviewer).
   - `seedIn b ins t st "clk" = st "clk"` in that case (SeqOptSoundness:892-894). So binder Defs:283
     `∀ t st, seedIn b ins t st "clk" = 0` is refuted by `st := fun _ => 1`. The `∀ i … →` part of Defs:278-295
     therefore holds for every case-(C) module, including S2's slotless leaves.
   - The OUTER `∃ ids … cache regs` with `Nodup`/lengths (Defs:274-277) is not vacuous.
   - Kernel statement: `topShipsInner_of_noClk` / `topShips_iff_outer_of_noClk` in Tools/ShippingGen2TopVacuity.lean
     (:83, :92). That file is untracked, written by another agent, and "WRITTEN, NOT BUILT" (:7).
   - S2's proof does not exploit this: the clk binder is `_` (SlotlessLeaf:202). But the statement carries no
     execution information there.
   - S5's main intermediate result is the clock-free and reset-free `TopShipsNC` (C2, C5a). The weakening
     `topShips_of_NC` gives the old `TopShips`, but that does NOT complete the slotless top guarantee, because its
     target is vacuous in case (C). Carrying the meaningful guarantee to the final root is issue
     `sparkle-gen2-top-contract` (TOP_CONTRACT_REVISION.md).
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

## 5. Stage C — slotless one-output TOP (new file `Tools/ShippingGen2SlotlessTop.lean`) — rev1

**Ambient.** The new file opens as OneOutTopO:27-40 plus FitChain:1060-1068. Below, every binder is written out,
including `ι`/`dom`/`mref`/`cref`, which the originals take from `variable` lines. No new semantic premise is added
(STOP §10). The only extra hypotheses are:
- `hZ`: syntactic, discharged by B1;
- `hnR`/`hnC`: the case discriminant, from the module's actual inputs (A1).

**C1 `hierRefineCheck_linked_noRst`** (KS-level). A copy of HierOptRun:532-555 and its proof.
- **Binders:** delete `hrstIn`, `hrstZ` (:543) and `hfitR` (:548-549). Add `hnoR` last.
- **Proof:** remove the `hrstIn'`/`hrstZ'` block (:632-637). `refineCheck_transfer` (:641-643) becomes
  `refineCheck_transfer_noReg … hnoR'` (RefineNoRst:224-227), with `hnoR' := (seqRegs_openFlat m _ _).trans hnoR`
  (HierOptRunHNoRst:46).
- This is HierOptRunHNoRst:56's change rule, moved to `KS`.
```lean
theorem hierRefineCheck_linked_noRst {σ : Type} (KS : KStep σ) (hloc : KSLocal KS)
    (children : String → Option (Module × WEnv)) {m o : Module}
    (hchk : Sparkle.IR.RefineCheck.hierRefineCheck m o = true)
    (hwfM : linkedWF children m.body = true) (hwfO : linkedWF children o.body = true)
    (hndM : (instNames m.body).Nodup) (hndO : (instNames o.body).Nodup)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ child cwe,
      children mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hOutM : ∀ w ∈ bodyInstOuts children m.body, w ∈ (openIns m).map (·.name))
    (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    {T : Nat} {s : KState σ} {envs : List Env}
    (hrun : runModuleTG KS (declWidth m) children m.body (seedIn m ins) T s = some envs)
    (hfitX : ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name),
      (envs[j]'hj) x < 2 ^ declWidth m x)
    (hnoR : Sparkle.IR.OptCheck.seqRegs m = []) :                                       -- NEW (replaces :543, :548-549)
    o.inputs = m.inputs ∧ o.outputs = m.outputs ∧
    ∃ envsO, runModuleTG KS (declWidth o) children o.body (seedIn m ins) T s = some envsO ∧
      envsO.length = envs.length ∧
      ∀ p ∈ m.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envs.length),
        (envsO[j]'hj) p.name = (envs[j]'hj') p.name
```

**C2 `TopShipsNC`** (new def in the new file; Defs is not edited).
- It is the text of Defs:273-295 with line :283 deleted. That one line holds BOTH premises,
  `(∀ t, ins t "rst" = 0)` and `(∀ t st, seedIn b ins t st "clk" = 0)`, so both are gone.
- Every other line is verbatim, including the slot-init premise. With `slots = []` that premise is vacuously
  satisfiable, not contradictory.
```lean
def TopShipsNC {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = p.d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
        (fun j => (p.extBS i bools bits j).val (T - 1 - t))
        (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
      (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
      -- Defs:283 DELETED: neither `ins t "rst" = 0` nor `seedIn b ins t st "clk" = 0`
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        p.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ResetNk n raw D kids →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
        st0 x < 2 ^ declWidth b x) →
      ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
          (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          p.d.shape.layout.outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]'hj) o.name = f j

/-- Weakening, by `intro`/drop of the two antecedents. Recorded as a projection only: in case (C) its target's inner
part is vacuous (§2.4), so this lemma is NOT the slotless top guarantee. -/
theorem topShips_of_NC {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) :
    TopShipsNC p n declName b raw D → TopShips p n declName b raw D
```

**C3 `RunFactsNR`.** `RunFacts` (GuardsSound:314-322) without `rst` (:320). There is a projection from `RunFacts`.
```lean
structure RunFactsNR (C : String → Option (Sparkle.IR.AST.Module × WEnv)) (b : Sparkle.IR.AST.Module) : Prop where
  gate : Sparkle.IR.RefineCheck.hierGate b = true
  wfB : linkedWF C b.body = true
  ndB : (Tools.ShippingHierState.instNames b.body).Nodup
  self : Tools.ShippingHierPremisesBase.noSelfRead C b.body = true
  outs : Tools.ShippingHierPremisesBase.outsExtracted C b = true
  wid : instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth b) b.body = true

theorem RunFacts.toNR {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {b : Sparkle.IR.AST.Module}
    (h : Tools.ShippingGuardsSound.RunFacts C b) : RunFactsNR C b
```

**C4 `machine_ships_hierC_runNR`.** A copy of FitChain:1073-1232.

Binder and conclusion changes, line by line:
- `hinitW` (FitChain:1118) is deleted. It is used only for `hstR` (:1182-1183), which is deleted.
- New binders after `houtTy` (:1117): `hslots`, `hsl0`.
- `facts` (:1129-1130) targets `RunFactsNR`.
- New binders after `facts`: `hnR`, `hnC`, `hZ`.
- Conclusion line :1145 is deleted, so the conclusion is `TopShipsNC`'s body at `d`/`src`/`ext`/`extB`/`kD`.

Proof changes:
- The `obtain … hrstIn …` at :1164 loses `hrstIn`.
- The `intro` at :1181 loses `hrstZ hclk`.
- `regs = []` follows from `rlen`, `hslots` and `hsl0`. So `H`'s register and slot premises are discharged by
  `simp at hr`, as at SlotlessLeaf:209-211.
- `hrst` (:1184-1187) and the `H` call (:1188-1189) become: `H` at `seed := slSeedZ b ins` (A3's def).
  - `SourceInputs` comes from `hsrc t (zeroed st)`.
  - rst/clk come from `hnR`/`hnC` and `hbI` (:1174). `slSeedZ` then reads the zeroed state.
- Then A2 (`runModuleTG_seed_offZ`) at `Z := ["rst","clk"]` (with `hbB`, :1172) transfers to `seedIn b ins`.
  - `hobs` transfers because every output name is `∉ Z` (`outName_ne_clk`, CallsAssemblyG:59-61).
  - `KSBoundedRun` (Gen2Fit:28-31) transfers because it reads only `.ref` instance conns, which `hZ`'s inst clause
    keeps off `Z`.
- `hierRefineCheck_linked` (:1218-1221) becomes C1, with `hnoR := seqRegs b = []`. This needs the new internal
  lemma `seqRegs_nil_of_wired_sl`: `wired`'s register clause (MachineEntry:755-758) with `hsl0` means no register
  statement, and `hbB` moves that to `b`.
- Lines :1190-1232 are otherwise verbatim.

```lean
theorem machine_ships_hierC_runNR {n : Nat} (hloc : ∀ D : Design, KSLocal (KSn (childMap D.modules) n))
    (Bnd : CtxBnd)
    (C : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    {declName : Name} (d : MachineData) {kD : Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc srcL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {extL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extBL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design →
      MachineTraceLB declName d m design dom srcL extL extBL lsrc)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design} {b : Sparkle.IR.AST.Module},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule m ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule m)) →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design → Tools.ConeFold.memFree m.body →
      Tools.ShippingGen2Fit.ComposedNWRegsF n declName d kD m design dom src ext extB
        (fun regs => ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → f.width ≤ declWidth b r))
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hslots : d.ss.length = d.shape.layout.slots.length)                                -- NEW
    (hsl0 : d.shape.layout.slots = [])                                                  -- NEW (hinitW :1118 DELETED)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : C mctx mref cctx cref)
    (facts : Bnd mctx mref cctx cref w raw D → RunFactsNR (childMap D.modules) b)       -- CHANGED
    (hnR : "rst" ∉ raw.inputs.map (·.name))                                             -- NEW (case C)
    (hnC : "clk" ∉ raw.inputs.map (·.name))                                             -- NEW (case C)
    (hZ : NoTouchZ ["rst", "clk"] raw.body) :                                            -- NEW (B1)
        Bnd mctx mref cctx cref w raw D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT n),
            (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
              (fun j => (extB i bools bits j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            -- FitChain:1145 DELETED (rst and clk)
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            ResetNk n raw D kids →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
              st0 x < 2 ^ declWidth b x) →
            ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T
                ⟨st0, mems, kids⟩ = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j
```
**Proof risk (stated, not hidden):** the run `H` gives is on `m.body = raw.body` (ComposedNWRegsF, FitChain:675-709).
So A2 is applied on `raw.body`, and the result is moved to `b` by `hbB`/`hbW` (:1172-1173), as at :1190-1192. If
`mergeChecked` changes the body before `hbr` (:1168-1171), the step goes through `hbr` exactly as in the original.

**C5a `oneOutSl_topShipsNC` — the no-clock branch, PUBLISHED BY NAME** (S5's main top result).
- **Binders:** those of `oneOut_topShipsO` (OneOutTopO:334-350), with `hsl` → `hsl0` and one new case binder `hrst`.
- **Conclusion:** `TopShipsNC`.
- **Proof:**
  - The `ι`-empty branch is OneOutTopO:353-357 with `TopShipsNC`.
  - Otherwise, `hnC` comes from A1 (`calls_ports_sl … |>.2.1`, resolved by `hrst`) on the trace's `wired`.
  - `facts : RunFactsNR` is built field by field from the lemmas OneOutTopO:376-394 uses. None takes `hsl`:
    - `core_hierGate_anyO` (ParentDesignO:49), `core_instNames₁O` (:121), `core_noSelfRead₁O` (:147),
      `core_outsExtracted₁O` (:179);
    - `core_linkedWF_ranO` (ParentTailsO:144), `core_instOutWidthsOk_oneO` (OneOutTopO:195).
    - `core_runFactsHO` (ParentDesignO:398-419) is NOT used, because it takes `hsl` for `rst` (:418).
  - `hZ := slotlessParent_noTouch_ofRun L p hdata hins hsl0 hA ran hrst` (B1).
  - `hNWF` and `composed` as OneOutTopO:396-415. `hslots` from `hdata.rows` (OneOutTopO:360).
  - Then C4.
```lean
theorem oneOutSl_topShipsNC {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hord : ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
      (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])  -- CHANGED
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hcore : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hW : ∀ k, OneOutWidth P p k)
    (hrst : "rst" ∉ raw.inputs.map (·.name))                                                                  -- NEW (case C)
    (n : Nat) :
    TopShipsNC p (n + 1) p.decl b raw D
```
**C5S `oneOutSl_topShipsS`** (case S).
- **Binders:** as C5a, with `hrst : "rst" ∈ raw.inputs.map (·.name)`.
- **Conclusion:** `TopShips p (n + 1) p.decl b raw D`.
- **Proof:** the OneOutTopO:351-415 body. The `rst` field (:389-390) becomes `hbI ▸ hrst`, where `hbI` is derived as
  at FitChain:1168-1174; `core_rst_anyO` is not used.
- **Meaningful:** A1 gives `"clk"` ∈ `raw.inputs` in this case, and `b.inputs = raw.inputs`. So Defs:283's clk
  binder reads `ins t "clk"` and is satisfiable. This is not the vacuous case of §2.4.

**C5 `oneOutSl_topShips`** (the rev0 statement, kept as a corollary). Binders as C5a without `hrst`; conclusion
`TopShips p (n + 1) p.decl b raw D`. The proof is `by_cases "rst" ∈ raw.inputs.map (·.name)`:
- yes: C5S;
- no: `topShips_of_NC ∘ C5a`.

In the no-branch the conclusion's inner part is vacuous (§2.4), so **C5 is not the slotless top guarantee**. C5a is.
C5 exists only so that callers stated against the current `TopShips` (`StepStmt`, Defs:300-313) typecheck. The
meaningful guarantee reaches the final root only through `sparkle-gen2-top-contract`.

- `hW` (OneOutWidth) and `hord` stay premises in C5a/C5S/C5, as in OneOutTopO. They are not claimed.

## 6. Staging
- **A** (pure): A1-A3, plus the controls P1/N1.
- **B:** B1-B3. Needs A.
- **C:** C1-C4, C5a, C5S, C5, plus the control P3 (§7). Needs A and B1. Each stage is a separate commit, review
  and build.

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
- **P3 (execution premises inhabited; REQUIRED for the stage-C acceptance).** New `Tests/Gen2/S5TopControl.lean`.
  Checking for the absence of `False.elim` is not enough. P3 shows that the premises of the case-(C) guarantee can
  be met and that the conclusion is then actually used.
  - **P3-core (pure, concrete; required whatever P2 finds).**
    - **The module.** A concrete case-(C) module `m0`:
      - inputs `[a]` only, so no `"clk"`/`"rst"`;
      - body `[inst c0 k [(i, ref "a"), (y, ref "x")], assign "o" := ref "x"]`;
      - in a design `d0` whose comb child `c0` is `[assign "y" := ref "i"]`.
    - **The run.** At concrete `T = 2` with `ins t "a" = t + 3`, `st0 := fun _ => 0` and the zero kid state `kids0`.
      The `memsOf … = 0` clause of `ResetN` (MachineDepth:55) holds; `c0` has no register or memory statement.
    - **(i) Premises.** Every premise of `TopShipsNC`'s inner part that does not mention the package witnesses
      `ids`/`cache` is proved at `m0` by `decide`/`simp`:
      - the passthrough over `regs = []`;
      - the slot inits over `slots = []`;
      - `ResetNk 1 m0 d0 kids0`;
      - the input fit and the `st0` fit.

      `SourceInputs` is the one premise that does mention them, so the run is stated directly at `seedIn m0 ins`.
    - **(ii) Conclusion used.** `NoTouchZ ["rst","clk"] m0.body` is decided. The run at `slSeedZ m0 ins` is computed
      (`rfl`). A2 (`runModuleTG_seed_offZ`) gives `envs₂` at `seedIn m0 ins`. Its conclusion is then used to derive
      `(envs₂[1]) "o" = 4`, which is cross-checked against direct evaluation of
      `runModuleTG … (seedIn m0 ins) 2 …` by `rfl`.
    - **(iii) Contrast with the old binder.** Defs:283's clk binder at `m0` is refuted by `not_seedIn_clk_zero`
      (Tools/ShippingGen2TopVacuity.lean:45, or a local copy if that file is not built). The `TopShipsNC`
      premises in (i) all hold. So (ii) is reached without any `False.elim`/`absurd` on a premise.
  - **P3-pkg (real declaration; conditional on P2 (a)).**
    - **If** the probe finds a real one-output slotless parent package `s5onePkg` in case (C):
      - `s5one_topShipsNC`: C5a instantiated, conditional only on the compile-run premises, as `pbh_ships`
        (Tests/Gen2/SlotlessLeafInstance.lean:45-57) is;
      - plus an exercise corollary that discharges every inner premise for an arbitrary stream:
        - `SourceInputs` by `sourceInputs_of_vals` (MachineSeqChild:35-41) at the stream's values;
        - `st0 := 0` and `kids := kids0` as in P3-core;
        - the input fit from the stream's widths;
      - the corollary concludes the output equations with no execution antecedent left.
    - **If** the probe finds none, P3-pkg is recorded as unavailable (D4).
- **N2 (D1 at a real module, recorded, not required).** The S2 instance `pbhPkg` is case (C): `pbh_noI`/`pbh_slots0`
  (SlotlessLeafInstance:40-42); its inputs are allocated by `slotless_inputs_alloc_ofRun`, SlotlessLeaf:397.
  `topShips_iff_outer_of_noClk` (TopVacuity:92) applied there shows that `pbh_ships`'s `TopShips` conjunct is the
  outer existence only. That conjunct gets its non-vacuous replacement through TOP_CONTRACT_REVISION.md (unit
  U-TOP-S2).

## 8. AUDIT clause (checked on the built proofs, stated in the file headers)
1. Expected types: `example`s pin A1-A3, B1-B3, C1, C2, C4, C5 against this freeze. A `CheckPair`-style comparison
   (S3GroupCheck:102-153) is run against the originals at 1b840215: only the listed binders may be dropped or changed.
2. Non-reference, over the full closure (`s3Reach`, S3GroupCheck:238-262, with direct and two-helper negative
   controls). No S5 theorem may reach `SeqKid`, `Tools.ShippingSlotlessClk.*` or `Tools.ShippingSlotlessKidFacts.*`.
3. Non-vacuity:
   - no `False.elim`/`absurd` on a clk/rst premise;
   - C4's and C5a's proof terms must not mention `TopShips` or `topShips_of_NC`, because `TopShipsNC` has neither
     binder (checked by a constant-closure scan as item 2);
   - P3-core (§7) builds and is exercised.
5. Naming: the no-clock branch is exported as `Tools.ShippingGen2.oneOutSl_topShipsNC` with the §5 C5a type, pinned by
   an `example`. Item 1's pin list is extended with C3, C5a and C5S.
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
- **D1 — DECIDED (reviewer, on fd55bcfc): the vacuity is confirmed.**
  - When `"clk"` ∉ inputs, Defs:283's `∀ t st, seedIn b ins t st "clk" = 0` is contradictory (SeqOptSoundness:892-894),
    so `TopShips`' INNER execution guarantee is vacuous. The OUTER `∃ ids/cache/regs` is not.
  - `TopShipsNC` (C2), via C5a `oneOutSl_topShipsNC`, is S5's main intermediate result.
  - Weakening to the old `TopShips` (`topShips_of_NC`, C5) does NOT complete the slotless top guarantee.
  - The shared repair is the new issue `sparkle-gen2-top-contract`, a dependency of T1 assembly. Its revision table
    is scripts/gen2/TOP_CONTRACT_REVISION.md. Defs is not changed in S5.
- **D2 — DECIDED: case S reuses C6.**
  - In A3/B2/B3, case (S) is Gen2C6:59-137 verbatim. For group slotless parents with clk/rst (engineOnce) nothing
    beyond B3 is needed.
  - To be CONFIRMED AT BUILD: the B3 term's case-S branch must reach `seqChildRunN_of_composedNW_run`'s body
    (Gen2C6:29-55) or its verbatim copy in A3. The audit item 2 closure lists it.
- **D3 — DECIDED: group slotless `TopShips` stays RESIDUAL.** It is blocked as for group parents with slots
  (S3_GROUP_FREEZE §5 :364). It is listed as open in the M2 acceptance and in TOP_CONTRACT_REVISION.md §5.
- **D4 — DECIDED: without a real `Pkg`, coverage stays INCOMPLETE.**
  - If P2 finds no real slotless parent with a `Pkg`, S5 is lemma-level only (P3-core only; P3-pkg unavailable). This
    is the same situation as STEP_S2_VACUITY_REPORT.md.
  - It is recorded as a coverage gap, not as M2 progress on real declarations.

## 11. Not claimed
- G-LIFT (`ShipsAt` vs `ShipsRes` in B3);
- G-SERVED;
- the one-output `TopShips` width/range (`hW`/OneOutWidth);
- group `TopShips`;
- `StepStmt`;
- that any real declaration is a slotless parent `Pkg`;
- that the shared `TopShips` (Defs:273-295) or any statement over it (StepStmt/LeafStmt/MemParentStmt/T1Stmt) now
  carries the slotless guarantee. That is `sparkle-gen2-top-contract`.
- Not M2 done.

## rev1.1 — review notes on a966486b (binding; supersede conflicting text above)
1. **P3-core is an execution control of A2 only.** It does NOT check `SourceInputs`, the outer ids/cache/regs witness,
   C4 or C5a; the text above must not be read as such. A separate control at package level (P-TOP of
   TOP_CONTRACT_REVISION.md) checks the NC/R-G root.
2. **`outNameOk` supply for C4's `outName_ne_clk`** (CallsAssemblyG:59-61): `houtTy` alone does not give it. C4/C5a must
   take it from the run (`outsExtracted` + `NoTouchZ`, or an equivalent named lemma), stated as a supplier with its
   full type before the C4 proof; it is not an extra premise.
3. Instances that ASSUME a real run (run premises as hypotheses) are kept distinct from controls whose premises are
   all supplied.
