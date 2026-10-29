# S4 stage B freeze: one-output `RunFacts.wid` (option (a), FOR REVIEW)

- **Issue:** `sparkle-gen2-step`. **Branch:** `par/gen2-spec` at bfb27a51. **Status:** freeze only, no Lean written.
- **Answers:** S4_STAGEB_STOP.md option (a), under the reviewer's four constraints.
- **Withdrawn:** `hkidW1_of_shipsRes` (STOP:29). The width fact below never identifies a `RealChildA` result `y` of the `ran` witness with the served child. `core_callPorts_oneA` does not mention `children`/`RealChildA` at all.

## 1. Which instance, which module, which wire, which call (constraint 1)

**One statement.** Fix `st = Stmt.inst mn iname conns ∈ b.body`; `b.body = M.body`, where `M = raw` (`core_kids_facts_ranA … ran).2.1`, ParentRunFactsA:438). Each side reads this same `st`:

| | `ran` side (`MachineRanA`, ParentRanA:47-60) | trace side (`h : MachineTraceLBX (ServedP …)`, FitChain:921) |
|---|---|---|
| closing | `CloseCalls` left disjunct (Entry:950-951): `closeInsts … (t.inputs.map (·.name)) … children (m₀, d₀) = some (M, D)` | `MachineWired` clause 2 (Entry:667-669) |
| `st` is call `k` | `closeInsts_insts` (Inst:295): `st ∈ m₀.body ∨ ∃ k args child mc, insts[k]? = some args ∧ children[k]? = some child ∧ moduleByName D.modules child.1.name = some mc ∧ CallStmt nIn kI n (t.inputs.map (·.name)) k args mc st`. The left disjunct is excluded by `closedBody_kinds_of_run` (used at ParentRunFactsA:462) | `∃ k args mc, … ∧ CallStmt nIn kI n names k args mc st` with `names = (machPorts p.decl ids cache binders).map (·.name)` |
| module `mc` | `moduleByName D.modules mn = some mc`, using `mn = mc.name` (the last conjunct of `CallStmt`, Inst:201) and `moduleByName_name` (Inst:328) | the `mc` that `Served1P` quantifies over (Defs:231-237) |
| output wire | `callStmt_parts` (OneOutClose:187): `mc.outputs = [outP]`, `(t.inputs.map (·.name))[nIn + k]? = some outW`, every connection is `(outP.name, ref outW)` or an input port with `q.name ≠ outP.name`, hence `x = outW` | `names[nIn + k]? = some outW` |

**Identifying call `k`.** This is a separate obligation from identifying `mc`.
- **The plan:** `core_callPorts_oneA` states the `ran`-side `CallStmt` in the TRACE's port names. `Served1P` holds for EVERY `k` with `CallStmt … names k args mc st` (Defs:233-236). So the `k` the `ran` side produces is passed directly to `Served1P`, for the same `st` and the same `mc`. There is no second index to match.
- **What remains to prove:** the names equality `NamesEq : t.inputs.map (·.name) = (machPorts p.decl ids cache p.d.shape.binders).map (·.name)` for the `ran` witness's `t` and the trace's `ids`/`cache`.
- **How it is obtained (two lemmas, full types in §4; written in `Tools/ShippingGen2OneOutNames.lean`, unbuilt):**
  - `ranA_inputs_machPorts`: on `ran`'s own `run` (the `MReturns synthesizeMixedCertified … (t, d₀)` inside `MachineRanA`), `synthesizeMixedCertified_returns` (MixedEntrySoundness:434-442) + `transition_facts` (Entry:303; third conjunct, as at Entry:1077-1081 and the same step as Entry:1449) give `∃ ids₀ cache₀, ids₀.length = binders.length ∧ machPorts c ids₀ cache₀ binders = t.inputs`. `ids₀`/`cache₀` are the run's own (existential), NOT the trace's. The WF premises come from `ok`, as at ParentPortsA:162-190 / TransitionTyped:66-97. Premises: `ok`, `hbody`, the run. Nothing else.
  - `machPorts_names_indep`: `ids.length = bs.length → ids'.length = bs.length → (machPorts c ids cache bs).map (·.name) = (machPorts c ids' cache' bs).map (·.name)`. A port name is `inputWire a.state …` (MixedInputSoundness:12). `extend` changes `state` using only the binder's name and kind (MixedEntrySoundness:25-38), and `start` sets it to `CircuitM.init` (:456-457). The cache and `ids` reach only `context`, `bools` and `bits`. The comment at Entry:641-642 says the same thing ("names depend on the allocator only"). The proof is an induction on `bs` over two zips (the analogue of `inputPorts_congr`, Entry:96, which fixes ONE list); it shows the whole walk is equal, names and types.
  - **`NamesEq` from the two:** destructure `ran` to get `run`; `obtain ⟨ids₀, cache₀, hl₀, hmp⟩ := ranA_inputs_machPorts d ok hbody run`; then `NamesEq := by rw [← hmp]; exact machPorts_names_indep c cache₀ cache hl₀ hlen`. It uses `hlen` (already a premise of `core_callPorts_oneA`) and no new premise.
- **The instance name is NOT used.** `instStmt` builds `inst{k}_{mc.name}` (Machine:283), and `closeInsts_stmts` (OneOutClose:67) exposes it on the `ran` side. But `CallStmt`'s `iname` is existential (Inst:192, 201), and `MachineWired` does not fix it (Entry:664-669). So the name cannot fix `k` on the trace side.

## 2. The local width fact (constraint 2)

The fact concerns the module `mc` of THE statement `st`, served at THE `k` of §1:
```lean
theorem oneOutWidthAt (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Sparkle.IR.AST.Module} {D : Design} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (hS : Served1P (ShipsRes L P) p.decl p.d.shape raw D ids cache)
    (hsimple : p.d.shape.instFields = [])
    (hnomem : ∀ x ∈ p.d.shape.instTagged,
      x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    (hW : ∀ k, OneOutWidth P p k) (i0 : ι)
    {k : Nat} (hk : k < p.d.shape.insts.length) {args : List Nat} {mc : Sparkle.IR.AST.Module} {st : Stmt}
    (hargs : (p.d.shape.insts.map (·.2.1))[k]? = some args) (hst : st ∈ raw.body)
    (hcs : Tools.ShippingMachineInst.CallStmt (machNIn p.d.shape) p.d.shape.insts.length
      p.d.shape.layout.slots.length ((machPorts p.decl ids cache p.d.shape.binders).map (·.name)) k args mc st)
    (hmod : moduleByName D.modules mc.name = some mc) :
    ∀ outP ∈ mc.outputs,
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some outP.ty.bitWidth
```
**Proof chain** (every step EXISTING unless marked):
1. Apply `hS hsimple k hk args mc st hargs hst hcs hmod` (Defs:231-237).
2. The left disjunct (memory origin) contradicts `nomem_tag hnomem hk` (ChildInv:522).
3. The right disjunct gives `Dc`, `⟨_, q, n', hq, _, hCS⟩ : ShipsRes … (mc, Dc)` (Defs:135-136), and `hDc`.
4. `hCS D hDc hmod i0 : ChildRunN …` (Defs:87-90). Both disjuncts start with `mc.outputs = q.d.shape.layout.outs.map (fun o => ⟨o.name, o.ty⟩)` (SeqChildRunN, MachineDepth:67; CombChildRunN, Defs:63).
5. `CallStmt` gives `mc.outputs = [outP]` (Inst:194). So `q.d.shape.layout.outs = [o]` and `outP = ⟨o.name, o.ty⟩` (`List.map_eq_singleton_iff`).
6. `hW k hk q hq o` (FitChain:893-896) gives binder width `= o.ty.bitWidth = outP.ty.bitWidth`.

No `CallDec`, no `RealChildA`, and nothing about another witness is used. The trace's `ShipsRes` is the one for `(k, mc, st)`.

## 3. `i` (constraint 3)

**Where `RunFacts` is consumed.** In `machine_ships_hierC_run`, `facts hBnd` is destructured at FitChain:1164, BEFORE `intro i` (:1181).
- `hwfB` is used before `i`, at :1175 (`hmf`, which feeds `composed` at :1179).
- `hIW` (`wid`) is used once, at :1221 (`fitX_of_runR`), inside `intro i` and inside the `hacc` branch.

An i-local `facts` (option (ii)) would therefore change the Block C consumer's statement. That is rejected.

**Chosen: option (i), a case split inside `oneOut_topShips`.** It uses `isEmpty_or_nonempty ι`. It adds no premise and no `Nonempty ι`, and it leaves `machine_ships_hierC_run` unchanged.
- **`IsEmpty ι`.** `TopShips p (n+1) p.decl b raw D` (Defs:273-277) is `∃ ids, ids.Nodup ∧ ids.length = … ∧ ∃ cache regs, regs.Nodup ∧ regs.length = p.d.ss.length ∧ ∀ i, …`. Take the EXISTING witness of `h` (`⟨ids, nd, len, cache, regs, rnd, rlen, …⟩`, as at FitChain:921), and close `∀ i` with `isEmptyElim i`. `machine_ships_hierC_run` is not called.
- **`⟨i0⟩`.** Build `wid` with `oneOutWidthAt … i0`. Only step 4 of §2 uses `i0`. The content it extracts (`mc.outputs`) does not depend on `i`.

## 4. Exact types

```lean
theorem core_callPorts_oneA (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ []) (hf0 : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body →
      ∃ mc, moduleByName D.modules mn = some mc ∧
        ∀ p ∈ mc.outputs, ∀ x, (p.name, Sparkle.IR.AST.Expr.ref x) ∈ conns →
          ∃ (k : Nat) (hk : k < d.shape.insts.length) (args : List Nat),
            (d.shape.insts.map (·.2.1))[k]? = some args ∧
            Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
              ((machPorts c ids cache d.shape.binders).map (·.name)) k args mc (Stmt.inst mn iname conns) ∧
            ∃ bn, d.shape.binders[nDecl + k]? = some bn ∧
              Sparkle.IR.RegDedup.declWidth b x = (kindTy bn.2).bitWidth

theorem core_instOutWidthsOk_oneA
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    {c : Name} (d : Tools.ShippingMachineAuto.MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hf0 : d.shape.instFields = [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hnomem : ∀ x ∈ d.shape.instTagged,
      x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)
    {M b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length)
    (cache : IO.Ref (ExprStructMap String))
    (hkidW1 : ∀ (k : Nat) (hk : k < d.shape.insts.length) (args : List Nat) (mc : Sparkle.IR.AST.Module)
        (st : Sparkle.IR.AST.Stmt),
      (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ M.body →
      Tools.ShippingMachineInst.CallStmt (Tools.ShippingMachineEntry.machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
        ((Tools.ShippingMachineEntry.machPorts c ids cache d.shape.binders).map (·.name)) k args mc st →
      Sparkle.IR.Machine.moduleByName D.modules mc.name = some mc →
      ∀ outP ∈ mc.outputs, (d.shape.binders[nDecl + k]?).map
        (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) = some outP.ty.bitWidth) :
    Tools.ShippingHierOpen.instOutWidthsOk (Tools.ShippingMachineLinked.childMap D.modules)
      (Sparkle.IR.RegDedup.declWidth b) b.body = true

-- the two names lemmas (Tools/ShippingGen2OneOutNames.lean, namespace Tools.ShippingGen2)
theorem machPorts_names_indep (c : Name) {bs : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {ids ids' : List FVarId} (cache cache' : IO.Ref (ExprStructMap String))
    (hl : ids.length = bs.length) (hl' : ids'.length = bs.length) :
    (Tools.ShippingMachineEntry.machPorts c ids cache bs).map (·.name) =
      (Tools.ShippingMachineEntry.machPorts c ids' cache' bs).map (·.name)

theorem ranA_inputs_machPorts {tenv : Lean.Environment} {c : Name}
    (d : Tools.ShippingMachineAuto.MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = Tools.ShippingUnifiedSource.quote d.dom
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.bpos j))
      (fun j => Tools.ShippingMixedSourceBridge.inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {logProf : String → IO Unit} {t : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    -- the inner harness run of `MachineRanA` (ParentRanA:47-60): there `logProf := profLogIO b`
    -- and `tenv`, `t`, `d₀` are `ran`'s existentials; `t` is the transition module `CloseCalls` reads
    (run : Tools.ShippingEntrySoundness.MReturns (Sparkle.Compiler.Elab.synthesizeMixedCertified
      (fun e hint top named => Sparkle.Compiler.Elab.translateExprToWire tenv e hint top named) logProf c
      d.shape.binders d.shape.body) (t, d₀)) :
    ∃ (ids₀ : List FVarId) (cache₀ : IO.Ref (ExprStructMap String)),
      ids₀.length = d.shape.binders.length ∧
      Tools.ShippingMachineEntry.machPorts c ids₀ cache₀ d.shape.binders = t.inputs
```
(`ExprStructMap` is `Lean.ExprStructMap`. `core_instOutWidthsOk_oneA`'s binders are `core_callPorts_oneA`'s, in the same order, then `hkidW1`; `core_callPorts_oneA` above is written with the `opens` of ParentRunFactsA:28-46 and means the same names.)
**How each proof is assembled.**
- **`core_callPorts_oneA`:** the proof of ParentRunFactsA:437-561, with these changes:
  - It takes the `hf0` branch of `CloseCalls` (the reverse of :460).
  - It uses `closeInsts_insts` instead of `closeInstsG_insts` (:471), and `callStmt_parts` instead of `callStmtG_outWireF` (:513).
  - It rewrites `CallStmt`'s port list with `NamesEq` (§1), obtained from `ran`'s own `run` by `ranA_inputs_machPorts` and then `machPorts_names_indep … hl₀ hlen`.
  - The `declWidth` part (:519-561) is unchanged: it is about `t` and does not depend on the closing. `hMw` comes from `CloseCalls.some` (Entry:957).
- **`core_instOutWidthsOk_oneA`:** the proof of :585-609, with `hkidW1` in place of `hkidW`, and `st ∈ M.body` obtained through `b.body = M.body`.

**Use in `oneOut_topShips`** (telescope as frozen, S4_CONSUMER_FREEZE:449-467; `ran` is `MachineTaken`):
- **`⟨i0⟩` branch:**
  - `ranA := machineRanA_of_runJQC L.O hA L.T ran` (RanABridge:38).
  - From `h`, take `ids`, `len`, `cache` and `hx.2 : Served1P …` (FitChain:921, 940).
  - Build `wid := core_instOutWidthsOk_oneA L.O p.d … (nDecl := p.kD) hsimple … ranA len cache (fun k hk args mc st hargs hst hcs hmod => oneOutWidthAt L P p hx.2 hsimple hnomem hW i0 hk hargs hst hcs hmod)`. Here `hC`/`hdomB`/`hslots`/`outTy` come from `MemParentDataOk` (MemParent:38-42).
  - Build `facts := fun _ => ⟨core_runFactsHA …, core_linkedWF_ranA …, wid⟩`, with the fields spread out.
  - Then `machine_ships_hierC_run` (FitChain:1073), unchanged.
- **Empty branch:** §3.

## 5. Suppliers

| item | status |
|---|---|
| `closeInsts_insts` Inst:295; `closeInsts_names` ChildServe:137; `callStmt_parts` OneOutClose:187; `moduleByName_name` Inst:328; `nomem_tag` ChildInv:522 | EXISTING |
| `closedPorts_of_run`, `transitionPortTys_of_run`, `declWidth_of_unique`, `instOutWidthsOk_of` (InstWidthsParts:25), `core_kids_facts_ranA` | EXISTING (used at ParentRunFactsA:438-561, 593) |
| `synthesizeMixedCertified_returns`, `transition_facts` Entry:303 | EXISTING |
| `machineRanA_of_runJQC` RanABridge:38; `core_runFactsHA` ParentDesignA:494; `core_linkedWF_ranA` ParentTailsA:197 | EXISTING |
| `machPorts_names_indep`, `ranA_inputs_machPorts` (so `NamesEq`) | WRITTEN, UNBUILT: `Tools/ShippingGen2OneOutNames.lean` (no lakefile entry yet). Uses `synthesizeMixedCertified_returns` MixedEntrySoundness:434, `transition_facts` Entry:303, `List.zip_cons_cons`, `extend`/`start`/`inputPorts`/`machPorts` by definition |
| `core_callPorts_oneA`, `oneOutWidthAt`, `core_instOutWidthsOk_oneA`, `oneOut_topShips` | MISSING (types above) |
| `hW` (G-ONEOUT-WID), `h` (G-SERVED) | premises without a supplier, unchanged (CONSUMER §5). `hBd` is NOT a stage-B premise: the run-local fit chain (S4_FIT_RESULT, c6951eb8) replaced it |

## 6. Stop conditions
- **S1.** `machPorts_names_indep` fails. For example, a port name turns out to depend on `context` (the cache) or on `ids`. Then report that the names are NOT allocator-only, and stop. Option (b) is not to be revived silently.
- **S2.** `ranA_inputs_machPorts` needs a premise that is not derivable from `ok`/`hbody`/`ran`. Name that premise, and stop.
- **S3.** The `IsEmpty ι` branch cannot take `ids`/`cache`/`regs` and their properties from `h`. Stop. Do NOT add `Nonempty ι`, and do NOT change `machine_ships_hierC_run`.
- **S4.** Any step needs a `RealChildA` result `y` of `ran`, or `RealChildA` of the trace's `mc`, to be identified with the other. Stop: that is the withdrawn `hkidW1_of_shipsRes`.
- **S5.** No change to `RunFacts`, `MachineWired`, `CallStmt`, `Served1P`, `TopShips`, FG or DataOk. If one is needed, stop.
