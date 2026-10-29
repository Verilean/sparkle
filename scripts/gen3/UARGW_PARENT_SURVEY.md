# U-ARGW-PARENT survey rev0: the argument-wire width lemmas `core_callArgPorts_oneA` / `_ranA` (DPORT L2)

**FOR REVIEW — design only, nothing built or proved.** No Lean file, lakefile or shared definition was written or
edited, and no Lean was run. Statements are TEXT ONLY.

Issue `sparkle-gen3-uargw-parent`. Base: `par/gen2-spec` at **10377764**. All `file:line` citations are at 10377764;
the `.lean` files are identical to 649a6bf5. Route: DPORT_ROUTE_REPORT.md rev1 §1 row L2, §2 (proposed text), §3
item 2. Templates: `core_callPorts_oneA` (Tools/ShippingGen2OneOutTop.lean:51-193) and `core_callPorts_ranA`
(Tools/ShippingParentRunFactsA.lean:410-562).

## 0. Finding: the width part does not depend on the instance
Both templates have two halves:
- (I) **instance part**: which statement, which output port, which wire, and (ranA) which `RealChildA` child.
- (W) **wire-width part**: for a transition input `q = t.inputs[machNIn + e]`, its binder
  `binders[nDecl + e]` exists, and `declWidth b q.name = (kindTy bn.2).bitWidth`.

(W) uses only the run facts `closedPorts_of_run`, `transitionPortTys_of_run`, `hMw`, `hcl` and `hpost`. It does not
use the instance, `hf0`/`hfne`, `hnomem`, `outTy`, `hkidP` or `RealChildA`. Of `hcc`, only the branch-independent
`hcc.some` is needed (oneA :97, ranA :459, both taken BEFORE the `CloseCalls` branch split).

An argument wire `argWs[j] = names[nIn + kI + n + args[j]]` (CallStmt MachineInst:193, CallStmtG MachineInstG:23) is
such a transition input, at index `e := kI + n + a`. The arg-side lemma is therefore one parent-kind-independent core
`core_inputWidth_A` plus two thin corollaries. Its premise set is strictly smaller than either template's.

## 1. Step map
Columns: template lines; what the step does; the argument-side analogue. Verdicts: **V** (reusable verbatim), **I**
(verbatim after the index change `k`/`e.1` ↦ `e`), **D** (dropped, not needed), **N** (needs a new small step or lemma,
stated), **STOP** (no route).

### 1.1 `core_callPorts_oneA` (OneOutTop:51-193)
| # | lines | step | arg analogue | verdict |
|---|---|---|---|---|
| o1 | :75-76 | `hbody' : b.body = M.body` via `core_kids_facts_ranA` (needs `hnomem`, `outTy`) | only used to move `hst` to `M.body` for `closeInsts_insts`; the arg lemma takes the wire from the TRACE's `CallStmt`/`mapM`, not from `b.body` | **D** (removes premises `hnomem`, `outTy`, `hf0`) |
| o2 | :78-84 | `hbw`: cleanup/merge keep non-zero wires (`dropZW_wires` OutsExtractedParts:182, `mergeChecked_ports`) | same | **V** |
| o3 | :85-91 | `hbsub`: `b.wires ⊆ M.wires` (`dropZW_wires_sub` InstWidthsParts:79) | same | **V** |
| o4 | :93-97 | destructure `ran` (MachineRanA ParentRanA:47); `hins` kills the call-free branch; `hMw` from `hcc.some` | same | **V** |
| o5 | :99-104 | `hI`: the `hf0` branch of `CloseCalls` → `closeInsts … = some (M, D)` | not needed | **D** |
| o6 | :105 | `hseq0` (`closedBody_kinds_of_run`): non-instance statements | not needed | **D** |
| o7 | :106-107 | `closedPorts_of_run` (ClosedPorts:205-221): `t.inputs = PI ++ ls`, `PI.length = machNIn`, `hinW` (every input a closed-machine wire, width ≠ 0) | same | **V** |
| o8 | :108-109 | `transitionPortTys_of_run` (TransitionPortTys:143-161): `hwnd`, `hwal`, `hinWt`, `P1 P2`, `hP2d`, `hP2ty` (P2 typed by `binders.drop nDecl`, length `kI+n+lets`: LET ports included) | same | **V** |
| o9 | :110 | `hls : P2 = ls` | same | **V** |
| o10 | :112-115 | NamesEq: `ranA_inputs_machPorts` (OneOutNames:83) + `machPorts_names_indep` (:29) ⇒ `t.inputs.map name = (machPorts c ids cache binders).map name` for ANY `ids` of the binders' length and any `cache` | same (it ties the trace's `ids`/`cache` to the run) | **V** |
| o11 | :116-127 | intro the statement; `closeInsts_insts` (MachineInst:295); `callStmt_parts` (OneOutClose:187); `moduleByName_name` (MachineInst:328) | replaced: the wire comes from the premise `names[machNIn + e]? = some w` (core) or from `mapM_some` (MachineInst:167) on CallStmt's `mapM` at `j` (corollary) | **N** (corollary step, no new lemma) |
| o12 | :129-131 | `hk` from `hargs` | not needed in the core; in the corollary not needed either (the binder exists by o17) | **D** |
| o13 | :133-137 | `hcs'`: the SAME CallStmt in trace names | not needed: the corollary's premise is already in trace names | **D** |
| o14 | :139-146 | output port = `outP`; `x = outW` (conns classification) | indexed form: `x := argWs[j]` given by premise, no conns reasoning. A conns form (`(p.name, ref x) ∈ conns`, `p ∈ argPorts mc`) needs **new lemma L-AW** below | **N** (only for the conns form) |
| o15 | :147-158 | `hget`, `cases hq : t.inputs[machNIn + k]?`, `hqm`, `hinW` | at index `machNIn + e`; from the trace-name premise by `rw [← hNames, List.getElem?_map]` | **I** |
| o16 | :159-166 | `hql : ls[k]? = some q` from `PI ++ ls`, `hPI` | `k ↦ e` | **I** |
| o17 | :167-176 | `hlt`, `hbn`, `hty` (via `hP2ty`), `hbn' : binders[nDecl + k]?` | `k ↦ e` | **I** |
| o18 | :178-188 | `huniq`: `q` is the only wire of its name in `b` (`closeMachine_wires_sup` TransitionPortTys:92, `closeLets_wires` :76, `port_of_name` :68, `nextName_not_allocated` MachineClose:81) | same | **V** |
| o19 | :189-192 | `hdw : declWidth b q.name = q.ty.bitWidth` (`declWidth_of_unique` InstWidthsParts:54, `kindTy_shape` TransitionPortTys:59) | same | **V** |
| o20 | :193 | assemble `⟨k, hk, args, hargs, hcs', _, hbn', …⟩` | assemble `⟨_, hbn', …⟩`; in corollaries rewrite `nDecl + (kI + n + a)` to `nDecl + (kI + (n + a))` (`Nat.add_assoc`, or `show … by omega`) to match `callArgsOkAt` (Adapt:76) | **N** (one `rw`) |

### 1.2 `core_callPorts_ranA` (RunFactsA:410-562)
| # | lines | step | arg analogue | verdict |
|---|---|---|---|---|
| r1 | :437-438 | `hbody'` | as o1 | **D** (removes `hnomem`, `outTy`, `hfne`, `hkidP`) |
| r2 | :440-453 | `hbw`, `hbsub` | as o2/o3 | **V** |
| r3 | :455-459 | `ran` destructure; `hMw`, `L`, `hLinst`, `hperm` from `hcc.some` | only `hMw` | **V** (drop the unused names) |
| r4 | :460-461 | the `hfne` branch → `hG` (closeInstsG) | not needed | **D** |
| r5 | :462-467 | `hseq0`, `closedPorts_of_run`, `transitionPortTys_of_run`, `hls` | as o6 (D), o7-o9 (V) | **V**/**D** |
| r6 | :468 | `hreal` (`hlenC`, `hallC`) | not needed | **D** |
| r7 | :469-473 | intro; `closeInstsG_insts` (MachineInstG:228) | replaced by the premise (as o11) | **N** |
| r8 | :475-500 | `hrealE`: every entry's module is `y.1` of a `RealChildA` child (`closeInstsG_names` MachineInstG:369, `nomem_tag`) | **not needed**: the arg width is a property of the parent's let wire, not of the child. This is exactly the R3 identification that DPORT §1 L1' marks CONDITIONAL; the arg lemma AVOIDS it | **D** |
| r9 | :501-509 | `hap` (via `hkidP`), `hmn` (`callStmtG_name` OutsExtractedParts:121), `hfind'` | not needed | **D** |
| r10 | :510-515 | `callStmtG_outWireF` (InstWidthsParts:93): output wire `= names[nIn + e.1]` | replaced: `mapM_some` on CallStmtG's `args.mapM` (MachineInstG:23) at `j` | **N** (no new lemma) |
| r11 | :517-541 | `hget`, cases, `hqm`, `hinW`, `hql`, `hlt`, `hbn`, `hty`, `hbn'` (all on `t.inputs` names; ranA has NO NamesEq) | index `e`; plus o10 (NamesEq) to start from trace names | **I** + **V** (o10 imported from oneA) |
| r12 | :546-560 | `huniq`, `hdw` | same | **V** |
| r13 | :561-562 | assemble | as o20 | **N** |

**STOP points: none found** for the parent half. Two risks remain. (i) The core works on `t.inputs` and reaches trace
names only through o10. If a consumer holds `names` from a DIFFERENT `ids` of the binders' length, o10 still applies
(`machPorts_names_indep` is for any `ids`/`cache`). (ii) If the consumer's `b` is not one of the two `hpost` forms,
o2/o3 fail. Every current consumer has `hpost` (S4/OneOut/MemShips).

## 2. Proposed statements (full text; new file `Tools/ShippingGen3ArgWidth.lean`)
Ambient: `import Tools.ShippingGen2OneOutTop` (it brings OneOutNames, RunFactsA, TransitionPortTys, ClosedPorts,
InstWidthsParts), `set_option autoImplicit false`, namespace `Tools.ShippingGen3ArgWidth`, and the opens of
OneOutTop:26-45 verbatim. `maxHeartbeats 4000000` as the templates.

```lean
/-- **(W) Every transition input wire of a closed machine run has its binder's declared width in `b`.** No instance,
no parent kind, no child. -/
theorem core_inputWidth_A {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)) :
    ∀ (e : Nat) (w : String),
      ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape + e]? = some w →
      ∃ bn, d.shape.binders[nDecl + e]? = some bn ∧
        Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth

/-- **(L2, one-output parent)** every argument wire of a call's `CallStmt` (trace names). -/
theorem core_callArgPorts_oneA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)) :
    ∀ (k : Nat) (args : List Nat) (mc : Sparkle.IR.AST.Module) (st : Stmt),
      Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
        ((machPorts c ids cache d.shape.binders).map (·.name)) k args mc st →
      ∀ (argWs : List String),
        args.mapM (fun j => ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape +
          d.shape.insts.length + d.shape.layout.slots.length + j]?) = some argWs →
        ∀ (j a : Nat) (w : String), args[j]? = some a → argWs[j]? = some w →
          ∃ bn, d.shape.binders[nDecl + (d.shape.insts.length + (d.shape.layout.slots.length + a))]? = some bn ∧
            Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth

/-- **(L2, group parent)** the same for a group statement `CallStmtG`. -/
theorem core_callArgPorts_ranA {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true) (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    {ids : List FVarId} (hlen : ids.length = d.shape.binders.length) (cache : IO.Ref (ExprStructMap String)) :
    ∀ (args : List Nat) (outs : List (Nat × String)) (mc : Sparkle.IR.AST.Module) (st : Stmt),
      Tools.ShippingMachineInstG.CallStmtG (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
        ((machPorts c ids cache d.shape.binders).map (·.name)) args outs mc st →
      ∀ (argWs : List String),
        args.mapM (fun j => ((machPorts c ids cache d.shape.binders).map (·.name))[machNIn d.shape +
          d.shape.insts.length + d.shape.layout.slots.length + j]?) = some argWs →
        ∀ (j a : Nat) (w : String), args[j]? = some a → argWs[j]? = some w →
          ∃ bn, d.shape.binders[nDecl + (d.shape.insts.length + (d.shape.layout.slots.length + a))]? = some bn ∧
            Sparkle.IR.RegDedup.declWidth b w = (kindTy bn.2).bitWidth
```
The `CallStmt`/`CallStmtG` premise of the two corollaries is carried for the consumer's convenience and is not used
by the proof (only the `mapM` is). It ties the `argWs` to a statement for the later PortTie composition; if review
prefers, it can be dropped. No `hf0`/`hfne` is needed: the corollaries are the same statement with different
witnesses. The names `_oneA`/`_ranA` follow DPORT §2.

**Optional new small lemma L-AW** (only if the conns form of PortTie is chosen; o14):
```lean
theorem callStmt_argWire {nIn kI n k : Nat} {names : List String} {args : List Nat} {mc : Sparkle.IR.AST.Module}
    {mn iname : String} {conns : List (String × Sparkle.IR.AST.Expr)}
    (h : Tools.ShippingMachineInst.CallStmt nIn kI n names k args mc (Stmt.inst mn iname conns))
    {p : Port} (hp : p ∈ Tools.ShippingMachineCompose.argPorts mc) {x : String}
    (hx : (p.name, Sparkle.IR.AST.Expr.ref x) ∈ conns) :
    ∃ (argWs : List String) (j : Nat),
      args.mapM (fun j => names[nIn + kI + n + j]?) = some argWs ∧
      (Tools.ShippingMachineCompose.argPorts mc)[j]? = some p ∧ argWs[j]? = some x
```
Proof: `callStmt_parts` (OneOutClose:187-197) classifies `hx`. The output disjunct is excluded by CallStmt :199
(`outP.name ∉ argPorts names`). The argument disjunct gives `(q, aw) ∈ zip (argPorts mc) argWs` with `q.name =
p.name`. Then `q = p` by `Nodup` of the arg-port names (CallStmt :197) and `List.mem_zip`/`List.getElem_zip`
indexing. About 30 lines. The group sibling `callStmtG_argWire` uses CallStmtG :25 and :28-29 (fields ∉ inputs), and
excludes the clk/rst block because `p ∈ argPorts mc` is neither clk nor rst; about 35 lines.

## 3. Proof of the core (route, from §1)
`intro e w hw`; then o2, o3, o4 (with `hins`), o7, o8, o9, o10. Rewrite `hw` with `← hNames` and
`List.getElem?_map`. Then `cases hq : t.inputs[machNIn d.shape + e]?` (o15), o16-o19 with `k := e`, and the
assembly `⟨_, hbn', by rw [← hget, hdw, hty]⟩`. The corollaries: `obtain ⟨-, hgetW⟩ := mapM_some _ _ _ hm`, and
`hgetW j hj` (with `hj` from `args[j]? = some a`) gives `y` with `names[nIn+kI+n+args[j]]? = some y ∧ argWs[j]? = some
y`. So `y = w` and `args[j] = a`. Then rewrite the index `nIn + kI + n + a = nIn + (kI + n + a)` (omega), apply the
core at `e := kI + n + a`, and rewrite `nDecl + (kI + n + a) = nDecl + (kI + (n + a))`.

## 4. What it gives, and what it does not
- L2 gives `declWidth b argWs[j] = (kindTy binders[nDecl+kI+n+a].2).bitWidth`, the LEFT half of `callArgsOkAt`
  (Adapt:73-77) through `nDecl = p.kD` (`closingNDecl_eq_kD`, S4_CONSUMER_FREEZE.md:510-512).
- **It alone supplies nothing for the row.** To reach `callArgsOkAt p.d p.kD k q.portWidths`, two more pieces are
  needed. One is L5, `(argPorts mc).map (·.ty.bitWidth) = q.portWidths` (UCHILD_PORTTYS_TABLE.md; a shared-interface
  export). The other is L6, the emitted tie `declWidth b argWs[j] = (argPorts mc)[j].ty.bitWidth`, which is still
  **UNSUPPLIED; no derivation route found** (DPORT §1 L6, unchanged here, not refuted). Composing L2+L5+L6 also needs
  U-ARITY for the index range.
- R3: the core never mentions the child, so L2 composes with L5 without identifying a `RealChildA` result. The `mc`
  of L5 must be the module of the SAME statement whose `mapM` L2 used. That is the `mc` that U-ARITY's A5/A6
  instantiate `ServedP` at (UARITY_FREEZE.md §4). If L5 is instead fed from `core_callPorts_ranA`'s `y`
  (RunFactsA:432-433), the DPORT L1' CONDITIONAL returns. Do not do that.
- `ran : MachineRanA … M D` and the trace must be about the same `(raw, D)` (`M := raw`). At the consumers both come
  from one `MachineTaken` (`machineRanA_of_runJQC`, used e.g. MemShips:58, OneOut:309), and the trace from the same run.

## 5. Controls, audit, size
- Controls (`Tests/Gen3/ArgWidthCheck.lean`): **P1** `#check` that `core_callArgPorts_oneA` instantiates with the
  premise set of an existing consumer. `oneOut_topShips` (OneOutTop:340-) has `ok`, `hbody` (`Pkg.body_eq`), `hC`,
  `hslots`, `hdomB`, `hins`, `hpost` and `ranA`; wire it in a conditional `example` with the trace's `CallStmt` (no
  run exists). **P2** data: for `callerL`, decide `callerL.machineData.shape.binders[1 + (1 + (1 + a))]?` for its
  argument lets `a ∈ (insts[0]).2.1`. These are the 16-bit and 2-bit lets, expected widths 16 and 2, which matches
  `pbhPkg.portWidths = [16, 2]` (decided too). The match is data only, not L6. **N1** a negative shape (to
  probe first; `declWidth`'s lookup order, RegDedup, is not read in this survey): a module whose wire list has the
  name twice with different widths. `decide` the `declWidth` value and show it differs from one of the two widths.
  This shows why o18 `huniq` is needed. If the lookup is not order-dependent in that way, drop N1.
- Audit: `#print axioms` of the four roots (standard or a subset); no `sorry`/`native_decide`; no reference to
  `RealChildA`, `core_callPorts_ranA` or `closeInsts_insts` in the core (grep); expected types as §2.
- Size: core about 100-110 lines (o2-o4, o7-o10, o15-o19 copied, minus o1/o5/o6/o11-o14). Each corollary is
  about 20-25 lines. L-AW and its G sibling are about 65 lines, optional. Controls are about 60 lines. Total about
  160 lines (without L-AW) to 225 lines (with). No interface change; new files only, plus lakefile registration at
  build time.
