# D-PORT: the module-port / source-package width correspondence, a ROUTE REPORT (read-only; nothing supplied)

Issue `sparkle-gen3-dport`. Plan: scripts/gen2/G3GEN_CALL_PLAN.md rev1 §2.1 (`PortTie`, :65-70), §2.2 (G-DATA-CALL,
:83-90), §2.3 (:92-96). Base: `par/gen2-spec` at 649a6bf5 (all citations are this branch unless marked `[M3]` =
`kjob/gen3-induct` worktree at b4ee77eb). No Lean was run, written or edited. Proposed statements below are TEXT ONLY.

**Reused, not redone.** The RESULT-width side (binder at `nDecl+k` vs the callee's one output; `OneOutWidth`/`hW`,
G-ONEOUT-WID, routes a/b/c, revision table) is S4_WID_SUPPLY.md rev2 and is not repeated here. This report covers the
ARGUMENT side that `PortTie` names (`callArgsOkAt`, Adapt.lean:73-77) and the arity half, and reuses the S4 stage-B
proof pattern (`core_callPorts_oneA`) as the template for the missing parent lemma. [M3] adds no port/width material
(its new files Tools/ShippingGen2{KidsInst,InstKeep,KeepChild}.lean are instance-existence / keep / cache lemmas).

## 0. Inventory
| artifact | file:line | proves | premises / scope | status |
|---|---|---|---|---|
| `instStmt` / `instStmtG` | Sparkle/IR/Machine.lean:272-288; Sparkle/IR/MachineInstG.lean:30-54 | emit the instance; argWs = `portNames[nIn+kI+n+j]` for `j ∈ args` | checks COUNT `inPorts.length = argWs.length`, names, Nodup; **no width check on inputs** | compiler |
| `closeInsts` / `closeInstsG` | Machine.lean:396-427; MachineInstG.lean:115- | closing checks | no width conjunct (S4_WID §3(c)); `linkedOk` (Machine.lean:337-354), `kidsCombB` (:371-383), `hierGate` (RefineCheck.lean:196-200) are name/shape only | compiler |
| `instOutWidthsOk` | Tools/ShippingHierOpen.lean:503-514 | OUTPUT conns only (`W w == p.ty.bitWidth` for `p ∈ child.outputs`) | no input analogue exists (grep `InWidths`: none) | def |
| `connsG` | Tools/ShippingMachineLinkedT.lean:28-34 | name connections `(argPorts.zip argWs)` | names only | def |
| `CallStmt` / `instStmt_some` | Tools/ShippingMachineInst.lean:190-206, :208- | argWs via `args.mapM`, `inPorts.length = argWs.length` | one-output | DONE |
| `CallStmtG` / `instStmtG_some` | Tools/ShippingMachineInstG.lean:19-37, :39- | same for groups (+clk/rst for seq kids) | group | DONE |
| `MachineWired` call conjuncts | Tools/ShippingMachineEntry.lean:663 (`lets = names.drop …`), :664-667 (one-output `CallStmt` per k), :709-719 / :720-724 (group `CallStmtG` per stmt / per k) | every call k has its statement in the module's port names | `instFields = []` resp. `≠ []` | DONE (exported) |
| `machPorts_names_indep`, `ranA_inputs_machPorts` | Tools/ShippingGen2OneOutNames.lean:29, :83 | trace names = harness names (NamesEq) | `ids.length = binders.length` | BUILT (g2sb-93e9994c) |
| `core_callPorts_oneA` | Tools/ShippingGen2OneOutTop.lean:51-196 | output wire `x` of call k: `declWidth b x = kindTy(binders[nDecl+k]).bitWidth` | `hf0 : instFields = []`, `hins`, `outTy`, `hnomem`, `hpost`, `MachineRanA` | BUILT; OUTPUT side only |
| `core_callPorts_ranA` | Tools/ShippingParentRunFactsA.lean:410-561 | same for groups, AND `RealChildA O c_k y ∧ mc = y.1` | `hfne`, `hkidP`, … | DONE; OUTPUT side only |
| run port facts | Tools/ShippingTransitionPortTys.lean:143-161 (`P2` typed by `binders.drop nDecl`, length kI+n+lets, so LET ports included); Tools/ShippingClosedPorts.lean:205-221 (every `t.inputs` port is a wire of `closeMachine … t'`, width ≠ 0); TransitionPortTys:76 (`closeLets_wires`), :92 (`closeMachine_wires_sup`), :68 (`port_of_name`); Tools/ShippingInstWidthsParts.lean:54 (`declWidth_of_unique`) | the ingredients of a let-wire width lemma | run of the machine route | DONE (ingredients) |
| `hWd_of_wired` | Tools/ShippingSrm32Width.lean:28-52 | slot REGISTER widths ≤ `declWidth b r` | `hpost`, `hierGate`, `houtTy` | BUILT; slots, not lets/args |
| child interface port export | Tools/ShippingGen2Defs.lean:65 (`CombChildRunN`), Tools/ShippingMachineDepth.lean:70 (`SeqChildRunN`) | `(argPorts mc).length = (bsC.filter nonDom).length`; outputs exported WITH types (Defs:63, Depth:66) | — | DONE for LENGTH only; input TYPES not exported |
| producer-local `argPorts` identity | Tools/ShippingMachineDepthChild.lean:41-56 (`calls_ports`: `argPorts m = machPorts c ids cache (d.bsIn.take kD)`); same `hargs` in Gen2C6.lean:58/79, Gen2LeafSeq.lean:66, Gen2SlotlessLeaf.lean:325, MachineChild.lean:196, MachineSeqChild.lean:128/319, MachineDepthRun.lean:185, MachineDepthRunR.lean:170, GateChild.lean:142/219, FirstGateChild.lean:603/679 (grep list, not audited for completeness) | at the producer, the shipped child's arg ports ARE its declared ports | per producer, inside proofs | DONE locally, NOT exported |
| `machPorts_tys` | Tools/ShippingPortWidthsPure.lean:142-147 | `(machPorts …bs).map ty = (bs.filter nonDom).map (kindTy ·.2)` | `bs.length ≤ ids.length` | DONE |
| `callArgsOk` / `callArgs_width` | Tools/ShippingPortsMatchRaw.lean:199-215 | global argument-width table row | per-declaration `decide` (CALLDEC_PROBE_RESULT.md:34) | DONE (data row) |
| `callArgsOkAt`, `Pkg.portWidths`, `callArgsOkAt_width`, `call_inRange_at`, `callDec_of_hPointAt_at` | Tools/ShippingGen2Adapt.lean:73, :80, :83, :106, :167 | k-local row ⇒ InRange ⇒ CallDec | `hargsK`, `hlenK` premises | BUILT (UADAPT_RESULT.md); row by `decide` per k (UADAPT_RESULT.md:43) |
| reader: arg kinds | Sparkle/Compiler/Elab.lean:3721-3728 (`machInstCall?`), :4366-4383 (`telescopeKinds`, `instSignature?`), :4070 (`machLetIndex … kind v'`), :3743-3750 (`machLetIndex`), :2337-2343 (`mixedGateBinderKind?`, canonical literal widths), :5181-5185 (binders `bs ++ instBinders ++ slots ++ lets`) | source of both widths (§1 L6) | `partial` `machInstance` | source reading only |
| `instSignature?_some` | Tools/ShippingInstSignature.lean:18-22 | `telescopeKinds ci.type = some kinds` | — | DONE |
| `ResDeclAt` / `P5At` | Tools/ShippingCallWidthsChildReal.lean:137-155 | RESULT-kind premises per callee | explicit premises | premise only (no ARG analogue exists) |

## 1. The chain, link by link
Target row (G3GEN_CALL_PLAN.md:86): `callArgsOkAt p.d p.kD k q.portWidths = true ∧ (insts[k]).2.1.length = q.ports.length`.
Index note: `callArgsOkAt` reads `binders[nDecl + (kI + (n + a))]` (Adapt.lean:73-77); the run lemmas use `nDecl` with
`callsOk nDecl`; `nDecl = p.kD` is the `closingNDecl_eq_kD` step (S4_CONSUMER_FREEZE.md:510-512).

| link | one-output parent (`instFields = []`) | group parent (`instFields ≠ []`) |
|---|---|---|
| L0 instance stmt of call k exists, in trace names | DONE: MachineEntry:664-667 + NamesEq (OneOutNames:29, :83; used at OneOutTop:112-116) | DONE: MachineEntry:720-724 (`(k, field) ∈ outs`, `args`) |
| L1 `argWs[j] = names[nIn+kI+n+args[j]]` (a let port) | DONE: `CallStmt` (MachineInst:192-193) | DONE: `CallStmtG` (MachineInstG:23) |
| L1' served module = callee's shipped result | CONDITIONAL on `MachineTraceLBX (ServedP (ShipsRes L P) …)`: `hx.2` gives `ShipsRes` (FitChain:930-943) | DONE via `core_callPorts_ranA` (`RealChildA`, `mc = y.1`, RunFactsA:432-433) plus `ServedP` |
| L2 `declWidth b argWs[j] = kindTy(binders[nDecl+kI+n+a]).bitWidth` | MISSING; composable (§0 "run port facts"): same steps as OneOutTop:142-190 at P2 index `kI+n+a` instead of `k`; `hinW` (ClosedPorts:221) gives width ≠ 0, so the wire survives `dropZeroWidthModule`/`mergeChecked` (OneOutTop:82-95). Premises those of `core_callPorts_oneA` | MISSING; same, under the premises of `core_callPorts_ranA` |
| L3 binder ↔ source binders | DONE (definitional: the shape's binder list IS `p.d.shape.binders`, Elab:5183-5185) | DONE |
| L4 arity `args.length = q.ports.length` | MISSING only as a composition; every piece exported: `args.mapM … = some argWs` (length), `inPorts.length = argWs.length` (CallStmt), `(argPorts mc).length = q.ports.length` (Defs:65 / Depth:70 with `bsC = q.d.bsIn.take q.kD`, Defs:90; `Pkg.ports` Pkg.lean:80) | same via CallStmtG + `ChildRunN` (both branches) |
| L5 child: `(argPorts mc).map (·.ty.bitWidth) = q.portWidths` | MISSING EXPORT. Derivable at each producer (`calls_ports`-style `hargs` + `machPorts_tys` + `argPorts` kept by the cleanup, C6:79) but `ChildShips`/`ChildRunN` export only the length | same |
| L6 emitted tie `declWidth b argWs[j] = (argPorts mc)[j].ty.bitWidth` | **REFUTED as a run/closing consequence**: no check in `instStmt` (Machine.lean:272-288), `closeInsts` (:409-427), `linkedOk`, `kidsCombB`, `hierGate`, `instOutWidthsOk` (outputs only) mentions an input width. A width-mismatched (M, D) passes every listed check; so `PortTie` is NOT implied by the closing (as the plan anticipated, :69-70). This is a statement about the exported checks, not a claim that such a run exists | same (`instStmtG`, MachineInstG:30-54) |
| L6' source tie `kind(binders[nDecl+kI+n+a]) = kind(q.ports[j])` (what `callArgsOkAt` actually states) | UNPROVED; source reading: a FRESH argument let is pushed with the callee SIGNATURE kind `kinds[j]` (Elab:4070; `kinds` = `telescopeKinds` of c's declared type, Elab:4366-4383). Two reuse branches keep an EARLIER kind: `_machLet j` fvar (Elab:3746) and same-value dedup (Elab:3748-3749); equality there needs Lean typing of `c args` + canonical literal reading (Elab:2342). Callee side: `q.d.bsIn` comes from `machineShape?` on `entryConst … ci` (value-lambda binders, possibly `userInliner`-rewritten), not from `telescopeKinds ci.type`; equal only via Lean typing (+ P5-like inliner fact) and env identity between the parent's `envR'` and the callee read (same gaps as S4_WID §1). Not refuted; no counterexample known | same reader path (`machInstanceS`, Elab:4085-) — not separately audited for arg kinds |

Consequence: with L2 and L5 proved, L6 is still needed and is exactly the source equality L6'; the emitted modules carry
two independent copies of source widths. So the route "closing ⇒ PortTie ⇒ callArgsOkAt" cannot close from exports
alone; only the ARITY half (L4) is run-derivable today.

## 2. Proposed statements (text only, for review)
```lean
/-- Parent half (L2): the let wire an argument port of call k is connected to has its binder's width in `b`. -/
theorem core_callArgPorts_oneA … (same premises as core_callPorts_oneA, OneOutTop:51-73) :
  ∀ k (hk : k < d.shape.insts.length) args mc st, (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ b.body →
    CallStmt (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      ((machPorts c ids cache d.shape.binders).map (·.name)) k args mc st →
    ∀ j a w, args[j]? = some a → (args.mapM fun j => names[nIn+kI+n+j]?) = some argWs → argWs[j]? = some w →
      ∃ bn, d.shape.binders[nDecl + (kI + (n + a))]? = some bn ∧ declWidth b w = (kindTy bn.2).bitWidth
-- group sibling `core_callArgPorts_ranA` with CallStmtG and the premises of RunFactsA:410-428.

/-- Child half (L5): the shipped module's argument ports have the package's port types. -/
def ChildPortTys (q : Pkg ι dom) (mc : Module) : Prop :=
  (argPorts mc).map (·.ty) = q.ports.map (fun b => kindTy b.2)

/-- PortTie (plan :65-68), made precise: the emitted widths of call k's argument wires equal the child's port widths. -/
def PortTie (p : Pkg ι dom) (b : Module) (k : Nat) (mc : Module) : Prop :=
  ∀ args argWs, (p.d.shape.insts.map (·.2.1))[k]? = some args →
    (args.mapM fun j => names[nIn + kI + n + j]?) = some argWs →
    argWs.map (declWidth b) = (argPorts mc).map (·.ty.bitWidth)

/-- Source half (L6'), the real content; an ARG analogue of ResDeclAt/P5At, per callee c and parent call. -/
def ArgDeclAt (c : Name) (kinds : List MixedGateBinder) : Prop := -- for every read of c (as ResDeclAt, ChildReal:137)
  ∀ mctx cctx w1 ci w2 dD, RunsTo (getConstInfo c) … ci w2 → ci = .defnInfo dD → telescopeKinds dD.type = some kinds
-- + "R1-arg": the parent's let kind at args[j] is kinds[j] (fresh pushes: by construction of the partial machInstance;
--   reuse branches: a typing premise), + "callee ports = telescope": (q.d.bsIn.take q.kD) kinds = kinds (P5-like).
```
Composition: L0+L1+L2 (parent) and L1'+L5 (child) give `PortTie ⇔ callArgsOkAt p.d p.kD k q.portWidths` (given L4);
i.e. `PortTie` is a RE-STATEMENT of the row on emitted modules, not a supplier. The supplier is L6' (ArgDeclAt +
R1-arg + callee-ports-telescope + env identity), or a per-declaration `decide` row, or a compiler guard
(`wireWidth m.wires w == p.ty.bitWidth` per input in `instStmt`/`instStmtG`; would make L6 a run fact; compiler change,
user decision — the reviewer declined the OUTPUT analogue, S4_WID_SUPPLY.md:74).

Unsupplied (named): G-ONEOUT-WID / `hW` (result side, S4_WID); the new ARG analogue (call it G-ARG-WID);
`MachineDefines.shape_eq` with conditions (i)-(iii) (S4_WID_SUPPLY.md:128) — needed if L5 is taken from a generator
table instead of the served child; `ResDeclAt`/`P5At` and their ARG analogues; env identity; R1 for the `partial`
`machInstance` (both result and argument kinds).

## 3. Recommended next units (route only)
1. **U-ARITY** (small, proof): `args.length = q.ports.length` from `MachineTraceLBX (ServedP (ShipsRes …))` +
   `CallStmt`/`CallStmtG` + `ChildRunN` length conjunct. Discharges `hlenK` run-locally. No interface change.
   SUPPLY unit → dependency of `sparkle-fg-final`.
2. **U-ARGW-PARENT** (proof): `core_callArgPorts_oneA` / `_ranA` (§2), template OneOutTop:51-196. No interface change.
   Only useful together with 3 and 4 (alone it supplies nothing).
3. **U-CHILD-PORTTYS** (design + revision table first): export `ChildPortTys` from `ChildShips` (or `ChildRunN`
   both branches). Shared-interface strengthening: needs an S4_WID §4.1-style table (every producer in §0's grep list,
   memory producers Srm4Run:96 / Srm4Mixed:244, `childRunN_of_seq` AComb:18, PkgCompat copies, GEN2_DEFS.lean.txt).
4. **D-ARGW** (decision unit, user): pick the supplier of L6': (a) ArgDeclAt + R1-arg + callee-telescope premises
   (moves the gap, like route (a) of S4_WID), (b) per-declaration decided `callArgsOkAt` row with a `kidInsP`
   table tie (analogue of `kidOutsP`, DataBridge:66-77; supplier-local), or (c) compiler input-width guard. Until
   decided, G-ARG-WID stays a named open gap row next to G-ONEOUT-WID.
5. **G-DATA-CALL** (M3) = 1 + (2+3+chosen 4, or 4(b) alone). Whichever of 2/3/4 is chosen is a SUPPLY unit and must be
   added as a dependency of `sparkle-fg-final`; units 1 and the chosen L6' supplier are mandatory for it.

## 4. Not claimed
- No lemma above is written or built; "composable" means the cited ingredients exist, not that the proof goes through.
- L6 "refuted" is about the exported closing checks only; no successful width-mismatched run is exhibited, and the
  source reading (L6') suggests none exists, but this is neither proved nor measured.
- The group reader path (`machInstanceS`) and memory-origin calls (handled by `MemDec`, never by the adapter) were not
  audited for argument kinds. The producer grep list in §0 is not a completeness audit.
- No change to `T1Hyp`, `ChildShips`, `ChildRunN`, `DataOkB`, FG or the compiler is proposed as applied.
