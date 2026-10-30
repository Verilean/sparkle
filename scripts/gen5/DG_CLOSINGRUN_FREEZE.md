# DG-CLOSINGRUN full-type freeze (Issue sparkle-gen5-dg-closingrun) — rev0

**FOR REVIEW. Design only: every Lean block is UNELABORATED text; nothing here is built or proved.** No Lean file is edited
by this commit. Names are the real names at base `fa84af5d` (`kjob/g2tc-s2` = S1 `43977202` + S2 Defs R-G), checked by
grep in the worktree. Source design: `par/gen5-t2:scripts/gen5/DGEN_FREEZE.md` §3 (rev2, `ClosingRun`, `closingRun_of_run`,
(i-a)/(i-b) split), §4 DG-CLOSINGRUN row; `DG_ENV_FREEZE.md` §4.4-§4.5; `DG_RUNREADS_FREEZE.md`; M3 side
`scripts/gen2/SERVED_FREEZE.md` (F1/F2), `GPOST_FREEZE.md` (P2), `SERVED_RESULT.md`.

Wording: "not found" = this survey did not find a supplier / route; it is not a claim of impossibility. A mutant is a
rejection by signature / defeq of a changed statement, not a semantic counterexample. A new unsupplied premise is never
counted as supply. **This freeze adds no new TRUSTED boundary, no law, no change to FG / guarantees, no shared-definition
change** (`Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean` untouched; `GenWF` not strengthened).

## 0. State of the ground at `fa84af5d` (what exists, what does not)
| item | where | state |
|---|---|---|
| `RunReadsAt`, `runReads_of_run`, `coreHead_jqcA`, `fromConst_machine_linkA` | `Tools/ShippingGen5RunReads.lean:42, :181, :69, :139` | BUILT (DG-RUNREADS, accepted) |
| `T1HypND` (`T1Hyp` without `dec`), `T1Hyp.toND` | `Tools/ShippingGen5T1ND.lean:35` | BUILT |
| `ReadsAt`, `readsAt_self`, `ci_of_readsAt`, `envR_of_readsAt` (E1-E6) | `Tools/ShippingGen5Env.lean` | BUILT; C0 itself NOT SUPPLIED |
| `QuietStrength`, `AdmDown`, `t1HypND_up`, `closesA_up`, `head_jqc_start` (Q1-Q10) | `Tools/ShippingGen5EnvQ.lean:38, :42, :87` | BUILT; both premises supplied nowhere |
| G-KEEP-BODY `keepBody`, G-KEEP-CHILD `keepChild_proved` | `Tools/ShippingGen2Keep.lean:54`, `Tools/ShippingGen2KeepChild.lean:360` | BUILT |
| `core_tripleAInv` (nested core keeps `InvAt D`, `1 ≤ D`) | `Tools/ShippingGen2KeepChild.lean:133` | BUILT |
| G-SERVED F1: `core_reads_invAt0`, `machineRunInv_of_core0`, `MachineRunInv`, `ChildrenShipsI`, `synthesizeMachineCertified_runsS` (= GPOST **P2**; the name `synthesizeMachineCertified_runsInv` of DGEN §3 does NOT exist; the real name is `_runsS`) | `Tools/ShippingGen2ServedRun.lean:80, :221, :263, :342, :445` | BUILT at `02e828fc` (SERVED_RESULT.md §4.4, build `s1c-02e828fc`) |
| G-SERVED F2: `soundX_ships_ran`, `Pkg.traceX`, `servedShips0_proved` (CONDITIONAL on `hrow`) | `Tools/ShippingGen2Served.lean:60, :622, :638` | BUILT; `soundX_ships_ran` HIDES `t t' d₀ children` (it re-obtains them from `MachineRunInv` through `runsS`) |
| `OneOutNoMemRow`, `hord_of_row` | `Tools/ShippingGen2DataBridge.lean:37, :57` | BUILT; no run-derived supplier of the row `hrow` found |
| `GeneratedAt`, `genP`, `CacheAcc`, `acc_of_run`, `genP_generated`, `CoverAt`/`cover_of_run` | DG-SEM / DG-GENP / DG-ACC / DG-COVER | NOT in the tree at `fa84af5d`. DG-COVER is at `kjob/g5cv-r2` (`DG_COVER_FREEZE.md` rev0, types for `CoverAt`, `cover_of_run`); DG-SEM files at `kjob/g5cv-r2`; DG-GENP/DG-ACC have no file. |

## 1. Effect of S2 R-G on this unit (recorded)
S2 switched only `Defs.TopShips` (Defs line ~282): the `rst`/`clk` premises are guarded by `"rst"/"clk" ∈ b.inputs.map (·.name)`
(TOP_CONTRACT_REVISION.md §2 R-G; `GEN2_DEFS` cmp-identical). Consequences for `ClosingRun`:
1. **The `ClosingRun` type does not mention `TopShips`.** It uses `ShipsRes` (`RealChildA ∧ ∃ q n, … ChildShips q n r.1 r.2 ∧ InstClosed r`),
   `InvAt`, `ServedP`, `MachineTraceLBX`, `ChildrenShipsI`; none unfolds `TopShips`. `ChildShips` is unchanged by S2 (`git diff 43977202 fa84af5d -- Tools/ShippingGen2Defs.lean` is the `TopShips` line only).
   So the field list, the producers (F1/P2/F2) and the trace do NOT change with R-G. Verified by reading; the Check (§5) re-asserts it by a closure scan for `TopShips`.
2. `StepStmt` (T2-STEP / the consumer of `ClosingRun`) concludes `∃ n, TopShips …` (`Defs`/`T1.lean` StepStmt text). That is the only consumer-side place
   R-G matters; unit DG-CLOSINGRUN does not touch it. The three clk/rst facts R-G needs at the consumer ("`slots ≠ []` ⇒ clk, rst ∈ inputs of the wired module", U-TOP-CLKIN
   `Tools/ShippingGen2TopClkIn.lean`) are NOT fields of `ClosingRun` and are not claimed here.
3. Earlier DGEN text (`par/gen5-t2`) was written at the old Defs; its only `TopShips` mention in §3 is prose. Nothing in §3 needs a rewrite beyond the renamings below.

## 2. Corrections to the DGEN §3 text (so the freeze is at real names)
1. P2 is `synthesizeMachineCertified_runsS` (ServedRun.lean:445), taking `hIH`, `hKI` at `n` and `InvAt n w` for the machine-run START world `w`; it returns `∃ t t' d₀, MReturns … ∧ closeLets … ∧ (… ∨ (… ∧ ∃ children, CloseCalls … ∧ ChildrenShipsI …))`.
   `children` exists only inside the right disjunct; the left disjunct has no `children`. `ClosingRun.shared` therefore sets `children = []` in the left disjunct (as DGEN §3 already does).
2. `ChildrenShipsI` (ServedRun.lean:342) is over `children : List Res` (`Res = Module × Design`), no `p.d.shape` argument other than `shape`.
3. The translator argument of the `MReturns` is the real one: `fun e hint top named => translateExprToWire tenv e hint top named` (DGEN wrote `fun e h t n`; alpha-equivalent).
4. `soundX_ships_ran`'s hidden parts: after `obtain ⟨t t' d₀ …⟩ := runsS …` it applies `synthesizeMachineCertified_soundX _ hmix hcl hmt0 ?hX …` (ShippingMachineEntry.lean:1044) with the callback
   `∀ ids cache regs lets, MachineWired … → machPorts … = t.inputs (this is `hmp`) → notInst → X ids cache`. So `PortsServed`'s first conjunct is `hmp` itself, available in the callback with no new work (DGEN §3 already says so).
5. `Start`/`stop` depth: `core_tripleAInv` needs `1 ≤ D` (cache clear at depth 0 is excluded). See §4 S-stop.

## 3. Types (the freeze)
New file `Tools/ShippingGen5ClosingRun.lean`, `namespace Tools.ShippingGen5ClosingRun`, `set_option autoImplicit false`; imports
`Tools.ShippingGen5RunReads`, `Tools.ShippingGen5T1ND`, `Tools.ShippingGen2Served`, `Tools.ShippingGen2KeepChild`, `Tools.ShippingGen2DataBridge`. Check file `Tests/Gen5/ClosingRunCheck.lean`. Not added: any import of `Tools.ShippingGen5Env*` for the main theorem
(the `ReadsAt` supply is a separate premise, §3.4).

```lean
namespace Tools.ShippingGen5ClosingRun
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingGen2 Tools.ShippingGen5RunReads
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- The trace predicate: the trace's own `ids`/`cache` give the ports of THE mixed-synthesis result `t` (this is `hmp`
of `synthesizeMachineCertified_soundX`, ShippingMachineEntry.lean:1055-1056), and serve every instance with a shipping result. -/
def PortsServed (L : Laws mref cref) (P : Pkgs ι dom) (X : Name) (shape : MachineShape)
    (t raw : Sparkle.IR.AST.Module) (D : Design) :
    List FVarId → IO.Ref (ExprStructMap String) → Prop :=
  fun ids cache => machPorts X ids cache shape.binders = t.inputs ∧
    ServedP (ShipsRes L P) X shape raw D ids cache

/-- `Gen` is the generation proposition at the run's reads, ABSTRACT in this unit: DG-GENP instantiates it with
`fun ci envR envR' => GeneratedAt P X (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (structEnv envR') p`
(DGEN §3). It is a parameter because `GeneratedAt` is not in the tree (§0); the SHARED `∃` block (one `ci`, `envR`, `envR'`, `t`, `t'`, `d₀`, `children`) is kept exactly as DGEN rev2. -/
structure ClosingRun (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run   : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  adm   : AdmCtx L.O.quiet mctx cctx
  start : InvAt L P Reach (dv w) w
  stop  : InvAt L P Reach (dv w) w'
  shared : ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
      (t t' : Sparkle.IR.AST.Module) (d₀ : Design) (children : List Res),
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧
    Gen ci envR envR' ∧
    InvAt L P Reach (dv w + 1) w5 ∧
    MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire envR e hint top named) (profLogIO b) X
        p.d.shape.binders p.d.shape.body) (t, d₀) ∧
    closeLets p.d.shape.layout.lets t = some t' ∧
    ((p.d.shape.insts = [] ∧ children = [] ∧ raw = closeMachine p.d.shape.layout t' ∧ D = d₀) ∨
     (p.d.shape.insts ≠ [] ∧ CloseCalls p.d.shape t (closeMachine p.d.shape.layout t') d₀ children raw D ∧
      ChildrenShipsI L P Reach p.d.shape children)) ∧
    Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P X p.d.shape t raw D) X p.d raw D dom
      p.src p.extS p.extBS p.lsrc
```
(`w w'` are explicit after `Gen` here; the argument order is a PROPOSAL fixed by this freeze and checked by the expected-type comparison.)

### 3.1 Independent pieces (the unit's implementation after approval)
```lean
/-- (CR0) The machine run of the reads chain, as a stand-alone run at `w5`. A projection of `RunReadsAt.chain`. -/
theorem RunReadsAt.machineRun {mctx cctx X w w' raw D b ci envR envR' shape w5 w6}
    (h : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6) :
    RunsTo (synthesizeMachineCertified (fun e hint top named => translateExprToWire envR e hint top named)
      (profLogIO b) X shape) mctx mref cctx cref w5 (some (raw, D)) w6

/-- (CR1) `InvAt (dv w + 1)` at the machine run's START world `w5` of the reads chain. Same world as `RunReadsAt`'s `w5`
(the F1 theorems `core_reads_invAt0` / `machineRunInv_of_core0` build their own, existentially hidden, chain; the match is
`runsTo_det` (ShippingStRefCorrespondence.lean:61) on the shared prefix `coreHead → getConstInfo → getEnv → getEnv`). -/
theorem invAt_w5_of_runReadsAt (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx cctx} (hA : AdmCtx L.O.quiet mctx cctx) {X w w' raw D b ci envR envR' shape w5 w6}
    (hst : InvAt L P Reach (dv w) w)
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6) :
    InvAt L P Reach (dv w + 1) w5

/-- (CR2 = (i-b)) The existing text of `soundX_ships_ran` after its `obtain`, with `t t' d₀ children` and their facts as
ARGUMENTS (no re-obtaining; no identification of two `t` by determinism, `MReturns` being an `∃`). -/
theorem soundX_ships_at (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {tenv : Environment} {b : Bool} {X : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {d : Design}
    {t t' : Sparkle.IR.AST.Module} {d₀ : Design} {children : List Res}
    (hmix : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) X shape.binders shape.body) (t, d₀))
    (hcl : closeLets shape.layout.lets t = some t')
    (hmt : (shape.insts = [] ∧ children = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨
      (shape.insts ≠ [] ∧ CloseCalls shape t (closeMachine shape.layout t') d₀ children m d ∧
        ChildrenShipsI L P Reach shape children))
    (hreach : ∀ k (hk : k < shape.insts.length),
      (shape.instOrigins.getD k .ord).child? = none → Reach (shape.insts[k]).1)
    (hord1 : shape.instFields = [] → ∀ k, k < shape.insts.length →
      (shape.instOrigins.getD k .ord).child? = none) :
    SoundXAt (PortsServed L P X shape t m d) X shape m d

/-- (CR3) `Pkg.traceX` at `PortsServed` (rows (j)-(m) of SERVED_FREEZE; no new proof). -/
theorem trace_of_soundX_at … (p : Pkg ι dom) {t m} {d : Design}
    (hX : SoundXAt (PortsServed L P p.decl p.d.shape t m d) p.decl p.d.shape m d) :
    Tools.ShippingMachineTraceX.MachineTraceLBX (PortsServed L P p.decl p.d.shape t m d) p.decl p.d m d dom
      p.src p.extS p.extBS p.lsrc :=
  Pkg.traceX p hX

/-- (CR4) `stop`: the nested core run keeps `InvAt (dv w)` (`core_tripleAInv` with `hbody := keepBody … (dv w + 1) hKI`). -/
theorem stop_of_run (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) {mctx cctx}
    (hA : AdmCtx L.O.quiet mctx cctx) {X w w' raw D}
    (h1 : 1 ≤ dv w) (hlim : dv w < sparkleSynthDepthLimit)
    (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hst : InvAt L P Reach (dv w) w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w') :
    InvAt L P Reach (dv w) w'
```
`dv w` is `Tools.ShippingChildBndCore.dv`. (CR4) proof sketch: `core_tripleAInv L P Reach hA (dv w) h1 X (fun hD b ci isInst => keepBody L P Reach (dv w + 1) hKI mctx cctx hA X _ b ci isInst)`; apply the Triple to `hst` and `hrun`. `hlim` is the `D < sparkleSynthDepthLimit` of `core_tripleAInv`'s `hbody`.
`hlim` is derivable from `hrun` by `core_limit_triple L.O hA (dv w) X` (ShippingChildCoreC.lean:128-133, used by `limitStmt_proved`); the implementer either proves that derived form
(then `hlim` leaves the premise list) or keeps `hlim` visibly. Either way it is not a new law.

### 3.2 The connection theorem (target of the unit; CONDITIONAL; INTERMEDIATE until every premise is supplied)
```lean
theorem closingRun_of_run (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)   -- UNSUPPLIED (G-DATA; §4 S-hrow)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w) (hlim : dv w < sparkleSynthDepthLimit)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingRun L P Reach mctx cctx X p Gen w w' raw D
```
Proof plan: `adm := hA`, `start := hst`, `run := hrun`, `stop := stop_of_run … hKI hst hrun`. `shared`:
`runReads_of_run L.O hA hst.1.1 (Or.inr hst.1.2) hrun (hT.defines X hR p hP mctx cctx hA) (hT.closes X hR p hP mctx cctx hA)` gives `b ci envR envR' w5 w6` and `RunReadsAt` (this uses `hst.1 : JQC L.O (dv w) w`, i.e. `JQ` at `dv w` and `CacheInvA`);
`hGen` gives `Gen`; (CR1) gives `InvAt (dv w+1) w5`; `synthesizeMachineCertified_runsS L P Reach hA hIH hKI (hw := CR1) (hr := CR0)` gives `t t' d₀` and the disjunction (children `[]` on the left, the inner `children` on the right); (CR2) with `hreach := fun k hk hn => hT.closed X hR p hP k hk hn` and
`hord1 := fun hf k hk => Tools.ShippingGen2DataBridge.hord_of_row (hrow p hDp) hf k hk` (where `hDp : DataOk p` from `hT.pkg X hR`, as in `servedShips0_proved`, Served.lean:638-657) gives `SoundXAt (PortsServed …)`; (CR3) gives the trace.
`MReturns` and `CloseCalls`/`ChildrenShipsI` share the SAME `t t' d₀ children` as the trace, since (CR2) takes them as arguments.
No premise mentions `T1Hyp.dec`; `T1HypND` only (`defines`, `closes`, `closed`, `pkg`).

### 3.3 Why `Gen` / `hGen` is the one place DG-COVER, DG-ENV and DG-GENP enter
`hGen` is a SINGLE premise about the run's own reads (`RunReadsAt` with the same `ci envR envR'`); it replaces DGEN's four premises
`hP : P = genP env₀`, `hR : ReadsAt env₀ cref w`, `hacc : CacheAcc env₀ w`, `hcov : MachineRouteCovered …`, which cannot be written yet (§0). The decomposition DGEN intended is recorded here so nothing is lost:
`hGen` ⇐ `genP_generated` (DG-GENP C6) at `P = genP env₀` ∧ `hcov` (DG-COVER: `CoverAt (runEntry ci envR) (structEnv envR') p.d.shape` by `cover_of_run`, DG_COVER_FREEZE.md §3, itself conditional on `OSH` and `CoverRows`)
∧ `hR` (DG-ENV: `ReadsAt env₀` at the run's worlds `w1/w3/w5`, i.e. `ci`, `envR`, `envR'` agree with `env₀`) ∧ `hacc` (DG-ACC, G-REACH).
When DG-GENP / DG-ACC land, a second theorem `closingRun_of_run_gen` instantiates `Gen := fun ci envR envR' => GeneratedAt P X (entryConst …) (structEnv envR') p` and replaces `hGen` by these four premises; the statement of §3.2 is then a corollary (not claimed now).
**`hGen` is not counted as supply.** `closingRun_of_run` with `hGen` is INTERMEDIATE.

### 3.4 The ReadsAt route (DG-ENV), stated, not used
Under the DG-ENV TQ route the whole connection is instantiated at `L'` with `QuietStrength L L' env₀` and `AdmDown L L'` (`Tools/ShippingGen5EnvQ.lean:38, :42`; both supplied nowhere) so that `L'.O.quiet w ↔ L.O.quiet w ∧ ReadsAt env₀ cref w`.
Then `hT : T1HypND L' P Reach DataOk` comes from `t1HypND_up hq hd H` (EnvQ.lean:87) and `ClosingRun L' …` follows from §3.2 with `L := L'`; `hA'` (C-ADM old ⇒ new at the top context) stays a premise (EnvQ Q10). This unit does NOT import `Tools.ShippingGen5EnvQ` and does not add `QuietStrength`/`AdmDown` as premises; they would enter the CALLER. **No new unsupplied DG-ENV assumption is added by this unit, and none is counted as supply.**

## 4. Supplier table (every premise and every field)
Legend: **S** = supplied by an existing export (file:line, built); **P** = provable now in this unit (new lemma over S); **W** = waits on another issue; **U** = this survey found no supplier / route (not a claim of impossibility).
| field / premise | source | status |
|---|---|---|
| `run` | the premise `hrun`; at the FG boundary it comes from the FG run by `fullEntry_sameDesign` (ShippingOneOutSameRun.lean:50-70, DGEN §3 producers row 1) | S (premise); the FG-run peel is a separate existing lemma, not part of this unit |
| `adm` | premise `hA` (`Start` at depth 0; `ihAt_stepPF` data inside the induction, `Tools/ShippingGen2T1.lean:165-183`) | S |
| `start` | premise `hst : InvAt (dv w) w`; in `ihAt_stepPF` it is `hu` (T1.lean:171-179); at the outermost start `Start` gives `JQC 0` only (Defs:52) | S inside the induction; **top-level `dv w = 0`: `InvAt 0` (the `CacheShips` half) is not given by `Start`: U (see S-stop)** |
| `stop` | (CR4) from `core_tripleAInv` (KeepChild:133) + `keepBody` (Keep:54) + `hKI` at `dv w+1` | P for `1 ≤ dv w`. **`dv w = 0`: `core_tripleAInv` excludes depth 0 (`hD : 1 ≤ D`); this survey found no `core_triple` at `InvAt 0` end world: U** |
| `shared`: `RunReadsAt` | `runReads_of_run` (RunReads:181) with `hT.defines`, `hT.closes` | S |
| `shared`: `Gen ci envR envR'` | `hGen` | **W/U**: DG-GENP (`GeneratedAt`, `genP_generated`) not in tree; DG-COVER `cover_of_run` conditional (rows, `OSH`); **DG-ENV `QuietStrength`/`AdmDown` unsupplied; C0 unsupplied**; DG-ACC/G-REACH unsupplied; `T1HypND`-side `pkg`/`closed` assignment is DG-PKGASSIGN |
| `shared`: `InvAt (dv w+1) w5` | (CR1): `core_reads_invAt0`/`synthesizeFromConst_machine_invAt` (ServedRun:80, :178) + `runsTo_det` on the common prefix | P (new, small; the same facts as `machineRunInv_of_core0` :221 but at `RunReadsAt`'s `w5`) |
| `shared`: `t t' d₀`, `MReturns`, `closeLets`, disjunction, `ChildrenShipsI` | P2 = `synthesizeMachineCertified_runsS` (ServedRun:445) at (CR0)+(CR1) | S |
| `shared`: `children` same in `CloseCalls` and `ChildrenShipsI` | the `∃ children` of `runsS` (right disjunct) | S |
| `shared`: `hreach` for (CR2) | `hT.closed` (T1HypND) | S |
| `shared`: `hord1` for (CR2) | `hord_of_row (hrow p hDp)` (DataBridge:57) | **U**: `hrow : ∀ q, DataOk q → OneOutNoMemRow q = true`. Data-supply (Issue `sparkle-gen3-data-supply`) U-DS1..DS5 (`Tools/ShippingGen3DataSupply*.lean`, DATA_SUPPLY_FREEZE_REV1.md / DS2_5.md) lists `OneOutNoMemRow` (`hrow`) as having no run-derived supplier in that survey; `DataRows` conj. 3 needs D3 `InstBindersNonDomain`; L6/R6 unsupplied. This unit takes `hrow` as an explicit premise of the exact data-supply type (`Tools.ShippingGen2DataBridge.OneOutNoMemRow`) |
| `shared`: trace | (CR2)+(CR3) | P (mechanical split of F2; CONDITIONAL on `hrow`) |
| depth bound `hlim` | `core_limit_triple` (ChildCoreC:128-133) | P (derivable) or visible premise |
| `hIH`, `hKI` at `dv w+1` | the induction hypotheses `ih_allPF` (T1.lean:197-200) provide both | S (premises inside the T1 induction) |

Not counted as supply: `hrow`, `hGen`, `h1` (top-level), the DG-ENV / DG-COVER / DG-ACC items above.

## 5. Check plan (after approval; `Tests/Gen5/ClosingRunCheck.lean`)
- Expected types (fully bound telescopes, written independently): `ClosingRun` (the structure's `mk` telescope field by field, names/order/binderInfo), `PortsServed`, CR0-CR4, `closingRun_of_run`.
- Mutants (rejection by signature / defeq of a changed statement, NOT semantic counterexamples): `ClosingRun.shared` with two separate `∃` blocks (independent `t`); `children` hidden under the right disjunct only; `PortsServed` without the `machPorts … = t.inputs` conjunct; `InvAt (dv w)` instead of `(dv w+1)` at `w5`; `stop` at `dv w+1`; `JQC` instead of `InvAt` at `w5`;
  `hrow` dropped; `hGen` replaced by `Gen` unconditional; `T1Hyp` instead of `T1HypND`; `hreach` dropped; `1 ≤ dv w` dropped from (CR4); `RunReadsAt` with `envR` and `envR'` swapped in the translator environment; (CR1) at `w3` (bound inside `chain`'s `∃`, so stated as a bound type).
- Closure audit (full reachable closure, explicit bodies; controls as in `T1NDCheck`): no reach to `T1Hyp.dec` (named projection, raw `.proj`, recursors; negative control), no `BodyStepC`, no `native_decide`, **no `TopShips`** (positive control: `StepStmt` reaches it), no `GeneratedAt`/`genP` (not in the tree), axioms standard (`#print axioms`).
- Vacuity audit: a concrete `Pkg` and run satisfying the premises is NOT available without DG-GENP/`hrow`; stated as not performed (the same as DATA_SUPPLY's control inventory, items 1-4). `ClosingRun` itself is checked non-vacuous only in so far as the F1/P2/F2 theorems it factors are (`servedShips0_proved`'s own checks, SERVED_RESULT.md).
- Build: `kjob lake build Tests.Gen5.ClosingRunCheck` by the coder (clean issue-linked build); the implementer commits with "clean build は coder が実行".

## 6. Questions for the reviewer (decisions this freeze needs; none touches a law / TRUSTED / FG)
1. **`Gen` as a parameter** (§3, §3.3) instead of `GeneratedAt` directly: accepted? It keeps the single shared `∃` block (the R2 requirement) while DG-GENP is not in the tree. The alternative is to wait for DG-GENP; that blocks the independent pieces CR0-CR4.
2. **`stop` / `start` at `dv w = 0`** (§4): `stop` as a `ClosingRun` field is provable only for `1 ≤ dv w`. Options: (a) keep `ClosingRun` as is and add `h1 : 1 ≤ dv w` to `closingRun_of_run` (the T1 induction only uses depth ≥ 1; the outermost run is a separate caller); (b) drop `stop` from `ClosingRun`.
   Recommended: (a). Reversible (a field can be added later). If neither is acceptable, the top-level case is U and is recorded; no law is proposed.
3. `hlim` visible or derived (§3.1): recommended derived by `core_limit_triple`; falls back to the visible premise if the derivation needs a law field beyond `L.O`.

## 7. Not claimed
- `GeneratedAt`, `genP`, `CacheAcc`, `hrow`, `ReadsAt`/C0, `QuietStrength`, `AdmDown`, `T1HypND.pkg` assignment for `P = genP env₀`: none supplied here.
- No claim for runs that fall back (DG-FALLBACK), nor for the top-level (`dv w = 0`) `start`/`stop`.
- No claim that `ClosingRun` is inhabited for any concrete run. Nothing is built or proved by this document.
- Not G-SERVED, G-POST, T1, M5 or FG completion. `closingRun_of_run` with `hrow` and `hGen` is an INTERMEDIATE result.

## 8. Implementation record (rev0 limited approval 25be9f8c -> `Tools/ShippingGen5ClosingRun.lean`, `Tests/Gen5/ClosingRunCheck.lean`)
Written by agent g5cr-r2. Built in this Pod, one target at a time (`kjob lake build Tools.ShippingGen5ClosingRun`, then `kjob lake build Tests.Gen5.ClosingRunCheck`), both exit 0, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `sorry` / `axiom` / `native_decide`. The clean issue-linked build is the coder's.

Differences from the §3 text (types changed at implementation):
1. **`hlim` removed** from (CR4) `stop_of_run` and from `closingRun_of_run`. Shown by the build: `core_tripleAInv`'s `hbody` has its own binder `D < sparkleSynthDepthLimit →`, which the supplier `keepBody ... (dv w + 1) hKI` does not use (it holds at every depth), so the premise is never needed. No `core_limit_triple` use, no law. Argument order of (CR4): `(h1) (hKI) (hst) (hrun)`.
2. **(CR1) is two theorems**: `coreHead_invAt0` (new, general: `JQC D w` and `D = 0 ∨ CacheShips`, concludes `InvAt (D+1)` at the end world of the chain's `coreHead`; a copy of `coreHead_jqcA` with the `InvAt` steps of `core_reads_invAt0`) and `invAt_w5_of_runReadsAt` (the §3.1 type, unchanged), which peels `RunReadsAt.chain`'s own `coreHead -> getConstInfo -> getEnv -> getEnv` at `InvAt`. `core_reads_invAt0` and `runsTo_det` are NOT used; the Check closure audit forbids `core_reads_invAt0` for `coreHead_invAt0`, `invAt_w5_of_runReadsAt`, `soundX_ships_at`, `stop_of_run` and `closingRun_of_run`.
3. (CR0) is declared as `Tools.ShippingGen5RunReads.RunReadsAt.machineRun` (via `_root_`) so that `h.machineRun` projection notation works; the statement is the §3.1 one.
4. (CR3) `trace_of_soundX_at` has all binders explicit: `(L) (P) (p)` and `{t m} {d}`; `Reach` is not a binder (`PortsServed` does not take it). Statement as §3.1 with `p.decl`.
5. `closingRun_of_run` assembly: it first rewrites `p.decl = X` from `hT.pkg X hR` (so the trace of `Pkg.traceX p` is at `X`); the ONLY other use of `hT` fields is `defines`, `closes`, `closed`, `pkg` (no `T1Hyp.dec`). In the left disjunct `children := []`; in the right it is the `children` of `synthesizeMachineCertified_runsS`, the SAME one used in `soundX_ships_at` and in the `ClosingRun.shared` block. `PortsServed`'s first conjunct is `hmp` of the `soundX` callback.
6. The depth-0 case is unchanged: `h1 : 1 ≤ dv w` stays a premise (recommended option (a) of §6.2).

Check (`Tests/Gen5/ClosingRunCheck.lean`): `ClosingRun` against an independent `ExpClosingRun` (5 fields) plus 6 one-point structure mutants (shared block split with an independent `t`, `children` under the right disjunct only, `InvAt (dv w)` at `w5`, `JQC` at `w5`, `stop` at `dv w + 1`, translator `envR'`); expected TYPES of `PortsServed`, `RunReadsAt.machineRun`, `coreHead_invAt0`, `invAt_w5_of_runReadsAt`, `soundX_ships_at`, `trace_of_soundX_at`, `stop_of_run`, `closingRun_of_run` (independent `def ... : Prop := ∀ ...`); 13 well-typed one-point mutants (all elaborate; they are rejected by signature / defeq of a changed statement, NOT semantic counterexamples; an elaboration failure would have been a build error and is not counted). Closure audit (full value + type closure): 9 negative controls (direct, through helpers in another namespace, raw `.proj`, recursor) detected and 2 clean controls not flagged; the five roots above reach none of `BodyStepC`, `core_reads_invAt0`, `soundX_ships_ran`, `servedShips0_proved`, `TopShips`, `ofReduceBool`, any `T1Hyp` field. AXIOMS for all 8 declarations: standard.

Still NOT supplied / not claimed (unchanged): `hrow`, `hGen` (and with it `GeneratedAt`, DG-GENP, DG-COVER, DG-ENV `ReadsAt`/`QuietStrength`/`AdmDown`, DG-ACC), the start / stop at `dv w = 0` (so the T1 / FG connection at depth 0 is NOT supplied by this nested version and cannot be replaced by it), the concrete (`Gen := GeneratedAt ...`) instance of §3.3 (`GeneratedAt` is not in the tree, so it was not written; when it lands it must be an instance of `closingRun_of_run`, not the other way round). **Non-vacuity of `ClosingRun` / `closingRun_of_run` is not verified** (no concrete `Pkg` and run satisfying the premises; not inherited from the earlier conditional theorems). `closingRun_of_run` is an INTERMEDIATE result, not T1 / M3 / M5 / FG completion.
