# DG-ACC freeze rev3 (issue `sparkle-gen5-dg-acc`): A5 supply survey, complete types, supplier table

**FOR REVIEW (docs only; no Lean for A5 is written until this is approved).** Rev1 (`DG_ACC_FREEZE_REV1.md`) and rev2 (`DG_ACC_FREEZE_REV2.md`) are unchanged. Base: `kjob/g5ac-r5`, rev2 §B.2/§C.2 Lean committed as
`Tools/ShippingGen5AccReads.lean` + `Tests/Gen5/AccReadsCheck.lean` (0f120373, Pod-built; clean build is the coder's).

Tags: `[S]` source read in this worktree (or the named branch); `[B]` built in the Pod; `[E]` the statement below elaborates (all proofs `sorry`) in a Pod scratch file (`kjob lake env lean`, scratchpad, **not committed**; exit 0, no error).
Wording rule: "not found" means *this investigation found no supplier or route*, never "impossible". A MUTANT is a rejection of a changed, well-typed statement by signature / defeq, **not** a semantic counterexample. Conditional results are INTERMEDIATE, never completion.

## 0. Summary

| item | result of the survey |
|---|---|
| `AccKeepChildStmt K L Reach` | **Closes with no premise at all** (not even a route premise): M3's `keepChild_proved` (`Tools/ShippingGen2KeepChild.lean:360`, `[S]`) is generic in `L P Reach` and uses `IHAt` only through `synthesizeChild_shipsRes`'s miss case and `CacheShips` through the hit case. The Acc copy uses `AccIHAt` and `CacheAcc` in the same two places (§2.1, 11 declarations). To be implemented after approval. |
| `AccServed0Stmt K L Reach` | **Reduces to four named premises**: `hcl` (the closure `∀ X c, Reach X → CallEdge K X c → Reach c`; for `Reach := ReachEdge K Top` it is the constructor `ReachEdge.edge`, supplied), `MachineRouteAt env₀ L Reach`, `ReadsSupplyAt env₀ L Reach` (rev2 §B, built), and either `RunDataLink K L Reach` (rev1 form) or `ReachCover K Reach` + `DataOfShape K` (this revision's refinement, §2.4). Everything between the premises and the statement (head, machine branch, closings, key match) is an Acc copy of M3 text (§1) and is stated in §2.2-§2.4. |
| not closed | `MachineRouteAt` (§3 row S1), `RunDataLink`/`ReachCover`/`DataOfShape` (S2), `ReadsSupplyAt` for a non-strengthened `L` (S3, rev2), `OffRouteServes` (S4), `GenSFacts` (S5). Listed in §3 with what was read. |

No new law, no TRUSTED boundary, no FG change, no change to `T1Hyp`/`T1HypND`, no shared or compiler file. All new Lean goes into new files (§4).

## 1. The survey: M3 sources, what each gives, what the Acc copy needs

`InvAt L P Reach D = JQC L.O D w ∧ CacheShips L P Reach (cv w)`; `AccInvAt K L Reach D = JQC L.O D w ∧ CacheAcc K Reach (cv w)` (A4). `CacheAcc` needs `cacheAcc_empty` and `cacheAcc_insert` (A2, `[B]`); the insert needs the inserted value's `Reach n → Acc n`, which `AccIHAt D` gives at the miss run. Only `cv`, `sv`, `dv`, `quiet` are used by the frame lemmas, so every M3 frame step is unchanged (`stableA_accInvAt`, A4, `[B]`).

| # | M3 item (file:line `[S]`) | Acc counterpart (name in §2) | premises of the counterpart | state |
|---|---|---|---|---|
| 1 | `tripleInv_depthSet` KeepChild:71, `tripleInv_depthModify` :82, `finInv` :100 | `tripleAcc_depthSet`, `tripleAcc_depthModify`, `finAcc` | `hA` | closes (copy; `hk.2` cache frame is `cv` unchanged) |
| 2 | `core_tripleAInv` :133, `full_tripleAInv` :209, `hentryT_of_bodyInv` :225 | `core_tripleAcc`, `full_tripleAcc`, `hentryT_of_bodyAcc` | `hbody` (the `AccBodyKeeps (D+1)` instance) | closes (copy) |
| 3 | `tripleInv_cacheGet` :239 | `tripleAcc_cacheGet` | `hA` | closes (copy) |
| 4 | `cacheShips_insert` :255, `invAt_insert_runs` :271 | `cacheAcc_insert` (A2, `[B]`), `accInvAt_insert_runs` | `RealChildA`, `Reach n → Acc n` | closes (copy; `jqc_insert_runs` is generic) |
| 5 | `synthesizeChild_tripleInv` :292, `synthesizeChild_shipsRes` :331, `keepChild_proved` :360 | `synthesizeChild_tripleAcc`, `synthesizeChild_accRes`, `accKeepChild_proved` | `AccIHAt D` (miss case), `CacheAcc` (hit case) | closes (copy) = **`AccKeepChildStmt`** |
| 6 | `cacheShips_empty` ServedRun:47, `tripleInv_clear` :58 | `cacheAcc_empty` (A2 `[B]`), `tripleAcc_clear` | `hA` | closes (copy) |
| 7 | `core_reads_invAt0` ServedRun:80 (head + clear, D=0 / D>0) | `coreHead_accInvAt` (head only, over `coreHead X`, the form `core_chain`/`RunReadsAt` already exposes: `Tools/ShippingEntryReadsLinked.lean:165`, `Tools/ShippingGen5RunReads.lean:69` `coreHead_jqcA`) | `JQC L.O D w`, `D = 0 ∨ CacheAcc K Reach (cv w)` | closes (copy of `coreHead_jqcA` with `tripleAcc_clear`/`stableA_accInvAt`). **Why not `core_reads_invAt0` itself:** its conclusion hides the `coreHead` run, and `ChainReadsAt` (rev2 §B.2) needs `RunsTo (coreHead X) w s w1`. |
| 8 | `synthesizeFromConst_machine_invAt` ServedRun:178; RR2 `fromConst_machine_linkA` RunReads:139 | `fromConst_machine_accInvAt` (start world `w` explicit, as RR2, so the second `getEnv` is at the chain's `w3`) | `old`, `miss` (gates) | closes (copy) |
| 9 | `synthesizeChild_ships` ServedRun:309 | `synthesizeChild_acc` | `AccIHAt D`, `AccChildKeeps D` | closes (copy) |
| 10 | `ChildrenShipsI` :342, `closeInstsM_ships` :353, `closeInstsGM_ships` :388, `synthesizeMachineCertified_runsS` :445 | `ChildrenAccI`, `closeInstsM_acc`, `closeInstsGM_acc`, `synthesizeMachineCertified_runsAcc` | `AccIHAt n`, `AccChildKeeps n` | closes (copy). The Acc form of the last is **weaker** than M3's (it drops the `MReturns`/`closeLets`/`CloseCalls` conjuncts, which A5 does not use): `shape.insts = [] ∨ (shape.insts ≠ [] ∧ ∃ children, ChildrenAccI …)`. |
| 11 | [REACH] S3 `childrenShips_reached` (key match: ordinary instance ⇒ `Reach`) | `childrenAcc_reached` (K-form: `CallEdge K X c` + the closure `hcl` replace `T1Hyp.closed`) | `hcl`, `dataOf₀ K X = some d`, `d.shape = shape` | closes |
| 12 | `servedShips0_proved` Served:636 (its `hord1`/`hrow`, `T1Hyp.defines/closes`, trace) | `accServed0_of_route` / `accServed0_of_cover` (assembly of 6-11) | `hcl`, `MachineRouteAt`, `ReadsSupplyAt`, and `RunDataLink` (route) or `ReachCover` + `DataOfShape` (cover) | closes **given** the premises of S1-S3 |

*What is not copied.* M3's `soundX_ships_ran`, `SoundXAt` and the trace chain (Served:1-560, Served:560-636) establish the *trace* (`MachineTraceLBX (ServedP …)`); `AccServed0Stmt`'s conclusion is about the static edges only, so none of it is needed. `hord1` (G-ONEOUT-REACH, `hrow`) belongs to that trace chain (memory-origin entries of the one-output closing); `AccServed0Stmt` concerns only `child? = none` entries, and `ChildrenAccI` already carries the `child? = some y` arm as a disjunct, so **no `hrow`-like premise appears in this survey** (checked by reading `closeInstsM_ships`/`closeInstsGM_ships`, whose only extra premises are `IHAt`/`ChildKeepsInv`).

*What the survey found that rev1 did not say.* (a) `AccKeepChildStmt` needs **no** route premise (item 5). (b) The head must be copied over `coreHead` (item 7) because of `ChainReadsAt`. (c) `RunDataLink`, as stated in rev1 §B.2, is not derivable from `MachineDefinesR` by logic alone: `MachineDefinesR` is a `∀` over read worlds, and the existence of such a world with `ReadsAt env₀` is not a fact about the abstract `Void IO.RealWorld`. Inside a run the worlds exist
(the chain), so §2.4 states the alternative `accServed0_of_cover`, which derives the link from `ReachCover` (kit coverage), the kit field `genData₀_dataOf` (`Tools/ShippingGen5Acc.lean:41`, `[B]`) and `DataOfShape`, the first conjunct of DG-DATAOF's `dataOf_sound` (`kjob/g5do-r6:scripts/gen5/DG_DATAOF_FREEZE.md` §2.4, `[S]`), together with `envR_of_readsAt`/`ci_of_readsAt` (`Tools/ShippingGen5Env.lean:52-63`, `[B]`) at the chain worlds.

## 2. Complete types `[E]`

Common preamble and variables of the statements (as in `Tools/ShippingGen5AccInd.lean`; `AccInvAt`, `AccIHAt`, `AccChildKeeps`, `AccKeepChildStmt`, `AccServed0Stmt`, `CacheAcc`, `CallEdge`, `CallRel`, `ReachEdge`, `ReachCover`, `dataOf₀` are those of A1-A4; `ReadsSupplyAt`, `ChainReadsAt` those of `Tools/ShippingGen5AccReads.lean`):
```lean
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingEntrySoundness
open Tools.ShippingEntryReadsLinked (CoreSaved coreHead)
open Tools.ShippingChildInv
open Tools.ShippingChildInvA (AdmCtx FramedA)
open Tools.ShippingChildVCA (JQ StableA)
open Tools.ShippingChildCacheA
open Tools.ShippingChildBndCore (cv dv sv)
open Tools.ShippingChildFrontCP
open Tools.ShippingMachineEntry
open Tools.ShippingGen5Env (ReadsAt MachineDefinesR)
open Tools.ShippingChildRunAKids (MachineClosesAtA)

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
variable (K : AssignKit ι dom env₀)
```

### 2.1 A5a — `AccKeepChildStmt` (file `Tools/ShippingGen5AccKeep.lean`)
```lean
def AccEInv (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Exception → Void IO.RealWorld → Prop :=
  fun e w => AccInvAt K L Reach D w ∧ OkExc e

theorem tripleAcc_depthSet (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D v : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (ST.Ref.set sparkleSynthDepth v : MetaM Unit)
      (fun _ => AccInvAt K L Reach v) R := by sorry /- proof: implementation -/

theorem tripleAcc_depthModify (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat) (f : Nat → Nat)
    {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (ST.Ref.modify sparkleSynthDepth f : MetaM Unit)
      (fun _ => AccInvAt K L Reach (f D)) R := by sorry /- proof: implementation -/

theorem finAcc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (d : Nat)
    (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
    (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
    (m7 : Std.HashMap String String) :
    Triple mctx mref cctx cref (AccInvAt K L Reach (d + 1))
      (do
        ST.Ref.modify sparkleSynthDepth fun x => x - 1
        if (d != 0) = true then do
            ST.Ref.set sparkleFvarValueMap m1
            ST.Ref.set sparkleWireWidthCache m2
            ST.Ref.set sparkleLetWireCache m3
            ST.Ref.set sparkleLoopWireCache m4
            ST.Ref.set sparkleWireCanon m5
            ST.Ref.set sparkleSubInstanceOutputs m6
            ST.Ref.set sparkleSingleOutInstanceCache m7
          else pure () : MetaM Unit)
      (fun _ => AccInvAt K L Reach d) (AccEInv K L Reach d) := by sorry /- proof: implementation -/

theorem core_tripleAcc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat) (hD : 1 ≤ D) (declName : Name)
    (hbody : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (AccInvAt K L Reach (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinationalCore declName [] false)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D) := by sorry /- proof: implementation -/

theorem full_tripleAcc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} {declName : Name}
    (hcore : Triple mctx mref cctx cref (AccInvAt K L Reach D)
      (synthesizeCombinationalCore declName [] false) (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D)) :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinational declName)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D) := by sorry /- proof: implementation -/

theorem hentryT_of_bodyAcc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} (hD : 1 ≤ D) {c : Name}
    (hbody : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (AccInvAt K L Reach (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst)) :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinational c)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D) := by sorry /- proof: implementation -/

theorem tripleAcc_cacheGet (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat) :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (sparkleChildCache.get : MetaM _)
      (fun m w => AccInvAt K L Reach D w ∧ m = cv w) (AccEInv K L Reach D) := by sorry /- proof: implementation -/

theorem accInvAt_insert_runs (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx)
    {D : Nat} {n : Name} {r : Res} {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (hw : AccInvAt K L Reach D w) (hr : RealChildA L.O n r) (hs : Reach n → Acc (CallRel K) n)
    (h : RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert n r) :
      MetaM Unit) mctx mref cctx cref w u w') :
    AccInvAt K L Reach D w' := by sorry /- proof: implementation -/

theorem synthesizeChild_tripleAcc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} {n : Name} (hIH : AccIHAt K L Reach D)
    (hentryT : Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinational n)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D)) :
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeChild n)
      (fun r w => RealChildA L.O n r ∧ (Reach n → Acc (CallRel K) n) ∧ AccInvAt K L Reach D w)
      (AccEInv K L Reach D) := by sorry /- proof: implementation -/

theorem synthesizeChild_accRes (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} {n : Name} {w w' : Void IO.RealWorld} {r : Res}
    (hw : AccInvAt K L Reach D w) (hIH : AccIHAt K L Reach D)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w r w') :
    Reach n → Acc (CallRel K) n := by sorry /- proof: implementation -/

theorem accKeepChild_proved (L : Laws mref cref) (Reach : Name → Prop) :
    AccKeepChildStmt K L Reach := by sorry /- proof: implementation -/
```

### 2.2-2.4 A5b — head, machine branch, closings, assembly (file `Tools/ShippingGen5AccServed.lean`)
```lean
open Sparkle.IR.Machine
open Sparkle.IR.AST (Design)
open Tools.ShippingMachineAuto (MachineData)

def MachineRouteAt (env₀ : Environment) (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∃ shape : MachineShape, MachineDefinesR env₀ mctx mref cctx cref c shape ∧ MachineClosesAtA L.O mctx cctx c shape

def RunDataLink (L : Laws mref cref) (Reach : Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∀ shape : MachineShape, MachineDefinesR env₀ mctx mref cctx cref c shape →
      ∃ d, dataOf₀ K c = some d ∧ d.shape = shape

theorem tripleAcc_clear (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) (D : Nat) {R : Exception → Void IO.RealWorld → Prop} :
    Triple mctx mref cctx cref (JQ L.O.quiet D) (sparkleChildCache.set {} : MetaM Unit)
      (fun _ => AccInvAt K L Reach D) R := by sorry /- proof: implementation -/

theorem coreHead_accInvAt (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {X : Name} {D : Nat} {w w1 : Void IO.RealWorld} {s : CoreSaved}
    (hw : JQC L.O D w) (hc : D = 0 ∨ CacheAcc K Reach (cv w))
    (hh : RunsTo (coreHead X) mctx mref cctx cref w s w1) :
    AccInvAt K L Reach (D + 1) w1 := by sorry /- proof: implementation -/

theorem fromConst_machine_accInvAt (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {tenv : Environment} {b : Bool} {X : Name} {n : Nat}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none) (miss : mixedCertifiedShape? false [] ci isInst = none)
    (hw : AccInvAt K L Reach n w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X [] false true
      ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR' : Environment) (w₁ : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w envR' w₁ ∧
      ∀ shape, machineShape? false [] ci (structEnv envR') = some shape →
        ∃ (r : Option Res) (w₂ : Void IO.RealWorld),
          RunsTo (synthesizeMachineCertified (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b) X shape)
            mctx mref cctx cref w₁ r w₂ ∧ AccInvAt K L Reach n w₁ ∧ (∀ res, r = some res → res = (m, d)) := by sorry /- proof: implementation -/

def ChildrenAccI (L : Laws mref cref) (Reach : Name → Prop) (shape : MachineShape) (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    ((shape.instOrigins.getD k .ord).child? = some y ∨
      (RealChildA L.O (shape.insts[k]).1 y ∧ (Reach (shape.insts[k]).1 → Acc (CallRel K) (shape.insts[k]).1)))

theorem synthesizeChild_acc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} {n : Name} {w w' : Void IO.RealWorld} {r : Res}
    (hw : AccInvAt K L Reach D w) (hIH : AccIHAt K L Reach D) (hKI : AccChildKeeps K L Reach D)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w r w') :
    RealChildA L.O n r ∧ (Reach n → Acc (CallRel K) n) ∧ AccInvAt K L Reach D w' := by sorry /- proof: implementation -/

theorem closeInstsM_acc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} (hIH : AccIHAt K L Reach D) (hKI : AccChildKeeps K L Reach D)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : AccInvAt K L Reach D w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) = some (m, d) ∧
      children.length = shape.insts.length ∧
      (∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
        (RealChildA L.O (shape.insts[k]).1 y ∧ (Reach (shape.insts[k]).1 → Acc (CallRel K) (shape.insts[k]).1))) ∧
      AccInvAt K L Reach D w' := by sorry /- proof: implementation -/

theorem closeInstsGM_acc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {D : Nat} (hIH : AccIHAt K L Reach D) (hKI : AccChildKeeps K L Reach D)
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : AccInvAt K L Reach D w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) = some (m, d) ∧ MemChildren shape children ∧
      ChildrenAccI K L Reach shape children ∧ AccInvAt K L Reach D w' := by sorry /- proof: implementation -/

theorem synthesizeMachineCertified_runsAcc (L : Laws mref cref) (Reach : Name → Prop)
    (hA : AdmCtx L.O.quiet mctx cctx) {n : Nat} {tenv : Lean.Environment}
    (hIH : AccIHAt K L Reach n) (hKI : AccChildKeeps K L Reach n)
    {b : Bool} {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (hw : AccInvAt K L Reach n w)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w') :
    (shape.insts = [] ∨ (shape.insts ≠ [] ∧ ∃ children, ChildrenAccI K L Reach shape children)) := by sorry /- proof: implementation -/

theorem childrenAcc_reached {L : Laws mref cref} {Reach : Name → Prop}
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c) {X : Name} (hX : Reach X)
    {d : MachineData} (hd : dataOf₀ K X = some d) {shape : MachineShape} (hsh : d.shape = shape)
    {children : List Res} (hch : ChildrenAccI K L Reach shape children) :
    ∀ c, CallEdge K X c → Acc (CallRel K) c := by sorry /- proof: implementation -/

theorem accServed0_of_route (L : Laws mref cref) (Reach : Name → Prop)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hRoute : MachineRouteAt env₀ L Reach) (hLink : RunDataLink K L Reach)
    (hRS : ReadsSupplyAt env₀ L Reach) : AccServed0Stmt K L Reach := by sorry /- proof: implementation -/


def DataOfShape : Prop :=
  ∀ (E : ConstantInfo) (se : StructEnv) (s : MachineShape) (d : MachineData), K.dataOf E se s = some d → d.shape = s

theorem machineClosesAtA_of_closes (L : Laws mref cref) {c : Name} {shape : MachineShape}
    (h : MachineCloses mctx mref cctx cref c shape) : MachineClosesAtA L.O mctx cctx c shape := by sorry /- proof: implementation -/

theorem accServed0_of_cover (L : Laws mref cref) (Reach : Name → Prop)
    (hcl : ∀ X c, Reach X → CallEdge K X c → Reach c)
    (hRoute : MachineRouteAt env₀ L Reach) (hcov : ReachCover K Reach) (hDS : DataOfShape K)
    (hRS : ReadsSupplyAt env₀ L Reach) : AccServed0Stmt K L Reach := by sorry /- proof: implementation -/
```

### 2.5 Notes on the types
* `machineClosesAtA_of_closes` is a bridge (`MachineCloses` has no `JQC`/depth premise; `MachineClosesAtA` is weaker): it only lets the existing suppliers of `MachineCloses` (`closes_of_data`, `Tools/ShippingMachineClosesData.lean:226`, no-call machines) feed `MachineRouteAt`.
* `accServed0_of_route` and `accServed0_of_cover` have the same conclusion; they differ only in how the shape link is obtained (premise `RunDataLink` vs derived in-run from `ReachCover`+`DataOfShape`). The proof of the second uses the chain worlds `w2`, `w3` of `ChainReadsAt` (`ReadsAt` there identifies `envR`, `envR'`, `ci` with `env₀`'s).
* `AccServed0Stmt` quantifies over `Reach X` and the run; both theorems take `hRS : ReadsSupplyAt env₀ L Reach` at the **same** `L` as the conclusion. For the FG's `L` this is not claimed (rev2 §B.3); the intended use is `L := L'` (quiet-strengthened), `hRS := readsSupply_of_quiet …` (rev2 `[E]`, now committed).

## 3. Open rows after rev3 (this investigation found no supplier or route for these, unless a path is named)

| row | what is needed | what was read | state |
|---|---|---|---|
| S1 `MachineRouteAt env₀ L Reach` | for each reached `c`: a `shape` with `MachineDefinesR env₀ …` and `MachineClosesAtA L.O …` | `MachineDefinesR`: `machineDefinesR_of_env` (`Tools/ShippingGen5EnvR.lean:50`, `[B]`) from three `env₀`-side facts: `env₀.find? c = some ci₀`, both certified gates `none` at `env₀`, `machineShape? … (structEnv env₀) = some shape` — facts about `env₀`; **no supplier found** (they are DG-COVER/DG-ENV census content, unsupplied). `MachineClosesAtA`: stated through the reader data `d`, not `P`: `closes_of_data` (no calls; needs `d.ok`, the body equation (both from `dataOf_sound`), and `d.letsOk = true`) then `machineClosesAtA_of_closes`; with calls `closes_of_data_calls` needs `CallsClose` (not derived anywhere found); `memCallee_closesA` (`Tools/ShippingSrm3Callee.lean:91`) needs `MemCalleeData` and `hord` (`ChildIfaceP` of `RealChildA` results). **No path found** for machines whose calls are ordinary children in general. | **unsupplied** |
| S2 `RunDataLink` / `ReachCover` + `DataOfShape` | the run's shape equals the reader data's shape | `ReachCover` (DG-COVER/ENV, unsupplied); `DataOfShape` is DG-DATAOF `dataOf_sound` conj. 1 (`kjob/g5do-r6`, not in this base); the kit field `genData₀_dataOf` is built (A1). | **unsupplied** (kit level) |
| S3 `ReadsSupplyAt env₀ L Reach` for the FG's `L` | `ReadsAt env₀` at the run's chain | rev2 §B.3: proved only at a quiet-strengthened `L'` from `QuietStrengthA` + `GetEnvFrame`; no route found for a non-strengthened `L`. | **unsupplied** |
| S4 `OffRouteServes` | reached names off route 3 (gate or legacy fallback) | rev1 §C.3: no route found; `accServed0_of_*` assume `MachineRouteAt` for **all** `Reach`, so off-route names are excluded by hypothesis, not served. | **unsupplied** |
| S5 `GenSFacts` | DG-FACTS/CAUSAL | not in scope of A5 | **unsupplied** |
| S6 `QuietStrengthA`, `GetEnvFrame`, `AdmDownA` | rev2 §B.3 | | **unsupplied** (named premises) |

## 4. Implementation plan after approval (new files; no shared or compiler file; lakefile `lean_lib` entries)

| file | contents | size indication (M3 lines copied) |
|---|---|---|
| `Tools/ShippingGen5AccKeep.lean` (A5a) | §2.1: `AccEInv`, items 1-5, `accKeepChild_proved` (+ the `iset`/`iget` macros copied under new names) | KeepChild:47-370 |
| `Tools/ShippingGen5AccServed.lean` (A5b) | §2.2-2.4: `MachineRouteAt`, `RunDataLink` (rev1 §B.2 texts), items 6-12, `DataOfShape`, `machineClosesAtA_of_closes`, `accServed0_of_route`, `accServed0_of_cover` | ServedRun:47-460, RunReads:69-140 |
| `Tests/Gen5/AccKeepCheck.lean`, `Tests/Gen5/AccServedCheck.lean` | TYPE (independent `Expected…`, `checkExpected` binder by binder, every theorem and definition), MUTANT (single-change well-typed statements; signature/defeq rejection, not semantic), AXIOMS (standard three), CLOSURE (explicit-value walker of `AccCheck` with its negative/clean controls and the unknown-name controls of `AccIndCheck`) | |

Mutant plan: `AccKeepChildStmt` without `1 ≤ D`; `AccServed0Stmt`'s premise `hcl` dropped from `accServed0_of_*`; `ChildrenAccI` with `Reach` premise dropped from the `Acc` conjunct; `childrenAcc_reached` without `hcl`; `accServed0_of_route` without `ReadsSupplyAt`; `coreHead_accInvAt` without the cache disjunct; `synthesizeChild_acc` without `AccChildKeeps`; conjunct-drop mutant of `fromConst_machine_accInvAt` (the `AccInvAt n w₁` conjunct). Counts will be reported as measured with their classification rule.

## 5. Not claimed
DG-ACC is **not** done. A5 is not implemented; §2.1-§2.4 are statements. `AccServed0Stmt` would be conditional on the rows S1-S3 (S4 excluded by hypothesis); `GenSFacts`, `MachineRouteAt`, `RunDataLink`/`ReachCover`/`DataOfShape`, `OffRouteServes`, `QuietStrengthA`, `GetEnvFrame`, `AdmDownA` have no producer found in this investigation. The results hold at the kit.
No change to FG, `T1Hyp`/`T1HypND`, a law, a TRUSTED boundary, or the compiler.

## 6. Implementation status (g5ac-r6; docs only, appended after the freeze approval)

Implemented as frozen, in new files: `Tools/ShippingGen5AccKeep.lean` (A5a, §2.1), `Tools/ShippingGen5AccServed.lean` (A5b, §2.2-§2.5), with `Tests/Gen5/AccKeepCheck.lean`
and `Tests/Gen5/AccServedCheck.lean`. Pod-built (not the coder's clean issue-linked build): `AccKeepChildStmt` is proved by `accKeepChild_proved` with **no** premise
(no route, data-link, reads or `hrow` premise). `AccServed0Stmt` is proved by `accServed0_of_route` / `accServed0_of_cover` **from the named premises** `hcl`,
`MachineRouteAt`, `ReadsSupplyAt`, and `RunDataLink` or `ReachCover` + `DataOfShape` (the premises are not supplied, §3). No premise was added to the frozen types. Two helper theorems
were added that are not in §2 (`getEnv_runs_exists`, `accServed_core`: the shared run analysis; covered by the AXIOMS / CLOSURE checks, not by TYPE).
The proof of `accServed_core` needs one fact the freeze did not spell out: a `getEnv` run exists at every world, so the second `getEnv` of the chain
can be exhibited before the body is unfolded (needed to read `old`/`miss` off `ChainReadsAt`); `getEnv_runs_exists` proves it (no new premise).

* "No `hrow`" holds only for the ordinary static edges (`child? = none` entries) that `AccServed0Stmt` talks about. It is **not** a statement about the supply of `ServedP`
  in general; M3's `hrow` belongs to the trace chain, which is not copied.
* `closes` rows of §1 are now proved (items 1-12) and may be counted as supply **of the statement, given the premises**; the premises are still unsupplied (S1-S6).
* `QuietStrengthA` / `AdmDownA` (and `QuietStrengthA`'s use in `readsSupply_of_quiet`) are copies of EnvQ's `QuietStrength` / `AdmDown`; they must be checked against the originals when EnvQ is
  integrated. EnvQ cannot be imported on this base, so `AccServedCheck` compares the definition **text** with `Tools/ShippingGen5EnvQ.lean` (positive and negative control).
* Mutants in the Checks are rejections by signature / defeq, not semantic counterexamples.
Still not supplied: `MachineRouteAt`, `RunDataLink` / `ReachCover` / `DataOfShape`, `ReadsSupplyAt` for the FG's `L`, `OffRouteServes`, `GenSFacts`, `QuietStrengthA`/`GetEnvFrame`/`AdmDownA`.
This is not DG-ACC, M5 or FG completion.
