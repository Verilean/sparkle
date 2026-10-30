# DG-CLOSINGRUN next unit — freeze r4 (Issue sparkle-gen5-dg-closingrun)

**FOR REVIEW. Docs only; no Lean file is edited by this commit.** Base: `kjob/g5cr-r3` `97bdfeff` (freeze r3, `changes_requested`: design
accepted, full types required). Supersedes `DG_CLOSINGRUN_FREEZE_R3.md` §1–§3 (r3 §0 survey, §4 supplier table, §6 answers stand).
Existing `Tools/ShippingGen5ClosingRun.lean` (`ClosingRun`, `PortsServed`, CR0–CR4, `closingRun_of_run`, `stop_of_run`) is NOT edited;
`stop_of_run` keeps its name and type (g4fb-fb7 uses it).

Wording: "not found" = this survey did not find a supplier / route, not a claim of impossibility. A mutant is a rejection by signature /
defeq of a changed statement, not a semantic counterexample. A new unsupplied premise is never counted as supply. No new TRUSTED
boundary, law, FG/guarantee change, shared-definition change (`ShippingGen2Defs`, `T1Hyp`, `T1HypND`, `Elab*` untouched); `GenWF`
not strengthened; no scope reduction.

## 0. How this freeze was checked (R1)
Every Lean block in §1 is the text that was ELABORATED in the Pod (`kjob lake build` of an uncommitted scratch module that imports
`Tools.ShippingGen5ClosingRun`, exit 0, 754 jobs; the scratch file and its lakefile entry were removed before this commit, and nothing
Lean is in this commit). In that scratch every declaration elaborated against the real definitions; the proofs of `ClosingRun.closingShared`,
`closingRun0_of_run`, `closingRun_of_run_ga`, `closingRun_nonempty_of_premises`, `gen_of_closingShared`, `not_closingShared_false`
were already accepted there. The only `sorry` are the bodies of the two statements whose proofs are the implementation (`invAt_w5_of_runReadsAt_JQC`,
`closingShared_of_run`, marked `-- IMPL`); in the real file they are proved and no `sorry` remains (Check enforces it). The ambient
`open`/`variable` preamble is part of the text (scope-bound): nothing is an unbound ambient. Expected types in the Check are
written independently from this document (as fully bound `Prop` defs), NOT derived from the implementation's signature.

## 1. The full types (verbatim, elaborated)
New file `Tools/ShippingGen5ClosingRun2.lean`, `namespace Tools.ShippingGen5ClosingRun2`; check file `Tests/Gen5/ClosingRun2Check.lean`.

```lean
import Tools.ShippingGen5ClosingRun
set_option autoImplicit false
namespace Tools.ShippingGen5ClosingRun2
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.IR.Builder
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildFrontCP
open Tools.ShippingChildRunA Tools.ShippingChildRunAMain Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids
open Tools.ShippingGen2 Tools.ShippingGen5RunReads Tools.ShippingGen5ClosingRun

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

def ClosingShared (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ (b : Bool) (ci : ConstantInfo) (envR envR' : Environment) (w5 w6 : Void IO.RealWorld)
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

theorem ClosingRun.closingShared {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : ClosingRun L P Reach mctx cctx X p Gen w w' raw D) :
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D := h.shared

theorem invAt_w5_of_runReadsAt_JQC (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design} {b : Bool}
    {ci : ConstantInfo} {envR envR' : Environment} {shape : MachineShape} {w5 w6 : Void IO.RealWorld}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hr : RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' shape w5 w6) :
    InvAt L P Reach (dv w + 1) w5 := sorry -- IMPL

theorem closingShared_of_run (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hw : JQC L.O (dv w) w) (hc : dv w = 0 ∨ CacheShips L P Reach (cv w))
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingShared L P Reach mctx cctx X p Gen w w' raw D := sorry -- IMPL

structure ClosingRun0 (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop where
  run    : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  start0 : Start L mctx cctx w
  depth0 : dv w = 0
  shared : ClosingShared L P Reach mctx cctx X p Gen w w' raw D

theorem closingRun0_of_run (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop)
    (hord : ∀ q : Pkg ι dom, DataOk q → q.d.shape.instFields = [] →
      ∀ k, k < q.d.shape.insts.length → (q.d.shape.instOrigins.getD k .ord).child? = none)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context}
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hs : Start L mctx cctx w) (hd0 : dv w = 0)
    (hIH : IHAt L P Reach 1) (hKI : ChildKeepsInv L P Reach 1)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (Gen : ConstantInfo → Environment → Environment → Prop)
    (hGen : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR') :
    ClosingRun0 L P Reach mctx cctx X p Gen w w' raw D := by
  have hw : JQC L.O (dv w) w := by rw [hd0]; exact hs.2
  have h1 : dv w + 1 = 1 := by rw [hd0]
  rw [← h1] at hIH hKI
  exact ⟨hrun, hs, hd0, closingShared_of_run L P Reach DataOk hord hT hs.1 hR hP hw (Or.inl hd0) hIH hKI hrun Gen hGen⟩

theorem closingRun_of_run_ga (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hT : T1HypND L P Reach DataOk)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {X : Name} {p : Pkg ι dom} (hR : Reach X) (hP : P X = some p)
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hst : InvAt L P Reach (dv w) w)
    (hIH : IHAt L P Reach (dv w + 1)) (hKI : ChildKeepsInv L P Reach (dv w + 1))
    (h1 : 1 ≤ dv w)
    (hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w')
    (GA : ConstantInfo → StructEnv → Pkg ι dom → Prop)
    (hGA : ∀ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 →
      GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR))
        (structEnv envR') p) :
    ClosingRun L P Reach mctx cctx X p
      (fun ci envR envR' => GA (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
        (structEnv envR)) (structEnv envR') p) w w' raw D :=
  closingRun_of_run L P Reach DataOk hrow hT hA hR hP hst hIH hKI h1 hrun _ hGA

structure ClosingPremises (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (mctx : Meta.Context) (cctx : Core.Context) (X : Name) (p : Pkg ι dom)
    (w w' : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Design)
    (Gen : ConstantInfo → Environment → Environment → Prop) : Prop where
  hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true
  hT   : T1HypND L P Reach DataOk
  hA   : AdmCtx L.O.quiet mctx cctx
  hR   : Reach X
  hP   : P X = some p
  hst  : InvAt L P Reach (dv w) w
  hIH  : IHAt L P Reach (dv w + 1)
  hKI  : ChildKeepsInv L P Reach (dv w + 1)
  h1   : 1 ≤ dv w
  hrun : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'
  hGen : ∀ b ci envR envR' w5 w6,
    RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 → Gen ci envR envR'

theorem closingRun_nonempty_of_premises {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {DataOk : Pkg ι dom → Prop} {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    (h : ClosingPremises L P Reach DataOk mctx cctx X p w w' raw D Gen) :
    Nonempty (ClosingRun L P Reach mctx cctx X p Gen w w' raw D) :=
  ⟨closingRun_of_run L P Reach DataOk h.hrow h.hT h.hA h.hR h.hP h.hst h.hIH h.hKI h.h1 h.hrun Gen h.hGen⟩

theorem gen_of_closingShared {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {Gen : ConstantInfo → Environment → Environment → Prop}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : ClosingShared L P Reach mctx cctx X p Gen w w' raw D) :
    ∃ b ci envR envR' w5 w6,
      RunReadsAt mctx mref cctx cref X w w' raw D b ci envR envR' p.d.shape w5 w6 ∧ Gen ci envR envR' := by
  obtain ⟨b, ci, envR, envR', w5, w6, -, -, -, -, hr, hg, -⟩ := h
  exact ⟨b, ci, envR, envR', w5, w6, hr, hg⟩

theorem not_closingShared_false {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {mctx : Meta.Context} {cctx : Core.Context} {X : Name} {p : Pkg ι dom}
    {w w' : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : ClosingShared L P Reach mctx cctx X p (fun _ _ _ => False) w w' raw D) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg, -⟩ := h
  exact hg

end Tools.ShippingGen5ClosingRun2
```

### 1.1 Notes on the types
* `mctx cctx` are binders of `ClosingShared` because `RunReadsAt mctx mref cctx cref …` mentions them. They are NOT droppable (the r3 note that
  said the implementer may drop them is withdrawn).
* `ClosingShared` is definitionally the type of `ClosingRun.shared` (`ClosingRun.closingShared` is `h.shared`, accepted by the elaborator).
* `invAt_w5_of_runReadsAt_JQC` (statement; proof = the body of `invAt_w5_of_runReadsAt` with `coreHead_invAt0 … hw hc hh`): it takes
  `JQC L.O (dv w) w` and `dv w = 0 ∨ CacheShips …`; the existing lemma is the case `hw := hst.1`, `hc := Or.inr hst.2`.
* `closingShared_of_run` (IMPL; proof = the body of `closingRun_of_run` after `hdecl`): `runReads_of_run L.O hA hw.1 hc' hrun hdef hcl` with
  `hc' : dv w = 0 ∨ CacheInvA (cv w) := hc.imp id (fun _ => hw.2)` (`hw.2 : CacheInvA` is the second half of `JQC`; `JQ` is `hw.1`; the old lemma passed
  `hst.1.1` / `Or.inr hst.1.2`).
  `invAt_w5_of_runReadsAt_JQC … hw hc hrr`; `synthesizeMachineCertified_runsS … hIH hKI hw5 …`; `hord1 := fun hf k hk => hord p hDp hf k hk`.
  Same `t t' d₀ children` are passed to `soundX_ships_at` and into the block (no re-obtaining). No `T1Hyp.dec`; no `hrow`; no `hlim`; no `h1`.
* `hord` is the SEMANTIC form (`child? = none` on every instance when `instFields = []`), weaker than `hrow` (`hord_of_row`, `DataBridge:57`).
  It is a **connection port, not a supply**: no run-derived supplier of `hord`/`hrow` was found by this survey.

### 1.2 Depth placement (R1 second item)
* **`hd0` position.** `closingRun0_of_run` takes `hs : Start L mctx cctx w` and `hd0 : dv w = 0` separately. `Start` gives `JQC L.O 0 w`
  (`hs.2`); the transport `JQC L.O 0 w → JQC L.O (dv w) w` is `by rw [hd0]; exact hs.2` and happens INSIDE `closingRun0_of_run` (see the elaborated
  proof). The shared theorem `closingShared_of_run` consumes `hw : JQC L.O (dv w) w` and `hc := Or.inl hd0`, so there is no `JQC 0` vs `JQC (dv w)` mismatch below that line.
  `hA := hs.1`.
* **`hIH` / `hKI` depth.** `closingShared_of_run` takes them at `dv w + 1` (same as `closingRun_of_run`). `closingRun0_of_run` takes them at the
  literal depth `1` (what a depth-0 call needs) and transports with `h1 : dv w + 1 = 1 := by rw [hd0]`, `rw [← h1] at hIH hKI` (elaborated).
  They remain PREMISES: they are supplied inside the T1 induction (`ih_allPF`), not by this unit.
* `ClosingRun0` has no `stop` field: `core_tripleAInv` needs `1 ≤ D`, and no triple giving `InvAt 0` at the end world of a depth-0 core run was found.
  `start0 : Start …` is `JQC 0` (not `InvAt 0`); `InvAt (dv w + 1) w5` appears inside `shared`. `ClosingRun0` is a separate structure, not a replacement of `ClosingRun`.

## 2. What each unit is, and what it is not
| unit | status | counts as supply progress? |
|---|---|---|
| **depth-0 shared-block connection** (`closingShared_of_run`, `closingRun0_of_run`, `invAt_w5_of_runReadsAt_JQC`) | Priority. Provable now from existing lemmas (the shared proof is `closingRun_of_run`'s body generalised from `InvAt (dv w)` to `JQC (dv w) ∧ (dv w = 0 ∨ CacheShips)`). Closes the depth-0 `start`/shared gap of the NESTED connection; the depth-0 `stop` is NOT closed. | Yes, for the depth-0 shared block only |
| **U-B GA wrapper** (`closingRun_of_run_ga`) | An instance of `closingRun_of_run` with `Gen` unfolded to the DGEN §3 shape and `GA` an abstract predicate. `hGA` is exactly `hGen` unfolded. | **No** (packaging) |
| **U-C bundle/projections** (`ClosingPremises`, `closingRun_nonempty_of_premises`, `gen_of_closingShared`, `not_closingShared_false`) | The premises of `closingRun_of_run` as one structure; `Nonempty` is `⟨closingRun_of_run …⟩`; `Gen` is not decorative (a projection of the block; `Gen := False` is refuted). | **No** (packaging). Not a non-vacuity proof. |

U-C wording: *if* every field of `ClosingPremises` holds, *then* `Nonempty (ClosingRun …)`. This is a **sufficient condition**; it is not claimed that
these premises are necessary, nor equivalent to the existence of a `ClosingRun`, nor that they are the only route. Non-vacuity (a concrete `Laws`/`Pkg`/run/
world satisfying all premises) is NOT supplied; no route found (no concrete `Laws` in the tree).

## 3. OPEN (unchanged; none is counted as done by this unit)
`hrow`/`hord` (R6), `hGen` / `GeneratedAt` (not in the tree; `hGA` is not supply), concrete non-vacuity, depth-0 `stop`, the T1 induction supplying
`hIH`/`hKI`, final T1/FG connection. No Issue / M5 / FG completion is claimed.

## 4. Check plan (`Tests/Gen5/ClosingRun2Check.lean`)
* Independent Expected TYPES (fully bound `def … : Prop`, written from this document, not from the implementation): `ClosingShared` (vs the telescope of
  `ClosingRun.shared`'s type, `isDefEq`), `invAt_w5_of_runReadsAt_JQC`, `closingShared_of_run`, `ClosingRun0` (structure comparison: field names + types),
  `closingRun0_of_run`, `closingRun_of_run_ga`, `ClosingPremises`, `closingRun_nonempty_of_premises`, `gen_of_closingShared`, `not_closingShared_false`.
* Positive controls first: the SAME comparator (reducible transparency) accepts each independently written Expected type and re-accepts the existing
  `ClosingRun`, `stop_of_run`, `closingRun_of_run` Expected types (without editing `ClosingRunCheck.lean`).
* Well-typed one-point mutants rejected by the same comparator (signature/defeq rejection, NOT semantic counterexamples): `hord` without `k < length`;
  `hord` with `instFields ≠ []`; `hc` dropped; `hw : JQC L.O 0 w` instead of `dv w`; `InvAt (dv w)` instead of `dv w + 1` at `w5`; `hIH` at `dv w` / `2`
  in `closingRun0_of_run`; `ClosingRun0` with a `stop` field; `depth0 : dv w = 1`; `GA` at `structEnv envR` instead of `envR'`; `entryConst false …`;
  `Gen := True`; `T1Hyp` instead of `T1HypND`; `ClosingShared` without the `mctx`/`cctx` binders is ill-typed (not a mutant).
* Explicit value+type closure with negative controls (direct, other-namespace helper, raw `.proj`, recursor) and clean controls: no `T1Hyp` field,
  `T1Hyp.dec`, `core_reads_invAt0`, `BodyStepC`, `soundX_ships_ran`, `servedShips0_proved`, `TopShips`, `ofReduceBool`. AXIOMS: standard only. No `sorry`.
* Build: the implementing agent commits Lean with "clean build は coder が実行"; the coder does the clean issue-linked build.

## 5. Questions for the reviewer
1. Are the §1 types (verbatim, elaborated) the required complete types, with `hd0`/`hIH`/`hKI` placement as §1.2?
2. Is the U-C wording (conditional sufficiency + projections, not non-vacuity) and the "U-B/U-C are packaging" row in §2 acceptable?
