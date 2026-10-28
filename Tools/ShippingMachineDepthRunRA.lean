import Tools.ShippingMachineDepthRunR
import Tools.ShippingMachineCallsLinkedTNR
import Tools.ShippingServedRealA
-- BUILT (unit SR2, par/u-sr2): sr2c exit 0; audit sr2d exit 0 (see REPORT-SR2.md). No `sorry`, no `axiom`, no `native_decide`, no new law / field.
-- Law witness `O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref`; no RefLaws / ChildBnd / InvW / ChildRanIn in the statements.

/-! # Unit SR2: consumers 1 and 2 of `ServedReal` on the new boundary

* `ChildRanInA O c mctx cctx` — analogue of `ChildRanIn` (old, `InvW` at the start world): some run of
  `c`'s entry in those contexts, from a world whose data are `AdmCtx`, `JQC O (dv w)` (quiet, synthesis ref,
  cache half). A HISTORY of a past run (as `RealChildA`).
* `MachineRunNCA` — analogue of `MachineRunNC`: the child's core run, `MachineDefines`, the closing
  `MachineClosesAtA` (instead of `MachineClosesAt`), its boundary `BndA` (a fact of the run's start data), the
  post-processing, `ExtendsAway`, `NoInstOf`.
* `machineRunNCA_of_real` — analogue of `machineRunNC_of_real`: from `RealChildA O c (mc, Dc)`
  (via `realChildA_inv`: `AdmCtx`, cache half, `sv`, quiet), `BodyStepC O`, the translator `htr` at `JQC O n`,
  `machine_children_realA'` (the child's start depth is `D := dv w`). `_main`: `BodyStepC`/`htr` from `T`.
* `machine_linkedT_callsRNA` — the composed head `machine_linkedT_callsRN` with `ServedRealA O` in the
  trace type and `hrunN` quantified over the `realChildA_inv` data (`AdmCtx`, `CacheInvA (cv w)`, `sv`, quiet)
  instead of `InvW`.

SCOPE: these reach a CHILD-HISTORY statement (every child run that served a call satisfies the child's
predicate; the parent's trace WITH child history). They are NOT a composed-parent semantic equivalence:
`hcalls`, `hrunN`, `hctx`, `hcl` stay premises of the heads. `RealChildA` is a history of past synthesis
results, not correctness in the current environment; `JQC` is not freshness; not runtime fit. -/
namespace Tools.ShippingMachineDepthRunRA

open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge
open Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierMono
open Tools.ShippingMachineDepth Tools.ShippingMachineDepthChild Tools.ShippingMachineDepthRun
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingEntrySoundness (RunsTo)
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA
open Tools.ShippingChildDepthC Tools.ShippingChildComposeC Tools.ShippingChildRunAKids
open Tools.ShippingChildRunAMain Tools.ShippingServedRealA Tools.ShippingChildTranslateA
open Tools.ShippingChildFrontCP Tools.ShippingMachineCallsLinkedT Tools.ShippingMachineCallsLinkedTN Tools.ShippingMachineCallsLinkedTNR
open Tools.ShippingChildBndCore Tools.ShippingChildBndInit Tools.ShippingMachineEntry

variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- `ChildRanIn` on the new boundary: some run of `c`'s entry in these contexts, from a world with
the data `realChildA_inv` gives (a history of a past run). -/
def ChildRanInA (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (c : Name) (mctx : Meta.Context)
    (cctx : Core.Context) : Prop :=
  ∃ (w : Void IO.RealWorld) (r : Res) (w' : Void IO.RealWorld),
    AdmCtx O.quiet mctx cctx ∧ JQC O (dv w) w ∧
    RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w'

/-- `MachineRunNC` on the new boundary. -/
def MachineRunNCA (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (c : Name) (shape : MachineShape)
    (BndA : Meta.Context → Core.Context → Void IO.RealWorld → Module → Design → Prop)
    (mc : Module) (dsn : Design) : Prop :=
  ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (raw : Module) (D : Design),
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w' ∧
    AdmCtx O.quiet mctx cctx ∧ JQC O (dv w) w ∧
    MachineDefines mctx mref cctx cref c shape ∧
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c shape ∧
    BndA mctx cctx w raw D ∧
    (mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
     mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
    ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules) ∧
    NoInstOf raw.name raw.body

/-- **`machineRunNC_of_real` on the new boundary.** Premises: `O`, `BodyStepC O`, the translator at
`JQC O n` in admissible contexts (`htr`), the child's own boundary `hctx` (a fact of the run's start
data) and closing `hcl` (`MachineClosesAtA`, PREMISE, per child), `MachineDefines`, `hi`. -/
theorem machineRunNCA_of_real (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (hB : BodyStepC O)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx → ∀ (D : Nat)
      (tenv : Lean.Environment) e hint top named, KeepsCP mctx mref cctx cref (JQC O (D + 1))
        (translateExprToWire tenv e hint top named))
    {c : Name} {shape : MachineShape}
    {BndA : Meta.Context → Core.Context → Void IO.RealWorld → Module → Design → Prop}
    {mc : Module} {Dc dsn : Design}
    {mctx₀ : Meta.Context} {cctx₀ : Core.Context}
    (hreal : RealChildA O c (mc, Dc))
    (hcons : ∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g)
    (entry₀ : MachineDefines mctx₀ mref cctx₀ cref c shape)
    (hctx : ∀ (mctx : Meta.Context) (cctx : Core.Context),
      ChildRanInA O c mctx cctx → ∀ w raw D, JQC O (dv w) w → BndA mctx cctx w raw D)
    (hcl : ∀ (mctx : Meta.Context) (cctx : Core.Context) w raw D,
      ChildRanInA O c mctx cctx → BndA mctx cctx w raw D →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c shape)
    (hi : shape.insts ≠ []) :
    MachineRunNCA O c shape BndA mc dsn := by
  obtain ⟨mctx, cctx, w, w', hadm, hcache, hsv, hq, hrun⟩ := realChildA_inv hreal
  have hjqc : JQC O (dv w) w := ⟨⟨hq, hsv, rfl⟩, hcache⟩
  have hin : ChildRanInA O c mctx cctx := ⟨w, _, w', hadm, hjqc, hrun⟩
  have entry : MachineDefines mctx mref cctx cref c shape :=
    Tools.ShippingReflectCtx.MachineDefines.ctx entry₀
  have hBnd := hctx mctx cctx hin
  obtain ⟨raw, D, w1, hcore, hpost, hagree⟩ := synthesizeCombinational_design hrun
  have closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c shape :=
    hcl mctx cctx w raw D hin (hBnd w raw D hjqc)
  obtain ⟨t, t', d₀, children, _, hcc, _⟩ :=
    machine_children_realA' O hB hadm hcore entry (htr mctx cctx hadm (dv w)) closes
      ⟨hq, hsv, rfl⟩ (Or.inr hcache) hi
  have acyc : NoInstOf raw.name raw.body ∧ ∀ g ∈ D.modules, NoInstOf raw.name g.body := by
    rcases hcc with ⟨_, h⟩ | ⟨_, h, _⟩
    · obtain ⟨_, h1, h2, _⟩ := Tools.ShippingChildServe.closeInsts_acyclic h
      exact ⟨h1, h2⟩
    · obtain ⟨_, h1, h2⟩ := Tools.ShippingChildServe.closeInstsG_acyclic h
      exact ⟨h1, h2⟩
  refine ⟨mctx, cctx, w, w1, raw, D, hcore, hadm, hjqc, entry, closes, hBnd w raw D hjqc, hpost,
    ⟨?_, ?_⟩, acyc.1⟩
  · intro x r hx hD
    obtain ⟨g, hg, rfl⟩ := childMap_some.mp hD
    have hDc : moduleByName Dc.modules x = some g := by rw [hagree x hx]; exact hg
    have hn : g.name = x := Tools.ShippingMachineInst.moduleByName_name hg
    exact childMap_some.mpr ⟨g, by rw [← hn]; exact hcons g (moduleByName_mem hDc), rfl⟩
  · intro x r hD
    obtain ⟨g, hg, rfl⟩ := childMap_some.mp hD
    exact acyc.2 g (moduleByName_mem hg)

/-- `machineRunNCA_of_real` with `BodyStepC` and `htr` DERIVED from `T : RefLawsATele`. -/
theorem machineRunNCA_of_real_main (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref)
    {c : Name} {shape : MachineShape}
    {BndA : Meta.Context → Core.Context → Void IO.RealWorld → Module → Design → Prop}
    {mc : Module} {Dc dsn : Design}
    {mctx₀ : Meta.Context} {cctx₀ : Core.Context}
    (hreal : RealChildA O c (mc, Dc))
    (hcons : ∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g)
    (entry₀ : MachineDefines mctx₀ mref cctx₀ cref c shape)
    (hctx : ∀ (mctx : Meta.Context) (cctx : Core.Context),
      ChildRanInA O c mctx cctx → ∀ w raw D, JQC O (dv w) w → BndA mctx cctx w raw D)
    (hcl : ∀ (mctx : Meta.Context) (cctx : Core.Context) w raw D,
      ChildRanInA O c mctx cctx → BndA mctx cctx w raw D →
      MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c shape)
    (hi : shape.insts ≠ []) :
    MachineRunNCA O c shape BndA mc dsn :=
  machineRunNCA_of_real O (bodyStepC_of_tele O T)
    (fun _ _ hA D => htr_of_tele O hA T D) hreal hcons entry₀ hctx hcl hi

/-- **Consumer 2.** `machine_linkedT_callsRN` with `ServedRealA O` in the trace type and `hrunN`
quantified over the data of `realChildA_inv` (`AdmCtx`, `CacheInvA (cv w)`, `sv`, quiet) instead of
`InvW`. The rest of the proof is unchanged. -/
theorem machine_linkedT_callsRNA (n : Nat) {declName : Name} {d : MachineData} {m : Module} {dsn : Design}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX
      (Tools.ShippingServedRealA.ServedRealA O declName d.shape m dsn)
      declName d m dsn dom src ext extB lsrc)
    (hfe : d.shape.instFields ≠ [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hI : ∀ b ∈ d.bsIn.drop kD, b.2 ≠ .domain)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (bsC : Name → List (Name × MixedGateBinder)) (outsC : Name → List OutField)
    (S : ι → Name → (Nat → List Nat) → List (Nat → Nat))
    (PC : Name → Module → Prop)
    (hcalls : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k c,
      (d.shape.insts.map (·.1))[k]? = some c →
      MemFacts d.shape (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD (ext i bools bits) k c ∨
      SeqFactsRN (childMap dsn.modules) n d.shape dsn m.body (lsrc i bools bits) d.ls.length
        (d.bsIn.drop kD) kD (extB i bools bits) (ext i bools bits) bsC outsC (S i) PC k c)
    -- every run of a sequential child's entry, in the parent's contexts,
    -- satisfies the child's depth conditions
    (hrunN : ∀ (k : Nat) (c : Name), (d.shape.insts.map (·.1))[k]? = some c →
      (d.shape.instOrigins.getD k .ord).child? = none →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (mc : Module) (Dc : Design)
        (w w' : Void IO.RealWorld),
        AdmCtx O.quiet mctx' cctx' → CacheInvA O (cv w) → sv w = some synthesizeChild → O.quiet w →
        Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
          mctx' mref cctx' cref w (mc, Dc) w' →
        (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) →
        moduleByName dsn.modules mc.name = some mc → PC c mc) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = d.ss.length ∧
      ∃ lets : List String, lets.length = d.letBs.length ∧
      MachineWired declName d.shape ids cache m dsn regs lets ∧
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
        (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
        (kids : String → KT n),
        (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
          (fun j => (extB i bools bits j).val (T - 1 - t))
          (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
        (∀ t st r, r ∈ regs → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        -- the children start from reset
        (∀ (iname : String) (mc : Module), (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
          moduleByName dsn.modules mc.name = some mc → ResetN dsn n mc (kids iname)) →
        ∃ envs, runModuleTG (KSn (childMap dsn.modules) n) (Tools.ShippingEntrySoundness.weOf m)
            (childMap dsn.modules) m.body seed T ⟨st0, mems, kids⟩ = some envs ∧
          envs.length = T ∧
          ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
            (envs[j]'hj) o.name = f j := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, trace⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit hreset
  exact Tools.ShippingMachineLinkedTG.machine_linkedTG_of (KSn (childMap dsn.modules) n)
    (KSn_local (childMap dsn.modules) n) nd len rnd rlen llen wired trace hfe kD hkD hI hIlen hSL
    hSlen hLlen hNIn i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit
    (calls_hchildRN (childMap dsn.modules) n d.shape dsn m.body (lsrc i bools bits) d.ls.length
      (d.bsIn.drop kD) kD (extB i bools bits) (ext i bools bits) bsC outsC (S i) _ _ _ T kids hreset
      PC
      (fun k c mc iname argWs outs outWs hc hnone hst hout hke hmod => by
        have hk : k < d.shape.insts.length := by
          have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
        have hck : (d.shape.insts[k]).1 = c := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc; simpa using hc
        rcases hx.1 hfe k hk mc iname argWs outs outWs hst hout hke hmod with ⟨md, hmd, _⟩ | ⟨Dc, hrc, hcons⟩
        · rw [hnone] at hmd; cases hmd
        · rw [hck] at hrc
          obtain ⟨mctx', cctx', w, w', hadm, hcache, hsv, hq, hrun⟩ := realChildA_inv hrc
          exact hrunN k c hc hnone mctx' cctx' mc Dc w w' hadm hcache hsv hq hrun hcons hmod)
      (hcalls i bools bits))


end Tools.ShippingMachineDepthRunRA
