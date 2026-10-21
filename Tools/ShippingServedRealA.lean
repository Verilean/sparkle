import Tools.ShippingMachineTraceX
import Tools.ShippingChildRunAKids
import Tools.ShippingChildRunAMain
-- BUILT (unit SR, par/u-sr): sr3 exit 0 (original), sr8 exit 0 (final, via the audit target); see REPORT-SR.md. No `sorry`, no `axiom`, no `native_decide`, no new law / field.
-- Law witness `O : RefLawsAOps MkRefd mref cref`; no RefLaws / ChildBnd / InvW in the statements.

/-! # Unit SR: `ServedRealA` — `ServedReal` on the NEW boundary

`Tools.ShippingMachineTraceX.ServedReal` says: the module of the instance serving call `k` is the
built memory module or `RealChild mref cref callee (mc, Dc)`. Here `RealChild` is replaced by
`RealChildA O` (history of a past admissible run of the real entry under the fixed `O`), nothing else.

* `ServedRealGA`, `ServedReal1A`, `ServedRealA`: the statement.
* `MachineRunJQC O n` (NOT the unit-PH `MachineRanA`, which also holds the closing/children facts; PH's is
  derivable from this + `synthesizeMachineCertified_runsA`): the new analogue of `MachineRan` — the machine synthesis a core run performs
  returned the run's result from a `JQC O n` world (replaces `InvW ∧ DepthPos`).
* `machineRunJQC_of_closesA`: from a returning core run (`JQ O.quiet D`, cache half if `D ≠ 0`),
  `MachineDefines` and `MachineClosesAtA` (a PREMISE): `MachineRunJQC O (D + 1)`.
* `synthesizeCombinationalCore_machine_soundRA_ranA`: the tail of `…_machine_soundRA_ran`, copied;
  the one use of the old boundary (`synthesizeMachineCertified_runs`, needs `InvW`) is replaced by
  `synthesizeMachineCertified_runsA` (premises `BodyStepC O`, `htr` at `JQC O n`).
* `synthesizeCombinationalCore_machine_soundRA_A`: composition with `machineRunJQC_of_closesA`.

SCOPE: `RealChildA` is a history of past synthesis results, not correctness in the current
environment; `JQC` is not freshness. Not runtime fit, not semantic preservation of the parent
(the `MachinePreservesX` conclusion is the same trace statement as before, with `ServedRealA` as `X`; it is a
trace WITH child history, NOT composed-parent semantic equivalence). `…_main` corollaries derive `BodyStepC`/`htr`
from `T : RefLawsATele`. -/
namespace Tools.ShippingServedRealA
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA
open Tools.ShippingChildCacheA Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingChildComposeC
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain Tools.ShippingMachineTraceX
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildTranslateA Tools.ShippingChildFrontCP
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge Tools.ShippingMachineAuto
open Tools.ShippingMachineRef Tools.ShippingMachineSource Tools.ShippingUnifiedSource

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

def ServedRealGA (O : RefLawsAOps MkRefd mref cref) (declName : Name)
    (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Sparkle.IR.AST.Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) : Prop :=
  shape.instFields ≠ [] →
  ∀ k (hk : k < shape.insts.length) (mc : Sparkle.IR.AST.Module) (iname : String)
    (argWs : List String) (outs : List (Nat × String)) (outWs : List String),
    Stmt.inst mc.name iname (Tools.ShippingMachineLinkedT.connsG mc argWs outs outWs) ∈ m.body →
    outs.mapM (fun (j, _) =>
      ((machPorts declName ids cache shape.binders).map (·.name))[machNIn shape + j]?) = some outWs →
    (∃ e ∈ outs, e.1 = k) →
    moduleByName dsn.modules mc.name = some mc →
    (∃ md, (shape.instOrigins.getD k .ord).child? = some md ∧ mc = md.1) ∨
      ∃ Dc, RealChildA O (shape.insts[k]).1 (mc, Dc) ∧
        ∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g

def ServedReal1A (O : RefLawsAOps MkRefd mref cref) (declName : Name)
    (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Sparkle.IR.AST.Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) : Prop :=
  shape.instFields = [] →
  ∀ k (hk : k < shape.insts.length) (args : List Nat) (mc : Sparkle.IR.AST.Module) (st : Stmt),
    (shape.insts.map (·.2.1))[k]? = some args → st ∈ m.body →
    Tools.ShippingMachineInst.CallStmt (machNIn shape) shape.insts.length shape.layout.slots.length
      ((machPorts declName ids cache shape.binders).map (·.name)) k args mc st →
    moduleByName dsn.modules mc.name = some mc →
    (∃ md, (shape.instOrigins.getD k .ord).child? = some md ∧ mc = md.1) ∨
      ∃ Dc, RealChildA O (shape.insts[k]).1 (mc, Dc) ∧
        ∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g

/-- **The instances serving the calls are `RealChildA`**, on either closing. -/
def ServedRealA (O : RefLawsAOps MkRefd mref cref) (declName : Name)
    (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Sparkle.IR.AST.Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) : Prop :=
  ServedRealGA O declName shape m dsn ids cache ∧ ServedReal1A O declName shape m dsn ids cache

/-- A `RealChildA`'s run, with the data of its start world (analogue of `RealChild.inv`, which gave
`InvW`): admissible contexts, cache half, synthesis ref, quiet. A history of a past run. -/
theorem realChildA_inv {O : RefLawsAOps MkRefd mref cref} {c : Name} {r : Res}
    (h : RealChildA O c r) :
    ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld),
      AdmCtx O.quiet mctx cctx ∧ CacheInvA O (cv w) ∧ sv w = some synthesizeChild ∧ O.quiet w ∧
      RunsTo (synthesizeCombinational c) mctx mref cctx cref w r w' := by
  cases h with
  | run mctx cctx w w' adm cache synth quiet hr => exact ⟨mctx, cctx, w, w', adm, cache, synth, quiet, hr⟩

/-- The machine synthesis a core run performs returned the run's result, from a `JQC O n` world. -/
def MachineRunJQC (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context) (cctx : Core.Context)
    (n : Nat) (c : Name) (shape : MachineShape) (M : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ (tenv : Lean.Environment), ∃ (b : Bool) (w9 w10 : Void IO.RealWorld),
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
      mctx mref cctx cref w9 (some (M, D)) w10 ∧ JQC O n w9

theorem machineRunJQC_of_closesA (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w)) :
    MachineRunJQC O mctx cctx (D + 1) declName shape m d := by
  obtain ⟨tenv, b, r, w9, w10, hrun, hw9, hres⟩ := machine_run_of_coreA O hA hr entry hw hc
  have hne := closes b (D + 1) w9 r w10 hw9 (by omega) hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    exact ⟨tenv, b, w9, w10, hrun, hw9⟩

/-- The tail of `synthesizeCombinationalCore_machine_soundRA_ran` on the new boundary: the instances
serving the calls are `RealChildA` (or origin-built). Premises `O`, `hA`, `BodyStepC O`, `htr`. -/
theorem synthesizeCombinationalCore_machine_soundRA_ranA (O : RefLawsAOps MkRefd mref cref) (hB : BodyStepC O)
    (hA : AdmCtx O.quiet mctx cctx) {n : Nat}
    (htr : ∀ (tenv : Lean.Environment) e hint top named, KeepsCP mctx mref cctx cref (JQC O n)
      (translateExprToWire tenv e hint top named)) {declName : Name}
    {m : Sparkle.IR.AST.Module} {d : Design}
    {shape : MachineShape} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (ran : MachineRunJQC O mctx cctx n declName shape m d)
    (hbs : shape.binders = bsIn ++ slotBs ++ letBs)
    (hlets : shape.layout.lets = letBs.length)
    (positive : PositiveBinders shape.binders)
    (slotKinds : ∀ b ∈ slotBs, b.2 ≠ .domain)
    (letKinds : ∀ b ∈ letBs, b.2 ≠ .domain)
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2)
      shape.layout.slots slotBs)
    (outsOk : ∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (shape.layout.outs.map (·.name)).Nodup) :
    MachinePreservesX (ServedRealA O declName shape m d)
      declName shape bsIn slotBs letBs m d := by
  obtain ⟨tenv, prof, w9, w10, hrun, hw9⟩ := ran
  obtain ⟨t, t', d₀, hmix, hcl, hmt⟩ :=
    synthesizeMachineCertified_runsA O hB hA (htr tenv) hw9 hrun
  have hmt0 : (shape.insts = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨
      (shape.insts ≠ [] ∧ ∃ children,
        CloseCalls shape t (closeMachine shape.layout t') d₀ children m d) := by
    rcases hmt with h0 | ⟨hi, children, hcc, _⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hi, children, hcc⟩
  refine synthesizeMachineCertified_soundX _ hmix hcl hmt0 ?_ hbs hlets positive slotKinds
    letKinds layW outsOk outsNodup
  intro ids cache regs lets wired hmp notInst
  have h0 : ∀ st ∈ (closeMachine shape.layout t').body, isInst st = false := fun st hs => by
    cases hi : isInst st
    · rfl
    · exact absurd (notInst st hs hi) id
  refine ⟨?g, ?o⟩
  case o =>
    intro hfe1 k hk args mc st hargs hst hcs hmod
    rcases hmt with ⟨h0', _, _⟩ | ⟨_, children, hcc, hreal⟩
    · rw [h0'] at hk; exact absurd hk (Nat.not_lt_zero _)
    rcases hcc with ⟨_, hC⟩ | ⟨hfe0, _, _⟩
    case inr => exact absurd hfe1 hfe0
    rw [hmp] at hcs
    obtain ⟨y, hy, hmcy⟩ := Tools.ShippingChildServe.closeInsts_serves hC h0 hst hcs hmod
    have hyc := (Tools.ShippingChildServe.closeInsts_acyclic hC).2.2.2 y (List.mem_of_getElem? hy)
    obtain ⟨_, hkr⟩ := hreal
    obtain ⟨y', hy', hor⟩ := hkr k hk
    rw [hy] at hy'; cases hy'
    subst hmcy
    rcases hor with hmem | hrc
    · exact Or.inl ⟨y, hmem, rfl⟩
    · exact Or.inr ⟨y.2, hrc, hyc⟩
  case g =>
  intro hfe k hk mc iname argWs outs outWs hst hout hke hmod
  rcases hmt with ⟨h0, _, _⟩ | ⟨_, children, hcc, hreal⟩
  · rw [h0] at hk; exact absurd hk (Nat.not_lt_zero _)
  rcases hcc with ⟨hfe0, _⟩ | ⟨_, hG, _⟩
  · exact absurd hfe0 hfe
  have hall := wired.2.1
  rw [hmp] at hall hout
  have hcr : "clk" ∉ t.inputs.map (·.name) ∧ "rst" ∉ t.inputs.map (·.name) :=
    ⟨fun h => (allocated_ne (hall _ h)).1 rfl, fun h => (allocated_ne (hall _ h)).2 rfl⟩
  obtain ⟨y, hy, hmcy⟩ := Tools.ShippingChildServe.closeInstsG_serves hG
    (fun st hs => by
      cases hi : isInst st
      · rfl
      · exact absurd (notInst st hs hi) id)
    hcr hk hst hout hke hmod
  have hyc := ((Tools.ShippingMachineInstG.closeInstsG_names hG).2.2.2 y (List.mem_of_getElem? hy)).2
  obtain ⟨_, hkr⟩ := hreal
  obtain ⟨y', hy', hor⟩ := hkr k hk
  rw [hy] at hy'; cases hy'
  subst hmcy
  rcases hor with hmem | hrc
  · exact Or.inl ⟨y, hmem, rfl⟩
  · exact Or.inr ⟨y.2, hrc, hyc⟩


/-- `synthesizeCombinationalCore_machine_soundRA` on the new boundary: the start premise
`ChildBnd` is replaced by `JQ O.quiet D` (+ cache half when `D ≠ 0`); `MachineClosesAt` by
`MachineClosesAtA` (PREMISE). -/
theorem synthesizeCombinationalCore_machine_soundRA_A (O : RefLawsAOps MkRefd mref cref)
    (hB : BodyStepC O) (hA : AdmCtx O.quiet mctx cctx) {D : Nat}
    (htr : ∀ (tenv : Lean.Environment) e hint top named, KeepsCP mctx mref cctx cref (JQC O (D + 1))
      (translateExprToWire tenv e hint top named))
    {declName : Name}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Design}
    {shape : MachineShape} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
    (hbs : shape.binders = bsIn ++ slotBs ++ letBs)
    (hlets : shape.layout.lets = letBs.length)
    (positive : PositiveBinders shape.binders)
    (slotKinds : ∀ b ∈ slotBs, b.2 ≠ .domain)
    (letKinds : ∀ b ∈ letBs, b.2 ≠ .domain)
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2)
      shape.layout.slots slotBs)
    (outsOk : ∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (shape.layout.outs.map (·.name)).Nodup) :
    MachinePreservesX (ServedRealA O declName shape m d)
      declName shape bsIn slotBs letBs m d :=
  synthesizeCombinationalCore_machine_soundRA_ranA O hB hA htr
    (machineRunJQC_of_closesA O hA hr entry closes hw hc)
    hbs hlets positive slotKinds letKinds layW outsOk outsNodup

/-- `synthesizeCombinationalCore_machine_soundRA_A` with `BodyStepC` and `htr` DERIVED from
`T : RefLawsATele` (ComposeC `bodyStepC_of_tele`, G2 `htr_of_tele`). Premises: `O`, `hA`, `T`, the run,
`MachineDefines`, `MachineClosesAtA` (PREMISE), the start world, the data conditions. -/
theorem synthesizeCombinationalCore_machine_soundRA_main (O : RefLawsAOps MkRefd mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (T : RefLawsATele O.quiet mref cref) {D : Nat}
    {declName : Name}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Design}
    {shape : MachineShape} {bsIn slotBs letBs : List (Name × MixedGateBinder)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName shape)
    (hw : JQ O.quiet D w) (hc : D = 0 ∨ CacheInvA O (cv w))
    (hbs : shape.binders = bsIn ++ slotBs ++ letBs)
    (hlets : shape.layout.lets = letBs.length)
    (positive : PositiveBinders shape.binders)
    (slotKinds : ∀ b ∈ slotBs, b.2 ≠ .domain)
    (letKinds : ∀ b ∈ letBs, b.2 ≠ .domain)
    (layW : Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2)
      shape.layout.slots slotBs)
    (outsOk : ∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true)
    (outsNodup : (shape.layout.outs.map (·.name)).Nodup) :
    MachinePreservesX (ServedRealA O declName shape m d)
      declName shape bsIn slotBs letBs m d :=
  synthesizeCombinationalCore_machine_soundRA_A O (bodyStepC_of_tele O T) hA (htr_of_tele O hA T D)
    hr entry closes hw hc hbs hlets positive slotKinds letKinds layW outsOk outsNodup

end Tools.ShippingServedRealA
