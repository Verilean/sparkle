import Tools.ShippingMachineComposeR
import Tools.ShippingMachineDepthRunRA
-- BUILT (unit SR2b, par/u-sr2b): sr2b2 exit 0; audit sr2b3 exit 0; axioms sr2b4 exit 0 (propext, Classical.choice, Quot.sound). No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit SR2b: `MachineRunNA` and the first composed head on the new boundary

* `MachineRunNA` — `MachineRunN` with the run's start data of the new boundary (`AdmCtx`, `JQC O (dv w)`) and
  `MachineClosesAtA` (instead of `MachineCloses`); `Bnd` is the plain `Module → Design → Prop` of `MachineRunN`.
  `machineRunNA_of_NCA`: it is a projection of `MachineRunNCA` (forget the start-world argument of the boundary).
* `machine_linked_callsRA` — the composed head `Tools.ShippingMachineComposeR.machine_linked_callsR` (first
  head of the inventory's composed-semantics row) with `ServedRealA O` in the trace type and `hfn` quantified
  over the data of `realChildA_inv` (`AdmCtx`, `CacheInvA (cv w)`, `sv`, quiet) instead of `InvW`.

SCOPE: the same statement as the old head (`ComposedH` with the trivial `R`, one-output combinational children)
under premises on the new boundary; `hcalls` and `hfn` stay premises. It is NOT a proof that `hfn` holds. -/
namespace Tools.ShippingMachineComposeRA

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
open Tools.ShippingChildFrontCP Tools.ShippingChildBndCore Tools.ShippingChildBndInit
open Tools.ShippingMachineDepthRunRA
open Tools.ShippingMachineTraceX (MachineTraceLBX)
open Tools.ShippingMachineCompose (ChildFn)

/-- `MachineRunN` on the new boundary: the core run starts in a `JQC O (dv w)` world with admissible
contexts, and the closing is `MachineClosesAtA`. -/
def MachineRunNA {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (c : Name) (shape : MachineShape)
    (Bnd : Module → Design → Prop) (mc : Module) (dsn : Design) : Prop :=
  ∃ (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld) (raw : Module) (D : Design),
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w' ∧
    AdmCtx O.quiet mctx cctx ∧ JQC O (dv w) w ∧
    MachineDefines mctx mref cctx cref c shape ∧
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx c shape ∧
    Bnd raw D ∧
    (mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
     mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
    ExtendsAway raw.name (childMap D.modules) (childMap dsn.modules) ∧
    NoInstOf raw.name raw.body

/-- `MachineRunNCA` gives `MachineRunNA` for the boundary that ignores the run's start data. -/
theorem machineRunNA_of_NCA {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref} {c : Name} {shape : MachineShape}
    {Bnd : Module → Design → Prop} {mc : Module} {dsn : Design}
    (h : MachineRunNCA O c shape (fun _ _ _ raw D => Bnd raw D) mc dsn) :
    MachineRunNA O c shape Bnd mc dsn := by
  obtain ⟨mctx, cctx, w, w', raw, D, hr, hadm, hjqc, hdef, hcl, hb, hmc, hea, hni⟩ := h
  exact ⟨mctx, cctx, w, w', raw, D, hr, hadm, hjqc, hdef, hcl, hb, hmc, hea, hni⟩

/-- Conversely `MachineRunNA` is `MachineRunNCA` at that boundary. -/
theorem machineRunNCA_of_NA {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref} {c : Name} {shape : MachineShape}
    {Bnd : Module → Design → Prop} {mc : Module} {dsn : Design}
    (h : MachineRunNA O c shape Bnd mc dsn) :
    MachineRunNCA O c shape (fun _ _ _ raw D => Bnd raw D) mc dsn := by
  obtain ⟨mctx, cctx, w, w', raw, D, hr, hadm, hjqc, hdef, hcl, hb, hmc, hea, hni⟩ := h
  exact ⟨mctx, cctx, w, w', raw, D, hr, hadm, hjqc, hdef, hcl, hb, hmc, hea, hni⟩

/-- **`machine_linked_callsR` on the new boundary.** `ServedRealA O` in the trace type; `hfn` over the
data `realChildA_inv` gives instead of `InvW`. Proof text unchanged otherwise. -/
theorem machine_linked_callsRA {declName : Name} {d : MachineData} {m : Sparkle.IR.AST.Module}
    {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref)
    (h : MachineTraceLBX (Tools.ShippingServedRealA.ServedRealA O declName d.shape m dsn)
      declName d m dsn dom src ext (fun _ bools _ => bools) lsrc)
    (hsimple : d.shape.instFields = [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hI : ∀ b ∈ d.bsIn.drop kD, b.2 ≠ .domain)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (P : Nat → List Nat → Prop) (F : Nat → List Nat → Nat)
    (hcalls : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k args j,
      (d.shape.insts.map (·.2.1))[k]? = some args →
      (∀ q ∈ args, q < d.ls.length ∧ q < (lsrc i bools bits).length) ∧
      P k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) ∧
      F k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) =
        posEnc (fun p => (bools p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k)
          (((d.bsIn.drop kD)[k]?.map (·.2)).getD .domain))
    (hfn : ∀ (k : Nat) (c : Name), (d.shape.insts.map (·.1))[k]? = some c →
      (d.shape.instOrigins.getD k .ord).child? = none ∧
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (mc : Sparkle.IR.AST.Module) (Dc : Design)
        (w w' : Void IO.RealWorld),
        AdmCtx O.quiet mctx' cctx' → CacheInvA O (cv w) → sv w = some synthesizeChild → O.quiet w →
        RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w (mc, Dc) w' →
        ChildFn mc (P k) (F k)) :
    Tools.ShippingMachineShipsHierH.ComposedH (fun _ _ => True) declName d kD m dsn dom src ext := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, trace⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems hsrc hpass hrst hinit _
  exact Tools.ShippingMachineCompose.machine_linked_of nd len rnd rlen llen wired trace hsimple kD hkD
    hI hIlen hSL hSlen hLlen hNIn P F i bools bits T seed st0 mems hsrc hpass hrst hinit
    (fun k args mc st hargs hst hcs hmod => by
      have hk : k < d.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hargs).1; simpa using this
      have hc : (d.shape.insts.map (·.1))[k]? = some (d.shape.insts[k]).1 := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
      obtain ⟨hnone, hf⟩ := hfn k _ hc
      rcases hx.2 hsimple k hk args mc st hargs hst hcs hmod with ⟨md, hmd, _⟩ | ⟨Dc, hrc, _⟩
      · rw [hnone] at hmd; cases hmd
      · obtain ⟨mctx', cctx', w, w', hadm, hcache, hsv, hq, hrun⟩ := realChildA_inv hrc
        exact hf mctx' cctx' mc Dc w w' hadm hcache hsv hq hrun)
    (fun k args j hk _ => hcalls i bools bits k args j hk)

end Tools.ShippingMachineComposeRA
