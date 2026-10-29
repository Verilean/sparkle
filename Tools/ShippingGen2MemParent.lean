import Tools.ShippingGen2MemFacts
import Tools.ShippingGen2Connect
set_option autoImplicit false

/-! # M2-a: the approved memory-parent definitions and C8 (scripts/gen2/MEMPARENT_FREEZE.md rev1 §2-§3, §7.1)

Definitions are the approved texts: `MemParentDataOkB`/`MemParentDataOk` (§2.1), `ExtInS` (§2.3), `MemOrigin` (§7, A4
option (a)), `MemParentStmt'` (§3 with `MemOrigin` right after `MemParentDataOk p → ExtInS p →`, §7.1).
C8 `pkg_memComposedNW`: `ComposedNW depth` of a memory-only package's run, from the run itself (`MachineRunJQC`),
generic in `ι`/`dom` (the `SrcPkg` form of `memCallee_composedNW`, Tools/ShippingSrm4Run.lean:75). -/
namespace Tools.ShippingGen2
open Lean hiding Module Expr
open Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain

open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingInstTagged (originAt)
open Sparkle.Compiler.MachMemory (memModule)

variable {ι : Type} {dom : ι → DomainConfig}

def MemParentDataOkB (p : Pkg ι dom) : Bool :=
  p.d.ok && p.d.callsOk p.kD &&
  decide (p.d.ss.length = p.d.shape.layout.slots.length) &&
  decide (∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width) &&
  decide (∀ b ∈ p.d.shape.binders.drop p.kD, b.2 ≠ .domain)

def MemParentDataOk (p : Pkg ι dom) : Prop := MemParentDataOkB p = true

def ExtInS (p : Pkg ι dom) : Prop :=
  (∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (j : Nat), j < p.kD → p.extBS i bools bits j = bools j) ∧
  (∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (j n' : Nat), j < p.kD → p.extS i bools bits j n' = bits j n')

def MemOrigin (p : Pkg ι dom) : Prop :=
  ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ (cb : Bool) (aw dw : Nat),
    (originAt p.d.shape k).child? = some (memModule cb aw dw) ∧
    ((p.d.bsIn.drop p.kD)[k]?.map (·.2)) = some (.bits dw)

def MemParentStmt' {mref cref} (L : Laws mref cref) : Prop :=
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    MemParentDataOk p → ExtInS p → MemOrigin p →
    p.d.shape.insts ≠ [] → p.d.shape.instFields ≠ [] → p.d.shape.layout.slots ≠ [] →
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) →
    ∀ n, TopShips p (n + 1) p.decl b raw D ∧ ChildShips p (n + 1) b D

variable {mctx : Meta.Context} {cctx : Core.Context}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **C8**: the composed run of a memory-only package at every depth, from the run itself. -/
theorem pkg_memComposedNW (L : Laws mref cref) (p : Pkg ι dom) (hA : AdmCtx L.O.quiet mctx cctx)
    (hfe : p.d.shape.instFields ≠ []) (hkD : p.kD ≤ p.d.bsIn.length)
    (hdomB : ∀ b ∈ p.d.shape.binders.drop p.kD, b.2 ≠ .domain)
    (hIlen : (p.d.bsIn.drop p.kD).length = p.d.shape.insts.length)
    (hSL : ∀ b ∈ p.d.slotBs ++ p.d.letBs, b.2 ≠ .domain)
    (hSlen : p.d.slotBs.length = p.d.shape.layout.slots.length)
    (hLlen : p.d.letBs.length = p.d.shape.layout.lets)
    (hNIn : machNIn p.d.shape = ((p.d.bsIn.take p.kD).filter (fun b => b.2 != .domain)).length)
    (hmd : ∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1)
    (hmo : MemOrigin p) (depth : Nat) {D₀ : Nat} {m : Sparkle.IR.AST.Module} {design : Design}
    (ran : Tools.ShippingServedRealA.MachineRunJQC L.O mctx cctx (D₀ + 1) p.decl p.d.shape m design) :
    Tools.ShippingMachineDepthRun.ComposedNW depth p.decl p.d p.kD m design dom p.src p.extS p.extBS := by
  have h := Pkg.trace L.O L.T hA p ran
  refine Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA depth L.O h hfe p.kD hkD
    (Tools.ShippingQuadComposed.bsIn_drop_nodomain p.d p.kD hdomB) hIlen hSL hSlen hLlen hNIn
    (fun _ => []) (fun _ => []) (fun _ _ _ => []) (fun _ _ => True) ?_ ?_
  · intro i bools bits k c hc
    have hk : k < p.d.shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
    have hck : (p.d.shape.insts[k]).1 = c := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc; simpa using hc
    exact Or.inl (hck ▸ hmd k hk i bools bits)
  · intro k c hc hnone
    have hk : k < p.d.shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
    obtain ⟨cb, aw, dw, ho, -⟩ := hmo k hk
    have ho' : (p.d.shape.instOrigins.getD k .ord).child? = some (memModule cb aw dw) := ho
    rw [hnone] at ho'
    cases ho'

end Tools.ShippingGen2
