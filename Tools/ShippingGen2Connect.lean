import Tools.ShippingGen2AComb
import Tools.ShippingGen2Consumer
import Tools.ShippingChildPinC
set_option autoImplicit false

/-! # Gen2 U0: the type connections (GENERAL_SPEC.md §8.1)

Proved here: `InvAt` is `StableA` (the frame/quiet premise of `RefLawsATele` and of the keep chain); the trace is
monotone in its served predicate; `ServedP Q` gives `ServedRealA` when `Q ⇒ RealChildA`; `MemDec` is `MemFacts`;
`CallDec` + the served child fact at height `n` give `SeqFactsRN` with `PC := ServedPC (ShipsAt L P n) dsn` and the
package's interface data; hence the per-entry premise `hcalls` of `machine_linkedT_callsServed`. Nothing here proves
G-SERVED, G-KEEP-BODY/CHILD, G-CALLDEC or any `…Stmt`. -/
namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
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

open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingChildInv (Res)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- `InvAt` implies quiet and is framed by `cv`/`sv`/`dv`/quiet: the `StableA` premise that `RefLawsATele`'s fields and
the components of `bodyKeepsP_of_tele` ask of an invariant (as `stableA_JQP`, ChildPinC.lean:56). -/
theorem stableA_invAt (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) :
    Tools.ShippingChildVCA.StableA L.O.quiet (InvAt L P Reach D) :=
  ⟨fun _ h => h.1.1.1, fun w w' hc hs hd hq h =>
    ⟨(Tools.ShippingChildCacheA.stableA_JQC L.O D).2 w w' hc hs hd hq h.1, by rw [hc]; exact h.2⟩⟩

/-- The trace is monotone in its served-instance predicate (same witnesses). -/
theorem machineTraceLBX_mono {X Y : List FVarId → IO.Ref (ExprStructMap String) → Prop}
    (hXY : ∀ ids cache, X ids cache → Y ids cache) {declName : Name} {d : MachineData}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι' : Type} {dom' : ι' → DomainConfig}
    {src : (i : ι') → (Nat → Signal (dom' i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom' i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι') → (Nat → Signal (dom' i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom' i) (BitVec n)) → (j : Nat) → (n : Nat) → Signal (dom' i) (BitVec n)}
    {extB : (i : ι') → (Nat → Signal (dom' i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom' i) (BitVec n)) → Nat → Signal (dom' i) Bool}
    {lsrc : (i : ι') → (Nat → Signal (dom' i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom' i) (BitVec n)) → List (Nat → Nat)}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX X declName d m dsn dom' src ext extB lsrc) :
    Tools.ShippingMachineTraceX.MachineTraceLBX Y declName d m dsn dom' src ext extB lsrc := by
  obtain ⟨ids, h1, h2, cache, regs, h3, h4, lets, h5, h6, hx, h7⟩ := h
  exact ⟨ids, h1, h2, cache, regs, h3, h4, lets, h5, h6, hXY ids cache hx, h7⟩

/-- `ServedP` is monotone in `Q`. -/
theorem servedP_mono {Q Q' : Name → Res → Prop} (hQ : ∀ c r, Q c r → Q' c r) {declName : Name}
    {shape : MachineShape} {m : Sparkle.IR.AST.Module} {dsn : Design} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} (h : ServedP Q declName shape m dsn ids cache) :
    ServedP Q' declName shape m dsn ids cache := by
  refine ⟨?_, ?_⟩
  · intro hf k hk mc iname argWs outs outWs hst hout hke hmod
    rcases h.1 hf k hk mc iname argWs outs outWs hst hout hke hmod with hm | ⟨Dc, hq, hc⟩
    · exact Or.inl hm
    · exact Or.inr ⟨Dc, hQ _ _ hq, hc⟩
  · intro hf k hk args mc st ha hst hcall hmod
    rcases h.2 hf k hk args mc st ha hst hcall hmod with hm | ⟨Dc, hq, hc⟩
    · exact Or.inl hm
    · exact Or.inr ⟨Dc, hQ _ _ hq, hc⟩

/-- `ServedP Q` with `Q ⇒ RealChildA` gives the existing `ServedRealA` (same `ids`/`cache`). -/
theorem servedRealA_of_servedP {L : Laws mref cref} {Q : Name → Res → Prop}
    (hQ : ∀ c r, Q c r → RealChildA L.O c r) {declName : Name} {shape : MachineShape}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (h : ServedP Q declName shape m dsn ids cache) :
    Tools.ShippingServedRealA.ServedRealA L.O declName shape m dsn ids cache :=
  servedP_mono hQ h

theorem shipsRes_real {L : Laws mref cref} {P : Pkgs ι dom} {c : Name} {r : Res} (h : ShipsRes L P c r) :
    RealChildA L.O c r := h.1

theorem shipsAt_real {L : Laws mref cref} {P : Pkgs ι dom} {n : Nat} {c : Name} {r : Res}
    (h : ShipsAt L P n c r) : RealChildA L.O c r := h.1

/-- `MemDec` is `MemFacts` of the parent's package (by definition). -/
theorem memFacts_of_memDec {p : Pkg ι dom} {k : Nat} {c : Name} (h : MemDec p k c) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    MemFacts p.d.shape (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extS i bools bits) k c :=
  h i bools bits

/-- `CallField` at a group parent (`instFields ≠ []`) is the old name conjunct (CALLFIELD_FREEZE.md §2.1). -/
theorem callField_group {p q : Pkg ι dom} {k : Nat} {o : OutField} (hG : p.d.shape.instFields ≠ []) :
    CallField p q k o ↔ o.name = p.d.shape.instFields.getD k "" := by
  unfold CallField; rw [if_neg hG]

/-- `CallField` at a one-output parent (`instFields = []`): the callee has exactly the one layout output `o`. -/
theorem callField_one {p q : Pkg ι dom} {k : Nat} {o : OutField} (h1 : p.d.shape.instFields = []) :
    CallField p q k o ↔ q.d.shape.layout.outs = [o] := by
  unfold CallField; rw [if_pos h1]

/-- The child-interface data of a package assignment. -/
def pkgBsC (P : Pkgs ι dom) : Name → List (Name × MixedGateBinder) :=
  fun c => ((P c).map fun q => q.d.bsIn.take q.kD).getD []
def pkgOutsC (P : Pkgs ι dom) : Name → List OutField :=
  fun c => ((P c).map fun q => q.d.shape.layout.outs).getD []
noncomputable def pkgS (P : Pkgs ι dom) (i : ι) : Name → (Nat → List Nat) → List (Nat → Nat) :=
  fun c => ((P c).map fun q => q.S i).getD (fun _ => [])

/-- **`CallDec` + the served child fact at height `n` ⇒ `SeqFactsRN`** (every conjunct; GENERAL_SPEC §4.2 table).
A-COMB: the served child must be sequential (`hseq`, a clock input); its `ChildRunN` is then `SeqChildRunN` (C2).
The combinational branch is S3's `CombFactsRN`. Group parents only (`hG`, CALLFIELD_FREEZE.md §2.3): `SeqFactsRN` asks
for the old name conjunct, which `CallField` gives only under `instFields ≠ []`. -/
theorem seqFactsRN_of_callDec {L : Laws mref cref} {P : Pkgs ι dom} {p q : Pkg ι dom} {k n : Nat} {c : Name}
    (dsn : Design) (body : List Stmt) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (hG : p.d.shape.instFields ≠ [])
    (hP : P c = some q) (hdec : CallDec p q k)
    (hseq : ∀ mc, ServedPC (ShipsAt L P n) dsn c mc → "clk" ∈ mc.inputs.map (·.name)) :
    Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN (childMap dsn.modules) n p.d.shape dsn body
      (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extBS i bools bits) (p.extS i bools bits)
      (pkgBsC P) (pkgOutsC P) (pkgS P i) (ServedPC (ShipsAt L P n) dsn) k c := by
  obtain ⟨hnone, args, hargs, hlen, hall⟩ := hdec
  obtain ⟨h4, h5, k', o, f, ho, hon, hf, hpos⟩ := hall i bools bits
  have hB : pkgBsC P c = q.d.bsIn.take q.kD := by simp [pkgBsC, hP]
  have hO : pkgOutsC P c = q.d.shape.layout.outs := by simp [pkgOutsC, hP]
  have hS : pkgS P i c = q.S i := by simp [pkgS, hP]
  refine ⟨hnone, args, hargs, ?_, h4, ?_, k', o, f, ?_, (callField_group hG).mp hon, ?_, hpos⟩
  · intro mc hmc
    have hclk := hseq mc hmc
    obtain ⟨hmod, Dc, ⟨_, q', hq', _, hcs⟩, hcons⟩ := hmc
    rw [hP] at hq'
    cases hq'
    have h := (childRunN_iff_seq hclk).mp (hcs.2 dsn hcons hmod i)
    rw [hB, hO, hS]
    refine ⟨h, ?_⟩
    rw [h.2.2.2.2.2.1, hlen]
    rfl
  · rw [hB]; exact h5
  · rw [hO]; exact ho
  · rw [hS]; exact hf

end Tools.ShippingGen2
