import Tools.ShippingGen4GateOutTyR
import Tools.ShippingGen4FirstLeafR
set_option autoImplicit false
-- BUILT by kjob lake build (focused, exit 0) at 6c24408f; clean build is the coder's. U-GC1 (scripts/gen2/GATE_CARRIER_FREEZE.md §3.1, §4): carrier GateTable/GateRec and gateReflects_shipsResI. No sorry / axiom / native_decide.

namespace Tools.ShippingGen4GateCarrier
open Lean Meta Sparkle.Compiler.Elab
open Sparkle.IR.Type (HWType)
open Tools.ShippingGen2
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingChildInv (Res)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingUnifiedSource (SType Term quote)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingEntrySoundness (FExpr quoteDecl)

variable {ι : Type}
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- the data of a mixed gate leaf WITHOUT the five reflected facts (those are the rows B.G-3..6) -/
structure GateData where
  decl : Name
  value : Lean.Expr
  domE : Lean.Expr
  bs : List (Name × MixedGateBinder)
  kb : Nat
  kv : Nat
  vw : Nat → Nat
  bpos : Nat → Nat
  vpos : Nat → Nat
  srt : SType
  e : Term srt

def GateData.Old (g : GateData) : Prop :=
  ∀ d : Lean.DefinitionVal, d.value = g.value → certifiedShape? false [] (.defnInfo d) = none
def GateData.Peel (g : GateData) : Prop :=
  mixedGatePeel g.value = some (g.bs, quote g.domE (fun j => inputExpr g.bs.length (g.bpos j)) (fun j => inputExpr g.bs.length (g.vpos j)) g.e)
def GateData.He (g : GateData) : Prop := g.e.WF g.kb g.kv g.vw
def GateData.Hb (g : GateData) : Prop := ∀ j, j < g.kb → ∃ name, g.bs[g.bpos j]? = some (name, .bool)
def GateData.Hv (g : GateData) : Prop := ∀ j, j < g.kv → ∃ name, g.bs[g.vpos j]? = some (name, .bits (g.vw j))

def GateData.toLeaf (g : GateData) (old : g.Old) (peel : g.Peel) (he : g.He) (hb : g.Hb) (hv : g.Hv) : GateLeaf ι :=
  ⟨g.decl, g.value, g.domE, g.bs, g.kb, g.kv, g.vw, g.bpos, g.vpos, g.srt, g.e, old, peel, he, hb, hv⟩

def GateLeaf.data (g : GateLeaf ι) : GateData :=
  ⟨g.decl, g.value, g.domE, g.bs, g.kb, g.kv, g.vw, g.bpos, g.vpos, g.srt, g.e⟩

/-- first-gate leaf data WITHOUT hwf / hn -/
structure FirstData where
  decl : Name
  dn : Name
  names : List Name
  n : Nat
  fe : FExpr

def FirstData.value (f : FirstData) : Lean.Expr := quoteDecl f.dn f.names f.n f.fe
def FirstData.toLeaf (f : FirstData) (hwf : f.fe.WF f.names.length f.n) (hn : 0 < f.n) : FirstLeaf ι :=
  ⟨f.decl, f.dn, f.names, f.n, f.fe, hwf, hn⟩

/-- one entry of the gate table: route 2 (mixed gate) or route 1 (first gate) -/
inductive GateRec
  | mixed (g : GateData)
  | first (f : FirstData)

def GateRec.decl : GateRec → Name
  | .mixed g => g.decl
  | .first f => f.decl
def GateRec.value : GateRec → Lean.Expr
  | .mixed g => g.value
  | .first f => f.value
noncomputable def GateRec.iface (ι : Type) : GateRec → ChildIface ι
  | .mixed g => ⟨g.decl, g.bs, [GateLeaf.outField (.bitVector g.srt.width)], fun _ => gateS g.bs g.e g.bpos g.vpos⟩
  | .first f => ⟨f.decl, Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n, [GateLeaf.outField (.bitVector f.n)], fun _ => gateS (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n) (Tools.ShippingUnifiedSource.ofF f.n f.fe) (fun _ => 0) (fun j => j + 1)⟩

abbrev GateTable := Name → Option GateRec

noncomputable def gateQ (ι : Type) (GT : GateTable) : IfaceMap ι := fun c => (GT c).map (GateRec.iface ι)

/-- B.G-1 (and B.G-8, F-6, F-7 merged): naming, entry, and for route 1 the two data facts -/
def GateEntryRow (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State) (GT : GateTable) : Prop :=
  ∀ c r, GT c = some r → r.decl = c ∧ ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context), EntryDefines mctx mref cctx cref c r.value
def GateFirstDataRow (GT : GateTable) : Prop :=
  ∀ c f, GT c = some (.first f) → f.fe.WF f.names.length f.n ∧ 0 < f.n
def GateOldRow (GT : GateTable) : Prop := ∀ c g, GT c = some (.mixed g) → g.Old
def GatePeelRow (GT : GateTable) : Prop := ∀ c g, GT c = some (.mixed g) → g.Peel
def GateHeRow (GT : GateTable) : Prop := ∀ c g, GT c = some (.mixed g) → g.He
def GateHbvRow (GT : GateTable) : Prop := ∀ c g, GT c = some (.mixed g) → g.Hb ∧ g.Hv
def GateWidthRow (GT : GateTable) : Prop := ∀ c g, GT c = some (.mixed g) → g.srt.width ≠ 1

def GateReflects (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State) (GT : GateTable) : Prop :=
  GateEntryRow mref cref GT ∧ GateFirstDataRow GT ∧ GateOldRow GT ∧ GatePeelRow GT ∧ GateHeRow GT ∧ GateHbvRow GT ∧ GateWidthRow GT


theorem realChildA_ctx {O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref} {c : Name} {y : Res}
    (h : RealChildA O c y) : ∃ (_ : Lean.Meta.Context) (_ : Lean.Core.Context), True := by
  cases h with
  | run mctx' cctx' w w' adm cache synth quiet hr => exact ⟨mctx', cctx', trivial⟩

theorem gateReflects_shipsResI (L : Laws mref cref) (GT : GateTable) (hG : GateReflects mref cref GT)
    (c : Name) (r : GateRec) (hr : GT c = some r) {y : Res} (h : RealChildA L.O c y) :
    ShipsResI L (gateQ ι GT) c y := by
  obtain ⟨hE, hF, hO, hP, hH, hBV, hW⟩ := hG
  obtain ⟨hd, hent⟩ := hE c r hr
  obtain ⟨mctx0, cctx0, -⟩ := realChildA_ctx h
  cases r with
  | mixed g =>
    have hd' : g.decl = c := hd
    subst hd'
    let leaf : GateLeaf ι := g.toLeaf (hO _ g hr) (hP _ g hr) (hH _ g hr) (hBV _ g hr).1 (hBV _ g hr).2
    have hw1 : leaf.srt.width ≠ 1 := hW _ g hr
    have entry : EntryDefines mctx0 mref cctx0 cref leaf.decl leaf.value := hent mctx0 cctx0
    apply gateLeaf_shipsResI_of_real L leaf (gateQ ι GT) entry h
    intro ty hty
    obtain ⟨w, hw, hout⟩ := gateLeaf_outTy L.O leaf entry h hw1
    rw [hout] at hty
    have hty' := List.singleton_inj.mp hty
    have hty2 : ty = .bitVector w := by
      have := congrArg Sparkle.IR.AST.Port.ty hty'
      exact this.symm
    subst hty2
    have hw' : w = g.srt.width := hw
    subst hw'
    simp [gateQ, hr, GateRec.iface, GateLeaf.ifaceOf, leaf, GateData.toLeaf]
  | first f =>
    have hd' : f.decl = c := hd
    subst hd'
    obtain ⟨hwf, hn⟩ := hF _ f hr
    let leaf : FirstLeaf ι := f.toLeaf hwf hn
    have entry : EntryDefines mctx0 mref cctx0 cref leaf.decl (quoteDecl leaf.dn leaf.names leaf.n leaf.fe) :=
      hent mctx0 cctx0
    apply firstLeaf_shipsResI_of_real L leaf (gateQ ι GT) entry h
    simp [gateQ, hr, GateRec.iface, FirstLeaf.ifaceOf, leaf, FirstData.toLeaf]

#print axioms gateReflects_shipsResI

theorem gateReflects_empty : GateReflects mref cref (fun _ => none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro c r h <;> cases h

theorem toLeaf_data (g : GateLeaf ι) : (GateLeaf.data g).toLeaf g.old g.peel g.he g.hb g.hv = g := rfl

theorem gateQ_none (GT : GateTable) (c : Name) (h : GT c = none) : gateQ ι GT c = none := by simp [gateQ, h]

end Tools.ShippingGen4GateCarrier
