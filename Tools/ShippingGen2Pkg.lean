import Tools.ShippingGen2Loop
import Tools.ShippingGen2SrcPkg
set_option autoImplicit false

/-! # loop-pkg step 2 interface: `Pkg` = circuit-do or loop package (LOOPPKG_FREEZE.md §6, for review)

The exact interface the step-2 refactor uses. ADDITIVE: nothing existing is changed by this file. Accessors are by cases;
`Pkg.trace`, `Pkg.ok`, `Pkg.body_eq`, `Pkg.lsrc_hl` are THEOREMS by cases (no semantic field). -/
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

open Tools.ShippingGen2Loop (SrcPkgL genTraceL letObsLoop_hl)

inductive Pkg (ι : Type) (dom : ι → DomainConfig) where
  | gen (p : SrcPkg ι dom)
  | loop (p : SrcPkgL ι dom)

variable {ι : Type} {dom : ι → DomainConfig}

def Pkg.decl : Pkg ι dom → Name
  | .gen p => p.decl
  | .loop p => p.decl

def Pkg.d : Pkg ι dom → MachineData
  | .gen p => p.d
  | .loop p => p.d

def Pkg.kD : Pkg ι dom → Nat
  | .gen p => p.kD
  | .loop p => p.kD

def Pkg.src : (p : Pkg ι dom) → (i : ι) → (Nat → Signal (dom i) Bool) →
    ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)
  | .gen p => p.src
  | .loop p => p.src

noncomputable def Pkg.extS : (p : Pkg ι dom) → (i : ι) → (Nat → Signal (dom i) Bool) →
    ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)
  | .gen p => p.extS
  | .loop p => p.extS

noncomputable def Pkg.extBS : (p : Pkg ι dom) → (i : ι) → (Nat → Signal (dom i) Bool) →
    ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool
  | .gen p => p.extBS
  | .loop p => p.extBS

noncomputable def Pkg.lsrc : (p : Pkg ι dom) → (i : ι) → (Nat → Signal (dom i) Bool) →
    ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)
  | .gen p => p.lsrc
  | .loop p => p.lsrc

/-- The declared, non-domain ports (as `SrcPkg.ports`). -/
def Pkg.ports (p : Pkg ι dom) : List (Name × MixedGateBinder) :=
  (p.d.bsIn.take p.kD).filter fun b => b.2 != .domain

/-- The child-interface source function (as `SrcPkg.S`). -/
noncomputable def Pkg.S (p : Pkg ι dom) (i : ι) : (Nat → List Nat) → List (Nat → Nat) :=
  fun vals => p.src i (boolsOf (D := dom i) (p.d.bsIn.take p.kD) vals)
    (bitsOf (D := dom i) (p.d.bsIn.take p.kD) vals)

theorem Pkg.ok (p : Pkg ι dom) : p.d.ok = true := by
  cases p with
  | gen p => letI := p.inh; exact p.gen.ok
  | loop p => letI := p.inh; exact p.facts.ok

theorem Pkg.body_eq (p : Pkg ι dom) : p.d.shape.body = Tools.ShippingUnifiedSource.quote p.d.dom
    (fun j => inputExpr p.d.shape.binders.length (p.d.bpos j))
    (fun j => inputExpr p.d.shape.binders.length (p.d.vpos j)) p.d.packed := by
  cases p with
  | gen p => letI := p.inh; exact p.gen.body_eq
  | loop p => letI := p.inh; exact p.facts.hbody

theorem Pkg.lsrc_hl (p : Pkg ι dom) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    ∀ (a : Nat) (l : Σ s : Tools.ShippingUnifiedSource.SType, Tools.ShippingUnifiedSource.Term s), p.d.ls[a]? = some l →
      ∃ v, (p.lsrc i bools bits)[a]? = some v ∧ ∀ τ, v τ < 2 ^ l.1.width := by
  cases p with
  | gen p => exact @Tools.ShippingQuadCalls.letObsB_hl p.d ι dom p.inh p.ρ p.inits p.body p.ext p.extB i bools bits
  | loop p => exact letObsLoop_hl p i bools bits

variable {mctx : Meta.Context} {cctx : Core.Context}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`Pkg.trace`** (a theorem by cases: `genTrace` / `genTraceL`). -/
theorem Pkg.trace (O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) (p : Pkg ι dom) {D₀ : Nat} {m : Sparkle.IR.AST.Module} {design : Design}
    (ran : Tools.ShippingServedRealA.MachineRunJQC O mctx cctx (D₀ + 1) p.decl p.d.shape m design) :
    Tools.ShippingMachineTraceX.MachineTraceLBX (Tools.ShippingServedRealA.ServedRealA O p.decl p.d.shape m design)
      p.decl p.d m design dom p.src p.extS p.extBS p.lsrc := by
  cases p with
  | gen p =>
    letI := p.inh
    exact Tools.ShippingQuadComposed.genTrace O T hA (declName := p.decl) p.d dom p.gen ran
  | loop p => exact genTraceL O T hA p ran

/-- The lift of a `SrcPkg` assignment (for the compatibility tests). -/
def Pkgs.lift (P : Name → Option (SrcPkg ι dom)) : Name → Option (Pkg ι dom) :=
  fun c => (P c).map Pkg.gen

/-- The DataOk lift used ONLY by the compatibility tests: the old `DataOk` on `.gen`, `False` on `.loop`. It never
restricts a real theorem. -/
def DataOkLiftCompat (DataOk : SrcPkg ι dom → Prop) : Pkg ι dom → Prop
  | .gen p => DataOk p
  | .loop _ => False

/-- Specialisation checks of the accessors (definitional). -/
example (p : SrcPkg ι dom) : (Pkg.gen p).extS = p.extS := rfl
example (p : SrcPkg ι dom) : (Pkg.gen p).extBS = p.extBS := rfl
example (p : SrcPkg ι dom) : (Pkg.gen p).lsrc = p.lsrc := rfl
example (p : SrcPkg ι dom) : (Pkg.gen p).ports = p.ports := rfl
example (p : SrcPkg ι dom) (i : ι) : (Pkg.gen p).S i = p.S i := rfl

end Tools.ShippingGen2
