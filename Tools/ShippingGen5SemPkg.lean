import Tools.ShippingGen2Pkg
set_option autoImplicit false
-- Built in g5sm-r2 at d5492921 (Pod `kjob lake build`, exit 0; SemUnitsCheck: TYPE 6, MUTANT 5, AXIOMS standard). No sorry / axiom / native_decide.
-- No sorry / axiom / native_decide.

/-! # DG-SEM: `SemPkg` (a package minus its fact field), `Pkg.toSem`, `genPkg` (scripts/gen5/DG_SEM_FREEZE_REV2.md §2.2, P8)

`SrcSem` / `CombSem` / `LoopSem` are `SrcPkg` / `CombPkg` / `SrcPkgL` WITHOUT the final Prop field (`gen` / `facts`), fields in the
same order with the same types (verbatim field extraction). `SemPkg` is their sum, in the order of `Pkg`. The data is what `genSem`
chooses; `FactsOf` is the fact each arm's package carries; `genPkg s hF` re-attaches it. No semantic claim; no new law.

* `Pkg.toSem` forgets the fact; `toSem_genPkg : (genPkg s hF).toSem = s` and `pkg_eq_of_toSem` (the fact is a Prop, so `toSem` is
  injective); the accessors of `Pkg` and `SemPkg` agree on `genPkg` / `Pkg.toSem` (definitionally, by cases). -/
namespace Tools.ShippingGen5Sem
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineChild (boolsOf bitsOf)
open Tools.ShippingGen2 (SrcPkg CombPkg Pkg)
open Tools.ShippingGen2Loop (SrcPkgL LoopFacts)

/-- `SrcPkg` without `gen`: same fields, same order, same types. -/
structure SrcSem (ι : Type) (dom : ι → DomainConfig) where
  decl : Name
  d : MachineData
  kD : Nat
  ρ : ι → Type
  inh : Inhabited (HList (tys d.ss))
  inits : HList (tys d.ss)
  body : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
    Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i)
  obsR : (i : ι) → ρ i → List (Nat → Nat)
  ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)
  extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    List (Nat → Nat)

/-- `CombPkg` without `facts`. -/
structure CombSem (ι : Type) (dom : ι → DomainConfig) where
  decl : Name
  d : MachineData
  kD : Nat
  inits : HList (tys d.ss)
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    List (Nat → Nat)

/-- `SrcPkgL` without `facts`. Never produced by `genSem` (freeze §2.5); present so that `SemPkg` is a faithful image of `Pkg`. -/
structure LoopSem (ι : Type) (dom : ι → DomainConfig) where
  decl : Name
  d : MachineData
  kD : Nat
  α : ι → Type
  inh : ∀ i, Inhabited (α i)
  ρ : ι → Type
  σ : (i : ι) → α i → HList (tys d.ss)
  inits : HList (tys d.ss)
  f : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → Signal (dom i) (α i)
  res : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → ρ i
  obsR : (i : ι) → ρ i → List (Nat → Nat)
  ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)
  extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (α i) → Nat → Signal (dom i) Bool
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    List (Nat → Nat)

/-- The package sum without facts, in the order of `Pkg`: `gen`, `loop`, `comb`. -/
inductive SemPkg (ι : Type) (dom : ι → DomainConfig) where
  | gen (s : SrcSem ι dom)
  | loop (s : LoopSem ι dom)
  | comb (s : CombSem ι dom)

variable {ι : Type} {dom : ι → DomainConfig}

/-! ## Accessors (by cases, as `Pkg`'s) -/

def SemPkg.decl : SemPkg ι dom → Name
  | .gen s => s.decl
  | .loop s => s.decl
  | .comb s => s.decl

def SemPkg.d : SemPkg ι dom → MachineData
  | .gen s => s.d
  | .loop s => s.d
  | .comb s => s.d

def SemPkg.kD : SemPkg ι dom → Nat
  | .gen s => s.kD
  | .loop s => s.kD
  | .comb s => s.kD

def SemPkg.src : (s : SemPkg ι dom) → (i : ι) → (Nat → Signal (dom i) Bool) →
    ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)
  | .gen s => s.src
  | .loop s => s.src
  | .comb s => s.src

/-- The declared, non-domain ports (as `Pkg.ports`). -/
def SemPkg.ports (s : SemPkg ι dom) : List (Name × MixedGateBinder) :=
  (s.d.bsIn.take s.kD).filter fun b => b.2 != .domain

/-- The child-interface source function (as `Pkg.S`). -/
noncomputable def SemPkg.S (s : SemPkg ι dom) (i : ι) : (Nat → List Nat) → List (Nat → Nat) :=
  fun vals => s.src i (boolsOf (D := dom i) (s.d.bsIn.take s.kD) vals)
    (bitsOf (D := dom i) (s.d.bsIn.take s.kD) vals)

/-- `ext`/`extB`/`lsrc` along each arm's own state stream: the SAME terms as `SrcPkg.extS` / `SrcPkgL.extS` / `CombPkg.extS` etc. -/
noncomputable def SrcSem.extS (s : SrcSem ι dom) := fun i bools bits =>
  s.ext i bools bits (@stateLoop _ _ _ s.inh s.inits (s.body i bools bits))
noncomputable def SrcSem.extBS (s : SrcSem ι dom) := fun i bools bits =>
  s.extB i bools bits (@stateLoop _ _ _ s.inh s.inits (s.body i bools bits))
noncomputable def SrcSem.lsrc (s : SrcSem ι dom) :=
  @Tools.ShippingMachineCausal.letObsB s.d ι dom s.inh s.ρ s.inits s.body s.ext s.extB
def LoopSem.extS (s : LoopSem ι dom) := fun i bools bits =>
  s.ext i bools bits (@Signal.loop _ _ (s.inh i) (s.f i bools bits))
def LoopSem.extBS (s : LoopSem ι dom) := fun i bools bits =>
  s.extB i bools bits (@Signal.loop _ _ (s.inh i) (s.f i bools bits))
def LoopSem.lsrc (s : LoopSem ι dom) :=
  @Tools.ShippingMachineCausal.letObsLoop s.d ι dom s.α s.inh s.σ s.f s.ext s.extB
def CombSem.extS (_s : CombSem ι dom) :=
  fun (i : ι) (_ : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) => bits
def CombSem.extBS (_s : CombSem ι dom) :=
  fun (i : ι) (bools : Nat → Signal (dom i) Bool) (_ : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) => bools
noncomputable def CombSem.lsrc (s : CombSem ι dom) :=
  Tools.ShippingMachineCausal.letObsComb s.d dom s.inits (fun _ _ bits => bits) (fun _ bools _ => bools)

noncomputable def SemPkg.extS : (s : SemPkg ι dom) → (i : ι) → (Nat → Signal (dom i) Bool) →
    ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)
  | .gen s => s.extS
  | .loop s => s.extS
  | .comb s => s.extS

noncomputable def SemPkg.extBS : (s : SemPkg ι dom) → (i : ι) → (Nat → Signal (dom i) Bool) →
    ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool
  | .gen s => s.extBS
  | .loop s => s.extBS
  | .comb s => s.extBS

noncomputable def SemPkg.lsrc : (s : SemPkg ι dom) → (i : ι) → (Nat → Signal (dom i) Bool) →
    ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)
  | .gen s => s.lsrc
  | .loop s => s.lsrc
  | .comb s => s.lsrc

/-! ## The facts each arm carries -/

/-- The fact field of the arm's package, at the arm's own fields (`SrcPkg.gen`, `SrcPkgL.facts`, `CombPkg.facts`). -/
def FactsOf : SemPkg ι dom → Prop
  | .gen s => @GenFacts s.d ι dom s.ρ s.inh s.inits s.body s.obsR s.ext s.extB s.src
  | .loop s => @LoopFacts s.d ι dom s.α s.inh s.ρ s.σ s.inits s.f s.res s.obsR s.ext s.extB s.src
  | .comb s => Tools.ShippingGen2.CombFacts s.d dom s.inits s.src

/-- Forget the fact. -/
def _root_.Tools.ShippingGen2.Pkg.toSem : Pkg ι dom → SemPkg ι dom
  | .gen p => .gen ⟨p.decl, p.d, p.kD, p.ρ, p.inh, p.inits, p.body, p.obsR, p.ext, p.extB, p.src⟩
  | .loop p => .loop ⟨p.decl, p.d, p.kD, p.α, p.inh, p.ρ, p.σ, p.inits, p.f, p.res, p.obsR, p.ext, p.extB, p.src⟩
  | .comb p => .comb ⟨p.decl, p.d, p.kD, p.inits, p.src⟩

/-- Attach the fact. -/
def genPkg : (s : SemPkg ι dom) → FactsOf s → Pkg ι dom
  | .gen s, hF => .gen ⟨s.decl, s.d, s.kD, s.ρ, s.inh, s.inits, s.body, s.obsR, s.ext, s.extB, s.src, hF⟩
  | .loop s, hF => .loop ⟨s.decl, s.d, s.kD, s.α, s.inh, s.ρ, s.σ, s.inits, s.f, s.res, s.obsR, s.ext, s.extB, s.src, hF⟩
  | .comb s, hF => .comb ⟨s.decl, s.d, s.kD, s.inits, s.src, hF⟩

/-- `Pkgs` forgetting facts, for the callee table `Q` of `genSem`. -/
def semOf (P : Name → Option (Pkg ι dom)) : Name → Option (SemPkg ι dom) := fun c => (P c).map Pkg.toSem

/-- The fact of a package is the `FactsOf` of its forgotten data. -/
theorem _root_.Tools.ShippingGen2.Pkg.factsOf_toSem : ∀ p : Pkg ι dom, FactsOf p.toSem
  | .gen p => p.gen
  | .loop p => p.facts
  | .comb p => p.facts

theorem toSem_genPkg : ∀ (s : SemPkg ι dom) (hF : FactsOf s), (genPkg s hF).toSem = s
  | .gen _, _ => rfl
  | .loop _, _ => rfl
  | .comb _, _ => rfl

/-- `toSem` is injective: the forgotten field is a Prop. -/
theorem pkg_eq_of_toSem : ∀ {p p' : Pkg ι dom}, p.toSem = p'.toSem → p = p'
  | .gen ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩,
    .gen ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩, h => by
    simp only [Pkg.toSem, SemPkg.gen.injEq, SrcSem.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, h5, rfl, h7, rfl, h9, h10, rfl⟩ := h
    cases h5; cases h7; cases h9; cases h10; rfl
  | .loop ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩,
    .loop ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩, h => by
    simp only [Pkg.toSem, SemPkg.loop.injEq, LoopSem.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, h5, rfl, h7, h8, rfl, h10, h11, h12, h13, rfl⟩ := h
    cases h5; cases h7; cases h8; cases h10; cases h11; cases h12; cases h13; rfl
  | .comb ⟨a1, a2, a3, a4, a5, a6⟩, .comb ⟨b1, b2, b3, b4, b5, b6⟩, h => by
    simp only [Pkg.toSem, SemPkg.comb.injEq, CombSem.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, h4, rfl⟩ := h
    cases h4; rfl
  | .gen _, .loop _, h => by cases h
  | .gen _, .comb _, h => by cases h
  | .loop _, .gen _, h => by cases h
  | .loop _, .comb _, h => by cases h
  | .comb _, .gen _, h => by cases h
  | .comb _, .loop _, h => by cases h

/-! ## Accessors agree (definitionally, by cases) -/

theorem decl_toSem (p : Pkg ι dom) : p.toSem.decl = p.decl := by cases p <;> rfl
theorem d_toSem (p : Pkg ι dom) : p.toSem.d = p.d := by cases p <;> rfl
theorem kD_toSem (p : Pkg ι dom) : p.toSem.kD = p.kD := by cases p <;> rfl
theorem src_toSem (p : Pkg ι dom) : p.toSem.src = p.src := by cases p <;> rfl
theorem extS_toSem (p : Pkg ι dom) : p.toSem.extS = p.extS := by cases p <;> rfl
theorem extBS_toSem (p : Pkg ι dom) : p.toSem.extBS = p.extBS := by cases p <;> rfl
theorem lsrc_toSem (p : Pkg ι dom) : p.toSem.lsrc = p.lsrc := by cases p <;> rfl
theorem S_toSem (p : Pkg ι dom) : p.toSem.S = p.S := by cases p <;> rfl

theorem extS_genPkg (s : SemPkg ι dom) (hF : FactsOf s) : (genPkg s hF).extS = s.extS := by cases s <;> rfl
theorem extBS_genPkg (s : SemPkg ι dom) (hF : FactsOf s) : (genPkg s hF).extBS = s.extBS := by cases s <;> rfl
theorem lsrc_genPkg (s : SemPkg ι dom) (hF : FactsOf s) : (genPkg s hF).lsrc = s.lsrc := by cases s <;> rfl
theorem src_genPkg (s : SemPkg ι dom) (hF : FactsOf s) : (genPkg s hF).src = s.src := by cases s <;> rfl
theorem d_genPkg (s : SemPkg ι dom) (hF : FactsOf s) : (genPkg s hF).d = s.d := by cases s <;> rfl
theorem kD_genPkg (s : SemPkg ι dom) (hF : FactsOf s) : (genPkg s hF).kD = s.kD := by cases s <;> rfl
theorem decl_genPkg (s : SemPkg ι dom) (hF : FactsOf s) : (genPkg s hF).decl = s.decl := by cases s <;> rfl
theorem S_genPkg (s : SemPkg ι dom) (hF : FactsOf s) : (genPkg s hF).S = s.S := by cases s <;> rfl

end Tools.ShippingGen5Sem
