# C3 — class C (SPECIFICATION; NOT elaborated, NOT proved). Base par/c3-spec @ 99dcc0863f3fa157aea7daed19cb8da5cdbc087e (accepted SRM33 final).
SRM37 (accepted 130283ce) is not checked out (read via `git show 130283ce:…` only). int-srm10 candidate c31383a1 (unvalidated) NOT used. No build.
Every type below is copied from a cited source declaration; the two `structure`s and four `def`s are NEW (exact text, to be added by the C4 unit).
Name resolution: as in Tools/ShippingQuadComposed.lean (genTrace :156, QuadGroupFacts :680), Tools/ShippingNmEntry.lean (NmParentData :100),
Tests/Compiler/Srm4ParentTest.lean (topshareM_nomem :57, topshareM_cw :68, topshareM_gen :174), Tests/Compiler/Srm9ComposedTest.lean (TmGrp :59).

## NEW exact definitions
/-- A machine-route declaration with the generator's kernel-checked facts (the shape of `f.machine_*`; cf. `topshareM_gen`). -/
structure GenPkg (ι : Type) (dom : ι → DomainConfig) where
  decl  : Lean.Name
  d     : MachineData
  ρ     : ι → Type
  inh   : Inhabited (HList (tys d.ss))
  inits : HList (tys d.ss)
  body  : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
            RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
            Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i)
  obsR  : (i : ι) → ρ i → List (Nat → Nat)
  ext   : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
            Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)
  extB  : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
            Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool
  src   : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)
  gen   : GenFacts d dom inits body obsR ext extB src          -- GENERATOR-CERTIFIED field (supplied by the #machine command's theorems)

noncomputable def GenPkg.extS {ι} {dom} (p : GenPkg ι dom) := fun i bools bits => p.ext i bools bits (@stateLoop _ _ _ p.inh p.inits (p.body i bools bits))
noncomputable def GenPkg.extBS {ι} {dom} (p : GenPkg ι dom) := fun i bools bits => p.extB i bools bits (@stateLoop _ _ _ p.inh p.inits (p.body i bools bits))
noncomputable def GenPkg.lsrc {ι} {dom} (p : GenPkg ι dom) := Tools.ShippingMachineCausal.letObsB p.d dom p.inits p.body p.ext p.extB
  -- (extS/extBS/lsrc are exactly the terms TmGrp / topshareM_soundLA use for topshareM; the implicit-argument spelling of stateLoop is fixed when elaborated)

/-- The class C: memory shared-leaf parents at instance depth 2. -/
structure MemSharedLeafParent where
  top      : GenPkg Unit (fun _ => defaultDomain)
  nDecl    : Nat
  cs       : List NCal
  pdata    : NmParentData top.d cs top.decl nDecl                                   -- DATA CHECKS (decide), = topshareM_parentData
  outTy    : ∀ o ∈ top.d.shape.layout.outs, o.ty.bitWidth = o.width                 -- DATA CHECK (decide), = topshareM_outTy
  noMem    : ∀ x ∈ top.d.shape.instTagged, x.2.child?.isNone = true ∧
               (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true              -- DATA CHECK (decide), = topshareM_nomem
  slotsNe  : top.d.shape.layout.slots ≠ []                                          -- DATA CHECK (decide), = topshareM_slotsNe
  outsOf   : Nat → List OutField                                                    -- DATA (= tmOuts)
  insOf    : Nat → List Nat                                                         -- DATA (= tmIns)
  cw       : Tools.ShippingCallWidths.callWidthsOk top.d nDecl outsOf = true        -- DATA CHECK (decide), = topshareM_cw
  ca       : Tools.ShippingPortsMatchRaw.callArgsOk top.d nDecl insOf = true        -- DATA CHECK (decide), = topshareM_ca
  leaf     : GenPkg DomainConfig (fun i => i)                                       -- the shared memory leaf (= leafM package)
  wrappers : List (GenPkg DomainConfig (fun i => i))                                -- the callees (= [wrapM, wrapM3] packages)
  bsC      : Lean.Name → List (Lean.Name × MixedGateBinder)                          -- DATA (= tmBsC)
  outsC    : Lean.Name → List OutField                                              -- DATA (= tmOutsC)
  srcC     : Unit → Lean.Name → (Nat → List Nat) → List (Nat → Nat)                 -- DATA (= tmSrcC)
  group    : QuadGroupFacts top.d nDecl top.lsrc top.extS top.extBS bsC outsC srcC  -- STRUCTURAL CLASS ASSUMPTION (option (a)), = TmGrp

## Classification of `group` (reviewer request): option (a)
`group` is NOT a decidable data check. It is a STRUCTURAL CLASS CONDITION: C consists of parents whose calls are grouped as QuadGroupFacts states
(it is exactly TmGrp, Tests/Compiler/Srm9ComposedTest.lean:59, which C2 carries as a PREMISE inside TmBnd). C4 therefore REQUIRES grouped calls;
it does NOT derive grouping. Deriving it from a Bool check is the separate, optional named item G-GRP-DERIVE (GAP_MAP.md).

## Known incompleteness of C (frozen honestly; amendments must be recorded)
* The tie between `wrappers`/`leaf` and the parent's call targets (`cs`, `top.d.shape.insts`) and the wrapper/leaf conditions needed by G-KID and
  G-HCALLS are NOT yet fields: they are fixed when G-KID / G-HCALLS are stated (each added field must be a decidable or generator-certified check,
  or an explicitly labelled structural class assumption, recorded as a C amendment). Until then C over-approximates the class for those two lemmas.
Members (to be instantiated by the C4 unit, by decide + the generated `f.machine_*` theorems): P_M (topshareM; wrappers wrapM/wrapM3; leaf leafM),
P_Q (topshareQ). C is the structure, not the list {topshareM, topshareQ}.
