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

## AMENDMENT 1 (C-DEF, issue sparkle-gen-c4-cdef, frozen before elaboration; base 42f1db69)
Exact Lean text: scripts/c3/EXPECTED_CDEF.lean.txt. Adds to MemSharedLeafParent the wrapper/leaf/callee ties that the "Known incompleteness" paragraph left open:
`wArity, wOf, wlen, tieCallee, tieOuts, tieIns, tieLeaf, tieBsC, tieOutsC, tieSrcC` (all DATA CHECKS by decide, except tieSrcC = structural defeq of the callee source table).
Reason for `wArity`: P_Q's wrappers have different declared arities (wrapP 3, wrapQ 5, parent nDecl 4), so `argWidths w.d nDecl` cannot be the tie.
Reason for `tieLeaf` as membership (not equality): in P_Q, wrapQ has a leaf call AND its own memory child (`wrapQ_kids`); the memory is not in a single shared leaf there. P_Q therefore only
conforms to the *shape* of C (and its `leaf` is leafP, which has no memory); the class name "MemSharedLeafParent" over-states P_Q and this is recorded, not hidden.
UNRESOLVED (NOT fields, NOT assumed): G-KID (`KidFactsNC` per call) and G-HCALLS (TmH1/TmH2 shape) remain separate dependencies; no per-design binder is added for them.
`gen` fields need the Inhabited instance + GenFacts proofs of leaf/wrappers (wrapM_gen etc., spread over Srm4CalleeTest/Srm4ComposedTest/Srm4MixedTest/Srm4RunTest/Srm4ComposedQTest); leafP_gen is not found in the tree and, if missing, is built from leafP.machine_* in CDefTest.

## AMENDMENT 2 (C-DEF, issue sparkle-gen-c4-cdef; found AFTER freezing, at first elaboration 2026-10-26; base addc3543, recorded at the C-DEF review SHA)
This amendment was found only when the class first elaborated (it was never built before the runner fix). It is NOT part of the frozen
scripts/c3/EXPECTED_CDEF.lean.txt, which stays as frozen. The exact text that builds is in Tests/Compiler/CDefTest.lean (cdef-focused-0c30b6d7 exit 0).
Change: the `leaf` field of MemSharedLeafParent is `leaf : LeafPkg DomainConfig (fun i => i)` instead of `leaf : GenPkg DomainConfig (fun i => i)`, with

```lean
structure LeafPkg (ι : Type) (dom : ι → DomainConfig) where
  decl : Lean.Name
  d : MachineData
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)
```

(the same three fields as in GenPkg, with the same types; GenPkg's ρ, inh, inits, body, obsR, ext, extB, gen are dropped for the leaf).
Reason: leafP (the leaf of P_Q) has no instances, so the generator emits no leafP.machineExt / machineExtB / machine_ext_causal, and the
GenFacts certificate that GenPkg.gen requires cannot be built for it (the drafted leafP_gen, see AMENDMENT 1's last line, does not exist and
cannot). The class reads the leaf only through leaf.decl, leaf.d and leaf.src (memLeafBsC / memLeafOutsC / memLeafSrcC / memLeafPC in the
G-HCALLS row of GAP_MAP.md, and tieLeaf). This narrows the requirement; it adds no field and no assumption.
Audit consequence: leafP_gen (and leafP_inhab) are removed, so the CDefTest audit set goes from 15 to 14 constants (P_M, P_Q, 12 projection
defeq audits), with the literal count guard changed to 14.
Elaboration-only fixes recorded with it (not class changes): EXPECTED line 8 `open A B C (x y)` is invalid Lean and is split into two opens with
the same names (D1); the opens EXPECTED never had (MachineData, NmParentData, NCal, MixedGateBinder) are added and autoImplicit is false (D2).

## AMENDMENT 3 (C4, issue sparkle-gen-c4-amend3; user decision 2026-10-26: "M shape only first")
Scope narrowing, decided after the C4 gap analysis (G-KID / G-HCALLS / G-COMPOSED instance proofs, 2026-10-26):
* C is narrowed to the M SHAPE: every wrapper calls only the leaf, and every call of the leaf is a memory entry. Every wrapper's declared
  arity equals nDecl (`wArityN`).
* P_Q (topshareQ) is NOT a member, for three reasons:
  - leafP is a plain leaf, so its closes fact `MachineCloses leafP` would be needed, and it is proved nowhere and is not a binder of the frozen C4 statement;
  - wrapQ mixes leaf and memory calls, so memLeafCallee_hcalls does not apply;
  - the wrapper arities (3, 5) differ from nDecl 4.

  The Q shape becomes a separate later class (issue sparkle-gen-c5-qshape).
* `leaf` is a GenPkg again. AMENDMENT 2's LeafPkg existed only because leafP has no generated ext. Every M-shape leaf has instances,
  so it has a generated machineExt / machineExtB, and its GenFacts are needed by the leaf run (memCallee_seqChildRunN).
* New fields. Exact Lean text is in Tests/Compiler/CDefTest.lean, the block "AMENDMENT 3" in MemSharedLeafParent. Each is labelled:
  - DATA: decide, plus machine_ok/body.
  - GEN-SHAPE: a fact about the generated ext / extB / body, filled per member by the same uniform unfolding as the existing
    leafM_hext / wrapM_hext / leafM_memcalls. NOT a generator certificate. A later unit may derive these generically.
  - Leaf call tables: lNameK lNk lOutsK lNamesK lNames lKidOuts lKidIns.
  - Leaf: leafMem (MemCalleeData, DATA), leafAllMem, leafMemT, leafCw, leafOutsClean, leafScalar, leafOutOk (DATA);
    leafMemCalls, leafHextB, leafHext (GEN-SHAPE).
  - Per wrapper: wMem (MemCalleeData with the leaf's tables, DATA), wKids, wAllOrd, wArgsN, wWid, wCw, wOutsClean, wScalar,
    wOutOk (DATA); wHextB, wHext (GEN-SHAPE); and wArityN (DATA).
  - None of them is a target Prop (KidFactsNC, HCallsOf, CallFactF, closes, run): those stay the C4 work items.
* Audit consequence: the CDefTest audit set is P_M plus its 6 defeq audits = 7 constants (was 14 with P_Q). C4 recovers only the
  topshareM corollary.
* The frozen C4 statement text (scripts/c3/C4_STATEMENT.lean.txt) is unchanged, since it only reads P.leaf.decl / P.leaf.d.

## AMENDMENT 4 (C4, issue sparkle-gen-c4-amend4; found by G-CLOSES worker c4-closes on 088da6aa, 2026-10-26)
G-CLOSES (nm_closes0 / nm_machineRun, Tools/ShippingNmEntry.lean:363/397) needs CalleeNM for every e ∈ cs and CalleeIface cs.
Every CalleeNM field reads e.d / e.Gs / e.names. The class only tied the call-target names (pdata.names, tieCallee), so e.d, e.Gs and
e.names were unconstrained. Added fields, all DATA (decide / rfl for P_M; exact text in the CDefTest.lean block "AMENDMENT 4"):
* The callee list:
  - `tieCs : cs = wrappers.map (fun w => ⟨w.decl, w.d, leaf.d.shape.insts.map (·.1), ofDecl leaf.decl :: lNames⟩)`
  - csNc / csCd (the nc / cd checks of NmCallees, as csM_nc / csM_cd).
* The leaf's step data, as leafM_step = memLeaf_stepNM (Tools/ShippingMemLeafRun.lean:493):
  - lAw, lDw (one memory shape)
  - leafMemOnly : MemOnlyData leaf.d nDecl lAw lDw
  - leafCloseData : MemOnlyCloseData leaf.d
  - leafCne.
* The wrappers' CalleeNM data, as wrapM_calleeNM: wTags, wAgree (TagsAgree), wCne, wNotin.

No target Prop is added. The closes / step / ifaceP facts are still derived by the C4 units.
