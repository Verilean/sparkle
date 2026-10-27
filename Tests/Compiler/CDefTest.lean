import Tests.Compiler.Srm9ComposedTest
import Tests.Compiler.SharedLeafMemKidEntryTest
import Tools.ShippingSeqParentGenD2MSD
-- C-DEF (issue sparkle-gen-c4-cdef): GenPkg / MemSharedLeafParent exactly as scripts/c3/EXPECTED_CDEF.lean.txt (+ members and defeq audits below). Test-only; no production edit.
-- NOT proved here: G-KID, G-HCALLS (unresolved dependencies). C4 and G3 stay OPEN.
-- (C-DEF, before AMENDMENT 3) BUILT: cdef-focused-6127769f (issue-linked, runner 2a678c60) exit 0, 932/932, CDEF|ok (14 constants, standard axioms). Earlier
-- cdef-focused-addc3543-r2a6 / -f96ef0f4 / -13242754 failed in this file (the deviations below), after the C targets built.
-- DEVIATION (2026-10-26, first build cdef-focused-addc3543-r2a6): EXPECTED_CDEF line 8 `open A B C (x y)` is not valid Lean (parse error at
-- 8:88); here it is split into `open A B` + `open C (x y)` with the same names, and `open Tools.ShippingMachineAuto (MachineData)` is added
-- (EXPECTED never opened it: every `d.ss` failed), likewise NmParentData / NCal / MixedGateBinder; autoImplicit is turned off so an
-- unresolved name is an error, not a silent implicit binder. EXPECTED_CDEF is left as frozen.
-- AMENDMENT 3 (2026-10-26, user decision, recorded in scripts/c3/C_CLASS.md): the class is narrowed to the M shape (every wrapper calls only
-- the memory-bearing leaf); P_Q is NOT a member; leaf is a GenPkg again; per-leaf / per-wrapper certificate fields (DATA / GEN-SHAPE) added.
-- AMENDMENT 6 (wCallOut, GEN-SHAPE) is not yet built at this SHA.
-- AMENDMENT 5 (wArgsIn via argInOk, DATA) BUILT: amend5-cdef-3868973c (issue-linked, runner 2a678c60) exit 0, 932/932, CDEF|ok.
-- AMENDMENT 4 (G-CLOSES data: tieCs, leaf MemOnlyData/CloseData/cne, wrapper tags/agree/cne/notin, csNc/csCd; all DATA) BUILT:
-- amend4-cdef-9daedb4a (issue-linked, runner 2a678c60) exit 0, 932/932, CDEF|ok.
-- AMENDMENT 3 BUILT: amend3-cdef-50f8b26e (issue-linked, runner 2a678c60) exit 0, 932/932, CDEF|ok (P_M + 6 audits). History:
-- AMENDMENT 2 (recorded in scripts/c3/C_CLASS.md, found after freezing): `leaf` is a LeafPkg (decl, d, src), not a GenPkg. leafP has no instances, so the generator emits no
-- leafP.machineExt / machineExtB / machine_ext_causal and the drafted leafP_gen cannot exist; the class only ever reads leaf.decl, leaf.d,
-- leaf.src (memLeafBsC / memLeafOutsC / memLeafSrcC / memLeafPC in the G-HCALLS row). Fewer requirements, not more.
set_option autoImplicit false
namespace Tests.Compiler.CDef
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts QuadGroupFacts)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingNmEntry (NmParentData)
open Tools.ShippingNmGroup (NCal)
open Sparkle.Compiler.Elab (MixedGateBinder)
open Tools.ShippingCallsChildPorts (argWidths)

structure GenPkg (ι : Type) (dom : ι → DomainConfig) where
  decl : Lean.Name
  d : MachineData
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
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)
  gen : @GenFacts d ι dom ρ inh inits body obsR ext extB src

noncomputable def GenPkg.extS {ι} {dom} (p : GenPkg ι dom) := fun i bools bits =>
  p.ext i bools bits (@stateLoop _ _ _ p.inh p.inits (p.body i bools bits))
noncomputable def GenPkg.extBS {ι} {dom} (p : GenPkg ι dom) := fun i bools bits =>
  p.extB i bools bits (@stateLoop _ _ _ p.inh p.inits (p.body i bools bits))
noncomputable def GenPkg.lsrc {ι} {dom} (p : GenPkg ι dom) :=
  @Tools.ShippingMachineCausal.letObsB p.d ι dom p.inh p.ρ p.inits p.body p.ext p.extB

/-- AMENDMENT 5: at leaf port `p` (of the port list `bs`), the call argument `args[portIdx bs p]` is a let of `d` whose term is
`d`'s own input term of that port: `boolInput j` with `bpos j = p`, or `bitsInput n j` (same width) with `vpos j = p`. Domain ports and
positions past the list are vacuous. -/
def argInOk (d : MachineData) (bs : List (Name × MixedGateBinder)) (args : List Nat) (p : Nat) : Bool :=
  match bs[p]? with
  | none => true
  | some b =>
    match b.2 with
    | .domain => true
    | .bool =>
      match args[Tools.ShippingMachineChild.portIdx bs p]? with
      | none => false
      | some a =>
        match d.ls[a]? with
        | some ⟨.bool, .boolInput j⟩ => d.bpos j == p
        | _ => false
    | .bits n =>
      match args[Tools.ShippingMachineChild.portIdx bs p]? with
      | none => false
      | some a =>
        match d.ls[a]? with
        | some ⟨.bits m, .bitsInput _ j⟩ => m == n && d.vpos j == p
        | _ => false

structure MemSharedLeafParent where
  top : GenPkg Unit (fun _ => defaultDomain)
  nDecl : Nat
  cs : List NCal
  pdata : NmParentData top.d cs top.decl nDecl
  outTy : ∀ o ∈ top.d.shape.layout.outs, o.ty.bitWidth = o.width
  noMem : ∀ x ∈ top.d.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true
  slotsNe : top.d.shape.layout.slots ≠ []
  outsOf : Nat → List OutField
  insOf : Nat → List Nat
  cw : Tools.ShippingCallWidths.callWidthsOk top.d nDecl outsOf = true
  ca : Tools.ShippingPortsMatchRaw.callArgsOk top.d nDecl insOf = true
  leaf : GenPkg DomainConfig (fun i => i)            -- AMENDMENT 3 (M shape): GenPkg again (AMENDMENT 2's LeafPkg was only for the plain leafP of P_Q)
  wrappers : List (GenPkg DomainConfig (fun i => i))
  bsC : Lean.Name → List (Name × MixedGateBinder)
  outsC : Lean.Name → List OutField
  srcC : Unit → Lean.Name → (Nat → List Nat) → List (Nat → Nat)
  group : QuadGroupFacts top.d nDecl top.lsrc top.extS top.extBS bsC outsC srcC
  -- AMENDMENT 1 (wrapper / leaf / callee ties; all decidable data except tieSrcC = structural defeq):
  wArity : List Nat                                   -- DATA: declared-input count of each wrapper (M: [4,4]; Q: [3,5])
  wOf : Nat → Nat                                     -- DATA: call index k ↦ index of the wrapper called at k
  wlen : wrappers.length = wArity.length              -- DATA CHECK
  tieCallee : ∀ k, k < top.d.shape.insts.length →
    wOf k < wrappers.length ∧ (top.d.shape.insts.map (·.1))[k]? = (wrappers.map (·.decl))[wOf k]?   -- DATA CHECK (decide)
  tieOuts : ∀ k, k < top.d.shape.insts.length → outsOf k = (wrappers.map (·.d.shape.layout.outs)).getD (wOf k) []   -- DATA CHECK
  tieIns : ∀ k, k < top.d.shape.insts.length →
    insOf k = ((wrappers.zip wArity).map (fun p => argWidths p.1.d p.2)).getD (wOf k) []                  -- DATA CHECK
  tieLeaf : ∀ w ∈ wrappers, leaf.decl ∈ w.d.shape.insts.map (·.1)                                    -- DATA CHECK (leaf is a callee of every wrapper)
  tieBsC : ∀ p ∈ wrappers.zip wArity, bsC p.1.decl = p.1.d.bsIn.take p.2                              -- DATA CHECK
  tieOutsC : ∀ p ∈ wrappers.zip wArity, outsC p.1.decl = p.1.d.shape.layout.outs                      -- DATA CHECK
  tieSrcC : ∀ p ∈ wrappers.zip wArity, srcC () p.1.decl = fun vals => p.1.src defaultDomain
    (Tools.ShippingMachineChild.boolsOf (p.1.d.bsIn.take p.2) vals) (Tools.ShippingMachineChild.bitsOf (p.1.d.bsIn.take p.2) vals)   -- STRUCTURAL (rfl-style)
  -- AMENDMENT 3 (M shape: every wrapper calls only the memory-bearing leaf; scripts/c3/C_CLASS.md). DATA = decide (+ machine_ok/body);
  -- GEN-SHAPE = a fact about the generated ext/extB/body, filled per member by its uniform unfolding (as leafM_hext / wrapM_hext).
  lNameK : Nat → String                               -- DATA: the leaf's call tables (its memory entries)
  lNk : Nat → Nat
  lOutsK : Nat → List String
  lNamesK : Nat → List String
  lNames : List String
  lKidOuts : Nat → List OutField
  lKidIns : Nat → List Nat
  leafMem : Tools.ShippingSrm3Callee.MemCalleeData leaf.d leaf.decl nDecl lNameK lNk lOutsK lNamesK lNames   -- DATA
  leafAllMem : ∀ k (hk : k < leaf.d.shape.insts.length),
    (Tools.ShippingInstTagged.originAt leaf.d.shape k).child?.isSome = true                                -- DATA (every leaf call is a memory)
  leafMemT : ∀ (k : Nat) (hk : k < leaf.d.shape.insts.length) (cb : Bool) (aw dw : Nat),
    (Tools.ShippingInstTagged.originAt leaf.d.shape k).child? = some (Sparkle.Compiler.MachMemory.memModule cb aw dw) →
    lKidOuts k = Tools.ShippingMemKid.memOuts dw ∧ lKidIns k = Tools.ShippingMemKid.memIns aw dw         -- DATA (memory tables)
  leafCw : Tools.ShippingCallWidths.callWidthsOk leaf.d nDecl lKidOuts = true                              -- DATA
  leafOutsClean : ∀ o ∈ leaf.d.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true -- DATA
  leafScalar : ∀ o ∈ leaf.d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true                -- DATA
  leafOutOk : ∀ o ∈ leaf.d.shape.layout.outs, outNameOk o.name = true                                       -- DATA
  leafMemCalls : @Tools.ShippingSrm4Run.MemCalls leaf.d nDecl leaf.ρ leaf.inh leaf.inits leaf.body leaf.ext leaf.extB  -- GEN-SHAPE
  leafHextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat),
    j < nDecl → leaf.extBS i bools bits j = bools j                                                        -- GEN-SHAPE
  leafHext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat),
    j < nDecl → leaf.extS i bools bits j n' = bits j n'                                                    -- GEN-SHAPE
  wMem : ∀ w ∈ wrappers, Tools.ShippingSrm3Callee.MemCalleeData w.d w.decl nDecl
    (fun _ => Sparkle.IR.ModuleName.ofDecl leaf.decl) (fun _ => Tools.ShippingMachineEntry.machNIn leaf.d.shape)
    (fun _ => leaf.d.shape.layout.outs.map (·.name)) (fun _ => lNames) (Sparkle.IR.ModuleName.ofDecl leaf.decl :: lNames)  -- DATA
  wKids : ∀ w ∈ wrappers, ∀ (k : Nat) (hk : k < w.d.shape.insts.length),
    (w.d.shape.insts[k]).1 = leaf.decl ∧ Tools.ShippingMemCloses.memKey (Tools.ShippingInstTagged.originAt w.d.shape k) = none  -- DATA
  wAllOrd : ∀ w ∈ wrappers, ∀ (k : Nat) (hk : k < w.d.shape.insts.length),
    (Tools.ShippingInstTagged.originAt w.d.shape k).child? = none                                          -- DATA
  wArgsN : ∀ w ∈ wrappers, ∀ (k : Nat) (hk : k < w.d.shape.insts.length),
    (w.d.shape.insts[k]).2.1.length = ((leaf.d.bsIn.take nDecl).filter Tools.ShippingPortWidthsPure.nonDom).length  -- DATA
  wWid : ∀ w ∈ wrappers, Tools.ShippingPortsMatchRaw.callArgsOk w.d nDecl (fun _ => argWidths leaf.d nDecl) = true  -- DATA
  wCw : ∀ w ∈ wrappers, Tools.ShippingCallWidths.callWidthsOk w.d nDecl (fun _ => leaf.d.shape.layout.outs) = true  -- DATA
  wOutsClean : ∀ w ∈ wrappers, ∀ o ∈ w.d.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true  -- DATA
  wScalar : ∀ w ∈ wrappers, ∀ o ∈ w.d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true     -- DATA
  wOutOk : ∀ w ∈ wrappers, ∀ o ∈ w.d.shape.layout.outs, outNameOk o.name = true                           -- DATA
  wHextB : ∀ w ∈ wrappers, ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n))
    (j : Nat), j < nDecl → w.extBS i bools bits j = bools j                                                -- GEN-SHAPE
  wHext : ∀ w ∈ wrappers, ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n))
    (j n' : Nat), j < nDecl → w.extS i bools bits j n' = bits j n'                                         -- GEN-SHAPE
  wArityN : ∀ a ∈ wArity, a = nDecl                                                                         -- DATA (one arity)
  -- AMENDMENT 4 (G-CLOSES data; scripts/c3/C_CLASS.md): ties the callee list cs to the wrappers, and the leaf / wrapper step data. All DATA.
  lAw : Nat                                           -- DATA: the leaf's memory address / data width (one memory shape)
  lDw : Nat
  leafMemOnly : Tools.ShippingMemOnly.MemOnlyData leaf.d nDecl lAw lDw                                     -- DATA
  leafCloseData : Tools.ShippingMemOnlyCloses.MemOnlyCloseData leaf.d                                     -- DATA
  leafCne : ∀ k (hk : k < leaf.d.shape.insts.length), (leaf.d.shape.insts[k]).1 ≠ leaf.decl               -- DATA
  wTags : ∀ w ∈ wrappers, ∀ x ∈ w.d.shape.instTagged, x.2.child? = none ∧ x.1 = leaf.decl                -- DATA
  wAgree : ∀ w ∈ wrappers, Tools.ShippingInstTagged.TagsAgree w.d.shape                                    -- DATA
  wCne : ∀ w ∈ wrappers, ∀ k (hk : k < w.d.shape.insts.length), (w.d.shape.insts[k]).1 ≠ w.decl          -- DATA
  wNotin : ∀ w ∈ wrappers, w.decl ∉ leaf.d.shape.insts.map (·.1)                                          -- DATA
  tieCs : cs = wrappers.map (fun w => (⟨w.decl, w.d, leaf.d.shape.insts.map (·.1),
    Sparkle.IR.ModuleName.ofDecl leaf.decl :: lNames⟩ : NCal))                                            -- DATA (rfl)
  csNc : ∀ e ∈ cs, ∀ e' ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c) ∧ e'.c ∉ e.Gs  -- DATA
  csCd : ∀ e ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ top.decl) ∧ top.decl ∉ e.Gs    -- DATA
  -- AMENDMENT 5 (G-HCALLS decoding data; scripts/c3/C_CLASS.md): each wrapper call passes, at every non-domain leaf port p, the
  -- wrapper's own input term of that port (so the decoded call arguments ARE the wrapper's input families). DATA (decide).
  wArgsIn : ∀ w ∈ wrappers, ∀ (k : Nat) (hk : k < w.d.shape.insts.length) (p : Nat),
    p < (leaf.d.bsIn.take nDecl).length → argInOk w.d (leaf.d.bsIn.take nDecl) (w.d.shape.insts[k]).2.1 p = true
  -- AMENDMENT 6 (G-HCALLS call output; user decision 2026-10-26: GEN-SHAPE class field, filled per member by the uniform unfolding of
  -- the generated ext / extB / machineSource, as wHext): at every wrapper call k, the generated ext / extB at the call-output position
  -- nDecl + k IS the leaf source's output k' (named like the call's field) on any families agreeing with the inputs at the leaf ports.
  wCallOut : ∀ w ∈ wrappers, ∀ (k : Nat) (_ : k < w.d.shape.insts.length) (i : DomainConfig) (bools : Nat → Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)),
    ∃ (k' : Nat) (o : OutField), leaf.d.shape.layout.outs[k']? = some o ∧ o.name = w.d.shape.instFields.getD k "" ∧
      ∀ (bools' : Nat → Signal i Bool) (bits' : (j : Nat) → (n : Nat) → Signal i (BitVec n)),
        (∀ p, (leaf.d.bsIn.take nDecl)[p]?.map (·.2) = some MixedGateBinder.bool → bools' p = bools p) →
        (∀ p n, (leaf.d.bsIn.take nDecl)[p]?.map (·.2) = some (MixedGateBinder.bits n) → bits' p n = bits p n) →
        ∃ f : Nat → Nat, (leaf.src i bools' bits')[k']? = some f ∧
          ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => (w.extBS i bools bits p).val τ) (fun p n => (w.extS i bools bits p n).val τ)
            (nDecl + k) (((w.d.bsIn.drop nDecl)[k]?.map (·.2)).getD .domain) = f τ          -- GEN-SHAPE


open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidIfaceTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tests.Compiler.SharedLeafMemKidRunTest
open Tests.Compiler.Srm9ComposedTest
variable {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}

/-! ## AMENDMENT 6: the member's call-output facts (moved from Tests/Compiler/C4HCallsTest.lean, c4-hcalls3 19192bdd) -/
open Tools.ShippingMachineEntry (posEnc)

theorem wrapM_len2 : wrapM.machineData.shape.insts.length = 2 := by decide
theorem wrapM3_len2 : wrapM3.machineData.shape.insts.length = 2 := by decide

theorem wrapM_callOut (k : Nat) (hk : k < wrapM.machineData.shape.insts.length) (i : DomainConfig) (bools : Nat → Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) :
    ∃ (k' : Nat) (o : OutField), leafM.machineData.shape.layout.outs[k']? = some o ∧
      o.name = wrapM.machineData.shape.instFields.getD k "" ∧
      ∀ (bools' : Nat → Signal i Bool) (bits' : (j : Nat) → (n : Nat) → Signal i (BitVec n)),
        (∀ p, (leafM.machineData.bsIn.take 4)[p]?.map (·.2) = some MixedGateBinder.bool → bools' p = bools p) →
        (∀ p n, (leafM.machineData.bsIn.take 4)[p]?.map (·.2) = some (MixedGateBinder.bits n) → bits' p n = bits p n) →
        ∃ f : Nat → Nat, (leafM.machineSource i bools' bits')[k']? = some f ∧
          ∀ τ, posEnc (fun p => ((wrapM.machineExtB i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits))) p).val τ)
            (fun p n => ((wrapM.machineExt i bools bits (stateLoop wrapM.machineInits (wrapM.machineBody i bools bits))) p n).val τ)
            (4 + k) (((wrapM.machineData.bsIn.drop 4)[k]?.map (·.2)).getD .domain) = f τ := by
  have hk2 : k = 0 ∨ k = 1 := by have := wrapM_len2; omega
  rcases hk2 with rfl | rfl
  · refine ⟨0, leafM.machineData.shape.layout.outs[0]'(by decide), List.getElem?_eq_getElem (by decide), by decide +kernel, ?_⟩
    intro bools' bits' hb hb'
    have hA : bools' 1 = bools 1 := hb 1 (by first | decide +kernel | rfl)
    have hB2 : bits' 2 4 = bits 2 4 := hb' 2 4 (by first | decide +kernel | rfl)
    have hB3 : bits' 3 8 = bits 3 8 := hb' 3 8 (by first | decide +kernel | rfl)
    obtain ⟨f, hf⟩ : ∃ f, (leafM.machineSource i bools' bits')[0]? = some f := by
      unfold leafM.machineSource; exact ⟨_, rfl⟩
    refine ⟨f, hf, ?_⟩
    unfold leafM.machineSource at hf
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
    subst hf
    intro τ
    unfold posEnc
    unfold wrapM.machineExt wrapM.machineExtB
    simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
    have hk : ((wrapM.machineData.bsIn.drop 4)[0]?.map (·.2)).getD .domain = .bits 8 := by decide +kernel
    rw [hk, hA, hB2, hB3]
    simp
  · refine ⟨1, leafM.machineData.shape.layout.outs[1]'(by decide), List.getElem?_eq_getElem (by decide), by decide +kernel, ?_⟩
    intro bools' bits' hb hb'
    have hA : bools' 1 = bools 1 := hb 1 (by first | decide +kernel | rfl)
    have hB2 : bits' 2 4 = bits 2 4 := hb' 2 4 (by first | decide +kernel | rfl)
    have hB3 : bits' 3 8 = bits 3 8 := hb' 3 8 (by first | decide +kernel | rfl)
    obtain ⟨f, hf⟩ : ∃ f, (leafM.machineSource i bools' bits')[1]? = some f := by
      unfold leafM.machineSource; exact ⟨_, rfl⟩
    refine ⟨f, hf, ?_⟩
    unfold leafM.machineSource at hf
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hf
    subst hf
    intro τ
    unfold posEnc
    unfold wrapM.machineExt wrapM.machineExtB
    simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
    have hk : ((wrapM.machineData.bsIn.drop 4)[1]?.map (·.2)).getD .domain = .bool := by decide +kernel
    rw [hk, hA, hB2, hB3]
    simp

theorem wrapM3_callOut (k : Nat) (hk : k < wrapM3.machineData.shape.insts.length) (i : DomainConfig) (bools : Nat → Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) :
    ∃ (k' : Nat) (o : OutField), leafM.machineData.shape.layout.outs[k']? = some o ∧
      o.name = wrapM3.machineData.shape.instFields.getD k "" ∧
      ∀ (bools' : Nat → Signal i Bool) (bits' : (j : Nat) → (n : Nat) → Signal i (BitVec n)),
        (∀ p, (leafM.machineData.bsIn.take 4)[p]?.map (·.2) = some MixedGateBinder.bool → bools' p = bools p) →
        (∀ p n, (leafM.machineData.bsIn.take 4)[p]?.map (·.2) = some (MixedGateBinder.bits n) → bits' p n = bits p n) →
        ∃ f : Nat → Nat, (leafM.machineSource i bools' bits')[k']? = some f ∧
          ∀ τ, posEnc (fun p => ((wrapM3.machineExtB i bools bits (stateLoop wrapM3.machineInits (wrapM3.machineBody i bools bits))) p).val τ)
            (fun p n => ((wrapM3.machineExt i bools bits (stateLoop wrapM3.machineInits (wrapM3.machineBody i bools bits))) p n).val τ)
            (4 + k) (((wrapM3.machineData.bsIn.drop 4)[k]?.map (·.2)).getD .domain) = f τ := by
  have hk2 : k = 0 ∨ k = 1 := by have := wrapM3_len2; omega
  rcases hk2 with rfl | rfl
  · refine ⟨0, leafM.machineData.shape.layout.outs[0]'(by decide), List.getElem?_eq_getElem (by decide), by decide +kernel, ?_⟩
    intro bools' bits' hb hb'
    have hA : bools' 1 = bools 1 := hb 1 (by first | decide +kernel | rfl)
    have hB2 : bits' 2 4 = bits 2 4 := hb' 2 4 (by first | decide +kernel | rfl)
    have hB3 : bits' 3 8 = bits 3 8 := hb' 3 8 (by first | decide +kernel | rfl)
    obtain ⟨f, hf⟩ : ∃ f, (leafM.machineSource i bools' bits')[0]? = some f := by
      unfold leafM.machineSource; exact ⟨_, rfl⟩
    refine ⟨f, hf, ?_⟩
    unfold leafM.machineSource at hf
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
    subst hf
    intro τ
    unfold posEnc
    unfold wrapM3.machineExt wrapM3.machineExtB
    simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
    have hk : ((wrapM3.machineData.bsIn.drop 4)[0]?.map (·.2)).getD .domain = .bits 8 := by decide +kernel
    rw [hk, hA, hB2, hB3]
    simp
  · refine ⟨1, leafM.machineData.shape.layout.outs[1]'(by decide), List.getElem?_eq_getElem (by decide), by decide +kernel, ?_⟩
    intro bools' bits' hb hb'
    have hA : bools' 1 = bools 1 := hb 1 (by first | decide +kernel | rfl)
    have hB2 : bits' 2 4 = bits 2 4 := hb' 2 4 (by first | decide +kernel | rfl)
    have hB3 : bits' 3 8 = bits 3 8 := hb' 3 8 (by first | decide +kernel | rfl)
    obtain ⟨f, hf⟩ : ∃ f, (leafM.machineSource i bools' bits')[1]? = some f := by
      unfold leafM.machineSource; exact ⟨_, rfl⟩
    refine ⟨f, hf, ?_⟩
    unfold leafM.machineSource at hf
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hf
    subst hf
    intro τ
    unfold posEnc
    unfold wrapM3.machineExt wrapM3.machineExtB
    simp only [Tools.ShippingMachineAuto.extendBits, Tools.ShippingMachineCausal.extendBools]
    have hk : ((wrapM3.machineData.bsIn.drop 4)[1]?.map (·.2)).getD .domain = .bool := by decide +kernel
    rw [hk, hA, hB2, hB3]
    simp



/-! ## P_M  (TmGrp is a PREMISE of TmBnd, not a theorem: P_M takes it as a hypothesis = the structural class assumption) -/
noncomputable def P_M (hgrp : TmGrp) : MemSharedLeafParent where
  top := { decl := ``topshareM, d := topshareM.machineData, ρ := _, inh := topshareM_inhab, inits := topshareM.machineInits,
           body := topshareM.machineBody, obsR := topshareM.machineResult, ext := topshareM.machineExt, extB := topshareM.machineExtB,
           src := topshareM.machineSource, gen := topshareM_gen }
  nDecl := 4
  cs := csM
  pdata := topshareM_parentData
  outTy := topshareM_outTy
  noMem := topshareM_nomem
  slotsNe := topshareM_slotsNe
  outsOf := tmOuts
  insOf := tmIns
  cw := topshareM_cw
  ca := topshareM_ca
  leaf := { decl := ``leafM, d := leafM.machineData, ρ := _, inh := leafM_inhab, inits := leafM.machineInits, body := leafM.machineBody,
            obsR := leafM.machineResult, ext := leafM.machineExt, extB := leafM.machineExtB, src := leafM.machineSource, gen := leafM_gen }
  wrappers := [{ decl := ``wrapM, d := wrapM.machineData, ρ := _, inh := wrapM_inhab, inits := wrapM.machineInits, body := wrapM.machineBody,
                 obsR := wrapM.machineResult, ext := wrapM.machineExt, extB := wrapM.machineExtB, src := wrapM.machineSource, gen := wrapM_gen },
               { decl := ``wrapM3, d := wrapM3.machineData, ρ := _, inh := wrapM3_inhab, inits := wrapM3.machineInits, body := wrapM3.machineBody,
                 obsR := wrapM3.machineResult, ext := wrapM3.machineExt, extB := wrapM3.machineExtB, src := wrapM3.machineSource, gen := wrapM3_gen }]
  bsC := tmBsC
  outsC := tmOutsC
  srcC := tmSrcC
  group := hgrp
  wArity := [4, 4]
  wOf := fun k => if k < 2 then 0 else 1
  wlen := rfl
  tieCallee := by first | decide | decide +kernel
  tieOuts := by first | decide | decide +kernel
  tieIns := by first | decide | decide +kernel
  tieLeaf := by first | decide | decide +kernel
  tieBsC := by first | decide | decide +kernel | (intro p hp; simp [List.zip] at hp; rcases hp with rfl | rfl <;> rfl)
  tieOutsC := by first | decide | decide +kernel | (intro p hp; simp [List.zip] at hp; rcases hp with rfl | rfl <;> rfl)
  tieSrcC := by intro p hp; simp [List.zip] at hp; rcases hp with rfl | rfl <;> rfl
  lNameK := lmName
  lNk := lmNk
  lOutsK := lmOuts
  lNamesK := lmNames
  lNames := [memNm]
  lKidOuts := lmKidOuts
  lKidIns := lmKidIns
  leafMem := leafM_memCallee
  leafAllMem := leafM_allmem
  leafMemT := fun k hk cb aw dw h => by
    have hk' : k < leafM.machineData.shape.insts.length := hk
    have hk0 : k = 0 := by have := leafM_len; omega
    subst hk0
    obtain ⟨e1, e2, e3⟩ := Tools.ShippingSrm4Kid.memModule_inj ((Option.some.inj (leafM_origin0.symm.trans h)))
    subst e1; subst e2; subst e3
    exact ⟨rfl, rfl⟩
  leafCw := by first | decide | decide +kernel
  leafOutsClean := leafM_outsClean
  leafScalar := by first | decide | decide +kernel
  leafOutOk := leafM_outOk
  leafMemCalls := leafM_memcalls
  leafHextB := leafM_hextB
  leafHext := leafM_hext
  wMem := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | exact wrapM_memCallee | exact wrapM3_memCallee
  wKids := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | decide | decide +kernel
  wAllOrd := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | decide | decide +kernel
  wArgsN := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | decide | decide +kernel
  wWid := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | decide | decide +kernel
  wCw := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | decide | decide +kernel
  wOutsClean := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | decide | decide +kernel
  wScalar := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | decide | decide +kernel
  wOutOk := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | decide | decide +kernel
  wHextB := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | exact wrapM_hextB | exact wrapM3_hextB
  wHext := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | exact wrapM_hext | exact wrapM3_hext
  wArityN := by decide
  lAw := 4
  lDw := 8
  leafMemOnly := leafM_memOnly
  leafCloseData := leafM_closeData
  leafCne := leafM_cne
  wTags := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | exact wrapM_tags | exact wrapM3_tags
  wAgree := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | exact wrapM_agree | exact wrapM3_agree
  wCne := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | exact wrapM_cne | exact wrapM3_cne
  wNotin := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | exact wrapM_notin | exact wrapM3_notin
  tieCs := rfl
  csNc := csM_nc
  csCd := csM_cd
  wArgsIn := by intro w hw; simp only [List.mem_cons, List.not_mem_nil, or_false] at hw; rcases hw with rfl | rfl <;> first | decide | decide +kernel
  wCallOut := by
    intro w hw k hk i bools bits
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact wrapM_callOut k hk i bools bits
    · exact wrapM3_callOut k hk i bools bits

/-! ## defeq audits (M): the class projections ARE the terms of TmGrp / topshareM_soundLA / tmOuts / tmIns / tmBsC -/
theorem P_M_group_defeq (hgrp : TmGrp) :
    QuadGroupFacts (P_M hgrp).top.d (P_M hgrp).nDecl (P_M hgrp).top.lsrc (P_M hgrp).top.extS (P_M hgrp).top.extBS (P_M hgrp).bsC (P_M hgrp).outsC (P_M hgrp).srcC = TmGrp := rfl
theorem P_M_ext_defeq (hgrp : TmGrp) : (P_M hgrp).top.extS = tmExt := rfl
theorem P_M_extB_defeq (hgrp : TmGrp) : (P_M hgrp).top.extBS = tmExtB := rfl
theorem P_M_lsrc_defeq (hgrp : TmGrp) :
    (P_M hgrp).top.lsrc = Tools.ShippingMachineCausal.letObsB topshareM.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareM.machineInits
        topshareM.machineBody topshareM.machineExt topshareM.machineExtB := rfl
theorem P_M_tables_defeq (hgrp : TmGrp) : (P_M hgrp).outsOf = tmOuts ∧ (P_M hgrp).insOf = tmIns ∧ (P_M hgrp).bsC = tmBsC ∧ (P_M hgrp).outsC = tmOutsC ∧ (P_M hgrp).srcC = tmSrcC :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
/-- the statement of `topshareM_soundLA` re-spelled through the class projections is the same type -/
theorem P_M_soundL_defeq (hgrp : TmGrp) :
    Tools.ShippingMachineAuto.MachineTraceLB (P_M hgrp).top.decl (P_M hgrp).top.d m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) (P_M hgrp).top.src
      (P_M hgrp).top.extS (P_M hgrp).top.extBS (P_M hgrp).top.lsrc =
    Tools.ShippingMachineAuto.MachineTraceLB ``topshareM topshareM.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareM.machineSource
      (fun i bools bits => topshareM.machineExt i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      (fun i bools bits => topshareM.machineExtB i bools bits (stateLoop topshareM.machineInits (topshareM.machineBody i bools bits)))
      (Tools.ShippingMachineCausal.letObsB topshareM.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) topshareM.machineInits
        topshareM.machineBody topshareM.machineExt topshareM.machineExtB) := rfl

/-! ## expected / binder / closure checks for the member P_M (AMENDMENT 3: P_Q is not a member) -/
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- the member takes exactly ONE explicit binder, the group class assumption TmGrp, nothing else
  for (n, g) in [(``P_M, ``Tests.Compiler.Srm9ComposedTest.TmGrp)] do
    let t := (← getConstInfo n).type
    forallTelescope t fun xs body => do
      unless xs.size == 1 do throwError "CDEF AUDIT FAILED: {n} has {xs.size} binders, expected 1 (the group assumption)"
      unless ← isDefEq (← inferType xs[0]!) (mkConst g) do throwError "CDEF AUDIT FAILED: {n}'s binder is not {g}"
      unless ← isDefEq body (mkConst ``MemSharedLeafParent) do throwError "CDEF AUDIT FAILED: {n} is not a MemSharedLeafParent"
  let audits := [``P_M_group_defeq, ``P_M_ext_defeq, ``P_M_extB_defeq, ``P_M_lsrc_defeq, ``P_M_tables_defeq, ``P_M_soundL_defeq, ``P_M]
  -- literal coverage guard: exactly these 7 constants (P_M and its 6 projection audits; AMENDMENT 3 removed P_Q and its 6); deleting one fails here
  let expected : List Name := [``P_M,
    ``P_M_group_defeq, ``P_M_ext_defeq, ``P_M_extB_defeq, ``P_M_lsrc_defeq, ``P_M_tables_defeq, ``P_M_soundL_defeq]
  unless expected.length == 7 do throwError "CDEF AUDIT FAILED: expected-name list has {expected.length} entries, not 7"
  unless audits.length == 7 do throwError "CDEF AUDIT FAILED: audit list has {audits.length} entries, not 7"
  unless audits.Nodup do throwError "CDEF AUDIT FAILED: duplicate entries in the audit list"
  unless expected.Nodup do throwError "CDEF AUDIT FAILED: duplicate entries in the expected-name list"
  for a in audits do
    unless expected.contains a do throwError "CDEF AUDIT FAILED: {a} in the audit list is not an expected name"
  for e in expected do
    unless audits.contains e do throwError "CDEF AUDIT FAILED: {e} missing from the audit list"
    discard <| getConstInfo e
  for a in audits do
    let axs ← Lean.collectAxioms a
    for x in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains x do throwError "CDEF AUDIT FAILED: non-standard axiom {x} in {a}"
  -- AMENDMENT 3 removed the Q member: it must not be in the environment of this file
  if (← getEnv).contains `Tests.Compiler.CDef.P_Q then throwError "CDEF AUDIT FAILED: P_Q still defined"
  logInfo m!"CDEF|ok|P_M: one binder (TmGrp), type MemSharedLeafParent (AMENDMENT 3, M shape); {audits.length} constants (6 defeq audits, P_M) with standard axioms only"

end Tests.Compiler.CDef
