import Tests.Compiler.CDefTest
-- SCOPE: M-shape class only (AMENDMENT 3; P_Q is not a member). Built earlier at 5c0d1c96 (gkid-focused-5c0d1c96 exit 0, 933/933: isDefEq type, 11
-- binders, standard axioms). The closure audit below was added on review; this SHA is rebuilt (see the issue record).
-- C4 G-KID (issue sparkle-gen-c4-gkid): `KidFactsNC` of every call entry of the top of a `MemSharedLeafParent`, generically.
-- Premises: only the C4 contract binders (P, O, T, entryL, entryW).  The class fields (AMENDMENT 3) supply every table / data fact.
-- No sorry, no axiom, no native_decide.
set_option autoImplicit false
set_option Elab.async false
namespace Tests.Compiler.C4Kid
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6
open Tools.ShippingCallsChildPorts (argWidths)
open Tools.ShippingMachineAuto Tools.ShippingMemCloses
open Tools.ShippingInstTagged (originAt)
open Tests.Compiler.CDef

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

theorem leaf_ifaceP_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape) {y : Res} (h : RealChildA O P.leaf.decl y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl P.leaf.decl) (Tools.ShippingMachineEntry.machNIn P.leaf.d.shape)
      (P.leaf.d.shape.layout.outs.map (·.name)) (P.lNames) y.1 y.2 :=
  memCallee_ifaceP O T P.leafMem
    (fun _ _ _ k hk y hn _ => by have := P.leafAllMem k hk; rw [hn] at this; exact absurd this (by decide)) entryL h

theorem leaf_kidFactsNC_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape) :
    KidFactsNC O P.leaf.decl P.leaf.d.shape.layout.outs (argWidths P.leaf.d P.nDecl) :=
  memCallee_kidFactsNC O T P.leafMem
    (fun _ _ _ k hk y hn _ => by have := P.leafAllMem k hk; rw [hn] at this; exact absurd this (by decide))
    P.lKidOuts P.lKidIns P.leafMemT
    (fun k hk hn => by have := P.leafAllMem k hk; rw [hn] at this; exact absurd this (by decide))
    P.leafCw (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (P.leafOutsClean o ho)) P.leafScalar entryL

theorem wrapper_kidFactsNC_of_class (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (w : GenPkg DomainConfig (fun i => i)) (hw : w ∈ P.wrappers)
    (entryW : MachineDefines mctx mref cctx cref w.decl w.d.shape) :
    KidFactsNC O w.decl w.d.shape.layout.outs (argWidths w.d P.nDecl) :=
  memCallee_kidFactsNC O T (P.wMem w hw)
    (fun m' c' _ k hk y _ hre => by
      rw [(P.wKids w hw k hk).1] at hre
      exact leaf_ifaceP_of_class P O T (mctx := m') (cctx := c') (Tools.ShippingReflectCtx.MachineDefines.ctx entryL) hre)
    (fun _ => P.leaf.d.shape.layout.outs) (fun _ => argWidths P.leaf.d P.nDecl)
    (fun k hk cb aw dw h => by rw [P.wAllOrd w hw k hk] at h; cases h)
    (fun k hk _ => by rw [(P.wKids w hw k hk).1]; exact leaf_kidFactsNC_of_class P O T entryL)
    (P.wCw w hw) (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (P.wOutsClean w hw o ho)) (P.wScalar w hw) entryW

theorem c4_hkid (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
    (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape) :
    ∀ (k : Nat) (hk : k < P.top.d.shape.insts.length), KidFactsNC O (P.top.d.shape.insts[k]).1 (P.outsOf k) (P.insOf k) := by
  intro k hk
  obtain ⟨hlt, hc⟩ := P.tieCallee k hk
  have ho := P.tieOuts k hk
  have hi := P.tieIns k hk
  have hlen := P.wlen
  have hlt' : P.wOf k < P.wArity.length := hlen ▸ hlt
  have hmem : P.wrappers[P.wOf k] ∈ P.wrappers := List.getElem_mem hlt
  have ha : P.wArity[P.wOf k] = P.nDecl := P.wArityN _ (List.getElem_mem hlt')
  have hcallee : (P.top.d.shape.insts[k]).1 = P.wrappers[P.wOf k].decl := by
    have h1 : (P.top.d.shape.insts.map (·.1))[k]? = some (P.top.d.shape.insts[k]).1 := by simp [hk]
    rw [h1] at hc
    have h2 : (P.wrappers.map (·.decl))[P.wOf k]? = some P.wrappers[P.wOf k].decl := by simp [hlt]
    rw [h2] at hc
    exact Option.some.inj hc
  have ho' : P.outsOf k = P.wrappers[P.wOf k].d.shape.layout.outs := by
    rw [ho]; simp [List.getD_eq_getElem?_getD, hlt]
  have hi' : P.insOf k = argWidths P.wrappers[P.wOf k].d P.nDecl := by
    have hz : (P.wrappers.zip P.wArity)[P.wOf k]? = some (P.wrappers[P.wOf k], P.wArity[P.wOf k]) := by
      rw [List.getElem?_eq_getElem (by simp only [List.length_zip]; omega)]; simp
    rw [hi, ← ha]; simp [List.getD_eq_getElem?_getD, hz]
  rw [hcallee, ho', hi']
  exact wrapper_kidFactsNC_of_class P O T entryL _ hmem (entryW _ hmem)

/-! ## corollary: `topshareM_hkid` -/
open Tests.Compiler.Srm9ComposedTest Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidIfaceTest in
theorem topshareM_hkid_of_class (hgrp : TmGrp) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape) :
    ∀ (k : Nat) (hk : k < topshareM.machineData.shape.insts.length),
      KidFactsNC O (topshareM.machineData.shape.insts[k]).1 (tmOuts k) (tmIns k) :=
  c4_hkid (P_M hgrp) O T entryL (fun wp hwp => by
    simp only [P_M, List.mem_cons, List.not_mem_nil, or_false] at hwp
    rcases hwp with rfl | rfl
    · exact entry₁
    · exact entry₂)

/-! ## audit -/
open Lean Meta Elab Term in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ci ← getConstInfo ``c4_hkid
  let expected ← elabTerm (← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
      {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
      (entryL : MachineDefines mctx mref cctx cref P.leaf.decl P.leaf.d.shape)
      (entryW : ∀ wp ∈ P.wrappers, MachineDefines mctx mref cctx cref wp.decl wp.d.shape),
      ∀ (k : Nat) (hk : k < P.top.d.shape.insts.length), KidFactsNC O (P.top.d.shape.insts[k]).1 (P.outsOf k) (P.insOf k))) none
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq ci.type (← instantiateMVars expected) do throwError "C4KID AUDIT FAILED: c4_hkid type differs from the stated theorem"
  forallTelescope ci.type fun xs _ => do
    let mut s := #[]
    for x in xs do s := s.push s!"{← x.fvarId!.getUserName}:{repr (← x.fvarId!.getBinderInfo)}"
    unless xs.size == 11 do throwError "C4KID AUDIT FAILED: {xs.size} binders, expected 11 (mctx mref cctx cref P O T entryL entryW k hk)"
    logInfo m!"C4KID|binders: {s}"
  for n in [``leaf_ifaceP_of_class, ``leaf_kidFactsNC_of_class, ``wrapper_kidFactsNC_of_class, ``c4_hkid, ``topshareM_hkid_of_class] do
    let axs ← Lean.collectAxioms n
    for x in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains x do throwError "C4KID AUDIT FAILED: {x} in {n}"
    logInfo m!"C4KID|axioms {n}: {axs}"

/-! ## closure audit (review request): the generic theorem reaches no instance constant and no premise substitute -/
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  -- walk every `Tests.*` constant reachable from c4_hkid's type and value (Tools / Sparkle / Lean constants are library code
  -- that cannot import Tests, so the walk stops at them)
  let mut seen : NameSet := {}
  let mut work : List Name := [``c4_hkid]
  let mut reached : Array Name := #[]
  while !work.isEmpty do
    let n := work.head!
    work := work.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "C4KID CLOSURE FAILED: {n} not found"
    -- read the body directly (as collectAxioms does): `value?` does not return theorem bodies here
    let body? : Option Lean.Expr := match ci with
      | .thmInfo t => some t.value
      | .defnInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    let cs := ci.type.getUsedConstants ++ (body?.map Lean.Expr.getUsedConstants).getD #[]
    for c in cs do
      -- substring match: auxiliary proofs may live under `_private.Tests…` names
      if (c.toString.splitOn "Tests.").length > 1 && !seen.contains c then
        reached := reached.push c
        work := c :: work
  logInfo m!"C4KID|closure reached: {reached.toList}"
  -- (1) only the class file and this file's own helpers
  for c in reached do
    unless (c.toString.splitOn "Tests.Compiler.CDef.").length > 1 || (c.toString.splitOn "Tests.Compiler.C4Kid.").length > 1 do
      throwError "C4KID CLOSURE FAILED: c4_hkid reaches {c} (outside the class definition and this file)"
  -- (2) no member value, no premise substitute
  for c in reached do
    -- whole name components (a field such as `leafMem` is not the instance `leafM`)
    for comp in c.components.map (·.toString) do
      if ["P_M", "P_Q", "WrapKidField", "wrapM", "wrapM3", "leafM", "leafP", "wrapP", "wrapQ"].contains comp
          || comp.startsWith "topshare" then
        throwError "C4KID CLOSURE FAILED: c4_hkid reaches {c} (instance / premise-substitute component {comp})"
  if env.contains `Tests.Compiler.C4Kid.WrapKidField then throwError "C4KID CLOSURE FAILED: WrapKidField is defined in this file"
  -- (3) the expected helper closure: exactly these three helpers of this file (plus compiler auxiliaries of them)
  let helpers := [``leaf_ifaceP_of_class, ``leaf_kidFactsNC_of_class, ``wrapper_kidFactsNC_of_class]
  for h in helpers do
    unless reached.contains h do throwError "C4KID CLOSURE FAILED: expected helper {h} not reached"
  for c in reached do
    if (c.toString.splitOn "Tests.Compiler.C4Kid.").length > 1 then
      unless (``c4_hkid :: helpers).any (fun h => (c.toString.splitOn h.toString).length > 1) do
        throwError "C4KID CLOSURE FAILED: unexpected own constant {c} in the closure"
  let cdef := reached.filter (fun c => (c.toString.splitOn "Tests.Compiler.CDef.").length > 1)
  logInfo m!"C4KID|closure ok: {reached.size} Tests constants reached = 3 helpers (+aux) and {cdef.size} class constants {cdef.toList}; no member value, no WrapKidField, no instance file"

#print axioms c4_hkid
#print axioms topshareM_hkid_of_class

end Tests.Compiler.C4Kid
