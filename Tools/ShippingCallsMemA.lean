import Tools.ShippingCallsCloseA
import Tools.ShippingMemClosesKidsT
import Tools.ShippingMemOnlyNames
import Tools.ShippingReaderOutsMemOnly
import Tools.ShippingMemOnly
-- BUILT (unit CM): cm6 exit 0 (Tools.ShippingCallsMemA); axioms standard (propext, Classical.choice, Quot.sound).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit CM: `CallsPureA` for memory children (the `closeInstsGM` memory branch), new boundary

RESTRICTED LEMMA. Old boundary: `machineClosesAt_of_kidsDMT` (`Tools/ShippingMemClosesKidsT.lean`)
runs `closeInstsGM_run_allM` (RefLaws, `ChildrenReal`, pin `hpair`) and then the PURE
`closeInstsG_of_kidsPT`. Here the pure half is reused verbatim and only the supply of its hypotheses
changes:
* children: `ChildrenRealA O` + `MemChildren` (from `closeInstsGM_runC`) instead of `ChildrenReal`;
  a child of entry `k` is `KidTA` (origin-built module, or origin builds none and `RealChildA`);
* `hpair` (two entries of one callee AND one memory key have ONE child): for memory keys it follows from
  `MemChildren` (both are the built memory module); for entries WITHOUT a memory key the old proof used
  the cache pin (`synthesizeChild_pin`, RefLaws); there is no pin on the `JQC` boundary, so the
  hypothesis `hdistOrd` (no two entries without a memory key name the same callee) replaces it.
  `hdistOrd` EXCLUDES inputs with a repeated non-memory callee; it is a hypothesis, not a compiler guard,
  and such shapes are NOT counted as ported (units CN2/AX1 work on the pin).
* mixed gate + memory: covered (the ord children only need `ChildIfaceP`, as in the old theorem).

PREMISES kept from the old theorem (data/name premises, `hkid` at `KidTA`): `hkid hargsN hfieldOut hfieldsNd
hsep hparent hfresh hparentD hdisjD`. `ChildrenRealA` is a HISTORY of past synthesis results, not semantic
correctness in the current environment; nothing here is a runtime-fit proof. -/

namespace Tools.ShippingCallsMemA
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingCallsGate Tools.ShippingCallsRunG Tools.ShippingSeqChildIface
open Tools.ShippingCallsKidsD
open Tools.ShippingMemCloses
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildRunAKids Tools.ShippingCallsCloseA

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The origin-based kid on the new boundary: the origin's built module, or (origin builds none) a
`RealChildA` of the entry's declaration. -/
def KidTA (O : RefLawsAOps MkRefd mref cref) (o : InstOrigin) (c : Name) (y : Res) : Prop :=
  o.child? = some y ∨ (o.child? = none ∧ RealChildA O c y)

set_option maxHeartbeats 1000000 in
/-- **`CallsPureA` for memory (and mixed gate + memory) children.** RESTRICTED by `hdistOrd`. -/
theorem callsPureA_of_memKids (O : RefLawsAOps MkRefd mref cref) {declName : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (nameK : Nat → String) (nk : Nat → Nat) (outsK : Nat → List String)
    (namesK : Nat → List String)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y →
      ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ outsK k)
    (hdistOrd : ∀ (i j : Nat) (hi : i < d.shape.insts.length) (hj : j < d.shape.insts.length),
      i ≠ j → (d.shape.insts[i]).1 = (d.shape.insts[j]).1 →
      memKey (originAt d.shape i) = none → memKey (originAt d.shape j) = none → False)
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      memKey (originAt d.shape k) = memKey (originAt d.shape k') →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), nameK k = nameK k' →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        memKey (originAt d.shape k) = memKey (originAt d.shape k'))
    (hparent : ∀ (k : Nat), k < d.shape.insts.length → nameK k ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (gi : Nat) (k : Nat), k < d.shape.insts.length → ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{nameK k}")
    (hparentD : ∀ (k : Nat), k < d.shape.insts.length → (Sparkle.IR.ModuleName.ofDecl declName) ∉ namesK k)
    (hdisjD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length),
      ¬ ((d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        memKey (originAt d.shape k) = memKey (originAt d.shape k')) →
      nameK k ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k') :
    CallsPureA O declName d.shape := by
  intro tenv b t d₀ t' children run hcl hreal
  refine ⟨fun h => absurd h hfne, fun _ hmc => ?_⟩
  obtain ⟨hlenC, hall⟩ := hreal
  have hfull : ∀ (k : Nat) (c : Res), children[k]? = some c →
      ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) c.1 c.2 := by
    intro k c hc
    have hk : k < d.shape.insts.length := by
      rw [← hlenC]
      exact (List.getElem?_eq_some_iff.mp hc).1
    obtain ⟨y, hy, hor⟩ := hall k hk
    rw [hc] at hy
    cases hy
    refine hkid k hk c ?_
    rcases hor with ho | hre
    · exact Or.inl ho
    · cases hom : (originAt d.shape k).child? with
      | none => exact Or.inr ⟨hom, hre⟩
      | some md =>
        have := hmc k hk md hom
        rw [hc] at this
        cases this
        exact Or.inl hom
  have hsameCall : ∀ (i j : Nat) (hi : i < d.shape.insts.length)
      (hj : j < d.shape.insts.length), (d.shape.insts[i]).1 = (d.shape.insts[j]).1 →
      memKey (originAt d.shape i) = memKey (originAt d.shape j) →
      children[i]? = children[j]? := by
    intro i j hi hj hcc hkey
    cases hki : memKey (originAt d.shape i) with
    | none =>
      by_cases hij : i = j
      · rw [hij]
      · exact (hdistOrd i j hi hj hij hcc hki (hkey ▸ hki)).elim
    | some p =>
      obtain ⟨cb, aw, dw⟩ := p
      have h1 := child?_of_memKey hki
      have h2 := child?_of_memKey (hkey ▸ hki)
      rw [hmc i hi _ h1, hmc j hj _ h2]
  refine closeInstsG_of_kidsPT d ok hbody hC hslots hdomB run hcl hlenC nameK nk outsK
    namesK hfull hsameCall ?_ hargsN hfieldOut hfieldsNd hsep hparent hfresh hparentD
  intro i j hki hkj ci cj hci hcj hdecl a ha b' hb hn
  exfalso
  have fi := hfull i ci hci
  have fj := hfull j cj hcj
  obtain ⟨hx1, hx2⟩ := hdisjD i hki j hkj hdecl
  obtain ⟨hx3, -⟩ := hdisjD j hkj i hki (fun e => hdecl ⟨e.1.symm, e.2.symm⟩)
  have han : a.name = nameK i ∨ a.name ∈ namesK i := by
    rcases List.mem_cons.mp ha with hae | hai
    · exact Or.inl (by rw [hae]; exact fi.name)
    · exact Or.inr (fi.desNames a hai)
  have hbn : b'.name = nameK j ∨ b'.name ∈ namesK j := by
    rcases List.mem_cons.mp hb with hbe | hbj
    · exact Or.inl (by rw [hbe]; exact fj.name)
    · exact Or.inr (fj.desNames b' hbj)
  rcases han with han | han
  · rcases hbn with hbn | hbn
    · exact hdecl (hsep i hki j hkj (by rw [← han, ← hbn, hn]))
    · exact hx1 (by rw [← han, hn]; exact hbn)
  · rcases hbn with hbn | hbn
    · exact hx3 (by rw [← hbn, ← hn]; exact han)
    · exact hx2 _ han (by rw [hn]; exact hbn)

/-- **`MachineClosesAtA` for memory (and mixed) parents** (with `T`, as `machineClosesAtA_of_tele`).
RESTRICTED by `hdistOrd` (see the header). -/
theorem machineClosesAtA_of_memKids (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) {declName : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (nameK : Nat → String) (nk : Nat → Nat) (outsK : Nat → List String)
    (namesK : Nat → List String)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      KidTA O (originAt d.shape k) (d.shape.insts[k]).1 y →
      ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ outsK k)
    (hdistOrd : ∀ (i j : Nat) (hi : i < d.shape.insts.length) (hj : j < d.shape.insts.length),
      i ≠ j → (d.shape.insts[i]).1 = (d.shape.insts[j]).1 →
      memKey (originAt d.shape i) = none → memKey (originAt d.shape j) = none → False)
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      memKey (originAt d.shape k) = memKey (originAt d.shape k') →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), nameK k = nameK k' →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        memKey (originAt d.shape k) = memKey (originAt d.shape k'))
    (hparent : ∀ (k : Nat), k < d.shape.insts.length → nameK k ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (gi : Nat) (k : Nat), k < d.shape.insts.length → ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{nameK k}")
    (hparentD : ∀ (k : Nat), k < d.shape.insts.length → (Sparkle.IR.ModuleName.ofDecl declName) ∉ namesK k)
    (hdisjD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length),
      ¬ ((d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        memKey (originAt d.shape k) = memKey (originAt d.shape k')) →
      nameK k ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k') :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName d.shape :=
  machineClosesAtA_of_tele O T hA
    (letsClose_of_data d ok hbody halias mctx mref cctx cref)
    (callsPureA_of_memKids O d ok hbody hC hslots hdomB hfne nameK nk outsK namesK hkid hargsN
      hfieldOut hdistOrd hfieldsNd hsep hparent hfresh hparentD hdisjD)

/-! ## Memory-only parents (UNRESTRICTED only in the sense: no repeated-callee restriction — no ord entry, so
`hdistOrd` is vacuous. Every other data condition of these theorems (`MemOnlyData`, `MemOnlyCloseData`, …)
REMAINS a premise.) -/

open Sparkle.Compiler.MachMemory (memModule memChild? memChildName memParams?)
open Sparkle.IR.ModuleName (ofDecl ofMem)

/-- The module name of the memory an origin builds (`""` for an origin that builds none). -/
def memNameO : InstOrigin → String
  | .mem cb aw dw => (memModule cb aw dw).1.name
  | .ord => ""
  | .field _ => ""

theorem memKey_of_child?_some {o : InstOrigin} {cb : Bool} {aw dw : Nat}
    (h : o.child? = some (memModule cb aw dw)) : memKey o = some (cb, aw, dw) := by
  cases o with
  | ord => cases h
  | field _ => cases h
  | mem cb' aw' dw' =>
    have e : memModule cb' aw' dw' = memModule cb aw dw := Option.some.inj h
    have e2 : memParams? (memModule cb' aw' dw').1 = memParams? (memModule cb aw dw).1 := by
      rw [e]
    rw [Tools.ShippingMachineShipsHier.memParams_memModule',
      Tools.ShippingMachineShipsHier.memParams_memModule'] at e2
    exact e2

theorem memNameO_of_child? {o : InstOrigin} {cb : Bool} {aw dw : Nat}
    (h : o.child? = some (memModule cb aw dw)) : memNameO o = (memModule cb aw dw).1.name := by
  cases o with
  | ord => cases h
  | field _ => cases h
  | mem cb' aw' dw' =>
    have e : memModule cb' aw' dw' = memModule cb aw dw := Option.some.inj h
    show (memModule cb' aw' dw').1.name = _
    rw [e]

/-- **`MachineClosesAtA` of a memory-only parent** (every entry a memory placeholder whose name
decodes to its origin, `hagree`): the data premises of `machineClosesAt_memOnly_names`, no reflection
premise and NO distinct-callee restriction. Premises: `O`, `hA`, `T`, the reader data. -/
theorem machineClosesAtA_memOnly_names (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) {declName : Name}
    (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (hmem : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      ∃ (cb : Bool) (aw dw : Nat), memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw))
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (d.shape.insts[k]).2.1.length = 4)
    (hfield : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" = "out")
    (hargsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 → k = k')
    (hout : ∀ o ∈ d.shape.layout.outs, o.name.toList.head? ≠ some 'i')
    (hagree : Tools.ShippingInstTagged.TagsAgree d.shape) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName d.shape := by
  -- every origin builds the memory its placeholder names
  have horig : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∃ (cb : Bool) (aw dw : Nat),
      (originAt d.shape k).child? = some (memModule cb aw dw) ∧
      (d.shape.insts[k]).1 = memChildName cb aw dw := by
    intro k hk
    obtain ⟨cb, aw, dw, hc⟩ := hmem k hk
    refine ⟨cb, aw, dw, ?_, Tools.ShippingMemOnlyNames.memChild_name_of hc⟩
    have := Tools.ShippingInstTagged.agree_at hagree hk
    rw [hc] at this
    exact this.symm
  have hkey : ∀ (k : Nat) (hk : k < d.shape.insts.length), ∃ (cb : Bool) (aw dw : Nat),
      memKey (originAt d.shape k) = some (cb, aw, dw) ∧ memNameO (originAt d.shape k) = ofMem cb aw dw ∧
      (d.shape.insts[k]).1 = memChildName cb aw dw := by
    intro k hk
    obtain ⟨cb, aw, dw, ho, hn⟩ := horig k hk
    refine ⟨cb, aw, dw, memKey_of_child?_some ho, ?_, hn⟩
    rw [memNameO_of_child? ho]
    exact Tools.ShippingMemOnlyNames.memModule_name cb aw dw
  have hnameEq : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length),
      memNameO (originAt d.shape k) = memNameO (originAt d.shape k') →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        memKey (originAt d.shape k) = memKey (originAt d.shape k') := by
    intro k hk k' hk' he
    obtain ⟨cb, aw, dw, hk1, hn1, hc1⟩ := hkey k hk
    obtain ⟨cb', aw', dw', hk2, hn2, hc2⟩ := hkey k' hk'
    rw [hn1, hn2] at he
    obtain ⟨e1, e2, e3⟩ := Tools.ShippingModuleName.ofMem_injective he
    subst e1 e2 e3
    exact ⟨hc1.trans hc2.symm, hk1.trans hk2.symm⟩
  intro tenv
  refine machineClosesAtA_of_memKids (declName := declName) O T hA d ok hbody halias hC hslots hdomB hfne
    (fun k => memNameO (originAt d.shape k)) (fun _ => 4) (fun _ => ["out"])
    (fun k => [memNameO (originAt d.shape k)]) ?_ ?_ ?_ ?_ ?_ hnameEq ?_ ?_ ?_ ?_
  · intro k hk y hy
    obtain ⟨cb, aw, dw, ho, -⟩ := horig k hk
    rcases hy with hy | ⟨hn, -⟩
    · rw [ho] at hy
      have e : memModule cb aw dw = y := Option.some.inj hy
      subst e
      have hnm : memNameO (originAt d.shape k) = (memModule cb aw dw).1.name :=
        memNameO_of_child? ho
      show ChildIfaceP (memNameO (originAt d.shape k)) 4 ["out"] [memNameO (originAt d.shape k)] _ _
      rw [hnm]
      exact memIface cb aw dw
    · rw [ho] at hn; cases hn
  · intro k hk; exact (hargsN k hk).symm
  · intro k hk
    show d.shape.instFields.getD k "" ∈ ["out"]
    exact List.mem_singleton.mpr (hfield k hk)
  · intro i j hi hj hij _ hki _
    obtain ⟨cb, aw, dw, hk1, -, -⟩ := hkey i hi
    rw [hk1] at hki; cases hki
  · intro k hk k' hk' hc hkk ha _
    exact hargsNd k hk k' hk' hc ha
  · intro k hk e
    obtain ⟨cb, aw, dw, -, hn, -⟩ := hkey k hk
    exact Tools.ShippingModuleName.ofDecl_ne_ofMem declName cb aw dw (e.symm.trans hn)
  · intro gi k _ o ho
    exact Tools.ShippingCallsGate.instName_ne_of_head (hout o ho) gi _
  · intro k hk hx
    obtain ⟨cb, aw, dw, -, hn, -⟩ := hkey k hk
    have := List.mem_singleton.mp hx
    exact Tools.ShippingModuleName.ofDecl_ne_ofMem declName cb aw dw (this.trans hn)
  · intro k hk k' hk' hne
    have hn : memNameO (originAt d.shape k) ≠ memNameO (originAt d.shape k') :=
      fun e => hne (hnameEq k hk k' hk' e)
    refine ⟨fun hx => hn (List.mem_singleton.mp hx), fun x hx hx' => hn ?_⟩
    exact (List.mem_singleton.mp hx).symm.trans (List.mem_singleton.mp hx')

/-- **`MachineClosesAtA` of a memory-only parent over the built `MemOnlyData`** (the new-boundary
`machineClosesAt_of_memOnlyData_names`): premises `O`, `hA`, `T` and the decided reader data. -/
theorem machineClosesAtA_of_memOnlyData_names (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx) {declName : Name}
    {d : MachineData} {nDecl aw dw : Nat}
    (D : Tools.ShippingMemOnly.MemOnlyData d nDecl aw dw)
    (C : Tools.ShippingMemOnlyCloses.MemOnlyCloseData d) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName d.shape :=
  machineClosesAtA_memOnly_names O T hA d D.ok D.body C.alias D.calls D.slots D.domB D.fne
    (Tools.ShippingMemOnlyNames.memAll_of_data D) C.argsN C.field C.argsNd C.outHead C.agree

end Tools.ShippingCallsMemA

#print axioms Tools.ShippingCallsMemA.machineClosesAtA_of_memKids
#print axioms Tools.ShippingCallsMemA.machineClosesAtA_memOnly_names
#print axioms Tools.ShippingCallsMemA.machineClosesAtA_of_memOnlyData_names
