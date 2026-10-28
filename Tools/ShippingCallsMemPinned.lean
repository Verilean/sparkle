import Tools.ShippingCallsGatePinned
import Tools.ShippingCallsMemA
-- BUILT (unit GMP): gmp4 exit 0 (Tools.ShippingCallsMemPinned); axioms standard (propext, Classical.choice, Quot.sound).
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit GMP: the pin for the general / memory closing (`closeInstsGM`), `hdistOrd` removed

* `mapM_loop_pinG`, `closeInstsGM_runP`: a returning run of the general closing from a `JQC O (D+1)`
  world returns the PURE `closeInstsG` of children that are `ChildrenRealA` + `MemChildren` and satisfy
  `SameCalleeNonMem` (two NON-memory entries — origin builds no child — of one callee carry the same
  child). Proof: each non-memory entry is a `synthesizeChild` step (`synthesizeChild_pinned`, PinC); memory
  entries are pure and change neither world nor pin. Same callee ⇒ same cache entry at the end ⇒ same child.
  NOT from `RealChildA`/types/histories.
* `CallsPureGP`, `machineClosesAtA_of_pure_pinG`: `CallsPureP` extended by the non-memory pin in the general
  conjunct.
* `callsPureGP_of_memKids'`, `machineClosesAtA_of_memKids'`: CM's lemmas with `hdistOrd` DROPPED.
Premises: `O`, `hA`, `T` (as `machineClosesAtA_of_tele`) and CM's data/name premises; no pin hypothesis.
`ChildrenRealA` is a history; not a runtime-fit proof. -/

namespace Tools.ShippingCallsMemPinned
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
open Tools.ShippingChildBndInit Tools.ShippingChildBndCore
open Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildDepthC
open Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildRunAKids
open Tools.ShippingChildCoreC Tools.ShippingChildPinC Tools.ShippingChildRunA
open Tools.ShippingCallsCloseA Tools.ShippingCallsGateA Tools.ShippingCallsGatePin
open Tools.ShippingCallsGatePinned Tools.ShippingCallsMemA
open Tools.ShippingChildTranslateA Tools.ShippingChildFrontCP
open Tools.ShippingClosesSplit

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- Two NON-memory entries (origin builds no child) of one callee carry the same child. -/
def SameCalleeNonMem (shape : MachineShape) (children : List Res) : Prop :=
  ∀ (k₁ k₂ : Nat) (h₁ : k₁ < shape.insts.length) (h₂ : k₂ < shape.insts.length),
    (shape.insts[k₁]).1 = (shape.insts[k₂]).1 →
    (shape.instOrigins.getD k₁ .ord).child? = none →
    (shape.instOrigins.getD k₂ .ord).child? = none → children[k₁]? = children[k₂]?

/-- The `mapM` loop of the general closing keeps the pin; non-memory entries are recorded at their child. -/
theorem mapM_loop_pinG (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat} (hD : 1 ≤ D)
    (f : Name × InstOrigin → MetaM Res)
    (hf : ∀ x, f x = match x.2.child? with
      | some md => pure md
      | none => synthesizeChild x.1) :
    ∀ (l : List (Name × InstOrigin)) (acc : List Res) (L : List (Name × Res)) (r : List Res)
      (w w' : Void IO.RealWorld), JQP O D L w →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧
          (∀ md, l[k].2.child? = some md → y = md) ∧
          (l[k].2.child? = some y ∨ (l[k].2.child? = none ∧ RealChildA O l[k].1 y ∧
            (cv w').get? l[k].1 = some y))) ∧ JQP O D L w'
  | [], acc, L, r, w, w', hp, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), hp⟩
  | (c, o) :: xs, acc, L, r, w, w', hp, h => by
    obtain ⟨y, w1, hy, h2⟩ := RunsTo.bind h
    rw [hf] at hy
    dsimp only at hy
    cases hmc : o.child? with
    | some md =>
      rw [hmc] at hy
      obtain ⟨rfl, rfl⟩ := RunsTo.pure_world hy
      obtain ⟨ys, hr, hlen, hk, hp'⟩ :=
        mapM_loop_pinG O T hA hD f hf xs (y :: acc) L r _ w' hp h2
      refine ⟨y :: ys, by simp [hr], by simp [hlen], fun k hk' => ?_, hp'⟩
      cases k with
      | zero => refine ⟨y, rfl, ?_⟩; show (∀ md, o.child? = some md → y = md) ∧ _; exact ⟨fun md' h' => by
          have : (some y : Option _) = some md' := by rw [← hmc]; exact h'
          exact Option.some.inj this, Or.inl hmc⟩
      | succ k =>
        obtain ⟨z, hz, hmz, hrz⟩ := hk k (by simpa using hk')
        exact ⟨z, by simpa using hz, by simpa using hmz, by simpa using hrz⟩
    | none =>
      rw [hmc] at hy
      obtain ⟨hreal, hjq, hget⟩ := triple_runs (synthesizeChild_pinned O T hA hD L c) hp hy
      have hp1 : JQP O D ((c, y) :: L) w1 := by
        refine ⟨hjq.1, fun p hp' => ?_⟩
        rcases List.mem_cons.mp hp' with rfl | hm
        · exact hget
        · exact hjq.2 p hm
      obtain ⟨ys, hr, hlen, hk, hp'⟩ :=
        mapM_loop_pinG O T hA hD f hf xs (y :: acc) ((c, y) :: L) r w1 w' hp1 h2
      refine ⟨y :: ys, by simp [hr], by simp [hlen], fun k hk' => ?_, ⟨hp'.1, fun p hm => hp'.2 p
        (List.mem_cons_of_mem _ hm)⟩⟩
      cases k with
      | zero => refine ⟨y, rfl, ?_⟩; show (∀ md, o.child? = some md → y = md) ∧ _; exact ⟨fun md' h' => (by rw [hmc] at h'; cases h'),
          Or.inr ⟨hmc, hreal, hp'.2 (c, y) (List.mem_cons_self ..)⟩⟩
      | succ k =>
        obtain ⟨z, hz, hmz, hrz⟩ := hk k (by simpa using hk')
        exact ⟨z, by simpa using hz, by simpa using hmz, by simpa using hrz⟩

/-- **A run of the general closing from a `JQC O (D+1)` world delivers `SameCalleeNonMem`.** -/
theorem closeInstsGM_runP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {D : Nat}
    {shape : MachineShape} {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQC O (D + 1) w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧ MemChildren shape children ∧
      ChildrenRealA O shape children ∧ SameCalleeNonMem shape children := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨hw1, rfl⟩ := triple_runs (tripleC_synthRead O hA (D + 1)) hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨ys, hys, hlen, hk, _⟩ := mapM_loop_pinG O T hA (Nat.succ_le_succ (Nat.zero_le D))
    (fun (x : Name × InstOrigin) => match x.2.child? with
      | some md => pure md
      | none => synthesizeChild x.1) (fun _ => rfl)
    shape.instTagged [] [] children w1 w' ⟨hw1, fun p hp => by cases hp⟩ hch
  simp only [List.reverse_nil, List.nil_append] at hys
  subst hys
  have hlenI : children.length = shape.insts.length := by
    rw [hlen]; exact instTagged_length' shape
  refine ⟨children, heq, ?_, ⟨hlenI, fun k hkl => ?_⟩, fun k₁ k₂ h₁ h₂ hc n₁ n₂ => ?_⟩
  · intro k hkl md hmd
    obtain ⟨hkT, he⟩ := instTagged_getAt shape hkl
    obtain ⟨y, hky, hm, _⟩ := hk k hkT
    rw [he] at hm
    rw [hm md hmd] at hky
    exact hky
  · obtain ⟨hkT, he⟩ := instTagged_getAt shape hkl
    obtain ⟨y, hky, _, hor⟩ := hk k hkT
    rw [he] at hor
    refine ⟨y, hky, ?_⟩
    rcases hor with ho | ⟨_, hre, _⟩
    · exact Or.inl ho
    · exact Or.inr hre
  · obtain ⟨hT₁, he₁⟩ := instTagged_getAt shape h₁
    obtain ⟨hT₂, he₂⟩ := instTagged_getAt shape h₂
    obtain ⟨y₁, hy₁, -, ho₁⟩ := hk k₁ hT₁
    obtain ⟨y₂, hy₂, -, ho₂⟩ := hk k₂ hT₂
    rw [he₁] at ho₁
    rw [he₂] at ho₂
    rw [hy₁, hy₂]
    rcases ho₁ with ho₁ | ⟨-, -, hc₁⟩
    · rw [n₁] at ho₁; cases ho₁
    rcases ho₂ with ho₂ | ⟨-, -, hc₂⟩
    · rw [n₂] at ho₂; cases ho₂
    dsimp only at hc₁ hc₂
    rw [hc] at hc₁
    rw [hc₁] at hc₂
    exact congrArg some (Option.some.inj hc₂)

/-- **`CallsPureA` with the pins as hypotheses of both branches** (`CallsPureP` plus the non-memory pin in
the general conjunct). Both pins are delivered by `closeInstsM_runP` / `closeInstsGM_runP`. -/
def CallsPureGP (O : RefLawsAOps MkRefd mref cref) (declName : Name) (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (b : Bool) t d₀ t' children,
    MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
      shape.binders shape.body) (t, d₀) →
    Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' →
    ChildrenRealA O shape children →
    (shape.instFields = [] → SameCalleeChildren shape children →
      (Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1)) children
        (Sparkle.IR.Machine.closeMachine shape.layout t', d₀)).isSome = true) ∧
    (shape.instFields ≠ [] → MemChildren shape children → SameCalleeNonMem shape children →
      (Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children
        (Sparkle.IR.Machine.closeMachine shape.layout t', d₀)).isSome = true)

/-- **`MachineClosesAtA` from `LetsClose` and `CallsPureGP`** (`machineClosesAtA_of_pure_pin` with the
general branch pinned). -/
theorem machineClosesAtA_of_pure_pinG (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape}
    (hl : LetsClose mctx mref cctx cref declName shape)
    (hp : CallsPureGP O declName shape) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName shape := by
  have htr := fun (tenv : Lean.Environment) (D : Nat) =>
    Tools.ShippingChildRunAMain.htr_of_tele O hA T D tenv
  intro tenv b n w r w' hw hn hr
  obtain ⟨D, rfl⟩ : ∃ D, n = D + 1 := ⟨n - 1, by omega⟩
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := triple_runs (keeps_iff.mp (mixed_keepsAP O hA (stableA_JQC O (D + 1)) _ b declName
    shape.binders shape.body (htr tenv D))) hw run
  dsimp only at hr
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (hl (profLogIO b) w t d' w1 run)
  rw [ht'] at hr
  dsimp only at hr
  split at hr
  · have := RunsTo.pure_eq hr
    rw [this]
    exact Option.some_ne_none _
  · split at hr
    · rename_i hf
      obtain ⟨children, rfl, hreal, hsame⟩ := closeInstsM_runP O T hA hw1 hr
      have := (hp b t d' t' children run.mreturns ht' hreal).1 (List.isEmpty_iff.mp hf) hsame
      intro h
      rw [h] at this
      cases this
    · rename_i hf
      obtain ⟨children, rfl, hmem, hreal, hsame⟩ := closeInstsGM_runP O T hA hw1 hr
      have := (hp b t d' t' children run.mreturns ht' hreal).2
        (fun h => hf (List.isEmpty_iff.mpr h)) hmem hsame
      intro h
      rw [h] at this
      cases this

set_option maxHeartbeats 1000000 in
/-- **`CallsPureGP` for memory (and mixed gate + memory) children**: CM's `callsPureA_of_memKids` with
`hdistOrd` DROPPED (the pin is delivered by `closeInstsGM_runP`). -/
theorem callsPureGP_of_memKids' (O : RefLawsAOps MkRefd mref cref) {declName : Name}
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
    CallsPureGP O declName d.shape := by
  intro tenv b t d₀ t' children run hcl hreal
  refine ⟨fun h _ => absurd h hfne, fun _ hmc hsameNM => ?_⟩
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
      have hn : ∀ k, memKey (originAt d.shape k) = none →
          (d.shape.instOrigins.getD k .ord).child? = none := by
        intro k hk
        show (originAt d.shape k).child? = none
        cases hok : (originAt d.shape k) with
        | ord => rfl
        | field _ => rfl
        | mem cb aw dw => rw [hok] at hk; cases hk
      exact hsameNM i j hi hj hcc (hn i hki) (hn j (hkey ▸ hki))
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

/-- **`MachineClosesAtA` for memory (and mixed) parents**, `hdistOrd` DROPPED (premises `O`, `hA`, `T`, data). -/
theorem machineClosesAtA_of_memKids' (O : RefLawsAOps MkRefd mref cref)
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
  machineClosesAtA_of_pure_pinG O T hA
    (letsClose_of_data d ok hbody halias mctx mref cctx cref)
    (callsPureGP_of_memKids' O d ok hbody hC hslots hdomB hfne nameK nk outsK namesK hkid hargsN
      hfieldOut hfieldsNd hsep hparent hfresh hparentD hdisjD)

end Tools.ShippingCallsMemPinned

#print axioms Tools.ShippingCallsMemPinned.closeInstsGM_runP
#print axioms Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids'
