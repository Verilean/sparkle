import Tests.Compiler.CDefTest
-- C4 G-HCALLS (issue sparkle-gen-c4-hcalls): `HCallsOf` of every wrapper of a `MemSharedLeafParent`, generically.
-- SCOPE: M-shape class only (AMENDMENT 3/4/5).  Premises of the generic theorems: only the contract binders (P, hco, O, T).
-- `WCallOut` (below) is the proposed GEN-SHAPE class field of AMENDMENT 5: the per-call OUTPUT fact about the generated `ext`/`extB`/`stateLoop`
-- and `P.leaf.src`, filled per member by the uniform unfolding (`P_M_wCallOut`); the decoding is a GENERIC lemma from `wArgsIn`.
-- No sorry, no axiom, no native_decide.
set_option autoImplicit false
set_option Elab.async false
namespace Tests.Compiler.C4HCalls
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6 Tools.ShippingSrm4Callee Tools.ShippingSrm4Run
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Tools.ShippingUnifiedSource (Term SType eval)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMuxLoweringSoundness (encodeBool)
open Tools.ShippingMachineChild (boolsOf bitsOf portIdx decB decV)
open Tools.ShippingMachineCallsLinkedT (valsOf)
open Tools.ShippingSeqParentLemmas (HCallsOf)
open Tools.ShippingMachineCausal (letObsB)
open Tests.Compiler.CDef

variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-! ## 1. `WCallOut`: the per-call OUTPUT fact (proposed AMENDMENT 5 field, GEN-SHAPE) -/

/-- For every wrapper `w` and call `k`, on the ORIGINAL input families `bools`, `bits`: the leaf has an output field `k'` named like the call's
field, and (for any families `bools'`, `bits'` that agree with `bools`, `bits` at the leaf's ports) the leaf source's `k'`-th output `f` is, at every
time, the value of the generated `w.extBS` / `w.extS` at the call-output position `nDecl + k`.  No decoding, no `valsOf`, no `CallFactF`. -/
def WCallOut (P : MemSharedLeafParent) : Prop :=
  ∀ w ∈ P.wrappers, ∀ (k : Nat) (_ : k < w.d.shape.insts.length) (i : DomainConfig) (bools : Nat → Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)),
    ∃ (k' : Nat) (o : OutField), P.leaf.d.shape.layout.outs[k']? = some o ∧ o.name = w.d.shape.instFields.getD k "" ∧
      ∀ (bools' : Nat → Signal i Bool) (bits' : (j : Nat) → (n : Nat) → Signal i (BitVec n)),
        (∀ p, (P.leaf.d.bsIn.take P.nDecl)[p]?.map (·.2) = some MixedGateBinder.bool → bools' p = bools p) →
        (∀ p n, (P.leaf.d.bsIn.take P.nDecl)[p]?.map (·.2) = some (MixedGateBinder.bits n) → bits' p n = bits p n) →
        ∃ f : Nat → Nat, (P.leaf.src i bools' bits')[k']? = some f ∧
          ∀ τ, posEnc (fun p => (w.extBS i bools bits p).val τ) (fun p n => (w.extS i bools bits p n).val τ)
            (P.nDecl + k) (((w.d.bsIn.drop P.nDecl)[k]?.map (·.2)).getD .domain) = f τ

/-! ## 2. generic decoding (from `wArgsIn`) -/

theorem argInOk_bool {d : MachineData} {bs : List (Name × MixedGateBinder)} {args : List Nat} {p : Nat}
    (h : argInOk d bs args p = true) {b : Name × MixedGateBinder} (hb : bs[p]? = some b) (hbb : b.2 = .bool) :
    ∃ a j, args[portIdx bs p]? = some a ∧ d.ls[a]? = some (⟨.bool, .boolInput j⟩ : Σ s : SType, Term s) ∧ d.bpos j = p := by
  obtain ⟨nm, bb⟩ := b
  simp only at hbb
  subst hbb
  unfold argInOk at h
  rw [hb] at h
  simp only at h
  cases ha : args[portIdx bs p]? with
  | none => rw [ha] at h; simp at h
  | some a =>
    rw [ha] at h
    simp only at h
    cases hl : d.ls[a]? with
    | none => rw [hl] at h; simp at h
    | some l =>
      rw [hl] at h
      obtain ⟨s, t⟩ := l
      cases t with
      | boolInput j => exact ⟨a, j, rfl, hl, by simpa using h⟩
      | _ => simp at h

theorem argInOk_bits {d : MachineData} {bs : List (Name × MixedGateBinder)} {args : List Nat} {p n : Nat}
    (h : argInOk d bs args p = true) {b : Name × MixedGateBinder} (hb : bs[p]? = some b) (hbb : b.2 = .bits n) :
    ∃ a j, args[portIdx bs p]? = some a ∧ d.ls[a]? = some (⟨.bits n, .bitsInput n j⟩ : Σ s : SType, Term s) ∧ d.vpos j = p := by
  obtain ⟨nm, bb⟩ := b
  simp only at hbb
  subst hbb
  unfold argInOk at h
  rw [hb] at h
  simp only at h
  cases ha : args[portIdx bs p]? with
  | none => rw [ha] at h; simp at h
  | some a =>
    rw [ha] at h
    simp only at h
    cases hl : d.ls[a]? with
    | none => rw [hl] at h; simp at h
    | some l =>
      rw [hl] at h
      obtain ⟨s, t⟩ := l
      cases t with
      | bitsInput m j =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨hm, hj⟩ := h
        subst hm
        exact ⟨a, j, rfl, hl, hj⟩
      | _ => simp at h

theorem letVal_lt (bpos vpos : Nat → Nat) : ∀ (ls : List (Σ s : SType, Term s)) (p : Nat) (V : TVal) (q : Nat), q < p →
    (letVal bpos vpos ls p V).b q = V.b q ∧ ∀ n, (letVal bpos vpos ls p V).v q n = V.v q n
  | [], _, _, _, _ => ⟨rfl, fun _ => rfl⟩
  | l :: ls, p, V, q, h => by
    obtain ⟨hb, hv⟩ := letVal_lt bpos vpos ls (p + 1) (V.set p l.1 (eval (fun j => V.b (bpos j)) (fun j w => V.v (vpos j) w) l.2)) q (by omega)
    exact ⟨hb.trans (set_b_ne (by omega)), fun n => (hv n).trans (set_v_ne (by omega) n)⟩

theorem typedVal_in {D : DomainConfig} (kIn : Nat) (bpos vpos : Nat → Nat) (ss : List SType) (ls : List (Σ s : SType, Term s))
    (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys ss)) (q : Nat)
    (hq : q < kIn) :
    (typedVal kIn bpos vpos ss ls bools bits t x).b q = (bools q).val t ∧
      ∀ n, (typedVal kIn bpos vpos ss ls bools bits t x).v q n = (bits q n).val t := by
  unfold typedVal
  obtain ⟨h1, h2⟩ := letVal_lt bpos vpos ls (kIn + ss.length) _ q (by omega)
  obtain ⟨h3, h4⟩ := slotVal_lt kIn ss x 0 ⟨fun p => (bools p).val t, fun p w => (bits p w).val t⟩ q (by omega)
  exact ⟨h1.trans h3, fun n => (h2 n).trans (h4 n)⟩

/-- the typed valuation of the generated machine of `w` at time `τ` -/
noncomputable abbrev tvOf (w : GenPkg DomainConfig (fun i => i)) (i : DomainConfig) (bools : Nat → Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (τ : Nat) : TVal :=
  typedVal w.d.nIn w.d.bpos w.d.vpos w.d.ss w.d.ls (w.extBS i bools bits) (w.extS i bools bits) τ
    ((@stateLoop _ _ _ w.inh w.inits (w.body i bools bits)).val τ)

theorem nDecl_le_nIn (P : MemSharedLeafParent) {w : GenPkg DomainConfig (fun i => i)} (hw : w ∈ P.wrappers) : P.nDecl ≤ w.d.nIn := by
  have h1 := (P.wMem w hw).hkD
  have h2 : w.d.bsIn.length ≤ w.d.nIn := by
    unfold MachineData.bsIn; simp only [List.length_take]; exact Nat.min_le_left _ _
  omega

theorem lsrc_bool_val (P : MemSharedLeafParent) {w : GenPkg DomainConfig (fun i => i)} (hw : w ∈ P.wrappers) (i : DomainConfig)
    (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) {a j : Nat}
    (hl : w.d.ls[a]? = some (⟨.bool, .boolInput j⟩ : Σ s : SType, Term s)) (hj : w.d.bpos j < P.nDecl) (τ : Nat) :
    ((w.lsrc i bools bits)[a]?.map (· τ)).getD 0 = encodeBool ((bools (w.d.bpos j)).val τ) := by
  have hin : w.d.bpos j < w.d.nIn := Nat.lt_of_lt_of_le hj (nDecl_le_nIn P hw)
  have hE := P.wHextB w hw i bools bits (w.d.bpos j) hj
  have hT := (typedVal_in (D := i) w.d.nIn w.d.bpos w.d.vpos w.d.ss w.d.ls (w.extBS i bools bits) (w.extS i bools bits) τ
    ((@stateLoop _ _ _ w.inh w.inits (w.body i bools bits)).val τ) (w.d.bpos j) hin).1
  have key : ((w.lsrc i bools bits)[a]?.map (· τ)).getD 0 = encodeBool ((tvOf w i bools bits τ).b (w.d.bpos j)) := by
    simp only [GenPkg.lsrc, Tools.ShippingMachineCausal.letObsB, List.getElem?_map, hl, Option.map_some, Option.getD_some] <;> rfl
  rw [key]
  change encodeBool ((typedVal w.d.nIn w.d.bpos w.d.vpos w.d.ss w.d.ls (w.extBS i bools bits) (w.extS i bools bits) τ
    ((@stateLoop _ _ _ w.inh w.inits (w.body i bools bits)).val τ)).b (w.d.bpos j)) = _
  rw [hT, hE]

theorem lsrc_bits_val (P : MemSharedLeafParent) {w : GenPkg DomainConfig (fun i => i)} (hw : w ∈ P.wrappers) (i : DomainConfig)
    (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) {a j n : Nat}
    (hl : w.d.ls[a]? = some (⟨.bits n, .bitsInput n j⟩ : Σ s : SType, Term s)) (hj : w.d.vpos j < P.nDecl) (τ : Nat) :
    ((w.lsrc i bools bits)[a]?.map (· τ)).getD 0 = ((bits (w.d.vpos j) n).val τ).toNat := by
  have hin : w.d.vpos j < w.d.nIn := Nat.lt_of_lt_of_le hj (nDecl_le_nIn P hw)
  have hE := P.wHext w hw i bools bits (w.d.vpos j) n hj
  have hT := (typedVal_in (D := i) w.d.nIn w.d.bpos w.d.vpos w.d.ss w.d.ls (w.extBS i bools bits) (w.extS i bools bits) τ
    ((@stateLoop _ _ _ w.inh w.inits (w.body i bools bits)).val τ) (w.d.vpos j) hin).2 n
  have key : ((w.lsrc i bools bits)[a]?.map (· τ)).getD 0 = ((tvOf w i bools bits τ).v (w.d.vpos j) n).toNat := by
    simp only [GenPkg.lsrc, Tools.ShippingMachineCausal.letObsB, List.getElem?_map, hl, Option.map_some, Option.getD_some] <;> rfl
  rw [key]
  change ((typedVal w.d.nIn w.d.bpos w.d.vpos w.d.ss w.d.ls (w.extBS i bools bits) (w.extS i bools bits) τ
    ((@stateLoop _ _ _ w.inh w.inits (w.body i bools bits)).val τ)).v (w.d.vpos j) n).toNat = _
  rw [hT, hE]

theorem signal_ext {D : DomainConfig} {α : Type} (s t : Signal D α) (h : ∀ τ, s.val τ = t.val τ) : s = t := by
  cases s; cases t; exact congrArg Signal.mk (funext h)

/-- **Generic decoding of a Bool port**: the decoded Bool at a Bool port of the leaf is the wrapper's input family. -/
theorem decode_bool (P : MemSharedLeafParent) {w : GenPkg DomainConfig (fun i => i)} (hw : w ∈ P.wrappers) {k : Nat}
    (hk : k < w.d.shape.insts.length) (i : DomainConfig) (bools : Nat → Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) {p : Nat}
    (hp : (P.leaf.d.bsIn.take P.nDecl)[p]?.map (·.2) = some MixedGateBinder.bool) :
    boolsOf (D := i) (P.leaf.d.bsIn.take P.nDecl) (valsOf (w.lsrc i bools bits) (w.d.shape.insts[k]).2.1) p = bools p := by
  obtain ⟨b, hb, hbb⟩ : ∃ b, (P.leaf.d.bsIn.take P.nDecl)[p]? = some b ∧ b.2 = .bool := by
    cases h : (P.leaf.d.bsIn.take P.nDecl)[p]? with
    | none => rw [h] at hp; simp at hp
    | some b => rw [h] at hp; simp at hp; exact ⟨b, rfl, hp⟩
  have hlen := (List.getElem?_eq_some_iff.mp hb).1
  have hlt : p < P.nDecl := by simp [List.length_take] at hlen; omega
  obtain ⟨a, j, harg, hl, hj⟩ := argInOk_bool (P.wArgsIn w hw k hk p hlen) hb hbb
  apply signal_ext; intro τ
  show (((valsOf (w.lsrc i bools bits) (w.d.shape.insts[k]).2.1) τ).getD (portIdx (P.leaf.d.bsIn.take P.nDecl) p) 0 != 0) = _
  have h1 : ((valsOf (w.lsrc i bools bits) (w.d.shape.insts[k]).2.1) τ).getD (portIdx (P.leaf.d.bsIn.take P.nDecl) p) 0 =
      ((w.lsrc i bools bits)[a]?.map (· τ)).getD 0 := by
    simp [valsOf, List.getD_eq_getElem?_getD, List.getElem?_map, harg]
  rw [h1, lsrc_bool_val P hw i bools bits hl (hj ▸ hlt) τ, hj]
  cases (bools p).val τ <;> simp [encodeBool]

/-- **Generic decoding of a BitVec port**. -/
theorem decode_bits (P : MemSharedLeafParent) {w : GenPkg DomainConfig (fun i => i)} (hw : w ∈ P.wrappers) {k : Nat}
    (hk : k < w.d.shape.insts.length) (i : DomainConfig) (bools : Nat → Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) {p n : Nat}
    (hp : (P.leaf.d.bsIn.take P.nDecl)[p]?.map (·.2) = some (MixedGateBinder.bits n)) :
    bitsOf (D := i) (P.leaf.d.bsIn.take P.nDecl) (valsOf (w.lsrc i bools bits) (w.d.shape.insts[k]).2.1) p n = bits p n := by
  obtain ⟨b, hb, hbb⟩ : ∃ b, (P.leaf.d.bsIn.take P.nDecl)[p]? = some b ∧ b.2 = .bits n := by
    cases h : (P.leaf.d.bsIn.take P.nDecl)[p]? with
    | none => rw [h] at hp; simp at hp
    | some b => rw [h] at hp; simp at hp; exact ⟨b, rfl, hp⟩
  have hlen := (List.getElem?_eq_some_iff.mp hb).1
  have hlt : p < P.nDecl := by simp [List.length_take] at hlen; omega
  obtain ⟨a, j, harg, hl, hj⟩ := argInOk_bits (P.wArgsIn w hw k hk p hlen) hb hbb
  apply signal_ext; intro τ
  show BitVec.ofNat n (((valsOf (w.lsrc i bools bits) (w.d.shape.insts[k]).2.1) τ).getD (portIdx (P.leaf.d.bsIn.take P.nDecl) p) 0) = _
  have h1 : ((valsOf (w.lsrc i bools bits) (w.d.shape.insts[k]).2.1) τ).getD (portIdx (P.leaf.d.bsIn.take P.nDecl) p) 0 =
      ((w.lsrc i bools bits)[a]?.map (· τ)).getD 0 := by
    simp [valsOf, List.getD_eq_getElem?_getD, List.getElem?_map, harg]
  rw [h1, lsrc_bits_val P hw i bools bits hl (hj ▸ hlt) τ, hj]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (bits p n |>.val τ).isLt

/-! ## 3. `CallFactF` of every wrapper -/

theorem callFactF_of_class (P : MemSharedLeafParent) (hco : WCallOut P) :
    ∀ w ∈ P.wrappers, Tools.ShippingQuadCalls.CallFactF w.d P.nDecl w.lsrc w.extS w.extBS
      (memLeafOutsC P.leaf.decl P.leaf.d) (memLeafSrcC P.leaf.decl P.leaf.d P.nDecl P.leaf.src) := by
  intro w hw i bools bits k hk
  have hkid := (P.wKids w hw k hk).1
  obtain ⟨k', o, ho, hname, hrest⟩ := hco w hw k hk i bools bits
  obtain ⟨f, hf, hτ⟩ := hrest (boolsOf (D := i) (P.leaf.d.bsIn.take P.nDecl) (valsOf (w.lsrc i bools bits) (w.d.shape.insts[k]).2.1))
    (bitsOf (D := i) (P.leaf.d.bsIn.take P.nDecl) (valsOf (w.lsrc i bools bits) (w.d.shape.insts[k]).2.1))
    (fun p hp => decode_bool P hw hk i bools bits hp) (fun p n hp => decode_bits P hw hk i bools bits hp)
  refine ⟨k', o, f, ?_, hname, ?_, hτ⟩
  · rw [hkid]; unfold memLeafOutsC; rw [if_pos rfl]; exact ho
  · rw [hkid]; unfold memLeafSrcC; rw [if_pos rfl]; exact hf

/-! ## 4. G-HCALLS -/

theorem hcalls_of_class (P : MemSharedLeafParent) (hco : WCallOut P) (O : RefLawsAOps MkRefd mref cref)
    (T : RefLawsATele O.quiet mref cref) :
    ∀ w ∈ P.wrappers, ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 w.d design m (dom := fun i : DomainConfig => i) w.lsrc w.extS w.extBS P.nDecl
        (memLeafBsC P.leaf.decl P.leaf.d P.nDecl) (memLeafOutsC P.leaf.decl P.leaf.d)
        (memLeafSrcC P.leaf.decl P.leaf.d P.nDecl P.leaf.src) (memLeafPC O P.leaf.decl P.leaf.d design) := by
  intro w hw m design
  letI := w.inh
  letI := P.leaf.inh
  exact memLeafCallee_hcalls (srcG := P.leaf.src) O (P.wMem w hw) (P.wKids w hw) (P.wArgsN w hw) (P.wWid w hw)
    (fun i design mc h => memCallee_seqChildRunN O T P.leafMem P.leafOutOk P.leaf.gen P.leafMemCalls P.leafHextB P.leafHext
      (fun _ _ _ _ _ => True) i 0 h)
    (callFactF_of_class P hco w hw) m design

/-! ## 5. the member `P_M`: `WCallOut` by the uniform unfolding (both calls of `wrapM` and of `wrapM3`) -/
section Member
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.Srm9ComposedTest Tests.Compiler.SharedLeafMemKidIfaceTest

/-- the member's WCallOut is its AMENDMENT 6 class field (proved in CDefTest by the uniform unfolding) -/
theorem P_M_wCallOut (hgrp : TmGrp) : WCallOut (P_M hgrp) := (P_M hgrp).wCallOut

/-- **G-HCALLS from the class alone** (AMENDMENT 6: `wCallOut` is a class field) -/
theorem hcalls_of_classF (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) :
    ∀ w ∈ P.wrappers, ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 w.d design m (dom := fun i : DomainConfig => i) w.lsrc w.extS w.extBS P.nDecl
        (memLeafBsC P.leaf.decl P.leaf.d P.nDecl) (memLeafOutsC P.leaf.decl P.leaf.d)
        (memLeafSrcC P.leaf.decl P.leaf.d P.nDecl P.leaf.src) (memLeafPC O P.leaf.decl P.leaf.d design) :=
  hcalls_of_class P P.wCallOut O T

/-- `TmH1` / `TmH2` (Srm9ComposedTest) recovered from the generic theorem -/
theorem TmH1_of_class (hgrp : TmGrp) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) : TmH1 O :=
  fun m design => hcalls_of_class (P_M hgrp) (P_M_wCallOut hgrp) O T ((P_M hgrp).wrappers[0]'(by simp [P_M])) (List.getElem_mem _) m design

theorem TmH2_of_class (hgrp : TmGrp) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) : TmH2 O :=
  fun m design => hcalls_of_class (P_M hgrp) (P_M_wCallOut hgrp) O T ((P_M hgrp).wrappers[1]'(by simp [P_M])) (List.getElem_mem _) m design

end Member

/-! ## 6. audit -/
open Lean Meta Elab Term in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ci ← getConstInfo ``hcalls_of_class
  let expected ← elabTerm (← `(∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      (P : MemSharedLeafParent) (hco : WCallOut P) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref),
      ∀ w ∈ P.wrappers, ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
        HCallsOf 1 w.d design m (dom := fun i : DomainConfig => i) w.lsrc w.extS w.extBS P.nDecl
          (memLeafBsC P.leaf.decl P.leaf.d P.nDecl) (memLeafOutsC P.leaf.decl P.leaf.d)
          (memLeafSrcC P.leaf.decl P.leaf.d P.nDecl P.leaf.src) (memLeafPC O P.leaf.decl P.leaf.d design))) none
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq ci.type (← instantiateMVars expected) do throwError "C4HCALLS AUDIT FAILED: hcalls_of_class type differs from the stated theorem"
  forallTelescope ci.type fun xs _ => do
    let mut s := #[]
    for x in xs do s := s.push s!"{← x.fvarId!.getUserName}:{repr (← x.fvarId!.getBinderInfo)}"
    unless xs.size == 10 do throwError "C4HCALLS AUDIT FAILED: {xs.size} binders, expected 10 (mref cref P hco O T w hw m design)"
    logInfo m!"C4HCALLS|binders: {s}"
  -- WCallOut and callFactF_of_class: stated types
  let c2 ← getConstInfo ``callFactF_of_class
  let expected2 ← elabTerm (← `(∀ (P : MemSharedLeafParent) (_ : WCallOut P), ∀ w ∈ P.wrappers,
      Tools.ShippingQuadCalls.CallFactF w.d P.nDecl w.lsrc w.extS w.extBS (memLeafOutsC P.leaf.decl P.leaf.d)
        (memLeafSrcC P.leaf.decl P.leaf.d P.nDecl P.leaf.src))) none
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq c2.type (← instantiateMVars expected2) do throwError "C4HCALLS AUDIT FAILED: callFactF_of_class type differs"
  for n in [``callFactF_of_class, ``hcalls_of_class, ``decode_bool, ``decode_bits, ``P_M_wCallOut, ``TmH1_of_class, ``TmH2_of_class] do
    let axs ← Lean.collectAxioms n
    for x in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains x do throwError "C4HCALLS AUDIT FAILED: {x} in {n}"
    logInfo m!"C4HCALLS|axioms {n}: {axs}"

/-! closure audit: the generic theorem reaches only the class file and the generic helpers of this file -/
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut work : List Name := [``hcalls_of_class]
  let mut reached : Array Name := #[]
  while !work.isEmpty do
    let n := work.head!
    work := work.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "C4HCALLS CLOSURE FAILED: {n} not found"
    let body? : Option Lean.Expr := match ci with
      | .thmInfo t => some t.value
      | .defnInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    let cs := ci.type.getUsedConstants ++ (body?.map Lean.Expr.getUsedConstants).getD #[]
    for c in cs do
      if (c.toString.splitOn "Tests.").length > 1 && !seen.contains c then
        reached := reached.push c
        work := c :: work
  logInfo m!"C4HCALLS|closure reached: {reached.toList}"
  for c in reached do
    unless (c.toString.splitOn "Tests.Compiler.CDef.").length > 1 || (c.toString.splitOn "Tests.Compiler.C4HCalls.").length > 1 do
      throwError "C4HCALLS CLOSURE FAILED: hcalls_of_class reaches {c} (outside the class definition and this file)"
  for c in reached do
    for comp in c.components.map (·.toString) do
      if ["P_M", "P_Q", "wrapM", "wrapM3", "leafM", "leafP", "wrapP", "wrapQ"].contains comp
          || comp.startsWith "topshare" || comp.startsWith "wrapM" || comp.startsWith "P_M" then
        throwError "C4HCALLS CLOSURE FAILED: hcalls_of_class reaches {c} (instance component {comp})"
  let helpers : List Name := [``callFactF_of_class, ``decode_bool, ``decode_bits, ``argInOk_bool, ``argInOk_bits, ``letVal_lt, ``typedVal_in,
    ``tvOf, ``nDecl_le_nIn, ``lsrc_bool_val, ``lsrc_bits_val, ``signal_ext, ``WCallOut]
  for c in reached do
    if (c.toString.splitOn "Tests.Compiler.C4HCalls.").length > 1 then
      unless helpers.any (fun h => (c.toString.splitOn h.toString).length > 1) do
        throwError "C4HCALLS CLOSURE FAILED: unexpected own constant {c} in the closure"
  for h in [``callFactF_of_class, ``decode_bool, ``decode_bits, ``WCallOut] do
    unless reached.contains h do throwError "C4HCALLS CLOSURE FAILED: expected helper {h} not reached"
  for h in [``P_M_wCallOut, ``wrapM_callOut, ``wrapM3_callOut, ``TmH1_of_class, ``TmH2_of_class] do
    if reached.contains h then throwError "C4HCALLS CLOSURE FAILED: member constant {h} reached"
  let cdef := reached.filter (fun c => (c.toString.splitOn "Tests.Compiler.CDef.").length > 1)
  logInfo m!"C4HCALLS|closure ok: {reached.size} Tests constants reached; class constants {cdef.toList}; no member value, no instance file"

/-! review request: audit the FINAL no-premise root `hcalls_of_classF` (type, binders, closure) and the member corollaries TmH1 / TmH2 -/
open Lean Meta Elab Term in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ci ← getConstInfo ``hcalls_of_classF
  let expected ← elabTerm (← `(∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
      (P : MemSharedLeafParent) (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref),
      ∀ w ∈ P.wrappers, ∀ (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
        HCallsOf 1 w.d design m (dom := fun i : DomainConfig => i) w.lsrc w.extS w.extBS P.nDecl
          (memLeafBsC P.leaf.decl P.leaf.d P.nDecl) (memLeafOutsC P.leaf.decl P.leaf.d)
          (memLeafSrcC P.leaf.decl P.leaf.d P.nDecl P.leaf.src) (memLeafPC O P.leaf.decl P.leaf.d design))) none
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq ci.type (← instantiateMVars expected) do throwError "C4HCALLS AUDIT FAILED: hcalls_of_classF type differs from the stated theorem"
  forallTelescope ci.type fun xs _ => do
    let mut s := #[]
    for x in xs do
      s := s.push s!"{← x.fvarId!.getUserName}:{repr (← x.fvarId!.getBinderInfo)}"
      -- no WCallOut-typed binder: the field is read from P
      if (← inferType x).isAppOf ``WCallOut then throwError "C4HCALLS AUDIT FAILED: hcalls_of_classF takes a WCallOut binder"
    unless xs.size == 9 do throwError "C4HCALLS AUDIT FAILED: hcalls_of_classF has {xs.size} binders, expected 9 (mref cref P O T w hw m design)"
    logInfo m!"C4HCALLS|F binders: {s}"
  -- member corollaries: exactly TmH1 O / TmH2 O of Srm9ComposedTest, with the one class assumption TmGrp
  for (n, t) in [(``TmH1_of_class, ``Tests.Compiler.Srm9ComposedTest.TmH1), (``TmH2_of_class, ``Tests.Compiler.Srm9ComposedTest.TmH2)] do
    let c ← getConstInfo n
    forallTelescope c.type fun xs body => do
      unless xs.size == 5 do throwError "C4HCALLS AUDIT FAILED: {n} has {xs.size} binders, expected 5 (mref cref hgrp O T)"
      unless ← isDefEq (← inferType xs[2]!) (mkConst ``Tests.Compiler.Srm9ComposedTest.TmGrp) do
        throwError "C4HCALLS AUDIT FAILED: {n}'s third binder is not TmGrp"
      unless ← isDefEq body (mkAppN (mkConst t) #[xs[0]!, xs[1]!, xs[3]!]) do
        throwError "C4HCALLS AUDIT FAILED: {n} does not conclude {t} O"
      logInfo m!"C4HCALLS|corollary {n} : TmGrp → {t} O (isDefEq)"

open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut work : List Name := [``hcalls_of_classF]
  let mut reached : Array Name := #[]
  while !work.isEmpty do
    let n := work.head!
    work := work.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "C4HCALLS CLOSURE(F) FAILED: {n} not found"
    let body? : Option Lean.Expr := match ci with
      | .thmInfo t => some t.value
      | .defnInfo v => some v.value
      | .opaqueInfo v => some v.value
      | _ => none
    let cs := ci.type.getUsedConstants ++ (body?.map Lean.Expr.getUsedConstants).getD #[]
    for c in cs do
      if (c.toString.splitOn "Tests.").length > 1 && !seen.contains c then
        reached := reached.push c
        work := c :: work
  for c in reached do
    unless (c.toString.splitOn "Tests.Compiler.CDef.").length > 1 || (c.toString.splitOn "Tests.Compiler.C4HCalls.").length > 1 do
      throwError "C4HCALLS CLOSURE(F) FAILED: hcalls_of_classF reaches {c} (outside the class definition and this file)"
    for comp in c.components.map (·.toString) do
      if ["P_M", "P_Q", "wrapM", "wrapM3", "leafM", "leafP", "wrapP", "wrapQ", "TmGrp", "TmH1", "TmH2"].contains comp
          || comp.startsWith "topshare" || comp.startsWith "wrapM" || comp.startsWith "P_M" then
        throwError "C4HCALLS CLOSURE(F) FAILED: hcalls_of_classF reaches {c} (instance component {comp})"
  let helpers : List Name := [``hcalls_of_class, ``callFactF_of_class, ``decode_bool, ``decode_bits, ``argInOk_bool, ``argInOk_bits,
    ``letVal_lt, ``typedVal_in, ``tvOf, ``nDecl_le_nIn, ``lsrc_bool_val, ``lsrc_bits_val, ``signal_ext, ``WCallOut]
  for c in reached do
    if (c.toString.splitOn "Tests.Compiler.C4HCalls.").length > 1 then
      unless helpers.any (fun h => (c.toString.splitOn h.toString).length > 1) do
        throwError "C4HCALLS CLOSURE(F) FAILED: unexpected own constant {c} in the closure"
  for h in [``hcalls_of_class, ``callFactF_of_class, ``decode_bool, ``decode_bits, ``MemSharedLeafParent.wCallOut] do
    unless reached.contains h do throwError "C4HCALLS CLOSURE(F) FAILED: expected constant {h} not reached"
  for h in [``P_M_wCallOut, ``TmH1_of_class, ``TmH2_of_class, ``Tests.Compiler.CDef.wrapM_callOut, ``Tests.Compiler.CDef.wrapM3_callOut] do
    if reached.contains h then throwError "C4HCALLS CLOSURE(F) FAILED: member constant {h} reached"
  logInfo m!"C4HCALLS|closure(F) ok: {reached.size} Tests constants reached from hcalls_of_classF (reads the class field wCallOut); no member value, no instance file"

#print axioms callFactF_of_class
#print axioms hcalls_of_class
#print axioms hcalls_of_classF
#print axioms P_M_wCallOut
#print axioms TmH1_of_class
#print axioms TmH2_of_class

end Tests.Compiler.C4HCalls
