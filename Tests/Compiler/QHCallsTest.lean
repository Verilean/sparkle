import Tests.Compiler.QDefTest
-- C5 Q-DECODE / Q-HCALLS (issue sparkle-gen-c5-hcalls): `HCallsOf` of every wrapper of a `QSharedLeafParent`, generically.
-- Route: `Tools.ShippingSrm4Mixed.ordCallee_hcalls` (the shape of `wrapQ_hcalls`) for BOTH wrappers: `wrapP` has no memory call, so its `memCalls`
-- premise is vacuous; the ordinary-call output fact `CallFactFO` is derived from the class field `callOut` and the generic port-map decoding.
-- Premises of the generic theorems: only the class `P`, the wrapper `w`, `hw`, `m`, `design` (no `O`, `T`: the route does not read them).
-- No sorry, no axiom, no native_decide.
set_option autoImplicit false
set_option Elab.async false
namespace Tests.Compiler.QHCalls
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Tools.ShippingSrm3Callee Tools.ShippingSrm4Kid Tools.ShippingSrm4Core6 Tools.ShippingSrm4Callee Tools.ShippingSrm4Run
open Tools.ShippingSrm4Mixed
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Tools.ShippingUnifiedSource (Term SType eval)
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMuxLoweringSoundness (encodeBool)
open Tools.ShippingMachineChild (boolsOf bitsOf portIdx decB decV)
open Tools.ShippingMachineCallsLinkedT (valsOf)
open Tools.ShippingSeqParentLemmas (HCallsOf)
open Tools.ShippingMachineCausal (letObsB)
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingQuadComposed (leafBsC leafOutsC leafSrcC leafPC)
open Tests.Compiler.CDef
open Tests.Compiler.QDef
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tests.Compiler.SharedLeafMemKidIfaceTest

variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-! ## 1. generic decoding with the port map `argPos` -/

theorem argInOkQ_bool {d : MachineData} {bs : List (Name × MixedGateBinder)} {args : List Nat} {pos : Nat → Nat} {p : Nat}
    (h : argInOkQ d bs args pos p = true) {b : Name × MixedGateBinder} (hb : bs[p]? = some b) (hbb : b.2 = .bool) :
    ∃ a j, args[portIdx bs p]? = some a ∧ d.ls[a]? = some (⟨.bool, .boolInput j⟩ : Σ s : SType, Term s) ∧ d.bpos j = pos p := by
  obtain ⟨nm, bb⟩ := b
  simp only at hbb
  subst hbb
  unfold argInOkQ at h
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

theorem argInOkQ_bits {d : MachineData} {bs : List (Name × MixedGateBinder)} {args : List Nat} {pos : Nat → Nat} {p n : Nat}
    (h : argInOkQ d bs args pos p = true) {b : Name × MixedGateBinder} (hb : bs[p]? = some b) (hbb : b.2 = .bits n) :
    ∃ a j, args[portIdx bs p]? = some a ∧ d.ls[a]? = some (⟨.bits n, .bitsInput n j⟩ : Σ s : SType, Term s) ∧ d.vpos j = pos p := by
  obtain ⟨nm, bb⟩ := b
  simp only at hbb
  subst hbb
  unfold argInOkQ at h
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

/-- the typed valuation of the generated machine of `g` at time `τ` -/
noncomputable abbrev tvOf (g : GenPkg DomainConfig (fun i => i)) (i : DomainConfig) (bools : Nat → Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (τ : Nat) : TVal :=
  typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (g.extBS i bools bits) (g.extS i bools bits) τ
    ((@stateLoop _ _ _ g.inh g.inits (g.body i bools bits)).val τ)

theorem arity_le_nIn (g : GenPkg DomainConfig (fun i => i)) {a : Nat} (hkD : a ≤ g.d.bsIn.length) : a ≤ g.d.nIn := by
  have h2 : g.d.bsIn.length ≤ g.d.nIn := by
    unfold MachineData.bsIn; simp only [List.length_take]; exact Nat.min_le_left _ _
  omega

theorem lsrc_bool_valQ (g : GenPkg DomainConfig (fun i => i)) {a0 : Nat} (hkD : a0 ≤ g.d.bsIn.length)
    (hextB : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j : Nat),
      j < a0 → g.extBS i bools bits j = bools j)
    (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) {a j : Nat}
    (hl : g.d.ls[a]? = some (⟨.bool, .boolInput j⟩ : Σ s : SType, Term s)) (hj : g.d.bpos j < a0) (τ : Nat) :
    ((g.lsrc i bools bits)[a]?.map (· τ)).getD 0 = encodeBool ((bools (g.d.bpos j)).val τ) := by
  have hin : g.d.bpos j < g.d.nIn := Nat.lt_of_lt_of_le hj (arity_le_nIn g hkD)
  have hE := hextB i bools bits (g.d.bpos j) hj
  have hT := (typedVal_in (D := i) g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (g.extBS i bools bits) (g.extS i bools bits) τ
    ((@stateLoop _ _ _ g.inh g.inits (g.body i bools bits)).val τ) (g.d.bpos j) hin).1
  have key : ((g.lsrc i bools bits)[a]?.map (· τ)).getD 0 = encodeBool ((tvOf g i bools bits τ).b (g.d.bpos j)) := by
    simp only [GenPkg.lsrc, Tools.ShippingMachineCausal.letObsB, List.getElem?_map, hl, Option.map_some, Option.getD_some] <;> rfl
  rw [key]
  change encodeBool ((typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (g.extBS i bools bits) (g.extS i bools bits) τ
    ((@stateLoop _ _ _ g.inh g.inits (g.body i bools bits)).val τ)).b (g.d.bpos j)) = _
  rw [hT, hE]

theorem lsrc_bits_valQ (g : GenPkg DomainConfig (fun i => i)) {a0 : Nat} (hkD : a0 ≤ g.d.bsIn.length)
    (hext : ∀ (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) (j n' : Nat),
      j < a0 → g.extS i bools bits j n' = bits j n')
    (i : DomainConfig) (bools : Nat → Signal i Bool) (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) {a j n : Nat}
    (hl : g.d.ls[a]? = some (⟨.bits n, .bitsInput n j⟩ : Σ s : SType, Term s)) (hj : g.d.vpos j < a0) (τ : Nat) :
    ((g.lsrc i bools bits)[a]?.map (· τ)).getD 0 = ((bits (g.d.vpos j) n).val τ).toNat := by
  have hin : g.d.vpos j < g.d.nIn := Nat.lt_of_lt_of_le hj (arity_le_nIn g hkD)
  have hE := hext i bools bits (g.d.vpos j) n hj
  have hT := (typedVal_in (D := i) g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (g.extBS i bools bits) (g.extS i bools bits) τ
    ((@stateLoop _ _ _ g.inh g.inits (g.body i bools bits)).val τ) (g.d.vpos j) hin).2 n
  have key : ((g.lsrc i bools bits)[a]?.map (· τ)).getD 0 = ((tvOf g i bools bits τ).v (g.d.vpos j) n).toNat := by
    simp only [GenPkg.lsrc, Tools.ShippingMachineCausal.letObsB, List.getElem?_map, hl, Option.map_some, Option.getD_some] <;> rfl
  rw [key]
  change ((typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (g.extBS i bools bits) (g.extS i bools bits) τ
    ((@stateLoop _ _ _ g.inh g.inits (g.body i bools bits)).val τ)).v (g.d.vpos j) n).toNat = _
  rw [hT, hE]

theorem signal_ext {D : DomainConfig} {α : Type} (s t : Signal D α) (h : ∀ τ, s.val τ = t.val τ) : s = t := by
  cases s; cases t; exact congrArg Signal.mk (funext h)

/-- **Q-DECODE, Bool port**: the decoded Bool at a Bool port `p` of the leaf, at an ordinary call `k`, is the wrapper's input family
at the position `argPos k p` (not at `p`: for `wrapQ`, leaf port 1 is wrapper position 3). -/
theorem decode_boolQ (L : QLeafPkg) (w : QWrapper L) {k : Nat} (hk : k < w.pkg.d.shape.insts.length)
    (hch : (originAt w.pkg.d.shape k).child? = none) (i : DomainConfig) (bools : Nat → Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) {p : Nat}
    (hp : L.d.bsIn[p]?.map (·.2) = some MixedGateBinder.bool) :
    boolsOf (D := i) L.d.bsIn (valsOf (w.pkg.lsrc i bools bits) (w.pkg.d.shape.insts[k]).2.1) p = bools (w.dat.argPos k p) := by
  obtain ⟨b, hb, hbb⟩ : ∃ b, L.d.bsIn[p]? = some b ∧ b.2 = .bool := by
    cases h : L.d.bsIn[p]? with
    | none => rw [h] at hp; simp at hp
    | some b => rw [h] at hp; simp at hp; exact ⟨b, rfl, hp⟩
  have hlen := (List.getElem?_eq_some_iff.mp hb).1
  have hlt := w.dat.argLt k hk hch p hlen
  obtain ⟨a, j, harg, hl, hj⟩ := argInOkQ_bool (w.dat.argsIn k hk hch p hlen) hb hbb
  apply signal_ext; intro τ
  show (((valsOf (w.pkg.lsrc i bools bits) (w.pkg.d.shape.insts[k]).2.1) τ).getD (portIdx L.d.bsIn p) 0 != 0) = _
  have h1 : ((valsOf (w.pkg.lsrc i bools bits) (w.pkg.d.shape.insts[k]).2.1) τ).getD (portIdx L.d.bsIn p) 0 =
      ((w.pkg.lsrc i bools bits)[a]?.map (· τ)).getD 0 := by
    simp [valsOf, List.getD_eq_getElem?_getD, List.getElem?_map, harg]
  rw [h1, lsrc_bool_valQ w.pkg w.dat.mem.hkD w.dat.hextB i bools bits hl (by rw [hj]; exact hlt) τ, hj]
  cases (bools (w.dat.argPos k p)).val τ <;> simp [encodeBool]

/-- **Q-DECODE, BitVec port** -/
theorem decode_bitsQ (L : QLeafPkg) (w : QWrapper L) {k : Nat} (hk : k < w.pkg.d.shape.insts.length)
    (hch : (originAt w.pkg.d.shape k).child? = none) (i : DomainConfig) (bools : Nat → Signal i Bool)
    (bits : (j : Nat) → (n : Nat) → Signal i (BitVec n)) {p n : Nat}
    (hp : L.d.bsIn[p]?.map (·.2) = some (MixedGateBinder.bits n)) :
    bitsOf (D := i) L.d.bsIn (valsOf (w.pkg.lsrc i bools bits) (w.pkg.d.shape.insts[k]).2.1) p n = bits (w.dat.argPos k p) n := by
  obtain ⟨b, hb, hbb⟩ : ∃ b, L.d.bsIn[p]? = some b ∧ b.2 = .bits n := by
    cases h : L.d.bsIn[p]? with
    | none => rw [h] at hp; simp at hp
    | some b => rw [h] at hp; simp at hp; exact ⟨b, rfl, hp⟩
  have hlen := (List.getElem?_eq_some_iff.mp hb).1
  have hlt := w.dat.argLt k hk hch p hlen
  obtain ⟨a, j, harg, hl, hj⟩ := argInOkQ_bits (w.dat.argsIn k hk hch p hlen) hb hbb
  apply signal_ext; intro τ
  show BitVec.ofNat n (((valsOf (w.pkg.lsrc i bools bits) (w.pkg.d.shape.insts[k]).2.1) τ).getD (portIdx L.d.bsIn p) 0) = _
  have h1 : ((valsOf (w.pkg.lsrc i bools bits) (w.pkg.d.shape.insts[k]).2.1) τ).getD (portIdx L.d.bsIn p) 0 =
      ((w.pkg.lsrc i bools bits)[a]?.map (· τ)).getD 0 := by
    simp [valsOf, List.getD_eq_getElem?_getD, List.getElem?_map, harg]
  rw [h1, lsrc_bits_valQ w.pkg w.dat.mem.hkD w.dat.hext i bools bits hl (by rw [hj]; exact hlt) τ, hj]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (bits (w.dat.argPos k p) n |>.val τ).isLt

/-! ## 2. `CallFactFO` of the ordinary calls of every wrapper, from `callOut` and the decoding -/

theorem callFactFO_of_class (L : QLeafPkg) (w : QWrapper L) :
    CallFactFO w.pkg.d w.dat.arity (dom := fun i : DomainConfig => i) w.pkg.lsrc w.pkg.extS w.pkg.extBS
      (genOutsC L.decl L.d.shape.layout.outs) (genSrcC L.decl L.d.bsIn L.src) := by
  intro i bools bits k hk hch
  have hkid := w.dat.ordKid k hk hch
  obtain ⟨k', o, ho, hname, hrest⟩ := w.dat.callOut k hk hch i bools bits
  obtain ⟨f, hf, hτ⟩ := hrest (boolsOf (D := i) L.d.bsIn (valsOf (w.pkg.lsrc i bools bits) (w.pkg.d.shape.insts[k]).2.1))
    (bitsOf (D := i) L.d.bsIn (valsOf (w.pkg.lsrc i bools bits) (w.pkg.d.shape.insts[k]).2.1))
    (fun p hp => decode_boolQ L w hk hch i bools bits hp) (fun p n hp => decode_bitsQ L w hk hch i bools bits hp)
  refine ⟨k', o, f, ?_, hname, ?_, hτ⟩
  · rw [hkid]; unfold genOutsC; rw [if_pos rfl]; exact ho
  · rw [hkid]; simp only [genSrcC, ↓reduceIte]; exact hf

/-! ## 3. Q-HCALLS -/

/-- **Q-HCALLS from the class alone** (both wrappers, one route): the shape of `wrapQ_hcalls`, `PCs := MachineRun` of the plain leaf. -/
theorem hcalls_of_classQ (P : QSharedLeafParent) (w : QWrapper P.leaf) (hw : w ∈ P.wrappers)
    (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    HCallsOf 1 w.pkg.d design m (dom := fun i : DomainConfig => i) w.pkg.lsrc w.pkg.extS w.pkg.extBS w.dat.arity
      (genBsC P.leaf.decl P.leaf.d.bsIn) (genOutsC P.leaf.decl P.leaf.d.shape.layout.outs)
      (genSrcC P.leaf.decl P.leaf.d.bsIn P.leaf.src)
      (genPC (fun mc => Tools.ShippingGateChild.MachineRun P.leaf.decl P.leaf.d.shape mc)) := by
  letI := w.pkg.inh
  exact ordCallee_hcalls (initsC := w.pkg.inits) (bodyC := w.pkg.body) (extC := w.pkg.ext) (extBC := w.pkg.extB)
    (srcG := P.leaf.src) (bsG := P.leaf.d.bsIn) (outsG := P.leaf.d.shape.layout.outs)
    (PCs := fun _ mc => Tools.ShippingGateChild.MachineRun P.leaf.decl P.leaf.d.shape mc)
    w.dat.mem w.dat.ordKid w.dat.ordArgsN w.dat.widths w.dat.wid w.dat.ordW w.dat.memCalls
    (fun i design mc hmc => by
      obtain ⟨mctx', mref', cctx', cref', w1, w2, Dc, hrun', hdef, hcl⟩ := hmc
      exact P.leafRun i hrun' hdef hcl (childMap design.modules) design 1)
    (callFactFO_of_class P.leaf w) m design

/-! ## 4. corollaries for the member `P_Q`: `TqHcallsP` and `TqFQ` -/

theorem wrapP_mem (hgrp : TqGrp) : (⟨wrapPPkg, wrapPDat⟩ : QWrapper qLeafP) ∈ (P_Q hgrp).wrappers := List.Mem.head _
theorem wrapQ_mem (hgrp : TqGrp) : (⟨wrapQPkg, wrapQDat⟩ : QWrapper qLeafP) ∈ (P_Q hgrp).wrappers := List.Mem.tail _ (List.Mem.head _)

/-- `leafPC` is an `if` with two equal branches: it is the constant run predicate of `genPC` (bridge by `ite_self`) -/
theorem leafPC_eq_genPC (G : Name) (dG : MachineData) :
    leafPC G dG = genPC (fun mc => Tools.ShippingGateChild.MachineRun G dG.shape mc) := by
  funext n
  unfold leafPC genPC
  exact ite_self _

/-- **`TqHcallsP O` recovered from the class route** (the shape differs only in the tables, defeq, and in `leafPC`, bridged by `ite_self`) -/
theorem TqHcallsP_of_class (hgrp : TqGrp) (O : RefLawsAOps MkRefd mref cref) : TqHcallsP O := by
  intro m design
  have h := hcalls_of_classQ (P_Q hgrp) ⟨wrapPPkg, wrapPDat⟩ (wrapP_mem hgrp) m design
  have e := leafPC_eq_genPC ``leafP leafP.machineData
  unfold Tools.ShippingQuadComposed.leafBsC Tools.ShippingQuadComposed.leafOutsC Tools.ShippingQuadComposed.leafSrcC
  rw [e]
  exact h

/-- **`TqFQ` recovered**: `CallFactFO` of `wrapQ` is the wrapQ instance of `callFactFO_of_class` -/
theorem TqFQ_of_class (hgrp : TqGrp) : TqFQ := callFactFO_of_class (P_Q hgrp).leaf ⟨wrapQPkg, wrapQDat⟩

/-- the `wrapQ` form of `wrapQ_hcalls` (its `wqPCs`) from the class route -/
theorem wrapQ_hcalls_of_class (hgrp : TqGrp) (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    HCallsOf 1 wrapQ.machineData design m (dom := fun i : DomainConfig => i)
      (letObsB wrapQ.machineData (fun i : DomainConfig => i) wrapQ.machineInits wrapQ.machineBody wrapQ.machineExt wrapQ.machineExtB)
      (fun i bools bits => wrapQ.machineExt i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits)))
      (fun i bools bits => wrapQ.machineExtB i bools bits (stateLoop wrapQ.machineInits (wrapQ.machineBody i bools bits)))
      5 (genBsC ``leafP leafP.machineData.bsIn) (genOutsC ``leafP leafP.machineData.shape.layout.outs)
      (genSrcC ``leafP leafP.machineData.bsIn leafP.machineSource) (genPC (wqPCs design)) :=
  hcalls_of_classQ (P_Q hgrp) ⟨wrapQPkg, wrapQDat⟩ (wrapQ_mem hgrp) m design

/-! ## 5. audit -/
open Lean Meta Elab Term in
run_cmd Lean.Elab.Command.liftTermElabM do
  let ci ← getConstInfo ``hcalls_of_classQ
  let expected ← elabTerm (← `(∀ (P : QSharedLeafParent) (w : QWrapper P.leaf) (hw : w ∈ P.wrappers)
      (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design),
      HCallsOf 1 w.pkg.d design m (dom := fun i : DomainConfig => i) w.pkg.lsrc w.pkg.extS w.pkg.extBS w.dat.arity
        (genBsC P.leaf.decl P.leaf.d.bsIn) (genOutsC P.leaf.decl P.leaf.d.shape.layout.outs)
        (genSrcC P.leaf.decl P.leaf.d.bsIn P.leaf.src)
        (genPC (fun mc => Tools.ShippingGateChild.MachineRun P.leaf.decl P.leaf.d.shape mc)))) none
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq ci.type (← instantiateMVars expected) do throwError "QHCALLS AUDIT FAILED: hcalls_of_classQ type differs from the stated theorem"
  forallTelescope ci.type fun xs _ => do
    let mut s := #[]
    for x in xs do
      s := s.push s!"{← x.fvarId!.getUserName}:{repr (← x.fvarId!.getBinderInfo)}"
      let ty ← inferType x
      -- no hypothesis binder other than membership `hw`: every binder is the class, a wrapper, hw, or the free module/design
      if ty.isAppOf ``HCallsOf || ty.isAppOf ``CallFactFO || ty.isAppOf ``Tests.Compiler.SharedLeafMemKidIfaceTest.TqGrp
          || ty.isAppOf ``Tools.ShippingQuadComposed.QuadGroupFacts then
        throwError "QHCALLS AUDIT FAILED: hcalls_of_classQ takes a hypothesis binder {← x.fvarId!.getUserName}"
    unless xs.size == 5 do throwError "QHCALLS AUDIT FAILED: {xs.size} binders, expected 5 (P w hw m design)"
    logInfo m!"QHCALLS|binders: {s}"
  -- callFactFO_of_class: stated type
  let c2 ← getConstInfo ``callFactFO_of_class
  let expected2 ← elabTerm (← `(∀ (L : QLeafPkg) (w : QWrapper L),
      CallFactFO w.pkg.d w.dat.arity (dom := fun i : DomainConfig => i) w.pkg.lsrc w.pkg.extS w.pkg.extBS
        (genOutsC L.decl L.d.shape.layout.outs) (genSrcC L.decl L.d.bsIn L.src))) none
  synthesizeSyntheticMVarsNoPostponing
  unless ← isDefEq c2.type (← instantiateMVars expected2) do throwError "QHCALLS AUDIT FAILED: callFactFO_of_class type differs"
  -- corollaries: exactly TqHcallsP O / TqFQ with the one class assumption TqGrp
  let c3 ← getConstInfo ``TqHcallsP_of_class
  forallTelescope c3.type fun xs body => do
    unless xs.size == 4 do throwError "QHCALLS AUDIT FAILED: TqHcallsP_of_class has {xs.size} binders, expected 4 (mref cref hgrp O)"
    unless ← isDefEq (← inferType xs[2]!) (mkConst ``Tests.Compiler.SharedLeafMemKidIfaceTest.TqGrp) do
      throwError "QHCALLS AUDIT FAILED: TqHcallsP_of_class's third binder is not TqGrp"
    unless ← isDefEq body (mkAppN (mkConst ``Tests.Compiler.SharedLeafMemKidIfaceTest.TqHcallsP) #[xs[0]!, xs[1]!, xs[3]!]) do
      throwError "QHCALLS AUDIT FAILED: TqHcallsP_of_class does not conclude TqHcallsP O"
  let c4 ← getConstInfo ``TqFQ_of_class
  forallTelescope c4.type fun xs body => do
    unless xs.size == 1 do throwError "QHCALLS AUDIT FAILED: TqFQ_of_class has {xs.size} binders, expected 1 (hgrp)"
    unless ← isDefEq (← inferType xs[0]!) (mkConst ``Tests.Compiler.SharedLeafMemKidIfaceTest.TqGrp) do
      throwError "QHCALLS AUDIT FAILED: TqFQ_of_class's binder is not TqGrp"
    unless ← isDefEq body (mkConst ``Tests.Compiler.SharedLeafMemKidIfaceTest.TqFQ) do
      throwError "QHCALLS AUDIT FAILED: TqFQ_of_class does not conclude TqFQ"
  -- wrapQ_hcalls_of_class: exactly 3 binders (hgrp : TqGrp, m, design) and the conclusion of the instance theorem
  -- SharedLeafMemKidIfaceTest.wrapQ_hcalls (whose first binder is the text-supplied hF : CallFactFO …, not used by its conclusion)
  let c5 ← getConstInfo ``wrapQ_hcalls_of_class
  let inst ← getConstInfo ``Tests.Compiler.SharedLeafMemKidIfaceTest.wrapQ_hcalls
  forallTelescope c5.type fun xs body => do
    let mut s := #[]
    for x in xs do s := s.push s!"{← x.fvarId!.getUserName}:{repr (← x.fvarId!.getBinderInfo)}"
    unless xs.size == 3 do throwError "QHCALLS AUDIT FAILED: wrapQ_hcalls_of_class has {xs.size} binders, expected 3 (hgrp m design)"
    unless s.toList == ["hgrp:Lean.BinderInfo.default", "m:Lean.BinderInfo.default", "design:Lean.BinderInfo.default"] do
      throwError "QHCALLS AUDIT FAILED: wrapQ_hcalls_of_class binders {s}, expected [hgrp, m, design] all explicit"
    unless ← isDefEq (← inferType xs[0]!) (mkConst ``Tests.Compiler.SharedLeafMemKidIfaceTest.TqGrp) do
      throwError "QHCALLS AUDIT FAILED: wrapQ_hcalls_of_class's first binder is not TqGrp"
    unless ← isDefEq (← inferType xs[1]!) (mkConst ``Sparkle.IR.AST.Module) do
      throwError "QHCALLS AUDIT FAILED: wrapQ_hcalls_of_class's second binder is not a Module"
    unless ← isDefEq (← inferType xs[2]!) (mkConst ``Sparkle.IR.AST.Design) do
      throwError "QHCALLS AUDIT FAILED: wrapQ_hcalls_of_class's third binder is not a Design"
    let instRest := inst.type.bindingBody!
    if instRest.hasLooseBVars then
      -- the instance's conclusion must not depend on its hF binder
      unless (instRest.bindingBody!.bindingBody!).looseBVarRange ≤ 2 do
        throwError "QHCALLS AUDIT FAILED: wrapQ_hcalls's conclusion depends on hF"
    let expected ← instantiateForall (instRest.instantiate1 (mkConst ``True.intro)) #[xs[1]!, xs[2]!]
    unless ← isDefEq body expected do
      throwError "QHCALLS AUDIT FAILED: wrapQ_hcalls_of_class does not conclude wrapQ_hcalls's HCallsOf"
    logInfo m!"QHCALLS|corollary wrapQ_hcalls_of_class binders {s}: TqGrp → ∀ m design, the conclusion of wrapQ_hcalls (isDefEq)"
  for n in [``hcalls_of_classQ, ``callFactFO_of_class, ``decode_boolQ, ``decode_bitsQ, ``TqHcallsP_of_class, ``TqFQ_of_class,
      ``wrapQ_hcalls_of_class, ``leafPC_eq_genPC] do
    let axs ← Lean.collectAxioms n
    for x in axs do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains x do throwError "QHCALLS AUDIT FAILED: {x} in {n}"
    logInfo m!"QHCALLS|axioms {n}: {axs}"

/-! closure audit: the generic root reaches only the class file and the generic helpers of this file -/
open Lean Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut work : List Name := [``hcalls_of_classQ]
  let mut reached : Array Name := #[]
  while !work.isEmpty do
    let n := work.head!
    work := work.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "QHCALLS CLOSURE FAILED: {n} not found"
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
    unless (c.toString.splitOn "Tests.Compiler.QDef.").length > 1 || (c.toString.splitOn "Tests.Compiler.CDef.").length > 1
        || (c.toString.splitOn "Tests.Compiler.QHCalls.").length > 1 do
      throwError "QHCALLS CLOSURE FAILED: hcalls_of_classQ reaches {c} (outside the class definition and this file)"
    for comp in c.components.map (·.toString) do
      if ["P_Q", "P_M", "wrapP", "wrapQ", "leafP", "wrapM", "wrapM3", "leafM"].contains comp
          || comp.startsWith "topshare" || comp.startsWith "Tq" || comp.startsWith "wrapP" || comp.startsWith "wrapQ" then
        throwError "QHCALLS CLOSURE FAILED: hcalls_of_classQ reaches {c} (instance component {comp})"
  let helpers : List Name := [``callFactFO_of_class, ``decode_boolQ, ``decode_bitsQ, ``argInOkQ_bool, ``argInOkQ_bits, ``letVal_lt,
    ``typedVal_in, ``tvOf, ``arity_le_nIn, ``lsrc_bool_valQ, ``lsrc_bits_valQ, ``signal_ext]
  for c in reached do
    if (c.toString.splitOn "Tests.Compiler.QHCalls.").length > 1 then
      unless helpers.any (fun h => (c.toString.splitOn h.toString).length > 1) do
        throwError "QHCALLS CLOSURE FAILED: unexpected own constant {c} in the closure"
  for h in [``callFactFO_of_class, ``decode_boolQ, ``decode_bitsQ, ``QSharedLeafParent.leafRun, ``QWrapData.callOut, ``QWrapData.argLt] do
    unless reached.contains h do throwError "QHCALLS CLOSURE FAILED: expected constant {h} not reached"
  for h in [``TqHcallsP_of_class, ``TqFQ_of_class, ``wrapQ_hcalls_of_class, ``wrapP_mem, ``wrapQ_mem, ``leafPC_eq_genPC] do
    if reached.contains h then throwError "QHCALLS CLOSURE FAILED: corollary {h} reached"
  logInfo m!"QHCALLS|closure ok: {reached.size} Tests constants reached; no member value, no instance file"

#print axioms hcalls_of_classQ
#print axioms callFactFO_of_class
#print axioms TqHcallsP_of_class
#print axioms TqFQ_of_class
#print axioms wrapQ_hcalls_of_class

end Tests.Compiler.QHCalls
