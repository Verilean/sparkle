import Tools.ShippingGen5SemGen
set_option autoImplicit false
-- Clean build smu4v-1258f07e (exit 0, 709 jobs, approved at 1258f07e; Lean content unchanged since c28de8a1). No sorry/axiom/native_decide.
/-! # DG-SEM U4A-U4D (scripts/gen5/DG_SEM_FREEZE_P4.md rev1, approved 6d596308)

U4A definitions, U4B `genSemI_local` & arm accessors, U4C structural lemmas on `callOut`/`ExtStage`, U4D `callOut_mem_val`.
Statements are those of the freeze. Nothing here supplies `GenWF` coverage, causality, `GenExtAtCall`, `dataOf`, ACC. -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineRef (reads)
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Sparkle.Compiler.MachInstOrigin

variable {ι : Type} {dom : ι → DomainConfig}

def ordCallees (d : MachineData) : List (Fin d.shape.insts.length) :=
  (List.finRange d.shape.insts.length).filter fun k => (d.shape.instOrigins.getD k .ord).child? = none

def lsrcGet (L : List (Nat → Nat)) (l : Nat) (j : Nat) : Nat := ((L[l]?).map (· j)).getD 0

noncomputable def lsrcAt (d : MachineData) {D : DomainConfig} (bs : Nat → Signal D Bool)
    (vs : (j n : Nat) → Signal D (BitVec n)) (S : Signal D (HList (tys d.ss))) : List (Nat → Nat) :=
  d.ls.map fun l t => enc l.1 (eval
    (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bs vs t (S.val t)).b (d.bpos j))
    (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bs vs t (S.val t)).v (d.vpos j) w) l.2)

def selIdx (d : MachineData) (q : SemPkg ι dom) (k : Nat) : Option Nat :=
  if d.shape.instFields = [] then (if q.d.shape.layout.outs.length = 1 then some 0 else none)
  else q.d.shape.layout.outs.findIdx? (·.name = d.shape.instFields.getD k "")

noncomputable def calleeOut (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat) : Nat → Nat :=
  match g.d.shape.insts[k]? with
  | none => fun _ => 0
  | some (c, _, _) =>
    match Q c with
    | none => fun _ => 0
    | some q =>
      let vals : Nat → List Nat := Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) (callArgs g.d k)
      let A := Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD) vals
      let B := Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD) vals
      match selIdx g.d q k with
      | none => fun _ => 0
      | some k' => ((q.src i A B)[k']?).getD (fun _ => 0)

noncomputable def withCall (g : GenIn) (i : ι) (k : Nat) (κ : MixedGateBinder) (f : Nat → Nat)
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) :
    (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)) :=
  match κ with
  | .bool   => (fun p => if p = kDOf g.d + k then ⟨fun τ => f τ != 0⟩ else bs p, vs)
  | .bits _ => (bs, fun p n => if p = kDOf g.d + k then ⟨fun τ => BitVec.ofNat n (f τ)⟩ else vs p n)
  | .domain => (bs, vs)

noncomputable def memOut (g : GenIn) (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) : Signal (dom i) (BitVec dw) :=
  Tools.ShippingMachineMemLinked.memRead (D := dom i) (aw := aw) (dw := dw) cb
    ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d bs vs S) l0 j)⟩
    ⟨fun j => BitVec.ofNat dw (lsrcGet (lsrcAt g.d bs vs S) l1 j)⟩
    ⟨fun j => lsrcGet (lsrcAt g.d bs vs S) l2 j != 0⟩
    ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d bs vs S) l3 j)⟩

noncomputable def callOut (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))) :
    (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)) :=
  match g.d.shape.insts[k]? with
  | none => st
  | some _ =>
    match originOf g.d k with
    | .mem cb aw dw =>
      match callArgs g.d k with
      | [l0, l1, l2, l3] =>
          (st.1, fun p n => if p = kDOf g.d + k then
                              (if h : dw = n then h ▸ memOut g cb aw dw l0 l1 l2 l3 i S st.1 st.2 else ⟨fun _ => 0⟩)
                            else st.2 p n)
      | _ => st
    | _ => withCall g i k (callKind g.d k) (calleeOut Q g i S st.1 st.2 k) st.1 st.2

noncomputable def ExtStage (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j n : Nat) → Signal (dom i) (BitVec n)) (S : Signal (dom i) (HList (tys g.d.ss))) :
    Nat → (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))
  | 0 => (bools, bits)
  | n + 1 => callOut Q g i S n (ExtStage Q g i bools bits S n)

noncomputable def extBOf (Q : Name → Option (SemPkg ι dom)) (g : GenIn) : ExtB ι dom g.d.ss :=
  fun i bools bits S => (ExtStage Q g i bools bits S g.d.shape.insts.length).1
noncomputable def extOf (Q : Name → Option (SemPkg ι dom)) (g : GenIn) : ExtV ι dom g.d.ss :=
  fun i bools bits S => (ExtStage Q g i bools bits S g.d.shape.insts.length).2

noncomputable def genSemGen (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) : SrcSem ι dom :=
  genSemGenE X g (extBOf Q g) (extOf Q g)

noncomputable def genSemComb (X : Name) (g : GenIn) : CombSem ι dom :=
  ⟨X, g.d, kDOf g.d, g.inits,
    fun _ bools bits =>
      g.d.outs.map fun o t => enc o.1 (eval
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls bools bits t g.inits).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls bools bits t g.inits).v (g.d.vpos j) w) o.2)⟩

noncomputable def genSemI (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) : SemPkg ι dom :=
  if g.d.ss.isEmpty && g.d.shape.insts.isEmpty then .comb (genSemComb X g) else .gen (genSemGen Q X g)

noncomputable def genSemVia (GD : Lean.ConstantInfo → Type) (toIn : {E : Lean.ConstantInfo} → GD E → GenIn)
    (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : Lean.ConstantInfo} (gd : GD E) : SemPkg ι dom :=
  genSemI Q X (toIn gd)

/-! ## U4B -/

theorem genSemI_decl (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) : (genSemI Q X g).decl = X := by
  unfold genSemI; split <;> rfl

theorem genSemI_d (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) : (genSemI Q X g).d = g.d := by
  unfold genSemI; split <;> rfl

theorem genSemI_not_loop (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) :
    ∀ s : LoopSem ι dom, genSemI Q X g ≠ .loop s := by
  intro s h
  unfold genSemI at h
  split at h <;> cases h

theorem callOut_local (Q Q' : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (hQ : ∀ (c : Name) (a : List Nat) (κ : MixedGateBinder), g.d.shape.insts[k]? = some (c, a, κ) →
            (originOf g.d k).child? = none → Q c = Q' c) :
    callOut Q g i S k st = callOut Q' g i S k st := by
  unfold callOut
  cases hk : g.d.shape.insts[k]? with
  | none => rfl
  | some e =>
    obtain ⟨c, a, κ⟩ := e
    have hc := hQ c a κ hk
    dsimp only
    cases ho : originOf g.d k with
    | mem cb aw dw => rfl
    | ord =>
      have := hc (by rw [ho]; rfl)
      simp only [calleeOut, hk, this]
    | field n =>
      have := hc (by rw [ho]; rfl)
      simp only [calleeOut, hk, this]

theorem ExtStage_zero (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) : ExtStage Q g i bools bits S 0 = (bools, bits) := rfl

theorem ExtStage_succ (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (n : Nat) :
    ExtStage Q g i bools bits S (n + 1) = callOut Q g i S n (ExtStage Q g i bools bits S n) := rfl

theorem mem_ordCallees (d : MachineData) (k : Fin d.shape.insts.length) :
    k ∈ ordCallees d ↔ (originOf d k).child? = none := by
  unfold ordCallees originOf
  simp [List.mem_filter, List.mem_finRange]

theorem ExtStage_local (Q Q' : Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : ∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1)
    (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (n : Nat) :
    ExtStage Q g i bools bits S n = ExtStage Q' g i bools bits S n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ExtStage_succ, ExtStage_succ, ih]
    apply callOut_local
    intro c a κ hk hch
    have hn : n < g.d.shape.insts.length := by
      rcases Nat.lt_or_ge n g.d.shape.insts.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hk
        cases hk
    have h1 := hQ ⟨n, hn⟩ ((mem_ordCallees g.d ⟨n, hn⟩).2 hch)
    have h2 : g.d.shape.insts[n] = (c, a, κ) := by
      rw [List.getElem?_eq_getElem hn] at hk
      exact Option.some.inj hk
    simpa [h2] using h1

theorem genSemI_local (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn)
    (hQ : ∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) :
    genSemI Q X g = genSemI Q' X g := by
  have hb : extBOf Q g = extBOf Q' g := by
    funext i bools bits S
    unfold extBOf
    rw [ExtStage_local Q Q' g hQ]
  have hv : extOf Q g = extOf Q' g := by
    funext i bools bits S
    unfold extOf
    rw [ExtStage_local Q Q' g hQ]
  unfold genSemI genSemGen
  rw [hb, hv]

/-! ## U4C -/

theorem callOut_none (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (hk : g.d.shape.insts[k]? = none) : callOut Q g i S k st = st := by
  unfold callOut
  rw [hk]

theorem calleeOut_none (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat)
    (hk : g.d.shape.insts[k]? = none) : calleeOut Q g i S bs vs k = fun _ => 0 := by
  unfold calleeOut
  rw [hk]

theorem callOut_frame (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))) :
    (∀ p, p ≠ kDOf g.d + k → (callOut Q g i S k st).1 p = st.1 p) ∧
    (∀ p n, p ≠ kDOf g.d + k → (callOut Q g i S k st).2 p n = st.2 p n) := by
  unfold callOut
  split
  · exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  · split
    · split
      · refine ⟨fun _ _ => rfl, fun p n hp => ?_⟩
        simp [hp]
      · exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
    · unfold withCall
      split
      · refine ⟨fun p hp => ?_, fun _ _ _ => rfl⟩
        simp [hp]
      · refine ⟨fun _ _ => rfl, fun p n hp => ?_⟩
        simp [hp]
      · exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem ExtStage_agree (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) {n m : Nat} (h : n ≤ m) :
    ∀ p, p < kDOf g.d + n →
      (ExtStage Q g i bools bits S m).1 p = (ExtStage Q g i bools bits S n).1 p ∧
      ∀ w, (ExtStage Q g i bools bits S m).2 p w = (ExtStage Q g i bools bits S n).2 p w := by
  induction h with
  | refl => intro p _; exact ⟨rfl, fun _ => rfl⟩
  | @step m hnm ih =>
    intro p hp
    obtain ⟨h1, h2⟩ := ih p hp
    have hnm' : n ≤ m := hnm
    have hne : p ≠ kDOf g.d + m := by omega
    obtain ⟨f1, f2⟩ := callOut_frame Q g i S m (ExtStage Q g i bools bits S m)
    rw [ExtStage_succ]
    exact ⟨(f1 p hne).trans h1, fun w => (f2 p w hne).trans (h2 w)⟩

/-! ## U4D -/

theorem callOut_mem_val (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (ho : originOf g.d k = .mem cb aw dw)
    (ha : callArgs g.d k = [l0, l1, l2, l3]) :
    (callOut Q g i S k st).2 (kDOf g.d + k) dw = memOut g cb aw dw l0 l1 l2 l3 i S st.1 st.2 := by
  unfold callOut
  rw [hk]
  dsimp only
  rw [ho]
  dsimp only
  rw [ha]
  dsimp only
  simp

end Tools.ShippingGen5Sem
