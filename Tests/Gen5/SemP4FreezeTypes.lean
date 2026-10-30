import Tools.ShippingGen5SemGen
set_option autoImplicit false
-- SCRATCH type-elaboration of scripts/gen5/DG_SEM_FREEZE_P4.md (rev1). Definitions are the U4A text; every theorem is a `Prop` def (statement only, no proof, no sorry).
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
      let vals : Nat → List Nat := ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) (callArgs g.d k)
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


/-! ## statements (each a `Prop` def: type-checks, no proof) -/
section Stmts
variable (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (i : ι)
  (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
  (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
  (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
  (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n))

def S_genSemI_decl : Prop := ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn), (genSemI Q X g).decl = X
def S_genSemI_d : Prop := ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn), (genSemI Q X g).d = g.d
def S_genSemI_not_loop : Prop := ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn),
    ∀ s : LoopSem ι dom, genSemI Q X g ≠ .loop s

def S_callOut_local : Prop :=
    (∀ (c : Name) (a : List Nat) (κ : MixedGateBinder), g.d.shape.insts[k]? = some (c, a, κ) →
            (originOf g.d k).child? = none → Q c = Q' c) →
    callOut Q g i S k st = callOut Q' g i S k st
def S_ExtStage_local : Prop :=
    (∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
    ∀ (n : Nat), ExtStage Q g i bools bits S n = ExtStage Q' g i bools bits S n
def S_genSemI_local : Prop :=
    (∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
    genSemI Q X g = genSemI Q' X g

def S_ExtStage_succ : Prop := ∀ n : Nat,
    ExtStage Q g i bools bits S (n + 1) = callOut Q g i S n (ExtStage Q g i bools bits S n)
def S_callOut_none : Prop := g.d.shape.insts[k]? = none → callOut Q g i S k st = st
def S_calleeOut_none : Prop := g.d.shape.insts[k]? = none → calleeOut Q g i S bs vs k = fun _ => 0
def S_callOut_frame : Prop :=
    (∀ p, p ≠ kDOf g.d + k → (callOut Q g i S k st).1 p = st.1 p) ∧
    (∀ p n, p ≠ kDOf g.d + k → (callOut Q g i S k st).2 p n = st.2 p n)
def S_ExtStage_agree : Prop := ∀ {n m : Nat}, n ≤ m →
    ∀ p, p < kDOf g.d + n →
      (ExtStage Q g i bools bits S m).1 p = (ExtStage Q g i bools bits S n).1 p ∧
      ∀ w, (ExtStage Q g i bools bits S m).2 p w = (ExtStage Q g i bools bits S n).2 p w

def S_callOut_mem_val : Prop := ∀ (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder),
    g.d.shape.insts[k]? = some (c, a, κ) → originOf g.d k = .mem cb aw dw →
    callArgs g.d k = [l0, l1, l2, l3] →
    (callOut Q g i S k st).2 (kDOf g.d + k) dw = memOut g cb aw dw l0 l1 l2 l3 i S st.1 st.2

def S_typedVal_let_congr (d : MachineData) (hok : d.ok = true) (k : Nat) {D : DomainConfig}
    (bools bools' : Nat → Signal D Bool)
    (bits bits' : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss)) : Prop :=
    (∀ p, p < kDOf d + k → (bools p).val t = (bools' p).val t) →
    (∀ p w, p < kDOf d + k → (bits p w).val t = (bits' p w).val t) →
    ∀ q, (cleanLets d k)[q]? = some true →
      (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).b (d.nIn + d.ss.length + q) =
        (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools' bits' t x).b (d.nIn + d.ss.length + q) ∧
      ∀ w, (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).v (d.nIn + d.ss.length + q) w =
        (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools' bits' t x).v (d.nIn + d.ss.length + q) w

def S_lsrcAt_congr (d : MachineData) (hok : d.ok = true) (k : Nat) {D : DomainConfig}
    (bs bs' : Nat → Signal D Bool) (vs vs' : (j n : Nat) → Signal D (BitVec n))
    (S : Signal D (HList (tys d.ss))) (t : Nat) : Prop :=
    (∀ p, p < kDOf d + k → (bs p).val t = (bs' p).val t) →
    (∀ p w, p < kDOf d + k → (vs p w).val t = (vs' p w).val t) →
    ∀ l, (cleanLets d k)[l]? = some true → lsrcGet (lsrcAt d bs vs S) l t = lsrcGet (lsrcAt d bs' vs' S) l t

def S_ext_mem_final : Prop := ∀ (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder),
    g.d.shape.insts[k]? = some (c, a, κ) → originOf g.d k = .mem cb aw dw →
    callArgs g.d k = [l0, l1, l2, l3] → GenWF g.d = true → g.d.ok = true →
    extOf Q g i bools bits S (kDOf g.d + k) dw =
      Tools.ShippingMachineMemLinked.memRead (D := dom i) (aw := aw) (dw := dw) cb
        ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l0 j)⟩
        ⟨fun j => BitVec.ofNat dw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l1 j)⟩
        ⟨fun j => lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l2 j != 0⟩
        ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l3 j)⟩

def S_lsrcAt_genSemGen : Prop :=
    let Sst := @stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGen Q X g).body i bools bits)
    lsrcAt g.d (extBOf Q g i bools bits Sst) (extOf Q g i bools bits Sst) Sst =
      (SemPkg.gen (genSemGen Q X g)).lsrc i bools bits

def S_memFacts_of_genSem : Prop := g.d.ok = true → ∀ (c : Name) (a : List Nat) (κ : MixedGateBinder),
    g.d.shape.insts[k]? = some (c, a, κ) →
    ∀ (cb : Bool) (aw dw : Nat), originOf g.d k = .mem cb aw dw →
    let Sst := @stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGen Q X g).body i bools bits)
    Tools.ShippingMachineCallsLinkedT.MemFacts (D := dom i) g.d.shape
      ((SemPkg.gen (genSemGen Q X g)).lsrc i bools bits) g.d.ls.length (g.d.bsIn.drop (kDOf g.d)) (kDOf g.d)
      (extOf Q g i bools bits Sst) k c
end Stmts

end Tools.ShippingGen5Sem
