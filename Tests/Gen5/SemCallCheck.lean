import Tools.ShippingGen5SemMem
import Tests.Gen5.SemGenCheck
set_option autoImplicit false
-- Built in g5sm-u4 at c28de8a1a7e26247d4b3082731cbcf6a820b640c (Pod kjob lake build, exit 0). Clean build is the coder's. No sorry/axiom/native_decide.

/-! # DG-SEM units U4A-U4F checks (Tools/ShippingGen5SemCall.lean, ShippingGen5SemCongr.lean, ShippingGen5SemMem.lean;
scripts/gen5/DG_SEM_FREEZE_P4.md rev1)

TYPE: every theorem of §3-§5 is compared (`checkExpected`) with an `Exp…` statement written here from the freeze text (not copied from the
implementation); every definition's *type* is compared with an `ExpTy…` written here (the bodies of the definitions are NOT compared). MUTANT:
one-place changes of an expected statement, and statements with a conjunct dropped, are rejected by the SAME comparer — signature / defeq
rejections, NOT semantic counterexamples. AXIOMS: standard only. CLOSURE/REACH: the explicit thm/defn/opaque walk of
`Tests.Gen5.SemGenCheck` (imported; its controls are re-run below). Counts are computed from the lists the checks iterate over. -/

namespace Tests.Gen5.SemCallCheck
open Lean Meta Elab
open Tools.ShippingGen5Sem Tests.Gen3.ExpectedType Tests.Gen5.SemGenCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource (stateLoop)
open Tools.ShippingMachineDenote (typedVal tys)
open Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineAuto

/-! ## Expected statements (theorems) -/

def ExpGenSemIDecl : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) (g : GenIn),
  (genSemI Q X g).decl = X
def ExpGenSemID : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) (g : GenIn),
  (genSemI Q X g).d = g.d
def ExpGenSemINotLoop : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) (g : GenIn),
  ∀ s : LoopSem ι dom, genSemI Q X g ≠ SemPkg.loop s
def ExpCallOutLocal : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q Q' : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (hQ : ∀ (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder), g.d.shape.insts[k]? = some (c, a, κ) →
            (originOf g.d k).child? = none → Q c = Q' c),
    callOut Q g i S k st = callOut Q' g i S k st
def ExpExtStageLocal : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q Q' : Lean.Name → Option (SemPkg ι dom)) (g : GenIn)
    (hQ : ∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1)
    (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (n : Nat),
    ExtStage Q g i bools bits S n = ExtStage Q' g i bools bits S n
def ExpGenSemILocal : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q Q' : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) (g : GenIn)
    (hQ : ∀ k ∈ ordCallees g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1),
    genSemI Q X g = genSemI Q' X g
def ExpExtStageZero : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))), ExtStage Q g i bools bits S 0 = (bools, bits)
def ExpExtStageSucc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (n : Nat),
    ExtStage Q g i bools bits S (n + 1) = callOut Q g i S n (ExtStage Q g i bools bits S n)
def ExpCallOutNone : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (hk : g.d.shape.insts[k]? = none), callOut Q g i S k st = st
def ExpCalleeOutNone : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat)
    (hk : g.d.shape.insts[k]? = none), calleeOut Q g i S bs vs k = fun _ => 0
def ExpCallOutFrame : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))),
    (∀ p, p ≠ kDOf g.d + k → (callOut Q g i S k st).1 p = st.1 p) ∧
    (∀ p n, p ≠ kDOf g.d + k → (callOut Q g i S k st).2 p n = st.2 p n)
def ExpExtStageAgree : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) {n m : Nat} (h : n ≤ m),
    ∀ p, p < kDOf g.d + n →
      (ExtStage Q g i bools bits S m).1 p = (ExtStage Q g i bools bits S n).1 p ∧
      ∀ w, (ExtStage Q g i bools bits S m).2 p w = (ExtStage Q g i bools bits S n).2 p w
def ExpCallOutMemVal : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (ho : originOf g.d k = InstOrigin.mem cb aw dw)
    (ha : callArgs g.d k = [l0, l1, l2, l3]),
    (callOut Q g i S k st).2 (kDOf g.d + k) dw = memOut g cb aw dw l0 l1 l2 l3 i S st.1 st.2
def ExpLsrcAtCongr : Prop := ∀ (d : MachineData) (hok : d.ok = true) (k : Nat) {D : DomainConfig}
    (bs bs' : Nat → Signal D Bool) (vs vs' : (j n : Nat) → Signal D (BitVec n))
    (S : Signal D (HList (tys d.ss))) (t : Nat)
    (hb : ∀ p, p < kDOf d + k → (bs p).val t = (bs' p).val t)
    (hv : ∀ p w, p < kDOf d + k → (vs p w).val t = (vs' p w).val t),
    ∀ l, (cleanLets d k)[l]? = some true → lsrcGet (lsrcAt d bs vs S) l t = lsrcGet (lsrcAt d bs' vs' S) l t
def ExpLsrcAtGenSemGen : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) (g : GenIn)
    (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n)),
    let Sst := @stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGen Q X g).body i bools bits)
    lsrcAt g.d (extBOf Q g i bools bits Sst) (extOf Q g i bools bits Sst) Sst =
      (SemPkg.gen (genSemGen Q X g)).lsrc i bools bits
def ExpExtMemFinal : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (ho : originOf g.d k = InstOrigin.mem cb aw dw)
    (ha : callArgs g.d k = [l0, l1, l2, l3]) (hwf : GenWF g.d = true) (hok : g.d.ok = true),
    extOf Q g i bools bits S (kDOf g.d + k) dw =
      Tools.ShippingMachineMemLinked.memRead (D := dom i) (aw := aw) (dw := dw) cb
        ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l0 j)⟩
        ⟨fun j => BitVec.ofNat dw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l1 j)⟩
        ⟨fun j => lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l2 j != 0⟩
        ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l3 j)⟩
def ExpMemFactsOfGenSem : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) (g : GenIn)
    (hok : g.d.ok = true) (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (k : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder) (hk : g.d.shape.insts[k]? = some (c, a, κ))
    (cb : Bool) (aw dw : Nat) (ho : originOf g.d k = InstOrigin.mem cb aw dw),
    let Sst := @stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGen Q X g).body i bools bits)
    Tools.ShippingMachineCallsLinkedT.MemFacts (D := dom i) g.d.shape
      ((SemPkg.gen (genSemGen Q X g)).lsrc i bools bits) g.d.ls.length (g.d.bsIn.drop (kDOf g.d)) (kDOf g.d)
      (extOf Q g i bools bits Sst) k c

/-- internal helper (not a freeze statement): the sort-aware stage preservation -/
def ExpTypedValLetAgree : Prop := ∀ (d : MachineData) (hok : d.ok = true) (k : Nat) {D : DomainConfig}
    (bs bs' : Nat → Signal D Bool) (vs vs' : (j n : Nat) → Signal D (BitVec n)) (t : Nat) (x : HList (tys d.ss))
    (hb : ∀ p, p < kDOf d + k → (bs p).val t = (bs' p).val t)
    (hv : ∀ p w, p < kDOf d + k → (vs p w).val t = (vs' p w).val t),
    ∀ p, posOk d k (cleanLets d k) p = true →
      AgrAt d (typedVal d.nIn d.bpos d.vpos d.ss d.ls bs vs t x) (typedVal d.nIn d.bpos d.vpos d.ss d.ls bs' vs' t x) p

/-! ## Expected types of the definitions (signature only) -/

def ExpTyOrdCallees : Type := (d : MachineData) → List (Fin d.shape.insts.length)
def ExpTyLsrcGet : Type := List (Nat → Nat) → Nat → Nat → Nat
def ExpTyLsrcAt : Type := (d : MachineData) → {D : DomainConfig} → (bs : Nat → Signal D Bool) →
  (vs : (j n : Nat) → Signal D (BitVec n)) → (S : Signal D (HList (tys d.ss))) → List (Nat → Nat)
def ExpTySelIdx : Type 1 := ∀ {ι : Type} {dom : ι → DomainConfig}, MachineData → SemPkg ι dom → Nat → Option Nat
def ExpTyCalleeOut : Type 1 := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (bs : Nat → Signal (dom i) Bool)
    (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat), Nat → Nat
def ExpTyWithCall : Type 1 := ∀ {ι : Type} {dom : ι → DomainConfig} (g : GenIn) (i : ι) (k : Nat) (κ : MixedGateBinder) (f : Nat → Nat)
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)),
    (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))
def ExpTyMemOut : Type 1 := ∀ {ι : Type} {dom : ι → DomainConfig} (g : GenIn) (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (bs : Nat → Signal (dom i) Bool)
    (vs : (j n : Nat) → Signal (dom i) (BitVec n)), Signal (dom i) (BitVec dw)
def ExpTyCallOut : Type 1 := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))),
    (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))
def ExpTyExtStage : Type 1 := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))), Nat → (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))
def ExpTyExtBOf : Type 1 := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn),
  (i : ι) → (Nat → Signal (dom i) Bool) → ((j n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys g.d.ss)) → Nat → Signal (dom i) Bool
def ExpTyExtOf : Type 1 := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn),
  (i : ι) → (Nat → Signal (dom i) Bool) → ((j n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys g.d.ss)) → (j n : Nat) → Signal (dom i) (BitVec n)
def ExpTyGenSemGen : Type 1 := ∀ {ι : Type} {dom : ι → DomainConfig}, (Lean.Name → Option (SemPkg ι dom)) → Lean.Name → GenIn → SrcSem ι dom
def ExpTyGenSemComb : Type 1 := ∀ {ι : Type} {dom : ι → DomainConfig}, Lean.Name → GenIn → CombSem ι dom
def ExpTyGenSemI : Type 1 := ∀ {ι : Type} {dom : ι → DomainConfig}, (Lean.Name → Option (SemPkg ι dom)) → Lean.Name → GenIn → SemPkg ι dom
def ExpTyGenSemVia : Type 1 := ∀ {ι : Type} {dom : ι → DomainConfig} (GD : Lean.ConstantInfo → Type)
    (toIn : {E : Lean.ConstantInfo} → GD E → GenIn) (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name)
    {E : Lean.ConstantInfo} (gd : GD E), SemPkg ι dom

/-! ## Mutants: one-place changes and dropped conjuncts (each is well typed) -/

def MutAgreeLt : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) {n m : Nat} (h : n ≤ m),
    ∀ p, p < kDOf g.d + n + 1 →
      (ExtStage Q g i bools bits S m).1 p = (ExtStage Q g i bools bits S n).1 p ∧
      ∀ w, (ExtStage Q g i bools bits S m).2 p w = (ExtStage Q g i bools bits S n).2 p w
def MutAgreeDropBits : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) {n m : Nat} (h : n ≤ m),
    ∀ p, p < kDOf g.d + n → (ExtStage Q g i bools bits S m).1 p = (ExtStage Q g i bools bits S n).1 p
def MutFramePlus : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))),
    (∀ p, p ≠ kDOf g.d + k + 1 → (callOut Q g i S k st).1 p = st.1 p) ∧
    (∀ p n, p ≠ kDOf g.d + k → (callOut Q g i S k st).2 p n = st.2 p n)
def MutFrameDropBits : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))),
    (∀ p, p ≠ kDOf g.d + k → (callOut Q g i S k st).1 p = st.1 p)
def MutCallOutNoneNoHyp : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))), callOut Q g i S k st = st
def MutMemValPos : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (ho : originOf g.d k = InstOrigin.mem cb aw dw)
    (ha : callArgs g.d k = [l0, l1, l2, l3]),
    (callOut Q g i S k st).2 (kDOf g.d + k + 1) dw = memOut g cb aw dw l0 l1 l2 l3 i S st.1 st.2
def MutLocalAllEntries : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q Q' : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) (g : GenIn)
    (hQ : ∀ k : Fin g.d.shape.insts.length, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1),
    genSemI Q X g = genSemI Q' X g
def MutLocalEmpty : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q Q' : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) (g : GenIn)
    (hQ : ∀ k ∈ ([] : List (Fin g.d.shape.insts.length)), Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1),
    genSemI Q X g = genSemI Q' X g
def MutCallOutLocalNoChild : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q Q' : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (hQ : ∀ (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder), g.d.shape.insts[k]? = some (c, a, κ) → Q c = Q' c),
    callOut Q g i S k st = callOut Q' g i S k st
def MutExtMemFinalStageK : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (cb : Bool) (aw dw l0 l1 l2 l3 : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (ho : originOf g.d k = InstOrigin.mem cb aw dw)
    (ha : callArgs g.d k = [l0, l1, l2, l3]) (hwf : GenWF g.d = true) (hok : g.d.ok = true),
    extOf Q g i bools bits S (kDOf g.d + k) dw =
      Tools.ShippingMachineMemLinked.memRead (D := dom i) (aw := aw) (dw := dw) cb
        ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d (ExtStage Q g i bools bits S k).1 (ExtStage Q g i bools bits S k).2 S) l0 j)⟩
        ⟨fun j => BitVec.ofNat dw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l1 j)⟩
        ⟨fun j => lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l2 j != 0⟩
        ⟨fun j => BitVec.ofNat aw (lsrcGet (lsrcAt g.d (extBOf Q g i bools bits S) (extOf Q g i bools bits S) S) l3 j)⟩
def MutMemFactsNextCall : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) (g : GenIn)
    (hok : g.d.ok = true) (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (k : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder) (hk : g.d.shape.insts[k]? = some (c, a, κ))
    (cb : Bool) (aw dw : Nat) (ho : originOf g.d k = InstOrigin.mem cb aw dw),
    let Sst := @stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGen Q X g).body i bools bits)
    Tools.ShippingMachineCallsLinkedT.MemFacts (D := dom i) g.d.shape
      ((SemPkg.gen (genSemGen Q X g)).lsrc i bools bits) g.d.ls.length (g.d.bsIn.drop (kDOf g.d)) (kDOf g.d)
      (extOf Q g i bools bits Sst) (k + 1) c
def MutLsrcCongrNoClean : Prop := ∀ (d : MachineData) (hok : d.ok = true) (k : Nat) {D : DomainConfig}
    (bs bs' : Nat → Signal D Bool) (vs vs' : (j n : Nat) → Signal D (BitVec n))
    (S : Signal D (HList (tys d.ss))) (t : Nat)
    (hb : ∀ p, p < kDOf d + k → (bs p).val t = (bs' p).val t)
    (hv : ∀ p w, p < kDOf d + k → (vs p w).val t = (vs' p w).val t),
    ∀ l, lsrcGet (lsrcAt d bs vs S) l t = lsrcGet (lsrcAt d bs' vs' S) l t
def MutLsrcCongrLate : Prop := ∀ (d : MachineData) (hok : d.ok = true) (k : Nat) {D : DomainConfig}
    (bs bs' : Nat → Signal D Bool) (vs vs' : (j n : Nat) → Signal D (BitVec n))
    (S : Signal D (HList (tys d.ss))) (t : Nat)
    (hb : ∀ p, p < kDOf d + k → (bs p).val t = (bs' p).val t)
    (hv : ∀ p w, p < kDOf d + k → (vs p w).val t = (vs' p w).val t),
    ∀ l, (cleanLets d k)[l]? = some true → lsrcGet (lsrcAt d bs vs S) l t = lsrcGet (lsrcAt d bs' vs' S) l (t + 1)
def MutNotLoopEq : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (X : Lean.Name) (g : GenIn),
  ∀ s : LoopSem ι dom, genSemI Q X g = SemPkg.loop s

/-! ## Checks -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let thms : List (Name × Name) :=
    [(``genSemI_decl, ``ExpGenSemIDecl), (``genSemI_d, ``ExpGenSemID), (``genSemI_not_loop, ``ExpGenSemINotLoop),
     (``callOut_local, ``ExpCallOutLocal), (``ExtStage_local, ``ExpExtStageLocal), (``genSemI_local, ``ExpGenSemILocal),
     (``ExtStage_zero, ``ExpExtStageZero), (``ExtStage_succ, ``ExpExtStageSucc), (``callOut_none, ``ExpCallOutNone),
     (``calleeOut_none, ``ExpCalleeOutNone), (``callOut_frame, ``ExpCallOutFrame), (``ExtStage_agree, ``ExpExtStageAgree),
     (``callOut_mem_val, ``ExpCallOutMemVal), (``lsrcAt_congr, ``ExpLsrcAtCongr),
     (``lsrcAt_genSemGen, ``ExpLsrcAtGenSemGen), (``ext_mem_final, ``ExpExtMemFinal),
     (``memFacts_of_genSem, ``ExpMemFactsOfGenSem)]
  for (t, e) in thms do checkExpected t e
  checkExpected ``typedVal_let_agree ``ExpTypedValLetAgree
  -- definitions: the TYPE of the constant against the independently written type (bodies are not compared)
  let defs : List (Name × Name) :=
    [(``ordCallees, ``ExpTyOrdCallees), (``lsrcGet, ``ExpTyLsrcGet), (``lsrcAt, ``ExpTyLsrcAt), (``selIdx, ``ExpTySelIdx),
     (``calleeOut, ``ExpTyCalleeOut), (``withCall, ``ExpTyWithCall), (``memOut, ``ExpTyMemOut), (``callOut, ``ExpTyCallOut),
     (``ExtStage, ``ExpTyExtStage), (``extBOf, ``ExpTyExtBOf), (``extOf, ``ExpTyExtOf), (``genSemGen, ``ExpTyGenSemGen),
     (``genSemComb, ``ExpTyGenSemComb), (``genSemI, ``ExpTyGenSemI), (``genSemVia, ``ExpTyGenSemVia)]
  for (c, e) in defs do
    let ci ← getConstInfo c
    let ee ← stmtOf e
    -- binder names of arrows are anonymous in the expected types, so: same binder count, same binder infos, types defeq
    let n1 ← forallTelescopeReducing ci.type fun xs _ => do
      return (← xs.mapM fun x => do return (← x.fvarId!.getBinderInfo))
    let n2 ← forallTelescopeReducing ee fun xs _ => do
      return (← xs.mapM fun x => do return (← x.fvarId!.getBinderInfo))
    unless n1 == n2 do throwError "GEN5 DEFTYPE FAILED {c}: binder count/infos differ from {e}"
    unless (← isDefEq ci.type ee) do throwError "GEN5 DEFTYPE FAILED {c}: type not defeq to {e}"
    logInfo m!"GEN5 DEFTYPE OK {c} against {e} ({n1.size} binders, binder infos equal, types defeq)"
  let mutants : List (Name × Name) :=
    [(``ExtStage_agree, ``MutAgreeLt), (``ExtStage_agree, ``MutAgreeDropBits), (``callOut_frame, ``MutFramePlus),
     (``callOut_frame, ``MutFrameDropBits), (``callOut_none, ``MutCallOutNoneNoHyp), (``callOut_mem_val, ``MutMemValPos),
     (``genSemI_local, ``MutLocalAllEntries), (``genSemI_local, ``MutLocalEmpty), (``callOut_local, ``MutCallOutLocalNoChild),
     (``ext_mem_final, ``MutExtMemFinalStageK), (``memFacts_of_genSem, ``MutMemFactsNextCall),
     (``lsrcAt_congr, ``MutLsrcCongrNoClean), (``lsrcAt_congr, ``MutLsrcCongrLate), (``genSemI_not_loop, ``MutNotLoopEq)]
  for (t, m) in mutants do checkMutant t m
  logInfo m!"GEN5 CALL COUNTS: TYPE theorems {thms.length} (freeze statements) + 1 internal helper (typedVal_let_agree); \
    definition-type checks {defs.length} (signature only); MUTANT {mutants.length} (conjunct-dropping 2, hypothesis-dropping 3, \
    one-place changes 9; signature/defeq rejections, NOT semantic counterexamples). Not covered here: typedVal_let_congr (not proved, see addendum), \
    mem_ordCallees (helper, not a freeze statement)."

run_cmd Lean.Elab.Command.liftTermElabM do
  let all : List Name :=
    [``genSemI_decl, ``genSemI_d, ``genSemI_not_loop, ``callOut_local, ``ExtStage_local, ``genSemI_local, ``ExtStage_zero,
     ``ExtStage_succ, ``callOut_none, ``calleeOut_none, ``callOut_frame, ``ExtStage_agree, ``callOut_mem_val, ``lsrcAt_congr,
     ``lsrcAt_genSemGen, ``ext_mem_final, ``memFacts_of_genSem, ``typedVal_let_agree, ``mem_ordCallees, ``ok_Kfacts,
     ``partial_agr, ``rowA_at, ``rowB_at, ``rowC_at, ``ordCallees, ``lsrcGet, ``lsrcAt, ``selIdx, ``calleeOut, ``withCall, ``memOut,
     ``callOut, ``ExtStage, ``extBOf, ``extOf, ``genSemGen, ``genSemComb, ``genSemI, ``genSemVia]
  for n in all do checkAxioms n
  logInfo m!"GEN5 CALL AXIOMS OK: {all.length} constants, standard axioms only"

/-! ## Closure audit (reuses `Tests.Gen5.SemGenCheck.closureRun`; its controls are re-run here) -/

run_cmd Lean.Elab.Command.liftTermElabM do
  for (r, want) in [(``Tests.Gen5.SemGenCheck.Ctl.direct, ``Lean.ofReduceBool), (``Tests.Gen5.SemGenCheck.Ctl.viaOpaque, ``Lean.reduceNat),
      (``Tests.Gen5.SemGenCheck.Ctl.ThirdNs.viaThm, ``Lean.ofReduceBool), (``Tests.Gen5.SemGenCheck.Ctl.ThirdNs.viaDef, ``Lean.reduceNat)] do
    let f ← detect [r]
    unless f.contains want do throwError "GEN5 CALL CONTROL FAILED: {r} not detected as reaching {want} (got {f})"
  for r in [``Tests.Gen5.SemGenCheck.Ctl.cleanThm, ``Tests.Gen5.SemGenCheck.Ctl.cleanVia, ``Tests.Gen5.SemGenCheck.Ctl.Unrelated.cleanFact] do
    let f ← detect [r]
    unless f.isEmpty do throwError "GEN5 CALL CONTROL FAILED: clean {r} falsely flagged {f}"
  -- an unknown root must THROW (never silently succeed)
  let threw ← (do let _ ← closureRun [`Tests.Gen5.SemCallCheck.NoSuchConstant]; pure false) <|> pure true
  unless threw do throwError "GEN5 CALL CONTROL FAILED: unknown constant did not throw"
  logInfo m!"GEN5 CALL CLOSURE CONTROLS OK: 4 forbidden uses detected, 3 clean roots not flagged, unknown root throws"

run_cmd Lean.Elab.Command.liftTermElabM do
  let roots : List Name :=
    [``genSemI_decl, ``genSemI_d, ``genSemI_not_loop, ``callOut_local, ``ExtStage_local, ``genSemI_local, ``ExtStage_zero,
     ``ExtStage_succ, ``callOut_none, ``calleeOut_none, ``callOut_frame, ``ExtStage_agree, ``callOut_mem_val, ``lsrcAt_congr,
     ``lsrcAt_genSemGen, ``ext_mem_final, ``memFacts_of_genSem]
  let c ← closureRun roots
  let f := forbiddenIn c
  unless f.isEmpty do throwError "GEN5 CALL CLOSURE FAILED: forbidden constants {f}"
  for n in c.seen.toList do
    let s := n.toString
    if (s.splitOn "dataOf").length > 1 || (s.splitOn "genS_some").length > 1 || (s.splitOn "native").length > 1 then
      throwError "GEN5 CALL CLOSURE FAILED: unexpected constant {n}"
  logInfo m!"GEN5 CALL CLOSURE OK: {c.seen.toList.length} constants over {roots.length} roots (thm/defn/opaque read explicitly), no forbidden/supplier constant; \
    opaque ({c.opaques.size}, logical value followed, implemented_by/extern/compiled not followed): {c.opaques}; body-less (type only): {c.bodyless.size}; unresolved: 0"

run_cmd Lean.Elab.Command.liftTermElabM do
  let reach (r : Name) (need : List Name) : MetaM Unit := do
    let c ← closureRun [r]
    for n in need do
      unless c.seen.contains n do throwError "GEN5 CALL REACH FAILED: {r} does not reach {n}"
  reach ``callOut_local [``calleeOut, ``callOut]
  reach ``ExtStage_local [``callOut_local, ``mem_ordCallees]
  reach ``genSemI_local [``ExtStage_local, ``genSemGenE]
  reach ``ExtStage_agree [``callOut_frame, ``ExtStage_succ]
  reach ``callOut_mem_val [``memOut]
  reach ``lsrcAt_congr [``typedVal_let_agree, ``cleanUpTo_full]
  reach ``typedVal_let_agree [``partial_agr]
  reach ``partial_agr [``Tools.ShippingMachineDenote.eval_congr_wf, ``slotVal_ge, ``Tools.ShippingMachineDenote.slotVal_at]
  reach ``ext_mem_final [``callOut_mem_val, ``ExtStage_agree, ``lsrcAt_congr, ``rowC_at]
  reach ``memFacts_of_genSem [``ext_mem_final, ``rowA_at, ``rowB_at, ``Tools.ShippingQuadCalls.letObsB_hl]
  logInfo m!"GEN5 CALL REACH OK: 10 reach assertions (callOut_local→calleeOut, genSemI_local→ExtStage_local, ExtStage_agree→callOut_frame, \
    lsrcAt_congr→typedVal_let_agree, ext_mem_final→callOut_mem_val+ExtStage_agree+lsrcAt_congr, memFacts_of_genSem→ext_mem_final, …)"

#print axioms ext_mem_final
#print axioms memFacts_of_genSem
#print axioms lsrcAt_congr
#print axioms genSemI_local

end Tests.Gen5.SemCallCheck
