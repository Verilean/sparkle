import Tools.ShippingGen5SemExt
import Tests.Gen5.SemGenCheck
set_option autoImplicit false
-- NOT BUILT (Check of U5A-D, scripts/gen5/DG_SEM_FREEZE_P4E.md rev2; Pod build result is recorded by a comment-only commit). No sorry/axiom/native_decide.

/-! # DG-SEM units U5A-U5D checks (Tools/ShippingGen5SemExt.lean; scripts/gen5/DG_SEM_FREEZE_P4E.md §2/§3, rev2 §5)

Categories (each count is computed from the list the check iterates over, and the counting rule is stated next to it):
* TYPE   — each freeze theorem of §2.1-§2.3 against an `Exp…` statement written here from the sentences of the freeze (same binder names/infos, same
           reducible-first comparer `checkExpected` as `Tests/Gen5/SemCallCheck.lean`); one internal helper (`outs_findIdx_nodup`) is counted separately.
* DEFBODY — the 10 definitions the new theorems depend on, compared BY BODY (`cmpTele` on `ConstantInfo.value`) with `ExpBody…` written here;
           `ExtStage` (structural recursion) is compared through the statements of its two equation lemmas instead (method reported).
* MUTANT — well-typed single-change mutants (a mutant that does not elaborate is not counted), rejected by the SAME comparer. Rejection is by
           signature/defeq, NOT a semantic counterexample. No U5 statement has a conjunctive conclusion, so the "conjunct dropped" category has 0 entries;
           hypothesis-dropped and one-place changes are listed.
* AXIOMS — standard only. CLOSURE — explicit thm/defn/opaque walk (`Tests.Gen5.SemGenCheck.closureRun`), unknown name ⇒ throwError, root itself
           forbidden-checked, helper-value / helper-type negative controls (fixtures inside `withoutModifyingEnv`). REACH — listed assertions. -/

namespace Tests.Gen5.SemExtCheck
open Lean Meta Elab
open Tools.ShippingGen5Sem Tests.Gen3.ExpectedType Tests.Gen5.SemGenCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote (tys)
open Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingMachineAuto

/-! ## Expected statements -/

def ExpCallOutBoolVal : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ InstOrigin.mem cb aw dw)
    (hκ : callKind g.d k = MixedGateBinder.bool),
    (callOut Q g i S k st).1 (kDOf g.d + k) = ⟨fun τ => calleeOut Q g i S st.1 st.2 k τ != 0⟩
def ExpCallOutBitsVal : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder) (w : Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ InstOrigin.mem cb aw dw)
    (hκ : callKind g.d k = MixedGateBinder.bits w),
    (callOut Q g i S k st).2 (kDOf g.d + k) w = ⟨fun τ => BitVec.ofNat w (calleeOut Q g i S st.1 st.2 k τ)⟩
def ExpCalleeOutCongr : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs bs' : Nat → Signal (dom i) Bool) (vs vs' : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat)
    (h : ∀ l ∈ callArgs g.d k, ∀ j, lsrcGet (lsrcAt g.d bs vs S) l j = lsrcGet (lsrcAt g.d bs' vs' S) l j),
    calleeOut Q g i S bs vs k = calleeOut Q g i S bs' vs' k
def ExpCalleeOutFinal : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (hkn : k < g.d.shape.insts.length),
    calleeOut Q g i S (ExtStage Q g i bools bits S k).1 (ExtStage Q g i bools bits S k).2 k =
      calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k
def ExpExtCallFinalBool : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ InstOrigin.mem cb aw dw)
    (hκ : callKind g.d k = MixedGateBinder.bool),
    extBOf Q g i bools bits S (kDOf g.d + k) =
      ⟨fun τ => calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k τ != 0⟩
def ExpExtCallFinalBits : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder) (w : Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ InstOrigin.mem cb aw dw)
    (hκ : callKind g.d k = MixedGateBinder.bits w),
    extOf Q g i bools bits S (kDOf g.d + k) w =
      ⟨fun τ => BitVec.ofNat w (calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k τ)⟩
def ExpCallArgsOfInsts : Prop := ∀ (d : MachineData) (k : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : d.shape.insts[k]? = some (c, a, κ)), callArgs d k = a
def ExpCalleeOutEqSrc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat)
    (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder) (q : SemPkg ι dom) (k' : Nat) (f : Nat → Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hQ : Q c = some q) (hsel : selIdx g.d q k = some k')
    (hf : (q.src i (Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD)
                      (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) a))
                  (Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD)
                      (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) a)))[k']? = some f),
    calleeOut Q g i S bs vs k = f
def ExpSelIdxOfCallField : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (d : MachineData) (q : SemPkg ι dom) (k k' : Nat)
    (o : Sparkle.IR.Machine.OutField) (ho : q.d.shape.layout.outs[k']? = some o)
    (hcf : if d.shape.instFields = [] then q.d.shape.layout.outs = [o] else o.name = d.shape.instFields.getD k "")
    (hnd : d.shape.instFields ≠ [] → (q.d.shape.layout.outs.map (·.name)).Nodup),
    selIdx d q k = some k'
/-- internal helper (not a freeze statement) -/
def ExpOutsFindIdxNodup : Prop := ∀ (l : List Sparkle.IR.Machine.OutField) (n : String) (k' : Nat)
    (o : Sparkle.IR.Machine.OutField) (hnd : (l.map (·.name)).Nodup) (ho : l[k']? = some o) (hn : o.name = n),
    l.findIdx? (·.name = n) = some k'

/-! ## Expected bodies (independent of the implementation text; ExtStage via equation statements) -/

noncomputable section
def ExpBodyCallArgs := fun (d : MachineData) (k : Nat) => ((d.shape.insts.map (·.2.1))[k]?).getD []
def ExpBodyCallKind := fun (d : MachineData) (k : Nat) => (((d.bsIn.drop (kDOf d))[k]?).map (·.2)).getD MixedGateBinder.domain
def ExpBodyOriginOf := fun (d : MachineData) (k : Nat) => d.shape.instOrigins.getD k InstOrigin.ord
def ExpBodySelIdx := fun {ι : Type} {dom : ι → DomainConfig} (d : MachineData) (q : SemPkg ι dom) (k : Nat) =>
  if d.shape.instFields = [] then (if q.d.shape.layout.outs.length = 1 then some 0 else none)
  else q.d.shape.layout.outs.findIdx? (·.name = d.shape.instFields.getD k "")
def ExpBodyCalleeOut := fun {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat) =>
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
def ExpBodyWithCall := fun {ι : Type} {dom : ι → DomainConfig} (g : GenIn) (i : ι) (k : Nat) (κ : MixedGateBinder) (f : Nat → Nat)
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) =>
  match κ with
  | MixedGateBinder.bool   => (fun p => if p = kDOf g.d + k then (⟨fun τ => f τ != 0⟩ : Signal (dom i) Bool) else bs p, vs)
  | MixedGateBinder.bits _ => (bs, fun p n => if p = kDOf g.d + k then (⟨fun τ => BitVec.ofNat n (f τ)⟩ : Signal (dom i) (BitVec n)) else vs p n)
  | MixedGateBinder.domain => (bs, vs)
def ExpBodyCallOut := fun {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))) =>
  match g.d.shape.insts[k]? with
  | none => st
  | some _ =>
    match originOf g.d k with
    | InstOrigin.mem cb aw dw =>
      match callArgs g.d k with
      | [l0, l1, l2, l3] =>
          (st.1, fun p n => if p = kDOf g.d + k then
                              (if h : dw = n then h ▸ memOut g cb aw dw l0 l1 l2 l3 i S st.1 st.2 else ⟨fun _ => 0⟩)
                            else st.2 p n)
      | _ => st
    | _ => withCall g i k (callKind g.d k) (calleeOut Q g i S st.1 st.2 k) st.1 st.2
def ExpBodyExtBOf := fun {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n)) (S : Signal (dom i) (HList (tys g.d.ss))) =>
  (ExtStage Q g i bools bits S g.d.shape.insts.length).1
def ExpBodyExtOf := fun {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n)) (S : Signal (dom i) (HList (tys g.d.ss))) =>
  (ExtStage Q g i bools bits S g.d.shape.insts.length).2
end

/-- `ExtStage` equation statements (replace the body comparison of the recursive definition) -/
def ExpExtStageEq0 : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))), ExtStage Q g i bools bits S 0 = (bools, bits)
def ExpExtStageEqSucc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (n : Nat),
    ExtStage Q g i bools bits S (n + 1) = callOut Q g i S n (ExtStage Q g i bools bits S n)

/-! ## Mutants (each well typed; one change, or one hypothesis dropped) -/

def MutBoolValNoHno : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hκ : callKind g.d k = MixedGateBinder.bool),
    (callOut Q g i S k st).1 (kDOf g.d + k) = ⟨fun τ => calleeOut Q g i S st.1 st.2 k τ != 0⟩
def MutBoolValEqZero : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ InstOrigin.mem cb aw dw)
    (hκ : callKind g.d k = MixedGateBinder.bool),
    (callOut Q g i S k st).1 (kDOf g.d + k) = ⟨fun τ => calleeOut Q g i S st.1 st.2 k τ == 0⟩
def MutBoolValPos : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ InstOrigin.mem cb aw dw)
    (hκ : callKind g.d k = MixedGateBinder.bool),
    (callOut Q g i S k st).1 (kDOf g.d) = ⟨fun τ => calleeOut Q g i S st.1 st.2 k τ != 0⟩
def MutBitsValKindBool : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder) (w : Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ InstOrigin.mem cb aw dw)
    (hκ : callKind g.d k = MixedGateBinder.bool),
    (callOut Q g i S k st).2 (kDOf g.d + k) w = ⟨fun τ => BitVec.ofNat w (calleeOut Q g i S st.1 st.2 k τ)⟩
def MutBitsValNoHno : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder) (w : Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hκ : callKind g.d k = MixedGateBinder.bits w),
    (callOut Q g i S k st).2 (kDOf g.d + k) w = ⟨fun τ => BitVec.ofNat w (calleeOut Q g i S st.1 st.2 k τ)⟩
def MutCongrNoH : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs bs' : Nat → Signal (dom i) Bool) (vs vs' : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat),
    calleeOut Q g i S bs vs k = calleeOut Q g i S bs' vs' k
def MutCongrNextArgs : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs bs' : Nat → Signal (dom i) Bool) (vs vs' : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat)
    (h : ∀ l ∈ callArgs g.d (k + 1), ∀ j, lsrcGet (lsrcAt g.d bs vs S) l j = lsrcGet (lsrcAt g.d bs' vs' S) l j),
    calleeOut Q g i S bs vs k = calleeOut Q g i S bs' vs' k
def MutFinalStageSucc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (hkn : k < g.d.shape.insts.length),
    calleeOut Q g i S (ExtStage Q g i bools bits S (k + 1)).1 (ExtStage Q g i bools bits S (k + 1)).2 k =
      calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k
def MutFinalNoBound : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat),
    calleeOut Q g i S (ExtStage Q g i bools bits S k).1 (ExtStage Q g i bools bits S k).2 k =
      calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k
def MutFinalBoolPos : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ InstOrigin.mem cb aw dw)
    (hκ : callKind g.d k = MixedGateBinder.bool),
    extBOf Q g i bools bits S (kDOf g.d + k + 1) =
      ⟨fun τ => calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k τ != 0⟩
def MutFinalBoolNoHno : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hκ : callKind g.d k = MixedGateBinder.bool),
    extBOf Q g i bools bits S (kDOf g.d + k) =
      ⟨fun τ => calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k τ != 0⟩
def MutFinalBitsNoHno : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder) (w : Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hκ : callKind g.d k = MixedGateBinder.bits w),
    extOf Q g i bools bits S (kDOf g.d + k) w =
      ⟨fun τ => BitVec.ofNat w (calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k τ)⟩
def MutFinalBitsStageK : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder) (w : Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ InstOrigin.mem cb aw dw)
    (hκ : callKind g.d k = MixedGateBinder.bits w),
    extOf Q g i bools bits S (kDOf g.d + k) w =
      ⟨fun τ => BitVec.ofNat w (calleeOut Q g i S (ExtStage Q g i bools bits S k).1 (ExtStage Q g i bools bits S k).2 k τ)⟩
def MutCallArgsNext : Prop := ∀ (d : MachineData) (k : Nat) (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : d.shape.insts[k]? = some (c, a, κ)), callArgs d (k + 1) = a
def MutEqSrcNoSel : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat)
    (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder) (q : SemPkg ι dom) (k' : Nat) (f : Nat → Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hQ : Q c = some q)
    (hf : (q.src i (Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD)
                      (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) a))
                  (Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD)
                      (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) a)))[k']? = some f),
    calleeOut Q g i S bs vs k = f
def MutEqSrcIdxSucc : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat)
    (c : Lean.Name) (a : List Nat) (κ : MixedGateBinder) (q : SemPkg ι dom) (k' : Nat) (f : Nat → Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hQ : Q c = some q) (hsel : selIdx g.d q k = some k')
    (hf : (q.src i (Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD)
                      (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) a))
                  (Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD)
                      (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) a)))[k' + 1]? = some f),
    calleeOut Q g i S bs vs k = f
def MutSelIdxNoNodup : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (d : MachineData) (q : SemPkg ι dom) (k k' : Nat)
    (o : Sparkle.IR.Machine.OutField) (ho : q.d.shape.layout.outs[k']? = some o)
    (hcf : if d.shape.instFields = [] then q.d.shape.layout.outs = [o] else o.name = d.shape.instFields.getD k ""),
    selIdx d q k = some k'
def MutSelIdxNodupEmpty : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (d : MachineData) (q : SemPkg ι dom) (k k' : Nat)
    (o : Sparkle.IR.Machine.OutField) (ho : q.d.shape.layout.outs[k']? = some o)
    (hcf : if d.shape.instFields = [] then q.d.shape.layout.outs = [o] else o.name = d.shape.instFields.getD k "")
    (hnd : d.shape.instFields = [] → (q.d.shape.layout.outs.map (·.name)).Nodup),
    selIdx d q k = some k'
def MutSelIdxZero : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (d : MachineData) (q : SemPkg ι dom) (k k' : Nat)
    (o : Sparkle.IR.Machine.OutField) (ho : q.d.shape.layout.outs[k']? = some o)
    (hcf : if d.shape.instFields = [] then q.d.shape.layout.outs = [o] else o.name = d.shape.instFields.getD k "")
    (hnd : d.shape.instFields ≠ [] → (q.d.shape.layout.outs.map (·.name)).Nodup),
    selIdx d q k = some 0
-- definition-body mutants
noncomputable section
def MutBodySelIdxLenTwo := fun {ι : Type} {dom : ι → DomainConfig} (d : MachineData) (q : SemPkg ι dom) (k : Nat) =>
  if d.shape.instFields = [] then (if q.d.shape.layout.outs.length = 2 then some 0 else none)
  else q.d.shape.layout.outs.findIdx? (·.name = d.shape.instFields.getD k "")
def MutBodyCallKindNoDrop := fun (d : MachineData) (k : Nat) => (((d.bsIn)[k]?).map (·.2)).getD MixedGateBinder.domain
def MutBodyExtOfLenSucc := fun {ι : Type} {dom : ι → DomainConfig} (Q : Lean.Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n)) (S : Signal (dom i) (HList (tys g.d.ss))) =>
  (ExtStage Q g i bools bits S (g.d.shape.insts.length + 1)).2
def MutBodyWithCallBoolNoShift := fun {ι : Type} {dom : ι → DomainConfig} (g : GenIn) (i : ι) (k : Nat) (κ : MixedGateBinder) (f : Nat → Nat)
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) =>
  match κ with
  | MixedGateBinder.bool   => (fun p => if p = kDOf g.d then (⟨fun τ => f τ != 0⟩ : Signal (dom i) Bool) else bs p, vs)
  | MixedGateBinder.bits _ => (bs, fun p n => if p = kDOf g.d + k then (⟨fun τ => BitVec.ofNat n (f τ)⟩ : Signal (dom i) (BitVec n)) else vs p n)
  | MixedGateBinder.domain => (bs, vs)
end

/-! ## Checks -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let thms : List (Name × Name) :=
    [(``callOut_bool_val, ``ExpCallOutBoolVal), (``callOut_bits_val, ``ExpCallOutBitsVal), (``calleeOut_congr, ``ExpCalleeOutCongr),
     (``calleeOut_final, ``ExpCalleeOutFinal), (``ext_call_final_bool, ``ExpExtCallFinalBool),
     (``ext_call_final_bits, ``ExpExtCallFinalBits), (``callArgs_of_insts, ``ExpCallArgsOfInsts),
     (``calleeOut_eq_src, ``ExpCalleeOutEqSrc), (``selIdx_of_callField, ``ExpSelIdxOfCallField)]
  for (t, e) in thms do checkExpected t e
  checkExpected ``outs_findIdx_nodup ``ExpOutsFindIdxNodup
  -- DEFBODY: compare `ConstantInfo.value` binder by binder (same comparer); ExtStage by its two equation statements
  let bodies : List (Name × Name) :=
    [(``callArgs, ``ExpBodyCallArgs), (``callKind, ``ExpBodyCallKind), (``originOf, ``ExpBodyOriginOf), (``selIdx, ``ExpBodySelIdx),
     (``calleeOut, ``ExpBodyCalleeOut), (``withCall, ``ExpBodyWithCall), (``callOut, ``ExpBodyCallOut),
     (``extBOf, ``ExpBodyExtBOf), (``extOf, ``ExpBodyExtOf)]
  for (c, e) in bodies do
    let a ← stmtOf c
    let x ← stmtOf e
    cmpTele s!"{c} (body)" a x
    logInfo m!"GEN5 EXT DEFBODY OK {c} against {e} (body compared)"
  checkExpected ``ExtStage_zero ``ExpExtStageEq0
  checkExpected ``ExtStage_succ ``ExpExtStageEqSucc
  logInfo m!"GEN5 EXT DEFBODY OK ExtStage by equation statements ExtStage_zero/ExtStage_succ (structural recursion; body not compared)"
  let bodyMut : List (Name × Name) :=
    [(``selIdx, ``MutBodySelIdxLenTwo), (``callKind, ``MutBodyCallKindNoDrop), (``extOf, ``MutBodyExtOfLenSucc),
     (``withCall, ``MutBodyWithCallBoolNoShift)]
  for (c, m) in bodyMut do
    let a ← stmtOf c
    let x ← stmtOf m
    let accepted ← withoutModifyingState do
      try cmpTele s!"{c} (body) vs {m}" a x; pure true catch _ => pure false
    if accepted then throwError "GEN5 EXT BODY MUTANT ACCEPTED: {m} matches {c}"
    logInfo m!"GEN5 EXT BODY MUTANT REJECTED {m} (against {c})"
  let mutants : List (Name × Name) :=
    [(``callOut_bool_val, ``MutBoolValNoHno), (``callOut_bool_val, ``MutBoolValEqZero), (``callOut_bool_val, ``MutBoolValPos),
     (``callOut_bits_val, ``MutBitsValKindBool), (``callOut_bits_val, ``MutBitsValNoHno),
     (``calleeOut_congr, ``MutCongrNoH), (``calleeOut_congr, ``MutCongrNextArgs),
     (``calleeOut_final, ``MutFinalStageSucc), (``calleeOut_final, ``MutFinalNoBound),
     (``ext_call_final_bool, ``MutFinalBoolPos), (``ext_call_final_bool, ``MutFinalBoolNoHno),
     (``ext_call_final_bits, ``MutFinalBitsNoHno), (``ext_call_final_bits, ``MutFinalBitsStageK),
     (``callArgs_of_insts, ``MutCallArgsNext),
     (``calleeOut_eq_src, ``MutEqSrcNoSel), (``calleeOut_eq_src, ``MutEqSrcIdxSucc),
     (``selIdx_of_callField, ``MutSelIdxNoNodup), (``selIdx_of_callField, ``MutSelIdxNodupEmpty),
     (``selIdx_of_callField, ``MutSelIdxZero)]
  for (t, m) in mutants do checkMutant t m
  logInfo m!"GEN5 EXT COUNTS: TYPE {thms.length} freeze theorems + 1 internal helper (outs_findIdx_nodup); \
    DEFBODY {bodies.length} by body + 1 (ExtStage) by equation statements = {bodies.length + 1} of the 10 dependent definitions; \
    MUTANT {mutants.length} theorem mutants (conclusion-conjunct dropped 0 (no conjunctive conclusion), hypothesis dropped 8, one-place changes 11) + {bodyMut.length} definition-body mutants; \
    signature/defeq rejections, NOT semantic counterexamples."

run_cmd Lean.Elab.Command.liftTermElabM do
  let all : List Name :=
    [``callOut_bool_val, ``callOut_bits_val, ``calleeOut_congr, ``calleeOut_final, ``ext_call_final_bool, ``ext_call_final_bits,
     ``callArgs_of_insts, ``calleeOut_eq_src, ``outs_findIdx_nodup, ``selIdx_of_callField]
  for n in all do checkAxioms n
  logInfo m!"GEN5 EXT AXIOMS OK: {all.length} constants (all U5A-D theorems), standard axioms only"

/-! ## Closure audit -/

/-- Unchecked declaration insertion, used ONLY inside `withoutModifyingEnv` for the invalid negative fixtures. -/
def addUnchecked (decl : Declaration) : CoreM Unit := do
  match (← getEnv).addDeclCore 0 decl none (doCheck := false) with
  | .ok env => setEnv env
  | .error _ => throwError "GEN5 EXT FIXTURE: could not add the fixture declaration"

def Ctl2 : Name := `Tests.Gen5.SemExtCheck.Ctl2

/-- The fixtures. `Mv`/`Mt` (and `Mc` for the clean control) are NEVER declared in the live environment; they are named in fixture
declarations only. Path of (3): `R3 → Hv`, `Hv`'s VALUE mentions `Mv`. Path of (4): `R4 → Hv4`, `Hv4`'s TYPE mentions `Mt` and nothing
else does (`R4`'s own type is `True`, its value mentions only `Hv4`, `Hv4`'s value is `True.intro`). -/
def withFixtures {α : Type} (act : Name → Name → Name → Name → Name → Name → MetaM α) : MetaM α := withoutModifyingEnv do
  let n (s : String) : Name := Ctl2 ++ Name.mkSimple s
  let tr := mkConst ``True
  let mk (nm : Name) (ty val : Expr) : Declaration :=
    .thmDecl { name := nm, levelParams := [], type := ty, value := val }
  let mkd (nm : Name) (ty val : Expr) : Declaration :=
    .defnDecl { name := nm, levelParams := [], type := ty, value := val, hints := .opaque, safety := .safe }
  -- (3) helper value
  addUnchecked (mkd (n "Hv") tr (mkConst (n "Mv")))
  addUnchecked (mk (n "R3") tr (mkConst (n "Hv")))
  -- (4) helper type
  addUnchecked (mk (n "Hv4") (mkConst (n "Mt")) (mkConst ``True.intro))
  addUnchecked (mk (n "R4") tr (mkConst (n "Hv4")))
  -- (5) clean control: same shape, the helper's type mentions a declared constant
  addUnchecked (mkd (n "Mc") (.sort (.succ .zero)) tr)
  addUnchecked (mk (n "Hc") (mkConst (n "Mc")) (mkConst ``True.intro))
  addUnchecked (mk (n "Rc") tr (mkConst (n "Hc")))
  act (n "R3") (n "R4") (n "Rc") (n "Mv") (n "Mt") (n "Hv4")

run_cmd Lean.Elab.Command.liftTermElabM do
  -- forbidden-constant controls of 1258f07e, re-run
  for (r, want) in [(``Tests.Gen5.SemGenCheck.Ctl.direct, ``Lean.ofReduceBool), (``Tests.Gen5.SemGenCheck.Ctl.viaOpaque, ``Lean.reduceNat),
      (``Tests.Gen5.SemGenCheck.Ctl.ThirdNs.viaThm, ``Lean.ofReduceBool), (``Tests.Gen5.SemGenCheck.Ctl.ThirdNs.viaDef, ``Lean.reduceNat)] do
    let f ← detect [r]
    unless f.contains want do throwError "GEN5 EXT CONTROL FAILED: {r} not detected as reaching {want} (got {f})"
  for r in [``Tests.Gen5.SemGenCheck.Ctl.cleanThm, ``Tests.Gen5.SemGenCheck.Ctl.cleanVia, ``Tests.Gen5.SemGenCheck.Ctl.Unrelated.cleanFact] do
    let f ← detect [r]
    unless f.isEmpty do throwError "GEN5 EXT CONTROL FAILED: clean {r} falsely flagged {f}"
  -- the ROOT itself is forbidden-checked
  for r in [``Lean.ofReduceBool, ``sorryAx] do
    let f ← detect [r]
    unless f.contains r do throwError "GEN5 EXT CONTROL FAILED: forbidden root {r} not flagged (got {f})"
  -- (1) unknown ROOT throws
  let t1 ← (do let _ ← closureRun [`Tests.Gen5.SemExtCheck.NoSuchConstant]; pure false) <|> pure true
  unless t1 do throwError "GEN5 EXT CONTROL FAILED: unknown root did not throw"
  -- (3)(4)(5): fixtures only inside withoutModifyingEnv
  withFixtures fun r3 r4 rc mv mt hv4 => do
    let env ← getEnv
    -- (3) unknown helper VALUE: R3 → Hv → value ∋ Mv ; R3 itself names neither Mv nor Mt
    let ci3 := env.find? r3 |>.get!
    if ci3.type.getUsedConstants.contains mv || ci3.value!.getUsedConstants.contains mv then
      throwError "GEN5 EXT FIXTURE: R3 must not mention Mv directly"
    let msg3 ← (do let _ ← closureRun [r3]; pure "") <|> (do pure "THROWN")
    unless msg3 == "THROWN" do throwError "GEN5 EXT CONTROL FAILED: unknown helper value did not throw"
    let (_, c3) ← (closureOf env r3).run {}
    unless c3.missing == #[mv] do throwError "GEN5 EXT CONTROL FAILED: helper-value case reported {c3.missing}, intended {mv}"
    unless c3.seen.contains (Ctl2 ++ `Hv) do throwError "GEN5 EXT CONTROL FAILED: helper-value path does not pass through Hv"
    -- (4) unknown helper TYPE: R4 → Hv4 → type ∋ Mt ; neither R4 (type/value) nor Hv4's value mention Mt
    let ci4 := env.find? r4 |>.get!
    let h4 := env.find? hv4 |>.get!
    if ci4.type.getUsedConstants.contains mt || ci4.value!.getUsedConstants.contains mt || h4.value!.getUsedConstants.contains mt then
      throwError "GEN5 EXT FIXTURE: only Hv4's TYPE may mention Mt"
    unless h4.type.getUsedConstants.contains mt do throwError "GEN5 EXT FIXTURE: Hv4's type must mention Mt"
    let t4 ← (do let _ ← closureRun [r4]; pure false) <|> pure true
    unless t4 do throwError "GEN5 EXT CONTROL FAILED: unknown helper type did not throw"
    let (_, c4) ← (closureOf env r4).run {}
    unless c4.missing == #[mt] do throwError "GEN5 EXT CONTROL FAILED: helper-type case reported {c4.missing}, intended {mt}"
    unless c4.seen.contains hv4 do throwError "GEN5 EXT CONTROL FAILED: helper-type path does not pass through Hv4"
    -- (5) clean control with the same shape passes
    let cc ← closureRun [rc]
    unless cc.missing.isEmpty && (forbiddenIn cc).isEmpty do throwError "GEN5 EXT CONTROL FAILED: clean fixture flagged"
  -- the fixtures did not leak
  if (← getEnv).contains (Ctl2 ++ `R3) then throwError "GEN5 EXT CONTROL FAILED: fixture leaked into the environment"
  logInfo m!"GEN5 EXT CLOSURE CONTROLS OK: 4 forbidden uses detected, 3 clean roots, 2 forbidden roots flagged (root itself checked), \
    unknown root throws, unknown helper VALUE throws naming the intended Mv via R3→Hv, unknown helper TYPE throws naming the intended Mt via R4→Hv4 (type only), \
    clean fixture passes; invalid fixtures lived only inside withoutModifyingEnv"

run_cmd Lean.Elab.Command.liftTermElabM do
  let roots : List Name :=
    [``callOut_bool_val, ``callOut_bits_val, ``calleeOut_congr, ``calleeOut_final, ``ext_call_final_bool, ``ext_call_final_bits,
     ``callArgs_of_insts, ``calleeOut_eq_src, ``outs_findIdx_nodup, ``selIdx_of_callField]
  let c ← closureRun roots
  let f := forbiddenIn c
  unless f.isEmpty do throwError "GEN5 EXT CLOSURE FAILED: forbidden constants {f}"
  for n in c.seen.toList do
    let s := n.toString
    if (s.splitOn "dataOf").length > 1 || (s.splitOn "genS_some").length > 1 || (s.splitOn "native").length > 1 then
      throwError "GEN5 EXT CLOSURE FAILED: unexpected constant {n}"
  logInfo m!"GEN5 EXT CLOSURE OK: {c.seen.toList.length} constants over {roots.length} roots (thm/defn/opaque read explicitly), no forbidden/supplier constant; \
    opaque ({c.opaques.size}): {c.opaques}; body-less (type only): {c.bodyless.size}; unresolved: 0"

run_cmd Lean.Elab.Command.liftTermElabM do
  let reach (r : Name) (need : List Name) : MetaM Unit := do
    let c ← closureRun [r]
    for n in need do
      unless c.seen.contains n do throwError "GEN5 EXT REACH FAILED: {r} does not reach {n}"
  reach ``ext_call_final_bool [``callOut_bool_val, ``calleeOut_final, ``ExtStage_agree]
  reach ``ext_call_final_bits [``callOut_bits_val, ``calleeOut_final, ``ExtStage_agree]
  reach ``calleeOut_final [``lsrcAt_congr, ``rowC_at, ``calleeOut_congr]
  reach ``calleeOut_eq_src [``calleeOut, ``callArgs_of_insts, ``selIdx]
  reach ``selIdx_of_callField [``selIdx]
  reach ``callOut_bool_val [``callOut, ``withCall]
  logInfo m!"GEN5 EXT REACH OK: 6 reach assertions (ext_call_final_bool/bits, calleeOut_final, calleeOut_eq_src, selIdx_of_callField, callOut_bool_val); 14 required constants checked"

#print axioms ext_call_final_bool
#print axioms ext_call_final_bits
#print axioms calleeOut_eq_src
#print axioms selIdx_of_callField

end Tests.Gen5.SemExtCheck
