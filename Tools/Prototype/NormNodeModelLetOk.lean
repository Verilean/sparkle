import Tools.Prototype.LiftExecLetOk

/-! # Unit LC19 (2/2): the ISOLATED lift/boolMap path of the node rewriter closed for the MODELS, without correspondence premises

BUILT (unit LC19): n1 exit 1 (name ambiguity `getD_ok`), n2 exit 0 (this file); Tests/Compiler/LiftExecAgreeTest.lean t1 exit 0.
No sorry / axiom / native_decide. `#print axioms`: [propext, Classical.choice, Quot.sound] for each theorem printed below.

`machNormLiftP`, `machNormMapP`, `machNormApLiftP`, `machNormNodeP` are the TEXT of `machNormMap.machNormLift`, `machNormMap`,
`machNormApLift`, `machNormNode` (Elab.lean) with the two partial callees `machLiftScalarN` and `machBoolMap` turned into the
parameters `lift : LiftFn`, `bm : BMFn`; `machNormNodeP_shipped` checks by `rfl` that at the shipped callees the copy IS
`machNormNode`. The `LetOk 0` proofs are the LC15 proofs, copied with `LiftScalarRange`/`BoolMapRange` generalised to
`LiftRangeP lift`/`BMRangeP bm`.
PROVED, NO PREMISE: `bmRangeP_model` (LC16's `boolMapModel` over `execLift`), `machNormNodeM_ok`: with `lift := execLift senv`,
`bm := boolMapModel (execLift senv dom [(wa, a)])` (= `machNormNodeM`), `LetOk 0 e → LetOk 0 (machNormNodeM senv e)`. It needs
neither `LiftScalarRange`/`LiftScalarCorr` nor `BoolMapRange`/`BoolMapCorr`. This is about the MODEL path, not the shipped
`machNormNode`.
PREMISE (named, NOT proved, OPEN): `NodeCorr senv`: on `LetOk 0` inputs `machNormNode senv e = machNormNodeM senv e` (the PRODUCTION
correspondence of the two shipped partial functions with their models, stated once at the node). `normNodeRange_of_corr` and
`machineShapeN_lets''_viaModel` (binder audit exact) derive `NormNodeRange` / the LC15 chain from it; that REPLACES `NormNodeRange`
(and LC15–LC17's `LiftScalarRange`/`BoolMapRange` or `…Corr`) by `NodeCorr`, it does not discharge anything about the shipped code.
Also OPEN (unchanged): `RawNodeRange` and the earlier premises. The `execNorm`/`normStep` layer still calls the shipped `machNormNode`
(it was not re-parametrised). -/

namespace Tools.Prototype.NormNodeModelLetOk
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
  Tools.Prototype.NormNodeRangeLetOk Tools.Prototype.BoolMapModelLetOk Tools.Prototype.LiftScalarModelLetOk
  Tools.Prototype.LiftExecLetOk

abbrev LiftFn := Lean.Expr → List (Nat × Lean.Expr) → Lean.Expr → Option (Nat × Lean.Expr)
abbrev BMFn := Lean.Expr → Lean.Expr → Nat → Lean.Expr → Option Lean.Expr

def BMRangeP (bm : BMFn) : Prop :=
  ∀ (dom a : Lean.Expr) (wa : Nat) (body r : Lean.Expr),
    LetOk 0 dom = true → LetOk 0 a = true → LetOk 0 body = true → bm dom a wa body = some r → LetOk 0 r = true

def machNormLiftP (lift : LiftFn) (senv : StructEnv) (dom tyA tyB a body e : Lean.Expr) : Lean.Expr :=
  match machBits? tyA, machBits? tyB with
  | some wa, some wb =>
    match lift dom [(wa, a)] body with
    -- the lambda's variable became `a`; every other leaf is a closed
    -- constant (`machLiftConst`), so `r` lives in the node's context
    | some (w, r) => if w == wb then r else e
    | none => e
  | _, _ => e

def machNormMapP (lift : LiftFn) (bm : BMFn) (senv : StructEnv) (dom tyA tyB f a : Lean.Expr) (mk : Lean.Expr → Lean.Expr)
    (e : Lean.Expr) : Lean.Expr :=
  match f with
  | .lam nm t (.app (.app (.app (.app (.const ``BitVec.extractLsb' ls) wsE) startE) lenE)
      (.bvar 0)) bi =>
    (match canonicalNatLitValue? startE with
     | some st =>
       -- a slice past the top from bit 0: the zero extension
       match canonicalNatLitValue? wsE, canonicalNatLitValue? lenE with
       | some n, some l =>
         if st == 0 && l > n then
           machConcatE dom (l - n) n (machPureE dom (l - n) (machBVLit (l - n) 0)) a
         else e
       | _, _ => e
     | none =>
       match senv.natOf startE with
       | some start =>
         mk (.lam nm t (mkApp4 (.const ``BitVec.extractLsb' ls) wsE (inlNatLit start) lenE
           (.bvar 0)) bi)
       | none => e)
  -- `map (fun x => ~~~x)` / `map BitVec.not` is `allOnes ^^^ a`
  | .lam _ _ (.app (.app (.const ``BitVec.not _) _) (.bvar 0)) _ =>
    (match machBits? tyA, machBits? tyB with
     | some w, some w' =>
       if w != w' then e else
       machSigBin ``HXor.hXor ``Sparkle.Core.Signal.instHXorSignalBitVec dom w
         (machPureE dom w (machBVLit w (2 ^ w - 1))) a
     | _, _ => e)
  | .lam _ _ (.app (.app (.app (.const ``Complement.complement _) _)
      (.app (.const ``BitVec.instComplement _) _)) (.bvar 0)) _ =>
    (match machBits? tyA, machBits? tyB with
     | some w, some w' =>
       if w != w' then e else
       machSigBin ``HXor.hXor ``Sparkle.Core.Signal.instHXorSignalBitVec dom w
         (machPureE dom w (machBVLit w (2 ^ w - 1))) a
     | _, _ => e)
  | .lam _ _ body _ =>
    (match machBits? tyA, machBits? tyB with
     | some w, some w' =>
       if w != w' then machNormLiftP lift senv dom tyA tyB a body e else
       (match machScalarBin? w body with
        | some (m, .bvar 0, c) =>
          if c.hasLooseBVars then e else
          (match machSigInst m, machLitOf senv w c with
           | some si, some l => machSigBin m si dom w a (machPureE dom w l)
           | _, _ => e)
        | some (m, c, .bvar 0) =>
          if c.hasLooseBVars then e else
          (match machSigInst m, machLitOf senv w c with
           | some si, some l => machSigBin m si dom w (machPureE dom w l) a
           | _, _ => e)
        | _ => machNormLiftP lift senv dom tyA tyB a body e)
     | some wa, none =>
       if tyB.isConstOf ``Bool then (bm dom a wa body).getD e else e
     | _, _ => e)
  | _ => e

def machNormApLiftP (lift : LiftFn) (senv : StructEnv) (e : Lean.Expr) : Lean.Expr :=
  match e with
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap _) _) _) β) _) _ =>
    ((do
      let (dom, f, args) ← machApSpine e []
      let n := args.length
      if n < 2 then none else
      -- a function that is not a lambda (`BitVec.append`): eta-expanded
      let body ← machLamBody n f <|>
        (if f.hasLooseBVars then none
         else some (mkAppN f ((List.range n).reverse.map Lean.Expr.bvar).toArray))
      let vars ← args.reverse.mapM fun (p : Lean.Expr × Lean.Expr) =>
        (machBits? p.1).map fun w => (w, p.2)
      match machBits? β with
      | some wb =>
        let (w, r) ← lift dom vars body
        if w == wb then some r else none
      | none =>
        if !β.isConstOf ``Bool then none else
        match body with
        | .app (.app (.app (.const c lsC) wE) x) y =>
          if !(c == ``BitVec.ult || c == ``BitVec.ule || c == ``BitVec.slt ||
              c == ``BitVec.sle) then none else do
          let w ← canonicalNatLitValue? wE
          let (wx, x') ← lift dom vars x
          let (wy, y') ← lift dom vars y
          if wx != w || wy != w then none else
          let bv := mkApp (.const ``BitVec []) (inlNatLit w)
          -- the canonical binder names of the `<$>`/`<*>` normaliser
          let fn := Lean.Expr.lam `x1 bv (.lam `x2 bv
            (mkApp3 (.const c lsC) (inlNatLit w) (.bvar 1) (.bvar 0)) .default) .default
          let fnT := Lean.Expr.forallE `a bv (.const ``Bool []) .default
          some (mkApp5 (.const ``Sparkle.Core.Signal.Signal.ap [.zero]) dom bv (.const ``Bool [])
            (mkApp5 (.const ``Sparkle.Core.Signal.Signal.map [.zero]) dom bv fnT fn x') y')
        | _ => none) : Option Lean.Expr).getD e
  | _ => e

def machNormNodeP (lift : LiftFn) (bm : BMFn) (senv : StructEnv) (e : Lean.Expr) : Lean.Expr :=
  match e with
  -- `Signal.lit dom x` is `Signal.pure x`
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.lit ls) ty) dom) x =>
    machNormPure senv (mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure ls) dom ty x)
  | .app (.app (.app (.const ``Sparkle.Core.Signal.Signal.pure _) _) _) _ => machNormPure senv e
  -- `~~~a` on a `BitVec` Signal is `allOnes ^^^ a` (`BitVec.not`, by definition)
  | .app (.app (.app (.const ``Complement.complement _) sigTy)
      (.app (.app (.const ``Sparkle.Core.Signal.instComplementSignalBitVec _) _) _)) a =>
    (match machSigBits? sigTy with
     | some (dom, w) =>
       machSigBin ``HXor.hXor ``Sparkle.Core.Signal.instHXorSignalBitVec dom w
         (machPureE dom w (machBVLit w (2 ^ w - 1))) a
     | none => e)
  -- `-a` on a `BitVec` Signal is `pure 0 - a` (pointwise `0 - x = -x`)
  | .app (.app (.app (.const ``Neg.neg _) sigTy)
      (.app (.app (.const ``Sparkle.Core.Signal.instNegSignalBitVec _) _) _)) a =>
    (match machSigBits? sigTy with
     | some (dom, w) =>
       machSigBin ``HSub.hSub ``Sparkle.Core.Signal.instHSubSignalBitVec dom w
         (machPureE dom w (machBVLit w 0)) a
     | none => e)
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.ap _) _) _) _) _) _ =>
    let e' := machNormAp e
    if e' == e then machNormApLiftP lift senv e else e'
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map ls) dom) tyA) tyB) f)
      a =>
    machNormMapP lift bm senv dom tyA tyB f a
      (fun f' => mkApp5 (.const ``Sparkle.Core.Signal.Signal.map ls) dom tyA tyB f' a) e
  | .app (.app (.app (.app (.app (.app (.const ``Functor.map ls)
      (.app (.const ``Sparkle.Core.Signal.Signal us) dom))
      (.app (.const ``Sparkle.Core.Signal.instFunctorSignal is) dom')) tyA) tyB) f) a =>
    machNormMapP lift bm senv dom tyA tyB f a
      (fun f' => mkApp6 (.const ``Functor.map ls)
        (.app (.const ``Sparkle.Core.Signal.Signal us) dom)
        (.app (.const ``Sparkle.Core.Signal.instFunctorSignal is) dom') tyA tyB f' a) e
  | .app (.app (.app (.app (.app (.app (.const _ _) _) _) _) _) _) _ => machNormMixed senv e
  | _ => e

section
variable {lift : LiftFn} {bm : BMFn}

theorem machNormLiftP_ok {senv : StructEnv} (hl : LiftRangeP lift) {dom tyA tyB a body e : Lean.Expr}
    (hd : LetOk 0 dom = true) (ha : LetOk 0 a = true) (hb : LetOk 0 body = true) (he : LetOk 0 e = true) :
    LetOk 0 (machNormLiftP lift senv dom tyA tyB a body e) = true := by
  unfold machNormLiftP
  split
  · split
    · rename_i r hr
      split
      · exact hl dom _ body _ r hd (by simpa using ha) hb hr
      · exact he
    · exact he
  · exact he

theorem machNormMapP_ok {senv : StructEnv} (hl : LiftRangeP lift) (hbm : BMRangeP bm)
    {dom tyA tyB f a e : Lean.Expr} {mk : Lean.Expr → Lean.Expr}
    (hmk : ∀ f', LetOk 0 f' = true → LetOk 0 (mk f') = true)
    (hd : LetOk 0 dom = true) (hf : LetOk 0 f = true) (ha : LetOk 0 a = true) (he : LetOk 0 e = true) :
    LetOk 0 (machNormMapP lift bm senv dom tyA tyB f a mk e) = true := by
  unfold machNormMapP
  split
  · rename_i nm t ls wsE startE lenE bi
    simp only [LetOk, Bool.and_eq_true] at hf
    repeat' split
    all_goals first
      | exact he
      | exact machConcatE_ok _ _ hd (machPureE_ok _ hd (machBVLit_ok _ _)) ha
      | (apply hmk; simp [mkApp4, LetOk, letOk_natLit, hf])
  · repeat' split
    all_goals first
      | exact he
      | exact machSigBin_ok hd _ _ _ (machPureE_ok _ hd (machBVLit_ok _ _)) ha
  · repeat' split
    all_goals first
      | exact he
      | exact machSigBin_ok hd _ _ _ (machPureE_ok _ hd (machBVLit_ok _ _)) ha
  · rename_i nm t body bi
    simp only [LetOk, Bool.and_eq_true] at hf
    have hbody := hf.2
    repeat' split
    all_goals first
      | exact he
      | exact machNormLiftP_ok hl hd ha hbody he
      | exact NormNodeRangeLetOk.getD_ok he (fun r hr => hbm dom a _ _ r hd ha hbody hr)
      | (obtain ⟨hx, hy⟩ := machScalarBin_ok hbody ‹machScalarBin? _ _ = some _›
         exact machSigBin_ok hd _ _ _ ha (machPureE_ok _ hd (machLitOf_ok hy ‹machLitOf _ _ _ = some _›)))
      | (obtain ⟨hx, hy⟩ := machScalarBin_ok hbody ‹machScalarBin? _ _ = some _›
         exact machSigBin_ok hd _ _ _ (machPureE_ok _ hd (machLitOf_ok hx ‹machLitOf _ _ _ = some _›)) ha)
  · exact he

theorem machNormApLiftP_ok {senv : StructEnv} (hl : LiftRangeP lift) {e : Lean.Expr}
    (he : LetOk 0 e = true) : LetOk 0 (machNormApLiftP lift senv e) = true := by
  have he0 := he
  unfold machNormApLiftP
  split
  · apply NormNodeRangeLetOk.getD_ok he0
    intro r hr
    simp only [bind, Option.bind_eq_some_iff] at hr
    obtain ⟨⟨dom, f, args⟩, hsp, hr⟩ := hr
    obtain ⟨hd, hf, hargs⟩ := machApSpine_ok _ [] he0 (by simp) hsp
    simp only at hr
    split at hr
    · cases hr
    rw [Option.bind_eq_some_iff] at hr
    obtain ⟨body, hbody, hr⟩ := hr
    have hbodyok : LetOk 0 body = true := by
      cases h : machLamBody args.length f with
      | some b =>
        simp [h] at hbody
        subst hbody
        exact machLamBody_ok _ hf h
      | none =>
        simp [h] at hbody
        obtain ⟨-, rfl⟩ := hbody
        apply letOk_mkAppN hf
        intro a ha
        rw [List.mem_reverse] at ha
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp ha
        rfl
    rw [Option.bind_eq_some_iff] at hr
    obtain ⟨vars, hvars, hr⟩ := hr
    have hvok : ∀ p ∈ vars, LetOk 0 p.2 = true := by
      intro p hp
      obtain ⟨q, hq, hqq⟩ := mapM_vars _ _ hvars p hp
      rw [hqq]
      exact (hargs q (List.mem_reverse.mp hq)).2
    split at hr
    · rw [Option.bind_eq_some_iff] at hr
      obtain ⟨⟨w0, r0⟩, hlift, hr⟩ := hr
      split at hr
      · have := Option.some.inj hr
        subst this
        exact hl dom vars body w0 r0 hd hvok hbodyok hlift
      · cases hr
    · split at hr
      · cases hr
      · split at hr
        · rename_i c lsC wE x y
          split at hr
          · cases hr
          · simp only [Option.bind_eq_some_iff] at hr
            obtain ⟨w, hw, ⟨wx, x'⟩, hx, ⟨wy, y'⟩, hy, hr⟩ := hr
            split at hr
            · cases hr
            · have := Option.some.inj hr
              subst this
              simp only [LetOk, Bool.and_eq_true] at hbodyok
              have h1 := hl dom vars x wx x' hd hvok hbodyok.1.2 hx
              have h2 := hl dom vars y wy y' hd hvok hbodyok.2 hy
              simp [mkApp5, mkApp4, mkApp3, mkApp2, mkApp, LetOk, letOk_natLit, hd, h1, h2]
        · cases hr
  · exact he0

theorem machNormNodeP_ok {senv : StructEnv} (hl : LiftRangeP lift) (hbm : BMRangeP bm)
    {e : Lean.Expr} (he : LetOk 0 e = true) : LetOk 0 (machNormNodeP lift bm senv e) = true := by
  have he0 := he
  unfold machNormNodeP
  split
  · rename_i ls ty dom x
    simp only [LetOk, Bool.and_eq_true] at he
    obtain ⟨⟨⟨-, hty⟩, hdom⟩, hx⟩ := he
    apply machNormPure_ok
    simp [mkApp3, mkApp2, mkApp, LetOk, hty, hdom, hx]
  · exact machNormPure_ok senv he0
  · rename_i sigTy _ _ a
    simp only [LetOk, Bool.and_eq_true] at he
    split
    · rename_i dom w hs
      exact machSigBin_ok (machSigBits_ok he.1.1.2 hs) _ _ _
        (machPureE_ok _ (machSigBits_ok he.1.1.2 hs) (machBVLit_ok _ _)) he.2
    · exact he0
  · rename_i sigTy _ _ a
    simp only [LetOk, Bool.and_eq_true] at he
    split
    · rename_i dom w hs
      exact machSigBin_ok (machSigBits_ok he.1.1.2 hs) _ _ _
        (machPureE_ok _ (machSigBits_ok he.1.1.2 hs) (machBVLit_ok _ _)) he.2
    · exact he0
  · have h1 := machNormAp_ok he0
    simp only
    split
    · exact machNormApLiftP_ok hl he0
    · exact h1
  · rename_i ls dom tyA tyB f a
    simp only [LetOk, Bool.and_eq_true] at he
    obtain ⟨⟨⟨⟨⟨-, hdom⟩, htyA⟩, htyB⟩, hf⟩, ha⟩ := he
    refine machNormMapP_ok hl hbm ?_ hdom hf ha he0
    intro f' hf'
    simp [mkApp5, mkApp4, mkApp3, mkApp2, mkApp, LetOk, hdom, htyA, htyB, hf', ha]
  · rename_i ls us dom is dom' tyA tyB f a
    simp only [LetOk, Bool.and_eq_true] at he
    obtain ⟨⟨⟨⟨⟨⟨-, -, hdom⟩, -, hdom'⟩, htyA⟩, htyB⟩, hf⟩, ha⟩ := he
    refine machNormMapP_ok hl hbm ?_ hdom hf ha he0
    intro f' hf'
    simp [mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkApp, LetOk, hdom, hdom', htyA, htyB, hf', ha]
  · exact machNormMixed_ok senv he0
  · exact he0

end

/-- The lift of the isolated path: the kernel-visible `execLift`. -/
def liftModel (senv : StructEnv) : LiftFn := execLift senv

/-- The boolean-map of the isolated path: LC16's `boolMapModel` at the lift `execLift senv dom [(wa, a)]`. -/
def bmModel (senv : StructEnv) : BMFn := fun dom a wa body => boolMapModel (execLift senv dom [(wa, a)]) dom body

/-- **PROVED, no premise**: the model boolean-map keeps `LetOk 0`. -/
theorem bmRangeP_model (senv : StructEnv) : BMRangeP (bmModel senv) := by
  intro dom a wa body r hd ha hb h
  exact boolMapModel_ok (execLift senv dom [(wa, a)]) hd
    (fun x w r' hx hr => execLift_ok hd (by simpa using ha) hx hr) body r hb h

/-- The isolated-path node rewriter: the text of `machNormNode` with `machLiftScalarN` := `execLift` and `machBoolMap` :=
`boolMapModel (execLift ..)`. -/
def machNormNodeM (senv : StructEnv) : Lean.Expr → Lean.Expr := machNormNodeP (liftModel senv) (bmModel senv) senv

/-- **PROVED, no correspondence premise (no `LiftScalarRange`/`LiftScalarCorr`/`BoolMapRange`/`BoolMapCorr`)**: the whole
isolated path (lift, `boolMap`, `Map`, `ApLift`, `Lift` arms of the node rewriter, with the models in place of the two partial
callees) keeps `LetOk 0`. About the MODEL only; the shipped `machNormNode` is not touched. -/
theorem machNormNodeM_ok (senv : StructEnv) {e : Lean.Expr} (he : LetOk 0 e = true) :
    LetOk 0 (machNormNodeM senv e) = true :=
  machNormNodeP_ok (liftRangeP_execLift senv) (bmRangeP_model senv) he

/-- The parametric copy, at the SHIPPED partial callees, is `machNormNode` (definitional; evidence that the copy is the same text). -/
theorem machNormNodeP_shipped (senv : StructEnv) (e : Lean.Expr) :
    machNormNodeP (machLiftScalarN senv) (fun dom a wa body => machBoolMap senv dom a wa body) senv e =
      machNormNode senv e := rfl

/-- OPEN (production correspondence; PREMISE, NOT proved): on `LetOk 0` inputs the shipped node rewriter agrees with the
isolated-path model. Agreement of the shipped `machLiftScalarN`/`machBoolMap` with `execLift`/`boolMapModel` on the calls the
rewriter makes would be a SUFFICIENT condition for it (that derivation is not written here; necessity is NOT claimed); the
correspondence itself is NOT proved, and no equation for the `partial def`s exists in the kernel (integrator wording, par/int-r39). -/
def NodeCorr (senv : StructEnv) : Prop :=
  ∀ e : Lean.Expr, LetOk 0 e = true → machNormNode senv e = machNormNodeM senv e

theorem normNodeRange_of_corr {senv : StructEnv} (hc : NodeCorr senv) : NormNodeRange senv := by
  intro e he
  rw [hc e he]
  exact machNormNodeM_ok senv he

/-- `machineShapeN_lets''_noNorm` with `NormNodeRange` replaced by the ONE production correspondence `NodeCorr`
(replacement, not a discharge). Without `NodeCorr` the isolated path is closed only for the model (`machNormNodeM_ok`). -/
theorem machineShapeN_lets''_viaModel {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange)
    (hinst1 : Inst1Range) (hsig : SigTyRange senv) (hz : ZeroLitAgrees)
    (hraw : RawNodeRange senv) (hnc : NodeCorr senv)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (hstart : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p →
      execNorm senv p.e = some en → StartDomOk senv (shapeMid senv p en))
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp :=
  machineShapeN_lets''_noNorm hroot hlift hinst1 hsig hz hraw (normNodeRange_of_corr hnc) hpe hstart h

#print axioms bmRangeP_model
#print axioms machNormNodeM_ok
#print axioms normNodeRange_of_corr
#print axioms machineShapeN_lets''_viaModel

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_lets''_viaModel
  ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ZeroLitAgrees", "RawNodeRange", "NodeCorr", "Eq",
    "StartDomOk", "Eq"])

end Tools.Prototype.NormNodeModelLetOk
