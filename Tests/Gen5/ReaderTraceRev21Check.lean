import Tools.ShippingGen5ReaderTraceDirect2
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT yet.

/-! # DG-READERTRACE rev20 / rev21.1 checks (`Tools/Assume/ExprEqv.lean`, `Tools/ShippingGen5ReaderTraceDomKeepF.lean`, `...DomKeepS.lean`, `...Shape2.lean`, `...Direct2.lean`)

TYPE: the 7 `def`s (by VALUE) and the 14 theorems are compared by `checkExpected` against `Exp…` statements written here (own spelling), independently of the freeze `#check` text.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples). Positive and negative controls: `DomForm` on concrete terms by `rfl` / `cases`.
`EqvAtom` is an ASSUMPTION (a `Prop` def): none of this is a proof that it holds. Runtime controls evaluate the compiled `Expr.eqv` at elaboration time (not a kernel proof): the unrestricted
statement fails on an alpha-renamed lambda, and the right-atom statement agrees on sample atoms. The `EqvAtom` dependency table is computed from the declarations below (type-level and closure-level). -/

namespace Tests.Gen5.ReaderTraceRev21Check
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.Assume.ExprEqv Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingReaderFuelShapeR5
  Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover5 Tools.ShippingGen5Cover6

section Expected

def ExpDomShape : Lean.Expr → Prop := fun d =>
  (∃ i : Nat, d = Lean.Expr.fvar ⟨Lean.Name.num (Lean.Name.str Lean.Name.anonymous "_machIn") i⟩) ∨
  (∃ ls : List Lean.Level, d = Lean.Expr.const ``Sparkle.Core.Domain.defaultDomain ls)
def ExpEqvAtom : Prop := ∀ a b : Lean.Expr, DomShape b → (a == b) = true → a = b
def ExpDomForm : Lean.Expr → Prop := fun d => ∃ r, machDom? 0 d = some r
def ExpDomKeepF : Hs → Prop := fun h =>
  ∀ (c : Call) (v : c.Res), h c = some (some v) →
    ∀ d : Lean.Expr, (callSt c).dom = some d →
      ∃ d' : Lean.Expr, (callOut c v).dom = some d' ∧ (DomForm d' → d' = d)
def ExpMidInputs' : Nat → StructEnv → ShapePre → Lean.Expr → Prop := fun nDecl senv p en =>
  p.bs.length ≤ nDecl ∧
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (shapeMid senv p en).rootLets[k]? = some x →
      NoPh x.2.2 = true ∧ BvarLt (k + nDecl) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) dom = true ∧
      NoPh b = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + 1 + nDecl) b = true) ∧
  ((shapeMid senv p en).run? = none →
      NoPh (shapeMid senv p en).root = true ∧
      BvarLt ((shapeMid senv p en).rootLets.length + nDecl) (shapeMid senv p en).root = true)
def ExpShapeInputs' : Nat → StructEnv → Bool → List (String × Nat) → ConstantInfo → Nat → Prop :=
  fun nDecl senv sm ps ci n =>
  ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p → machNormF n senv p.e = some en →
    MidInputs' nDecl senv p en
def ExpNDeclOfCi : ConstantInfo → Nat := fun ci =>
  match ci with
  | .defnInfo d =>
    ((mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value)).map (fun x => x.1.length)).getD 0
  | _ => 0

def ExpDomFormShape : Prop := ∀ (d : Lean.Expr), DomForm d → DomShape d
def ExpReadFDomKeepF : Prop := ∀ (hE : EqvAtom) (senv : StructEnv) (n : Nat), DomKeepF (readF senv n)
def ExpSeq : Prop := ∀ {d d1 d2 : Lean.Expr}, (h1 : DomForm d1 → d1 = d) → (h2 : DomForm d2 → d2 = d1) →
  DomForm d2 → d2 = d
def ExpWrite : Prop := ∀ (hE : EqvAtom) {d dom' : Lean.Expr}, (hb : (d != dom') = false) → DomForm dom' → dom' = d
def ExpRootLet : Prop := ∀ (senv : StructEnv) (n : Nat) (hK : DomKeepF (readF senv n))
    (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
    {s' : List MachVal × MachRead} (hr : (shapeRootLet senv s a).run (wtab senv n) = some (some s'))
    (d : Lean.Expr) (hd : s.2.dom = some d),
    ∃ d', s'.2.dom = some d' ∧ (DomForm d' → d' = d)
def ExpRootLets : Prop := ∀ (senv : StructEnv) (n : Nat) (hK : DomKeepF (readF senv n))
    (l : List (Name × Lean.Expr × Lean.Expr)) (env : List MachVal) (st : MachRead)
      {env' : List MachVal} {st' : MachRead},
    (foldO (shapeRootLet senv) (env, st) l).run (wtab senv n) = some (some (env', st')) →
    ∀ d : Lean.Expr, st.dom = some d → ∃ d', st'.dom = some d' ∧ (DomForm d' → d' = d)
def ExpBody : Prop := ∀ (senv : StructEnv) (n : Nat) (hK : DomKeepF (readF senv n))
    (m : ShapeMid) (env : List MachVal) (st1 : MachRead) {st : MachRead} {v : Lean.Expr}
    (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v)))
    (d : Lean.Expr) (hd : st1.dom = some d),
    ∃ d', st.dom = some d' ∧ (DomForm d' → d' = d)
def ExpPost : Prop := ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr}
    {sp : MachineShape} (h : shapePost ai p m st v = some sp)
    {d : Lean.Expr} (hd : st.dom = some d), DomForm d
def ExpStart : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid)
    (hdom : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh dom = true ∧ BvarLt (m.rootLets.length + nDecl) dom = true)
    {st0 : MachRead} (hr : (shapeStart senv m).run (wtab senv n) = some (some st0))
    (hform : ∀ d : Lean.Expr, st0.dom = some d → DomForm d),
    FReachC nDecl ({} : MachRead) st0 ∧ ShapeCarry senv nDecl [] st0
def ExpReach : Prop := ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape} {nDecl : Nat} (hE : EqvAtom)
    (hT : TraceGood senv nDecl (readF senv n))
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hIn : ShapeInputs' nDecl senv sm ps ci n),
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size ∧
      FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
      TrInv senv nDecl st ∧
      ((shapeMid senv p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v)
def ExpBsLen : Prop := ∀ {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {senv : StructEnv}
    {p : ShapePre} (h : shapePre sm ps ci senv = some p), p.bs.length = nDeclOfCi ci
def ExpHbs : Prop := ∀ (sm : Bool) (ps : List (String × Nat)) (ci : Lean.ConstantInfo) (senv : StructEnv),
    ∀ p : ShapePre, shapePre sm ps ci senv = some p → p.bs.length ≤ nDeclOfCi ci
def ExpInputsOf : Prop := ∀ (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hrf : RootFloatAgrees)
    {nDecl : Nat} {senv : StructEnv} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {n : Nat}
    (hdecl : ∀ d, ci = ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true)
    (hpack : ∀ (L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
      NoPh (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true ∧
        BvarLt L (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true)
    (hnorm : ∀ (L : Nat) (e en : Lean.Expr), NoPh e = true → BvarLt L e = true → machNormF n senv e = some en →
      NoPh en = true ∧ BvarLt L en = true)
    (hbs : ∀ p : ShapePre, shapePre sm ps ci senv = some p → p.bs.length ≤ nDecl),
    ShapeInputs' nDecl senv sm ps ci n
def ExpDirect' : Prop := ∀ (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    {ci : Lean.ConstantInfo} (hci : CiDirect env ci)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {sm : Bool} {ps : List (String × Nat)} {n : Nat},
    ShapeInputs' (nDeclOfCi ci) (structEnv env) sm ps ci n

-- mutants (single changes; rejected by signature / defeq, NOT semantic counterexamples)
def MutDomShapeNoConst : Lean.Expr → Prop := fun d =>
  (∃ i : Nat, d = Lean.Expr.fvar ⟨Lean.Name.num (Lean.Name.str Lean.Name.anonymous "_machIn") i⟩)
def MutEqvAtomBoth : Prop := ∀ a b : Lean.Expr, (DomShape a ∨ DomShape b) → (a == b) = true → a = b
def MutEqvAtomLeft : Prop := ∀ a b : Lean.Expr, DomShape a → (a == b) = true → a = b
def MutEqvAtomAny : Prop := ∀ a b : Lean.Expr, (a == b) = true → a = b
def MutDomKeepFStrong : Hs → Prop := fun h =>
  ∀ (c : Call) (v : c.Res), h c = some (some v) →
    ∀ d : Lean.Expr, (callSt c).dom = some d → (callOut c v).dom = some d
def MutDomKeepFNoForm : Hs → Prop := fun h =>
  ∀ (c : Call) (v : c.Res), h c = some (some v) →
    ∀ d : Lean.Expr, (callSt c).dom = some d →
      ∃ d' : Lean.Expr, (callOut c v).dom = some d' ∧ d' = d
def MutReadFNoHE : Prop := ∀ (senv : StructEnv) (n : Nat), DomKeepF (readF senv n)
def MutSeqWithHE : Prop := ∀ (hE : EqvAtom) {d d1 d2 : Lean.Expr}, (h1 : DomForm d1 → d1 = d) → (h2 : DomForm d2 → d2 = d1) →
  DomForm d2 → d2 = d
def MutWriteRev : Prop := ∀ (hE : EqvAtom) {d dom' : Lean.Expr}, (hb : (d != dom') = false) → DomForm dom' → d = dom'
def MutWriteLeftForm : Prop := ∀ (hE : EqvAtom) {d dom' : Lean.Expr}, (hb : (d != dom') = false) → DomForm d → dom' = d
def MutReachNoHE : Prop := ∀ {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape} {nDecl : Nat}
    (hT : TraceGood senv nDecl (readF senv n))
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hIn : ShapeInputs' nDecl senv sm ps ci n),
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead), shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧ (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0)
def MutStartNoForm : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid)
    (hdom : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh dom = true ∧ BvarLt (m.rootLets.length + nDecl) dom = true)
    {st0 : MachRead} (hr : (shapeStart senv m).run (wtab senv n) = some (some st0)),
    FReachC nDecl ({} : MachRead) st0 ∧ ShapeCarry senv nDecl [] st0
def MutNDecl : ConstantInfo → Nat := fun ci =>
  match ci with
  | .defnInfo d =>
    ((mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value)).map (fun x => x.1.length)).getD 1
  | _ => 0
def MutBsLen : Prop := ∀ {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {senv : StructEnv}
    {p : ShapePre} (h : shapePre sm ps ci senv = some p), p.bs.length = nDeclOfCi ci + 1
def MutDirectNoHbsNDecl : Prop := ∀ (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    {ci : Lean.ConstantInfo} (hci : CiDirect env ci)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {sm : Bool} {ps : List (String × Nat)} {n : Nat},
    ShapeInputs' 0 (structEnv env) sm ps ci n
def MutDirectNoHla : Prop := ∀ (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    {ci : Lean.ConstantInfo} (hci : CiDirect env ci)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {sm : Bool} {ps : List (String × Nat)} {n : Nat},
    ShapeInputs' (nDeclOfCi ci) (structEnv env) sm ps ci n
def MutMidBvar : Nat → StructEnv → ShapePre → Lean.Expr → Prop := fun nDecl senv p en =>
  p.bs.length ≤ nDecl ∧
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (shapeMid senv p en).rootLets[k]? = some x →
      NoPh x.2.2 = true ∧ BvarLt (k + nDecl) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) dom = true ∧
      NoPh b = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) b = true) ∧
  ((shapeMid senv p en).run? = none →
      NoPh (shapeMid senv p en).root = true ∧
      BvarLt ((shapeMid senv p en).rootLets.length + nDecl) (shapeMid senv p en).root = true)

end Expected

-- positive / negative controls (kernel evaluation of `machDom?`)
example : DomForm (Lean.Expr.fvar ⟨.num (.str .anonymous "_machIn") 3⟩) := ⟨_, rfl⟩
example : DomForm (Lean.Expr.const ``Sparkle.Core.Domain.defaultDomain []) := ⟨_, rfl⟩
example : ¬ DomForm (Lean.Expr.bvar 0) := by rintro ⟨r, h⟩; cases h
example : ¬ DomForm (Lean.Expr.fvar ⟨.num (.str .anonymous "_machLet") 0⟩) := by rintro ⟨r, h⟩; cases h
example : ¬ DomForm (Lean.Expr.const `Nat []) := by rintro ⟨r, h⟩; cases h
example : ¬ DomForm (Lean.Expr.app (Lean.Expr.const ``Sparkle.Core.Domain.defaultDomain []) (Lean.Expr.bvar 0)) := by
  rintro ⟨r, h⟩; cases h
-- the shapes `DomForm` accepts are `DomShape` (and `DomShape` of a `DomForm` term holds)
example : DomShape (Lean.Expr.fvar ⟨.num (.str .anonymous "_machIn") 3⟩) := Or.inl ⟨3, rfl⟩
example : ¬ DomShape (Lean.Expr.bvar 0) := by rintro (⟨i, h⟩ | ⟨ls, h⟩) <;> cases h
-- `nDeclOfCi` of a non-definition is 0
example : nDeclOfCi (.axiomInfo { name := `a, levelParams := [], type := .bvar 0, isUnsafe := false }) = 0 := rfl

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``DomShape ``ExpDomShape
  checkExpected ``EqvAtom ``ExpEqvAtom
  checkExpected ``DomForm ``ExpDomForm
  checkExpected ``DomKeepF ``ExpDomKeepF
  checkExpected ``MidInputs' ``ExpMidInputs'
  checkExpected ``ShapeInputs' ``ExpShapeInputs'
  checkExpected ``nDeclOfCi ``ExpNDeclOfCi
  checkExpected ``domForm_shape ``ExpDomFormShape
  checkExpected ``readF_domKeepF ``ExpReadFDomKeepF
  checkExpected ``domKeepF_seq ``ExpSeq
  checkExpected ``domKeepF_write ``ExpWrite
  checkExpected ``shapeRootLet_domKeepF ``ExpRootLet
  checkExpected ``rootLets_domKeepF ``ExpRootLets
  checkExpected ``shapeBody_domKeepF ``ExpBody
  checkExpected ``shapePost_domForm ``ExpPost
  checkExpected ``shapeStart_trace' ``ExpStart
  checkExpected ``machineShapeF_reach' ``ExpReach
  checkExpected ``bs_len_eq ``ExpBsLen
  checkExpected ``hbs_of_nDeclOfCi ``ExpHbs
  checkExpected ``shapeInputs_of' ``ExpInputsOf
  checkExpected ``shapeInputs_of_direct' ``ExpDirect'
  logInfo m!"GEN5 REV21CHECK TYPE 21 declarations compared"
  checkMutant ``DomShape ``MutDomShapeNoConst
  checkMutant ``EqvAtom ``MutEqvAtomBoth
  checkMutant ``EqvAtom ``MutEqvAtomLeft
  checkMutant ``EqvAtom ``MutEqvAtomAny
  checkMutant ``DomKeepF ``MutDomKeepFStrong
  checkMutant ``DomKeepF ``MutDomKeepFNoForm
  checkMutant ``readF_domKeepF ``MutReadFNoHE
  checkMutant ``domKeepF_seq ``MutSeqWithHE
  checkMutant ``domKeepF_write ``MutWriteRev
  checkMutant ``domKeepF_write ``MutWriteLeftForm
  checkMutant ``machineShapeF_reach' ``MutReachNoHE
  checkMutant ``shapeStart_trace' ``MutStartNoForm
  checkMutant ``nDeclOfCi ``MutNDecl
  checkMutant ``bs_len_eq ``MutBsLen
  checkMutant ``shapeInputs_of_direct' ``MutDirectNoHbsNDecl
  checkMutant ``shapeInputs_of_direct' ``MutDirectNoHla
  checkMutant ``MidInputs' ``MutMidBvar
  logInfo m!"GEN5 REV21CHECK MUTANT 17 statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"
  logInfo m!"GEN5 REV21CHECK COUNTS: TYPE 21 / MUTANT 17 / POSITIVE+NEGATIVE examples 9"

-- runtime controls on the compiled `Expr.eqv` (elaboration-time evaluation; not a kernel proof)
run_cmd Lean.Elab.Command.liftTermElabM do
  let nat := mkConst ``Nat
  let a := mkLambda `x .default nat (mkBVar 0)
  let b := mkLambda `y .default nat (mkBVar 0)
  unless (a == b) && !(a.equal b) do
    throwError "GEN5 REV21CHECK RUNTIME CONTROL FAILED: alpha-renamed lambdas expected `==` true and structurally different"
  let fv : Lean.Expr := .fvar ⟨.num (.str .anonymous "_machIn") 2⟩
  let cs : Lean.Expr := .const ``Sparkle.Core.Domain.defaultDomain []
  let atoms := [fv, cs]
  let cands : List Lean.Expr := [fv, cs, .fvar ⟨.num (.str .anonymous "_machIn") 3⟩, .fvar ⟨.num (.str .anonymous "_machLet") 2⟩,
    .mdata {} fv, .mdata {} cs, .const ``Sparkle.Core.Domain.defaultDomain [Level.zero], .bvar 0, .app fv fv, a, b, nat]
  let mut agree : Nat := 0
  for at_ in atoms do
    for c in cands do
      if c == at_ then
        unless c.equal at_ do throwError "GEN5 REV21CHECK RUNTIME CONTROL FAILED: {c} == {at_} but not structurally equal"
      agree := agree + 1
  logInfo m!"GEN5 REV21CHECK RUNTIME CONTROLS OK: unrestricted `a == b → a = b` fails on alpha-renamed lambdas (a == b true, structurally different); right-atom statement agrees on {agree} sample pairs (compiled Expr.eqv, not a kernel proof)"

def newThms : List Name := [``DomShape, ``EqvAtom, ``DomForm, ``domForm_shape, ``DomKeepF, ``readF_domKeepF, ``domKeepF_seq,
  ``domKeepF_write, ``shapeRootLet_domKeepF, ``rootLets_domKeepF, ``shapeBody_domKeepF, ``shapePost_domForm,
  ``MidInputs', ``ShapeInputs', ``shapeStart_trace', ``machineShapeF_reach', ``nDeclOfCi, ``bs_len_eq, ``hbs_of_nDeclOfCi,
  ``shapeInputs_of', ``shapeInputs_of_direct']

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 REV21CHECK AXIOMS {newThms.length} declarations checked (standard axioms only)"

def closureRoots : List Name := newThms

/-! ## Closure audit -/

def valueOfCI : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def closureOf (env : Environment) (root : Name) : StateT (NameSet × NameSet) MetaM Unit := do
  if (← get).1.contains root then return
  modify fun (s, u) => (s.insert root, u)
  match env.find? root with
  | none => modify fun (s, u) => (s, u.insert root)
  | some ci =>
    for c in ci.type.getUsedConstants do closureOf env c
    match valueOfCI ci with
    | some v => for c in v.getUsedConstants do closureOf env c
    | none => pure ()
    match ci with
    | .inductInfo v => for c in v.ctors do closureOf env c
    | _ => pure ()

def forbiddenConsts : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]

def closureHits (env : Environment) (roots : List Name) : MetaM (NameSet × NameSet × List Name) := do
  let (_, (seen, unk)) ← (roots.forM (closureOf env)).run ({}, {})
  pure (seen, unk, forbiddenConsts.filter seen.contains)

-- Negative controls (built in memory, no `sorry` token in this file): each must be detected; clean controls must not be.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let bad := mkApp2 (mkConst ``sorryAx [Level.zero]) tru (mkConst ``Bool.false)
    let ok := mkConst ``True.intro
    addDecl (.thmDecl { name := `ReaderTraceRev21Check.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceRev21Check.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceRev21Check.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceRev21Check.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceRev21Check.direct, `ReaderTraceRev21Check.viaHelper, `ReaderTraceRev21Check.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 REV21CHECK CLOSURE CONTROL FAILED: {n} not detected"
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 REV21CHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceRev21Check.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 REV21CHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 REV21CHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceRev21Check.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceRev21Check.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceRev21Check.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceRev21Check.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceRev21Check.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceRev21Check.Missing.nowhere do throwError "GEN5 REV21CHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceRev21Check.viaHelperU, `ReaderTraceRev21Check.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceRev21Check.Missing.nowhere do throwError "GEN5 REV21CHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceRev21Check.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 REV21CHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 REV21CHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 21 do throwError "GEN5 REV21CHECK CLOSURE FAILED: expected 21 declarations"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 REV21CHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 REV21CHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 REV21CHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 REV21CHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 REV21CHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (21 declarations); all 21 target declarations in seen, no forbidden constant"

/-! ## `EqvAtom` dependency table

For each declaration of this unit: does its TYPE take `EqvAtom` (a hypothesis), and does its CLOSURE (type and value) reach `EqvAtom`? Expected: exactly `readF_domKeepF`, `domKeepF_write`,
`machineShapeF_reach'` take it in the type; the closure reaches it also through the same three (no other declaration of this unit uses it, in particular none of `shapeStart_trace'`,
`shapeInputs_of'`, `shapeInputs_of_direct'`, `domKeepF_seq`, `shapeRootLet_domKeepF`, `rootLets_domKeepF`, `shapeBody_domKeepF`, `shapePost_domForm`). -/

def eqvName : Name := ``EqvAtom
def expectedTakers : List Name := [``readF_domKeepF, ``domKeepF_write, ``machineShapeF_reach']

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut typeTakers : List Name := []
  let mut closureReach : List Name := []
  let mut rows : List String := []
  for n in newThms do
    if n == eqvName then continue
    let some ci := env.find? n | throwError "GEN5 REV21CHECK DEPTABLE FAILED: {n} unknown"
    let inType := ci.type.getUsedConstants.contains eqvName
    let (seen, _, _) ← closureHits env [n]
    let inClosure := seen.contains eqvName
    if inType then typeTakers := typeTakers ++ [n]
    if inClosure then closureReach := closureReach ++ [n]
    rows := rows ++ [s!"{n}: takes-EqvAtom-in-type={inType} closure-reaches-EqvAtom={inClosure}"]
  for r in rows do logInfo m!"GEN5 REV21CHECK DEP {r}"
  unless typeTakers == expectedTakers do throwError "GEN5 REV21CHECK DEPTABLE FAILED: type-level takers {typeTakers}, expected {expectedTakers}"
  unless closureReach == expectedTakers do throwError "GEN5 REV21CHECK DEPTABLE FAILED: closure-level reach {closureReach}, expected {expectedTakers}"
  logInfo m!"GEN5 REV21CHECK DEPTABLE OK: EqvAtom is a hypothesis of exactly {expectedTakers}; no other declaration of this unit depends on it"

end Tests.Gen5.ReaderTraceRev21Check
