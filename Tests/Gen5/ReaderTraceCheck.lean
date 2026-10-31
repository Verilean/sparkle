import Tools.ShippingGen5ReaderTrace
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in g5rt-r3 (Pod `kjob lake build Tests.Gen5.ReaderTraceCheck`, exit 0, 722 jobs; built at a86a33c5). TYPE 11 theorems + 5 defs = 16 compared (adds TyClosed; ExpBundleSlots now uses the independent ExpTyClosed), EQN 16 (NoPh 8 + BvarLt 8), DEFPIN 2 full-argument theorems (noPh_eq_exp, bvarLt_eq_exp) + sample comparer over 247 terms with 11 default-branch def mutants (NoPh 6 + BvarLt 5) rejected, MUTANT 10 statement (5 theorem + 5 def) + 4 equation, AXIOMS 13 standard, CLOSURE OK with 3 negative + 3 forbidden-root self-hit + 2 clean controls, UNKNOWN 3 negative / 1 clean; 3 intended sorry negatives print 3 warnings. Clean build is the coder's. No sorry / axiom / native_decide in source.
/-! # DG-READERTRACE U-R1 independent part (Tools/ShippingGen5ReaderTrace.lean) checks

TYPE: each theorem / non-recursive def of the freeze (`DG_READERTRACE_FREEZE.md` §2, `DG_READERTRACE_FREEZE_REV1.md`) is compared by the SAME comparer (`checkExpected` of `Tests/Gen3/ExpectedType.lean`)
with an `Exp…` statement written here from the freeze text (own spelling; the Tools file is not copied). Counting rule: one compared declaration = 1.
EQN: `NoPh` and `BvarLt` are structurally recursive, so their compiled values are not compared; instead each defining equation of the freeze text is stated as an `Exp…Eqn…` proposition, proved here by `rfl`
(a wrong Tools definition would fail to build), and the SAME predicate `eqnHolds` (defeq of the two sides under the equation's binders) is used for the mutants.
MUTANT: well-typed single changes only, rejected by the same comparer / `eqnHolds` (signature / defeq rejection, NOT a semantic counterexample).
CLOSURE: value-closure walk over `getUsedConstants`; unknown names throw; negatives built in memory inside `withoutModifyingEnv`
(3 intended `sorry`-based negatives, so the build prints 3 "declaration uses `sorry`" warnings). -/

namespace Tests.Gen5.ReaderTraceCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel

section Expected

def ExpPhTag : String → Bool := fun t => t == "_machIn" || t == "_machInst" || t == "_machSlot" || t == "_machLet"

def ExpNoLoose : Nat → Lean.Expr → Prop := fun d v => ∀ b, ¬ LooseOcc d v b

def ExpEnvPh : Nat → MachRead → List MachVal → Prop := fun nDecl st env =>
  (∀ v, MachVal.val v ∈ env → InRange nDecl st st.lets.size v ∧ NoLoose 0 v) ∧
  (∀ b n, MachVal.state b n ∈ env → b + n ≤ st.kinds.size)

def ExpTyClosed : Lean.Expr → Prop := fun y => (∀ tag i, ¬ MentionsPh tag i y) ∧ ExpNoLoose 0 y

def ExpDomPh : Nat → MachRead → Prop := fun nDecl st =>
  ∀ d, st.dom = some d → InRange nDecl st st.lets.size d ∧ NoLoose 0 d

-- defining equations (NoPh)
def ExpNoPhFvar : Prop := ∀ (t : String) (k : Nat), NoPh (.fvar ⟨.num (.str .anonymous t) k⟩) = !phTag t
def ExpNoPhApp : Prop := ∀ (f a : Lean.Expr), NoPh (.app f a) = (NoPh f && NoPh a)
def ExpNoPhLam : Prop := ∀ (n : Name) (t b : Lean.Expr) (bi : BinderInfo), NoPh (.lam n t b bi) = (NoPh t && NoPh b)
def ExpNoPhAll : Prop := ∀ (n : Name) (t b : Lean.Expr) (bi : BinderInfo), NoPh (.forallE n t b bi) = (NoPh t && NoPh b)
def ExpNoPhLet : Prop := ∀ (n : Name) (t v b : Lean.Expr) (nd : Bool), NoPh (.letE n t v b nd) = (NoPh t && NoPh v && NoPh b)
def ExpNoPhMdata : Prop := ∀ (m : MData) (e : Lean.Expr), NoPh (.mdata m e) = NoPh e
def ExpNoPhProj : Prop := ∀ (s : Name) (i : Nat) (e : Lean.Expr), NoPh (.proj s i e) = NoPh e
def ExpNoPhBvar : Prop := ∀ (j : Nat), NoPh (.bvar j) = true
-- defining equations (BvarLt)
def ExpBvarLtBvar : Prop := ∀ (L j : Nat), BvarLt L (.bvar j) = decide (j < L)
def ExpBvarLtApp : Prop := ∀ (L : Nat) (f a : Lean.Expr), BvarLt L (.app f a) = (BvarLt L f && BvarLt L a)
def ExpBvarLtLam : Prop := ∀ (L : Nat) (n : Name) (t b : Lean.Expr) (bi : BinderInfo), BvarLt L (.lam n t b bi) = (BvarLt L t && BvarLt (L + 1) b)
def ExpBvarLtAll : Prop := ∀ (L : Nat) (n : Name) (t b : Lean.Expr) (bi : BinderInfo), BvarLt L (.forallE n t b bi) = (BvarLt L t && BvarLt (L + 1) b)
def ExpBvarLtLet : Prop := ∀ (L : Nat) (n : Name) (t v b : Lean.Expr) (nd : Bool), BvarLt L (.letE n t v b nd) = (BvarLt L t && BvarLt L v && BvarLt (L + 1) b)
def ExpBvarLtMdata : Prop := ∀ (L : Nat) (m : MData) (e : Lean.Expr), BvarLt L (.mdata m e) = BvarLt L e
def ExpBvarLtProj : Prop := ∀ (L : Nat) (s : Name) (i : Nat) (e : Lean.Expr), BvarLt L (.proj s i e) = BvarLt L e
def ExpBvarLtConst : Prop := ∀ (L : Nat) (c : Name) (ls : List Level), BvarLt L (.const c ls) = true

theorem eqn_noPhFvar : ExpNoPhFvar := fun _ _ => rfl
theorem eqn_noPhApp : ExpNoPhApp := fun _ _ => rfl
theorem eqn_noPhLam : ExpNoPhLam := fun _ _ _ _ => rfl
theorem eqn_noPhAll : ExpNoPhAll := fun _ _ _ _ => rfl
theorem eqn_noPhLet : ExpNoPhLet := fun _ _ _ _ _ => rfl
theorem eqn_noPhMdata : ExpNoPhMdata := fun _ _ => rfl
theorem eqn_noPhProj : ExpNoPhProj := fun _ _ _ => rfl
theorem eqn_noPhBvar : ExpNoPhBvar := fun _ => rfl
theorem eqn_bvarLtBvar : ExpBvarLtBvar := fun _ _ => rfl
theorem eqn_bvarLtApp : ExpBvarLtApp := fun _ _ _ => rfl
theorem eqn_bvarLtLam : ExpBvarLtLam := fun _ _ _ _ _ => rfl
theorem eqn_bvarLtAll : ExpBvarLtAll := fun _ _ _ _ _ => rfl
theorem eqn_bvarLtLet : ExpBvarLtLet := fun _ _ _ _ _ _ => rfl
theorem eqn_bvarLtMdata : ExpBvarLtMdata := fun _ _ _ => rfl
theorem eqn_bvarLtProj : ExpBvarLtProj := fun _ _ _ _ => rfl
theorem eqn_bvarLtConst : ExpBvarLtConst := fun _ _ _ => rfl


/-! ### Independent full-argument specs of `NoPh` / `BvarLt` (every `Expr` constructor listed, no wildcard)

`noPh_eq_exp` / `bvarLt_eq_exp` are theorems over ALL arguments, so no branch of the Tools definitions (including the `| _ => true` defaults:
bvar / mvar / sort / const / lit, and every fvar whose name is not `.num (.str .anonymous t) _`) is left unpinned. -/
def ExpNoPhFn : Lean.Expr → Bool
  | .bvar _ => true
  | .fvar id => match id.name with
    | .num (.str .anonymous t) _ => !(t == "_machIn" || t == "_machInst" || t == "_machSlot" || t == "_machLet")
    | _ => true
  | .mvar _ => true
  | .sort _ => true
  | .const _ _ => true
  | .lit _ => true
  | .app f a => ExpNoPhFn f && ExpNoPhFn a
  | .lam _ t b _ => ExpNoPhFn t && ExpNoPhFn b
  | .forallE _ t b _ => ExpNoPhFn t && ExpNoPhFn b
  | .letE _ t v b _ => ExpNoPhFn t && ExpNoPhFn v && ExpNoPhFn b
  | .mdata _ e => ExpNoPhFn e
  | .proj _ _ e => ExpNoPhFn e

def ExpBvarLtFn : Nat → Lean.Expr → Bool
  | L, .bvar j => decide (j < L)
  | _, .fvar _ => true
  | _, .mvar _ => true
  | _, .sort _ => true
  | _, .const _ _ => true
  | _, .lit _ => true
  | L, .app f a => ExpBvarLtFn L f && ExpBvarLtFn L a
  | L, .lam _ t b _ => ExpBvarLtFn L t && ExpBvarLtFn (L + 1) b
  | L, .forallE _ t b _ => ExpBvarLtFn L t && ExpBvarLtFn (L + 1) b
  | L, .letE _ t v b _ => ExpBvarLtFn L t && ExpBvarLtFn L v && ExpBvarLtFn (L + 1) b
  | L, .mdata _ e => ExpBvarLtFn L e
  | L, .proj _ _ e => ExpBvarLtFn L e

theorem noPh_eq_exp : ∀ e : Lean.Expr, NoPh e = ExpNoPhFn e := by
  intro e
  induction e with
  | fvar id =>
    obtain ⟨n⟩ := id
    simp only [ExpNoPhFn]
    rcases n with _ | ⟨p, k⟩ | ⟨p, k⟩
    · simp [NoPh]
    · simp [NoPh]
    · rcases p with _ | ⟨q, t⟩ | ⟨q, t⟩
      · simp [NoPh]
      · rcases q with _ | ⟨q', t'⟩ | ⟨q', t'⟩ <;> simp [NoPh, phTag]
      · simp [NoPh]
  | app f a ihf iha => simp [NoPh, ExpNoPhFn, ihf, iha]
  | lam _ t b _ iht ihb => simp [NoPh, ExpNoPhFn, iht, ihb]
  | forallE _ t b _ iht ihb => simp [NoPh, ExpNoPhFn, iht, ihb]
  | letE _ t v b _ iht ihv ihb => simp [NoPh, ExpNoPhFn, iht, ihv, ihb]
  | mdata _ e ih => simp [NoPh, ExpNoPhFn, ih]
  | proj _ _ e ih => simp [NoPh, ExpNoPhFn, ih]
  | _ => simp [NoPh, ExpNoPhFn]

theorem bvarLt_eq_exp : ∀ (e : Lean.Expr) (L : Nat), BvarLt L e = ExpBvarLtFn L e := by
  intro e
  induction e with
  | app f a ihf iha => intro L; simp [BvarLt, ExpBvarLtFn, ihf, iha]
  | lam _ t b _ iht ihb => intro L; simp [BvarLt, ExpBvarLtFn, iht, ihb]
  | forallE _ t b _ iht ihb => intro L; simp [BvarLt, ExpBvarLtFn, iht, ihb]
  | letE _ t v b _ iht ihv ihb => intro L; simp [BvarLt, ExpBvarLtFn, iht, ihv, ihb]
  | mdata _ e ih => intro L; simp [BvarLt, ExpBvarLtFn, ih]
  | proj _ _ e ih => intro L; simp [BvarLt, ExpBvarLtFn, ih]
  | _ => intro L; simp [BvarLt, ExpBvarLtFn]

/-! ### Mutant definitions (one flag per default / fvar branch; all-`true` = faithful copy of the freeze text) -/
def NoPhM (dB dM dS dC dL dFv : Bool) : Lean.Expr → Bool
  | .bvar _ => dB
  | .mvar _ => dM
  | .sort _ => dS
  | .const _ _ => dC
  | .lit _ => dL
  | .fvar ⟨.num (.str .anonymous t) _⟩ => !phTag t
  | .fvar _ => dFv
  | .app f a => NoPhM dB dM dS dC dL dFv f && NoPhM dB dM dS dC dL dFv a
  | .lam _ t b _ => NoPhM dB dM dS dC dL dFv t && NoPhM dB dM dS dC dL dFv b
  | .forallE _ t b _ => NoPhM dB dM dS dC dL dFv t && NoPhM dB dM dS dC dL dFv b
  | .letE _ t v b _ => NoPhM dB dM dS dC dL dFv t && NoPhM dB dM dS dC dL dFv v && NoPhM dB dM dS dC dL dFv b
  | .mdata _ e => NoPhM dB dM dS dC dL dFv e
  | .proj _ _ e => NoPhM dB dM dS dC dL dFv e

def BvarLtM (dM dS dC dL dFv : Bool) : Nat → Lean.Expr → Bool
  | L, .bvar j => decide (j < L)
  | _, .mvar _ => dM
  | _, .sort _ => dS
  | _, .const _ _ => dC
  | _, .lit _ => dL
  | _, .fvar _ => dFv
  | L, .app f a => BvarLtM dM dS dC dL dFv L f && BvarLtM dM dS dC dL dFv L a
  | L, .lam _ t b _ => BvarLtM dM dS dC dL dFv L t && BvarLtM dM dS dC dL dFv (L + 1) b
  | L, .forallE _ t b _ => BvarLtM dM dS dC dL dFv L t && BvarLtM dM dS dC dL dFv (L + 1) b
  | L, .letE _ t v b _ => BvarLtM dM dS dC dL dFv L t && BvarLtM dM dS dC dL dFv L v && BvarLtM dM dS dC dL dFv (L + 1) b
  | L, .mdata _ e => BvarLtM dM dS dC dL dFv L e
  | L, .proj _ _ e => BvarLtM dM dS dC dL dFv L e

/-- sample terms: one atom of every constructor / fvar-name shape, each wrapped by every composite constructor in every position. -/
def phFv (t : String) : Lean.Expr := .fvar ⟨.num (.str .anonymous t) 0⟩
def atoms : List Lean.Expr :=
  [ .bvar 0, .bvar 1, .bvar 3, .mvar ⟨`m⟩, .sort .zero, .const `c [], .lit (.natVal 1), .lit (.strVal "s"),
    phFv "_machIn", phFv "_machInst", phFv "_machSlot", phFv "_machLet", phFv "x",
    .fvar ⟨.anonymous⟩, .fvar ⟨.str .anonymous "_machIn"⟩, .fvar ⟨.num .anonymous 2⟩,
    .fvar ⟨.num (.str (.str .anonymous "a") "_machIn") 0⟩, .fvar ⟨.num (.num (.str .anonymous "_machIn") 1) 0⟩,
    .fvar ⟨.str (.num (.str .anonymous "_machIn") 0) "z"⟩ ]
def wraps (a : Lean.Expr) : List Lean.Expr :=
  [ a, .app a (.const `c []), .app (.const `c []) a, .lam `x a (.const `c []) .default, .lam `x (.const `c []) a .default,
    .forallE `x a (.const `c []) .default, .forallE `x (.const `c []) a .default,
    .letE `x a (.const `c []) (.const `c []) false, .letE `x (.const `c []) a (.const `c []) false, .letE `x (.const `c []) (.const `c []) a false,
    .mdata {} a, .proj `S 0 a, .lam `x (.const `c []) (.lam `y (.const `c []) a .default) .default ]
def samples : List Lean.Expr := atoms.flatMap wraps

/-- the SAME comparer for the real definition and every mutant: full agreement with the independent spec on all samples (and all `L ≤ 4`). -/
def agreeNoPh (f : Lean.Expr → Bool) : Bool := samples.all fun e => f e == ExpNoPhFn e
def agreeBvarLt (f : Nat → Lean.Expr → Bool) : Bool := samples.all fun e => (List.range 5).all fun L => f L e == ExpBvarLtFn L e

-- theorems
def ExpNoLooseZeroLe : Prop := ∀ {d : Nat} {v : Lean.Expr} (h : NoLoose 0 v), NoLoose d v
def ExpBvarLtMono : Prop := ∀ {L L' : Nat} {e : Lean.Expr} (hL : L ≤ L') (h : BvarLt L e = true), BvarLt L' e = true
def ExpNoPhLetOk : Prop := ∀ (n : Nat) (e : Lean.Expr) (h : NoPh e = true), Tools.ShippingLetsReaderInv.LetOk n e = true
def ExpReachWs : Prop := ∀ {nDecl : Nat} (st : MachRead) (ws' : Array (Nat × Lean.Expr))
    (h : ∀ w ∈ ws', w.1 < st.kinds.size ∧ InRange nDecl st st.lets.size w.2), FReachC nDecl st { st with ws := ws' }
def ExpReachLetv : Prop := ∀ {nDecl : Nat} (st : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr)
    (h : InRange nDecl st st.lets.size v), FReachC nDecl st { st with lets := st.lets.push (nm, kd, v) }
def ExpReachSlots : Prop := ∀ {nDecl : Nat} (st : MachRead) (ks : List MixedGateBinder) (is : List Nat) (ns : List Name),
    FReachC nDecl st { st with kinds := st.kinds ++ ks.toArray, inits := st.inits ++ is.toArray, names := st.names ++ ns.toArray }
def ExpEnvPhMono : Prop := ∀ {nDecl : Nat} {st st' : MachRead} {env : List MachVal} (h : EnvPh nDecl st env)
    (hr : FReachC nDecl st st'), EnvPh nDecl st' env
def ExpEnvPhCons : Prop := ∀ {nDecl : Nat} {st : MachRead} {env : List MachVal} {x : Lean.Expr} (h : EnvPh nDecl st env)
    (hx : InRange nDecl st st.lets.size x) (hn : NoLoose 0 x), EnvPh nDecl st (MachVal.val x :: env)
def ExpBundleSlots : Prop := ∀ {nDecl : Nat} {st : MachRead} {dom : Lean.Expr}
    (hdom : InRange nDecl st st.lets.size dom) (hdn : NoLoose 0 dom)
    (is : List Nat) (ts : List Lean.Expr) (e t : Lean.Expr),
      (∀ i ∈ is, i < st.kinds.size) → (∀ y ∈ ts, ExpTyClosed y) →
      bundleSlots dom is ts = some (e, t) →
      InRange nDecl st st.lets.size e ∧ NoLoose 0 e ∧ ExpTyClosed t
def ExpConvBvarTrace : Prop := ∀ {nDecl : Nat} {env : List MachVal} {d j : Nat} {st : MachRead} {r : Lean.Expr × MachRead}
    (hE : EnvPh nDecl st env) (hD : DomPh nDecl st)
    (hb : BvarLt (d + env.length + nDecl) (Lean.Expr.bvar j) = true) (h : convBvar env d j st = some r),
    r.2 = st ∧ InRange nDecl st st.lets.size r.1 ∧ NoLoose d r.1
def ExpBindLetReach : Prop := ∀ {nDecl : Nat} {st : MachRead} {nm : Name} {ty v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v'),
    FReachC nDecl st { st with lets := (machBindLet nm ty v' st.lets).2 } ∧
    InRange nDecl { st with lets := (machBindLet nm ty v' st.lets).2 } (machBindLet nm ty v' st.lets).2.size
      (machBindLet nm ty v' st.lets).1 ∧
    NoLoose 0 (machBindLet nm ty v' st.lets).1

-- mutants (theorem / def statements)
def MutConvBvarNoD : Prop := ∀ {nDecl : Nat} {env : List MachVal} {d j : Nat} {st : MachRead} {r : Lean.Expr × MachRead}
    (hE : EnvPh nDecl st env) (hD : DomPh nDecl st)
    (hb : BvarLt (env.length + nDecl) (Lean.Expr.bvar j) = true) (h : convBvar env d j st = some r),
    r.2 = st ∧ InRange nDecl st st.lets.size r.1 ∧ NoLoose d r.1
def MutConvBvarNoLoose : Prop := ∀ {nDecl : Nat} {env : List MachVal} {d j : Nat} {st : MachRead} {r : Lean.Expr × MachRead}
    (hE : EnvPh nDecl st env) (hD : DomPh nDecl st)
    (hb : BvarLt (d + env.length + nDecl) (Lean.Expr.bvar j) = true) (h : convBvar env d j st = some r),
    r.2 = st ∧ InRange nDecl st st.lets.size r.1
def MutConvBvarNoRange : Prop := ∀ {nDecl : Nat} {env : List MachVal} {d j : Nat} {st : MachRead} {r : Lean.Expr × MachRead}
    (hE : EnvPh nDecl st env) (hD : DomPh nDecl st)
    (hb : BvarLt (d + env.length + nDecl) (Lean.Expr.bvar j) = true) (h : convBvar env d j st = some r),
    r.2 = st ∧ NoLoose d r.1
def MutEnvPhNoState : Nat → MachRead → List MachVal → Prop := fun nDecl st env =>
  (∀ v, MachVal.val v ∈ env → InRange nDecl st st.lets.size v ∧ NoLoose 0 v)
def MutDomPhNoLoose : Nat → MachRead → Prop := fun nDecl st =>
  ∀ d, st.dom = some d → InRange nDecl st st.lets.size d
def MutTyClosedNoLoose : Lean.Expr → Prop := fun y => ∀ tag i, ¬ MentionsPh tag i y
def MutTyClosedNoPh : Lean.Expr → Prop := fun y => NoLoose 0 y
def MutPhTagFewer : String → Bool := fun t => t == "_machIn" || t == "_machInst" || t == "_machSlot"
def MutReachWsNoRange : Prop := ∀ {nDecl : Nat} (st : MachRead) (ws' : Array (Nat × Lean.Expr)),
    FReachC nDecl st { st with ws := ws' }
def MutBindLetFReach : Prop := ∀ {nDecl : Nat} {st : MachRead} {nm : Name} {ty v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v'),
    FReach nDecl st { st with lets := (machBindLet nm ty v' st.lets).2 } ∧
    InRange nDecl { st with lets := (machBindLet nm ty v' st.lets).2 } (machBindLet nm ty v' st.lets).2.size
      (machBindLet nm ty v' st.lets).1 ∧
    NoLoose 0 (machBindLet nm ty v' st.lets).1
-- mutants (defining equations)
def MutBvarLtLamNoSucc : Prop := ∀ (L : Nat) (n : Name) (t b : Lean.Expr) (bi : BinderInfo), BvarLt L (.lam n t b bi) = (BvarLt L t && BvarLt L b)
def MutBvarLtBvarLe : Prop := ∀ (L j : Nat), BvarLt L (.bvar j) = decide (j ≤ L)
def MutNoPhLetNoV : Prop := ∀ (n : Name) (t v b : Lean.Expr) (nd : Bool), NoPh (.letE n t v b nd) = (NoPh t && NoPh b)
def MutNoPhMdataTrue : Prop := ∀ (m : MData) (e : Lean.Expr), NoPh (.mdata m e) = true

end Expected

/-- The SAME predicate for positive and negative equation checks: the two sides of the equation are defeq under its binders. -/
def eqnHolds (n : Name) : MetaM Bool := do
  let ty ← stmtOf n
  forallTelescope ty fun _ body => do
    match body.eq? with
    | some (_, a, b) => withoutModifyingState (isDefEq a b)
    | none => throwError "GEN6 CHECK FAILED: {n} is not an equation"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``noLoose_zero_le ``ExpNoLooseZeroLe
  checkExpected ``bvarLt_mono ``ExpBvarLtMono
  checkExpected ``noPh_letOk ``ExpNoPhLetOk
  checkExpected ``reachC_ws ``ExpReachWs
  checkExpected ``reachC_letv ``ExpReachLetv
  checkExpected ``reachC_slots ``ExpReachSlots
  checkExpected ``envPh_mono ``ExpEnvPhMono
  checkExpected ``envPh_cons_val ``ExpEnvPhCons
  checkExpected ``bundleSlots_ph ``ExpBundleSlots
  checkExpected ``convBvar_trace ``ExpConvBvarTrace
  checkExpected ``bindLet_reach ``ExpBindLetReach
  checkExpected ``phTag ``ExpPhTag
  checkExpected ``NoLoose ``ExpNoLoose
  checkExpected ``EnvPh ``ExpEnvPh
  checkExpected ``DomPh ``ExpDomPh
  checkExpected ``TyClosed ``ExpTyClosed
  logInfo m!"GEN6 READERTRACE TYPE 11 theorems + 5 defs (phTag, NoLoose, EnvPh, DomPh, TyClosed)"
  for n in [``ExpNoPhFvar, ``ExpNoPhApp, ``ExpNoPhLam, ``ExpNoPhAll, ``ExpNoPhLet, ``ExpNoPhMdata, ``ExpNoPhProj, ``ExpNoPhBvar,
      ``ExpBvarLtBvar, ``ExpBvarLtApp, ``ExpBvarLtLam, ``ExpBvarLtAll, ``ExpBvarLtLet, ``ExpBvarLtMdata, ``ExpBvarLtProj, ``ExpBvarLtConst] do
    unless (← eqnHolds n) do throwError "GEN6 CHECK FAILED: equation {n} does not hold by defeq"
  logInfo m!"GEN6 READERTRACE EQN 16 equations (NoPh 8 + BvarLt 8), each also proved by rfl above and re-checked by eqnHolds"
  -- mutants (same comparers; signature / defeq rejection, not semantic counterexamples)
  checkMutant ``convBvar_trace ``MutConvBvarNoD
  checkMutant ``convBvar_trace ``MutConvBvarNoLoose
  checkMutant ``convBvar_trace ``MutConvBvarNoRange
  checkMutant ``EnvPh ``MutEnvPhNoState
  checkMutant ``DomPh ``MutDomPhNoLoose
  checkMutant ``phTag ``MutPhTagFewer
  checkMutant ``TyClosed ``MutTyClosedNoLoose
  checkMutant ``TyClosed ``MutTyClosedNoPh
  checkMutant ``reachC_ws ``MutReachWsNoRange
  checkMutant ``bindLet_reach ``MutBindLetFReach
  for n in [``MutBvarLtLamNoSucc, ``MutBvarLtBvarLe, ``MutNoPhLetNoV, ``MutNoPhMdataTrue] do
    if (← eqnHolds n) then throwError "GEN6 EQN MUTANT ACCEPTED: {n}"
  logInfo m!"GEN6 READERTRACE MUTANT 10 statement (5 theorem + 5 def) + 4 equation: all rejected"

-- Definition pin, positive and negative through the SAME comparers `agreeNoPh` / `agreeBvarLt`. The theorems `noPh_eq_exp` / `bvarLt_eq_exp` cover all arguments for
-- the real definitions; the sampled comparer is what rejects mutants (a rejection by disagreement on a sample term, not a semantic counterexample to anything).
run_cmd Lean.Elab.Command.liftTermElabM do
  unless agreeNoPh NoPh do throwError "GEN6 CHECK FAILED: NoPh disagrees with the independent spec on a sample"
  unless agreeBvarLt BvarLt do throwError "GEN6 CHECK FAILED: BvarLt disagrees with the independent spec on a sample"
  unless agreeNoPh (NoPhM true true true true true true) do throwError "GEN6 CHECK FAILED: faithful NoPhM copy disagrees"
  unless agreeBvarLt (BvarLtM true true true true true) do throwError "GEN6 CHECK FAILED: faithful BvarLtM copy disagrees"
  let nm : List (String × Bool) :=
    [ ("bvar", agreeNoPh (NoPhM false true true true true true)), ("mvar", agreeNoPh (NoPhM true false true true true true)),
      ("sort", agreeNoPh (NoPhM true true false true true true)), ("const", agreeNoPh (NoPhM true true true false true true)),
      ("lit", agreeNoPh (NoPhM true true true true false true)), ("fvar-other", agreeNoPh (NoPhM true true true true true false)) ]
  for (k, ok) in nm do
    if ok then throwError "GEN6 DEF MUTANT ACCEPTED: NoPh default branch {k}"
  let bm : List (String × Bool) :=
    [ ("mvar", agreeBvarLt (BvarLtM false true true true true)), ("sort", agreeBvarLt (BvarLtM true false true true true)),
      ("const", agreeBvarLt (BvarLtM true true false true true)), ("lit", agreeBvarLt (BvarLtM true true true false true)),
      ("fvar", agreeBvarLt (BvarLtM true true true true false)) ]
  for (k, ok) in bm do
    if ok then throwError "GEN6 DEF MUTANT ACCEPTED: BvarLt default branch {k}"
  logInfo m!"GEN6 READERTRACE DEFPIN 2 full-argument theorems (noPh_eq_exp, bvarLt_eq_exp) over {samples.length} sample terms; DEFMUTANT 11 default-branch mutants (NoPh 6 + BvarLt 5) rejected"

def allThms : List Name := [``noLoose_zero_le, ``bvarLt_mono, ``noPh_letOk, ``reachC_ws, ``reachC_letv, ``reachC_slots,
  ``envPh_mono, ``envPh_cons_val, ``bundleSlots_ph, ``convBvar_trace, ``bindLet_reach, ``noPh_eq_exp, ``bvarLt_eq_exp]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in allThms do checkAxioms n

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
    addDecl (.thmDecl { name := `ReaderTraceCtl.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceCtl.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceCtl.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceCtl.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceCtl.direct, `ReaderTraceCtl.viaHelper, `ReaderTraceCtl.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 READERTRACE CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 READERTRACE CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceCtl.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 READERTRACE CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 READERTRACE CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceCtl.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceCtl.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceCtl.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceCtl.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceCtl.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceCtl.Missing.nowhere do throwError "GEN5 READERTRACE UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceCtl.viaHelperU, `ReaderTraceCtl.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceCtl.Missing.nowhere do throwError "GEN5 READERTRACE UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceCtl.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 READERTRACE UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 READERTRACE UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env allThms
  unless hits.isEmpty do throwError "GEN5 READERTRACE CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 READERTRACE CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 READERTRACE CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 READERTRACE CLOSURE OK: {seen.toList.length} constants, no forbidden constant"

end Tests.Gen5.ReaderTraceCheck
