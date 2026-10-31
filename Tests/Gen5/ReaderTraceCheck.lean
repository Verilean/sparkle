import Tools.ShippingGen5ReaderTrace
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in g5rt-r2 at 521b3e8a (Pod `kjob lake build Tests.Gen5.ReaderTraceCheck`, exit 0; TYPE 11 theorems + 4 defs = 15 compared, EQN 16 (NoPh 8 + BvarLt 8), MUTANT 8 statement (5 theorem + 3 def) + 4 equation, AXIOMS 11 standard, CLOSURE OK 4181 constants with 3 negative / 2 clean controls, UNKNOWN 3 negative / 1 clean; 3 intended sorry negatives print 3 warnings). Clean build is the coder's. No sorry / axiom / native_decide in source.
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
      (∀ i ∈ is, i < st.kinds.size) → (∀ y ∈ ts, TyClosed y) →
      bundleSlots dom is ts = some (e, t) →
      InRange nDecl st st.lets.size e ∧ NoLoose 0 e ∧ TyClosed t
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
  logInfo m!"GEN6 READERTRACE TYPE 11 theorems + 4 defs (phTag, NoLoose, EnvPh, DomPh)"
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
  checkMutant ``reachC_ws ``MutReachWsNoRange
  checkMutant ``bindLet_reach ``MutBindLetFReach
  for n in [``MutBvarLtLamNoSucc, ``MutBvarLtBvarLe, ``MutNoPhLetNoV, ``MutNoPhMdataTrue] do
    if (← eqnHolds n) then throwError "GEN6 EQN MUTANT ACCEPTED: {n}"
  logInfo m!"GEN6 READERTRACE MUTANT 8 statement (5 theorem + 3 def) + 4 equation: all rejected"

def allThms : List Name := [``noLoose_zero_le, ``bvarLt_mono, ``noPh_letOk, ``reachC_ws, ``reachC_letv, ``reachC_slots,
  ``envPh_mono, ``envPh_cons_val, ``bundleSlots_ph, ``convBvar_trace, ``bindLet_reach]

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
    for n in [`ReaderTraceCtl.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 READERTRACE CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 READERTRACE CLOSURE CONTROLS OK: 3 negative controls detected, 2 unrelated clean controls clean"

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
