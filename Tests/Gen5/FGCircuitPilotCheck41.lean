import Tools.ShippingFGCircuitS2iRun
import Tools.ShippingFGCircuitS2pValHead
import Tools.ShippingFGCircuitS2qBits
set_option autoImplicit false
-- FG circuit pilot S2u check (light, small run_cmd blocks). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §45.

/-! # FGCircuitPilotCheck41 — fixed expected types

`deriveRootT` takes the declared type of the generated theorem from `inferType` of its own body, so the kernel accepting the theorem says nothing about WHICH input / WHICH result it is about.
This check closes that gap. For every example:
* the generator derives the theorem `T` from the input `Expr` (as in Check29/36/38);
* the EXPECTED type is written here by hand, independently of the generator: the input `Expr` is quoted again with the raw `Lean.Expr` constructors (not `appN`, not `toExpr`, not the generator's quote cache),
  the result type `α` and the result value `v` are ordinary Lean terms;
  `∀ env (hΔ : EnvDefs env T.Delta) (hΓ : EnvCtors env T.Gamma) (hrec : RecFact env), DT env [] <input> (Res.val α v)`;
* the KERNEL (`Environment.addDeclCore`, synchronous) is asked to accept `theorem T_fixed : <expected type> := T`. A type mismatch is a kernel error.
`fixed_dt accept` must be accepted, `fixed_dt reject` must be refused by the kernel with a type mismatch (and no declaration is added). The positive and the negative cases go through the SAME command, the same
kernel call, and the same report text; a negative control differs from a positive one only in the expected input / result / captured environment.
α-equivalence: the generator's quote cache is keyed by `Expr` equality that ignores binder names; the accepted wrappers compare binder names EXACTLY (they are `Name` data inside the quoted `Expr`),
so a literal changed by the cache would be refused by an `accept` case (the `ALPHA` case below uses two α-equivalent lambdas with different binder names in one input). -/
namespace Tests.Gen5.FGCircuitPilotCheck41
open Lean Meta Elab Command Term Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1sCD Tools.ShippingFGCircuitS1wTbl
open Tools.ShippingFGCircuitS2iSh Tools.ShippingFGCircuitS2iDT Tools.ShippingFGCircuitS2iTbl Tools.ShippingFGCircuitS2iRun

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def axiomsOk (n : Name) : CoreM Unit := do
  let ax ← collectAxioms n
  unless ax.all (standardAxioms.contains ·) do throwError "{n}: non-standard axioms {ax}"

/-- `accept`: the kernel must accept `T_fixed`; `reject`: the kernel must refuse it. The expected input, result type and result value are Lean terms. -/
syntax (name := fixedDT) "fixed_dt " (&"accept" <|> &"reject") str ident term:max term:max term:max : command

@[command_elab fixedDT] def elabFixedDT : CommandElab := fun stx => do
  let acc := stx[1].getAtomVal == "accept"
  let tag := stx[2].isStrLit?.getD ""
  let thm ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[3])
  let tyStx ← `(∀ (env : Lean.Environment) (hΔ : EnvDefs env $(mkIdent (Name.str thm "Delta"))) (hΓ : EnvCtors env $(mkIdent (Name.str thm "Gamma"))) (hrec : RecFact env),
      DT env [] $(⟨stx[4]⟩) (Res.val $(⟨stx[5]⟩) $(⟨stx[6]⟩)))
  let ty ← liftTermElabM do
    let t ← Term.elabType tyStx
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars t
  let fixedName := Name.str thm "fixed"
  let decl : Declaration := .thmDecl { name := fixedName, levelParams := [], type := ty, value := Lean.mkConst thm }
  let env0 ← getEnv
  let r ← IO.lazyPure (fun _ => Lean.Environment.addDeclCore env0 0 decl none)
  match r with
  | .ok env' =>
    unless acc do throwError "{tag}: the control was ACCEPTED by the kernel"
    setEnv env'
    liftTermElabM (axiomsOk fixedName)
    logInfo m!"{tag} accepted: {fixedName} kernel-checked against the fixed input and result, standard axioms only"
  | .error ex =>
    let msg ← liftCoreM (ex.toMessageData (← getOptions)).toString
    if acc then throwError "{tag}: the kernel refused the fixed type: {msg}"
    unless (msg.splitOn "type mismatch").length > 1 do throwError "{tag}: unexpected kernel error: {msg}"
    if (← getEnv).contains fixedName then throwError "{tag}: a theorem was added"
    logInfo m!"{tag} rejected: the kernel refused {fixedName} against the fixed input and result (type mismatch; a wrong-input / wrong-value proof is not accepted)"

run_cmd liftTermElabM do
  for n in [``sh_fun, ``dt_fun, ``cdt_fun, ``Tools.ShippingFGCircuitS2pValHead.sh_var_val, ``Tools.ShippingFGCircuitS2qBits.extract_at, ``Tools.ShippingFGCircuitS2qBits.shl_at,
      ``Tools.ShippingFGCircuitS2qBits.append_at] do
    axiomsOk n
  logInfo "AXIOMS ok: Sh/DT functionality and the per-time bit equations use only the standard axioms"

/-! ## the generated theorems (from the generator's helper constructors; the expected types below do NOT use them) -/
def bl : Lean.Expr := .const ``Bool []
def bF : Lean.Expr := .const ``Bool.false []
def bT : Lean.Expr := .const ``Bool.true []
def pBB : Lean.Expr := appN ``Prod [.zero, .zero] [bl, bl]
def mkP (x y : Lean.Expr) : Lean.Expr := appN ``Prod.mk [.zero, .zero] [bl, bl, x, y]
def lamB (b : Lean.Expr) : Lean.Expr := .lam `x bl b .default
def lamT (T b : Lean.Expr) : Lean.Expr := .lam `x T b .default
def bb : Lean.Expr := .forallE `a bl bl .default
def nilB : Lean.Expr := appN ``List.nil [.zero] [bl]
def consTB : Lean.Expr := appN ``List.cons [.zero] [bl, bT, nilB]
def motB : Lean.Expr := lamT (appN ``List [.zero] [bl]) bl
def recB (nilc consc major : Lean.Expr) : Lean.Expr := appN ``List.rec [.succ .zero, .zero] [bl, motB, nilc, consc, major]
def listBl : Lean.Expr := appN ``List [.zero] [bl]
def consH : Lean.Expr := .lam `h bl (.lam `t listBl (.lam `ih bl (.bvar 2) .default) .default) .default
def consIH : Lean.Expr := .lam `h bl (.lam `t listBl (.lam `ih bl (.bvar 0) .default) .default) .default

derive_expr_t share := (Lean.Expr.app (lamB (mkP (.bvar 0) (.bvar 0))) bF : Lean.Expr)
derive_expr_t shadow := (Lean.Expr.app (lamB (Lean.Expr.app (lamB (mkP (.bvar 0) (.bvar 1))) bT)) bF : Lean.Expr)
derive_expr_t higher := (Lean.Expr.app (lamT bb (mkP (.app (.bvar 0) bT) (.app (.bvar 0) bF))) (lamB (.bvar 0)) : Lean.Expr)
derive_expr_t recNil := (recB bF consH nilB : Lean.Expr)
derive_expr_t recCons := (recB bF consH consTB : Lean.Expr)
derive_expr_t recIH := (recB bF consIH consTB : Lean.Expr)
-- two α-equivalent lambdas with DIFFERENT binder names in one input: `Prod.mk ((fun x => x) false) ((fun y => y) true)`
def idX : Lean.Expr := .lam `x bl (.bvar 0) .default
def idY : Lean.Expr := .lam `y bl (.bvar 0) .default
derive_expr_t alpha := (mkP (.app idX bF) (.app idY bT) : Lean.Expr)
-- value-head application: `let x := true; let x := false; Prod.mk ((fun y => y) #1) ((fun y => y) #0)`
def idB : Lean.Expr := .lam `y bl (.bvar 0) .default
def letB (v b : Lean.Expr) : Lean.Expr := .letE `x bl v b false
derive_expr_t valHead := (letB bF (.app idB (.bvar 0)) : Lean.Expr)
derive_expr_t valNest := (letB bT (letB bF (mkP (.app idB (.bvar 1)) (.app idB (.bvar 0)))) : Lean.Expr)

def nat (n : Nat) : Lean.Expr := appN ``OfNat.ofNat [.zero] [.const ``Nat [], .lit (.natVal n), appN ``instOfNatNat [] [.lit (.natVal n)]]
def bvT (w : Lean.Expr) : Lean.Expr := appN ``BitVec [] [w]
def dom : Lean.Expr := .const ``Sparkle.Core.Domain.defaultDomain []
def bvLit (w k : Nat) : Lean.Expr := appN ``BitVec.ofNat [] [nat w, nat k]
def sigC (d : Lean.Expr) (w k : Nat) : Lean.Expr := appN ``Sparkle.Core.Signal.Signal.pure [.zero] [d, bvT (nat w), bvLit w k]
def sigT (d t : Lean.Expr) : Lean.Expr := appN ``Sparkle.Core.Signal.Signal [.zero] [d, t]
def extFn (wB nE lo len : Lean.Expr) : Lean.Expr := .lam `x (bvT wB) (appN ``BitVec.extractLsb' [] [nE, lo, len, .bvar 0]) .default
def mapExt (d wTy lTy f s : Lean.Expr) : Lean.Expr := appN ``Sparkle.Core.Signal.Signal.map [.zero] [d, bvT wTy, bvT lTy, f, s]
def ext (w lo len k : Nat) : Lean.Expr := mapExt dom (nat w) (nat len) (extFn (nat w) (nat w) (nat lo) (nat len)) (sigC dom w k)
def shl (d : Lean.Expr) (w : Nat) (a b : Lean.Expr) : Lean.Expr :=
  appN ``HShiftLeft.hShiftLeft [.zero, .zero, .zero] [sigT d (bvT (nat w)), bvT (nat w), sigT d (bvT (nat w)),
    appN ``Sparkle.Core.Signal.instHShiftLeftSignalBitVec [] [d, nat w], a, b]
def natAdd (m n : Lean.Expr) : Lean.Expr :=
  appN ``HAdd.hAdd [.zero, .zero, .zero] [.const ``Nat [], .const ``Nat [], .const ``Nat [], appN ``instHAdd [.zero] [.const ``Nat [], .const ``instAddNat []], m, n]
def app (d : Lean.Expr) (m n : Nat) (a b : Lean.Expr) : Lean.Expr :=
  appN ``HAppend.hAppend [.zero, .zero, .zero] [bvT (nat m), sigT d (bvT (nat n)), sigT d (bvT (natAdd (nat m) (nat n))),
    appN ``Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat [] [nat m, d, nat n], a, b]

derive_expr_t extA := (ext 8 6 1 5 : Lean.Expr)      -- bit 6 of 5#8 = 0
derive_expr_t extB := (ext 16 3 10 1021 : Lean.Expr) -- 1021 = 0b1111111101; bits 3..12 = 0b0001111111 = 127
derive_expr_t shlA := (shl dom 16 (sigC dom 16 3) (bvLit 16 8) : Lean.Expr)    -- 3 <<< 8 = 768
derive_expr_t shlB := (shl dom 32 (sigC dom 32 3) (bvLit 32 40) : Lean.Expr)   -- amount ≥ width: 0
derive_expr_t appA := (app dom 8 8 (bvLit 8 1) (sigC dom 8 2) : Lean.Expr)      -- 1#8 ++ 2#8 = 258#16
derive_expr_t appB := (app dom 8 16 (bvLit 8 1) (sigC dom 16 2) : Lean.Expr)    -- 1#8 ++ 2#16 = 65538#24

section
/-! ## POSITIVE: the fixed expected input and result (the input is re-quoted with raw constructors) -/
-- SHARE: `(fun x : Bool => Prod.mk x x) false` = (false, false)
fixed_dt accept "SHARE (false,false)" share
  (Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Prod.mk [Level.zero, Level.zero])
    (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool [])) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 0)) BinderInfo.default) (Lean.Expr.const `Bool.false []))
  (Bool × Bool) ((false, false))
-- SHADOW: `(fun x => (fun x => Prod.mk x #1) true) false` = (true, false)
fixed_dt accept "SHADOW (true,false)" shadow
  (Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.const `Bool [])
    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Prod.mk [Level.zero, Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []))
      (Lean.Expr.bvar 0)) (Lean.Expr.bvar 1)) BinderInfo.default) (Lean.Expr.const `Bool.true [])) BinderInfo.default) (Lean.Expr.const `Bool.false []))
  (Bool × Bool) ((true, false))
-- HIGHER: `(fun g : Bool → Bool => Prod.mk (g true) (g false)) (fun b => b)` = (true, false)
fixed_dt accept "HIGHER (true,false)" higher
  (Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.forallE `a (Lean.Expr.const `Bool []) (Lean.Expr.const `Bool []) BinderInfo.default)
    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Prod.mk [Level.zero, Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []))
      (Lean.Expr.app (Lean.Expr.bvar 0) (Lean.Expr.const `Bool.true []))) (Lean.Expr.app (Lean.Expr.bvar 0) (Lean.Expr.const `Bool.false []))) BinderInfo.default)
    (Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default))
  (Bool × Bool) ((true, false))
-- REC: the static `List.rec` rule; the three expected results are `false`, `true`, `false`
fixed_dt accept "REC-NIL false" recNil
  (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `List.rec [Level.succ Level.zero, Level.zero]) (Lean.Expr.const `Bool []))
    (Lean.Expr.lam `x (Lean.Expr.app (Lean.Expr.const `List [Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []) BinderInfo.default))
    (Lean.Expr.const `Bool.false []))
    (Lean.Expr.lam `h (Lean.Expr.const `Bool []) (Lean.Expr.lam `t (Lean.Expr.app (Lean.Expr.const `List [Level.zero]) (Lean.Expr.const `Bool []))
      (Lean.Expr.lam `ih (Lean.Expr.const `Bool []) (Lean.Expr.bvar 2) BinderInfo.default) BinderInfo.default) BinderInfo.default))
    (Lean.Expr.app (Lean.Expr.const `List.nil [Level.zero]) (Lean.Expr.const `Bool [])))
  Bool false
fixed_dt accept "REC-CONS true" recCons
  (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `List.rec [Level.succ Level.zero, Level.zero]) (Lean.Expr.const `Bool []))
    (Lean.Expr.lam `x (Lean.Expr.app (Lean.Expr.const `List [Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []) BinderInfo.default))
    (Lean.Expr.const `Bool.false []))
    (Lean.Expr.lam `h (Lean.Expr.const `Bool []) (Lean.Expr.lam `t (Lean.Expr.app (Lean.Expr.const `List [Level.zero]) (Lean.Expr.const `Bool []))
      (Lean.Expr.lam `ih (Lean.Expr.const `Bool []) (Lean.Expr.bvar 2) BinderInfo.default) BinderInfo.default) BinderInfo.default))
    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `List.cons [Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool.true []))
      (Lean.Expr.app (Lean.Expr.const `List.nil [Level.zero]) (Lean.Expr.const `Bool []))))
  Bool true
fixed_dt accept "REC-IH false" recIH
  (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `List.rec [Level.succ Level.zero, Level.zero]) (Lean.Expr.const `Bool []))
    (Lean.Expr.lam `x (Lean.Expr.app (Lean.Expr.const `List [Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []) BinderInfo.default))
    (Lean.Expr.const `Bool.false []))
    (Lean.Expr.lam `h (Lean.Expr.const `Bool []) (Lean.Expr.lam `t (Lean.Expr.app (Lean.Expr.const `List [Level.zero]) (Lean.Expr.const `Bool []))
      (Lean.Expr.lam `ih (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default) BinderInfo.default) BinderInfo.default))
    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `List.cons [Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool.true []))
      (Lean.Expr.app (Lean.Expr.const `List.nil [Level.zero]) (Lean.Expr.const `Bool []))))
  Bool false
-- ALPHA: `Prod.mk ((fun x => x) false) ((fun y => y) true)` = (false, true), the binder names `x` and `y` are compared exactly
fixed_dt accept "ALPHA (false,true), binder names x / y" alpha
  (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Prod.mk [Level.zero, Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []))
    (Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default) (Lean.Expr.const `Bool.false [])))
    (Lean.Expr.app (Lean.Expr.lam `y (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default) (Lean.Expr.const `Bool.true [])))
  (Bool × Bool) ((false, true))
-- VALUE-HEAD application: `let x := false; (fun y => y) x` = false; `let x := true; let x := false; Prod.mk ((fun y => y) #1) ((fun y => y) #0)` = (true, false)
fixed_dt accept "VALHEAD false" valHead
  (Lean.Expr.letE `x (Lean.Expr.const `Bool []) (Lean.Expr.const `Bool.false [])
    (Lean.Expr.app (Lean.Expr.lam `y (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default) (Lean.Expr.bvar 0)) false)
  Bool false
fixed_dt accept "VALHEAD-NEST (true,false)" valNest
  (Lean.Expr.letE `x (Lean.Expr.const `Bool []) (Lean.Expr.const `Bool.true [])
    (Lean.Expr.letE `x (Lean.Expr.const `Bool []) (Lean.Expr.const `Bool.false [])
      (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Prod.mk [Level.zero, Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []))
        (Lean.Expr.app (Lean.Expr.lam `y (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default) (Lean.Expr.bvar 1)))
        (Lean.Expr.app (Lean.Expr.lam `y (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default) (Lean.Expr.bvar 0))) false) false)
  (Bool × Bool) ((true, false))
end

-- BitVec: width and value examples. The inputs are re-quoted with raw constructors through the local `Q*` terms below; the result is stated at the semantic level (`BitVec` operations on literals).
/-- `OfNat.ofNat Nat n (instOfNatNat n)` written with raw constructors -/
def qNat (n : Nat) : Lean.Expr :=
  Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Level.zero]) (Lean.Expr.const `Nat [])) (Lean.Expr.lit (Literal.natVal n)))
    (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Literal.natVal n)))
def qBV (w : Lean.Expr) : Lean.Expr := Lean.Expr.app (Lean.Expr.const `BitVec []) w
def qLit (w k : Nat) : Lean.Expr := Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `BitVec.ofNat []) (qNat w)) (qNat k)
def qDom : Lean.Expr := Lean.Expr.const `Sparkle.Core.Domain.defaultDomain []
def qSig (t : Lean.Expr) : Lean.Expr := Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Sparkle.Core.Signal.Signal [Level.zero]) qDom) t
def qPure (w k : Nat) : Lean.Expr :=
  Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Sparkle.Core.Signal.Signal.pure [Level.zero]) qDom) (qBV (qNat w))) (qLit w k)
def qExt (w lo len k : Nat) : Lean.Expr :=
  Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Sparkle.Core.Signal.Signal.map [Level.zero]) qDom) (qBV (qNat w))) (qBV (qNat len)))
    (Lean.Expr.lam `x (qBV (qNat w)) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `BitVec.extractLsb' []) (qNat w)) (qNat lo)) (qNat len)) (Lean.Expr.bvar 0))
      BinderInfo.default)) (qPure w k)
def qShl (w k a : Nat) : Lean.Expr :=
  Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `HShiftLeft.hShiftLeft [Level.zero, Level.zero, Level.zero])
    (qSig (qBV (qNat w)))) (qBV (qNat w))) (qSig (qBV (qNat w))))
    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Sparkle.Core.Signal.instHShiftLeftSignalBitVec []) qDom) (qNat w))) (qPure w k)) (qLit w a)
def qAdd (m n : Nat) : Lean.Expr :=
  Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `HAdd.hAdd [Level.zero, Level.zero, Level.zero]) (Lean.Expr.const `Nat []))
    (Lean.Expr.const `Nat [])) (Lean.Expr.const `Nat []))
    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `instHAdd [Level.zero]) (Lean.Expr.const `Nat [])) (Lean.Expr.const `instAddNat []))) (qNat m)) (qNat n)
def qApp (m n a b : Nat) : Lean.Expr :=
  Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `HAppend.hAppend [Level.zero, Level.zero, Level.zero])
    (qBV (qNat m))) (qSig (qBV (qNat n)))) (qSig (qBV (qAdd m n))))
    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat []) (qNat m)) qDom) (qNat n)))
    (qLit m a)) (qPure n b)

section
abbrev S (n : Nat) : Type := Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain (BitVec n)
abbrev P {n : Nat} (v : BitVec n) : S n := Sparkle.Core.Signal.Signal.pure v
-- extract: `extractLsb' lo len` of `k#w`
fixed_dt accept "EXTRACT 8/6/1 of 5 = 0#1" extA (qExt 8 6 1 5) (S 1) (P (BitVec.ofNat 1 0))
fixed_dt accept "EXTRACT 16/3/10 of 1021 = 127#10" extB (qExt 16 3 10 1021) (S 10) (P (BitVec.ofNat 10 127))
-- shift: `k#w <<< a#w`
fixed_dt accept "SHL 16: 3 <<< 8 = 768#16" shlA (qShl 16 3 8) (S 16) (P (BitVec.ofNat 16 768))
fixed_dt accept "SHL 32: 3 <<< 40 = 0#32" shlB (qShl 32 3 40) (S 32) (P (BitVec.ofNat 32 0))
-- append: `a#m ++ b#n`
fixed_dt accept "APPEND 8+8: 1#8 ++ 2#8 = 258#16" appA (qApp 8 8 1 2) (S (8 + 8)) (P (BitVec.ofNat (8 + 8) 258))
fixed_dt accept "APPEND 8+16: 1#8 ++ 2#16 = 65538#24" appB (qApp 8 16 1 2) (S (8 + 16)) (P (BitVec.ofNat (8 + 16) 65538))

/-! ## NEGATIVE CONTROLS: the SAME command, the same kernel call and report text; only the expected input / value / captured environment is wrong -/
def eShare : Lean.Expr :=
  Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Prod.mk [Level.zero, Level.zero])
    (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool [])) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 0)) BinderInfo.default) (Lean.Expr.const `Bool.false [])
-- another VALUE
fixed_dt reject "CTRL SHARE as (true,true)" share eShare (Bool × Bool) ((true, true))
fixed_dt reject "CTRL SHARE as (false,true) (the two uses differ)" share eShare (Bool × Bool) ((false, true))
-- another INPUT: the SHARE theorem against the `true` argument / against the SHADOW input
fixed_dt reject "CTRL SHARE theorem, input with argument true" share
  (Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Prod.mk [Level.zero, Level.zero])
    (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool [])) (Lean.Expr.bvar 0)) (Lean.Expr.bvar 0)) BinderInfo.default) (Lean.Expr.const `Bool.true []))
  (Bool × Bool) ((false, false))
-- captured environment: SHADOW with the roles of the inner / outer binder swapped (result (false,true)), and with the input's `#1` replaced by `#0`
fixed_dt reject "CTRL SHADOW as (false,true) (inner / outer environment swapped)" shadow
  (Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.const `Bool [])
    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Prod.mk [Level.zero, Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []))
      (Lean.Expr.bvar 0)) (Lean.Expr.bvar 1)) BinderInfo.default) (Lean.Expr.const `Bool.true [])) BinderInfo.default) (Lean.Expr.const `Bool.false []))
  (Bool × Bool) ((false, true))
fixed_dt reject "CTRL SHADOW theorem, input with #0 instead of #1" shadow
  (Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.const `Bool [])
    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Prod.mk [Level.zero, Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []))
      (Lean.Expr.bvar 0)) (Lean.Expr.bvar 0)) BinderInfo.default) (Lean.Expr.const `Bool.true [])) BinderInfo.default) (Lean.Expr.const `Bool.false []))
  (Bool × Bool) ((true, true))
-- HIGHER with the two applications swapped
fixed_dt reject "CTRL HIGHER as (false,true)" higher
  (Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.forallE `a (Lean.Expr.const `Bool []) (Lean.Expr.const `Bool []) BinderInfo.default)
    (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Prod.mk [Level.zero, Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []))
      (Lean.Expr.app (Lean.Expr.bvar 0) (Lean.Expr.const `Bool.true []))) (Lean.Expr.app (Lean.Expr.bvar 0) (Lean.Expr.const `Bool.false []))) BinderInfo.default)
    (Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default))
  (Bool × Bool) ((false, true))
-- REC: the wrong constructor result for each of the three, and a result of the wrong TYPE
def eRecNil : Lean.Expr :=
  Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `List.rec [Level.succ Level.zero, Level.zero]) (Lean.Expr.const `Bool []))
    (Lean.Expr.lam `x (Lean.Expr.app (Lean.Expr.const `List [Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []) BinderInfo.default))
    (Lean.Expr.const `Bool.false []))
    (Lean.Expr.lam `h (Lean.Expr.const `Bool []) (Lean.Expr.lam `t (Lean.Expr.app (Lean.Expr.const `List [Level.zero]) (Lean.Expr.const `Bool []))
      (Lean.Expr.lam `ih (Lean.Expr.const `Bool []) (Lean.Expr.bvar 2) BinderInfo.default) BinderInfo.default) BinderInfo.default))
    (Lean.Expr.app (Lean.Expr.const `List.nil [Level.zero]) (Lean.Expr.const `Bool []))
fixed_dt reject "CTRL REC-NIL as true" recNil eRecNil Bool true
fixed_dt reject "CTRL REC-NIL as (false,false) (wrong type)" recNil eRecNil (Bool × Bool) ((false, false))
fixed_dt reject "CTRL REC-CONS as false" recCons eRecNil Bool false   -- other input (the nil list) against the cons theorem
fixed_dt reject "CTRL REC-IH as true" recIH eRecNil Bool true
-- VALUE-HEAD: the value variable resolved in the wrong entry
fixed_dt reject "CTRL VALHEAD as true" valHead
  (Lean.Expr.letE `x (Lean.Expr.const `Bool []) (Lean.Expr.const `Bool.false [])
    (Lean.Expr.app (Lean.Expr.lam `y (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default) (Lean.Expr.bvar 0)) false)
  Bool true
fixed_dt reject "CTRL VALHEAD-NEST as (false,true) (entries swapped)" valNest
  (Lean.Expr.letE `x (Lean.Expr.const `Bool []) (Lean.Expr.const `Bool.true [])
    (Lean.Expr.letE `x (Lean.Expr.const `Bool []) (Lean.Expr.const `Bool.false [])
      (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Prod.mk [Level.zero, Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []))
        (Lean.Expr.app (Lean.Expr.lam `y (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default) (Lean.Expr.bvar 1)))
        (Lean.Expr.app (Lean.Expr.lam `y (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default) (Lean.Expr.bvar 0))) false) false)
  (Bool × Bool) ((false, true))
-- ALPHA: the same input with the binder names swapped (α-equivalent, but not the quoted data) is refused: exact equality
fixed_dt reject "CTRL ALPHA input with binder names y / x (α-equivalent, not equal)" alpha
  (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Prod.mk [Level.zero, Level.zero]) (Lean.Expr.const `Bool [])) (Lean.Expr.const `Bool []))
    (Lean.Expr.app (Lean.Expr.lam `y (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default) (Lean.Expr.const `Bool.false [])))
    (Lean.Expr.app (Lean.Expr.lam `x (Lean.Expr.const `Bool []) (Lean.Expr.bvar 0) BinderInfo.default) (Lean.Expr.const `Bool.true [])))
  (Bool × Bool) ((false, true))
-- BitVec: another value / width / input constant / shift amount / operand order
fixed_dt reject "CTRL EXTRACT value 1#1" extA (qExt 8 6 1 5) (S 1) (P (BitVec.ofNat 1 1))
fixed_dt reject "CTRL EXTRACT width 2" extA (qExt 8 6 1 5) (S 2) (P (BitVec.ofNat 2 0))
fixed_dt reject "CTRL EXTRACT input constant 4 instead of 5" extA (qExt 8 6 1 4) (S 1) (P (BitVec.ofNat 1 0))
fixed_dt reject "CTRL EXTRACT offset 2 instead of 6" extA (qExt 8 2 1 5) (S 1) (P (BitVec.ofNat 1 0))
fixed_dt reject "CTRL EXTRACT theorem 16/3/10 as 126#10" extB (qExt 16 3 10 1021) (S 10) (P (BitVec.ofNat 10 126))
fixed_dt reject "CTRL SHL value 3#16" shlA (qShl 16 3 8) (S 16) (P (BitVec.ofNat 16 3))
fixed_dt reject "CTRL SHL amount 7 instead of 8" shlA (qShl 16 3 7) (S 16) (P (BitVec.ofNat 16 768))
fixed_dt reject "CTRL SHL 32 big amount as 3#32" shlB (qShl 32 3 40) (S 32) (P (BitVec.ofNat 32 3))
fixed_dt reject "CTRL APPEND value 513#16 (operands swapped)" appA (qApp 8 8 1 2) (S (8 + 8)) (P (BitVec.ofNat (8 + 8) 513))
fixed_dt reject "CTRL APPEND width 8+8 for the 8+16 theorem" appB (qApp 8 16 1 2) (S (8 + 8)) (P (BitVec.ofNat (8 + 8) 258))
fixed_dt reject "CTRL APPEND operands 2#8 ++ 1#16" appB (qApp 8 16 2 1) (S (8 + 16)) (P (BitVec.ofNat (8 + 16) 65538))
end

end Tests.Gen5.FGCircuitPilotCheck41
