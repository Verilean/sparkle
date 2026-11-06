import Tools.ShippingFGCircuitS2iRun
import Tools.ShippingFGCircuitS2qBits
set_option autoImplicit false
-- FG circuit pilot S2t check (light, small run_cmd blocks). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §45.

/-! # FGCircuitPilotCheck40

The evidence-carrying rule `DT.sigOrBV` (`Signal D (BitVec W) ||| Signal D (BitVec W)`): the second type argument of `HOr.hOr` is `Signal d (BitVec wb)` with the SAME `d` and a closed width `wb` with `natEvalE wb = some W` (kernel evidence).
1. AXIOMS: `dt_fun`, `or_at`, `natEvalE_*` use only the standard axioms.
2. POSITIVE (kernel-checked): `8 + 8` vs `16`, `24 + 8` vs `32`, plain `16` / `16`; under a domain binder; the Bool OR is still derived (by `sigOrBool`, a different rule).
3. CONTROLS, two kinds with the SAME comparison method (`expectErr`: not derived, no theorem added, the error text is searched):
   (G) GENERATOR rejection (the error is the generator's own check; a wrong generator could skip it);
   (K) KERNEL rejection: the same wrong request with the generator's own `sigOrBV` checks switched OFF (`deriveTermLax`, test hook): the ill-typed term reaches the kernel, which rejects it (`(kernel)` text).
   A generator failure is not a non-derivability theorem; the (K) rows are the evidence that the RULE (its types) is what stops the request. -/
namespace Tests.Gen5.FGCircuitPilotCheck40
open Lean Meta Elab Command Term Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1sCD Tools.ShippingFGCircuitS1wTbl
open Tools.ShippingFGCircuitS2iSh Tools.ShippingFGCircuitS2iDT Tools.ShippingFGCircuitS2iTbl Tools.ShippingFGCircuitS2iRun

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def axiomsOk (n : Name) : CoreM Unit := do
  let ax ← collectAxioms n
  unless ax.all (standardAxioms.contains ·) do throwError "{n}: non-standard axioms {ax}"

run_cmd liftTermElabM do
  for n in [``dt_fun, ``Tools.ShippingFGCircuitS2qBits.or_at, ``natEvalE_8, ``natEvalE_add88] do
    axiomsOk n
  logInfo "AXIOMS ok: dt_fun (with the sigOrBV case), or_at and the natEvalE examples use only the standard axioms"

def nat (n : Nat) : Lean.Expr := appN ``OfNat.ofNat [.zero] [.const ``Nat [], .lit (.natVal n), appN ``instOfNatNat [] [.lit (.natVal n)]]
def natAdd (m n : Lean.Expr) : Lean.Expr :=
  appN ``HAdd.hAdd [.zero, .zero, .zero] [.const ``Nat [], .const ``Nat [], .const ``Nat [], appN ``instHAdd [.zero] [.const ``Nat [], .const ``instAddNat []], m, n]
def bvT (w : Lean.Expr) : Lean.Expr := appN ``BitVec [] [w]
def dom : Lean.Expr := .const ``Sparkle.Core.Domain.defaultDomain []
def bvLit (w k : Nat) : Lean.Expr := appN ``BitVec.ofNat [] [nat w, nat k]
def sigC (d : Lean.Expr) (w k : Nat) : Lean.Expr := appN ``Sparkle.Core.Signal.Signal.pure [.zero] [d, bvT (nat w), bvLit w k]
def sigT (d t : Lean.Expr) : Lean.Expr := appN ``Sparkle.Core.Signal.Signal [.zero] [d, t]
/-- `HOr.hOr (Signal d (BitVec w)) T2 (Signal d (BitVec w)) (inst d w) a b`; every type argument and the instance are explicit parameters -/
def orE (inst : Name) (tA t2 tR : Lean.Expr) (instArgs : List Lean.Expr) (a b : Lean.Expr) : Lean.Expr :=
  appN ``HOr.hOr [.zero, .zero, .zero] [tA, t2, tR, appN inst [] instArgs, a, b]
/-- the intended form: domain `d`, instance width `w`, second type argument over width expression `wb` -/
def orBV (d : Lean.Expr) (w : Nat) (wb : Lean.Expr) (a b : Lean.Expr) : Lean.Expr :=
  orE ``Sparkle.Core.Signal.instHOrSignalBitVec (sigT d (bvT (nat w))) (sigT d (bvT wb)) (sigT d (bvT (nat w))) [d, nat w] a b

def report (tag : String) (n : Name) : CommandElabM Unit := do
  unless (← getEnv).contains n do throwError "{tag}: {n} missing"
  liftTermElabM (axiomsOk n)
  logInfo m!"{tag} ok: {n} kernel-checked, standard axioms only"

-- POSITIVE
derive_expr_t orA := (orBV dom 16 (natAdd (nat 8) (nat 8)) (sigC dom 16 3) (sigC dom 16 12) : Lean.Expr)
run_cmd report "OR 8+8 vs 16" `Tests.Gen5.FGCircuitPilotCheck40.orA
derive_expr_t orB := (orBV dom 32 (natAdd (nat 24) (nat 8)) (sigC dom 32 3) (sigC dom 32 12) : Lean.Expr)
run_cmd report "OR 24+8 vs 32" `Tests.Gen5.FGCircuitPilotCheck40.orB
derive_expr_t orC := (orBV dom 16 (nat 16) (sigC dom 16 3) (sigC dom 16 12) : Lean.Expr)
run_cmd report "OR 16 vs 16 (plain)" `Tests.Gen5.FGCircuitPilotCheck40.orC
derive_expr_t orD := (orBV dom 5 (natAdd (nat 2) (nat 3)) (sigC dom 5 1) (sigC dom 5 2) : Lean.Expr)
run_cmd report "OR 2+3 vs 5 (not a probe size)" `Tests.Gen5.FGCircuitPilotCheck40.orD
def domV : Lean.Expr := .bvar 0
derive_expr_t orEnv := (.lam `d (.const ``Sparkle.Core.Domain.DomainConfig []) (orBV domV 16 (natAdd (nat 8) (nat 8)) (sigC domV 16 3) (sigC domV 16 12)) .default : Lean.Expr)
run_cmd report "OR under a domain binder (the same domain variable everywhere)" `Tests.Gen5.FGCircuitPilotCheck40.orEnv
-- the Bool OR is still a different rule (sigOrBool)
derive_expr_t orBool := (orE ``Sparkle.Core.Signal.instHOrSignalBool (sigT dom (.const ``Bool [])) (sigT dom (.const ``Bool [])) (sigT dom (.const ``Bool [])) [dom]
  (appN ``Sparkle.Core.Signal.Signal.pure [.zero] [dom, .const ``Bool [], .const ``Bool.true []]) (appN ``Sparkle.Core.Signal.Signal.pure [.zero] [dom, .const ``Bool [], .const ``Bool.false []]) : Lean.Expr)
run_cmd report "OR Bool (the other rule)" `Tests.Gen5.FGCircuitPilotCheck40.orBool

def errOf (lax : Bool) (n : Name) (e : Lean.Expr) : CommandElabM (Option String) := do
  try
    if lax then deriveTermLax n e else deriveTerm n e
    pure none
  catch ex => pure (some (← (liftCoreM ex.toMessageData.toString)))

def expectErr (lax : Bool) (tag : String) (n : Name) (e : Lean.Expr) (needle : String) : CommandElabM Unit := do
  match ← errOf lax n e with
  | none => throwError "{tag}: the control was derived"
  | some msg =>
    unless (msg.splitOn needle).length > 1 do throwError "{tag}: unexpected error text: {msg}"
    if (← getEnv).contains n then throwError "{tag}: a theorem was added"
    logInfo m!"{tag} ok: not derived, with the expected error «{needle}» ({if lax then "KERNEL, generator checks off" else "generator"}; not a non-derivability theorem)"

abbrev N := `Tests.Gen5.FGCircuitPilotCheck40
def d2 : Lean.Expr := .const ``Sparkle.Core.Domain.defaultDomain []
def eqW : Lean.Expr := natAdd (nat 8) (nat 8)
-- controls: DIFFERENT WIDTHS (operand b is 8 wide, the instance is 16)
def cWidthE : Lean.Expr := orBV dom 16 eqW (sigC dom 16 3) (sigC dom 8 12)
run_cmd expectErr false "G-OR-OPERAND-WIDTH" (N ++ `gOpW) cWidthE "not a Signal of the instance's domain and width"
run_cmd expectErr true "K-OR-OPERAND-WIDTH" (N ++ `kOpW) cWidthE "(kernel)"
-- 8+8 against the instance width 32 (different widths, hidden by the notation)
def cEvalE : Lean.Expr := orBV dom 32 eqW (sigC dom 32 3) (sigC dom 32 12)
run_cmd expectErr false "G-OR-EVAL (8+8 vs 32)" (N ++ `gEval) cEvalE "does not evaluate to the instance's width"
run_cmd expectErr true "K-OR-EVAL (8+8 vs 32)" (N ++ `kEval) cEvalE "(kernel)"
-- ANOTHER DOMAIN: the second type argument over a different domain (a bound variable), operands over `dom`
def cDomE : Lean.Expr := .lam `d (.const ``Sparkle.Core.Domain.DomainConfig []) (orE ``Sparkle.Core.Signal.instHOrSignalBitVec (sigT dom (bvT (nat 16))) (sigT domV (bvT eqW)) (sigT dom (bvT (nat 16))) [dom, nat 16] (sigC dom 16 3) (sigC dom 16 12)) .default
run_cmd expectErr false "G-OR-DOMAIN (second type argument)" (N ++ `gDom) cDomE "another domain"
run_cmd expectErr true "K-OR-DOMAIN (second type argument)" (N ++ `kDom) cDomE "(kernel)"
-- operands over another domain than the instance's
def cDom2E : Lean.Expr := .lam `d (.const ``Sparkle.Core.Domain.DomainConfig []) (orBV dom 16 eqW (sigC domV 16 3) (sigC domV 16 12)) .default
run_cmd expectErr false "G-OR-OPERAND-DOMAIN" (N ++ `gDom2) cDom2E "not a Signal of the instance's domain and width"
run_cmd expectErr true "K-OR-OPERAND-DOMAIN" (N ++ `kDom2) cDom2E "(kernel)"
-- ANOTHER INSTANCE: mixed-constant instances (`Signal ||| BitVec`, `BitVec ||| Signal`) and the Bool instance on BitVec operands
def cMix1E : Lean.Expr := orE ``Sparkle.Core.Signal.instHOrSignalBitVec_1 (sigT dom (bvT (nat 16))) (bvT (nat 16)) (sigT dom (bvT (nat 16))) [dom, nat 16] (sigC dom 16 3) (bvLit 16 12)
run_cmd expectErr false "G-OR-MIXED-1 (Signal ||| BitVec)" (N ++ `gMix1) cMix1E "no direct rule"
def cMix2E : Lean.Expr := orE ``Sparkle.Core.Signal.instHOrBitVecSignal (bvT (nat 16)) (sigT dom (bvT (nat 16))) (sigT dom (bvT (nat 16))) [nat 16, dom] (bvLit 16 3) (sigC dom 16 12)
run_cmd expectErr false "G-OR-MIXED-2 (BitVec ||| Signal)" (N ++ `gMix2) cMix2E "no direct rule"
def cBoolE : Lean.Expr := orE ``Sparkle.Core.Signal.instHOrSignalBool (sigT dom (bvT (nat 16))) (sigT dom (bvT (nat 16))) (sigT dom (bvT (nat 16))) [dom] (sigC dom 16 3) (sigC dom 16 12)
run_cmd expectErr false "G-OR-BOOLINSTANCE (Bool instance on BitVec operands)" (N ++ `gBool) cBoolE "no direct rule"
-- SECOND TYPE ARGUMENT replaced by an unrelated type
def cUnrelE : Lean.Expr := orE ``Sparkle.Core.Signal.instHOrSignalBitVec (sigT dom (bvT (nat 16))) (.const ``Nat []) (sigT dom (bvT (nat 16))) [dom, nat 16] (sigC dom 16 3) (sigC dom 16 12)
run_cmd expectErr false "G-OR-UNRELATED (second type argument Nat)" (N ++ `gUnrel) cUnrelE "is not Signal d (BitVec wb)"
run_cmd expectErr true "K-OR-UNRELATED (second type argument Nat)" (N ++ `kUnrel) cUnrelE "(kernel)"
def cUnrel2E : Lean.Expr := orE ``Sparkle.Core.Signal.instHOrSignalBitVec (sigT dom (bvT (nat 16))) (sigT dom (.const ``Bool [])) (sigT dom (bvT (nat 16))) [dom, nat 16] (sigC dom 16 3) (sigC dom 16 12)
run_cmd expectErr false "G-OR-UNRELATED-2 (second type argument Signal Bool)" (N ++ `gUnrel2) cUnrel2E "is not Signal d (BitVec wb)"
run_cmd expectErr true "K-OR-UNRELATED-2 (second type argument Signal Bool)" (N ++ `kUnrel2) cUnrel2E "(kernel)"
-- CHANGED RESULT WIDTH (third type argument)
def cResE : Lean.Expr := orE ``Sparkle.Core.Signal.instHOrSignalBitVec (sigT dom (bvT (nat 16))) (sigT dom (bvT eqW)) (sigT dom (bvT (nat 17))) [dom, nat 16] (sigC dom 16 3) (sigC dom 16 12)
run_cmd expectErr false "G-OR-RESULT-WIDTH" (N ++ `gRes) cResE "no direct rule"
run_cmd expectErr true "K-OR-RESULT-WIDTH" (N ++ `kRes) cResE "(kernel)"
-- CHANGED FIRST TYPE ARGUMENT
def cFirstE : Lean.Expr := orE ``Sparkle.Core.Signal.instHOrSignalBitVec (sigT dom (bvT (nat 17))) (sigT dom (bvT eqW)) (sigT dom (bvT (nat 16))) [dom, nat 16] (sigC dom 16 3) (sigC dom 16 12)
run_cmd expectErr false "G-OR-FIRST-TYPE" (N ++ `gFirst) cFirstE "no direct rule"
run_cmd expectErr true "K-OR-FIRST-TYPE" (N ++ `kFirst) cFirstE "(kernel)"
-- a width expression that is not closed (a variable) is not evidence
def cVarE : Lean.Expr := .lam `n (.const ``Nat []) (orE ``Sparkle.Core.Signal.instHOrSignalBitVec (sigT dom (bvT (nat 16))) (sigT dom (bvT (.bvar 0))) (sigT dom (bvT (nat 16))) [dom, nat 16] (sigC dom 16 3) (sigC dom 16 12)) .default
run_cmd expectErr false "G-OR-OPENWIDTH (second type argument over a variable width)" (N ++ `gVar) cVarE "does not evaluate"
run_cmd expectErr true "K-OR-OPENWIDTH (second type argument over a variable width)" (N ++ `kVar) cVarE "(kernel)"

end Tests.Gen5.FGCircuitPilotCheck40
