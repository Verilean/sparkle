import Tools.ShippingFGCircuitS2iRun
import Tools.ShippingFGCircuitS2qBits
set_option autoImplicit false
-- FG circuit pilot S2q check (light, small run_cmd blocks). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §43.

/-! # FGCircuitPilotCheck38

1. AXIOMS: `sh_fun`, `dt_fun`, `cdt_eq` and the per-time equations (`extract_at`, `shl_at`, `shl_at_toNat`, `shl_at_big`, `append_at`, `append_at_toNat`) use only the standard axioms.
2. POSITIVE (kernel-checked by the generator, same report text as the controls): the `extractLsb'`-only map rule at several widths/offsets/lengths (not only the three sizes of the probe), `Signal <<< BitVec` at two widths,
   `BitVec ++ Signal` at two sizes, and `<<<` under a binder over the domain (the same domain variable for all operands).
3. NEGATIVE CONTROLS (fail-closed with the EXPECTED generator error text; a generator failure is NOT a non-derivability theorem): wrong width / length / input-signal width / other function / non-variable argument
   for the extract rule; wrong shift-amount width / wrong signal width / wrong domain for `<<<`; swapped sides / wrong instance / wrong output width / wrong right width for `++`.
   Correct expressions with OTHER constants are derived (item 2). -/
namespace Tests.Gen5.FGCircuitPilotCheck38
open Lean Meta Elab Command Term Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1sCD Tools.ShippingFGCircuitS1wTbl
open Tools.ShippingFGCircuitS2iSh Tools.ShippingFGCircuitS2iDT Tools.ShippingFGCircuitS2iTbl Tools.ShippingFGCircuitS2iRun

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def axiomsOk (n : Name) : CoreM Unit := do
  let ax ← collectAxioms n
  unless ax.all (standardAxioms.contains ·) do throwError "{n}: non-standard axioms {ax}"

run_cmd liftTermElabM do
  for n in [``sh_fun, ``dt_fun, ``cdt_eq, ``Tools.ShippingFGCircuitS2qBits.extract_at, ``Tools.ShippingFGCircuitS2qBits.shl_at, ``Tools.ShippingFGCircuitS2qBits.shl_at_toNat,
      ``Tools.ShippingFGCircuitS2qBits.shl_at_big, ``Tools.ShippingFGCircuitS2qBits.append_at, ``Tools.ShippingFGCircuitS2qBits.append_at_toNat] do
    axiomsOk n
  logInfo "AXIOMS ok: Sh/DT functionality and the per-time bit equations use only the standard axioms"

def nat (n : Nat) : Lean.Expr := appN ``OfNat.ofNat [.zero] [.const ``Nat [], .lit (.natVal n), appN ``instOfNatNat [] [.lit (.natVal n)]]
def bvT (w : Lean.Expr) : Lean.Expr := appN ``BitVec [] [w]
def dom : Lean.Expr := .const ``Sparkle.Core.Domain.defaultDomain []
def bvLit (w k : Nat) : Lean.Expr := appN ``BitVec.ofNat [] [nat w, nat k]
/-- the constant stream `Signal.pure (k#w)` over `d` -/
def sigC (d : Lean.Expr) (w k : Nat) : Lean.Expr := appN ``Sparkle.Core.Signal.Signal.pure [.zero] [d, bvT (nat w), bvLit w k]
def sigT (d t : Lean.Expr) : Lean.Expr := appN ``Sparkle.Core.Signal.Signal [.zero] [d, t]
def extFn (wB nE lo len : Lean.Expr) : Lean.Expr := .lam `x (bvT wB) (appN ``BitVec.extractLsb' [] [nE, lo, len, .bvar 0]) .default
def mapExt (d wTy lTy f s : Lean.Expr) : Lean.Expr := appN ``Sparkle.Core.Signal.Signal.map [.zero] [d, bvT wTy, bvT lTy, f, s]
/-- `map (fun x : BitVec w => extractLsb' w lo len x) (pure k#w)` -/
def ext (w lo len k : Nat) : Lean.Expr := mapExt dom (nat w) (nat len) (extFn (nat w) (nat w) (nat lo) (nat len)) (sigC dom w k)
def shl (d : Lean.Expr) (w : Nat) (a b : Lean.Expr) : Lean.Expr :=
  appN ``HShiftLeft.hShiftLeft [.zero, .zero, .zero] [sigT d (bvT (nat w)), bvT (nat w), sigT d (bvT (nat w)),
    appN ``Sparkle.Core.Signal.instHShiftLeftSignalBitVec [] [d, nat w], a, b]
def natAdd (m n : Lean.Expr) : Lean.Expr :=
  appN ``HAdd.hAdd [.zero, .zero, .zero] [.const ``Nat [], .const ``Nat [], .const ``Nat [], appN ``instHAdd [.zero] [.const ``Nat [], .const ``instAddNat []], m, n]
def app (d : Lean.Expr) (m n : Nat) (a b : Lean.Expr) : Lean.Expr :=
  appN ``HAppend.hAppend [.zero, .zero, .zero] [bvT (nat m), sigT d (bvT (nat n)), sigT d (bvT (natAdd (nat m) (nat n))),
    appN ``Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat [] [nat m, d, nat n], a, b]

def report (tag : String) (n : Name) : CommandElabM Unit := do
  unless (← getEnv).contains n do throwError "{tag}: {n} missing"
  liftTermElabM (axiomsOk n)
  logInfo m!"{tag} ok: {n} kernel-checked, standard axioms only"

-- POSITIVE: extract (the probe's sizes and others; width, lo, len are free parameters)
derive_expr_t extA := (ext 8 6 1 5 : Lean.Expr)
run_cmd report "EXTRACT 8/6/1" `Tests.Gen5.FGCircuitPilotCheck38.extA
derive_expr_t extB := (ext 32 0 8 77 : Lean.Expr)
run_cmd report "EXTRACT 32/0/8" `Tests.Gen5.FGCircuitPilotCheck38.extB
derive_expr_t extC := (ext 32 2 2 77 : Lean.Expr)
run_cmd report "EXTRACT 32/2/2" `Tests.Gen5.FGCircuitPilotCheck38.extC
derive_expr_t extD := (ext 16 3 10 1 : Lean.Expr)
run_cmd report "EXTRACT 16/3/10 (not a probe size)" `Tests.Gen5.FGCircuitPilotCheck38.extD
derive_expr_t extE := (ext 64 60 9 1 : Lean.Expr)   -- the slice runs past the width: BitVec's own meaning (zero-extended), no side condition
run_cmd report "EXTRACT 64/60/9 (out of range: BitVec's meaning)" `Tests.Gen5.FGCircuitPilotCheck38.extE
-- POSITIVE: Signal <<< BitVec
derive_expr_t shlA := (shl dom 16 (sigC dom 16 3) (bvLit 16 8) : Lean.Expr)
run_cmd report "SHL 16" `Tests.Gen5.FGCircuitPilotCheck38.shlA
derive_expr_t shlB := (shl dom 32 (sigC dom 32 3) (bvLit 32 40) : Lean.Expr)   -- amount ≥ width: BitVec's own meaning
run_cmd report "SHL 32 (amount ≥ width)" `Tests.Gen5.FGCircuitPilotCheck38.shlB
-- POSITIVE: BitVec ++ Signal
derive_expr_t appA := (app dom 8 8 (bvLit 8 1) (sigC dom 8 2) : Lean.Expr)
run_cmd report "APPEND 8+8" `Tests.Gen5.FGCircuitPilotCheck38.appA
derive_expr_t appB := (app dom 8 16 (bvLit 8 1) (sigC dom 16 2) : Lean.Expr)
run_cmd report "APPEND 8+16" `Tests.Gen5.FGCircuitPilotCheck38.appB
-- POSITIVE (environment): `fun (d : DomainConfig) => #0 ...` — the SAME domain variable in every operand
def domV : Lean.Expr := .bvar 0
derive_expr_t shlEnv := (.lam `d (.const ``Sparkle.Core.Domain.DomainConfig []) (shl domV 8 (sigC domV 8 3) (bvLit 8 1)) .default : Lean.Expr)
run_cmd report "SHL under a domain binder" `Tests.Gen5.FGCircuitPilotCheck38.shlEnv

def errOf (n : Name) (e : Lean.Expr) : CommandElabM (Option String) := do
  try
    deriveTerm n e
    pure none
  catch ex => pure (some (← (liftCoreM ex.toMessageData.toString)))

def expectErr (tag : String) (n : Name) (e : Lean.Expr) (needle : String) : CommandElabM Unit := do
  match ← errOf n e with
  | none => throwError "{tag}: the control was derived"
  | some msg =>
    unless (msg.splitOn needle).length > 1 do throwError "{tag}: unexpected error text: {msg}"
    if (← getEnv).contains n then throwError "{tag}: a theorem was added"
    logInfo m!"{tag} ok: not derived, with the expected generator error «{needle}» (a generator failure, not a non-derivability theorem)"

abbrev N := `Tests.Gen5.FGCircuitPilotCheck38
-- extract controls
run_cmd expectErr "CTRL-EXT-WIDTH" (N ++ `cWidth) (mapExt dom (nat 8) (nat 1) (extFn (nat 8) (nat 9) (nat 6) (nat 1)) (sigC dom 8 5)) "differs from the input width"
run_cmd expectErr "CTRL-EXT-LEN" (N ++ `cLen) (mapExt dom (nat 8) (nat 1) (extFn (nat 8) (nat 8) (nat 6) (nat 2)) (sigC dom 8 5)) "differs from the result width"
run_cmd expectErr "CTRL-EXT-INPUT" (N ++ `cInput) (mapExt dom (nat 8) (nat 1) (extFn (nat 8) (nat 8) (nat 6) (nat 1)) (sigC dom 16 5)) "not a Signal of the same domain and width"
run_cmd expectErr "CTRL-EXT-OTHERFN" (N ++ `cOther) (mapExt dom (nat 8) (nat 8) (.lam `x (bvT (nat 8)) (.bvar 0) .default) (sigC dom 8 5)) "no direct rule"
run_cmd expectErr "CTRL-EXT-NOTVAR" (N ++ `cNotVar) (mapExt dom (nat 8) (nat 1) (.lam `x (bvT (nat 8)) (appN ``BitVec.extractLsb' [] [nat 8, nat 6, nat 1, bvLit 8 5]) .default) (sigC dom 8 5)) "no direct rule"
-- shift controls
run_cmd expectErr "CTRL-SHL-AMOUNT" (N ++ `cAmt) (shl dom 16 (sigC dom 16 3) (bvLit 8 8)) "not a BitVec of the signal's width"
run_cmd expectErr "CTRL-SHL-SIGNAL" (N ++ `cSig) (shl dom 16 (sigC dom 8 3) (bvLit 16 8)) "not a Signal of the instance's domain and width"
def eShlDom : Lean.Expr := .lam `d (.const ``Sparkle.Core.Domain.DomainConfig []) (shl dom 8 (sigC domV 8 3) (bvLit 8 1)) .default
run_cmd expectErr "CTRL-SHL-DOMAIN" (N ++ `cDom) eShlDom "not a Signal of the instance's domain and width"
-- append controls
run_cmd expectErr "CTRL-APP-SWAPPED" (N ++ `cSwap) (app dom 8 8 (sigC dom 8 2) (bvLit 8 1)) "left operand is not a BitVec"
run_cmd expectErr "CTRL-APP-RIGHTWIDTH" (N ++ `cRW) (app dom 8 8 (bvLit 8 1) (sigC dom 16 2)) "right operand is not a Signal"
def eAppOut : Lean.Expr :=
  appN ``HAppend.hAppend [.zero, .zero, .zero] [bvT (nat 8), sigT dom (bvT (nat 8)), sigT dom (bvT (natAdd (nat 8) (nat 9))),
    appN ``Sparkle.Core.Signal.instHAppendBitVecSignalHAddNat [] [nat 8, dom, nat 8], bvLit 8 1, sigC dom 8 2]
run_cmd expectErr "CTRL-APP-OUTWIDTH" (N ++ `cOW) eAppOut "do not agree with the instance"
def eAppInst : Lean.Expr :=
  appN ``HAppend.hAppend [.zero, .zero, .zero] [sigT dom (bvT (nat 8)), bvT (nat 8), sigT dom (bvT (natAdd (nat 8) (nat 8))),
    appN ``Sparkle.Core.Signal.instHAppendSignalBitVecHAddNat [] [nat 8, dom, nat 8], sigC dom 8 2, bvLit 8 1]
run_cmd expectErr "CTRL-APP-WRONGINSTANCE" (N ++ `cInst) eAppInst "no direct rule"

end Tests.Gen5.FGCircuitPilotCheck38
