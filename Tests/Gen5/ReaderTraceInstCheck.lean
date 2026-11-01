import Tools.ShippingGen5ReaderTraceInst
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT: written against freeze rev10 addendum §4 `scripts/gen5/DG_READERTRACE_FREEZE_REV10.md` (U-R7). No sorry / axiom / native_decide in source; the closure-control negatives are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R7 checks (Tools/ShippingGen5ReaderTraceInst.lean)

TYPE: the seven frozen theorems are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling); `instEntry_trace` (helper) is checked by AXIOMS and CLOSURE only.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples).
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceInstCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

section Expected

def ExpOut : Prop := ∀ {nDecl k' kk : Nat} {st : MachRead} (h : k' < st.insts.size),
    InRange nDecl st kk (machInstOut k')
def ExpLetIndex : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {nm : Name}
    {kd : MixedGateBinder} {v' : Lean.Expr} (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v'),
    TrInv senv nDecl { st with lets := (machLetIndex nm kd v' st.lets).2 }
def ExpDom : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v'),
    FReachC nDecl st { st with dom := some v' } ∧ TrInv senv nDecl { st with dom := some v' }
def ExpPushInst : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st)
    (c : Name) (js : List Nat) (r : MixedGateBinder) (o : Sparkle.Compiler.MachInstOrigin.InstOrigin) (f : String)
    (hj : ∀ a ∈ js, a < st.lets.size) (hr : r ≠ .domain)
    (ho : ∀ cb aw dw, o = .mem cb aw dw → js.length = 4 ∧ r = .bits dw) (hf : ∀ i, o ≠ .field i),
    FReachC nDecl st ({ st with insts := st.insts.push (c, js, r), instFields := st.instFields.push f, instOrigins := st.instOrigins.push o } : MachRead) ∧
    TrInv senv nDecl ({ st with insts := st.insts.push (c, js, r), instFields := st.instFields.push f, instOrigins := st.instOrigins.push o } : MachRead)
def ExpArg : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (k : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (kind : MixedGateBinder) (arg : Lean.Expr) (harg : NoPh arg = true ∧ BvarLt (env.length + nDecl) arg = true)
    (js : List Nat) (st : MachRead) (hI : InstFold senv nDecl st0 (js, st)),
    SatP (readF senv n) (fun p : List Nat × MachRead => InstFold senv nDecl st0 p ∧ p.1.length = js.length + nonDom kind)
      (instArg env k (js, st) (kind, arg))
def ExpFold : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (k : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (l : List (MixedGateBinder × Lean.Expr)), (∀ a ∈ l, NoPh a.2 = true ∧ BvarLt (env.length + nDecl) a.2 = true) →
    ∀ (js : List Nat) (st : MachRead), InstFold senv nDecl st0 (js, st) →
      SatP (readF senv n) (fun p : List Nat × MachRead => InstFold senv nDecl st0 p ∧
          p.1.length = js.length + (l.map fun a => nonDom a.1).sum)
        (foldO (instArg env k) (js, st) l)
def ExpInst : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (c : Name) (org : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (kinds : List MixedGateBinder) (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.inst env c org kinds res args st))
    (r : (Call.inst env c org kinds res args st).Res)
    (hv : (instStep env c org kinds res args st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.inst env c org kinds res args st) r) ∧
    PhPost senv nDecl (Call.inst env c org kinds res args st) r

def MutOutBound : Prop := ∀ {nDecl k' kk : Nat} {st : MachRead} (h : k' < st.kinds.size),
    InRange nDecl st kk (machInstOut k')
def MutLetIndexNoNL : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {nm : Name}
    {kd : MixedGateBinder} {v' : Lean.Expr} (h : InRange nDecl st st.lets.size v'),
    TrInv senv nDecl { st with lets := (machLetIndex nm kd v' st.lets).2 }
def MutDomNoReach : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v'),
    TrInv senv nDecl { st with dom := some v' }
def MutPushInstNoHf : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st)
    (c : Name) (js : List Nat) (r : MixedGateBinder) (o : Sparkle.Compiler.MachInstOrigin.InstOrigin) (f : String)
    (hj : ∀ a ∈ js, a < st.lets.size) (hr : r ≠ .domain)
    (ho : ∀ cb aw dw, o = .mem cb aw dw → js.length = 4 ∧ r = .bits dw),
    FReachC nDecl st ({ st with insts := st.insts.push (c, js, r), instFields := st.instFields.push f, instOrigins := st.instOrigins.push o } : MachRead) ∧
    TrInv senv nDecl ({ st with insts := st.insts.push (c, js, r), instFields := st.instFields.push f, instOrigins := st.instOrigins.push o } : MachRead)
def MutPushInstNoHr : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st)
    (c : Name) (js : List Nat) (r : MixedGateBinder) (o : Sparkle.Compiler.MachInstOrigin.InstOrigin) (f : String)
    (hj : ∀ a ∈ js, a < st.lets.size)
    (ho : ∀ cb aw dw, o = .mem cb aw dw → js.length = 4 ∧ r = .bits dw) (hf : ∀ i, o ≠ .field i),
    FReachC nDecl st ({ st with insts := st.insts.push (c, js, r), instFields := st.instFields.push f, instOrigins := st.instOrigins.push o } : MachRead) ∧
    TrInv senv nDecl ({ st with insts := st.insts.push (c, js, r), instFields := st.instFields.push f, instOrigins := st.instOrigins.push o } : MachRead)
def MutArgLen : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (k : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (kind : MixedGateBinder) (arg : Lean.Expr) (harg : NoPh arg = true ∧ BvarLt (env.length + nDecl) arg = true)
    (js : List Nat) (st : MachRead) (hI : InstFold senv nDecl st0 (js, st)),
    SatP (readF senv n) (fun p : List Nat × MachRead => InstFold senv nDecl st0 p ∧ p.1.length = js.length + 1)
      (instArg env k (js, st) (kind, arg))
def MutArgNoLen : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (k : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (kind : MixedGateBinder) (arg : Lean.Expr) (harg : NoPh arg = true ∧ BvarLt (env.length + nDecl) arg = true)
    (js : List Nat) (st : MachRead) (hI : InstFold senv nDecl st0 (js, st)),
    SatP (readF senv n) (fun p : List Nat × MachRead => InstFold senv nDecl st0 p)
      (instArg env k (js, st) (kind, arg))
def MutFoldNoPh : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (k : Nat) {st0 : MachRead} (hE0 : EnvOk st0.lets.size env) (hEp0 : EnvPh nDecl st0 env)
    (l : List (MixedGateBinder × Lean.Expr)),
    ∀ (js : List Nat) (st : MachRead), InstFold senv nDecl st0 (js, st) →
      SatP (readF senv n) (fun p : List Nat × MachRead => InstFold senv nDecl st0 p ∧
          p.1.length = js.length + (l.map fun a => nonDom a.1).sum)
        (foldO (instArg env k) (js, st) l)
def MutInstNoReach : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (c : Name) (org : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (kinds : List MixedGateBinder) (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.inst env c org kinds res args st))
    (r : (Call.inst env c org kinds res args st).Res)
    (hv : (instStep env c org kinds res args st).run (readF senv n) = some (some r)),
    PhPost senv nDecl (Call.inst env c org kinds res args st) r
def MutInstNoHT : Prop := ∀ (senv : StructEnv) (nDecl n : Nat)
    (env : List MachVal) (c : Name) (org : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (kinds : List MixedGateBinder) (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.inst env c org kinds res args st))
    (r : (Call.inst env c org kinds res args st).Res)
    (hv : (instStep env c org kinds res args st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.inst env c org kinds res args st) r) ∧
    PhPost senv nDecl (Call.inst env c org kinds res args st) r

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``inRange_machInstOut ``ExpOut
  checkExpected ``trInv_letIndex ``ExpLetIndex
  checkExpected ``trInv_dom ``ExpDom
  checkExpected ``trInv_pushInst ``ExpPushInst
  checkExpected ``instArg_trace ``ExpArg
  checkExpected ``instFold_trace ``ExpFold
  checkExpected ``inst_trace ``ExpInst
  logInfo m!"GEN5 INSTCHECK TYPE 7 theorems compared"
  checkMutant ``inRange_machInstOut ``MutOutBound
  checkMutant ``trInv_letIndex ``MutLetIndexNoNL
  checkMutant ``trInv_dom ``MutDomNoReach
  checkMutant ``trInv_pushInst ``MutPushInstNoHf
  checkMutant ``trInv_pushInst ``MutPushInstNoHr
  checkMutant ``instArg_trace ``MutArgLen
  checkMutant ``instArg_trace ``MutArgNoLen
  checkMutant ``instFold_trace ``MutFoldNoPh
  checkMutant ``inst_trace ``MutInstNoReach
  checkMutant ``inst_trace ``MutInstNoHT
  logInfo m!"GEN5 INSTCHECK MUTANT 10 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``inRange_machInstOut, ``trInv_letIndex, ``trInv_dom, ``trInv_pushInst, ``instArg_trace,
  ``instFold_trace, ``instEntry_trace, ``inst_trace]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 INSTCHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceInstCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceInstCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceInstCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceInstCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceInstCheck.direct, `ReaderTraceInstCheck.viaHelper, `ReaderTraceInstCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 INSTCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 INSTCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceInstCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 INSTCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 INSTCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceInstCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceInstCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceInstCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceInstCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceInstCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceInstCheck.Missing.nowhere do throwError "GEN5 INSTCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceInstCheck.viaHelperU, `ReaderTraceInstCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceInstCheck.Missing.nowhere do throwError "GEN5 INSTCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceInstCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 INSTCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 INSTCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 8 do throwError "GEN5 INSTCHECK CLOSURE FAILED: expected 8 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 INSTCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 INSTCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 INSTCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 INSTCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 INSTCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (8 theorems); all 8 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceInstCheck
