import Tools.ShippingGen5ReaderTraceLet
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in Pod (kjob lake build Tests.Gen5.ReaderTraceLetCheck, exit 0; TYPE 8 theorems; MUTANT 10 theorem-statement mutants (signature/defeq rejections, not semantic counterexamples); AXIOMS 9 (standard only); CLOSURE OK 4932 constants from 9 roots, 9 targets seen; 3 intended in-memory sorry negatives print warnings) on the tree of d6839f6362a55d0aa07c562f8d839e4803a7c7cb (Lean content identical; this header is comment-only). Written against freeze rev10 `scripts/gen5/DG_READERTRACE_FREEZE_REV10.md` (U-R5a). No sorry / axiom / native_decide in source; the closure-control negatives are built in memory (no `sorry` token).
/-! # DG-READERTRACE U-R5a checks (Tools/ShippingGen5ReaderTraceLet.lean)

TYPE: the eight frozen theorems are compared by `checkExpected` against `Exp…` statements written here from the freeze text (own spelling); `trInv_pushLet` (helper) is checked by AXIOMS and CLOSURE only.
Mutants are well-typed single changes, rejected by signature / defeq (NOT semantic counterexamples).
CLOSURE: value-closure walk from the new declarations, forbidden-root self-hit, unknown-root / helper value / helper type controls, clean controls. -/

namespace Tests.Gen5.ReaderTraceLetCheck
open Lean Meta Elab
open Tools.ShippingGen5ReaderTrace Tools.ShippingGen5Cover6 Tests.Gen3.ExpectedType
open Sparkle.Compiler.Elab Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover2 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv

section Expected

def ExpLift01 : Prop := ∀ (hla : LiftAgrees) {e : Lean.Expr} {L : Nat} (hn : NoPh e = true) (hb : BvarLt L e = true),
    NoPh (e.liftLooseBVars 0 1) = true ∧ BvarLt (L + 1) (e.liftLooseBVars 0 1) = true
def ExpLift11 : Prop := ∀ (hla : LiftAgrees) {e : Lean.Expr} {L : Nat} (hn : NoPh e = true) (hb : BvarLt L e = true),
    NoPh (e.liftLooseBVars 1 1) = true ∧ BvarLt (L + 1) (e.liftLooseBVars 1 1) = true
def ExpRootFloat : Prop := ∀ (hrf : RootFloatAgrees) {v : Lean.Expr} {L : Nat} (hn : NoPh v = true) (hb : BvarLt L v = true),
    NoPh (Sparkle.Compiler.MachRawSurface.rootFloat v) = true ∧ BvarLt L (Sparkle.Compiler.MachRawSurface.rootFloat v) = true
def ExpRegs : Prop := ∀ {nDecl : Nat} {st : MachRead} {env : List MachVal} (h : EnvPh nDecl st env) (p : Nat),
    EnvPh nDecl st (MachVal.regs p :: env)
def ExpHandle : Prop := ∀ {nDecl : Nat} {st : MachRead} {env : List MachVal} (h : EnvPh nDecl st env) (i : Nat),
    EnvPh nDecl st (MachVal.handle i :: env)
def ExpRoot : Prop := ∀ {nDecl : Nat} {st : MachRead} {env : List MachVal} {mv : MachVal} (h : EnvPh nDecl st env)
    (hs : ∀ b n, mv = MachVal.state b n → b + n ≤ st.kinds.size)
    (hv : ∀ v, mv = MachVal.val v → InRange nDecl st st.lets.size v ∧ NoLoose 0 v), EnvPh nDecl st (mv :: env)
def ExpBindLet : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {nm : Name}
    {ty v' : Lean.Expr} (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v'),
    TrInv senv nDecl { st with lets := (machBindLet nm ty v' st.lets).2 }
def ExpLetE : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.letE nm ty v b nd) st))
    (r : (Call.conv env d (.letE nm ty v b nd) st).Res)
    (hv : (convStep senv env d (.letE nm ty v b nd) st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.conv env d (.letE nm ty v b nd) st) r) ∧
    PhPost senv nDecl (Call.conv env d (.letE nm ty v b nd) st) r

-- theorem mutants (well-typed single changes)

def MutLift01NoHla : Prop := ∀ {e : Lean.Expr} {L : Nat} (hn : NoPh e = true) (hb : BvarLt L e = true),
    NoPh (e.liftLooseBVars 0 1) = true ∧ BvarLt (L + 1) (e.liftLooseBVars 0 1) = true
def MutLift01L : Prop := ∀ (hla : LiftAgrees) {e : Lean.Expr} {L : Nat} (hn : NoPh e = true) (hb : BvarLt L e = true),
    NoPh (e.liftLooseBVars 0 1) = true ∧ BvarLt L (e.liftLooseBVars 0 1) = true
def MutLift11At0 : Prop := ∀ (hla : LiftAgrees) {e : Lean.Expr} {L : Nat} (hn : NoPh e = true) (hb : BvarLt L e = true),
    NoPh (e.liftLooseBVars 0 1) = true ∧ BvarLt (L + 1) (e.liftLooseBVars 0 1) = true ∧ BvarLt (L + 1) (e.liftLooseBVars 1 1) = true
def MutRootFloatNoHrf : Prop := ∀ {v : Lean.Expr} {L : Nat} (hn : NoPh v = true) (hb : BvarLt L v = true),
    NoPh (Sparkle.Compiler.MachRawSurface.rootFloat v) = true ∧ BvarLt L (Sparkle.Compiler.MachRawSurface.rootFloat v) = true
def MutRootFloatL1 : Prop := ∀ (hrf : RootFloatAgrees) {v : Lean.Expr} {L : Nat} (hn : NoPh v = true) (hb : BvarLt L v = true),
    NoPh (Sparkle.Compiler.MachRawSurface.rootFloat v) = true ∧ BvarLt (L + 1) (Sparkle.Compiler.MachRawSurface.rootFloat v) = true
def MutRootNoHs : Prop := ∀ {nDecl : Nat} {st : MachRead} {env : List MachVal} {mv : MachVal} (h : EnvPh nDecl st env)
    (hv : ∀ v, mv = MachVal.val v → InRange nDecl st st.lets.size v ∧ NoLoose 0 v), EnvPh nDecl st (mv :: env)
def MutBindLetNoNL : Prop := ∀ {senv : StructEnv} {nDecl : Nat} {st : MachRead} (hTr : TrInv senv nDecl st) {nm : Name}
    {ty v' : Lean.Expr} (h : InRange nDecl st st.lets.size v'),
    TrInv senv nDecl { st with lets := (machBindLet nm ty v' st.lets).2 }
def MutLetENoHrf : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.letE nm ty v b nd) st))
    (r : (Call.conv env d (.letE nm ty v b nd) st).Res)
    (hv : (convStep senv env d (.letE nm ty v b nd) st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.conv env d (.letE nm ty v b nd) st) r) ∧
    PhPost senv nDecl (Call.conv env d (.letE nm ty v b nd) st) r
def MutLetENoReach : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.letE nm ty v b nd) st))
    (r : (Call.conv env d (.letE nm ty v b nd) st).Res)
    (hv : (convStep senv env d (.letE nm ty v b nd) st).run (readF senv n) = some (some r)),
    PhPost senv nDecl (Call.conv env d (.letE nm ty v b nd) st) r
def MutLetENoHpre : Prop := ∀ (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (nm : Name) (ty v b : Lean.Expr) (nd : Bool) (st : MachRead)
    (r : (Call.conv env d (.letE nm ty v b nd) st).Res)
    (hv : (convStep senv env d (.letE nm ty v b nd) st).run (readF senv n) = some (some r)),
    FReachC nDecl st (callOut (Call.conv env d (.letE nm ty v b nd) st) r) ∧
    PhPost senv nDecl (Call.conv env d (.letE nm ty v b nd) st) r

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``lift01_ph ``ExpLift01
  checkExpected ``lift11_ph ``ExpLift11
  checkExpected ``rootFloat_ph ``ExpRootFloat
  checkExpected ``envPh_cons_regs ``ExpRegs
  checkExpected ``envPh_cons_handle ``ExpHandle
  checkExpected ``envPh_cons_root ``ExpRoot
  checkExpected ``trInv_bindLet ``ExpBindLet
  checkExpected ``conv_letE_trace ``ExpLetE
  logInfo m!"GEN5 LETCHECK TYPE 8 theorems compared"
  checkMutant ``lift01_ph ``MutLift01NoHla
  checkMutant ``lift01_ph ``MutLift01L
  checkMutant ``lift11_ph ``MutLift11At0
  checkMutant ``rootFloat_ph ``MutRootFloatNoHrf
  checkMutant ``rootFloat_ph ``MutRootFloatL1
  checkMutant ``envPh_cons_root ``MutRootNoHs
  checkMutant ``trInv_bindLet ``MutBindLetNoNL
  checkMutant ``conv_letE_trace ``MutLetENoHrf
  checkMutant ``conv_letE_trace ``MutLetENoReach
  checkMutant ``conv_letE_trace ``MutLetENoHpre
  logInfo m!"GEN5 LETCHECK MUTANT 10 theorem-statement mutants rejected (signature/defeq rejection, not semantic counterexamples)"

def newThms : List Name := [``lift01_ph, ``lift11_ph, ``rootFloat_ph, ``envPh_cons_regs, ``envPh_cons_handle, ``envPh_cons_root,
  ``trInv_pushLet, ``trInv_bindLet, ``conv_letE_trace]

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in newThms do checkAxioms n
  logInfo m!"GEN5 LETCHECK AXIOMS {newThms.length} theorems checked (standard axioms only)"

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
    addDecl (.thmDecl { name := `ReaderTraceLetCheck.direct, levelParams := [], type := tru, value := bad })
    addDecl (.defnDecl { name := `Other.Ns.helperD, levelParams := [], type := tru, value := bad, hints := .abbrev, safety := .safe })
    addDecl (.thmDecl { name := `ReaderTraceLetCheck.viaHelper, levelParams := [], type := tru, value := mkConst `Other.Ns.helperD })
    addDecl (.opaqueDecl { name := `Another.Ns.helperO, levelParams := [], type := tru, value := bad, isUnsafe := false })
    addDecl (.thmDecl { name := `ReaderTraceLetCheck.viaOpaque, levelParams := [], type := tru, value := mkConst `Another.Ns.helperO })
    addDecl (.thmDecl { name := `ReaderTraceLetCheck.clean1, levelParams := [], type := tru, value := ok })
    addDecl (.defnDecl { name := `Elsewhere.clean2, levelParams := [], type := tru, value := ok, hints := .abbrev, safety := .safe })
    let env ← getEnv
    for n in [`ReaderTraceLetCheck.direct, `ReaderTraceLetCheck.viaHelper, `ReaderTraceLetCheck.viaOpaque] do
      let (_, _, hits) ← closureHits env [n]
      if hits.isEmpty then throwError "GEN5 LETCHECK CLOSURE CONTROL FAILED: {n} not detected"
    -- the forbidden root itself (not reached through a helper value)
    for f in forbiddenConsts do
      let (_, _, hits) ← closureHits env [f]
      unless hits.contains f do throwError "GEN5 LETCHECK CLOSURE CONTROL FAILED: forbidden root {f} does not hit itself"
    for n in [`ReaderTraceLetCheck.clean1, `Elsewhere.clean2] do
      let (_, _, hits) ← closureHits env [n]
      unless hits.isEmpty do throwError "GEN5 LETCHECK CLOSURE CONTROL FAILED: clean control {n} flagged {hits}"
    logInfo m!"GEN5 LETCHECK CLOSURE CONTROLS OK: 3 negative controls detected, 3 forbidden roots (sorryAx, ofReduceBool, trustCompiler) hit themselves, 2 unrelated clean controls clean"

-- Unknown-name controls: the SAME `closureHits` path must report `unk` non-empty for a name the environment lacks, whether it is a root, reached through a
-- declaration in another namespace (helper resolution), or reached through a helper's type. The fixtures reference a missing constant, so they are added with
-- `debug.skipKernelTC` (inside `withoutModifyingEnv`); they are not sorry-based. The final `unknown` gate is the same predicate (`unk.isEmpty`) used below.
run_cmd Lean.Elab.Command.liftTermElabM do
  withoutModifyingEnv do
    let tru := mkConst ``True
    let ok := mkConst ``True.intro
    let missing := mkConst `ReaderTraceLetCheck.Missing.nowhere
    withOptions (fun o => o.setBool `debug.skipKernelTC true) do
      addDecl (.defnDecl { name := `Other.Ns.helperU, levelParams := [], type := tru, value := missing, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceLetCheck.viaHelperU, levelParams := [], type := tru, value := mkConst `Other.Ns.helperU })
      addDecl (.defnDecl { name := `Another.Ns.helperT, levelParams := [], type := missing, value := ok, hints := .abbrev, safety := .safe })
      addDecl (.thmDecl { name := `ReaderTraceLetCheck.viaHelperT, levelParams := [], type := tru, value := mkConst `Another.Ns.helperT })
      addDecl (.thmDecl { name := `ReaderTraceLetCheck.cleanU, levelParams := [], type := tru, value := ok })
    let env ← getEnv
    let (_, unkRoot, _) ← closureHits env [`ReaderTraceLetCheck.Missing.nowhere]
    unless unkRoot.contains `ReaderTraceLetCheck.Missing.nowhere do throwError "GEN5 LETCHECK UNKNOWN CONTROL FAILED: missing root not reported"
    for n in [`ReaderTraceLetCheck.viaHelperU, `ReaderTraceLetCheck.viaHelperT] do
      let (_, unk, _) ← closureHits env [n]
      unless unk.contains `ReaderTraceLetCheck.Missing.nowhere do throwError "GEN5 LETCHECK UNKNOWN CONTROL FAILED: {n} does not reach the unknown name"
    let (_, unkClean, _) ← closureHits env [`ReaderTraceLetCheck.cleanU]
    unless unkClean.isEmpty do throwError "GEN5 LETCHECK UNKNOWN CONTROL FAILED: clean control reported unknown {unkClean.toList}"
    logInfo m!"GEN5 LETCHECK UNKNOWN CONTROLS OK: 3 negative (root, helper value, helper type) reported unknown, 1 clean not"

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (seen, unk, hits) ← closureHits env closureRoots
  unless newThms.length == 9 do throwError "GEN5 LETCHECK CLOSURE FAILED: expected 9 theorems"
  for n in newThms do
    unless seen.contains n do throwError "GEN5 LETCHECK CLOSURE FAILED: target declaration {n} not in the closure seen set"
  unless hits.isEmpty do throwError "GEN5 LETCHECK CLOSURE FAILED: forbidden constants {hits}"
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "native_decide").length > 1 then
      throwError "GEN5 LETCHECK CLOSURE FAILED: unexpected constant {n}"
  unless unk.isEmpty do throwError "GEN5 LETCHECK CLOSURE FAILED: unknown constants (not in the environment): {unk.toList}"
  logInfo m!"GEN5 LETCHECK CLOSURE OK: {seen.toList.length} constants from {closureRoots.length} roots (9 theorems); all 9 target declarations in seen, no forbidden constant"

end Tests.Gen5.ReaderTraceLetCheck
