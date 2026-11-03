import Tools.ShippingGen4KWalkTranslate
import Tools.ShippingGen2Defs
import Tools.ShippingGen5T1ND
set_option autoImplicit false
-- NOT BUILT. Audit of Tools/ShippingGen4KWalkTranslate.lean (S2 of scripts/gen4/KWALK_PLAN.md).

/-! # Audit of Tools/ShippingGen4KWalkTranslate.lean

1. TYPE: each audited theorem's type is `isDefEq` to `Expected.*` below, written separately (`KeepsCP` unfolded to
   `∀ ctx st, CtxOk ctx → Keeps …`; `StableK` as `Expected.StableKOf` with `readOf`).
2. MUTANT: signature/defeq REJECTIONS only. NOT semantic counterexamples.
3. AXIOMS: only propext / Classical.choice / Quot.sound.
4. CLOSURE: no `Laws` / `T1Hyp` / `T1HypND` constant in the transitive closure (positive controls: the detector flags
   `T1Hyp`, `T1HypND`). `MemoFamily` is allowed (it is the hypothesis `M`). -/

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Sparkle.Compiler.Elab

namespace Tests.Gen4.KWalkTranslateCheck

namespace Expected

def StableKOf (quiet : Void IO.RealWorld → Prop) (I : Void IO.RealWorld → Prop) : Prop :=
  (∀ w, I w → quiet w) ∧
  (∀ w w', readOf sparkleChildCache w' = readOf sparkleChildCache w →
    readOf sparkleChildSynth w' = readOf sparkleChildSynth w →
    readOf sparkleSynthDepth w' = readOf sparkleSynthDepth w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w →
    (quiet w → quiet w') → I w → I w')

def pureLiteral : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I →
    ∀ (args : Array Lean.Expr) (hint : String) (named : Bool)
      (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (translateSignalPureLiteral? args hint named ctx st)

def core : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I →
    ∀ (rec : TranslateFn),
    (∀ e hint top named (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
      Keeps mctx mref cctx cref I (rec e hint top named ctx st)) →
    ∀ (e : Lean.Expr) (hint : String) (top named : Bool) (ctx : CompilerState)
      (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (translateCore rec e hint top named ctx st)

def stepWith : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I →
    ∀ (fallback : TranslateFn → TranslateFn) (rec : TranslateFn),
    (∀ e hint top named (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
      Keeps mctx mref cctx cref I (rec e hint top named ctx st)) →
    (∀ e hint top named (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
      Keeps mctx mref cctx cref I (fallback rec e hint top named ctx st)) →
    ∀ (e : Lean.Expr) (hint : String) (top named : Bool) (ctx : CompilerState)
      (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (translateStepWith fallback rec e hint top named ctx st)

/-- The translator keeps `I` in every admissible context, given that the fallback does whenever its argument does. -/
def fromFallback : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I →
    ∀ (tenv : Lean.Environment),
    (∀ rec : TranslateFn,
      (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
        ∀ e hint top named (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
        Keeps mctx mref cctx cref I (rec e hint top named ctx st)) →
      (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
        ∀ e hint top named (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
        Keeps mctx mref cctx cref I (translateFallback tenv rec e hint top named ctx st))) →
    ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (translateExprToWire tenv e hint top named ctx st)

end Expected

namespace Mutant

/-- M1: `translateCoreK` without the `MemoFamily` hypothesis. -/
def M1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, Expected.StableKOf O.quiet I →
    ∀ (rec : TranslateFn),
    (∀ e hint top named (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
      Keeps mctx mref cctx cref I (rec e hint top named ctx st)) →
    ∀ (e : Lean.Expr) (hint : String) (top named : Bool) (ctx : CompilerState)
      (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (translateCore rec e hint top named ctx st)

/-- M2: `translateStepWithK` without the fallback hypothesis. -/
def M2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, Expected.StableKOf O.quiet I →
    ∀ (fallback : TranslateFn → TranslateFn) (rec : TranslateFn),
    (∀ e hint top named (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
      Keeps mctx mref cctx cref I (rec e hint top named ctx st)) →
    ∀ (e : Lean.Expr) (hint : String) (top named : Bool) (ctx : CompilerState)
      (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (translateStepWith fallback rec e hint top named ctx st)

/-- M3: `translateK_of_fallback` without the `AdmCtx` hypothesis on the context. -/
def M3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O →
    ∀ {I : Void IO.RealWorld → Prop}, Expected.StableKOf O.quiet I →
    ∀ (tenv : Lean.Environment),
    (∀ rec : TranslateFn,
      (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
        ∀ e hint top named (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
        Keeps mctx mref cctx cref I (rec e hint top named ctx st)) →
      (∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
        ∀ e hint top named (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
        Keeps mctx mref cctx cref I (translateFallback tenv rec e hint top named ctx st))) →
    ∀ (mctx : Meta.Context) (cctx : Core.Context),
    ∀ e hint top named (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (translateExprToWire tenv e hint top named ctx st)

end Mutant

/-! ## The checker -/

private partial def closure (env : Environment) (todo : List Name) (seen : NameSet) (opq : NameSet) :
    NameSet × NameSet :=
  match todo with
  | [] => (seen, opq)
  | n :: rest =>
    if seen.contains n then closure env rest seen opq else
    let seen := seen.insert n
    match env.find? n with
    | none => closure env rest seen opq
    | some ci =>
      let (body, opq) : List Name × NameSet := match ci with
        | .thmInfo v => (v.value.getUsedConstants.toList, opq)
        | .defnInfo v => (v.value.getUsedConstants.toList, opq)
        | .opaqueInfo _ => ([], opq.insert n)
        | _ => ([], opq)
      closure env (ci.type.getUsedConstants.toList ++ body ++ rest) seen opq

private def forbidden : List Name :=
  [`Tools.ShippingGen2.Laws, `Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND]

private def closureBad (n : Name) : CoreM (List Name × Nat) := do
  let (seen, _) := closure (← getEnv) [n] {} {}
  return (seen.toList.filter fun m => forbidden.any fun f => f.isPrefixOf m, seen.size)

elab "#kwalktranslate_check" : command => liftTermElabM do
  let w := `Tools.ShippingGen4KWalkTranslate
  let pre := `Tests.Gen4.KWalkTranslateCheck
  let typeCases : List (Name × Name) :=
    [(w ++ `translateSignalPureLiteralK, pre ++ `Expected ++ `pureLiteral),
     (w ++ `translateCoreK, pre ++ `Expected ++ `core),
     (w ++ `translateStepWithK, pre ++ `Expected ++ `stepWith),
     (w ++ `translateK_of_fallback, pre ++ `Expected ++ `fromFallback)]
  let mutCases : List (String × Name × Name) :=
    [("M1", w ++ `translateCoreK, `M1), ("M2", w ++ `translateStepWithK, `M2),
     ("M3", w ++ `translateK_of_fallback, `M3)]
  let mut ok : Nat := 0
  for (t, e) in typeCases do
    let ti ← getConstInfo t
    unless ← isDefEq ti.type (mkConst e) do throwError "TYPE mismatch for {t}"
    ok := ok + 1
  let mut rej : Nat := 0
  for (lbl, t, m) in mutCases do
    let ti ← getConstInfo t
    if ← isDefEq ti.type (mkConst (pre ++ `Mutant ++ m)) then throwError "mutant {lbl} NOT rejected for {t}"
    rej := rej + 1
  let audited : List Name := typeCases.map (·.1) ++
    [w ++ `translateCanonicalSignalBinaryK, w ++ `fuelZeroK]
  let mut axOk : Nat := 0
  let mut clOk : Nat := 0
  for n in audited do
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a)
    unless bad.isEmpty do throwError "{n}: axioms {bad}"
    axOk := axOk + 1
    let (bad, _) ← closureBad n
    unless bad.isEmpty do throwError "{n}: forbidden constants {bad}"
    clOk := clOk + 1
  for c in [`Tools.ShippingGen2.T1Hyp, `Tools.ShippingGen2.T1HypND] do
    let (bad, _) ← closureBad c
    if bad.isEmpty then throwError "closure detector MISSED {c}"
  logInfo m!"KWALKTRANSLATE CHECK: TYPE {ok}/4 / MUTANT {rej}/3 (signature/defeq rejections, not semantic counterexamples) / AXIOMS {axOk}/{audited.length} standard-only / CLOSURE {clOk}/{audited.length} clean (+2 positive controls)"

#kwalktranslate_check

end Tests.Gen4.KWalkTranslateCheck
