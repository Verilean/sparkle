import Tools.ShippingGen4KWalkFallback
import Tools.ShippingGen2Defs
import Tools.ShippingGen5T1ND
set_option autoImplicit false
-- NOT BUILT. Audit of Tools/ShippingGen4KWalk{Emit,Inst,ProjField,Canon,Fallback}.lean (S3 of scripts/gen4/KWALK_PLAN.md).

/-! # Audit of the S3 files

1. TYPE: each audited theorem's type is `isDefEq` to `Expected.*` below, written separately (`KeepsCP` unfolded to
   `∀ ctx st, CtxOk ctx → Keeps …`; `StableK` as `Expected.StableKOf` with `readOf`; `RecK` as `Expected.recKOf`).
2. MUTANT: signature/defeq REJECTIONS only. NOT semantic counterexamples.
3. AXIOMS: only propext / Classical.choice / Quot.sound.
4. CLOSURE: no `Laws` / `T1Hyp` / `T1HypND` constant in the transitive closure (positive controls: the detector flags
   `T1Hyp`, `T1HypND`). `MemoFamily` is allowed (it is the hypothesis `M`). -/

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Sparkle.Compiler.Elab

namespace Tests.Gen4.KWalkFallbackCheck

namespace Expected

def StableKOf (quiet : Void IO.RealWorld → Prop) (I : Void IO.RealWorld → Prop) : Prop :=
  (∀ w, I w → quiet w) ∧
  (∀ w w', readOf sparkleChildCache w' = readOf sparkleChildCache w →
    readOf sparkleChildSynth w' = readOf sparkleChildSynth w →
    readOf sparkleSynthDepth w' = readOf sparkleSynthDepth w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w →
    (quiet w → quiet w') → I w → I w')

def recKOf {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) (rec : TranslateFn) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ e hint top named (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (rec e hint top named ctx st)

def projField : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I → ∀ (n s : Name),
    Keeps mctx mref cctx cref I (projFieldName? n s)

def throwErr : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I → ∀ {α : Type} (msg : MessageData), OkMsg msg →
    Keeps mctx mref cctx cref I (Lean.throwError msg : MetaM α)

def canonKey : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I → ∀ (value : Lean.Expr)
    (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (canonHardwareKey value ctx st)

def legacyImpl {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ rec, recKOf O I rec →
    recKOf O I (fun e h t n => Rec.translateExprToWireImpl (fun e h t n => rec e h t n) e h t n)

def legacyCached {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ rec, recKOf O I rec →
    recKOf O I (fun e h t n => Rec.translateExprToWireCached (fun e h t n => rec e h t n) e h t n)

def childEntry {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (I : Void IO.RealWorld → Prop) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx O.quiet mctx cctx →
    ∀ c, Keeps mctx mref cctx cref I (childSynthEntry c)

def fallback : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I → ∀ (tenv : Lean.Environment),
    legacyImpl O I → legacyCached O I → childEntry O I →
    ∀ (rec : TranslateFn), recKOf O I rec → recKOf O I (translateFallback tenv rec)

def translator : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I → ∀ (tenv : Lean.Environment),
    legacyImpl O I → legacyCached O I → childEntry O I →
    recKOf O I (fun e h t n => translateExprToWire tenv e h t n)

end Expected

namespace Mutant

/-- M1: `projFieldNameK` without the `MemoFamily` hypothesis. -/
def M1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, Expected.StableKOf O.quiet I → ∀ (n s : Name),
    Keeps mctx mref cctx cref I (projFieldName? n s)

/-- M2: `translateFallbackK` without the child-entry hypothesis. -/
def M2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O →
    ∀ {I : Void IO.RealWorld → Prop}, Expected.StableKOf O.quiet I → ∀ (tenv : Lean.Environment),
    Expected.legacyImpl O I → Expected.legacyCached O I →
    ∀ (rec : TranslateFn), Expected.recKOf O I rec → Expected.recKOf O I (translateFallback tenv rec)

/-- M3: `keepsK_throwError` without the message-class hypothesis. -/
def M3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, Expected.StableKOf O.quiet I → ∀ {α : Type} (msg : MessageData),
    Keeps mctx mref cctx cref I (Lean.throwError msg : MetaM α)

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

elab "#kwalkfallback_check" : command => liftTermElabM do
  let pf := `Tools.ShippingGen4KWalkProjField
  let ck := `Tools.ShippingGen4KWalkCanon
  let fb := `Tools.ShippingGen4KWalkFallback
  let pre := `Tests.Gen4.KWalkFallbackCheck
  let typeCases : List (Name × Name) :=
    [(pf ++ `projFieldNameK, pre ++ `Expected ++ `projField),
     (pf ++ `keepsK_throwError, pre ++ `Expected ++ `throwErr),
     (ck ++ `canonHardwareKeyK, pre ++ `Expected ++ `canonKey),
     (fb ++ `translateFallbackK, pre ++ `Expected ++ `fallback),
     (fb ++ `translate_keepsK, pre ++ `Expected ++ `translator)]
  let mutCases : List (String × Name × Name) :=
    [("M1", pf ++ `projFieldNameK, `M1), ("M2", fb ++ `translateFallbackK, `M2),
     ("M3", pf ++ `keepsK_throwError, `M3)]
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
    [`Tools.ShippingGen4KWalkEmit.translateBoolUncachedWithK,
     `Tools.ShippingGen4KWalkEmit.translateLoopRegisterUncachedWithK,
     `Tools.ShippingGen4KWalkInst.translateInstanceUncachedWithK,
     `Tools.ShippingGen4KWalkInst.translateProjInstanceUncachedWithK,
     `Tools.ShippingGen4KWalkInst.translateInstanceOrFallbackK]
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
  logInfo m!"KWALKFALLBACK CHECK: TYPE {ok}/5 / MUTANT {rej}/3 (signature/defeq rejections, not semantic counterexamples) / AXIOMS {axOk}/{audited.length} standard-only / CLOSURE {clOk}/{audited.length} clean (+2 positive controls)"

#kwalkfallback_check

end Tests.Gen4.KWalkFallbackCheck
