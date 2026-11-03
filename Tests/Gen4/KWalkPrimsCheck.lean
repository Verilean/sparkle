import Tools.ShippingGen4KWalkPrims
import Tools.ShippingGen2Defs
import Tools.ShippingGen5T1ND
set_option autoImplicit false
-- BUILT: kjob lake build Tests.Gen4.KWalkPrimsCheck exit 0 (745 jobs, rt165, source as of 3ce5d54f): KWALKPRIMS CHECK: TYPE 7/7 / MUTANT 3/3 (signature/defeq rejections, not semantic counterexamples) / AXIOMS 14/14 standard-only / CLOSURE 14/14 clean (+2 positive controls). Clean build is the coder's. Audit of Tools/ShippingGen4KWalkPrims.lean (S1 of scripts/gen4/KWALK_PLAN.md).

/-! # Audit of Tools/ShippingGen4KWalkPrims.lean

1. TYPE: each audited theorem's type is `isDefEq` to `Expected.*` below, written separately from the plan's sentence
   ("`StableK` = `StableA`'s transport condition plus `mv w' = mv w`"; the world reads are spelled with `readOf`).
2. MUTANT: signature/defeq REJECTIONS only (a mutant's type is not defeq to the theorem's). NOT semantic counterexamples.
3. AXIOMS: only propext / Classical.choice / Quot.sound.
4. CLOSURE: the transitive constant closure of each theorem contains no `Laws` / `T1Hyp` / `T1HypND` constant
   (positive controls: the detector flags `T1Hyp`, `T1HypND`). `MemoFamily` is allowed (it is the hypothesis `M`). -/

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildTranslateA
open Sparkle.Compiler.Elab

namespace Tests.Gen4.KWalkPrimsCheck

abbrev Mem := Std.HashMap Name Res

namespace Expected

/-- `StableA`'s transport condition (cache, synth ref, depth) plus the memo. -/
def StableKOf (quiet : Void IO.RealWorld → Prop) (I : Void IO.RealWorld → Prop) : Prop :=
  (∀ w, I w → quiet w) ∧
  (∀ w w', readOf sparkleChildCache w' = readOf sparkleChildCache w →
    readOf sparkleChildSynth w' = readOf sparkleChildSynth w →
    readOf sparkleSynthDepth w' = readOf sparkleSynthDepth w →
    readOf sparkleSubModuleCache w' = readOf sparkleSubModuleCache w →
    (quiet w → quiet w') → I w → I w')

def framedNM : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I →
    ∀ {α : Type} {p : MetaM α}, Tools.Assume.MemoFamily.FramedNM MkRefd p →
    Keeps mctx mref cctx cref I p

def makeWire : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I →
    ∀ (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool),
    ∀ (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (CompilerM.makeWire hint ty named ctx st)

def addInput : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I →
    ∀ (name : String) (ty : Sparkle.IR.Type.HWType),
    ∀ (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (CompilerM.addInput name ty ctx st)

def addOutput : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I →
    ∀ (name : String) (ty : Sparkle.IR.Type.HWType),
    ∀ (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (CompilerM.addOutput name ty ctx st)

def lookup : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I →
    ∀ (e : Lean.Expr) (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (cacheLookupValidated e ctx st)

def record : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableKOf O.quiet I →
    ∀ (e : Lean.Expr) (w : String) (cacheable : Bool) (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState), CtxOk ctx →
    Keeps mctx mref cctx cref I (recordTranslation e w cacheable ctx st)

def stableKW : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (P : Mem → Mem → Prop),
    StableKOf O.quiet (fun w => O.quiet w ∧ readOf sparkleChildSynth w = some synthesizeChild ∧
      P (readOf sparkleSubModuleCache w) (readOf sparkleChildCache w))

end Expected

namespace Mutant

/-- M1: the transport condition without the memo equation (`StableA`'s shape) — the K primitive is not stated for it. -/
def StableNoMemo (quiet : Void IO.RealWorld → Prop) (I : Void IO.RealWorld → Prop) : Prop :=
  (∀ w, I w → quiet w) ∧
  (∀ w w', readOf sparkleChildCache w' = readOf sparkleChildCache w →
    readOf sparkleChildSynth w' = readOf sparkleChildSynth w →
    readOf sparkleSynthDepth w' = readOf sparkleSynthDepth w →
    (quiet w → quiet w') → I w → I w')

def M1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, StableNoMemo O.quiet I →
    ∀ {α : Type} {p : MetaM α}, Tools.Assume.MemoFamily.FramedNM MkRefd p →
    Keeps mctx mref cctx cref I p

/-- M2: `keepsK_framedNM` without the `MemoFamily` hypothesis. -/
def M2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, Expected.StableKOf O.quiet I →
    ∀ {α : Type} {p : MetaM α}, Tools.Assume.MemoFamily.FramedNM MkRefd p →
    Keeps mctx mref cctx cref I p

/-- M3: `makeWireK` without the `CtxOk` hypothesis. -/
def M3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {O : RefLawsAOps MkRefd mref cref},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {I : Void IO.RealWorld → Prop}, Expected.StableKOf O.quiet I →
    ∀ (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool),
    ∀ (ctx : CompilerState) (st : Sparkle.IR.Builder.CircuitState),
    Keeps mctx mref cctx cref I (CompilerM.makeWire hint ty named ctx st)

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

elab "#kwalkprims_check" : command => liftTermElabM do
  let w := `Tools.ShippingGen4KWalkPrims
  let pre := `Tests.Gen4.KWalkPrimsCheck
  let typeCases : List (Name × Name) :=
    [(w ++ `keepsK_framedNM, pre ++ `Expected ++ `framedNM), (w ++ `makeWirePK, pre ++ `Expected ++ `makeWire),
     (w ++ `addInputPK, pre ++ `Expected ++ `addInput), (w ++ `addOutputPK, pre ++ `Expected ++ `addOutput),
     (w ++ `cacheLookupValidatedK, pre ++ `Expected ++ `lookup), (w ++ `recordTranslationK, pre ++ `Expected ++ `record),
     (w ++ `stableK_KW, pre ++ `Expected ++ `stableKW)]
  let mutCases : List (String × Name × Name) :=
    [("M1", w ++ `keepsK_framedNM, `M1), ("M2", w ++ `keepsK_framedNM, `M2), ("M3", w ++ `makeWirePK, `M3)]
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
    [w ++ `StableK, w ++ `wireWidthK, w ++ `makeWireK, w ++ `addInputK, w ++ `addOutputK, w ++ `emitRegisterK,
     w ++ `emitMemoryK]
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
  logInfo m!"KWALKPRIMS CHECK: TYPE {ok}/7 / MUTANT {rej}/3 (signature/defeq rejections, not semantic counterexamples) / AXIOMS {axOk}/{audited.length} standard-only / CLOSURE {clOk}/{audited.length} clean (+2 positive controls)"

#kwalkprims_check

end Tests.Gen4.KWalkPrimsCheck
