import Tools.ShippingGen4KWalk
import Tools.ShippingGen2Defs
import Tools.ShippingGen5T1ND
set_option autoImplicit false
-- BUILT: kjob lake build Tests.Gen4.KWalkCheck exit 0 (744 jobs, rt164, source as of df94a168): KWALK CHECK: TYPE 7/7 / MUTANT 3/3 (signature/defeq rejections, not semantic counterexamples) / AXIOMS 24/24 standard-only / CLOSURE 24/24 clean (+2 positive controls). Clean build is the coder's.

/-! # Audit of Tools/ShippingGen4KWalk.lean (scripts/gen4/KWALK_PLAN.md)

1. TYPE: each audited theorem's type is `isDefEq` to `Expected.*` below, written separately (the invariant is spelled with
   `readOf`, not with `mv/cv/sv`).
2. MUTANT: signature/defeq REJECTIONS only (a mutant's type is not defeq to the theorem's). NOT semantic counterexamples.
3. AXIOMS: only propext / Classical.choice / Quot.sound.
4. CLOSURE: the transitive constant closure of each theorem contains no `Laws` / `T1Hyp` / `T1HypND` constant
   (positive controls: the detector flags `T1Hyp`, `T1HypND`). `MemoFamily` is allowed (it is the hypothesis `M`). -/

open Lean Elab Command Meta
open Tools.ShippingEntrySoundness Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh
open Sparkle.Compiler.Elab

namespace Tests.Gen4.KWalkCheck

abbrev Mem := Std.HashMap Name Res

def MemKeys (m c : Mem) : Prop := ∀ k, m.contains k = true → c.contains k = true

namespace Expected

def KWOf {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (O : RefLawsAOps MkRefd mref cref) (P : Mem → Mem → Prop) (w : Void IO.RealWorld) : Prop :=
  O.quiet w ∧ readOf sparkleChildSynth w = some synthesizeChild ∧
    P (readOf sparkleSubModuleCache w) (readOf sparkleChildCache w)

def framedNM : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref} {mctx : Meta.Context} {cctx : Core.Context},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ (P : Mem → Mem → Prop) {α : Type} {p : MetaM α}, Tools.Assume.MemoFamily.FramedNM MkRefd p →
    Keeps mctx mref cctx cref (KWOf O P) p

def memoGet : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref} {mctx : Meta.Context} {cctx : Core.Context},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ (P : Mem → Mem → Prop),
    Keeps mctx mref cctx cref (KWOf O P) (sparkleSubModuleCache.get : MetaM Mem)

def memoReset : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref} {mctx : Meta.Context} {cctx : Core.Context},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ {w w' : Void IO.RealWorld} {u : Unit},
    RunsTo (sparkleSubModuleCache.set {} : MetaM Unit) mctx mref cctx cref w u w' →
    KWOf O (fun _ _ => True) w → KWOf O MemKeys w'

def memoInsert : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref} {mctx : Meta.Context} {cctx : Core.Context},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ (n : Name) (r : Res) {w w' : Void IO.RealWorld} {u : Unit},
    RunsTo (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit) mctx mref cctx cref w u w' →
    KWOf O MemKeys w → KWOf O (fun m c => ∀ k, m.contains k = true → c.contains k = true ∨ (n == k) = true) w'

def childInsert : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref} {mctx : Meta.Context} {cctx : Core.Context},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ (n : Name) (r : Res) {w w' : Void IO.RealWorld} {u : Unit},
    RunsTo (sparkleChildCache.modify (·.insert n r) : MetaM Unit) mctx mref cctx cref w u w' →
    KWOf O (fun m c => ∀ k, m.contains k = true → c.contains k = true ∨ (n == k) = true) w → KWOf O MemKeys w'

def childMono : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref} {mctx : Meta.Context} {cctx : Core.Context},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ (f : Mem → Mem), (∀ c k, c.contains k = true → (f c).contains k = true) →
    ∀ {w w' : Void IO.RealWorld} {u : Unit},
    RunsTo (sparkleChildCache.modify f : MetaM Unit) mctx mref cctx cref w u w' →
    KWOf O MemKeys w → KWOf O MemKeys w'

def forallTele : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref} {mctx : Meta.Context} {cctx : Core.Context},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ (P : Mem → Mem → Prop) {α : Type} (ty : Lean.Expr) (k : Array Lean.Expr → Lean.Expr → MetaM α),
    (∀ (mctx' : Meta.Context) (cctx' : Core.Context) xs b, AdmCtx O.quiet mctx' cctx' →
      Keeps mctx' mref cctx' cref (KWOf O P) (k xs b)) →
    Keeps mctx mref cctx cref (KWOf O P) (Lean.Meta.forallTelescopeReducing ty k)

end Expected

/-! Mutants (rejected by signature / defeq only). -/
namespace Mutant

/-- M1: memoInsert concludes K (no in-flight name). -/
def M1 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref} {mctx : Meta.Context} {cctx : Core.Context},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ (n : Name) (r : Res) {w w' : Void IO.RealWorld} {u : Unit},
    RunsTo (sparkleSubModuleCache.modify (·.insert n r) : MetaM Unit) mctx mref cctx cref w u w' →
    Expected.KWOf O MemKeys w → Expected.KWOf O MemKeys w'

/-- M2: the invariant without `quiet`. -/
def M2 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref} {mctx : Meta.Context} {cctx : Core.Context},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ (P : Mem → Mem → Prop),
    Keeps mctx mref cctx cref (fun w => readOf sparkleChildSynth w = some synthesizeChild ∧
      P (readOf sparkleSubModuleCache w) (readOf sparkleChildCache w))
      (sparkleSubModuleCache.get : MetaM Mem)

/-- M3: childInsert starting from K instead of K_n. -/
def M3 : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {O : RefLawsAOps MkRefd mref cref} {mctx : Meta.Context} {cctx : Core.Context},
    Tools.Assume.MemoFamily.MemoFamily O → AdmCtx O.quiet mctx cctx →
    ∀ (n : Name) (r : Res) {w w' : Void IO.RealWorld} {u : Unit},
    RunsTo (sparkleChildCache.modify (·.insert n r) : MetaM Unit) mctx mref cctx cref w u w' →
    Expected.KWOf O MemKeys w → Expected.KWOf O MemKeys w'

end Mutant

/-! ## The checker -/

/-- Transitive constant closure; `thmInfo`/`defnInfo` bodies and all types are traversed; `opaqueInfo` bodies are not
(reached opaque constants are returned so the log can say so). -/
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

elab "#kwalk_check" : command => liftTermElabM do
  let w := `Tools.ShippingGen4KWalk
  let pre := `Tests.Gen4.KWalkCheck
  let typeCases : List (Name × Name) :=
    [(w ++ `keeps_KW_framedNM, pre ++ `Expected ++ `framedNM), (w ++ `keeps_KW_memoGet, pre ++ `Expected ++ `memoGet),
     (w ++ `kwalk_memoReset, pre ++ `Expected ++ `memoReset), (w ++ `kwalk_memoInsert, pre ++ `Expected ++ `memoInsert),
     (w ++ `kwalk_childInsert, pre ++ `Expected ++ `childInsert), (w ++ `kwalk_childMono, pre ++ `Expected ++ `childMono),
     (w ++ `keeps_KW_forallTelescopeReducing, pre ++ `Expected ++ `forallTele)]
  let mutCases : List (String × Name × Name) :=
    [("M1", w ++ `kwalk_memoInsert, `M1), ("M2", w ++ `keeps_KW_memoGet, `M2), ("M3", w ++ `kwalk_childInsert, `M3)]
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
    [w ++ `keeps_KW_lambdaTelescope, w ++ `keeps_KW_withLocalDeclD, w ++ `keeps_KW_withLetDecl, w ++ `keeps_KW_bind,
     w ++ `keeps_KW_seq, w ++ `keeps_KW_ite, w ++ `keeps_KW_tryCatch, w ++ `keeps_KW_pure, w ++ `framedNM_toA,
     w ++ `framedA_of_memoAccess, w ++ `framedA_ctx, w ++ `memoSet_ctx, w ++ `memoModify_ctx, w ++ `childModify_ctx,
     w ++ `KW, w ++ `KWalk, w ++ `KWalkX]
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
  logInfo m!"KWALK CHECK: TYPE {ok}/7 / MUTANT {rej}/3 (signature/defeq rejections, not semantic counterexamples) / AXIOMS {axOk}/{audited.length} standard-only / CLOSURE {clOk}/{audited.length} clean (+2 positive controls)"

#kwalk_check

end Tests.Gen4.KWalkCheck
