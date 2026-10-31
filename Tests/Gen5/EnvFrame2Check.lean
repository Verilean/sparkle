import Tests.Gen5.EnvFrameCheck
import Tools.ShippingGen5EnvFrame2
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT: check for the U2 implementation (freeze scripts/gen5/DG_ENV_T2_U2_FREEZE.md §4). Pod scratch runs are not acceptance; Pod build / clean build are the coder's.
-- Counting rule: TYPE = Expected comparisons (13 items: A1-A3 + U2-1..10); MUTANT = single changes rejected by the same comparator; negatives = direct + helper controls; unresolved = throwing controls; self-root = forbidden constant as root; clean = not-flagged controls.

/-! # DG-ENV unit U2 checks (Tools/ShippingGen5EnvFrame2.lean)

1. TYPE (13): Expected propositions written from freeze §2 (statements and variable binders), through ONE comparator:
   `withReducible` around `checkExpected` (same path for positive and negative).
2. MUTANT (11): well-typed single changes of the signatures N1-N11, rejected by that comparator. These are signature/defeq
   rejections, NOT semantic counterexamples. The conclusions are single equations (no conjunction), so there is no
   conjunct-dropping mutant; N11 replaces the conclusion of U2-9 by a trivial `envAt cref w = envAt cref w`.
3. CLOSURE: the `reach` walker and `mkForbid` of `Tests.Gen5.EnvFrameCheck` (root itself judged, unknown name throws), over TYPE and VALUE
   of the 13 roots (the private helper `envFrameEnd_withRef` is reached from U2-10). U1 control suite re-run, plus two new controls.
4. AXIOMS: standard only. -/

namespace Tests.Gen5.EnvFrame2Fixture
-- new control 1: reaches `envFrame_getConstInfo`, whose TYPE mentions `GetEnvFrame`
theorem fGetConstInfo : True := (fun _ => trivial) @Tools.ShippingEnvSnapshot.envFrame_getConstInfo
-- new control 2: reaches `getEnvFrame_of_readKeeps` only through a helper's TYPE (root -> helper theorem -> def in its type -> lemma)
def lemTy : Prop := (fun _ => True) @Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps
theorem helperLemTy : lemTy := trivial
theorem fHelperTyLemma : True := helperLemTy
end Tests.Gen5.EnvFrame2Fixture

namespace Tests.Gen5.EnvFrame2Check
open Lean Meta
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInv (endW)
open Tools.ShippingStRefCorrespondence (ReadWorld ReadKeeps SetFrame SetGet)
open Tools.ShippingGen5EnvFrame (EnvFrameEnd)
open Tools.ShippingGen5EnvFrame2
open Tests.Gen3.ExpectedType
open Tests.Gen5.EnvFrameCheck (mkForbid badProj reach guarded)

/-! ## 1. Expected types and mutants -/
def ExpA1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {α : Type} {x : MetaM α}
    (h : ∀ w, endW mctx mref cctx cref x w = w), EnvFrameEnd x mctx mref cctx cref

def ExpA2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {α : Type} (msg : MessageData) (hc : ReadWorld cref) (hm : ReadWorld mref),
    EnvFrameEnd (Lean.throwError msg : MetaM α) mctx mref cctx cref

def ExpA3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {β : Type} (g : Core.State → β × Core.State)
    (henv : ∀ s, (g s).2.env = s.env) (hc : ReadWorld cref) (hs : SetGet cref),
    EnvFrameEnd (ST.Ref.modifyGet cref g : MetaM β) mctx mref cctx cref

def Exp1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {σ : Type} {r : IO.Ref σ} (hr : ReadWorld r),
    EnvFrameEnd (liftM (ST.Ref.get r : IO σ) : MetaM σ) mctx mref cctx cref

def Exp2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {σ : Type} {r : IO.Ref σ} (v : σ) (hne : r.ref ≠ cref.ref)
    (hf : SetFrame r cref), EnvFrameEnd (liftM (ST.Ref.set r v : IO Unit) : MetaM Unit) mctx mref cctx cref

def Exp3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {σ : Type} {r : IO.Ref σ} (f : σ → σ) (hr : ReadWorld r)
    (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref),
    EnvFrameEnd (liftM (ST.Ref.modify r f : IO Unit) : MetaM Unit) mctx mref cctx cref

def Exp4 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ) (hr : ReadWorld r)
    (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref),
    EnvFrameEnd (liftM (ST.Ref.modifyGet r f : IO β) : MetaM β) mctx mref cctx cref

def Exp5 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    (hm : ReadWorld mref),
    EnvFrameEnd (get : MetaM Meta.State) mctx mref cctx cref

def Exp6 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    (f : Meta.State → Meta.State) (hm : ReadWorld mref)
    (hne : mref.ref ≠ cref.ref) (hf : SetFrame mref cref),
    EnvFrameEnd (modify f : MetaM Unit) mctx mref cctx cref

def Exp7 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    (f : TraceState → TraceState) (hc : ReadWorld cref) (hs : SetGet cref),
    EnvFrameEnd (liftM (modifyTraceState f : CoreM Unit) : MetaM Unit) mctx mref cctx cref

def Exp8 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    (hc : ReadWorld cref) (hs : SetGet cref),
    EnvFrameEnd (mkFreshFVarId : MetaM FVarId) mctx mref cctx cref

def Exp9 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {α : Type} (id : FVarId) (hc : ReadWorld cref),
    EnvFrameEnd (liftM (id.throwUnknown : CoreM α) : MetaM α) mctx mref cctx cref

def Exp10 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    (n : Name) (hc : ReadWorld cref) (hm : ReadWorld mref),
    EnvFrameEnd (getConstInfo n : MetaM ConstantInfo) mctx mref cctx cref

def MutN1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {σ : Type} {r : IO.Ref σ} (hr : ReadKeeps r),
    EnvFrameEnd (liftM (ST.Ref.get r : IO σ) : MetaM σ) mctx mref cctx cref

def MutN2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {σ : Type} {r : IO.Ref σ} (v : σ)
    (hf : SetFrame r cref), EnvFrameEnd (liftM (ST.Ref.set r v : IO Unit) : MetaM Unit) mctx mref cctx cref

def MutN3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {σ : Type} {r : IO.Ref σ} (v : σ) (hne : r.ref ≠ cref.ref),
    EnvFrameEnd (liftM (ST.Ref.set r v : IO Unit) : MetaM Unit) mctx mref cctx cref

def MutN4 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {σ : Type} {r : IO.Ref σ} (f : σ → σ)
    (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref),
    EnvFrameEnd (liftM (ST.Ref.modify r f : IO Unit) : MetaM Unit) mctx mref cctx cref

def MutN5 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ)
    (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref),
    EnvFrameEnd (liftM (ST.Ref.modifyGet r f : IO β) : MetaM β) mctx mref cctx cref

def MutN6 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    (f : Meta.State → Meta.State) (hm : ReadWorld mref)
    (hne : mref.ref ≠ cref.ref),
    EnvFrameEnd (modify f : MetaM Unit) mctx mref cctx cref

def MutN7 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    (f : TraceState → TraceState) (hc : ReadWorld cref),
    EnvFrameEnd (liftM (modifyTraceState f : CoreM Unit) : MetaM Unit) mctx mref cctx cref

def MutN8 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    (hc : ReadKeeps cref) (hs : SetGet cref),
    EnvFrameEnd (mkFreshFVarId : MetaM FVarId) mctx mref cctx cref

def MutN9 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    (n : Name) (hc : ReadWorld cref),
    EnvFrameEnd (getConstInfo n : MetaM ConstantInfo) mctx mref cctx cref

def MutN10 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {β : Type} (g : Core.State → β × Core.State)
    (hc : ReadWorld cref) (hs : SetGet cref),
    EnvFrameEnd (ST.Ref.modifyGet cref g : MetaM β) mctx mref cctx cref

def MutN11 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State}
    {α : Type} (id : FVarId) (hc : ReadWorld cref),
    ∀ w : Void IO.RealWorld, envAt cref w = envAt cref w

/-- The one comparator: reducible transparency for every comparison, positive and negative alike. -/
def cmpExp (thm exp : Name) : MetaM Unit := withReducible (checkExpected thm exp)
def cmpMut (thm mt : Name) : MetaM Unit := withReducible (checkMutant thm mt)

run_cmd Lean.Elab.Command.liftTermElabM do
  cmpExp ``envFrameEnd_keep ``ExpA1
  cmpExp ``envFrameEnd_throwError ``ExpA2
  cmpExp ``envFrameEnd_coreModifyGet ``ExpA3
  cmpExp ``envFrameEnd_getIO ``Exp1
  cmpExp ``envFrameEnd_setIO ``Exp2
  cmpExp ``envFrameEnd_modifyIO ``Exp3
  cmpExp ``envFrameEnd_modifyGetIO ``Exp4
  cmpExp ``envFrameEnd_metaGet ``Exp5
  cmpExp ``envFrameEnd_metaModify ``Exp6
  cmpExp ``envFrameEnd_coreModifyTrace ``Exp7
  cmpExp ``envFrameEnd_freshFVar ``Exp8
  cmpExp ``envFrameEnd_fvarThrowUnknown ``Exp9
  cmpExp ``envFrameEnd_constInfo ``Exp10
  logInfo "ENVFRAME2 TYPE total 13 (A1-A3 + U2-1..10), all through withReducible checkExpected"
  cmpMut ``envFrameEnd_getIO ``MutN1
  cmpMut ``envFrameEnd_setIO ``MutN2
  cmpMut ``envFrameEnd_setIO ``MutN3
  cmpMut ``envFrameEnd_modifyIO ``MutN4
  cmpMut ``envFrameEnd_modifyGetIO ``MutN5
  cmpMut ``envFrameEnd_metaModify ``MutN6
  cmpMut ``envFrameEnd_coreModifyTrace ``MutN7
  cmpMut ``envFrameEnd_freshFVar ``MutN8
  cmpMut ``envFrameEnd_constInfo ``MutN9
  cmpMut ``envFrameEnd_coreModifyGet ``MutN10
  cmpMut ``envFrameEnd_fvarThrowUnknown ``MutN11
  logInfo "ENVFRAME2 MUTANT total 11 (N1-N11) rejected by the same comparator (signature/defeq rejections, not semantic counterexamples)"

/-! ## 2. Closure audit -/
set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let forbid ← mkForbid
  let ops := ``Tools.ShippingChildInvA.RefLawsAOps
  for s in guarded do
    unless badProj (.proj s 0 (.bvar 0)) do throwError "ENVFRAME2 AUDIT FAILED: misses raw projection of {s}"
  if badProj (.proj ``Prod 0 (.bvar 0)) then throwError "ENVFRAME2 AUDIT FAILED: flags raw Prod projection"
  let F := `Tests.Gen5.EnvFrameFixture
  let G := `Tests.Gen5.EnvFrame2Fixture
  -- (control, intended forbidden constant, constant that must lie on the reported path)
  let direct : List (Name × Name) :=
    [(F ++ `dLawsO, ``Tools.ShippingGen2.Laws.O), (F ++ `dOps, ops ++ `frame),
     (F ++ `dTele, ``Tools.ShippingChildInvA.RefLawsATele.telescope),
     (F ++ `dT1, ``Tools.ShippingGen2.T1Hyp.defines), (F ++ `dND, ``Tools.ShippingGen2.T1HypND.defines),
     (F ++ `dRec, ops ++ `casesOn), (F ++ `dGetEnvFrame, ``Tools.ShippingEnvSnapshot.GetEnvFrame),
     (F ++ `dSnapshot, ``Tools.ShippingEntryReadsLinked.EnvSnapshot),
     (F ++ `dLemma, ``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps),
     -- new: reaches envFrame_getConstInfo, flagged through GetEnvFrame
     (G ++ `fGetConstInfo, ``Tools.ShippingEnvSnapshot.GetEnvFrame)]
  let helper : List (Name × Name) :=
    [(F ++ `hOps, ops ++ `frame), (F ++ `hLemma, ``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps),
     (F ++ `hT1, ``Tools.ShippingGen2.T1Hyp.defines),
     -- new: lemma only through a helper type
     (G ++ `fHelperTyLemma, ``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps)]
  let mut nNeg : Nat := 0
  for (c, t) in direct ++ helper do
    let r ← reach forbid c
    if r.hit.isNone then throwError "ENVFRAME2 AUDIT FAILED: misses {c}"
    unless forbid.contains t do throwError "ENVFRAME2 AUDIT FAILED: intended {t} not forbidden"
    let rt ← reach [t] c
    unless rt.hit.map (·.getLast? == some t) == some true do
      throwError "ENVFRAME2 AUDIT FAILED: {c} does not reach its intended {t}"
    nNeg := nNeg + 1
    logInfo m!"ENVFRAME2 CONTROL {c}: flagged {toString r.hit}; intended {t} alone {toString rt.hit}"
  -- the two new controls: assert the route (the intermediate constant on the path)
  -- the route: the fixture reaches envFrame_getConstInfo (alone), and that lemma is itself flagged through GetEnvFrame
  let lem := ``Tools.ShippingEnvSnapshot.envFrame_getConstInfo
  let some p1 := (← reach [lem] (G ++ `fGetConstInfo)).hit
    | throwError "ENVFRAME2 AUDIT FAILED: fGetConstInfo does not reach envFrame_getConstInfo"
  unless p1.getLast? == some lem do throwError "ENVFRAME2 AUDIT FAILED: fGetConstInfo path {p1} does not end at envFrame_getConstInfo"
  let some p1' := (← reach forbid lem).hit | throwError "ENVFRAME2 AUDIT FAILED: envFrame_getConstInfo not flagged"
  unless p1' == [lem, ``Tools.ShippingEnvSnapshot.GetEnvFrame] do
    throwError "ENVFRAME2 AUDIT FAILED: envFrame_getConstInfo path {p1'} is not [lemma, GetEnvFrame]"
  let some p2 := (← reach [``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps] (G ++ `fHelperTyLemma)).hit
    | throwError "ENVFRAME2 AUDIT FAILED: fHelperTyLemma not flagged"
  unless p2.contains (G ++ `helperLemTy) && p2.contains (G ++ `lemTy) do
    throwError "ENVFRAME2 AUDIT FAILED: fHelperTyLemma path {p2} does not run through helperLemTy and lemTy"
  -- unresolved names must throw (and name the right constant, with the path through every `via` constant)
  let missing := `Tests.Gen5.EnvFrameFixture.noSuchRoot
  let unres : List (Name × Option Name × Name × List Name) :=
    [(missing, none, missing, []), (F ++ `hv, some (F ++ `helperClean), F ++ `helperClean, []),
     (F ++ `ht, some (F ++ `helperTy), F ++ `helperTy, []),
     (F ++ `ht2, some (F ++ `helperTy), F ++ `helperTy, [F ++ `ht2, F ++ `helperHt])]
  let mut nUnres : Nat := 0
  for (c, hid, nm, via) in unres do
    let ok ← try
        let _ ← reach forbid c hid
        pure false
      catch e =>
        let msg ← e.toMessageData.toString
        let has (n : Name) := (msg.splitOn (toString n)).length > 1
        pure (msg.startsWith s!"ENVFRAME AUDIT UNRESOLVED NAME {nm} " && via.all has)
    unless ok do throwError "ENVFRAME2 AUDIT FAILED: unresolved {nm} under root {c} did not throw"
    nUnres := nUnres + 1
    logInfo m!"ENVFRAME2 CONTROL unresolved {nm} under {c} via {via}: throws"
  -- the root itself is a forbidden constant
  let selfRoots : List Name :=
    [``Tools.ShippingEnvSnapshot.GetEnvFrame, ``Tools.ShippingGen2.T1Hyp.defines,
     ``Tools.ShippingGen2.T1HypND.defines, ``Tools.ShippingGen2.Laws.O, ops ++ `frame, ops ++ `casesOn,
     ``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps]
  let mut nSelf : Nat := 0
  for t in selfRoots do
    unless forbid.contains t do throwError "ENVFRAME2 AUDIT FAILED: self-root {t} not forbidden"
    for fl in [forbid, [t]] do
      let r ← reach fl t
      unless r.hit == some [t] do throwError "ENVFRAME2 AUDIT FAILED: forbidden root {t} itself not flagged ({toString r.hit})"
    nSelf := nSelf + 1
  -- clean controls
  let clean : List Name := [F ++ `cUnrelated, F ++ `cBinders, F ++ `cBinders2, F ++ `cHelper, F ++ `hv, F ++ `ht, F ++ `ht2]
  let mut nClean : Nat := 0
  for c in clean do
    let r ← reach forbid c
    if let some p := r.hit then throwError "ENVFRAME2 AUDIT FAILED: clean control {c} flagged via {p}"
    nClean := nClean + 1
  -- roots
  let roots : List Name := [``envFrameEnd_keep, ``envFrameEnd_throwError, ``envFrameEnd_coreModifyGet, ``envFrameEnd_getIO, ``envFrameEnd_setIO, ``envFrameEnd_modifyIO, ``envFrameEnd_modifyGetIO, ``envFrameEnd_metaGet, ``envFrameEnd_metaModify, ``envFrameEnd_coreModifyTrace, ``envFrameEnd_freshFVar, ``envFrameEnd_fvarThrowUnknown, ``envFrameEnd_constInfo]
  let mut nRoots : Nat := 0
  for c in roots do
    let r ← reach forbid c
    if let some p := r.hit then throwError "ENVFRAME2 AUDIT FAILED {c}: forbidden use via {p}"
    nRoots := nRoots + 1
    logInfo m!"ENVFRAME2 REACH {c}: clean, type and value (visited {r.visited})"
  logInfo m!"ENVFRAME2 CLOSURE total: {nRoots} roots / negatives {nNeg} ({direct.length} direct + {helper.length} helper) + {nUnres} unresolved + {nSelf} self-root / {nClean} clean"

/-! ## 3. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``envFrameEnd_keep, ``envFrameEnd_throwError, ``envFrameEnd_coreModifyGet, ``envFrameEnd_getIO, ``envFrameEnd_setIO, ``envFrameEnd_modifyIO, ``envFrameEnd_modifyGetIO, ``envFrameEnd_metaGet, ``envFrameEnd_metaModify, ``envFrameEnd_coreModifyTrace, ``envFrameEnd_freshFVar, ``envFrameEnd_fvarThrowUnknown, ``envFrameEnd_constInfo] do
    checkAxioms n
  logInfo "ENVFRAME2 AXIOMS total 13 standard"

end Tests.Gen5.EnvFrame2Check
