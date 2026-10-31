import Tools.ShippingGen5EnvFrame
import Tools.ShippingGen5EnvQ
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT (unit U1 checks; scripts/gen5/DG_ENV_T2_FREEZE_R3.md rev3.1 §2.1).

/-! # DG-ENV unit U1 checks (Tools/ShippingGen5EnvFrame.lean)

1. TYPE (9): `EnvFrameEnd` body and U1-1..U1-8 against Expected propositions written from freeze §2 (not copied from the
   implementation), through ONE comparator: `withReducible` around `checkExpected` (same path for positive and negative).
2. MUTANT (8): single changes, rejected by that comparator. These are signature/defeq rejections, NOT semantic
   counterexamples. M1-M7 as in the freeze; M8 (added) drops three conjuncts of the `ReadsAt` conclusion of U1-8.
3. CLOSURE: walker over TYPE and VALUE of every constant reachable from a root. Forbidden: every field (and
   `rec/casesOn/recOn`) of `Laws`, `RefLawsAOps`, `RefLawsATele`, `T1Hyp`, `T1HypND`; raw `Expr.proj` on those structures;
   `GetEnvFrame`, `EnvSnapshot`, `getEnvFrame_of_readKeeps`. No name is exempted. An unresolved name (root, helper value,
   helper type) is `throwError`. Negative controls (direct and through a helper; each forbidden control also hits its
   intended constant alone), unresolved-name negatives, clean controls.
4. AXIOMS: standard only. -/

/-! ## 0. Fixtures -/
namespace Tests.Gen5.EnvFrameFixture
-- helpers reaching a forbidden constant / a hide-able clean name
theorem helperOps : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.frame
theorem helperLemma : True := (fun _ => trivial) @Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps
theorem helperT1 : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.defines
theorem helperClean : True := trivial
def helperTy : Prop := True
-- direct negatives
theorem dLawsO : True := (fun _ => trivial) @Tools.ShippingGen2.Laws.O
theorem dOps : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.frame
theorem dTele : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsATele.telescope
theorem dT1 : True := (fun _ => trivial) @Tools.ShippingGen2.T1Hyp.defines
theorem dND : True := (fun _ => trivial) @Tools.ShippingGen2.T1HypND.defines
theorem dRec : True := (fun _ => trivial) @Tools.ShippingChildInvA.RefLawsAOps.casesOn.{0}
theorem dGetEnvFrame : True := (fun _ => trivial) @Tools.ShippingEnvSnapshot.GetEnvFrame
theorem dSnapshot : True := (fun _ => trivial) @Tools.ShippingEntryReadsLinked.EnvSnapshot
theorem dLemma : True := (fun _ => trivial) @Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps
-- helper negatives
theorem hOps : True := helperOps
theorem hLemma : True := helperLemma
theorem hT1 : True := helperT1
-- unresolved-name carriers (the name is hidden by the walker's lookup)
theorem hv : True := helperClean
theorem ht (_ : helperTy) : True := trivial
-- clean controls
theorem cUnrelated : True := trivial
theorem cBinders {σ : Type} (r : IO.Ref σ) (_ : Tools.ShippingStRefCorrespondence.ReadWorld r) : True := trivial
theorem cBinders2 {σ τ : Type} (r : IO.Ref σ) (r' : IO.Ref τ)
    (_ : Tools.ShippingStRefCorrespondence.SetFrame r r') : True := trivial
theorem cHelper : True := helperClean
end Tests.Gen5.EnvFrameFixture

namespace Tests.Gen5.EnvFrameCheck
open Lean Meta
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInv (endW)
open Tools.ShippingStRefCorrespondence (ReadWorld ReadKeeps SetFrame)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvFrame
open Tests.Gen3.ExpectedType

/-! ## 1. Expected types (written from freeze §2). `ExpEnvFrameEnd` fixes the body of the def; the theorem statements use
the def itself, so the reducible comparator needs no unfolding. -/
def ExpEnvFrameEnd {α : Type} (x : MetaM α) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ w : Void IO.RealWorld, envAt cref (endW mctx mref cctx cref x w) = envAt cref w

def MutEnvFrameEnd {α : Type} (x : MetaM α) (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  ∀ w : Void IO.RealWorld, envAt cref w = envAt cref w

def Exp1 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {α : Type} (a : α),
    EnvFrameEnd (Pure.pure a : MetaM α) mctx mref cctx cref

def Exp2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {α β : Type} {m : MetaM α} {f : α → MetaM β}
    (hm : EnvFrameEnd m mctx mref cctx cref) (hf : ∀ a, EnvFrameEnd (f a) mctx mref cctx cref),
    EnvFrameEnd (m >>= f) mctx mref cctx cref

def MutM6 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {α β : Type} {m : MetaM α} {f : α → MetaM β}
    (hm : EnvFrameEnd m mctx mref cctx cref),
    EnvFrameEnd (m >>= f) mctx mref cctx cref

def Exp3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {σ : Type} {r : IO.Ref σ} (hr : ReadWorld r),
    EnvFrameEnd (ST.Ref.get r : MetaM σ) mctx mref cctx cref

def MutM2 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {σ : Type} {r : IO.Ref σ} (hr : ReadKeeps r),
    EnvFrameEnd (ST.Ref.get r : MetaM σ) mctx mref cctx cref

def Exp4 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {σ : Type} {r : IO.Ref σ} (v : σ) (hne : r.ref ≠ cref.ref)
    (hf : SetFrame r cref), EnvFrameEnd (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref

def MutM3 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {σ : Type} {r : IO.Ref σ} (v : σ)
    (hf : SetFrame r cref), EnvFrameEnd (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref

def MutM4 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {σ : Type} {r : IO.Ref σ} (v : σ) (hne : r.ref ≠ cref.ref),
    EnvFrameEnd (ST.Ref.set r v : MetaM Unit) mctx mref cctx cref

def Exp5 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {σ : Type} {r : IO.Ref σ} (f : σ → σ) (hr : ReadWorld r)
    (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref),
    EnvFrameEnd (ST.Ref.modify r f : MetaM Unit) mctx mref cctx cref

def MutM5 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {σ : Type} {r : IO.Ref σ} (f : σ → σ)
    (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref),
    EnvFrameEnd (ST.Ref.modify r f : MetaM Unit) mctx mref cctx cref

def Exp6 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {σ β : Type} {r : IO.Ref σ} (f : σ → β × σ) (hr : ReadWorld r)
    (hne : r.ref ≠ cref.ref) (hf : SetFrame r cref),
    EnvFrameEnd (ST.Ref.modifyGet r f : MetaM β) mctx mref cctx cref

def Exp7 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} (hr : ReadWorld cref),
    EnvFrameEnd (Lean.getEnv : MetaM Environment) mctx mref cctx cref

def Exp8 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {α : Type} {x : MetaM α}
    (hx : EnvFrameEnd x mctx mref cctx cref) {w : Void IO.RealWorld} (h : ReadsAt env₀ cref w),
    ReadsAt env₀ cref (endW mctx mref cctx cref x w)

def MutM7 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {α : Type} {x : MetaM α}
    (hx : EnvFrameEnd x mctx mref cctx cref) {w : Void IO.RealWorld},
    ReadsAt env₀ cref (endW mctx mref cctx cref x w)

/-- M8: the conclusion keeps only the first conjunct of `ReadsAt` (three conjuncts dropped). -/
def MutM8 : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {env₀ : Environment} {α : Type} {x : MetaM α}
    (hx : EnvFrameEnd x mctx mref cctx cref) {w : Void IO.RealWorld} (h : ReadsAt env₀ cref w),
    ∀ X ci, (envAt cref (endW mctx mref cctx cref x w)).find? X = some ci → env₀.find? X = some ci

/-- The one comparator: reducible transparency for every comparison, positive and negative alike. -/
def cmpExp (thm exp : Name) : MetaM Unit := withReducible (checkExpected thm exp)
def cmpMut (thm mt : Name) : MetaM Unit := withReducible (checkMutant thm mt)

run_cmd Lean.Elab.Command.liftTermElabM do
  cmpExp ``EnvFrameEnd ``ExpEnvFrameEnd
  cmpExp ``envFrameEnd_pure ``Exp1
  cmpExp ``envFrameEnd_bind ``Exp2
  cmpExp ``envFrameEnd_get ``Exp3
  cmpExp ``envFrameEnd_set ``Exp4
  cmpExp ``envFrameEnd_modify ``Exp5
  cmpExp ``envFrameEnd_modifyGet ``Exp6
  cmpExp ``envFrameEnd_getEnv ``Exp7
  cmpExp ``readsAt_endW ``Exp8
  logInfo "ENVFRAME TYPE total 9 (def 1 + theorems 8), all through withReducible checkExpected"
  cmpMut ``EnvFrameEnd ``MutEnvFrameEnd
  cmpMut ``envFrameEnd_get ``MutM2
  cmpMut ``envFrameEnd_set ``MutM3
  cmpMut ``envFrameEnd_set ``MutM4
  cmpMut ``envFrameEnd_modify ``MutM5
  cmpMut ``envFrameEnd_bind ``MutM6
  cmpMut ``readsAt_endW ``MutM7
  cmpMut ``readsAt_endW ``MutM8
  logInfo "ENVFRAME MUTANT total 8 (M1-M8) rejected by the same comparator (signature/defeq rejections, not semantic counterexamples)"

/-! ## 2. Closure audit -/
def fieldsOf (s : Name) : MetaM (List Name) := do
  let fs := getStructureFields (← getEnv) s
  if fs.isEmpty then throwError "ENVFRAME AUDIT FAILED: {s} has no fields"
  return fs.toList.map (s ++ ·)

def recsOf (s : Name) : List Name := [s ++ `rec, s ++ `casesOn, s ++ `recOn]

def guarded : List Name :=
  [``Tools.ShippingGen2.Laws, ``Tools.ShippingChildInvA.RefLawsAOps, ``Tools.ShippingChildInvA.RefLawsATele,
   ``Tools.ShippingGen2.T1Hyp, ``Tools.ShippingGen2.T1HypND]

def mkForbid : MetaM (List Name) := do
  let mut out : List Name := []
  for s in guarded do
    out := out ++ (← fieldsOf s) ++ recsOf s
  return out ++ [``Tools.ShippingEnvSnapshot.GetEnvFrame, ``Tools.ShippingEntryReadsLinked.EnvSnapshot,
    ``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps]

def badProj (e : Expr) : Bool :=
  (e.find? fun x => match x with
    | .proj s _ _ => guarded.contains s
    | _ => false).isSome

def body? : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

structure AReach where
  hit : Option (List Name) := none
  seen : NameSet := {}
  visited : Nat := 0

/-- Walk TYPE and VALUE of every reachable constant. `hidden` makes one name unresolvable (negative controls only).
Any unresolved name throws. -/
def reach (forbid : List Name) (root : Name) (hidden : Option Name := none) (cap : Nat := 3000000) : MetaM AReach := do
  let env ← getEnv
  let lookup (n : Name) : Option ConstantInfo := if hidden == some n then none else env.find? n
  let mut out : AReach := { seen := ({} : NameSet).insert root }
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i : Nat := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then throwError "ENVFRAME AUDIT INCOMPLETE at {root}"
    let some ci := lookup c | throwError "ENVFRAME AUDIT UNRESOLVED NAME {c} (path {path})"
    let body := body? ci
    if badProj ci.type || (body.map badProj).getD false then
      return { out with hit := some (path ++ [`rawProj]) }
    for u in ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[] do
      if forbid.contains u then return { out with hit := some (path ++ [u]) }
      unless out.seen.contains u do
        out := { out with seen := out.seen.insert u }
        queue := queue.push (u, path ++ [u])
  return out

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let forbid ← mkForbid
  -- raw projection controls
  let ops := ``Tools.ShippingChildInvA.RefLawsAOps
  for s in guarded do
    unless badProj (.proj s 0 (.bvar 0)) do throwError "ENVFRAME AUDIT FAILED: misses raw projection of {s}"
  if badProj (.proj ``Prod 0 (.bvar 0)) then throwError "ENVFRAME AUDIT FAILED: flags raw Prod projection"
  logInfo m!"ENVFRAME CONTROL rawProj: {guarded.length} guarded structures flagged, 1 unrelated not flagged (forbid list {forbid.length} names)"
  let F := `Tests.Gen5.EnvFrameFixture
  -- (control, intended forbidden constant)
  let direct : List (Name × Name) :=
    [(F ++ `dLawsO, ``Tools.ShippingGen2.Laws.O), (F ++ `dOps, ops ++ `frame),
     (F ++ `dTele, ``Tools.ShippingChildInvA.RefLawsATele.telescope),
     (F ++ `dT1, ``Tools.ShippingGen2.T1Hyp.defines), (F ++ `dND, ``Tools.ShippingGen2.T1HypND.defines),
     (F ++ `dRec, ops ++ `casesOn), (F ++ `dGetEnvFrame, ``Tools.ShippingEnvSnapshot.GetEnvFrame),
     (F ++ `dSnapshot, ``Tools.ShippingEntryReadsLinked.EnvSnapshot),
     (F ++ `dLemma, ``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps)]
  let helper : List (Name × Name) :=
    [(F ++ `hOps, ops ++ `frame), (F ++ `hLemma, ``Tools.ShippingStRefCorrespondence.getEnvFrame_of_readKeeps),
     (F ++ `hT1, ``Tools.ShippingGen2.T1Hyp.defines)]
  let mut nNeg : Nat := 0
  for (c, t) in direct ++ helper do
    let r ← reach forbid c
    if r.hit.isNone then throwError "ENVFRAME AUDIT FAILED: misses {c}"
    unless forbid.contains t do throwError "ENVFRAME AUDIT FAILED: intended {t} not forbidden"
    let rt ← reach [t] c
    unless rt.hit.map (·.getLast? == some t) == some true do
      throwError "ENVFRAME AUDIT FAILED: {c} does not reach its intended {t}"
    nNeg := nNeg + 1
    logInfo m!"ENVFRAME CONTROL {c}: flagged {toString r.hit}; intended {t} alone {toString rt.hit}"
  -- unresolved names must throw (and name the right constant)
  let missing := `Tests.Gen5.EnvFrameFixture.noSuchRoot
  let unres : List (Name × Option Name × Name) :=
    [(missing, none, missing), (F ++ `hv, some (F ++ `helperClean), F ++ `helperClean),
     (F ++ `ht, some (F ++ `helperTy), F ++ `helperTy)]
  let mut nUnres : Nat := 0
  for (c, hid, nm) in unres do
    let ok ← try
        let _ ← reach forbid c hid
        pure false
      catch e =>
        let msg ← e.toMessageData.toString
        pure (msg.startsWith "ENVFRAME AUDIT UNRESOLVED NAME" && (msg.splitOn (toString nm)).length > 1)
    unless ok do throwError "ENVFRAME AUDIT FAILED: unresolved {nm} under root {c} did not throw"
    nUnres := nUnres + 1
    logInfo m!"ENVFRAME CONTROL unresolved {nm} under {c}: throws"
  -- clean controls (and the carriers of the unresolved cases WITHOUT hiding)
  let clean : List Name := [F ++ `cUnrelated, F ++ `cBinders, F ++ `cBinders2, F ++ `cHelper, F ++ `hv, F ++ `ht]
  let mut nClean : Nat := 0
  for c in clean do
    let r ← reach forbid c
    if let some p := r.hit then throwError "ENVFRAME AUDIT FAILED: clean control {c} flagged via {p}"
    nClean := nClean + 1
    logInfo m!"ENVFRAME CONTROL clean {c}: not flagged (visited {r.visited})"
  -- roots
  let roots : List Name :=
    [``envFrameEnd_pure, ``envFrameEnd_bind, ``envFrameEnd_get, ``envFrameEnd_set, ``envFrameEnd_modify,
     ``envFrameEnd_modifyGet, ``envFrameEnd_getEnv, ``readsAt_endW]
  let mut nRoots : Nat := 0
  for c in roots do
    let r ← reach forbid c
    if let some p := r.hit then throwError "ENVFRAME AUDIT FAILED {c}: forbidden use via {p}"
    nRoots := nRoots + 1
    logInfo m!"ENVFRAME REACH {c}: clean, type and value (visited {r.visited})"
  logInfo m!"ENVFRAME CLOSURE total: {nRoots} roots / negatives {nNeg} ({direct.length} direct + {helper.length} helper) + {nUnres} unresolved / {nClean} clean"

/-! ## 3. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``EnvFrameEnd, ``envFrameEnd_pure, ``envFrameEnd_bind, ``envFrameEnd_get, ``envFrameEnd_set,
      ``envFrameEnd_modify, ``envFrameEnd_modifyGet, ``envFrameEnd_getEnv, ``readsAt_endW] do
    checkAxioms n
  logInfo "ENVFRAME AXIOMS total 9 standard"

end Tests.Gen5.EnvFrameCheck
