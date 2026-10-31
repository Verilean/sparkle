import Tools.ShippingGen5AccKeep
import Tests.Gen5.AccCheck
set_option autoImplicit false
-- Built in the Pod (g5ac-r6) at 5c38c6fc: `kjob lake build Tests.Gen5.AccKeepCheck`, exit 0, 714 jobs. TYPE 12 (1 definition + 11 theorems, all syntactic, no isDefEq fallback), MUTANT 10 (signature/defeq rejection, not semantic), AXIOMS 12 (standard three), walker controls + unknown controls + CLOSURE OK 12149 constants. Clean issue-linked build is the coder's. No sorry / axiom / native_decide in this source (the 3 `sorry` warnings come from the intended walker-control negatives).

/-! # DG-ACC unit A5a checks (Tools/ShippingGen5AccKeep.lean; scripts/gen5/DG_ACC_FREEZE_REV3.md §2.1)

TYPE: the definition `AccEInv` and the 11 theorems are each compared binder by binder (`checkExpected`) with an independently written
`Expected…` statement (written from the prose of REV3 §2.1, not copied from the implementation file); all comparisons use the same
`cmpTele` comparator (syntactic `==` first, `isDefEq` fallback, logged as DEFEQ).
MUTANT: one-place, well-typed changes (or a dropped conjunct / premise) rejected by `checkMutant` -- a rejection by signature / defeq, NOT a
semantic counterexample. AXIOMS: standard three only. CLOSURE: the explicit-value walker of `AccCheck`, with its negative/clean controls and
the unknown-name controls re-run; the roots (all 12 constants) are put in `seen` and judged. -/
namespace Tests.Gen5.AccKeepCheck
open Lean Meta Elab
open Sparkle.Compiler.Elab
open Tools.ShippingGen5Acc Tests.Gen3.ExpectedType
open Tools.ShippingGen2 (Laws)
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv (Res Keeps Triple profLogIO OkExc)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingChildBndCore (cv)

section Expected

def ExpectedAccEInvValue {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Exception → Void IO.RealWorld → Prop :=
  fun e w => AccInvAt K L Reach D w ∧ OkExc e

def ExpectedDepthSet : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ (D v : Nat) {R : Exception → Void IO.RealWorld → Prop},
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (ST.Ref.set sparkleSynthDepth v : MetaM Unit)
      (fun _ => AccInvAt K L Reach v) R

def ExpectedDepthModify : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ (D : Nat) (f : Nat → Nat) {R : Exception → Void IO.RealWorld → Prop},
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (ST.Ref.modify sparkleSynthDepth f : MetaM Unit)
      (fun _ => AccInvAt K L Reach (f D)) R

def ExpectedFin : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ (d : Nat)
    (m1 : Std.HashMap Lean.Name Lean.Expr) (m2 : Std.HashMap String Nat)
    (m3 m4 m5 : Std.HashMap String String) (m6 : Std.HashMap (UInt64 × String) String)
    (m7 : Std.HashMap String String),
    Triple mctx mref cctx cref (AccInvAt K L Reach (d + 1))
      (do
        ST.Ref.modify sparkleSynthDepth fun x => x - 1
        if (d != 0) = true then do
            ST.Ref.set sparkleFvarValueMap m1
            ST.Ref.set sparkleWireWidthCache m2
            ST.Ref.set sparkleLetWireCache m3
            ST.Ref.set sparkleLoopWireCache m4
            ST.Ref.set sparkleWireCanon m5
            ST.Ref.set sparkleSubInstanceOutputs m6
            ST.Ref.set sparkleSingleOutInstanceCache m7
          else pure () : MetaM Unit)
      (fun _ => AccInvAt K L Reach d) (AccEInv K L Reach d)

def ExpectedCoreTriple : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ (D : Nat), (hD : 1 ≤ D) → ∀ (declName : Name),
    (hbody : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (AccInvAt K L Reach (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) →
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinationalCore declName [] false)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D)

def ExpectedFullTriple : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ {D : Nat} {declName : Name},
    (hcore : Triple mctx mref cctx cref (AccInvAt K L Reach D)
      (synthesizeCombinationalCore declName [] false) (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D)) →
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinational declName)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D)

def ExpectedHentryT : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ {D : Nat}, (hD : 1 ≤ D) → ∀ {c : Name},
    (hbody : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (AccInvAt K L Reach (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst)) →
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinational c)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D)

def ExpectedCacheGet : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ (D : Nat),
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (sparkleChildCache.get : MetaM _)
      (fun m w => AccInvAt K L Reach D w ∧ m = cv w) (AccEInv K L Reach D)

def ExpectedInsertRuns : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) →
    ∀ {D : Nat} {n : Name} {r : Res} {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld},
    (hw : AccInvAt K L Reach D w) → (hr : RealChildA L.O n r) → (hs : Reach n → Acc (CallRel K) n) →
    (h : RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert n r) : MetaM Unit)
      mctx mref cctx cref w u w') → AccInvAt K L Reach D w'

def ExpectedChildTriple : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ {D : Nat} {n : Name}, (hIH : AccIHAt K L Reach D) →
    (hentryT : Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinational n)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D)) →
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeChild n)
      (fun r w => RealChildA L.O n r ∧ (Reach n → Acc (CallRel K) n) ∧ AccInvAt K L Reach D w)
      (AccEInv K L Reach D)

def ExpectedAccRes : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) →
    ∀ {D : Nat} {n : Name} {w w' : Void IO.RealWorld} {r : Res},
    (hw : AccInvAt K L Reach D w) → (hIH : AccIHAt K L Reach D) →
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w r w') → Reach n → Acc (CallRel K) n

def ExpectedKeepChildProved : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop), AccKeepChildStmt K L Reach

/-- the unfolded form of the statement (not syntactic with the above; checked by `example` below) -/
def ExpectedKeepChildUnfolded : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop), ∀ D, 1 ≤ D → (D < sparkleSynthDepthLimit → AccBodyKeeps K L Reach (D + 1)) →
      AccIHAt K L Reach D → AccChildKeeps K L Reach D

-- mutants (each well-typed, one place changed; signature/defeq rejection only)
/-- `AccEInv` without the exception class -/
def MutEInvNoOk {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) : Exception → Void IO.RealWorld → Prop :=
  fun _ w => AccInvAt K L Reach D w

/-- depth set concluding the OLD depth -/
def MutDepthSetOldDepth : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ (D v : Nat) {R : Exception → Void IO.RealWorld → Prop},
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (ST.Ref.set sparkleSynthDepth v : MetaM Unit)
      (fun _ => AccInvAt K L Reach D) R

/-- the nested core entry without `1 ≤ D` -/
def MutCoreNoD1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ (D : Nat), ∀ (declName : Name),
    (hbody : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (AccInvAt K L Reach (D + 1))
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)) →
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinationalCore declName [] false)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D)

/-- the body keep asked at depth `D` instead of `D + 1` -/
def MutHentryBodyAtD : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ {D : Nat}, (hD : 1 ≤ D) → ∀ {c : Name},
    (hbody : ∀ {tenv : Lean.Environment}, D < sparkleSynthDepthLimit → ∀ (b : Bool) ci isInst,
      Keeps mctx mref cctx cref (AccInvAt K L Reach D)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          c [] false true ci isInst)) →
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinational c)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D)

/-- the cache read without the equation `m = cv w` -/
def MutCacheGetNoEq : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ (D : Nat),
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (sparkleChildCache.get : MetaM _)
      (fun _ w => AccInvAt K L Reach D w) (AccEInv K L Reach D)

/-- the insert without the `Acc` premise of the inserted key -/
def MutInsertNoHs : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) →
    ∀ {D : Nat} {n : Name} {r : Res} {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld},
    (hw : AccInvAt K L Reach D w) → (hr : RealChildA L.O n r) →
    (h : RunsTo (sparkleChildCache.modify (fun m : Std.HashMap Name Res => m.insert n r) : MetaM Unit)
      mctx mref cctx cref w u w') → AccInvAt K L Reach D w'

/-- the child triple without its `RealChildA` conjunct -/
def MutChildTripleNoReal : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) → ∀ {D : Nat} {n : Name}, (hIH : AccIHAt K L Reach D) →
    (hentryT : Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeCombinational n)
      (fun _ => AccInvAt K L Reach D) (AccEInv K L Reach D)) →
    Triple mctx mref cctx cref (AccInvAt K L Reach D) (synthesizeChild n)
      (fun _ w => (Reach n → Acc (CallRel K) n) ∧ AccInvAt K L Reach D w)
      (AccEInv K L Reach D)

/-- `Acc` of the returned child without the IH premise -/
def MutAccResNoIH : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop),
    (hA : AdmCtx L.O.quiet mctx cctx) →
    ∀ {D : Nat} {n : Name} {w w' : Void IO.RealWorld} {r : Res},
    (hw : AccInvAt K L Reach D w) →
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w r w') → Reach n → Acc (CallRel K) n

/-- the child-keep statement without `1 ≤ D` -/
def MutKeepChildNoD1 : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop), ∀ D, (D < sparkleSynthDepthLimit → AccBodyKeeps K L Reach (D + 1)) →
      AccIHAt K L Reach D → AccChildKeeps K L Reach D

/-- the child-keep statement without the IH -/
def MutKeepChildNoIH : Prop :=
  ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (K : AssignKit ι dom env₀)
    (L : Laws mref cref) (Reach : Name → Prop), ∀ D, 1 ≤ D → (D < sparkleSynthDepthLimit → AccBodyKeeps K L Reach (D + 1)) →
      AccChildKeeps K L Reach D
end Expected

section Examples
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
/-- the statement of `accKeepChild_proved` is the unfolded REV3 §2.1 text (kernel defeq) -/
example : ExpectedKeepChildUnfolded := fun K L Reach => accKeepChild_proved K L Reach
example (K : AssignKit ι dom env₀) (L : Laws mref cref) (Reach : Name → Prop) (D : Nat) :
    AccEInv K L Reach D = ExpectedAccEInvValue K L Reach D := rfl
end Examples

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``AccEInv ``ExpectedAccEInvValue
  checkExpected ``tripleAcc_depthSet ``ExpectedDepthSet
  checkExpected ``tripleAcc_depthModify ``ExpectedDepthModify
  checkExpected ``finAcc ``ExpectedFin
  checkExpected ``core_tripleAcc ``ExpectedCoreTriple
  checkExpected ``full_tripleAcc ``ExpectedFullTriple
  checkExpected ``hentryT_of_bodyAcc ``ExpectedHentryT
  checkExpected ``tripleAcc_cacheGet ``ExpectedCacheGet
  checkExpected ``accInvAt_insert_runs ``ExpectedInsertRuns
  checkExpected ``synthesizeChild_tripleAcc ``ExpectedChildTriple
  checkExpected ``synthesizeChild_accRes ``ExpectedAccRes
  checkExpected ``accKeepChild_proved ``ExpectedKeepChildProved
  checkMutant ``AccEInv ``MutEInvNoOk
  checkMutant ``tripleAcc_depthSet ``MutDepthSetOldDepth
  checkMutant ``core_tripleAcc ``MutCoreNoD1
  checkMutant ``hentryT_of_bodyAcc ``MutHentryBodyAtD
  checkMutant ``tripleAcc_cacheGet ``MutCacheGetNoEq
  checkMutant ``accInvAt_insert_runs ``MutInsertNoHs
  checkMutant ``synthesizeChild_tripleAcc ``MutChildTripleNoReal
  checkMutant ``synthesizeChild_accRes ``MutAccResNoIH
  checkMutant ``accKeepChild_proved ``MutKeepChildNoD1
  checkMutant ``accKeepChild_proved ``MutKeepChildNoIH

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``AccEInv, ``tripleAcc_depthSet, ``tripleAcc_depthModify, ``finAcc, ``core_tripleAcc, ``full_tripleAcc,
      ``hentryT_of_bodyAcc, ``tripleAcc_cacheGet, ``accInvAt_insert_runs, ``synthesizeChild_tripleAcc,
      ``synthesizeChild_accRes, ``accKeepChild_proved] do
    checkAxioms n

run_cmd Lean.Elab.Command.liftTermElabM Tests.Gen5.AccCheck.walkerControls

/-- Unknown-name controls through the same `closureReport` path (see AccIndCheck): root / helper value / helper type naming an
absent constant MUST be reported; a clean chain MUST NOT. -/
def unknownControls : MetaM Unit := do
  let ghost := `Ghost.Absent.name
  let addU (n : Name) (type value : Expr) : MetaM Unit :=
    withOptions (fun o => debug.skipKernelTC.set o true) do
      addDecl (.thmDecl { name := n, levelParams := [], type := type, value := value })
  let unk (roots : List Name) : MetaM (Array Name) := do
    let (_, u, _) ← Tests.Gen5.AccCheck.closureReport (← getEnv) roots
    pure u
  let u1 ← unk [ghost]
  unless u1 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: unknown root not reported ({u1})"
  let u2 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.HelperVal (mkConst ``True) (mkConst ghost)
    addU `Tests.Gen5.UnkCtl.RootVal (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.HelperVal)
    unk [`Tests.Gen5.UnkCtl.RootVal]
  unless u2 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper value naming an unknown constant not reported ({u2})"
  let u3 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.HelperTy (mkConst ghost) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtl.RootTy (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.HelperTy)
    unk [`Tests.Gen5.UnkCtl.RootTy]
  unless u3 == #[ghost] do throwError "GEN5 UNKNOWN CONTROL FAILED: helper type naming an unknown constant not reported ({u3})"
  let u4 ← withoutModifyingEnv do
    addU `Tests.Gen5.UnkCtl.CleanHelper (mkConst ``True) (mkConst ``True.intro)
    addU `Tests.Gen5.UnkCtl.CleanRoot (mkConst ``True) (mkConst `Tests.Gen5.UnkCtl.CleanHelper)
    unk [`Tests.Gen5.UnkCtl.CleanRoot]
  unless u4.isEmpty do throwError "GEN5 UNKNOWN CONTROL FAILED: clean control reported unknown ({u4})"
  logInfo m!"GEN5 UNKNOWN CONTROLS OK: 3 negatives reported unknown (root / helper value / helper type), clean control not reported"

run_cmd Lean.Elab.Command.liftTermElabM unknownControls

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``AccEInv, ``tripleAcc_depthSet, ``tripleAcc_depthModify, ``finAcc, ``core_tripleAcc, ``full_tripleAcc,
    ``hentryT_of_bodyAcc, ``tripleAcc_cacheGet, ``accInvAt_insert_runs, ``synthesizeChild_tripleAcc,
    ``synthesizeChild_accRes, ``accKeepChild_proved]
  let (seen, unk, hits) ← Tests.Gen5.AccCheck.closureReport env roots
  unless hits.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants reached: {hits}"
  for n in roots do
    unless seen.contains n do throwError "GEN5 CLOSURE FAILED: root {n} is not in the seen set"
  for n in seen.toList do
    let s := n.toString
    if s.startsWith "Tools.ShippingGen5DataOf" || s.startsWith "Tools.ShippingGen5SemGen" then
      throwError "GEN5 CLOSURE FAILED: supplier constant {n} reached"
  unless unk.isEmpty do throwError "GEN5 CLOSURE FAILED: unknown constants (not in the environment): {unk}"
  logInfo m!"GEN5 CLOSURE OK (A5a): {seen.toList.length} constants, no forbidden constant, no supplier-unit constant, no unknown constant"

end Tests.Gen5.AccKeepCheck
