import Tools.ShippingFGCircuitS2hHist3
import Tests.Gen5.FGCircuitPilotCheck26
set_option autoImplicit false
-- FG circuit pilot S2h check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §34.

/-! # FGCircuitPilotCheck28 (light: each part is a small `run_cmd`; every real type is normalised once)

1. DEFS: `MissE`, `JQH` and the constructor `RealChildE.run` against independently written expected statements, with mutants (evidence dropped / at the end world, only one conjunct, no depth bound, no miss condition, the history invariant dropped, a weaker cache field, a hit instead of a miss).
2. LEMMAS (complete types): `coreHeadOff_jqhA` (cache initialisation), `synthesizeChild_tripleH` (hit takes the evidence out, miss saves it), `hftCoreCloses_of_kidsH`, `synth_hftPcieOutByte_finalOffLNKH_Z`, against independently written expected types (`isDefEq`, binder kinds too); `machineChild_of_realE` structurally.
3. REACH: within the reach walk (a walk over the types and values of `defnInfo` under `Tools`/`Sparkle`; it does not unfold inductive constructors or theorems) `MachineDefines`, `HftKidsDefine`, `MachineCloses` and the universal `KidStartEnv` are not reached from the new hypotheses. This is NOT a claim about the whole dependency closure.
4. REMAINING, AXIOMS. WHENEVER the final wrapper changes, this check must be updated in the same commit. -/
namespace Tests.Gen5.FGCircuitPilotCheck28
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingEntryReadsLinked (envAt CoreSaved)
open Tools.ShippingFGCircuitS1oHead (GetEnvProfileAt)
open Tools.ShippingFGCircuitS2hHist
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1qLinked (coreHeadOff)
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 Mod ZS ZE idF idW sameN diffN tyOf binderInfos HttpData TlpData RootData ExpFinalKK ExpCoreK ExpKidsEnv ExpKidsGates kgReal kgSwapped kgHttp kgTrue NmRoot NmHttp NmTlp ShE reach litBool iteStep Pre EntryOf)
open Tools.ShippingFGCircuitS1tFinal (cdvZ CDRel)
open Tools.ShippingFGCircuitS1rCD (HftObCDZ)
open Sparkle.Compiler.Elab

def normOnce3 (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let some e' := iteStep e then return .visit e'
    if let .const c _ := e.getAppFn then
      if c == ``MissE || c == ``JQH || c == ``EQH || c == ``CacheE || c == ``KidEv || c == ``HftFinalStmtOffLNKH || c == ``Tools.ShippingFGCircuitS2dKids.HftKidsGates ||
          (`Tests.Gen5.FGCircuitPilotCheck28).isPrefixOf c || (`Tests.Gen5.FGCircuitPilotCheck26).isPrefixOf c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm3 (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:7] do
    e ← normOnce3 e
  return e
/-- `a` is the normal form of a real type, computed once and compared with the expected statement / every mutant -/
def same3 (what : String) (a exp : Lean.Expr) : MetaM Unit := do
  let e ← norm3 exp
  unless ← withDefault (isDefEq a e) do throwError "{what}: type is NOT the expected statement"
  unless binderInfos a == binderInfos e do throwError "{what}: binder kinds differ"
def diff3 (what : String) (a exp : Lean.Expr) : MetaM Unit := do
  let e ← norm3 exp
  if a == e then throwError "{what}: the MUTANT is the same expression"
  if ← withReducible (isDefEq a e) then throwError "{what}: the MUTANT was accepted"

/-! ## 1. DEFS -/

section Defs
variable {mref : Rf1} {cref : Rf2}

/-- the evidence a history entry saves, written again -/
def ExpEv (e : Environment) : Cx → Cc → W → Prop :=
  fun mctx cctx w => ReadsAt e cref w ∧ GetEnvProfileAt mctx mref cctx cref w
def EvOnlyReads (e : Environment) : Cx → Cc → W → Prop := fun _ _ w => ReadsAt e cref w
def EvOnlyProf (e : Environment) : Cx → Cc → W → Prop := fun mctx cctx w => GetEnvProfileAt mctx mref cctx cref w
def EvEq (e : Environment) : Cx → Cc → W → Prop := fun mctx cctx w => envAt cref w = e ∧ GetEnvProfileAt mctx mref cctx cref w
def EvTrue (_ : Environment) : Cx → Cc → W → Prop := fun _ _ _ => True

/-- the miss premise, written again. Knobs: the depth bound, the miss condition, the history invariant on the world. -/
def ExpMiss (O : RefLawsAOps MkRefd mref cref) (E : Cx → Cc → W → Prop) (depth miss hist : Bool) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc), AdmCtx O.quiet mctx cctx →
    ∀ (D : Nat), (if depth then 1 ≤ D else True) → ∀ (n : Name) (w : W),
      (if hist then (JQ O.quiet D w ∧ ∀ c r, (cv w).get? c = some r → RealChildE O E c r) else (JQ O.quiet D w)) →
      (if miss then (cv w).get? n = none else True) → E mctx cctx w
def MissOnHit (O : RefLawsAOps MkRefd mref cref) (E : Cx → Cc → W → Prop) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc), AdmCtx O.quiet mctx cctx →
    ∀ (D : Nat), 1 ≤ D → ∀ (n : Name) (w : W),
      (JQ O.quiet D w ∧ ∀ c r, (cv w).get? c = some r → RealChildE O E c r) → ((cv w).get? n).isSome = true → E mctx cctx w
/-- the evidence is claimed at a context independent of the call -/
def MissOtherCtx (O : RefLawsAOps MkRefd mref cref) (E : Cx → Cc → W → Prop) : Prop :=
  ∀ (mctx : Cx) (cctx : Cc), AdmCtx O.quiet mctx cctx →
    ∀ (D : Nat), 1 ≤ D → ∀ (n : Name) (w : W) (mctx' : Cx),
      (JQ O.quiet D w ∧ ∀ c r, (cv w).get? c = some r → RealChildE O E c r) → (cv w).get? n = none → E mctx' cctx w
/-- the history invariant, written again (and the weaker cache of the old invariant) -/
def ExpJQH (O : RefLawsAOps MkRefd mref cref) (E : Cx → Cc → W → Prop) (D : Nat) (w : W) : Prop :=
  JQ O.quiet D w ∧ ∀ c r, (cv w).get? c = some r → RealChildE O E c r
def JQHOld (O : RefLawsAOps MkRefd mref cref) (_ : Cx → Cc → W → Prop) (D : Nat) (w : W) : Prop :=
  JQ O.quiet D w ∧ ∀ c r, (cv w).get? c = some r → RealChildA O c r
def JQHNoCache (O : RefLawsAOps MkRefd mref cref) (_ : Cx → Cc → W → Prop) (D : Nat) (w : W) : Prop := JQ O.quiet D w

/-- the constructor of the history entry, written again. Knobs: the evidence (`evK`: absent / at the start / at the end world), the cache field (history / old), the premises, the entry. -/
def ExpRun (evK : Nat) (cacheE adm synth quiet off : Bool) : Prop :=
  ∀ {mref : Rf1} {cref : Rf2} {O : RefLawsAOps MkRefd mref cref} {E : Cx → Cc → W → Prop} {c : Name} {r : Res}
    (mctx : Cx) (cctx : Cc) (w w' : W),
    (if adm then AdmCtx O.quiet mctx cctx else True) →
    (if cacheE then (∀ c' r', (cv w).get? c' = some r' → RealChildE O E c' r')
      else (∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r')) →
    (if synth then sv w = some synthesizeChild else True) →
    (if quiet then O.quiet w else True) →
    RunsTo (if off then synthesizeCombinationalOff c else synthesizeCombinational c) mctx mref cctx cref w r w' →
    (if evK == 0 then True else if evK == 1 then E mctx cctx w else E mctx cctx w') → RealChildE O E c r
end Defs

def RunReal : Prop := ExpRun 1 true true true true false
def RunNoEv : Prop := ExpRun 0 true true true true false
def RunEvEnd : Prop := ExpRun 2 true true true true false
def RunOldCache : Prop := ExpRun 1 false true true true false
def RunNoAdm : Prop := ExpRun 1 true false true true false
def RunNoSynth : Prop := ExpRun 1 true true false true false
def RunNoQuiet : Prop := ExpRun 1 true true true false false
def RunOff : Prop := ExpRun 1 true true true true true


/-! ## the lemmas' expected types -/

/-- `coreHeadOff_jqhA`: the cache is initialised by the head of the profile-free root run. Knobs: the head (`off`), the start depth, the conclusion's depth, the invariant concluded (history / old / no cache). -/
def ExpHead (off : Bool) (d0 d1 : Nat) (inv : Nat) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref), AdmCtx O.quiet mctx cctx →
    ∀ {E : Cx → Cc → W → Prop} {X : Name} {w w1 : W} {s : CoreSaved},
      JQ O.quiet d0 w →
      RunsTo (if off then coreHeadOff X else Tools.ShippingEntryReadsLinked.coreHead X) mctx mref cctx cref w s w1 →
      (if inv == 0 then ExpJQH O E d1 w1 else if inv == 1 then JQHOld O E d1 w1 else JQHNoCache O E d1 w1)
def HeadReal : Prop := ExpHead true 0 (0 + 1) 0
def HeadDiag : Prop := ExpHead false 0 (0 + 1) 0
def HeadStart1 : Prop := ExpHead true 1 (0 + 1) 0
def HeadDepth0 : Prop := ExpHead true 0 0 0
def HeadOld : Prop := ExpHead true 0 (0 + 1) 1
def HeadNoCache : Prop := ExpHead true 0 (0 + 1) 2

/-- `synthesizeChild_tripleH`: a hit reads the evidence from the entry, a miss saves it. Knobs: the entry's result (`RealChildE` / `RealChildA`), the post invariant (history / old), the premises. -/
def ExpChild (res : Bool) (post : Nat) (needD needMiss needEntry : Bool) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) {E : Cx → Cc → W → Prop},
    AdmCtx O.quiet mctx cctx → ∀ {D : Nat},
    Pre needD (1 ≤ D) (
    Pre needMiss (ExpMiss O E true true true) (
    ∀ {n : Name},
    Pre needEntry (Triple mctx mref cctx cref (ExpJQH O E D) (synthesizeCombinational n)
      (fun _ => ExpJQH O E D) (fun e w => ExpJQH O E D w ∧ OkExc e)) (
    Triple mctx mref cctx cref (ExpJQH O E D) (synthesizeChild n)
      (fun r w => (if res then RealChildE O E n r else RealChildA O n r) ∧ (if post == 0 then ExpJQH O E D w else if post == 1 then JQHOld O E D w else JQHNoCache O E D w))
      (fun e w => ExpJQH O E D w ∧ OkExc e))))

def ChReal : Prop := ExpChild true 0 true true true
def ChNoEv : Prop := ExpChild false 0 true true true
def ChOldPost : Prop := ExpChild true 1 true true true
def ChNoCachePost : Prop := ExpChild true 2 true true true
def ChNoDepth : Prop := ExpChild true 0 false true true
def ChNoMiss : Prop := ExpChild true 0 true false true
def ChNoEntry : Prop := ExpChild true 0 true true false

/-- the miss premise of the lemmas below, as a function of the environment `e` (evidence = reads + profile-off) -/
def kmissR {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  ExpMiss O (ExpEv (mref := mref) (cref := cref) e) true true true
def kmissNoDepth {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  ExpMiss O (ExpEv (mref := mref) (cref := cref) e) false true true
def kmissNoMiss {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  ExpMiss O (ExpEv (mref := mref) (cref := cref) e) true false true
def kmissNoHist {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  ExpMiss O (ExpEv (mref := mref) (cref := cref) e) true true false
def kmissOnHit {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  MissOnHit O (ExpEv (mref := mref) (cref := cref) e)
def kmissOtherCtx {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  MissOtherCtx O (ExpEv (mref := mref) (cref := cref) e)
def kmissOnlyReads {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  ExpMiss O (EvOnlyReads (mref := mref) (cref := cref) e) true true true
def kmissOnlyProf {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  ExpMiss O (EvOnlyProf (mref := mref) (cref := cref) e) true true true
def kmissEq {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  ExpMiss O (EvEq (mref := mref) (cref := cref) e) true true true
def kmissTrue {mref : Rf1} {cref : Rf2} (O : RefLawsAOps MkRefd mref cref) (e : Environment) : Prop :=
  ExpMiss O (EvTrue e) true true true

-- the core: the children's hypothesis is the miss premise (or a mutant of it, or the old universal one)
def CH_True : Prop := ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_missNoDepth : Prop := ExpCoreK kmissNoDepth NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_missNoMiss : Prop := ExpCoreK kmissNoMiss NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_missNoHist : Prop := ExpCoreK kmissNoHist NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_missOnHit : Prop := ExpCoreK kmissOnHit NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_missOtherCtx : Prop := ExpCoreK kmissOtherCtx NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_missOnlyReads : Prop := ExpCoreK kmissOnlyReads NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_missOnlyProf : Prop := ExpCoreK kmissOnlyProf NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_missEq : Prop := ExpCoreK kmissEq NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_missTrue : Prop := ExpCoreK kmissTrue NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_OldKenv : Prop := ExpCoreK ExpKidsEnv NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_ReadersSwapped : Prop := ExpCoreK kmissR NmTlp NmHttp TlpData HttpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_ReaderShapes : Prop := ExpCoreK kmissR NmHttp NmTlp TlpData HttpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF idF
def CH_GatesSwapped : Prop := ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmTlp NmHttp true true true true true true idW idW idW idW idF idF idF idF
def CH_GatesHttp : Prop := ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmHttp true true true true true true idW idW idW idW idF idF idF idF
def CH_NoStart : Prop := ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp false true true true true true idW idW idW idW idF idF idF idF
def CH_NoCell : Prop := ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true false true true true true idW idW idW idW idF idF idF idF
def CH_NoReaders : Prop := ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true false true true true idW idW idW idW idF idF idF idF
def CH_NoGates : Prop := ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true false true true idW idW idW idW idF idF idF idF
def CH_NoKenv : Prop := ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true false true idW idW idW idW idF idF idF idF
def CH_NoConcl : Prop := ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true false idW idW idW idW idF idF idF idF
def CH_KenvIndep : Prop := ∀ {a : W}, ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW (fun _ => a) idW idF idF idF idF
def CH_ReadersIndep : Prop := ∀ {a : W}, ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true (fun _ => a) idW idW idW idF idF idF idF
def CH_GatesIndep : Prop := ∀ {a : W}, ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW (fun _ => a) idW idW idF idF idF idF
def CH_ConclWorld : Prop := ∀ {a : W}, ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW (fun _ => a) idF idF idF idF
def CH_CtxM : Prop := ∀ {a : Cx}, ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW (fun _ => a) idF idF idF
def CH_CtxC : Prop := ∀ {a : Cc}, ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF (fun _ => a) idF
def CH_RefM : Prop := ∀ {a : Rf1}, ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF (fun _ => a) idF idF
def CH_RefC : Prop := ∀ {a : Rf2}, ExpCoreK kmissR NmHttp NmTlp HttpData TlpData NmHttp NmTlp true true true true true true idW idW idW idW idF idF idF (fun _ => a)

-- the final statement
def FH (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_missNoDepth (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissNoDepth kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_missNoMiss (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissNoMiss kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_missNoHist (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissNoHist kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_missOnHit (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissOnHit kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_missOtherCtx (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissOtherCtx kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_missOnlyReads (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissOnlyReads kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_missOnlyProf (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissOnlyProf kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_missEq (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissEq kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_missTrue (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissTrue kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_OldKenv (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV ExpKidsEnv kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_KenvEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZS ZE NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_GatesEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZE ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_BothEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZE ZE NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_Diag (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal true false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_OldArt (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false true true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_NoHcd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false false true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_NoTop (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false true false true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_NoKenv (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false true true false true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_NoKg (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false true true true false true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_KgSwapped (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgSwapped false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_KgHttp (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgHttp false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_KgTrue (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgTrue false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_Root (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZS ZS NmHttp NmRoot (ShE) ZS ZS idF idF idF idF idF
def FH_PostRoot (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZS ZS NmRoot NmHttp (ShE) ZS ZS idF idF idF idF idF
def FH_Output (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZS ZS NmRoot NmRoot ({ ShE with res := .one (.bits 16) }) ZS ZS idF idF idF idF idF
def FH_HcdEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZE ZS idF idF idF idF idF
def FH_ConclEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZE idF idF idF idF idF
def FH_RefM (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Rf1}, ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF (fun _ => a) idF idF idF
def FH_RefC (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Rf2}, ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF (fun _ => a) idF
def FH_CtxM (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Cx}, ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS (fun _ => a) idF idF idF idF
def FH_CtxC (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Cc}, ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF (fun _ => a) idF idF
def FH_Design (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Design}, ExpFinalKK Ob CV kmissR kgReal false false true true true true true ZS ZS NmRoot NmRoot (ShE) ZS ZS idF idF idF idF (fun _ => a)
def FH_CarrierY : Prop := FH HftObCDZ cdvY
def FH_CarrierOld : Prop := FH HftObCDZ Tools.ShippingFGCircuitS1tFinal.cdvOld
def FH_ObY : Prop := FH Tools.ShippingFGCircuitS1rCD.HftObCDY cdvZ


/-! ## DEFS: MissE and JQH as terms (each is a function of `O` and `E`) -/

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2hHist
  let Q := `Tests.Gen5.FGCircuitPilotCheck28
  let q (n : String) : Lean.Expr := mkConst (Q ++ Name.mkSimple n)
  let mut nm : Nat := 0
  -- the constructor of the history entry
  let runN ← norm3 (← tyOf (X ++ `RealChildE.run))
  same3 "RealChildE.run" runN (q "RunReal")
  for mu in ["RunNoEv", "RunEvEnd", "RunOldCache", "RunNoAdm", "RunNoSynth", "RunNoQuiet", "RunOff"] do
    diff3 s!"RealChildE.run vs {mu}" runN (q mu); nm := nm + 1
  logInfo m!"FGCIRCUIT28 DEFS-RUN: RealChildE.run matches the independently written constructor (the producing run's start world carries the evidence, the history is the cache field, the run is the full entry); {nm} mutants rejected (no evidence, evidence at the end world, the old cache field, a premise missing, the profile-free entry)"

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2hHist
  let Q := `Tests.Gen5.FGCircuitPilotCheck28
  let q (n : String) : Lean.Expr := mkConst (Q ++ Name.mkSimple n)
  let mut nm : Nat := 0
  -- MissE : the type of a function; compare the bodies after instantiating the arguments with free variables
  let miss ← norm3 (← (do
    let t ← tyOf (X ++ `MissE)
    forallTelescope t fun xs _ => do
      let app := mkAppN (mkConst (X ++ `MissE)) xs
      let r ← norm3 app
      mkLambdaFVars xs r))
  let expM ← norm3 (← (do
    let t ← tyOf (Q ++ `ExpMiss)
    forallTelescope t fun xs _ => do
      -- ExpMiss O E true true true
      let n := xs.size
      let app := mkAppN (mkConst (Q ++ `ExpMiss)) (xs.extract 0 (n - 3) ++ #[mkConst ``Bool.true, mkConst ``Bool.true, mkConst ``Bool.true])
      let r ← norm3 app
      mkLambdaFVars (xs.extract 0 (n - 3)) r))
  unless ← withDefault (isDefEq miss expM) do throwError "MissE is not the expected statement"
  for (mu, args) in [("depth", #[``Bool.false, ``Bool.true, ``Bool.true]), ("miss", #[``Bool.true, ``Bool.false, ``Bool.true]), ("hist", #[``Bool.true, ``Bool.true, ``Bool.false])] do
    let m ← norm3 (← (do
      let t ← tyOf (Q ++ `ExpMiss)
      forallTelescope t fun xs _ => do
        let n := xs.size
        let app := mkAppN (mkConst (Q ++ `ExpMiss)) (xs.extract 0 (n - 3) ++ args.map mkConst)
        let r ← norm3 app
        mkLambdaFVars (xs.extract 0 (n - 3)) r))
    if ← withDefault (isDefEq miss m) then throwError "MissE vs the no-{mu} mutant was accepted"
    nm := nm + 1
  logInfo m!"FGCIRCUIT28 DEFS-MISS: MissE matches the independently written ExpMiss (depth D ≥ 1, a JQ world whose cache entries are all RealChildE, no entry for the callee ⇒ the evidence at the call's contexts); {nm} mutants rejected (no depth bound, no miss condition, no history invariant)"

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2hHist
  let Q := `Tests.Gen5.FGCircuitPilotCheck28
  let jqh ← norm3 (← (do
    let t ← tyOf (X ++ `JQH)
    forallTelescope t fun xs _ => do mkLambdaFVars xs (← norm3 (mkAppN (mkConst (X ++ `JQH)) xs))))
  let mk (n : Name) : MetaM Lean.Expr := do
    let t ← tyOf n
    forallTelescope t fun xs _ => do mkLambdaFVars xs (← norm3 (mkAppN (mkConst n) xs))
  let e ← norm3 (← mk (Q ++ `ExpJQH))
  unless ← withDefault (isDefEq jqh e) do throwError "JQH is not the expected invariant"
  let mut nm : Nat := 0
  for mu in ["JQHOld", "JQHNoCache"] do
    let m ← norm3 (← mk (Q ++ Name.mkSimple mu))
    if ← withDefault (isDefEq jqh m) then throwError "JQH vs {mu} was accepted"
    nm := nm + 1
  logInfo m!"FGCIRCUIT28 DEFS-JQH: JQH matches the independently written ExpJQH (JQ plus a cache whose every entry is a RealChildE); {nm} mutants rejected (the old RealChildA cache, no cache)"

/-! ## 2. LEMMAS (complete types, normalised once) -/

set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS2hHist
  let Q := `Tests.Gen5.FGCircuitPilotCheck28
  let q (n : String) : Lean.Expr := mkConst (Q ++ Name.mkSimple n)
  -- cache initialisation
  let headN ← norm3 (← tyOf (X ++ `coreHeadOff_jqhA))
  same3 "coreHeadOff_jqhA" headN (q "HeadReal")
  let mut nm0 : Nat := 0
  for mu in ["HeadDiag", "HeadStart1", "HeadDepth0", "HeadOld", "HeadNoCache"] do
    diff3 s!"coreHeadOff_jqhA vs {mu}" headN (q mu); nm0 := nm0 + 1
  -- hit / miss
  let chN ← norm3 (← tyOf (X ++ `synthesizeChild_tripleH))
  same3 "synthesizeChild_tripleH" chN (q "ChReal")
  let mut nm1 : Nat := 0
  for mu in ["ChNoEv", "ChOldPost", "ChNoCachePost", "ChNoDepth", "ChNoMiss", "ChNoEntry"] do
    diff3 s!"synthesizeChild_tripleH vs {mu}" chN (q mu); nm1 := nm1 + 1
  logInfo m!"FGCIRCUIT28 SIGNATURES-INV: the complete types of coreHeadOff_jqhA (the profile-free head of the root run, from JQ at depth 0, establishes JQH at depth 1 for any E: the cache is initialised) and synthesizeChild_tripleH (from a JQH world at depth ≥ 1, with the miss premise and the nested entry's triple: the result is a RealChildE n and the end world is JQH) match the independently written types; mutants rejected: coreHeadOff_jqhA {nm0} (the diagnostic head, a depth-1 start, the conclusion at depth 0, the old cache, no cache), synthesizeChild_tripleH {nm1} (a RealChildA result, the old or no cache in the post, no depth bound, no miss premise, no entry premise)"

set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS2hHist
  let Q := `Tests.Gen5.FGCircuitPilotCheck28
  let q (n : String) : Lean.Expr := mkConst (Q ++ Name.mkSimple n)
  let coreN ← norm3 (← tyOf (X ++ `hftCoreCloses_of_kidsH))
  same3 "hftCoreCloses_of_kidsH" coreN (q "CH_True")
  let mut nm1 : Nat := 0
  for mu in ["CH_missNoDepth", "CH_missNoMiss", "CH_missNoHist", "CH_missOnHit", "CH_missOtherCtx", "CH_missOnlyReads", "CH_missOnlyProf", "CH_missEq", "CH_missTrue", "CH_OldKenv", "CH_ReadersSwapped", "CH_ReaderShapes", "CH_GatesSwapped", "CH_GatesHttp", "CH_NoStart", "CH_NoCell", "CH_NoReaders", "CH_NoGates", "CH_NoKenv", "CH_NoConcl", "CH_KenvIndep", "CH_ReadersIndep", "CH_GatesIndep", "CH_ConclWorld", "CH_CtxM", "CH_CtxC", "CH_RefM", "CH_RefC"] do
    diff3 s!"hftCoreCloses_of_kidsH vs {mu}" coreN (q mu); nm1 := nm1 + 1
  logInfo m!"FGCIRCUIT28 SIGNATURES-CORE: the complete type of hftCoreCloses_of_kidsH matches the independently written expected type (the children's hypothesis is the miss premise MissE over the evidence ReadsAt e ∧ GetEnvProfileAt at the SAME environment as the readers and the gates); {nm1} mutants rejected (each of the miss premise's knobs, the old universal premise, only reads / only profile / equality / True evidence, readers or gates swapped, a premise or the conclusion missing, the environment of the readers / gates / hkenv at an independent world, another conclusion world / context / reference)"

set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := mkConst n
  let X := `Tools.ShippingFGCircuitS2hHist
  let Q := `Tests.Gen5.FGCircuitPilotCheck28
  let q (n : String) : Lean.Expr := mkConst (Q ++ Name.mkSimple n)
  let finN ← norm3 (← tyOf (X ++ `synth_hftPcieOutByte_finalOffLNKH_Z))
  same3 "synth_hftPcieOutByte_finalOffLNKH_Z" finN (mkApp2 (q "FH") (C ``HftObCDZ) (C ``cdvZ))
  let mut nm2 : Nat := 0
  for mu in ["FH_missNoDepth", "FH_missNoMiss", "FH_missNoHist", "FH_missOnHit", "FH_missOtherCtx", "FH_missOnlyReads", "FH_missOnlyProf", "FH_missEq", "FH_missTrue", "FH_OldKenv", "FH_KenvEnd", "FH_GatesEnd", "FH_BothEnd", "FH_Diag", "FH_OldArt", "FH_NoHcd", "FH_NoTop", "FH_NoKenv", "FH_NoKg", "FH_KgSwapped", "FH_KgHttp", "FH_KgTrue", "FH_Root", "FH_PostRoot", "FH_Output", "FH_HcdEnd", "FH_ConclEnd", "FH_RefM", "FH_RefC", "FH_CtxM", "FH_CtxC", "FH_Design"] do
    diff3 s!"finalOffLNKH_Z vs {mu}" finN (mkApp2 (q mu) (C ``HftObCDZ) (C ``cdvZ)); nm2 := nm2 + 1
  for mu in ["FH_CarrierY", "FH_CarrierOld", "FH_ObY"] do
    diff3 s!"finalOffLNKH_Z vs {mu}" finN (q mu); nm2 := nm2 + 1
  logInfo m!"FGCIRCUIT28 SIGNATURES-FINAL: the complete type of synth_hftPcieOutByte_finalOffLNKH_Z matches the independently written expected type (14 hypotheses; hkenv of S2d is replaced by the miss premise hmiss over ReadsAt ∧ profile-off at the root start environment envAt cref w; hkgates unchanged); {nm2} mutants rejected (each of the miss premise's knobs, the old universal hkenv, hmiss or hkgates environment at the END world or both, the diagnostic entry, the old artifact, a premise missing, hkgates swapped / one name twice / True, another root / post root / output, hcd or conclusion at the end world, another reference / context / design, another carrier / obligation)"

/-! ## 3. structural checks and the reach walk -/

partial def binderNames : Lean.Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2hHist
  let mut nm : Nat := 0
  -- the consumer of a history entry: the premise is a RealChildE over the evidence, not a RealChildA under a universal premise
  let t ← tyOf (X ++ `machineChild_of_realE)
  let uses := t.getUsedConstants
  for c in [``RealChildE, ``KidEv, ``Tools.ShippingFGCircuitCover.RootReader, ``Tools.ShippingFGCircuitFinal4.EntryGates, ``Tools.ShippingGen5EnvFrame3.CellPrem] do
    unless uses.contains c do throwError "machineChild_of_realE does not mention {c}"
  for bad in [``Tools.ShippingFGCircuitS2dKids.KidStartEnv, ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv, ``Tools.ShippingChildCacheA.RealChildA, ``Tools.ShippingMachineEntry.MachineDefines] do
    if uses.contains bad then throwError "machineChild_of_realE mentions {bad}"
  nm := nm + 9
  -- the final statement and the core lemma do not mention the universal premise
  for n in [`hftCoreCloses_of_kidsH, `synth_hftPcieOutByte_finalOffLNKH_Z] do
    let t ← tyOf (X ++ n)
    let t ← if n == `synth_hftPcieOutByte_finalOffLNKH_Z then (do let some t' ← unfoldDefinition? t | throwError "not a definition"; pure t') else pure t
    let uses := t.getUsedConstants
    for bad in [``Tools.ShippingFGCircuitS2dKids.KidStartEnv, ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv, ``Tools.ShippingFGCircuitS2aClose.HftKidsDefine, ``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingMachineEntry.MachineCloses] do
      if uses.contains bad then throwError "{n} mentions {bad}"
    unless uses.contains ``MissE do throwError "{n} does not mention MissE"
    nm := nm + 6
  let t2 ← tyOf (X ++ `hftCoreCloses_of_kidsH)
  let names := binderNames (← instantiateMVars t2) |>.map (·.toString)
  let exp0 := ["mctx", "mref", "cctx", "cref", "L", "w", "hstart", "hcell", "lvl", "hrH", "hrT", "hg", "hmiss"]
  unless names == exp0 do throwError "hftCoreCloses_of_kidsH binders: {names}"
  nm := nm + 1
  -- the reach walk (Check26): within the walk over defnInfo types and values under Tools/Sparkle
  let env ← getEnv
  let r := reach env [``MissE, ``Tools.ShippingFGCircuitS2dKids.HftKidsGates, ``KidEv] {}
  for bad in [``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingFGCircuitS2aClose.HftKidsDefine, ``Tools.ShippingMachineEntry.MachineCloses, ``Tools.ShippingFGCircuitS2dKids.KidStartEnv] do
    if r.contains bad then throwError "{bad} is reachable from hmiss/hkgates within the walk"
  for good in [``Tools.ShippingFGCircuitS1oHead.GetEnvProfileAt, ``Tools.ShippingFGCircuitFinal4.EntryGates, ``RealChildE, ``JQH, ``Tools.ShippingGen5Env.ReadsAt] do
    unless r.contains good do throwError "{good} is not reached from hmiss/hkgates"
  nm := nm + 9
  logInfo m!"FGCIRCUIT28 REACH: machineChild_of_realE takes a RealChildE over the saved evidence (no RealChildA premise, no universal KidStartEnv, no MachineDefines); hftCoreCloses_of_kidsH and finalOffLNKH_Z mention MissE and none of KidStartEnv / HftKidsStartEnv / HftKidsDefine / MachineDefines / MachineCloses; hftCoreCloses_of_kidsH binders {exp0}; {nm} structural checks. Within the reach walk (types and values of defnInfo under Tools/Sparkle; inductive constructors and theorems are not unfolded) MachineDefines, HftKidsDefine, MachineCloses and KidStartEnv are NOT reachable from MissE / HftKidsGates / KidEv (reach set {r.size}); this is not a claim about the whole dependency closure"

/-! ## 4. REMAINING, AXIOMS -/

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2hHist
  let a ← getConstInfo (X ++ `MissE)
  let pp ← try pure (toString (← ppExpr a.value!)) catch _ => pure "<unprintable>"
  logInfo m!"FGCIRCUIT28 REMAINING hmiss : MissE L.O (KidEv mref cref (envAt cref w)) [FG D.T-4h] := {pp}"
  logInfo m!"FGCIRCUIT28 REMAINING hkgates : HftKidsGates (envAt cref w) [FG D.T-4g] (unchanged, S2g)"
  logInfo m!"FGCIRCUIT28 REMAINING scope: hmiss is asked in worlds of a history whose every cache entry already carries its own evidence, only where a child run is about to be created; it is still universal over those worlds (their environment is not tied to the root's run) — the root run's frames alone do not supply it"

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2hHist
  let names : List Name := [X ++ `RealChildE.toA, X ++ `cacheE_empty, X ++ `cacheE_insert, X ++ `JQH.toC, X ++ `stableA_JQH, X ++ `jqh_cacheGet, X ++ `tripleH_cacheGet, X ++ `tripleH_clear, X ++ `tripleH_clear',
    X ++ `jqh_insert_runs, X ++ `synthesizeChild_tripleH, X ++ `synthesizeChild_tripleH', X ++ `synthesizeChild_realH', X ++ `core_tripleAH, X ++ `childKeepsH_all, X ++ `childKeepsH_all_of_tele, X ++ `htrH_of_tele,
    X ++ `closeInstsM_runH, X ++ `closeInstsGM_runH, X ++ `machineClosesAtH_of_pure, X ++ `machineClosesAtH_of_gateKids, X ++ `callsPureE_of_gateKids,
    X ++ `machineChild_of_realE, X ++ `hft_kid_ifaceH, X ++ `hft_closesAtH, X ++ `coreHeadOff_jqhA, X ++ `hftCoreCloses_of_kidsH,
    X ++ `synth_hftPcieOutByte_finalOffLNKH, X ++ `synth_hftPcieOutByte_finalOffLNKH_Z, X ++ `synth_hftPcieOutByte_finalOffLNKH_Y, X ++ `synth_hftPcieOutByte_finalOffLNKH_X]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT28 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck28
