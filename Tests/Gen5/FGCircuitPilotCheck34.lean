import Tools.ShippingFGCircuitS2nAdm
import Tests.Gen5.FGCircuitPilotCheck33
set_option autoImplicit false
-- FG circuit pilot S2n check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §40.

/-! # FGCircuitPilotCheck34 (light)

ONE comparison function (`Check33.cmp`: the same constants are normalised and `isDefEq` runs at DEFAULT transparency) is used for the positive case and for every mutant.

1. DEFS: `AdmBoth` (the context-carried form) and `QuietCover` (the world-level replacement of `AdmDownR`) against independently written statements, with mutants.
2. SIGNATURES: the complete types of `hftCoreCloses_of_kidsR'` (hdown replaced by hcover) and `hftCoreCloses_of_cover` (seven premises replaced by `hcover hs h0`), binder kinds and names, with mutants (each premise dropped, the cover without reach / without ReadsAt / reversed, another root environment, a world not reached from the root, an end world, the profile ON).
3. STEPS (where `AdmDownR` still occurs and where it does not), AXIOMS. WHENEVER `hftCoreCloses_of_kidsR'`, `hftCoreCloses_of_cover` or `QuietCover` changes, this check must be updated in the same commit. -/
namespace Tests.Gen5.FGCircuitPilotCheck34
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingChildInv Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS2hHist
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingFGCircuitS2nAdm
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5EnvFrame3 (CellPrem DRow)
open Tools.ShippingFGCircuitS1zClose (HftCoreCloses)
open Tools.ShippingFGCircuitCover (RootReader)
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 NmHttp NmTlp HttpData TlpData Pre ExpKidsGates tyOf binderNames idW iteStep)
open Tests.Gen5.FGCircuitPilotCheck33 (cmp agree differ binderKinds checkDef norm4 ExpQuiet ExpD ExpG ExpT ExpPS ExpProfOff ProfOnW)

/-- the normalisation of Check33, also unfolding this file's own independent definitions (used for the binder kinds) -/
def normOnce5 (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let some e' := iteStep e then return .visit e'
    if let .const c _ := e.getAppFn then
      if (`Tests.Gen5.FGCircuitPilotCheck34).isPrefixOf c || (`Tests.Gen5.FGCircuitPilotCheck33).isPrefixOf c ||
          c == ``Tests.Gen5.FGCircuitPilotCheck26.Pre || c == ``Tests.Gen5.FGCircuitPilotCheck26.ExpKidsGates then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm5 (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:6] do
    e ← normOnce5 e
  return e

/-! ## independently written statements -/

section Exp
variable {mref : Rf1} {cref : Rf2}

/-- both admissibilities, written again -/
def ExpBoth (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) (mctx : Cx) (cctx : Cc) : Prop :=
  AdmCtx O.quiet mctx cctx ∧ AdmCtx (ExpQuiet O.quiet mref cref e w₀) mctx cctx
def BothPlain (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) (mctx : Cx) (cctx : Cc) : Prop :=
  AdmCtx O.quiet mctx cctx
def BothStrong (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) (mctx : Cx) (cctx : Cc) : Prop :=
  AdmCtx (ExpQuiet O.quiet mref cref e w₀) mctx cctx
/-- the bridge direction (what `AdmDownR` says) is NOT the pair -/
def BothImp (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) (mctx : Cx) (cctx : Cc) : Prop :=
  AdmCtx (ExpQuiet O.quiet mref cref e w₀) mctx cctx → AdmCtx O.quiet mctx cctx
def BothOr (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) (mctx : Cx) (cctx : Cc) : Prop :=
  AdmCtx O.quiet mctx cctx ∨ AdmCtx (ExpQuiet O.quiet mref cref e w₀) mctx cctx
def BothOtherEnv (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) (mctx : Cx) (cctx : Cc) (e' : Environment) : Prop :=
  AdmCtx O.quiet mctx cctx ∧ AdmCtx (ExpQuiet O.quiet mref cref e' w₀) mctx cctx

/-- the cover, written again (knob `k`: 0 real; 1 no reach; 2 no ReadsAt; 3 the trivial reverse inclusion) -/
def ExpCov (k : Nat) (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop :=
  ∀ w : W,
    if k == 3 then ExpQuiet O.quiet mref cref e w₀ w → O.quiet w
    else O.quiet w → (if k == 2 then True else ReadsAt e cref w) ∧ (if k == 1 then True else Reached O.quiet mref cref w₀ w)
def ExpCover (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop := ExpCov 0 O e w₀
def CoverNoReach (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop := ExpCov 1 O e w₀
def CoverNoReads (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop := ExpCov 2 O e w₀
def CoverRev (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) : Prop := ExpCov 3 O e w₀
def CoverOtherEnv (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) (e' : Environment) : Prop :=
  ∀ w : W, O.quiet w → ReadsAt e' cref w ∧ Reached O.quiet mref cref w₀ w
def CoverOtherRoot (O : RefLawsAOps MkRefd mref cref) (e : Environment) (w₀ : W) (w₁ : W) : Prop :=
  ∀ w : W, O.quiet w → ReadsAt e cref w ∧ Reached O.quiet mref cref w₁ w
end Exp

/-- `hftCoreCloses_of_kidsR'`, complete. Knobs: which premises are present; `cov` the cover variant; `fEnv` the world whose environment is the root environment, `fRoot` the world the reach starts from, `fProf` the world of the root profile fact, `fW` the conclusion's world; `profOn` replaces the root profile fact by the profile lookup ON. -/
def ExpKR (needStart needCell needR needG needAdm needCov needD needGd needT needS need0 concl profOn : Bool) (cov : Nat)
    (fEnv fRoot fProf fW : W → W) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : Laws mref cref) {w : W},
    Pre needStart (Start L mctx cctx w) (
    Pre needCell (CellPrem MkRefd mref cref) (
    ∀ {lvl : Lean.Expr → Nat},
    Pre needR (RootReader lvl (envAt cref w) NmHttp HttpData) (
    Pre needR (RootReader lvl (envAt cref w) NmTlp TlpData) (
    Pre needG (ExpKidsGates (envAt cref w) NmHttp NmTlp) (
    Pre needAdm (AdmCtx (ExpQuiet L.O.quiet mref cref (envAt cref (fEnv w)) (fRoot w)) mctx cctx) (
    Pre needCov (ExpCov cov L.O (envAt cref (fEnv w)) (fRoot w)) (
    Pre needD (ExpD L.O (envAt cref (fEnv w)) (fRoot w)) (
    Pre needGd (ExpG L.O (envAt cref (fEnv w)) (fRoot w)) (
    Pre needT (ExpT L.O (envAt cref (fEnv w)) (fRoot w)) (
    Pre needS (ExpPS L.O (fRoot w)) (
    Pre need0 (if profOn then ProfOnW mref cref (fProf w) else ExpProfOff mref cref (fProf w)) (
    if concl then HftCoreCloses mctx mref cctx cref (fW w) else True))))))))))))
def KR_real : Prop := ExpKR true true true true true true true true true true true true false 0 idW idW idW idW
def KR_noStart : Prop := ExpKR false true true true true true true true true true true true false 0 idW idW idW idW
def KR_noCell : Prop := ExpKR true false true true true true true true true true true true false 0 idW idW idW idW
def KR_noReaders : Prop := ExpKR true true false true true true true true true true true true false 0 idW idW idW idW
def KR_noGates : Prop := ExpKR true true true false true true true true true true true true false 0 idW idW idW idW
def KR_noAdm : Prop := ExpKR true true true true false true true true true true true true false 0 idW idW idW idW
def KR_noCov : Prop := ExpKR true true true true true false true true true true true true false 0 idW idW idW idW
def KR_noD : Prop := ExpKR true true true true true true false true true true true true false 0 idW idW idW idW
def KR_noG : Prop := ExpKR true true true true true true true false true true true true false 0 idW idW idW idW
def KR_noT : Prop := ExpKR true true true true true true true true false true true true false 0 idW idW idW idW
def KR_noS : Prop := ExpKR true true true true true true true true true false true true false 0 idW idW idW idW
def KR_no0 : Prop := ExpKR true true true true true true true true true true false true false 0 idW idW idW idW
def KR_noConcl : Prop := ExpKR true true true true true true true true true true true false false 0 idW idW idW idW
def KR_covNoReach : Prop := ExpKR true true true true true true true true true true true true false 1 idW idW idW idW
def KR_covNoReads : Prop := ExpKR true true true true true true true true true true true true false 2 idW idW idW idW
def KR_covRev : Prop := ExpKR true true true true true true true true true true true true false 3 idW idW idW idW
def KR_profOn : Prop := ExpKR true true true true true true true true true true true true true 0 idW idW idW idW
def KR_otherEnv : Prop := ∀ {a : W}, ExpKR true true true true true true true true true true true true false 0 (fun _ => a) idW idW idW
def KR_notReached : Prop := ∀ {a : W}, ExpKR true true true true true true true true true true true true false 0 idW (fun _ => a) idW idW
def KR_endWorld : Prop := ∀ {a : W}, ExpKR true true true true true true true true true true true true false 0 idW idW idW (fun _ => a)

/-- `hftCoreCloses_of_cover`, complete (the seven premises `hadm hdown hD hG hT` are gone: `hcover hs h0`) -/
def ExpCC (needStart needCell needR needG needCov needS need0 concl profOn : Bool) (cov : Nat) (fEnv fRoot fProf fW : W → W) : Prop :=
  ∀ {mctx : Cx} {mref : Rf1} {cctx : Cc} {cref : Rf2} (L : Laws mref cref) {w : W},
    Pre needStart (Start L mctx cctx w) (
    Pre needCell (CellPrem MkRefd mref cref) (
    ∀ {lvl : Lean.Expr → Nat},
    Pre needR (RootReader lvl (envAt cref w) NmHttp HttpData) (
    Pre needR (RootReader lvl (envAt cref w) NmTlp TlpData) (
    Pre needG (ExpKidsGates (envAt cref w) NmHttp NmTlp) (
    Pre needCov (ExpCov cov L.O (envAt cref (fEnv w)) (fRoot w)) (
    Pre needS (ExpPS L.O (fRoot w)) (
    Pre need0 (if profOn then ProfOnW mref cref (fProf w) else ExpProfOff mref cref (fProf w)) (
    if concl then HftCoreCloses mctx mref cctx cref (fW w) else True))))))))
def CC_real : Prop := ExpCC true true true true true true true true false 0 idW idW idW idW
def CC_noStart : Prop := ExpCC false true true true true true true true false 0 idW idW idW idW
def CC_noCell : Prop := ExpCC true false true true true true true true false 0 idW idW idW idW
def CC_noReaders : Prop := ExpCC true true false true true true true true false 0 idW idW idW idW
def CC_noGates : Prop := ExpCC true true true false true true true true false 0 idW idW idW idW
def CC_noCov : Prop := ExpCC true true true true false true true true false 0 idW idW idW idW
def CC_noS : Prop := ExpCC true true true true true false true true false 0 idW idW idW idW
def CC_no0 : Prop := ExpCC true true true true true true false true false 0 idW idW idW idW
def CC_noConcl : Prop := ExpCC true true true true true true true false false 0 idW idW idW idW
def CC_covNoReach : Prop := ExpCC true true true true true true true true false 1 idW idW idW idW
def CC_covNoReads : Prop := ExpCC true true true true true true true true false 2 idW idW idW idW
def CC_covRev : Prop := ExpCC true true true true true true true true false 3 idW idW idW idW
def CC_profOn : Prop := ExpCC true true true true true true true true true 0 idW idW idW idW
def CC_otherEnv : Prop := ∀ {a : W}, ExpCC true true true true true true true true false 0 (fun _ => a) idW idW idW
def CC_notReached : Prop := ∀ {a : W}, ExpCC true true true true true true true true false 0 idW (fun _ => a) idW idW
def CC_endWorld : Prop := ∀ {a : W}, ExpCC true true true true true true true true false 0 idW idW idW (fun _ => a)

/-! ## 1. DEFS -/

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2nAdm
  let Q := `Tests.Gen5.FGCircuitPilotCheck34
  let mut nm : Nat := 0
  nm := nm + (← checkDef "AdmBoth" (X ++ `AdmBoth) (Q ++ `ExpBoth)
    [Q ++ `BothPlain, Q ++ `BothStrong, Q ++ `BothImp, Q ++ `BothOr, Q ++ `BothOtherEnv])
  nm := nm + (← checkDef "QuietCover" (X ++ `QuietCover) (Q ++ `ExpCover)
    [Q ++ `CoverNoReach, Q ++ `CoverNoReads, Q ++ `CoverRev, Q ++ `CoverOtherEnv, Q ++ `CoverOtherRoot])
  logInfo m!"FGCIRCUIT34 DEFS: AdmBoth (the plain AND the strengthened admissibility of a context, both kept) and QuietCover (every quiet world of the laws reads the root environment and is reached from the root start world) match the independently written statements, with the same comparison function and the same transparency for the positive case and every mutant; {nm} mutants rejected (only the plain half, only the strengthened half, the bridge implication AdmDownR instead of the pair, a disjunction, another environment; no reach, no ReadsAt, the trivial reverse inclusion, another environment, reach from another world)"

/-! ## 2. SIGNATURES -/

set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2nAdm
  let Q := `Tests.Gen5.FGCircuitPilotCheck34
  let q (n : String) : Lean.Expr := Lean.mkConst (Q ++ Name.mkSimple n)
  let t1 ← tyOf (X ++ `hftCoreCloses_of_kidsR')
  agree "hftCoreCloses_of_kidsR'" t1 (q "KR_real")
  unless binderKinds (← norm5 t1) == binderKinds (← norm5 (q "KR_real")) do throwError "hftCoreCloses_of_kidsR': binder kinds differ {repr (binderKinds (← norm5 t1))} vs {repr (binderKinds (← norm5 (q "KR_real")))}"
  let names1 := binderNames (← instantiateMVars t1) |>.map (·.toString)
  let exp1 := ["mctx", "mref", "cctx", "cref", "L", "w", "hstart", "hcell", "lvl", "hrH", "hrT", "hg", "hadm", "hcover", "hD", "hG", "hT", "hs", "h0"]
  unless names1 == exp1 do throwError "hftCoreCloses_of_kidsR' binders: {names1}"
  let mut n1 : Nat := 0
  for mu in ["KR_noStart", "KR_noCell", "KR_noReaders", "KR_noGates", "KR_noAdm", "KR_noCov", "KR_noD", "KR_noG", "KR_noT", "KR_noS", "KR_no0", "KR_noConcl",
      "KR_covNoReach", "KR_covNoReads", "KR_covRev", "KR_profOn", "KR_otherEnv", "KR_notReached", "KR_endWorld"] do
    differ s!"hftCoreCloses_of_kidsR' vs {mu}" t1 (q mu); n1 := n1 + 1
  let t2 ← tyOf (X ++ `hftCoreCloses_of_cover)
  agree "hftCoreCloses_of_cover" t2 (q "CC_real")
  unless binderKinds (← norm5 t2) == binderKinds (← norm5 (q "CC_real")) do throwError "hftCoreCloses_of_cover: binder kinds differ"
  let names2 := binderNames (← instantiateMVars t2) |>.map (·.toString)
  let exp2 := ["mctx", "mref", "cctx", "cref", "L", "w", "hstart", "hcell", "lvl", "hrH", "hrT", "hg", "hcover", "hs", "h0"]
  unless names2 == exp2 do throwError "hftCoreCloses_of_cover binders: {names2}"
  let mut n2 : Nat := 0
  for mu in ["CC_noStart", "CC_noCell", "CC_noReaders", "CC_noGates", "CC_noCov", "CC_noS", "CC_no0", "CC_noConcl",
      "CC_covNoReach", "CC_covNoReads", "CC_covRev", "CC_profOn", "CC_otherEnv", "CC_notReached", "CC_endWorld"] do
    differ s!"hftCoreCloses_of_cover vs {mu}" t2 (q mu); n2 := n2 + 1
  logInfo m!"FGCIRCUIT34 SIGNATURES: the complete type of hftCoreCloses_of_kidsR' (hdown : AdmDownR … of hftCoreCloses_of_kidsR replaced by hcover : QuietCover L.O (envAt cref w) w; binders {exp1}) and of hftCoreCloses_of_cover (hadm hdown hD hG hT replaced by the one world-level premise hcover; binders {exp2}) match the independently written types (binder kinds too); mutants rejected: kidsR' {n1} (each premise dropped (12), the cover without reach / without ReadsAt / the trivial reverse inclusion, the profile lookup ON at the root, another root environment, a world not reached from the root, an end world), cover {n2} (each premise dropped (8), the same controls)"

/-! ## 3. STEPS, CONTROLS, AXIOMS -/

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2nAdm
  let usesOf (n : Name) : MetaM (Array Name) := do pure (← tyOf (X ++ n)).getUsedConstants
  let mut c : Nat := 0
  -- AdmDownR is gone from both new statements; the cover route removes the other four as well
  let u1 ← usesOf `hftCoreCloses_of_kidsR'
  for bad in [``AdmDownR, ``MissE] do
    if u1.contains bad then throwError "hftCoreCloses_of_kidsR' mentions {bad}";
  unless u1.contains ``QuietCover do throwError "hftCoreCloses_of_kidsR' does not take QuietCover"
  c := c + 3
  let u2 ← usesOf `hftCoreCloses_of_cover
  for bad in [``AdmDownR, ``DRowEnvR, ``DiagEnvR, ``TeleR, ``MissE] do
    if u2.contains bad then throwError "hftCoreCloses_of_cover mentions {bad}"
  unless u2.contains ``QuietCover do throwError "hftCoreCloses_of_cover does not take QuietCover"
  unless u2.contains ``ProfStepR do throwError "hftCoreCloses_of_cover does not take ProfStepR"
  c := c + 7
  -- the strengthened laws on AdmBoth contexts do not take AdmDownR; the only statement that does is the conversion
  for f in [`opsB, `OpsB.diag, `OpsB.frameT, `OpsB.excOk, `OpsB.frameQ, `OpsB.cacheSetQ, `OpsB.depthSetQ] do
    let u3 ← usesOf f
    if u3.contains ``AdmDownR then throwError "{f} mentions AdmDownR"
    if f != `opsB && f != `OpsB.excOk && !u3.contains ``AdmBoth then throwError "{f} does not use AdmBoth"
    if f == `OpsB.excOk && !u3.contains ``AdmBoth then throwError "{f} does not use AdmBoth"
  let u4 ← usesOf `admBoth_of_down
  unless u4.contains ``AdmDownR do throwError "admBoth_of_down does not take AdmDownR"
  c := c + 10
  logInfo m!"FGCIRCUIT34 STEPS: hftCoreCloses_of_kidsR' and hftCoreCloses_of_cover do not mention AdmDownR (nor MissE); the cover route also drops DRowEnvR / DiagEnvR / TeleR; opsB (the ten strengthened operation laws, the ropsR fields) is stated on AdmBoth contexts and does not mention AdmDownR; the only statement of the file that takes AdmDownR is admBoth_of_down, the conversion from a bundle context to an AdmBoth one (the entry point into the S2h chain, which takes ONE bundle); {c} structural checks"

run_cmd liftTermElabM do
  let lines := [
    "hs : ProfStepR L.O w (a leaf step from a reached world keeps the profile lookup unset; needs only Reached + LeafStep + ProfOffW)",
    "h0 : ProfOffW mref cref w (the profile lookup is unset at the root start world)",
    "hcover : QuietCover L.O (envAt cref w) w (every quiet world of the laws reads the root environment and is reached from w; a premise about the laws' quiet predicate, NOT supplied; hftCoreCloses_of_kidsR' keeps hadm hD hG hT, which it makes redundant)",
    "NOT DONE: the carried form AdmBoth is established (root, context updates) and the strengthened laws are derived on it (opsB), but the S2h chain takes one bundle whose contexts are AdmCtx bundle.quiet; a chain over AdmBoth contexts is not built, so the conversion admBoth_of_down (= AdmDownR) is still what the unchanged chain needs without the cover"]
  for l in lines do logInfo m!"FGCIRCUIT34 REMAINING {l}"

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2nAdm
  let names : List Name := [`admBoth_none, `admBoth_mkMetaContext, `AdmBoth.lctx, `AdmBoth.localInsts, `AdmBoth.lctx_insts, `AdmBoth.config, `AdmBoth.cctx,
    `AdmBoth.plain, `admBoth_of_down, `opsB, `quietR_eq_of_cover, `admDownR_of_cover, `drow_toFramedA, `drowEnvR_of_cover, `diagEnvR_of_cover, `teleR_of_cover,
    `hftCoreCloses_of_kidsR', `hftCoreCloses_of_cover].map (X ++ ·)
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT34 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck34
