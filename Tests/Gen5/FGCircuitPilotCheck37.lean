import Tools.ShippingFGCircuitS2rFinal
import Tests.Gen5.FGCircuitPilotCheck33
import Tests.Gen5.FGCircuitPilotCheck31
import Tests.Gen5.FGCircuitCmp
set_option autoImplicit false
-- FG circuit pilot S2r check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §42.

/-! # FGCircuitPilotCheck37 (light: each part is a small `run_cmd`; every real type is normalised ONCE; ONE criterion `FGCircuitCmp.stmtEq` for the expected statement and for every mutant)

The combined final statement v2 `HftFinalStmtOffCombined2` (S2r): `hdec` is gone (`hftCallDec_of_checked`, `hfind` not a hypothesis), `hmiss` is replaced by the seven premises of S2m (their quantifier ranges differ: DRow/Diag, ProfStep, ProfOff, Tele, admissibility; see §39).

1. SIGNATURES-FINAL: `synth_hftPcieOutByte_finalOffCombined2_Z` (COMPLETE type, binder kinds at all depths) against an independently written `ExpFinal2`, with mutants: another world / reference / environment / root / carrier / output / conclusion, every premise dropped, `hfind` as an extra hypothesis, the old `hdec` / `hmiss` premises, the profile lookup ON, reach from another world, the plain bundle, ...
2. HYPS: the binder list (19 explicit), what is NOT a hypothesis (`hfind`, `hdec`, `hmiss`, `htop`, ...), the reach walk from the seven premises, and the value of the final theorem (it is built from `hftCallDec_of_checked`, `root_find_of_headAtOff`, `ropsR`, `missR`, `hftCoreCloses_of_kidsR`, `kid_shipsResW`; not from `hftCoreCloses_of_kidsH`).
3. SIGNATURES-TOP, REMAINING, AXIOMS. WHENEVER the final wrapper changes, this check must be updated in the same commit. -/
namespace Tests.Gen5.FGCircuitPilotCheck37
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS2hHist (MissE JQH EQH CacheE KidEv)
open Tools.ShippingFGCircuitS2rFinal
open Tools.ShippingFGCircuitS2mReach
open Tools.ShippingFGCircuitS2jTop (HftCallDec)
open Tools.ShippingFGCircuitS2gGates (HftKidsGateFacts)
open Tools.ShippingGen2 (Laws Start)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt
open Tools.ShippingFGCircuitS1tFinal (cdvZ cdvY cdvOld CDRel)
open Tools.ShippingFGCircuitS1rCD (HftObCDZ)
open Tools.ShippingFGCircuitS1uSrc (HftRootLink)
open Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitS1iEnv Tools.ShippingGen2 Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuit
open Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.IR.AST
open Tools.ShippingChildInv Tools.ShippingChildBndCore Tools.ShippingChildInvA Tools.ShippingChildVCA Tools.ShippingChildCacheA Tools.ShippingChildFresh
open Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iHead
open Tools.ShippingFGCircuitS1kPkg Tools.ShippingFGCircuitS1qLinked Tools.ShippingFGCircuitS1qHead
open Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1tFinal
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 Mod ZS ZE idF idW NmRoot NmHttp NmTlp ShE RootData HttpData TlpData Pre EntryOf iteStep binderInfos)
open Tests.Gen5.FGCircuitPilotCheck28 (kmissR)
open Tests.Gen5.FGCircuitPilotCheck30 (ExpDec)
open Tests.Gen5.FGCircuitPilotCheck27 (ExpHK MuSwap MuSwapName MuHttpTwice MuTlpTwice MuHttpOnly MuTlpOnly MuWholeBoth MuTrue)
open Tests.Gen5.FGCircuitPilotCheck31 (EnvK eS eE e0)
open Tests.Gen5.FGCircuitPilotCheck33 (ExpQuiet ExpD ExpG ExpT ExpPS ExpDown ExpProfOff ProfOnW DNoReach DNoReads DStart GNoReach TPlain TNoReach DownUp DownId PSNoReach PSStart PSAnyStep)

/-- **`HftFinalStmtOffCombined2`, written again.** Knobs (each mutant turns one): the entry (`diag`), the carrier (`oldArt`), which premises are present (`needFind`: the `hfind` that must NOT be a hypothesis; `needDec` / `needMiss`: the old premises that are gone), the forms of the seven premises (`dP gP tP`), the profile fact (`profOn`), the environments (`hE` of `hcd`, `eA` of the five reach premises, `kE` of the gate facts, `cE` of the conclusion), the world the reach starts from (`rA`) and the world of the profile fact (`pA`), the readers' names and data, the root / post root / output shape, the reference / context / design of the post run, and which conjunct of the conclusion is present. -/
def ExpFinal2 (Ob : Environment → Prop) (CV : CDRel) (kgf : Environment → Prop)
    (dec : ∀ {ι : Type}, (Lean.Expr → Nat) → Environment → Prop)
    (miss : ∀ {mref : Rf1} {cref : Rf2}, RefLawsAOps MkRefd mref cref → Environment → Prop)
    (dP : ∀ {mref : Rf1} {cref : Rf2}, RefLawsAOps MkRefd mref cref → Environment → W → Prop)
    (gP : ∀ {mref : Rf1} {cref : Rf2}, RefLawsAOps MkRefd mref cref → Environment → W → Prop)
    (tP : ∀ {mref : Rf1} {cref : Rf2}, RefLawsAOps MkRefd mref cref → Environment → W → Prop)
    (dnP : ∀ {mref : Rf1} {cref : Rf2}, RefLawsAOps MkRefd mref cref → Environment → W → Prop)
    (psP : ∀ {mref : Rf1} {cref : Rf2}, RefLawsAOps MkRefd mref cref → W → Prop)
    (diag oldArt needHcd needFind needDec needMiss needAdm needDown needD needG needT needS need0 needKgf c1 c2 profOn : Bool)
    (hE eA kE cE : EnvK) (rA pA : W → W → W) (hn tn : Name) (hd td : MachineData) (root postRoot : Name) (sh : SigShape)
    (fM : Cx → Cx) (fR : Rf1 → Rf1) (fC : Cc → Cc) (fF : Rf2 → Rf2) (fD : Design → Design) : Prop :=
  HftRootLink →
  ∀ {ι : Type} {mref : Rf1} {cref : Rf2}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Cx} {cctx : Cc} {w w' : W} {b : Mod} {D' : Design},
    Start L mctx cctx w →
    RunsTo (EntryOf diag root) mctx mref cctx cref w (b, D') w' →
    CellPrem Tools.ShippingChildFresh.MkRefd mref cref →
    CheckedStart lvl env₀ cref w root hftRootType hftRootValue RootData →
    RootReader lvl (envAt cref w) hn hd →
    RootReader lvl (envAt cref w) tn td →
    Pre needHcd (Ob (hE cref w w' env₀)) (
    Pre needFind (∃ ci : ConstantInfo, (envAt cref w).find? root = some ci) (
    Pre needDec (dec (ι := ι) lvl (envAt cref w)) (
    Pre needMiss (miss L.O (envAt cref w)) (
    Pre needAdm (AdmCtx (ExpQuiet L.O.quiet mref cref (eA cref w w' env₀) (rA w w')) mctx cctx) (
    Pre needDown (dnP L.O (eA cref w w' env₀) (rA w w')) (
    Pre needD (dP L.O (eA cref w w' env₀) (rA w w')) (
    Pre needG (gP L.O (eA cref w w' env₀) (rA w w')) (
    Pre needT (tP L.O (eA cref w w' env₀) (rA w w')) (
    Pre needS (psP L.O (rA w w')) (
    Pre need0 (if profOn then ProfOnW mref cref (pA w w') else ExpProfOff mref cref (pA w w')) (
    Pre needKgf (kgf (kE cref w w' env₀)) (
    (if c1 then (∃ raw, PostRunOff (fM mctx) (fR mref) (fC cctx) (fF cref) w postRoot (fD D') b raw) else True) ∧
    (if c2 then (∃ (mm : MonoTy sh) (p : Pkg ι (fun _ => defaultDomain)),
      (if oldArt then RootArtifactMono (cE cref w w' env₀) (GPt (ι := ι) lvl (cE cref w w' env₀)) (PostRunOff (fM mctx) (fR mref) (fC cctx) (fF cref) w postRoot (fD D')) NmRoot sh mm b (fD D') p
       else RootArtifactMonoV CV (cE cref w w' env₀) (GPt (ι := ι) lvl (cE cref w w' env₀)) (PostRunOff (fM mctx) (fR mref) (fC cctx) (fF cref) w postRoot (fD D')) NmRoot sh mm b (fD D') p)) else True)))))))))))))

def decTrue {ι : Type} (_ : Lean.Expr → Nat) (_ : Environment) : Prop := True
def FD_real (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_no_Adm (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false false true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_no_Down (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true false true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_no_D (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true false true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_no_G (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true false true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_no_T (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true false true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_no_S (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true false true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_no_0 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true false true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_no_Kgf (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true false true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_no_Hcd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false false false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_hfind (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true true false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_hdec (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false true false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_hdecTrue (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @decTrue @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false true false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_hmiss (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false true true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_hdecAndHmiss (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false true true true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_hmissAndHfind (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true true false true true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_profOn (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true true eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_dNoReach (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @DNoReach @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_dNoReads (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @DNoReads @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_dStart (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @DStart @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_gNoReach (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @GNoReach @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_gAsD (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpD @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_tPlain (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @TPlain @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_tNoReach (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @TNoReach @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_downUp (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @DownUp @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_downId (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @DownId @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_psNoReach (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @PSNoReach false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_psStart (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @PSStart false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_psAny (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @PSAnyStep false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_adm_envEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eE eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_adm_env0 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS e0 eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_adm_envIndep (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : W}, ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS (fun cref _ _ _ => envAt cref a) eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_reach_fromEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZE ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_reach_fromIndep (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : W}, ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS (fun _ _ => a) ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_prof_atEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZE NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_prof_atIndep (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : W}, ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS (fun _ _ => a) NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_kgf_envEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eE eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_kgf_env0 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS e0 eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_kgf_envIndep (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : W}, ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS (fun cref _ _ _ => envAt cref a) eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_hcd_envEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eE eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_hcd_env0 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false e0 eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_concl_envEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eE ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_concl_env0 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS e0 ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_kgfSwap (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV MuSwap @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_kgfSwapName (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV MuSwapName @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_kgfHttpTwice (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV MuHttpTwice @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_kgfTlpTwice (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV MuTlpTwice @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_kgfHttpOnly (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV MuHttpOnly @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_kgfTlpOnly (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV MuTlpOnly @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_kgfWholeBoth (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV MuWholeBoth @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_kgfTrue (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV MuTrue @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_readersSwapped (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmTlp NmHttp TlpData HttpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_readerShapes (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp TlpData HttpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_diag (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS true false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_oldArt (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false true true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_noC1 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true false true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_noC2 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true false false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_noConcl (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true false false false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF idF
def FD_root (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmHttp NmRoot ShE idF idF idF idF idF
def FD_postRoot (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmHttp ShE idF idF idF idF idF
def FD_output (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ({ ShE with res := .one (.bits 16) }) idF idF idF idF idF
def FD_refM (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Rf1}, ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF (fun _ => a) idF idF idF
def FD_refC (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Rf2}, ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF (fun _ => a) idF
def FD_ctxM (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Cx}, ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE (fun _ => a) idF idF idF idF
def FD_ctxC (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Cc}, ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF (fun _ => a) idF idF
def FD_design (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Design}, ExpFinal2 Ob CV ExpHK @ExpDec @kmissR @ExpD @ExpG @ExpT @ExpDown @ExpPS false false true false false false true true true true true true true true true true false eS eS eS eS ZS ZS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE idF idF idF idF (fun _ => a)
def FD_carrierY : Prop := FD_real HftObCDZ cdvY
def FD_carrierOld : Prop := FD_real HftObCDZ cdvOld
def FD_obY : Prop := FD_real Tools.ShippingFGCircuitS1rCD.HftObCDY cdvZ

/-! ## the comparison: the real type is normalised ONCE; the expected statement and every mutant go through the same normalisation and the same criterion (`FGCircuitCmp.stmtEq`) -/

def unfold37 : List Name := [``HftFinalStmtOffCombined2, ``Tools.ShippingFGCircuitS2kFinal.HftFinalStmtOffCombined, ``HftKidsGateFacts, ``Tools.ShippingFGCircuitS2dKids.HftKidsGates,
  ``DRowEnvR, ``DiagEnvR, ``ProfStepR, ``ProfOffW, ``AdmDownR, ``TeleR, ``quietR, ``KidEv, ``MissE, ``JQH, ``HftCallDec]

def normOnce37 (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let .const c _ := e.getAppFn then
      if unfold37.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm37 (e0 : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e0
  for _ in [0:8] do
    e ← normOnce37 e
  -- `ExpKGF` was shown (Check27 SIGNATURES-A) to have the constructor type of `KidGateFacts`; here it is read as that structure
  let e1 ← Tests.Gen5.FGCircuitCmp.normCommon e
  pure (e1.replace fun x => if x.isConstOf `Tests.Gen5.FGCircuitPilotCheck27.ExpKGF then some (mkConst `Tools.ShippingFGCircuitS2gGates.KidGateFacts) else none)
def tyOf (n : Name) : MetaM Lean.Expr := do
  let ci ← getConstInfo n
  unless ci.levelParams.isEmpty do throwError "{n}: level parameters"
  pure ci.type
/-- `a` is the normal form of a real type (once); ONE criterion for the expected statement and for every mutant -/
def same37 (what : String) (a exp : Lean.Expr) : MetaM Unit := do
  Tests.Gen5.FGCircuitCmp.checkSame what a (← norm37 exp)
def diff37 (what : String) (a exp : Lean.Expr) : MetaM Unit := do
  Tests.Gen5.FGCircuitCmp.checkDiff what a (← norm37 exp)

/-! ## 1. the combined final statement v2 -/

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := Lean.mkConst n
  let Q := `Tests.Gen5.FGCircuitPilotCheck37
  let q (n : String) : Lean.Expr := Lean.mkConst (Q ++ Name.mkSimple n)
  let finN ← norm37 (← tyOf ``synth_hftPcieOutByte_finalOffCombined2_Z)
  same37 "synth_hftPcieOutByte_finalOffCombined2_Z" finN (mkApp2 (q "FD_real") (C ``HftObCDZ) (C ``cdvZ))
  let mut nm : Nat := 0
  for mu in ["FD_no_Adm", "FD_no_Down", "FD_no_D", "FD_no_G", "FD_no_T", "FD_no_S", "FD_no_0", "FD_no_Kgf", "FD_no_Hcd", "FD_hfind", "FD_hdec", "FD_hdecTrue", "FD_hmiss", "FD_hdecAndHmiss", "FD_hmissAndHfind", "FD_profOn", "FD_dNoReach", "FD_dNoReads", "FD_dStart", "FD_gNoReach", "FD_gAsD", "FD_tPlain", "FD_tNoReach", "FD_downUp", "FD_downId", "FD_psNoReach", "FD_psStart", "FD_psAny", "FD_adm_envEnd", "FD_adm_env0", "FD_adm_envIndep", "FD_reach_fromEnd", "FD_reach_fromIndep", "FD_prof_atEnd", "FD_prof_atIndep", "FD_kgf_envEnd", "FD_kgf_env0", "FD_kgf_envIndep", "FD_hcd_envEnd", "FD_hcd_env0", "FD_concl_envEnd", "FD_concl_env0", "FD_kgfSwap", "FD_kgfSwapName", "FD_kgfHttpTwice", "FD_kgfTlpTwice", "FD_kgfHttpOnly", "FD_kgfTlpOnly", "FD_kgfWholeBoth", "FD_kgfTrue", "FD_readersSwapped", "FD_readerShapes", "FD_diag", "FD_oldArt", "FD_noC1", "FD_noC2", "FD_noConcl", "FD_root", "FD_postRoot", "FD_output", "FD_refM", "FD_refC", "FD_ctxM", "FD_ctxC", "FD_design"] do
    diff37 s!"finalOffCombined2_Z vs {mu}" finN (mkApp2 (q mu) (C ``HftObCDZ) (C ``cdvZ)); nm := nm + 1
  for mu in ["FD_carrierY", "FD_carrierOld", "FD_obY"] do
    diff37 s!"finalOffCombined2_Z vs {mu}" finN (q mu); nm := nm + 1
  -- the older final statements are NOT the v2 one
  for (old, what) in [(`Tools.ShippingFGCircuitS2kFinal.synth_hftPcieOutByte_finalOffCombined_Z, "S2k combined"), (`Tools.ShippingFGCircuitS2hHist.synth_hftPcieOutByte_finalOffLNKH_Z, "S2h"),
      (`Tools.ShippingFGCircuitS2jTop.synth_hftPcieOutByte_finalOffLNKKGT_Z, "S2j"), (`Tools.ShippingFGCircuitS2gGates.synth_hftPcieOutByte_finalOffLNKKG_Z, "S2g"),
      (`Tools.ShippingFGCircuitS2dKids.synth_hftPcieOutByte_finalOffLNKK_Z, "S2d")] do
    diff37 s!"finalOffCombined2_Z vs the {what} statement" finN (← tyOf old); nm := nm + 1
  logInfo m!"FGCIRCUIT37 SIGNATURES-FINAL: the complete type of synth_hftPcieOutByte_finalOffCombined2_Z (19 explicit hypotheses, binder kinds at all depths) matches the independently written ExpFinal2 under ONE criterion (FGCircuitCmp.stmtEq: the same normal form, structural equality); the real type is normalised once; {nm} mutants rejected with the same criterion (another world / reference / environment / root / carrier / output / conclusion, every premise dropped, hfind as an extra hypothesis, the old hdec / hmiss, the profile lookup ON, reach from another world, the plain bundle, the older final statements)"
  logInfo m!"FGCIRCUIT37 NOTE: the gate facts are compared through Check27's ExpKGF/ExpHK, the seven premises through Check33's ExpD/ExpG/ExpT/ExpPS/ExpDown/ExpProfOff/ExpQuiet (their statements are shown equal to the real definitions in Check33 DEFS/HYPS); the old premises through Check30's ExpDec and Check28's kmissR"

/-! ## 2. HYPS, the reach walk and the proof term -/

partial def reach (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | some (.defnInfo d) =>
        if (`Tools).isPrefixOf n || (`Sparkle).isPrefixOf n then reach env (d.value.getUsedConstants.toList ++ d.type.getUsedConstants.toList ++ rest) seen
        else reach env rest seen
      | some (.inductInfo i) => if (`Tools).isPrefixOf n then reach env (i.ctors ++ rest) seen else reach env rest seen
      | some (.ctorInfo c) => reach env (c.type.getUsedConstants.toList ++ rest) seen
      | _ => reach env rest seen

def valueConsts (n : Name) : MetaM (Array Name) := do
  match (← getEnv).find? n with
  | some (.thmInfo t) => pure t.value.getUsedConstants
  | some (.defnInfo d) => pure d.value.getUsedConstants
  | _ => throwError "{n}: no value"

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let tF ← tyOf ``synth_hftPcieOutByte_finalOffCombined2_Z
  let some ty2 ← unfoldDefinition? tF | throwError "not a definition"
  let hs ← forallTelescope ty2 fun xs _ => do
    let mut hs : List (String × BinderInfo × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, d.binderInfo, ← instantiateMVars d.type)]
    return hs
  let expected := ["hlink", "L", "lvl", "env₀", "hstart", "hr", "hcell", "hchk", "hreadH", "hreadT", "hcd", "hadm", "hdown", "hD", "hG", "hT", "hs", "h0", "hkgfacts"]
  unless hs.map (·.1) == expected do throwError "hypotheses are {hs.map (·.1)}, expected {expected}"
  for gone in ["hfind", "hdec", "hmiss", "htop", "hkenv", "hkgates", "hkids", "hclL", "hcl", "hgate", "hnoraw", "hdRun", "hsrc", "hhead", "hcore"] do
    if (hs.map (·.1)).contains gone then throwError "{gone} is a hypothesis"
  let ty (n : String) : MetaM Lean.Expr := do
    let some (_, _, t) := hs.find? (·.1 == n) | throwError "{n} missing"
    pure t
  let needs : List (String × Name) := [("hadm", ``Tools.ShippingChildInvA.AdmCtx), ("hadm", ``quietR), ("hdown", ``AdmDownR), ("hD", ``DRowEnvR), ("hG", ``DiagEnvR), ("hT", ``TeleR),
    ("hs", ``ProfStepR), ("h0", ``ProfOffW), ("hkgfacts", ``HftKidsGateFacts), ("hreadH", ``Tools.ShippingFGCircuitCover.RootReader), ("hreadT", ``Tools.ShippingFGCircuitCover.RootReader)]
  for (n, c) in needs do
    unless (← ty n).getUsedConstants.contains c do throwError "{n} does not mention {c}"
  -- no premise mentions `hfind`'s statement, the old miss premise, or the all-world reflections
  for (n, _, t) in hs do
    for bad in [``MissE, ``Tools.ShippingFGCircuitS2dKids.KidStartEnv, ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv, ``Tools.ShippingMachineEntry.MachineDefines, ``HftCallDec] do
      if t.getUsedConstants.contains bad then throwError "{n} mentions {bad}"
  for (n, bi, _) in hs do
    unless bi.isExplicit do throwError "{n} is not explicit"
  let env ← getEnv
  let r := reach env [``DRowEnvR, ``DiagEnvR, ``TeleR, ``ProfStepR, ``ProfOffW, ``AdmDownR, ``quietR, ``HftKidsGateFacts] {}
  for bad in [``MissE, ``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingFGCircuitS2aClose.HftKidsDefine, ``Tools.ShippingMachineEntry.MachineCloses,
      ``Tools.ShippingFGCircuitS2dKids.KidStartEnv, ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv, ``Tools.ShippingGen2.Start, ``Tools.ShippingFGCircuitS1iEnv.CheckedStart,
      ``Tools.ShippingGen2.ShipsRes, ``Tools.ShippingGen2.ChildShips, ``Tools.ShippingGen2.TopShips, ``HftCallDec] do
    if r.contains bad then throwError "{bad} is reachable from the seven premises / the gate facts within the walk"
  for good in [``Tools.ShippingFGCircuitS1oHead.GetEnvProfileAt, ``Tools.ShippingGen5Env.ReadsAt, ``Reached, ``LeafStep, ``Tools.ShippingChildInvA.AdmCtx] do
    unless r.contains good do throwError "{good} is not reached from the seven premises"
  -- the proof term: where each named piece comes from
  let top ← valueConsts ``hftTop_of_runR
  for need in [``Tools.ShippingFGCircuitS2lDec.hftCallDec_of_checked, ``Tools.ShippingFGCircuitS1qHead.root_find_of_headAtOff, ``ropsR, ``missR, ``kid_shipsResW,
      ``Tools.ShippingFGCircuitS2kRun.soundX_served_E, ``Tools.ShippingFGCircuitS2hHist.hft_closesAtH, ``Tools.ShippingFGCircuitS2kRun.machineRunJQH_of_closesHOff] do
    unless top.contains need do throwError "hftTop_of_runR does not use {need}"
  for bad in [``Tools.ShippingFGCircuitS2kFinal.kid_shipsResE, ``Tools.ShippingFGCircuitS2kFinal.hftTop_of_runH, ``Tools.ShippingFGCircuitS2dKids.KidStartEnv, ``Tools.ShippingMachineEntry.MachineDefines] do
    if top.contains bad then throwError "hftTop_of_runR uses {bad}"
  let fin ← valueConsts ``synth_hftPcieOutByte_finalOffCombined2
  for need in [``hftTop_of_runR, ``Tools.ShippingFGCircuitS2mReach.hftCoreCloses_of_kidsR] do
    unless fin.contains need do throwError "the v2 wrapper does not use {need}"
  for bad in [``Tools.ShippingFGCircuitS2hHist.hftCoreCloses_of_kidsH, ``Tools.ShippingFGCircuitS2kFinal.hftTop_of_runH] do
    if fin.contains bad then throwError "the v2 wrapper uses {bad}"
  logInfo m!"FGCIRCUIT37 HYPS: synth_hftPcieOutByte_finalOffCombined2_Z = {expected} (19 explicit); hfind, hdec, hmiss, htop, hkenv, hkgates are NOT hypotheses; the seven premises mention AdmCtx/quietR, AdmDownR, DRowEnvR, DiagEnvR, TeleR, ProfStepR, ProfOffW and no premise mentions MissE / KidStartEnv / HftKidsStartEnv / MachineDefines / HftCallDec. REACH (a walk over the types and values of `defnInfo` under `Tools`/`Sparkle` and the constructors of `Tools` inductives; theorems are not unfolded): {r.size} constants from the seven premises and the gate facts, none of MissE / MachineDefines / HftKidsDefine / MachineCloses / KidStartEnv / Start / CheckedStart / ShipsRes / ChildShips / TopShips / HftCallDec. PROOF TERM: hftTop_of_runR uses hftCallDec_of_checked (hfind from the core run via root_find_of_headAtOff), ropsR/missR/kid_shipsResW/soundX_served_E (the served children are RealChildE of ropsR, the same history); the wrapper uses hftCoreCloses_of_kidsR, not hftCoreCloses_of_kidsH"

/-! ## 3. SIGNATURES-TOP, REMAINING, AXIOMS -/

run_cmd liftTermElabM do
  let t ← tyOf ``hftTop_of_runR
  let names := (← forallTelescope t fun xs _ => do
    let mut r : List String := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      r := r ++ [d.userName.toString]
    return r)
  let expected := ["ι", "mref", "cref", "L", "lvl", "env₀", "mctx", "cctx", "w", "b", "D'", "hstart", "hcell", "hchk", "hreadH", "hreadT", "hkgfacts", "hadm", "hdown", "hD", "hG", "hT", "hs", "h0"]
  unless names.take 24 == expected do throwError "hftTop_of_runR binders {names}, expected {expected}"
  let uses := t.getUsedConstants
  for bad in [``Tools.ShippingFGCircuitS2dKids.KidStartEnv, ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv, ``Tools.ShippingMachineEntry.MachineDefines, ``MissE, ``HftCallDec] do
    if uses.contains bad then throwError "hftTop_of_runR mentions {bad}"
  for need in [``AdmDownR, ``DRowEnvR, ``DiagEnvR, ``TeleR, ``ProfStepR, ``ProfOffW, ``HftKidsGateFacts, ``quietR] do
    unless uses.contains need do throwError "hftTop_of_runR does not mention {need}"
  logInfo m!"FGCIRCUIT37 SIGNATURES-TOP: hftTop_of_runR binders {names}: hmiss and hdec are gone; the seven premises of S2m are there; no hkenv / KidStartEnv / MissE / HftCallDec in the type"

run_cmd liftTermElabM do
  logInfo m!"FGCIRCUIT37 REMAINING (named hypotheses of the combined statement v2, none supplied): hadm [FG D.T-4m6] : AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx; hdown [D.T-4m7] : AdmDownR L.O (envAt cref w) w; hD [D.T-4m1] : DRowEnvR; hG [D.T-4m2] : DiagEnvR; hT [D.T-4m3] : TeleR; hs [D.T-4m4] : ProfStepR L.O w; h0 [D.T-4m5] : ProfOffW mref cref w (NOT one common shape: the quantifier ranges differ per premise, see §39/§42: hD/hG range over DRow/Diag rows, hT over Tele, hs over ProfStep, h0 over ProfOff at w, hadm/hdown are admissibility of the context / the lowering; only some of them quantify over worlds reached from the root's start world w); hkgfacts : HftKidsGateFacts (envAt cref w) [FG D.T-4g, 10 environment facts]; hlink : HftRootLink [S2c, conclusion part proved independently in S2kLink if it compiles]; hcd : Ob (envAt cref w) [S2b/S2i]; hreadH/hreadT : RootReader; hchk : CheckedStart; CellPrem; Laws / Start / hr. NOT hypotheses any more: hdec (hftCallDec_of_checked), hfind (root_find_of_headAtOff from the core run of hr and CellPrem), hmiss (derived: missR)"

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2rFinal
  let names : List Name := [X ++ `realChildA_weak, X ++ `jqc_weak, X ++ `kid_shipsResW, X ++ `hftTop_of_runR,
    X ++ `synth_hftPcieOutByte_finalOffCombined2, X ++ `synth_hftPcieOutByte_finalOffCombined2_Z, X ++ `synth_hftPcieOutByte_finalOffCombined2_Y, X ++ `synth_hftPcieOutByte_finalOffCombined2_X]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT37 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck37
