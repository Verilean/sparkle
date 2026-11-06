import Tools.ShippingFGCircuitS2kFinal
import Tests.Gen5.FGCircuitPilotCheck28
import Tests.Gen5.FGCircuitPilotCheck27
import Tests.Gen5.FGCircuitPilotCheck30
import Tests.Gen5.FGCircuitCmp
set_option autoImplicit false
-- FG circuit pilot S2k check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §37.

/-! # FGCircuitPilotCheck31 (light: each part is a small `run_cmd`; every real type is normalised once)

The COMBINED final statement `HftFinalStmtOffCombined` (hmiss of S2h instead of hkenv, hkgfacts of S2g instead of hkgates, hdec of S2j instead of htop).

1. SIGNATURES-TOP: `hftTop_of_runH` (complete type; the children premise is the miss premise on the history).
2. SIGNATURES-FINAL: `synth_hftPcieOutByte_finalOffCombined_Z` against an independently written COMPLETE expected type (binder kinds too), with negative controls: the facts / miss / decoding environment moved to the end world, to `env₀`, or to an independent world; swapped child names / quotes; a changed Off entry, carrier, output, conclusion; every knob of the three named hypotheses.
3. HYPS: the binder list, and the reach walk (it walks the types and values of `defnInfo` under `Tools`/`Sparkle` and the constructors of `Tools` inductives; it does not unfold theorems).
4. REMAINING, AXIOMS. WHENEVER the final wrapper changes, this check must be updated in the same commit. -/
namespace Tests.Gen5.FGCircuitPilotCheck31
open Lean Meta Elab Command Term
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingFGCircuitS2hHist (MissE JQH EQH CacheE KidEv)
open Tools.ShippingFGCircuitS2kFinal
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
open Tests.Gen5.FGCircuitPilotCheck26 (W Cx Cc Rf1 Rf2 Mod ZS ZE idF NmRoot NmHttp NmTlp ShE RootData HttpData TlpData Pre EntryOf iteStep binderInfos ExpKidsEnv kgReal)
open Tests.Gen5.FGCircuitPilotCheck28 (kmissR kmissNoDepth kmissNoMiss kmissNoHist kmissOnHit kmissOtherCtx kmissOnlyReads kmissOnlyProf kmissEq kmissTrue)

/-- environment knobs: the environment is `envAt cref w`, `envAt cref w'`, `env₀`, or an independent world's -/
abbrev EnvK := Rf2 → W → W → Environment → Environment
def eS : EnvK := fun cref w _ _ => envAt cref w
def eE : EnvK := fun cref _ w' _ => envAt cref w'
def e0 : EnvK := fun _ _ _ env₀ => env₀

/-- **`HftFinalStmtOffCombined`, written again.** Knobs (each mutant turns one): the entry (`diag`), the carrier of the artifact (`oldArt`), which premises are present, the three named hypotheses `dec`/`miss`/`kgf` and the environments they are stated at
(`dE`, `mE`, `gE`), the readers' names and data, the root / post root / output shape, the environment of `hcd` and of the conclusion, the reference / context / design the post run is stated at, and which conjunct of the conclusion is present. -/
def ExpFinalComb (Ob : Environment → Prop) (CV : CDRel) (dec : ∀ {ι : Type}, (Lean.Expr → Nat) → Environment → Prop)
    (miss : ∀ {mref : Rf1} {cref : Rf2}, RefLawsAOps MkRefd mref cref → Environment → Prop) (kgf : Environment → Prop)
    (diag oldArt needHcd needDec needMiss needKgf c1 c2 : Bool)
    (hE dE mE gE : EnvK) (hn tn : Name) (hd td : MachineData) (root postRoot : Name) (sh : SigShape) (cE : EnvK)
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
    Pre needDec (dec (ι := ι) lvl (dE cref w w' env₀)) (
    Pre needMiss (miss L.O (mE cref w w' env₀)) (
    Pre needKgf (kgf (gE cref w w' env₀)) (
    (if c1 then (∃ raw, PostRunOff (fM mctx) (fR mref) (fC cctx) (fF cref) w postRoot (fD D') b raw) else True) ∧
    (if c2 then (∃ (mm : MonoTy sh) (p : Pkg ι (fun _ => defaultDomain)),
      (if oldArt then RootArtifactMono (cE cref w w' env₀) (GPt (ι := ι) lvl (cE cref w w' env₀)) (PostRunOff (fM mctx) (fR mref) (fC cctx) (fF cref) w postRoot (fD D')) NmRoot sh mm b (fD D') p
       else RootArtifactMonoV CV (cE cref w w' env₀) (GPt (ι := ι) lvl (cE cref w w' env₀)) (PostRunOff (fM mctx) (fR mref) (fC cctx) (fF cref) w postRoot (fD D')) NmRoot sh mm b (fD D') p)) else True)))))

open Tests.Gen5.FGCircuitPilotCheck30 (ExpDec MuDecFixed MuDecZero MuDecOtherRoot MuDecNoPkg)
open Tests.Gen5.FGCircuitPilotCheck27 (ExpHK MuSwap MuSwapName MuHttpTwice MuTlpTwice MuHttpOnly MuTlpOnly MuWholeBoth MuTrue)

def decTrue {ι : Type} (_ : Lean.Expr → Nat) (_ : Environment) : Prop := True

/-- the REAL statement, with every knob at its real value -/
def FC (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
-- the decoding premise
def FC_decFixed (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @MuDecFixed kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_decZero (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @MuDecZero kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_decOtherRoot (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @MuDecOtherRoot kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_decNoPkg (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @MuDecNoPkg kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_decTrue (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @decTrue kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_decEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eE eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_decEnv0 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS e0 eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_decIndep (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : W}, ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS (fun cref _ _ _ => envAt cref a) eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_NoDec (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true false true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
-- the miss premise (children of the run)
def FC_missNoDepth (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissNoDepth ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_missNoMiss (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissNoMiss ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_missNoHist (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissNoHist ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_missOnHit (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissOnHit ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_missOtherCtx (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissOtherCtx ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_missOnlyReads (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissOnlyReads ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_missOnlyProf (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissOnlyProf ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_missEq (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissEq ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_missTrue (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissTrue ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_OldKenv (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec ExpKidsEnv ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_missEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eE eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_missEnv0 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS e0 eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_missIndep (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : W}, ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS (fun cref _ _ _ => envAt cref a) eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_NoMiss (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true false true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
-- the gate facts (the two called declarations)
def FC_kgfSwap (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR MuSwap false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_kgfSwapName (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR MuSwapName false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_kgfHttpTwice (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR MuHttpTwice false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_kgfTlpTwice (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR MuTlpTwice false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_kgfHttpOnly (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR MuHttpOnly false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_kgfTlpOnly (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR MuTlpOnly false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_kgfWhole (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR MuWholeBoth false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_kgfTrue (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR MuTrue false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_kgfGates (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR kgReal false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_kgfEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eE NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_kgfEnv0 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS e0 NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_kgfIndep (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : W}, ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS (fun cref _ _ _ => envAt cref a) NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_NoKgf (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true false true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
-- the other premises, the readers, the entry, the conclusion
def FC_ReadersSwapped (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmTlp NmHttp TlpData HttpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_ReaderShapes (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp TlpData HttpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_Diag (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK true false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_OldArt (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false true true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_NoHcd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false false true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_NoC1 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true false true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_NoC2 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true false eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_NoConcl (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true false false eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_Root (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmHttp NmRoot ShE eS idF idF idF idF idF
def FC_PostRoot (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmHttp ShE eS idF idF idF idF idF
def FC_Output (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot { ShE with res := .one (.bits 16) } eS idF idF idF idF idF
def FC_HcdEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eE eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF idF
def FC_ConclEnd (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eE idF idF idF idF idF
def FC_ConclEnv0 (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE e0 idF idF idF idF idF
def FC_RefM (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Rf1}, ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF (fun _ => a) idF idF idF
def FC_RefC (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Rf2}, ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF (fun _ => a) idF
def FC_CtxM (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Cx}, ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS (fun _ => a) idF idF idF idF
def FC_CtxC (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Cc}, ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF (fun _ => a) idF idF
def FC_Design (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {a : Design}, ExpFinalComb Ob CV @ExpDec kmissR ExpHK false false true true true true true true eS eS eS eS NmHttp NmTlp HttpData TlpData NmRoot NmRoot ShE eS idF idF idF idF (fun _ => a)
def FC_CarrierY : Prop := FC HftObCDZ cdvY
def FC_CarrierOld : Prop := FC HftObCDZ cdvOld
def FC_ObY : Prop := FC Tools.ShippingFGCircuitS1rCD.HftObCDY cdvZ

/-! ## the comparison: the real type is normalised ONCE; every statement (expected and mutants) is compared at the same transparency -/

def normOnce4 (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    let e := e.headBeta
    if let some e' := iteStep e then return .visit e'
    if let .const c _ := e.getAppFn then
      if c == ``HftFinalStmtOffCombined || c == ``HftCallDec || c == ``MissE || c == ``JQH || c == ``EQH || c == ``CacheE || c == ``KidEv ||
          c == ``HftKidsGateFacts || c == ``Tools.ShippingFGCircuitS2dKids.HftKidsGates || c == ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv ||
          c == ``Tools.ShippingFGCircuitS1tFinal.HftObTopCoreOff ||
          (`Tests.Gen5.FGCircuitPilotCheck31).isPrefixOf c || (`Tests.Gen5.FGCircuitPilotCheck30).isPrefixOf c || (`Tests.Gen5.FGCircuitPilotCheck28).isPrefixOf c ||
          (`Tests.Gen5.FGCircuitPilotCheck27).isPrefixOf c || (`Tests.Gen5.FGCircuitPilotCheck26).isPrefixOf c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)
def norm4 (e : Lean.Expr) : MetaM Lean.Expr := do
  let mut e := e
  for _ in [0:8] do
    e ← normOnce4 e
  -- `ExpKGF` was shown (Check27 SIGNATURES-A) to have the constructor type of `KidGateFacts`; here it is read as that structure
  Tests.Gen5.FGCircuitCmp.normCommon (e.replace fun x => if x.isConstOf `Tests.Gen5.FGCircuitPilotCheck27.ExpKGF then some (mkConst `Tools.ShippingFGCircuitS2gGates.KidGateFacts) else none)
def tyOf (n : Name) : MetaM Lean.Expr := do
  let ci ← getConstInfo n
  unless ci.levelParams.isEmpty do throwError "{n}: level parameters"
  pure ci.type
/-- `a` is the normal form of a real type (once); ONE criterion (`FGCircuitCmp.stmtEq`) for the expected statement and for every mutant, both normalised by `norm4` -/
def same4 (what : String) (a exp : Lean.Expr) : MetaM Unit := do
  Tests.Gen5.FGCircuitCmp.checkSame what a (← norm4 exp)
def diff4 (what : String) (a exp : Lean.Expr) : MetaM Unit := do
  Tests.Gen5.FGCircuitCmp.checkDiff what a (← norm4 exp)

/-! ## 1. `hftTop_of_runH` -/

open Tools.ShippingFGCircuitS1tFinal (HftObTopCoreOff)

set_option maxHeartbeats 32000000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := Lean.mkConst n
  let t ← tyOf ``hftTop_of_runH
  let a ← norm4 t
  let _ := C
  -- the real binder list of hftTop_of_runH
  let names := (← forallTelescope t fun xs _ => do
    let mut r : List String := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      r := r ++ [d.userName.toString]
    return r)
  let expected := ["ι", "mref", "cref", "L", "lvl", "env₀", "mctx", "cctx", "w", "b", "D'", "hstart", "hcell", "hchk", "hreadH", "hreadT", "hmiss", "hkgfacts", "hdec"]
  unless names.take 19 == expected do throwError "hftTop_of_runH binders {names}, expected {expected}"
  logInfo m!"FGCIRCUIT31 SIGNATURES-TOP: hftTop_of_runH binders {names} (19 incl. implicit): hkenv is replaced by hmiss, kgfacts and hdec as in the final statement; no hkenv / KidStartEnv"
  let uses := t.getUsedConstants
  for bad in [``Tools.ShippingFGCircuitS2dKids.KidStartEnv, ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv, ``Tools.ShippingMachineEntry.MachineDefines] do
    if uses.contains bad then throwError "hftTop_of_runH mentions {bad}"
  for need in [``MissE, ``KidEv, ``HftKidsGateFacts, ``HftCallDec, ``HftObTopCoreOff] do
    unless uses.contains need do throwError "hftTop_of_runH does not mention {need}"
  let _ := a

/-! ## 2. the combined final statement -/

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := Lean.mkConst n
  let Q := `Tests.Gen5.FGCircuitPilotCheck31
  let q (n : String) : Lean.Expr := Lean.mkConst (Q ++ Name.mkSimple n)
  let finN ← norm4 (← tyOf ``synth_hftPcieOutByte_finalOffCombined_Z)
  same4 "synth_hftPcieOutByte_finalOffCombined_Z" finN (mkApp2 (q "FC") (C ``HftObCDZ) (C ``cdvZ))
  let mut nm : Nat := 0
  for mu in ["FC_decFixed", "FC_decZero", "FC_decOtherRoot", "FC_decNoPkg", "FC_decTrue", "FC_decEnd", "FC_decEnv0", "FC_decIndep", "FC_NoDec",
      "FC_missNoDepth", "FC_missNoMiss", "FC_missNoHist", "FC_missOnHit", "FC_missOtherCtx", "FC_missOnlyReads", "FC_missOnlyProf", "FC_missEq", "FC_missTrue", "FC_OldKenv",
      "FC_missEnd", "FC_missEnv0", "FC_missIndep", "FC_NoMiss",
      "FC_kgfSwap", "FC_kgfSwapName", "FC_kgfHttpTwice", "FC_kgfTlpTwice", "FC_kgfHttpOnly", "FC_kgfTlpOnly", "FC_kgfWhole", "FC_kgfTrue", "FC_kgfGates",
      "FC_kgfEnd", "FC_kgfEnv0", "FC_kgfIndep", "FC_NoKgf",
      "FC_ReadersSwapped", "FC_ReaderShapes", "FC_Diag", "FC_OldArt", "FC_NoHcd", "FC_NoC1", "FC_NoC2", "FC_NoConcl", "FC_Root", "FC_PostRoot", "FC_Output",
      "FC_HcdEnd", "FC_ConclEnd", "FC_ConclEnv0", "FC_RefM", "FC_RefC", "FC_CtxM", "FC_CtxC", "FC_Design"] do
    diff4 s!"finalOffCombined_Z vs {mu}" finN (mkApp2 (q mu) (C ``HftObCDZ) (C ``cdvZ)); nm := nm + 1
  for mu in ["FC_CarrierY", "FC_CarrierOld", "FC_ObY"] do
    diff4 s!"finalOffCombined_Z vs {mu}" finN (q mu); nm := nm + 1
  -- the older final statements are NOT the combined one
  for (old, what) in [(`Tools.ShippingFGCircuitS2hHist.synth_hftPcieOutByte_finalOffLNKH_Z, "S2h"), (`Tools.ShippingFGCircuitS2jTop.synth_hftPcieOutByte_finalOffLNKKGT_Z, "S2j"),
      (`Tools.ShippingFGCircuitS2gGates.synth_hftPcieOutByte_finalOffLNKKG_Z, "S2g"), (`Tools.ShippingFGCircuitS2dKids.synth_hftPcieOutByte_finalOffLNKK_Z, "S2d")] do
    diff4 s!"finalOffCombined_Z vs the {what} statement" finN (← tyOf old); nm := nm + 1
  logInfo m!"FGCIRCUIT31 SIGNATURES-FINAL: the complete type of synth_hftPcieOutByte_finalOffCombined_Z (14 explicit hypotheses, binder kinds too) matches the independently written ExpFinalComb at its real knobs; the real type is normalised once and every statement is compared at the default transparency for the expected statement and reducible for the mutants (as Check26/28); {nm} mutants rejected: hdec (a fixed callee, call index 0, another root, package not required, True, at the end world / env₀ / an independent world, dropped), hmiss (each knob of MissE, the old universal hkenv, only reads / only profile / equality / True evidence, at the end world / env₀ / an independent world, dropped), hkgfacts (swapped by quote, swapped by name, a callee twice, one callee only, the whole-value points, True, the old EntryGates (hkgates), at the end world / env₀ / an independent world, dropped), swapped / shape-swapped readers, the diagnostic entry, the old artifact, a premise or conjunct missing, another root / post root / output, hcd or the conclusion at the end world / env₀, another reference / context / design, another carrier / obligation, and the S2h / S2j / S2g / S2d statements"
  logInfo m!"FGCIRCUIT31 NOTE: the facts of hkgfacts are compared through Check27's ExpKGF/ExpHK (their constructor types are shown equal to KidGateFacts in Check27 SIGNATURES-A); hdec through Check30's ExpDec; hmiss through Check28's kmissR (ExpMiss over ExpEv)"

/-! ## 3. HYPS and the reach walk -/

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

set_option maxHeartbeats 8000000 in
run_cmd liftTermElabM do
  let tF ← tyOf ``synth_hftPcieOutByte_finalOffCombined_Z
  let some ty2 ← unfoldDefinition? tF | throwError "not a definition"
  let hs ← forallTelescope ty2 fun xs _ => do
    let mut hs : List (String × BinderInfo × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, d.binderInfo, ← instantiateMVars d.type)]
    return hs
  let expected := ["hlink", "L", "lvl", "env₀", "hstart", "hr", "hcell", "hchk", "hreadH", "hreadT", "hcd", "hdec", "hmiss", "hkgfacts"]
  unless hs.map (·.1) == expected do throwError "hypotheses are {hs.map (·.1)}, expected {expected}"
  for gone in ["htop", "hkenv", "hkgates", "hkids", "hclL", "hcl", "hgate", "hnoraw", "hdRun", "hsrc", "hhead"] do
    if (hs.map (·.1)).contains gone then throwError "{gone} is a hypothesis"
  let ty (n : String) : MetaM Lean.Expr := do
    let some (_, _, t) := hs.find? (·.1 == n) | throwError "{n} missing"
    pure t
  unless (← ty "hmiss").getUsedConstants.contains ``MissE do throwError "hmiss is not MissE"
  unless (← ty "hkgfacts").getUsedConstants.contains ``HftKidsGateFacts do throwError "hkgfacts is not HftKidsGateFacts"
  unless (← ty "hdec").getUsedConstants.contains ``HftCallDec do throwError "hdec is not HftCallDec"
  for n in ["hreadH", "hreadT"] do
    unless (← ty n).getUsedConstants.contains ``Tools.ShippingFGCircuitCover.RootReader do throwError "{n} is not a RootReader"
  let env ← getEnv
  let r := reach env [``MissE, ``KidEv, ``HftKidsGateFacts, ``HftCallDec] {}
  for bad in [``Tools.ShippingMachineEntry.MachineDefines, ``Tools.ShippingFGCircuitS2aClose.HftKidsDefine, ``Tools.ShippingMachineEntry.MachineCloses,
      ``Tools.ShippingFGCircuitS2dKids.KidStartEnv, ``Tools.ShippingFGCircuitS2dKids.HftKidsStartEnv, ``Tools.ShippingGen2.Start, ``Tools.ShippingFGCircuitS1iEnv.CheckedStart,
      ``Tools.ShippingGen2.ShipsRes, ``Tools.ShippingGen2.ChildShips, ``Tools.ShippingGen2.TopShips] do
    if r.contains bad then throwError "{bad} is reachable from hmiss / hkgfacts / hdec within the walk"
  for good in [``Tools.ShippingFGCircuitS1oHead.GetEnvProfileAt, ``Tools.ShippingGen5Env.ReadsAt, ``Tools.ShippingFGCircuitS2hHist.RealChildE, ``JQH, ``Tools.ShippingGen2.CallDec, ``instancePredicate, ``userInliner] do
    unless r.contains good do throwError "{good} is not reached from hmiss / hkgfacts / hdec"
  -- the explicit binders of the three hypotheses are the only changes: kinds are explicit
  for (n, bi, _) in hs do
    unless bi.isExplicit do throwError "{n} is not explicit"
  logInfo m!"FGCIRCUIT31 HYPS: synth_hftPcieOutByte_finalOffCombined_Z = {expected} (14 explicit); hkenv, hkgates and htop are all gone; hmiss (MissE over KidEv), hkgfacts (HftKidsGateFacts) and hdec (HftCallDec) are in their places. REACH (a walk over the types and values of defnInfo under Tools/Sparkle and the constructors of Tools inductives; it does NOT unfold theorems and says nothing about the whole dependency closure): none of MachineDefines / HftKidsDefine / MachineCloses / KidStartEnv / HftKidsStartEnv / Start / CheckedStart / ShipsRes / ChildShips / TopShips is reached from the three hypotheses (reach set {r.size})"

/-! ## 4. REMAINING, AXIOMS -/

run_cmd liftTermElabM do
  logInfo m!"FGCIRCUIT31 REMAINING (named hypotheses of the combined statement): hmiss : MissE L.O (KidEv mref cref (envAt cref w)) [FG D.T-4h]; hkgfacts : HftKidsGateFacts (envAt cref w) [FG D.T-4g, 10 environment facts]; hdec : HftCallDec lvl (envAt cref w) [FG D.D-4 G-CALLDEC]. Also unchanged: hlink (S2c), hcd (S2b/S2i), hreadH/hreadT, hchk, CellPrem, Laws/Start/hr. hkenv (the universal KidStartEnv), hkgates and htop are no longer hypotheses."

run_cmd liftTermElabM do
  let X := `Tools.ShippingFGCircuitS2kFinal
  let R := `Tools.ShippingFGCircuitS2kRun
  let names : List Name := [R ++ `synthesizeFromConst_machine_invH, R ++ `machine_run_of_coreHOff, R ++ `machineRunJQH_of_closesHOff, R ++ `synthesizeMachineCertified_runsH, R ++ `soundX_served_E,
    R ++ `MachineRunJQH.toC, X ++ `servedP_mono, X ++ `kid_shipsResE, X ++ `hftTop_of_runH,
    X ++ `synth_hftPcieOutByte_finalOffCombined, X ++ `synth_hftPcieOutByte_finalOffCombined_Z, X ++ `synth_hftPcieOutByte_finalOffCombined_Y, X ++ `synth_hftPcieOutByte_finalOffCombined_X]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT31 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

end Tests.Gen5.FGCircuitPilotCheck31
