import Tools.ShippingGen5ReaderTraceAppCall
import Tools.ShippingGen5ReaderTraceLet
import Tools.ShippingGen5ReaderTraceChainLet
import Tools.ShippingGen5ReaderTraceChain
import Tools.ShippingGen5ReaderTraceInstS
import Tools.ShippingGen5ReaderTraceLoopRoot
import Tools.ShippingBundleIotaRange
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceDispatch, exit 0, 769 jobs) on the tree of this file's commit. Written against freeze rev5 U-R11 (no new premise). No sorry / axiom / native_decide in source.

/-! # DG-READERTRACE U-R11b: dispatch — `TraceGood senv nDecl (readF senv n)` for every fuel `n`

Assembles the arm lemmas U-R4a … U-R10 (`conv_basic_trace`, the `app` arms, `conv_letE_trace`, `nested_trace`, `inst_trace`, `instS_trace`, `chain_basic_trace`, `chain_letE_trace`,
`loopBody_trace`, `loopRoot_trace`) with `readF_traceGood_of_step`. No new premise: the named hypotheses are the existing `LiftAgrees`, `RootFloatAgrees`, `Inst1Agrees` (via `Inst1Ph`),
`SigTyPh` (from `EnvTypesFVarFree` and `SigTyClosed`), `InstSFieldsDet` (registered in `Tools/Assume/EnvInstS.lean`) and the record `PureFacts senv`.
Conditional (intermediate) result: it does not claim that any of these named hypotheses is true. Not supplied: R-in / R-nl / R-dom for the readF calls of `machineShapeF`, U-E3b `machineShapeF_reach`,
`ShapeInputs`, the real run, FG. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Tools.Assume.EnvInstS

theorem conv_app_trace (senv : StructEnv) (nDecl n : Nat) (hS : SigTyPh senv)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (f a : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d (.app f a) st))
    (v : (Call.conv env d (.app f a) st).Res)
    (hv : (convStep senv env d (.app f a) st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d (.app f a) st) v) ∧
    PhPost senv nDecl (Call.conv env d (.app f a) st) v := by
  rcases hreg : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs with _ | ⟨dom, α, init, x⟩
  · rcases hl : machLoopRead? env d (.app f a) with _ | i
    · rcases hrun : machRunApp? (.app f a) with _ | ⟨dom, αs, initsE, body⟩
      · rcases hic : machInstCall? senv (.app f a) with _ | ⟨c, kinds, res, args⟩
        · rcases hics : machInstCallS? senv (.app f a) with _ | ⟨c, kinds, ty, args⟩
          · rcases hmem : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e)
              (.app f a) with _ | ⟨combo, aw, dw, dom, ops⟩
            · rcases hr : machReadV env d (.app f a) with _ | i
              · exact conv_app_general_trace senv nDecl n hT env d f a st hpre hreg hl hrun hic hics hmem hr v hv
              · exact conv_app_readV_trace senv nDecl n env d f a st hpre hreg hl hrun hic hics hmem i hr v hv
            · exact conv_app_mem_trace senv nDecl n hT env d f a st hpre hreg hl hrun hic hics combo aw dw dom ops hmem v hv
          · exact conv_app_instS_trace senv nDecl n hS hT env d f a st hpre hreg hl hrun hic c kinds ty args hics v hv
        · exact conv_app_inst_trace senv nDecl n hT env d f a st hpre hreg hl hrun c kinds res args hic v hv
      · exact conv_app_nested_trace senv nDecl n hT env d f a st hpre hreg hl dom αs initsE body hrun v hv
    · exact conv_app_loopRead_trace senv nDecl n env d f a st hpre hreg i hl v hv
  · by_cases hg : (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = false
    · rcases hfind : st.bareRegs.find? (·.1 == Lean.Expr.app f a) with _ | ⟨e0, k⟩
      · exact conv_app_bareNew_trace senv nDecl n hT env d f a st hpre dom α init x hreg hg hfind v hv
      · exact conv_app_bareFound_trace senv nDecl n env d f a st hpre dom α init x hreg hg e0 k hfind v hv
    · exfalso
      have hg' : (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) = true := by
        revert hg
        cases (d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty) <;> simp
      simp [convStep, hreg, hg', failO, run_pure] at hv

theorem conv_trace (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees) (hS : SigTyPh senv)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.conv env d e st))
    (v : (Call.conv env d e st).Res)
    (hv : (convStep senv env d e st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.conv env d e st) v) ∧
    PhPost senv nDecl (Call.conv env d e st) v := by
  by_cases hb : ConvBasic e
  · exact conv_basic_trace senv nDecl n hT env d e st hb hpre v hv
  · cases e with
    | app f a => exact conv_app_trace senv nDecl n hS hT env d f a st hpre v hv
    | letE nm ty val body nd => exact conv_letE_trace senv nDecl n hla hrf hT env d nm ty val body nd st hpre v hv
    | _ => exact (hb trivial).elim

theorem chain_trace (senv : StructEnv) (nDecl n : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hT : TraceGood senv nDecl (readF senv n))
    (env : List MachVal) (e : Lean.Expr) (st : MachRead)
    (hpre : TracePre senv nDecl (Call.chain env e st))
    (v : (Call.chain env e st).Res)
    (hv : (chainStep senv env e st).run (readF senv n) = some (some v)) :
    FReachC nDecl st (callOut (Call.chain env e st) v) ∧
    PhPost senv nDecl (Call.chain env e st) v := by
  by_cases hb : ChainBasic e
  · exact chain_basic_trace senv nDecl n hT env e st hb hpre v hv
  · cases e with
    | letE nm ty val body nd => exact chain_letE_trace senv nDecl n hla hrf hT env nm ty val body nd st hpre v hv
    | _ => exact (hb trivial).elim

theorem step_trace (senv : StructEnv) (nDecl : Nat) (hla : LiftAgrees) (hrf : RootFloatAgrees) (hI : Inst1Ph)
    (hD : InstSFieldsDet senv) (hS : SigTyPh senv) (n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (c : Call) (hpre : TracePre senv nDecl c) (v : c.Res)
    (hv : (step senv c).run (readF senv n) = some (some v)) :
    FReachC nDecl (callSt c) (callOut c v) ∧ PhPost senv nDecl c v := by
  cases c with
  | conv env d e st => exact conv_trace senv nDecl n hla hrf hS hT env d e st hpre v hv
  | nested env dom αs initsE body st => exact nested_trace senv nDecl n hT env dom αs initsE body st hpre v hv
  | inst env c org kinds res args st => exact inst_trace senv nDecl n hT env c org kinds res args st hpre v hv
  | instS env c kinds ty args st => exact instS_trace senv nDecl n hI hD hT env c kinds ty args st hpre v hv
  | chain env e st => exact chain_trace senv nDecl n hla hrf hT env e st hpre v hv
  | loopBody base env e st => exact loopBody_trace senv nDecl n hT base env e st hpre v hv
  | loopRoot env e st => exact loopRoot_trace senv nDecl n hT env e st hpre v hv

theorem readF_traceGood (senv : StructEnv) (F : PureFacts senv) (nDecl : Nat) (hla : LiftAgrees)
    (hrf : RootFloatAgrees) (hI : Inst1Ph) (hD : InstSFieldsDet senv) (hS : SigTyPh senv) :
    ∀ n : Nat, TraceGood senv nDecl (readF senv n) :=
  readF_traceGood_of_step senv F nDecl (fun n hT c hpre v hv => step_trace senv nDecl hla hrf hI hD hS n hT c hpre v hv)

/-- The same, with the `PureFacts` record built from the existing named premises. -/
theorem readF_traceGood_of_premises (env : Lean.Environment) (hK : EnvTypesFVarFree env)
    (hC : Tools.Assume.EnvSigTy.SigTyClosed (structEnv env)) (hla : LiftAgrees) (hrf : RootFloatAgrees)
    (hi1 : Inst1Agrees) (hD : InstSFieldsDet (structEnv env)) (nDecl : Nat) :
    ∀ n : Nat, TraceGood (structEnv env) nDecl (readF (structEnv env) n) :=
  readF_traceGood (structEnv env)
    (pureFacts_of (rootFloatRange_of_agrees hrf) (liftRange_of_agrees hla) (inst1Range_of_agrees hi1)
      (sigTyRange_structEnv env hK) bundleIotaRange)
    nDecl hla hrf (inst1Ph_of_agrees hi1) hD (sigTyPh_of env hK hC)

end Tools.ShippingGen5ReaderTrace
