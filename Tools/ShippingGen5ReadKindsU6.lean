import Tools.Prototype.DGenProv
import Tools.ShippingGen5ReadKindsU5
import Tools.ShippingGen5RunReads
import Tools.ShippingEnvSnapshot
import Tools.ShippingEntryReadsLinked
set_option autoImplicit false
-- Built: kjob lake build Tests.Gen5.ReadKindsU6Check exit 0 (816 jobs) in pod on dc880c86e4f840e8b0dc5f61ced3550714445f45 (not a clean issue-linked build; that is the coder's). Freeze: scripts/gen5/DG_READKINDS_U6_FREEZE.md. No sorry / axiom / native_decide.

/-! # DG-READKINDS U6 (freeze scripts/gen5/DG_READKINDS_U6_FREEZE.md)

U6a `readMachine_rootFactsAt`, U6d `readMachine_root` (the walk of `Tools.Prototype.DGenProv.readMachine_run` repeated with the root body recorded),
U6b `readMachine_agrees_runReads` (CONDITIONAL on `GetEnvFrame`, `hw`, `declName = X`: intermediate, not a supply of `hentry`).
Not claimed: `hentry` unconditional, hq, reader coverage, a real-run tie, FG. -/
namespace Tools.ShippingGen5ReadKindsU6
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineCommand Tools.ShippingMachineEntry
open Tools.Prototype.DGenProv
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU5
open Tools.ShippingEntryReadsLinked (envAt getEnv_value getConstInfo_value)
open Tools.ShippingEnvSnapshot (GetEnvFrame envFrame_getConstInfo)
open Tools.ShippingChildInv

/-- What a `readMachine` run says about the root body it used. -/
def ReadRoot (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  ReadConcl ci env r ∧
  ∃ body : Lean.Expr, RootFactsTie (GenEntry ci env) body ∧
    r.rootLets = (machRoot (structEnv env).proj body []).1.length ∧
    r.sel? = (machRoot (structEnv env).proj body []).2.1 ∧
    r.hasOuter = (machRoot (structEnv env).proj body []).2.2.1.isSome

set_option hygiene false in
/-- the part of the `readMachine` walk after the outputs are read -/
local macro "tail4R" : tactic => `(tactic| (
  have_open h as kinds hx_kinds
  have_open h as c hx_c
  have_open h as idx hx_idx
  have_open h as bposL hx_bposL
  have_open h as vposL hx_vposL
  have_open h as vwL hx_vwL
  generalize hu : unq c shape.body = o at h
  rcases o with _ | whole
  · dsimp (config := {zeta := false}) only at h
    exact (throwError_not_runs _ h).elim
  dsimp (config := {zeta := false}) only at h
  rcases whole with ⟨_ | W, whole⟩
  · dsimp (config := {zeta := false}) only at h
    exact (throwError_not_runs _ h).elim
  dsimp (config := {zeta := false}) only at h
  generalize hl : splitLets nLets ⟨W, whole⟩ = o at h
  rcases o with _ | ⟨letFs, core⟩
  · dsimp (config := {zeta := false}) only at h
    exact (throwError_not_runs _ h).elim
  dsimp (config := {zeta := false}) only at h
  have_open h as nOuts hx_nOuts
  generalize hf : splitFields (nOuts + nSlots) core = o at h
  rcases o with _ | fs
  · dsimp (config := {zeta := false}) only at h
    exact (throwError_not_runs _ h).elim
  dsimp (config := {zeta := false}) only at h
  have_open h as typed hx_typed
  obtain ⟨ls, _, h1, h⟩ := RunsTo.bind h
  clear h1
  obtain ⟨outs, _, h1, h⟩ := RunsTo.bind h
  clear h1
  obtain ⟨nexts, _, h1, h⟩ := RunsTo.bind h
  clear h1
  have_open h as packed hx_packed
  have_open h as q hx_q
  have_open h as jp5 hj5
  have H5 : ∀ (a : Unit) w r w', RunsTo (jp5 a) mctx mref cctx cref w r w' →
      ReadRoot ci env r := by
    intro a w r w' h
    subst hj5
    have hpr := RunsTo.pure_eq h
    subst hpr
    exact ⟨⟨rfl, hs⟩, eb, ⟨entryV, bsIn, entryBody, hv, hp, hx_eb⟩, by rw [hm], by rw [hm], by rw [hm]⟩
  rcases runs_dcases h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
    exact (throwError_not_runs _ h1).elim
  · exact H5 _ _ _ _ h))

theorem readMachine_root {declName : Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w') :
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ReadRoot ci env r := by
  unfold readMachine at h
  obtain ⟨env, w1, he, h⟩ := RunsTo.bind h
  obtain ⟨ci, w2, hc, h⟩ := RunsTo.bind h
  refine ⟨ci, env, w1, w2, he, hc, ?_⟩
  have_open h as jp0 hj0
  have H0 : ∀ a w r w', RunsTo (jp0 a) mctx mref cctx cref w r w' → ReadRoot ci env r := by
    intro a w r w' h
    subst hj0
    have_open h as senv hse
    subst hse
    have_open h as entry hen
    subst hen
    rcases runs_dcases h with ⟨_, h⟩ | ⟨_, h⟩
    case inr =>
      obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ h1).elim
    generalize hs : machineShape? false [] (entryConst true false [] ci (instancePredicate env)
      (userInliner env) (structEnv env)) (structEnv env) = o at h
    rcases o with _ | shape
    · dsimp (config := {zeta := false}) only at h
      exact (throwError_not_runs _ h).elim
    dsimp (config := {zeta := false}) only at h
    generalize hv : (entryConst true false [] ci (instancePredicate env)
      (userInliner env) (structEnv env)).value? = o at h
    rcases o with _ | entryV
    · dsimp (config := {zeta := false}) only at h
      exact (throwError_not_runs _ h).elim
    dsimp (config := {zeta := false}) only at h
    generalize hp : mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = o at h
    rcases o with _ | ⟨bsIn, entryBody⟩
    · dsimp (config := {zeta := false}) only at h
      exact (throwError_not_runs _ h).elim
    dsimp (config := {zeta := false}) only at h
    have_open h as eb hx_eb
    have_open h as nDecl hx_nDecl
    have_open h as nIn hx_nIn
    have_open h as nSlots hx_nSlots
    have_open h as nLets hx_nLets
    have_open h as binders hx_binders
    have_open h as jp2 hj2
    have H2 : ∀ (a : Unit) w r w', RunsTo (jp2 a) mctx mref cctx cref w r w' →
        ReadRoot ci env r := by
      intro a w r w' h
      subst hj2
      generalize hm : machRoot (structEnv env).proj eb [] = o at h
      rcases o with ⟨rootLets, sel?, run?, snd⟩
      dsimp (config := {zeta := false}) only at h
      have_open h as jp3 hj3
      have H3 : ∀ (a : Lean.Expr × Nat) w r w', RunsTo (jp3 a) mctx mref cctx cref w r w' →
          ReadRoot ci env r := by
        intro a w r w' h
        subst hj3
        rcases a with ⟨srcDom, depth⟩
        dsimp (config := {zeta := false}) only at h
        have_open h as jp4 hj4
        have H4 : ∀ (a : Lean.Expr) w r w', RunsTo (jp4 a) mctx mref cctx cref w r w' →
            ReadRoot ci env r := by
          intro a w r w' h
          subst hj4
          dsimp (config := {zeta := false}) only at h
          generalize hd : machDom? (shape.insts.length + nSlots + nLets) a = o at h
          rcases o with _ | ⟨dom, snd⟩
          · dsimp (config := {zeta := false}) only at h
            exact (throwError_not_runs _ h).elim
          dsimp (config := {zeta := false}) only at h
          have_open h as tup? hx_tupq
          rcases tup? with _ | ks
          · dsimp (config := {zeta := false}) only at h
            generalize hk : machOuts? (structEnv env) (entryConst true false [] ci
              (instancePredicate env) (userInliner env) (structEnv env)).type = o at h
            rcases o with _ | ⟨ctor?, outKinds⟩
            · dsimp (config := {zeta := false}) only at h
              exact (throwError_not_runs _ h).elim
            dsimp (config := {zeta := false}) only at h
            tail4R
          · dsimp (config := {zeta := false}) only at h
            tail4R
        cases srcDom
        case bvar j =>
          dsimp (config := {zeta := false}) only at h
          refine (RunsTo.ite h).elim (fun h => ?_) (fun h => ?_)
          · obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
            exact (throwError_not_runs _ h1).elim
          · obtain ⟨x, w1, h1, h⟩ := RunsTo.bind h
            have hx := RunsTo.pure_eq h1
            subst hx
            exact H4 _ _ _ _ h
        all_goals
          dsimp (config := {zeta := false}) only at h
          obtain ⟨x, w1, h1, h⟩ := RunsTo.bind h
          have hx := RunsTo.pure_eq h1
          subst hx
          exact H4 _ _ _ _ h
      rcases run? with _ | run
      · dsimp (config := {zeta := false}) only at h
        generalize hfd : Expr.find? (fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8) eb = o at h
        rcases o with _ | run
        · dsimp (config := {zeta := false}) only at h
          generalize hll : readMachine.loopLet 0 eb = o at h
          rcases o with _ | rr
          · dsimp (config := {zeta := false}) only at h
            generalize hrd : readMachine.resDom (structEnv env) (entryConst true false [] ci
              (instancePredicate env) (userInliner env) (structEnv env)).type 0 = o at h
            rcases o with _ | rr
            · dsimp (config := {zeta := false}) only at h
              obtain ⟨x, w1, h1, h⟩ := RunsTo.bind h
              exact (throwError_not_runs _ h1).elim
            · dsimp (config := {zeta := false}) only at h
              obtain ⟨x, w1, h1, h⟩ := RunsTo.bind h
              have hx := RunsTo.pure_eq h1
              subst hx
              exact H3 _ _ _ _ h
          · dsimp (config := {zeta := false}) only at h
            obtain ⟨x, w1, h1, h⟩ := RunsTo.bind h
            have hx := RunsTo.pure_eq h1
            subst hx
            exact H3 _ _ _ _ h
        · dsimp (config := {zeta := false}) only at h
          obtain ⟨x, w1, h1, h⟩ := RunsTo.bind h
          have hx := RunsTo.pure_eq h1
          subst hx
          exact H3 _ _ _ _ h
      · dsimp (config := {zeta := false}) only at h
        obtain ⟨x, w1, h1, h⟩ := RunsTo.bind h
        have hx := RunsTo.pure_eq h1
        subst hx
        exact H3 _ _ _ _ h
    rcases runs_dcases h with ⟨_, h⟩ | ⟨_, h⟩
    · obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ h1).elim
    · exact H2 _ _ _ _ h
  rcases runs_dcases h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
    exact (throwError_not_runs _ h1).elim
  · exact H0 _ _ _ _ h



theorem readMachine_rootFactsAt {declName : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w') :
    RootFactsAt r.entry := by
  obtain ⟨ci, env, w1, w2, he, hc, hent, hsh⟩ := readMachine_run hrun
  rw [hent]
  exact rootFactsAt_of_machineShape hsh

theorem readMachine_agrees_runReads {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {w1 w2 w3 w5 : Void IO.RealWorld} {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment}
    {shape : MachineShape}
    (hget : RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2)
    (henv : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3)
    (henv' : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5)
    (hshape : machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR)
      (structEnv envR)) (structEnv envR') = some shape)
    (hX : declName = X) (hg : GetEnvFrame mctx mref cctx cref) (hw : envAt cref w = envAt cref w1) :
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape := by
  subst hX
  obtain ⟨ci', env, v1, v2, he, hc, hent, hsh⟩ := readMachine_run hrun
  have e1 : env = envAt cref w := getEnv_value he
  have e2 : envAt cref v1 = envAt cref w := hg w env v1 he
  have e3 : (envAt cref v1).find? declName = some ci' := getConstInfo_value hc
  have e4 : (envAt cref w1).find? declName = some ci := getConstInfo_value hget
  have eR : envR = envAt cref w2 := getEnv_value henv
  have eR' : envR' = envAt cref w3 := getEnv_value henv'
  have f1 : envAt cref w2 = envAt cref w1 := envFrame_getConstInfo declName hg w1 ci w2 hget
  have f2 : envAt cref w3 = envAt cref w2 := hg w2 envR w3 henv
  have hE : env = envR := e1.trans (hw.trans (f1.symm.trans eR.symm))
  have hE' : envR' = envR := eR'.trans (f2.trans eR.symm)
  have hci : ci' = ci := by
    rw [e2, hw] at e3
    exact Option.some.inj (e3.symm.trans e4)
  subst hci hE hE'
  refine ⟨hent, ?_⟩
  have := hsh.symm.trans hshape
  exact Option.some.inj this

end Tools.ShippingGen5ReadKindsU6
