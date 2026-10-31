import Tools.Prototype.DGenProv
import Tools.ShippingGen5ReadKindsU5
import Tools.ShippingGen5ReadKindsU6
import Tools.ShippingGen5Env
set_option autoImplicit false
-- Built: kjob lake build Tests.Gen5.ReadKindsU7Check exit 0 in pod on 31717003b3a3d933585ee1222fdbbeeaa331f9d4 (not a clean issue-linked build; that is the coder's). Freeze: (U7 freeze scripts/gen5/DG_READKINDS_U7_FREEZE.md). No sorry / axiom / native_decide.

/-! # DG-READKINDS U7 (freeze scripts/gen5/DG_READKINDS_U7_FREEZE.md)

U7a `readMachine_fields` (the `readMachine_run` walk repeated, recording the guard / assignment facts for the remaining `Read` fields),
U7b `readMachine_agrees_runReads_of_readsAt` (CONDITIONAL on the DG-ENV premise `hall` and `declName = X`: intermediate, not a supply).
Not claimed: hq, `Expr.equal_sound`, `srcDom`, `ls`/`outs`/`nexts`, `GetEnvFrame`/`hX`/`hall` supplied, real-run tie, reader coverage, FG.
`ReadRoot` (U6) and `ReadFields` are separate walks: do not identify their existence witnesses by a mere conjunction. -/
namespace Tools.ShippingGen5ReadKindsU7
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineCommand Tools.ShippingMachineEntry
open Tools.Prototype.DGenProv
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU5
open Tools.ShippingEntryReadsLinked (envAt getEnv_value getConstInfo_value)
open Tools.ShippingChildInv

def ReadFields (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  ∃ (entryV : Lean.Expr) (bsIn : List (Lean.Name × MixedGateBinder)) (b0 : Lean.Expr),
    (GenEntry ci env).value? = some entryV ∧
    mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs entryV) = some (bsIn, b0) ∧
    r.nDecl = bsIn.length ∧
    r.nIn = r.nDecl + r.shape.insts.length ∧
    r.shape.binders.length = r.nIn + r.shape.layout.slots.length + r.shape.layout.lets ∧
    r.tuple = machTupleKinds? (GenEntry ci env).type ∧
    (∃ outKinds : List (String × MixedGateBinder),
      (match machTupleKinds? (GenEntry ci env).type with
        | some ks => some (none, [("out", MixedGateBinder.bits (ks.map machWidth).sum)])
        | none => machOuts? (structEnv env) (GenEntry ci env).type) = some (r.ctor?, outKinds) ∧
      r.outNames = outKinds.map (·.1)) ∧
    r.bposL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (p, k) => if k == .bool then some p else none) ∧
    r.vposL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (p, k) => match k with | .bits _ => some p | _ => none) ∧
    r.vwL = ((List.range (r.shape.binders.map (·.2)).length).zip (r.shape.binders.map (·.2))).filterMap
      (fun (_, k) => match k with | .bits w => some w | _ => none) ∧
    ∃ (srcDom' : Lean.Expr) (snd : Sparkle.IR.Type.ResetKind),
      machDom? (r.shape.insts.length + r.shape.layout.slots.length + r.shape.layout.lets) srcDom' = some (r.dom, snd)

set_option hygiene false in
/-- the part of the `readMachine` walk after the outputs are read -/
local macro "tail4F" tupT:tacticSeq : tactic => `(tactic| (
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
      (ReadConcl ci env r ∧ ReadFields ci env r) := by
    intro a5 w r w' h
    subst hj5
    have hpr := RunsTo.pure_eq h
    subst hpr
    have hcnt' := beq_iff_eq.mp hcnt
    refine ⟨⟨rfl, hs⟩, entryV, bsIn, entryBody, hv, hp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hx_nDecl
    · exact hx_nIn
    · rw [hx_binders, hx_nSlots, hx_nLets] at hcnt'
      exact hcnt'
    · exact hx_tupq
    · $tupT
    · rw [hx_bposL, hx_idx, hx_kinds, hx_binders] <;> rfl
    · rw [hx_vposL, hx_idx, hx_kinds, hx_binders] <;> rfl
    · rw [hx_vwL, hx_idx, hx_kinds, hx_binders] <;> rfl
    · refine ⟨a, snd, ?_⟩
      subst hx_nSlots hx_nLets
      exact hd
  rcases runs_dcases h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
    exact (throwError_not_runs _ h1).elim
  · exact H5 _ _ _ _ h))

theorem readMachine_fields {declName : Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w') :
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ (ReadConcl ci env r ∧ ReadFields ci env r) := by
  unfold readMachine at h
  obtain ⟨env, w1, he, h⟩ := RunsTo.bind h
  obtain ⟨ci, w2, hc, h⟩ := RunsTo.bind h
  refine ⟨ci, env, w1, w2, he, hc, ?_⟩
  have_open h as jp0 hj0
  have H0 : ∀ a w r w', RunsTo (jp0 a) mctx mref cctx cref w r w' → (ReadConcl ci env r ∧ ReadFields ci env r) := by
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
    have H2 : (binders.length == nIn + nSlots + nLets) = true → ∀ (a : Unit) w r w', RunsTo (jp2 a) mctx mref cctx cref w r w' →
        (ReadConcl ci env r ∧ ReadFields ci env r) := by
      intro hcnt a w r w' h
      subst hj2
      generalize hm : machRoot (structEnv env).proj eb [] = o at h
      rcases o with ⟨rootLets, sel?, run?, snd⟩
      dsimp (config := {zeta := false}) only at h
      have_open h as jp3 hj3
      have H3 : ∀ (a : Lean.Expr × Nat) w r w', RunsTo (jp3 a) mctx mref cctx cref w r w' →
          (ReadConcl ci env r ∧ ReadFields ci env r) := by
        intro a w r w' h
        subst hj3
        rcases a with ⟨srcDom, depth⟩
        dsimp (config := {zeta := false}) only at h
        have_open h as jp4 hj4
        have H4 : ∀ (a : Lean.Expr) w r w', RunsTo (jp4 a) mctx mref cctx cref w r w' →
            (ReadConcl ci env r ∧ ReadFields ci env r) := by
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
            tail4F (have e : machTupleKinds? (GenEntry ci env).type = none := hx_tupq.symm; exact ⟨outKinds, by rw [e]; exact hk, rfl⟩)
          · dsimp (config := {zeta := false}) only at h
            tail4F (have e : machTupleKinds? (GenEntry ci env).type = some ks := hx_tupq.symm; exact ⟨[("out", MixedGateBinder.bits (ks.map machWidth).sum)], by rw [e] <;> rfl, rfl⟩)
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
    rcases runs_dcases h with ⟨_, h⟩ | ⟨hcnt, h⟩
    · obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
      exact (throwError_not_runs _ h1).elim
    · exact H2 hcnt _ _ _ _ h
  rcases runs_dcases h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
    exact (throwError_not_runs _ h1).elim
  · exact H0 _ _ _ _ h


theorem readMachine_agrees_runReads_of_readsAt {declName X : Lean.Name} {allowGate : Bool}
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
    {env₀ : Lean.Environment} (hall : ∀ u, Tools.ShippingGen5Env.ReadsAt env₀ cref u) (hX : declName = X) :
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape := by
  subst hX
  obtain ⟨ci', env, v1, v2, he, hc, hent, hsh⟩ := readMachine_run hrun
  have hci' : env₀.find? declName = some ci' := Tools.ShippingGen5Env.ci_of_readsAt hc (hall v1)
  have hci : env₀.find? declName = some ci := Tools.ShippingGen5Env.ci_of_readsAt hget (hall w1)
  have hcc : ci' = ci := Option.some.inj (hci'.symm.trans hci)
  obtain ⟨_, p1, p2, p3⟩ := Tools.ShippingGen5Env.envR_of_readsAt he (hall w)
  obtain ⟨_, q1, q2, q3⟩ := Tools.ShippingGen5Env.envR_of_readsAt henv (hall w2)
  obtain ⟨_, s1, s2, s3⟩ := Tools.ShippingGen5Env.envR_of_readsAt henv' (hall w3)
  subst hcc
  have hent' : r.entry = entryConst true false [] ci' (instancePredicate env) (userInliner env) (structEnv env) := hent
  have hsh' : machineShape? false [] (entryConst true false [] ci' (instancePredicate env) (userInliner env)
      (structEnv env)) (structEnv env) = some r.shape := hsh
  clear hent hsh
  rw [p1, p2, p3] at hent' hsh'
  rw [q1, q2, q3] at hshape
  rw [s3] at hshape
  rw [q1, q2, q3]
  refine ⟨hent', ?_⟩
  exact Option.some.inj (hsh'.symm.trans hshape)

end Tools.ShippingGen5ReadKindsU7
