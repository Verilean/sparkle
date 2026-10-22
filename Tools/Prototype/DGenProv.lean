import Tools.Prototype.DGenConnect
import Tools.ShippingMachineCommand
import Tools.ShippingReflectCtx
import Tools.ShippingChildKeeps

/-! # Unit DGEN2/DGEN2b: provenance of `E` / `envG` in `dgen_connect_gen`, read off the run of `readMachine`

BUILT (unit DGEN2/DGEN2b): p1-p6 exit 1/0/1/1/1/137 (OOM; the earlier `repeat'`/`split at` walk, discarded); then fast `qbuild env lean` checks; p7 `build Tools.Prototype.DGenProv Tests.Compiler.DGenToggleTest` exit 0.  No sorry/axiom/native_decide.

* PROVED (`readMachine_run`): from ONE run `RunsTo (readMachine declName allowGate) … w r w'` there are `ci env w1 w2` with
  `getEnv` run from `w` (returning `env`, ending at `w1`), then `getConstInfo declName` run from `w1` (returning `ci`, ending at `w2`) — the
  SAME chain the definition has — and `r.entry = GenEntry ci env` and `machineShape? false [] (GenEntry ci env) (structEnv env) = some r.shape`.
  (The remainder of the run, from `w2` to `w'`, is walked by the proof; it is not recorded as a separate statement.)
  The proof peels `readMachine` one bind / `if` / `match` / `have` at a time (`runs_have`, `runs_dcases`, `RunsTo.ite`, `generalize`+`rcases`); no
  `split at`, no raised heartbeats.
* `GenEntry ci env` is `entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)`: exactly the `entry` that
  `readMachine` forms from the two reads.
* PREMISE, NOT PROVED IN THIS CHANGE: `d.shape = r.shape` (`hstore`) — that the kernel-checked stored constant `d` (`f.machineData`, added by
  `generateCore` as `dataE r`) carries the shape of the `Read` that the run returned. This is the link between (i) the kernel-checked `d`
  and (ii) what `readMachine` returned; it needs the correctness of `dataE` (reflection of `r.shape` into a closed constant) and is not proved here.
* The run itself (`hrun`) is a hypothesis in the RunsTo style used elsewhere: this change does not produce it from the elaboration of the command. -/

namespace Tools.Prototype.DGenProv
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingMachineEntry Tools.ShippingEntrySoundness
open Tools.ShippingMachineCommand Tools.ShippingChildInv Tools.ShippingReflectCtx
open Tools.Prototype.DGenConnect Tools.ShippingMachineAuto Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.Prototype.ReaderExec Tools.Prototype.ReaderTyped Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk Tools.Prototype.StartDomOk Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.Prototype.ReaderClosed Tools.Prototype.ReaderComposed

def GenEntry (ci : Lean.ConstantInfo) (env : Lean.Environment) : Lean.ConstantInfo :=
  entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env)

/-- `have x := v; b x` run: `x` is an opaque local with the equation `x = v`. -/
theorem runs_have {γ α : Type} (v : γ) (b : γ → MetaM α) {mctx mref cctx cref w r w'}
    (h : RunsTo (letFun v b) mctx mref cctx cref w r w') :
    ∃ x, x = v ∧ RunsTo (b x) mctx mref cctx cref w r w' := ⟨v, rfl, h⟩

/-- `have_open h as x hx`: `h : RunsTo (have y := v; body y)` becomes `hx : x = v`, `h : RunsTo (body x)`
(the value and the body are read off the term, so unification cannot mis-split it). -/
elab "have_open " h:ident " as " x:ident hx:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let some decl := (← getLCtx).findFromUserName? h.getId | throwError "no hypothesis {h.getId}"
  let ty ← instantiateMVars decl.type
  let args := ty.getAppArgs
  unless ty.isAppOf ``RunsTo && args.size == 9 do throwError "not a RunsTo"
  let m := args[1]!.headBeta.consumeMData
  let (v, b) ← match m with
    | .letE n t v body _ => pure (v, Expr.lam n t body .default)
    | _ =>
      unless m.isAppOfArity ``letFun 4 do throwError "not a `have`: {m.getAppFn.ctorName} {m.getAppNumArgs}"
      pure (m.getAppArgs[2]!, m.getAppArgs[3]!)
  let pf ← Lean.Meta.mkAppM ``runs_have #[v, b, mkFVar decl.fvarId]
  let pfS ← Lean.Elab.Term.exprToSyntax pf
  Lean.Elab.Tactic.evalTactic (← `(tactic| obtain ⟨$x:ident, $hx:ident, $h:ident⟩ := $pfS))

/-- A decided `if` in the form the equation lemma of `readMachine` has. -/
theorem runs_dcases {c : Prop} {d : Decidable c} {α : Type} {f : ¬c → MetaM α} {g : c → MetaM α}
    {mctx mref cctx cref w r w'}
    (h : RunsTo (Decidable.casesOn d f g) mctx mref cctx cref w r w') :
    (∃ hn : ¬c, RunsTo (f hn) mctx mref cctx cref w r w') ∨
    (∃ hc : c, RunsTo (g hc) mctx mref cctx cref w r w') := by
  cases d with
  | isFalse hn => exact .inl ⟨hn, h⟩
  | isTrue hc => exact .inr ⟨hc, h⟩

/-- What a `readMachine` run returns, in terms of the entry constant and the shape. -/
def ReadConcl (ci : Lean.ConstantInfo) (env : Lean.Environment) (r : Read) : Prop :=
  r.entry = GenEntry ci env ∧ machineShape? false [] (GenEntry ci env) (structEnv env) = some r.shape

set_option hygiene false in
/-- the part of the `readMachine` walk after the outputs are read -/
local macro "tail4" : tactic => `(tactic| (
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
      ReadConcl ci env r := by
    intro a w r w' h
    subst hj5
    have hp := RunsTo.pure_eq h
    subst hp
    exact ⟨rfl, hs⟩
  rcases runs_dcases h with ⟨_, h⟩ | ⟨_, h⟩
  · obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
    exact (throwError_not_runs _ h1).elim
  · exact H5 _ _ _ _ h))

theorem readMachine_run {declName : Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (h : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w') :
    ∃ ci env w1 w2, RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧ ReadConcl ci env r := by
  unfold readMachine at h
  obtain ⟨env, w1, he, h⟩ := RunsTo.bind h
  obtain ⟨ci, w2, hc, h⟩ := RunsTo.bind h
  refine ⟨ci, env, w1, w2, he, hc, ?_⟩
  have_open h as jp0 hj0
  have H0 : ∀ a w r w', RunsTo (jp0 a) mctx mref cctx cref w r w' → ReadConcl ci env r := by
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
        ReadConcl ci env r := by
      intro a w r w' h
      subst hj2
      generalize hm : machRoot (structEnv env).proj eb [] = o at h
      rcases o with ⟨rootLets, sel?, run?, snd⟩
      dsimp (config := {zeta := false}) only at h
      have_open h as jp3 hj3
      have H3 : ∀ (a : Lean.Expr × Nat) w r w', RunsTo (jp3 a) mctx mref cctx cref w r w' →
          ReadConcl ci env r := by
        intro a w r w' h
        subst hj3
        rcases a with ⟨srcDom, depth⟩
        dsimp (config := {zeta := false}) only at h
        have_open h as jp4 hj4
        have H4 : ∀ (a : Lean.Expr) w r w', RunsTo (jp4 a) mctx mref cctx cref w r w' →
            ReadConcl ci env r := by
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
            tail4
          · dsimp (config := {zeta := false}) only at h
            tail4
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

#print axioms readMachine_run

/-- The stored constant carries the shape of the `Read` the run returned.  PREMISE (OPEN, not proved in this change): needs `dataE`'s
reflection to evaluate back to `r.shape`. -/
def StoredFromRead (d : MachineData) (r : Read) : Prop := d.shape = r.shape

/-- **PROVED** (from the run of `readMachine` and `StoredFromRead`): the `E`/`envG` of `GenReadsShape` are the entry constant and the
environment of that run — the results of its `getConstInfo`/`getEnv` reads, chained as in the definition. -/
theorem readMachine_genReads {declName : Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {d : MachineData} (hstore : StoredFromRead d r) :
    ∃ (ci : Lean.ConstantInfo) (env : Lean.Environment) (w1 w2 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      r.entry = GenEntry ci env ∧ GenReadsShape (GenEntry ci env) env d := by
  obtain ⟨ci, env, w1, w2, he, hc, hent, hsh⟩ := readMachine_run hrun
  refine ⟨ci, env, w1, w2, he, hc, hent, ?_⟩
  unfold GenReadsShape
  rw [hstore]
  exact hsh

/-- **PROVED (conditional on A's premises, the run `hrun`, `StoredFromRead`, and — for the discovered `ci`/`env` — `hpe`, `ShippedToProto`)**:
`dgen_connect_gen` with `E := GenEntry ci env`, `envG := env` the entry constant and environment of the run of `readMachine`, no longer
arbitrary binders.  `hpe` and `hcorr` are about those very `ci`/`env` (they are antecedents of the last conjunct, since `ci`/`env` exist
only after the run is unpacked). -/
theorem dgen_connect_prov
    (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range) (hz : ZeroLitAgrees)
    (hE : EqvLetOk0)
    (hsig : ∀ senv, SigTyRange senv) (hraw : ∀ senv, RawNodeRange senv) (hnode : ∀ senv, NormNodeRange senv)
    {declName : Name} {allowGate : Bool}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    (d : MachineData) (hok : d.ok = true)
    (hbody : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hstore : StoredFromRead d r) :
    ∃ (ci : Lean.ConstantInfo) (env : Lean.Environment) (w1 w2 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env w1 ∧
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      r.entry = GenEntry ci env ∧ GenReadsShape (GenEntry ci env) env d ∧
      ((∀ p : ShapePre, shapePre false [] (GenEntry ci env) (structEnv env) = some p → LetOk 0 p.e = true) →
        ShippedToProto (GenEntry ci env) (structEnv env) d.shape →
        machineShapeN false [] (GenEntry ci env) (structEnv env) true = some (some d.shape) ∧
        d.letsAliasOk = true ∧
        ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
          (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
          Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape) := by
  obtain ⟨ci, env, w1, w2, he, hc, hent, hgen⟩ := readMachine_genReads hrun hstore
  exact ⟨ci, env, w1, w2, he, hc, hent, hgen, fun hpe hcorr =>
    dgen_connect_gen hroot hlift hinst1 hz hE hsig hraw hnode d hok hbody hgen hpe hcorr⟩

#print axioms readMachine_genReads
#print axioms dgen_connect_prov

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``dgen_connect_prov
  ["RootFloatRange", "LiftRange", "Inst1Range", "ZeroLitAgrees", "EqvLetOk0", "SigTyRange", "RawNodeRange",
    "NormNodeRange", "RunsTo", "Eq", "Eq", "StoredFromRead"])

end Tools.Prototype.DGenProv
