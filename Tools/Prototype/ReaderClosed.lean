import Tools.Prototype.ReaderFixpointTyped
import Tools.ShippingCloInv

/-! # Unit LCQ2 prototype: `NoLetBvar st.lets` for the reader's final state, derived (no new hypothesis)

BUILT: c7 exit 0 (c5 exit 1 and c6 exit 1: base-file parse error in the `run_meta auditPropBinders` lines of ReaderFixpointSpec/Typed/PreprocLetOk, whitespace-only fix, then missing `open`s here).  No sorry / axiom / native_decide.  Production unchanged.

LCQ (`ReaderFixpointTyped`, ledger L6c13) left `NoLetBvar st.lets` (no `let` value is a bare `bvar`) as an OPEN premise of
`machineShapeN_typed`.  `Tools/ShippingCloInv.lean` proves, for the fuel twin `readF`, that a SUCCESSFUL run keeps
`CloSt st` (every `let` value, saved nested result and domain has no loose bound variable) from the entry condition
`CloSt st ∧ EnvClo env`.  Here the wrapper phases of `machineShapeN` are walked (`shapeStart` from `{}`, the root-`let`
fold from the all-`unit` start environment, `shapeBody`):

* `shapeStart_clo`, `shapeRootLet_clo`, `rootLets_clo`, `shapeBody_clo`: `CloSt` of every intermediate state; the START
  state is the empty state / `reserved {} dom'` with `dom'` a reader result, and the START environment is the list of
  `unit`s, so NO closedness hypothesis on any input expression is needed (an input `bvar` outside the environment becomes
  the `machIn` placeholder);
* `machineShapeN_lets_nb`: `machineShapeN_lets` with the extra conclusion `NoLetBvar st.lets` for the SAME `st`, `v`;
* `machineShapeN_typed_nb`: `machineShapeN_typed` without the `NoLetBvar st.lets →` antecedent (same premises:
  `RootFloatRange`, `LiftRange`, `Inst1Range`, `SigTyRange senv`, `ShapeInOk`).  A THROWING check at the end of the file
  compares its type with `machineShapeN_typed`'s (the only difference is the removed antecedent, and the new type
  contains no `NoLetBvar` constant).

What this is NOT: a statement about the shipped `machineShape?` / `partial` readers (needs `TwinCoverAt` and
`machNorm = execNorm`, OPEN as before); `d.ok` / `hbody` stay the generation-path checks; the existence of `d` (the `unq`
step) is not covered.  `NoLetBvar` is REMOVED as a hypothesis, not replaced by another: the closedness needed is derived
from the empty start state and the `unit` environment by `readF_clo`.

## BUILD LOG
c5 exit 1, c6 exit 1, c7 exit 0 (the `run_meta` checks at the end of the file ran and passed in c7). -/
namespace Tools.Prototype.ReaderClosed
open Lean Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk Tools.ShippingCloInv
open Tools.Prototype.ReaderExec Tools.Prototype.ReaderTyped
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedSourceBridge

theorem envClo_units {α : Type} (l : List α) : EnvClo (l.map fun _ => MachVal.unit) := by
  intro v hv
  obtain ⟨_, _, h⟩ := List.mem_map.mp hv
  cases h

theorem letsClo_noLetBvar {lets : MachLets} (h : LetsClo lets) : NoLetBvar lets :=
  fun l hl b => clo_ne_bvar (h l hl) b

section Phases
variable {senv : StructEnv}

theorem shapeStart_clo {n : Nat} {m : ShapeMid} {st0 : MachRead}
    (hr : (shapeStart senv m).run (wtab senv n) = some (some st0)) : CloSt st0 := by
  rcases shapeStart_inv hr with ⟨_, h0⟩ | ⟨dom, αs, initsE, body, dom', stc, base, hm, hc, hres⟩
  · rw [h0]; exact cloSt_init
  · obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hres
    subst hst
    have hd := (machConvF_clo cloSt_init (envClo_units m.rootLets) hc).2
    exact cloSt_dom cloSt_init (by rfl) (by rfl) (d := dom') (by rfl) hd

theorem rootBind_clo {nm : Name} {ty v' : Lean.Expr} {lets : MachLets} {c : Bool}
    (H : LetsClo lets) (hv : Clo 0 v' = true) :
    LetsClo (if c = true then machBindLetNamed nm ty v' lets else machBindLet nm ty v' lets).2 ∧
    Clo 0 (if c = true then machBindLetNamed nm ty v' lets else machBindLet nm ty v' lets).1 = true := by
  by_cases h : c = true
  · rw [if_pos h]
    exact machBindLetNamed_clo H hv
  · rw [if_neg h]
    exact machBindLet_clo H hv

theorem shapeRootLet_clo {n : Nat} (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr)
    (s' : List MachVal × MachRead) (hs : CloSt s.2 ∧ EnvClo s.1)
    (hr : (shapeRootLet senv s a).run (wtab senv n) = some (some s')) :
    CloSt s'.2 ∧ EnvClo s'.1 := by
  obtain ⟨env, st⟩ := s
  obtain ⟨nm, ty, v⟩ := a
  obtain ⟨hst, hE⟩ := hs
  first
    | (simp only [shapeRootLet] at hr)
    | (unfold shapeRootLet at hr; try dsimp only at hr)
  split at hr
  · obtain ⟨⟨mv, st2⟩, hl2, hr⟩ := bindO_some_inv hr
    have hp := machLoopRootF_clo hst hE hl2
    try dsimp only at hr
    have e := okO_run_inv hr
    subst e
    exact ⟨hp.1, envClo_cons hE (fun w hw => by subst hw; exact hp.2)⟩
  · split at hr
    · obtain ⟨⟨v', st2⟩, hc, hr⟩ := bindO_some_inv hr
      have hp := machConvF_clo hst hE hc
      try dsimp only at hr
      have e := okO_run_inv hr
      subst e
      have hF := rootBind_clo (nm := nm) (ty := ty) (c := (!st2.loops.isEmpty && machIsSlot v'))
        hp.1.1 hp.2
      generalize (if (!st2.loops.isEmpty && machIsSlot v') = true then machBindLetNamed nm ty v' st2.lets
        else machBindLet nm ty v' st2.lets) = bl at hF ⊢
      obtain ⟨x, lets'⟩ := bl
      exact ⟨cloSt_lets hp.1 hF.1 (by rfl) (by rfl),
        envClo_cons hE (fun w hw => by injection hw with hw; subst hw; exact hF.2)⟩
    · exact (failO_run_inv hr).elim

theorem rootLets_clo {n : Nat} {l : List (Name × Lean.Expr × Lean.Expr)} {env env' : List MachVal}
    {st0 st1 : MachRead} (h0 : CloSt st0) (hE : EnvClo env)
    (hr : (foldO (shapeRootLet senv) (env, st0) l).run (wtab senv n) = some (some (env', st1))) :
    CloSt st1 ∧ EnvClo env' := by
  exact foldO_inv_mem (h := wtab senv n) (fun s : List MachVal × MachRead => CloSt s.2 ∧ EnvClo s.1)
    (fun _ : Name × Lean.Expr × Lean.Expr => True) (f := shapeRootLet senv)
    (fun s a s' _ hs hr => shapeRootLet_clo s a s' hs hr) l (env, st0) (env', st1)
    (fun _ _ => trivial) ⟨h0, hE⟩ hr

theorem shapeBody_clo {n : Nat} {m : ShapeMid} {env : List MachVal} {st1 st : MachRead}
    {v : Lean.Expr} (hs : CloSt st1) (hE : EnvClo env)
    (hr : (shapeBody m env st1).run (wtab senv n) = some (some (st, v))) : CloSt st := by
  unfold shapeBody at hr
  rcases hm : m.run? with _ | ⟨dom, αs, initsE, body⟩
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    injection e with e1 e2
    subst e1
    exact (machConvF_clo hs hE hc).1
  · rw [hm] at hr
    try dsimp only at hr
    obtain ⟨⟨ws, v0, st2⟩, hc, hr⟩ := bindO_some_inv hr
    try dsimp only at hr
    have e := okO_run_inv hr
    injection e with e1 e2
    have hp := machChainF_clo hs (envClo_cons hE (fun w hw => by cases hw)) hc
    subst e1
    exact cloSt_congr hp.1 (by rfl) (by rfl) (by rfl)

end Phases

/-! ## The final state of a successful run -/

/-- **`machineShapeN_lets` plus `NoLetBvar`** for the SAME `st`, `v` (PROVED; the premises are those of
`machineShapeN_lets`, nothing is added). -/
theorem machineShapeN_lets_nb {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange)
    (hinst1 : Inst1Range) (hsig : SigTyRange senv)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hin : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p →
      execNorm senv p.e = some en → ShapeInOk senv (shapeMid senv p en))
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧ NoLetBvar st.lets ∧
      shapePost ai p (shapeMid senv p en) st v = some sp := by
  obtain ⟨n, p, en, st0, env, st1, st, v, hp, hen, h0, h1, h2, h3⟩ := machineShapeN_steps h
  have hI := hin p en hp ((execNorm_iff senv).mpr ⟨n, hen⟩)
  have hbundle := Tools.ShippingLetsReaderInv.bundleIotaRange
  have r0 : RdOk st0 := shapeStart_ok (n := n) (fun dom αs initsE body dom' stc hm hc =>
    hI.startDom n dom αs initsE body dom' stc hm hc) h0
  have r1 := rootLets_ok hroot hlift hinst1 hsig hbundle hI.rootLets r0 h1
    (fun v hv => by cases hv)
  have r2 := shapeBody_ok hroot hlift hinst1 hsig hbundle r1.1 r1.2 hI.root hI.runBody
    (shapeMid_wrap_ok senv p en hI.root) h2
  have c0 : CloSt st0 := shapeStart_clo h0
  have c1 := rootLets_clo c0 (fun v hv => by cases hv) h1
  have c2 : CloSt st := shapeBody_clo c1.1 c1.2 h2
  exact ⟨p, en, st, v, hp, (execNorm_iff senv).mpr ⟨n, hen⟩, r2.1, r2.1.1, r2.2.2,
    letsClo_noLetBvar c2.1, h3⟩

/-- **`machineShapeN_typed` WITHOUT the `NoLetBvar st.lets →` antecedent** (PROVED; same premises as
`machineShapeN_typed`).  Everything else in the conclusion is unchanged; `d.ok` and `hbody` remain the checks of the
generation path.  Conditional on the same named premises; about the prototype wrapper `machineShapeN`, not the shipped
`machineShape?` (`TwinCoverAt`, `machNorm = execNorm` OPEN). -/
theorem machineShapeN_typed_nb {senv : StructEnv}
    (hroot : RootFloatRange) (hlift : LiftRange) (hinst1 : Inst1Range) (hsig : SigTyRange senv)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hin : ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p →
      execNorm senv p.e = some en → ShapeInOk senv (shapeMid senv p en))
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      (∀ (d : MachineData), d.shape = sp → d.ok = true →
        d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
          (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed →
        d.letsAliasOk = true ∧
        ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
          (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
          Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape) := by
  obtain ⟨p, en, st, v, hp, hen, hrd, hna, hlo, hnb, hpost⟩ :=
    machineShapeN_lets_nb hroot hlift hinst1 hsig hin h
  refine ⟨p, en, st, v, hp, hen, hrd, hna, hlo, hpost, ?_⟩
  intro d hs hok hbody
  have halias := typed_letsAlias (shapePre_outs_ne hp) hpost hna hnb d hs hok hbody
  exact ⟨halias, fun mctx mref cctx cref => letsClose_of_data d hok hbody halias mctx mref cctx cref⟩

#print axioms clo_ne_bvar
#print axioms readF_clo
#print axioms shapeStart_clo
#print axioms shapeRootLet_clo
#print axioms rootLets_clo
#print axioms shapeBody_clo
#print axioms machineShapeN_lets_nb
#print axioms machineShapeN_typed_nb

/-! ## Throwing checks (reviewer, binding)

`auditPropBinders` only checks the head constants of the OUTER Prop hypotheses, so the removal of the antecedent
`NoLetBvar st.lets →` inside the conclusion is checked separately: strip that antecedent from the type of
`machineShapeN_typed`, require it to be syntactically (alpha-)equal to the type of `machineShapeN_typed_nb`, require that
it really occurred in the old type, and require that the new type contains no `NoLetBvar` constant. -/

open Lean Meta in
/-- Remove every non-dependent antecedent whose type is headed by `NoLetBvar`. -/
def stripNoLetBvar (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .forallE _ dom body _ =>
      if dom.getAppFn.isConstOf ``Tools.Prototype.ReaderTyped.NoLetBvar then
        some (body.lowerLooseBVars 1 1)
      else none
    | _ => none

/-- Every `∀ _ : NoLetBvar …, body` binder occurring in `e`, with its body (integrator, par/int-r31). -/
partial def noLetBvarSites : Expr → Array Expr
  | .forallE _ dom body _ =>
    let rest := noLetBvarSites dom ++ noLetBvarSites body
    if dom.getAppFn.isConstOf ``Tools.Prototype.ReaderTyped.NoLetBvar then #[body] ++ rest else rest
  | .lam _ d b _ => noLetBvarSites d ++ noLetBvarSites b
  | .app f a => noLetBvarSites f ++ noLetBvarSites a
  | .letE _ t v b _ => noLetBvarSites t ++ noLetBvarSites v ++ noLetBvarSites b
  | .mdata _ b => noLetBvarSites b
  | .proj _ _ b => noLetBvarSites b
  | _ => #[]

open Lean Meta in
def checkNoLetBvarRemoved (oldN newN : Name) : MetaM Unit := do
  let oi ← getConstInfo oldN
  let ni ← getConstInfo newN
  -- (reviewer, int-r31) exactly ONE antecedent is removed, and the remaining body does not refer to it
  let sites := noLetBvarSites oi.type
  unless sites.size == 1 do
    throwError "REMOVAL CHECK FAILED: {oldN} has {sites.size} NoLetBvar antecedents, expected exactly 1"
  for body in sites do
    if body.hasLooseBVar 0 then
      throwError "REMOVAL CHECK FAILED: the body under the NoLetBvar antecedent of {oldN} refers to it"
  let stripped := stripNoLetBvar oi.type
  if stripped == oi.type then
    throwError "REMOVAL CHECK FAILED: {oldN} has no NoLetBvar antecedent to strip"
  unless stripped == ni.type do
    throwError "REMOVAL CHECK FAILED: the type of {newN} differs from {oldN} with the NoLetBvar antecedent stripped"
  if (ni.type.find? fun x => x.isConstOf ``Tools.Prototype.ReaderTyped.NoLetBvar).isSome then
    throwError "REMOVAL CHECK FAILED: {newN} still mentions NoLetBvar"
  logInfo m!"removal check {newN}: type = {oldN} minus its single NoLetBvar antecedent (body independent of it); no NoLetBvar constant"

run_meta checkNoLetBvarRemoved ``Tools.Prototype.ReaderTyped.machineShapeN_typed ``machineShapeN_typed_nb
run_meta Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_typed_nb ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ShapeInOk", "Eq"]
run_meta Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_lets_nb ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ShapeInOk", "Eq"]

end Tools.Prototype.ReaderClosed
