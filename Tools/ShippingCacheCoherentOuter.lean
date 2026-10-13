import Tools.ShippingCacheCoherentVia

variable {tenv : Lean.Environment}

/-! # An OUTERMOST run: after the clear the cache is empty, so `Prov` holds where the machine synthesis starts

`Tools.ShippingCacheCoherentVia.core_reads_val` is the core entry at a
POSITIVE depth (no clear). This file is its sibling at depth 0 — the entry
clears the child cache — and the consequence for a machine-route
declaration:

* `InvE L C Dp w` = `InvC L C Dp w ∧ (C → L.val w = {})`: once the clear has
  run (`C` becomes `True`), the cache's value is the empty map; its step
  lemmas (`invE_pure`, `invE_framed`, `invE_depthSet`, `invE_clear`) and the
  tactic `peel_e` (the text of `peel_inv`);
* `core_reads_val0`: an outermost core run (`L.dval w = 0`; only the
  synthesis ref and quietness are asked of the start world — the depth-0
  half of `ChildBnd`): the body `synthesizeFromConst` starts in an invariant
  world of positive depth whose cache is `{}`, and the run ends with the
  cache the body ends with;
* `coreVia0_of`: for a machine-route declaration, IF the machine synthesis
  does not fall back from invariant worlds of positive depth whose cache
  satisfies `Prov` (`hclose` — what
  `Tools.ShippingCacheCoherentCert.machine_closes_of_entryOk` gives), THEN
  an outermost core run IS a machine synthesis that returns the run's
  result. SCOPE: outermost starts only. For a nested start the cache at the
  machine synthesis's start is whatever the start world holds, and `Prov` of
  it is not derived.

WRITTEN, NOT BUILT (par/a-38). -/
namespace Tools.ShippingCacheCoherentOuter
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv Tools.ShippingCacheCoherentRun Tools.ShippingCacheCoherentVia

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- `InvC`, and after the clear the cache's value is the empty map. -/
def InvE (L : RefLaws mref cref) (C Dp : Prop) (w : Void IO.RealWorld) : Prop :=
  InvC L C Dp w ∧ (C → L.val w = ({} : Std.HashMap Name Res))

theorem invE_pure (L : RefLaws mref cref) {C Dp : Prop} {α : Type} {a b : α}
    {w w' : Void IO.RealWorld}
    (h : RunsTo (Pure.pure a : MetaM α) mctx mref cctx cref w b w') (hw : InvE L C Dp w) :
    InvE L C Dp w' := by
  refine ⟨inv_pure L h hw.1, fun c => ?_⟩
  rw [(RunsTo.pure_world h).2]
  exact hw.2 c

theorem invE_framed (L : RefLaws mref cref) {C Dp : Prop} {α : Type} {p : MetaM α}
    {w : Void IO.RealWorld} {a : α} {w' : Void IO.RealWorld}
    (h : RunsTo p mctx mref cctx cref w a w') (hw : InvE L C Dp w)
    (hp : Op p := by first
      | exact Op.framed (Framed.sideSet _ (by constructor))
      | exact Op.framed (Framed.sideGet (by constructor))
      | exact Op.framed (Framed.sideModify _ (by constructor))
      | exact Op.framed (by constructor)
      | exact Op.diag (by constructor)) : InvE L C Dp w' := by
  refine ⟨inv_framed L h hw.1 hp, fun c => ?_⟩
  rw [(L.sameOp hp h hw.1.2.2.1).1.1]
  exact hw.2 c

theorem invE_depthSet (L : RefLaws mref cref) {C Dp : Prop} {v : Nat}
    {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (h : RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w')
    (hw : InvE L C Dp w) : InvE L C (v ≠ 0) w' := by
  refine ⟨inv_depthSet L h hw.1, fun c => ?_⟩
  rw [(L.depthSet _ _ _ _ h).1]
  exact hw.2 c

/-- **The depth-0 clear**: from then on the cache's value is `{}`. -/
theorem invE_clear (L : RefLaws mref cref) {C Dp : Prop}
    {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (h : RunsTo (sparkleChildCache.set {} : MetaM Unit) mctx mref cctx cref w u w')
    (hw : InvE L C Dp w) : InvE L True Dp w' :=
  ⟨inv_clear L h hw.1, fun _ => (L.cacheSet _ _ _ _ h).1⟩

/-- The lemma carrying `InvE` over one step, by the step's head. -/
meta def stepLemmaE (prog : Lean.Expr) : Lean.MetaM (Lean.TSyntax `term) := do
  let prog ← Lean.instantiateMVars prog
  if prog.isAppOf ``Pure.pure then return ← `(invE_pure)
  if prog.isAppOf ``ST.Ref.set then
    if (prog.getAppArgs.find? (·.isConstOf ``sparkleChildCache)).isSome then return ← `(invE_clear)
    if (prog.getAppArgs.find? (·.isConstOf ``sparkleSynthDepth)).isSome then
      return ← `(invE_depthSet)
  return ← `(invE_framed)

/-- One bind of the prefix, `InvE` carried to the next world (the text of
`peel_inv`). -/
elab "peel_e " L:term:max h:ident hw:ident : tactic => do
  match ← runHeadIs h.getId ``Bind.bind with
  | some true =>
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      obtain ⟨_, _, $(Lean.mkIdent `step):ident, $h:ident⟩ := RunsTo.bind $h:ident))
    let lem ← Lean.Elab.Tactic.withMainContext do
      let d ← Lean.Meta.getLocalDeclFromUserName `step
      stepLemmaE (← Lean.instantiateMVars d.type).getAppArgs[1]!
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      (have $hw:ident := $lem $L $(Lean.mkIdent `step):ident $hw
       clear $(Lean.mkIdent `step):ident)))
  | _ => throwError "head is not a bind"

/-- **The core entry at depth 0, with its worlds.** The body
(`synthesizeFromConst`) starts in an invariant world of positive depth whose
cache is EMPTY (the clear), and the run ends with the cache the body ends
with. Of the start world only the synthesis ref and quietness are asked. -/
theorem core_reads_val0 (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {declName : Name} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design} (hs : L.sval w = some synthesizeChild) (hq : L.quiet w)
    (hd0 : L.dval w = 0)
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (b : Bool) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (profLogIO b)
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, D) w4 ∧ InvV L w3 ∧ L.dval w3 ≠ 0 ∧
      L.val w3 = ({} : Std.HashMap Name Res) ∧ InvV L w4 ∧ L.val w' = L.val w4 := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
  obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
  obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
  have q1 := L.sameQ (.ioEnv _) s1 hq
  obtain ⟨⟨a2, b2, c2⟩, q2⟩ := L.sameD (.profLog _ _) s2 q1
  have q3 := L.sameQ .depthGet s3 q2
  have keep : (L.val wc = L.val w ∧ L.sval wc = L.sval w ∧ L.dval wc = L.dval w) ∧ L.quiet wc := by
    obtain ⟨a1, b1, c1⟩ := L.same (.ioEnv _) s1
    obtain ⟨a3, b3, c3⟩ := L.same .depthGet s3
    exact ⟨⟨a3.trans (a2.trans a1), b3.trans (b2.trans b1), c3.trans (c2.trans c1)⟩, q3⟩
  have hd : d = L.dval w := by
    rw [L.depthGet _ _ _ s3, c2, (L.same (.ioEnv _) s1).2.2]
  -- a returning run passed the depth guard
  rcases RunsTo.ite h with h | h
  · obtain ⟨_, _, ht, _⟩ := RunsTo.bind h
    exact (throwError_not_runs _ ht).elim
  -- outermost: the clear
  have h0 : (d == 0) = true := by
    rw [hd, hd0]
    rfl
  have hwE : InvE L False False wc :=
    ⟨invC_keep L keep ⟨fun f => f.elim, hs, hq, fun f => f.elim⟩, fun f => f.elim⟩
  simp only [h0, ↓reduceIte] at h
  iterate 40 (first | peel_e L h hwE | skip)
  obtain ⟨w4, u, h, hfin⟩ := tryFinally_fin h
  obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
  have hwE := invE_framed L hget hwE (Op.framed (.constInfo _))
  obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
  have hwE := invE_framed L henv hwE (Op.framed .env)
  have hw3 := invV_of_invC L hwE.1
  have hd3 := hwE.1.2.2.2 (Nat.succ_ne_zero _)
  have hv3 := hwE.2 trivial
  -- the body keeps the invariant: the world the `finally` starts in
  have hJ := keeps_runs
    (hB L.plain _ (childKeeps_all L.plain (hB _) _ (fun _ => trivial)) mctx cctx prof.isSome
      declName _ _)
    (show J L.plain _ _ from ⟨hw3, rfl, trivial⟩) h
  have hw4 : InvV L w4 := hJ.1
  have hf0 : InvM L (L.val w4) True False w4 :=
    ⟨⟨fun _ => hw4.1, hw4.2.1, hw4.2.2, fun f => f.elim⟩, rfl⟩
  -- the `finally`: the depth's release (at depth 0 nothing is restored)
  obtain ⟨_, wf, hmodf, hfin⟩ := RunsTo.bind hfin
  have hwf := invM_depthModify L hmodf hf0
  have hvf : L.val w' = L.val w4 := by
    first
      | (rcases RunsTo.ite hfin with hfin | hfin
         · iterate 10 (first | peel_val L hfin hwf | skip)
           exact (invM_framed L hfin hwf).2
         · rw [(RunsTo.pure_world hfin).2]
           exact hwf.2)
      | (rw [(RunsTo.pure_world hfin).2]
         exact hwf.2)
      | (iterate 10 (first | peel_val L hfin hwf | skip)
         exact (invM_framed L hfin hwf).2)
  exact ⟨prof.isSome, env, ci, _, w2, _, _, _, _, hget, henv, h, hw3, hd3, hv3, hw4, hvf⟩

/-- **An outermost core run of a machine-route declaration is its machine
synthesis, started from a `Prov` (empty) cache** — given that the machine
synthesis does not fall back from `Prov` worlds (`hclose`). OUTERMOST STARTS
ONLY: `L.dval w = 0`. -/
theorem coreVia0_of (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hH : ∀ L' : RefLaws mref cref, HarnessRel L') {c : Name} {shape : MachineShape}
    (entry : MachineDefines mctx mref cctx cref c shape)
    (hclose : ∀ {tenv : Lean.Environment} (b : Bool) (w9 : Void IO.RealWorld) (r : Option Res)
      (w10 : Void IO.RealWorld),
      InvV L w9 → L.dval w9 ≠ 0 → Prov (L.val w9) →
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
        mctx mref cctx cref w9 r w10 → r ≠ none)
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hs : L.sval w = some synthesizeChild) (hq : L.quiet w) (hd0 : L.dval w = 0)
    (hr : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (tenv : Lean.Environment) (b : Bool) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
        mctx mref cctx cref w9 (some (M, D)) w10 ∧
      InvV L w9 ∧ L.dval w9 ≠ 0 ∧ Prov (L.val w9) := by
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, hget, henv, run, hw3, hd3, hv3, -, -⟩ :=
    core_reads_val0 L hB hs hq hd0 hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ hget henv henv
  obtain ⟨envR', w7, w8, henv', hmach⟩ := sfc_machine_val L old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ hget henv henv'
  obtain ⟨r, w9, w10, hrun, hw9, hd9, hv9, hres⟩ := hmach shape hshape
  have hd9' : L.dval w9 ≠ 0 := by
    rw [hd9]
    exact hd3
  have hp9 : Prov (L.val w9) := by
    rw [hv9, hv3]
    exact prov_empty
  have hne := hclose b w9 r w10 hw9 hd9' hp9 hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have hJ := keeps_runs
      (machine_keeps (mctx := mctx) (cctx := cctx) L.plain (hH _) (L.dval w9)
        (childKeeps_all L.plain (hB _) _ (fun _ => trivial)) b c shape)
      (show J L.plain _ _ from ⟨hw9, rfl, trivial⟩) hrun
    obtain ⟨he, -⟩ := hres res rfl hJ.1.2.2
    subst he
    exact ⟨_, b, w9, w10, hrun, hw9, hd9', hp9⟩

end Tools.ShippingCacheCoherentOuter
