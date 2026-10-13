import Tools.ShippingCacheCoherentCert

/-! # `CoreVia`: a core run on the machine route, with its worlds

`Tools.ShippingCacheCoherentCert.CoreVia L c shape` was a statement: a
returning core run of `c` from an invariant world of positive depth IS a
machine synthesis of `shape` that returns the run's result, whose start
world has the run's start cache and whose end world has the run's end
cache. Here it is a theorem (`coreVia_of`), from the route premises the
endpoints already carry — `MachineDefines` (what the run reads of the
declaration) and `MachineClosesAt` (the closing) — and FRAME steps only.
Nothing is assumed beyond `RefLaws`; no built file is modified.

The built inversions do not relate cache values (`core_reads_inv` returns
`InvV` of the body's start world; `synthesizeFromConst_machine_inv` drops
the suffix; `RunsTo.try_finally` drops the `finally`). What is added:

* `tryFinally_fin`: a returning `try … finally` is a returning run
  of the body followed by a returning run of the `finally` block;
* `InvM L mb C Dp w` = `InvC L C Dp w ∧ L.val w = mb`, its step lemmas
  (`invM_pure`, `invM_framed`, `invM_depthSet`, `invM_depthModify`) and the
  tactic `peel_val` (the text of `peel_inv` over these lemmas);
* `core_reads_val`: the entry's prefix at POSITIVE depth (no clear) leaves
  the cache, and so does its `finally`;
* `sfc_machine_val`: the machine arm of `synthesizeFromConst`: the machine
  synthesis starts with the arm's start cache, and when it returns a module
  the arm ends with the machine synthesis's end cache (the log, the memo
  insert);
* `coreVia_of`.

WRITTEN, NOT BUILT (par/a-35). -/
namespace Tools.ShippingCacheCoherentVia
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInv Tools.ShippingCacheCoherentCert

/-! ## `try … finally`, with the run of the `finally` block -/

/-- A returning `try x finally fin`: `x` returns, then `fin` returns, and the
whole ends where `fin` does. (The text of `RunsTo.try_finally`, keeping the
second run.) -/
theorem tryFinally_fin {α β : Type} {x : MetaM α} {fin : MetaM β}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w : Void IO.RealWorld} {a : α}
    {w' : Void IO.RealWorld}
    (h : RunsTo (_root_.tryFinally x fin) mctx mref cctx cref w a w') :
    ∃ (w1 : Void IO.RealWorld) (u : β),
      RunsTo x mctx mref cctx cref w a w1 ∧ RunsTo fin mctx mref cctx cref w1 u w' := by
  unfold RunsTo at h
  change (EST.bind (@MonadFinally.tryFinally' (EST Exception IO.RealWorld) _ _ _
      (x mctx mref cctx cref) (fun _ => fin mctx mref cctx cref)) (fun p => EST.pure p.1)) w = _
    at h
  unfold EST.bind at h
  split at h
  · rename_i p w1 heq
    simp only [MonadFinally.tryFinally'] at heq
    split at heq
    · rename_i v w2 hx
      split at heq
      · rename_i u w3 hfin
        cases heq
        simp only [EST.pure] at h
        cases h
        exact ⟨w2, u, hx, hfin⟩
      · cases heq
    · split at heq <;> cases heq
  · cases h

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- A returning run from a world satisfying a kept predicate ends in one. -/
theorem keeps_runs {α : Type} {I : Void IO.RealWorld → Prop} {m : MetaM α}
    (hk : Keeps mctx mref cctx cref I m) {w : Void IO.RealWorld} {a : α}
    {w' : Void IO.RealWorld} (hw : I w) (h : RunsTo m mctx mref cctx cref w a w') : I w' := by
  have := (hk w hw).1
  rwa [endW_of_runs h] at this

/-! ## The prefix invariant with the cache value -/

/-- `InvC`, and the cache's value is `mb`. -/
def InvM (L : RefLaws mref cref) (mb : Std.HashMap Name Res) (C Dp : Prop)
    (w : Void IO.RealWorld) : Prop :=
  InvC L C Dp w ∧ L.val w = mb

theorem invM_pure (L : RefLaws mref cref) {mb : Std.HashMap Name Res} {C Dp : Prop}
    {α : Type} {a b : α} {w w' : Void IO.RealWorld}
    (h : RunsTo (Pure.pure a : MetaM α) mctx mref cctx cref w b w') (hw : InvM L mb C Dp w) :
    InvM L mb C Dp w' := by
  refine ⟨inv_pure L h hw.1, ?_⟩
  rw [(RunsTo.pure_world h).2]
  exact hw.2

/-- A framed or diagnostic operation's successful run. -/
theorem invM_framed (L : RefLaws mref cref) {mb : Std.HashMap Name Res} {C Dp : Prop}
    {α : Type} {p : MetaM α} {w : Void IO.RealWorld} {a : α} {w' : Void IO.RealWorld}
    (h : RunsTo p mctx mref cctx cref w a w') (hw : InvM L mb C Dp w)
    (hp : Op p := by first
      | exact Op.framed (Framed.sideSet _ (by constructor))
      | exact Op.framed (Framed.sideGet (by constructor))
      | exact Op.framed (Framed.sideModify _ (by constructor))
      | exact Op.framed (by constructor)
      | exact Op.diag (by constructor)) : InvM L mb C Dp w' := by
  refine ⟨inv_framed L h hw.1 hp, ?_⟩
  rw [(L.sameOp hp h hw.1.2.2.1).1.1]
  exact hw.2

theorem invM_depthSet (L : RefLaws mref cref) {mb : Std.HashMap Name Res} {C Dp : Prop}
    {v : Nat} {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (h : RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w')
    (hw : InvM L mb C Dp w) : InvM L mb C (v ≠ 0) w' := by
  refine ⟨inv_depthSet L h hw.1, ?_⟩
  rw [(L.depthSet _ _ _ _ h).1]
  exact hw.2

/-- The depth's `modify` leaves the cache and the synthesis ref (nothing is
kept about the depth). -/
theorem invM_depthModify (L : RefLaws mref cref) {mb : Std.HashMap Name Res} {C Dp : Prop}
    {f : Nat → Nat} {w : Void IO.RealWorld} {u : Unit} {w' : Void IO.RealWorld}
    (h : RunsTo (ST.Ref.modify sparkleSynthDepth f : MetaM Unit) mctx mref cctx cref w u w')
    (hw : InvM L mb C Dp w) : InvM L mb C False w' := by
  obtain ⟨hv, hs, -⟩ := L.depthModify _ _ _ _ h
  refine ⟨⟨?_, ?_, L.depthModifyQ _ _ _ _ h hw.1.2.2.1, fun f => f.elim⟩, ?_⟩
  · rw [hv]
    exact hw.1.1
  · rw [hs]
    exact hw.1.2.1
  · rw [hv]
    exact hw.2

/-- The lemma carrying `InvM` over one step, by the step's head. -/
meta def stepLemmaV (prog : Lean.Expr) : Lean.MetaM (Lean.TSyntax `term) := do
  let prog ← Lean.instantiateMVars prog
  if prog.isAppOf ``Pure.pure then return ← `(invM_pure)
  if prog.isAppOf ``ST.Ref.set then
    if (prog.getAppArgs.find? (·.isConstOf ``sparkleSynthDepth)).isSome then
      return ← `(invM_depthSet)
  return ← `(invM_framed)

/-- One bind of the prefix, `InvM` carried to the next world (the text of
`peel_inv`). -/
elab "peel_val " L:term:max h:ident hw:ident : tactic => do
  match ← runHeadIs h.getId ``Bind.bind with
  | some true =>
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      obtain ⟨_, _, $(Lean.mkIdent `step):ident, $h:ident⟩ := RunsTo.bind $h:ident))
    let lem ← Lean.Elab.Tactic.withMainContext do
      let d ← Lean.Meta.getLocalDeclFromUserName `step
      stepLemmaV (← Lean.instantiateMVars d.type).getAppArgs[1]!
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      (have $hw:ident := $lem $L $(Lean.mkIdent `step):ident $hw
       clear $(Lean.mkIdent `step):ident)))
  | _ => throwError "head is not a bind"

/-! ## The entry's prefix and `finally`, at positive depth -/

/-- **The core entry at positive depth, with its worlds.** `core_reads_inv`,
and: the body (`synthesizeFromConst`) starts with the run's start cache —
the prefix reads, resets other refs and bumps the depth; at a positive depth
it does not clear — and the run ends with the cache the body ends with (the
`finally`: the depth, the other refs). -/
theorem core_reads_val (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {declName : Name} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module}
    {D : Sparkle.IR.AST.Design} (hw : InvV L w) (hdw : L.dval w ≠ 0)
    (h : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (b : Bool) (envR : Environment) (ci : ConstantInfo)
      (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire e h t n) (profLogIO b)
        declName [] false true
        (entryConst true false [] ci (Sparkle.Compiler.Elab.instancePredicate envR)
          (userInliner envR) (structEnv envR))
        (Sparkle.Compiler.Elab.instancePredicate envR))
        mctx mref cctx cref w3 (M, D) w4 ∧ InvV L w3 ∧ L.dval w3 ≠ 0 ∧
      L.val w3 = L.val w ∧ InvV L w4 ∧ L.val w' = L.val w4 := by
  have hq : L.quiet w := hw.2.2
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
  -- nested: no clear
  have h0 : ¬ (d == 0) = true := by
    rw [hd]
    simpa using hdw
  have hwM : InvM L (L.val w) True False wc :=
    ⟨invC_keep L keep ⟨fun _ => hw.1, hw.2.1, hq, fun f => f.elim⟩, keep.1.1⟩
  simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
  iterate 40 (first | peel_val L h hwM | skip)
  obtain ⟨w4, u, h, hfin⟩ := tryFinally_fin h
  obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
  have hwM := invM_framed L hget hwM (Op.framed (.constInfo _))
  obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
  have hwM := invM_framed L henv hwM (Op.framed .env)
  have hw3 := invV_of_invC L hwM.1
  have hd3 := hwM.1.2.2.2 (Nat.succ_ne_zero _)
  -- the body keeps the invariant: the world the `finally` starts in
  have hJ := keeps_runs
    (hB L.plain _ (childKeeps_all L.plain (hB _) _ (fun _ => trivial)) mctx cctx prof.isSome
      declName _ _)
    (show J L.plain _ _ from ⟨hw3, rfl, trivial⟩) h
  have hw4 : InvV L w4 := hJ.1
  have hf0 : InvM L (L.val w4) True False w4 :=
    ⟨⟨fun _ => hw4.1, hw4.2.1, hw4.2.2, fun f => f.elim⟩, rfl⟩
  -- the `finally`: the depth's release, then the other refs
  obtain ⟨_, wf, hmodf, hfin⟩ := RunsTo.bind hfin
  have hwf := invM_depthModify L hmodf hf0
  have hvf : L.val w' = L.val w4 := by
    first
      | (rcases RunsTo.ite hfin with hfin | hfin
         · iterate 10 (first | peel_val L hfin hwf | skip)
           exact (invM_framed L hfin hwf).2
         · rw [(RunsTo.pure_world hfin).2]
           exact hwf.2)
      | (iterate 10 (first | peel_val L hfin hwf | skip)
         exact (invM_framed L hfin hwf).2)
  exact ⟨prof.isSome, env, ci, _, w2, _, _, _, _, hget, henv, h, hw3, hd3, hwM.2, hw4, hvf⟩

/-! ## The machine arm of `synthesizeFromConst`, with its worlds -/

/-- **`synthesizeFromConst_machine_inv` with the cache values**: the machine
synthesis starts with the arm's start cache; when it returns a module from a
quiet world, that module is the arm's result and the arm ends with the
machine synthesis's end cache (the log line and the memo insert leave it). -/
theorem sfc_machine_val (L : RefLaws mref cref) {b : Bool} {declName : Name}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none) (hw : InvV L w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire e h t n) (profLogIO b)
      declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR : Environment) (w5 w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ r w7 w8, RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName
            shape) mctx mref cctx cref w7 r w8 ∧ InvV L w7 ∧ L.dval w7 = L.dval w ∧
          L.val w7 = L.val w ∧
          ∀ res, r = some res → L.quiet w8 → res = (m, d) ∧ L.val w' = L.val w8 := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, miss, Bool.not_false, Bool.and_self, List.isEmpty_nil] at hr
  obtain ⟨envR, w1, henv, hr⟩ := RunsTo.bind hr
  have hw1 := invV_framed L .env henv hw
  obtain ⟨mach, w2, hp, hr⟩ := RunsTo.bind hr
  obtain ⟨hm, rfl⟩ := RunsTo.pure_world hp
  subst hm
  refine ⟨envR, _, _, henv, ?_⟩
  intro shape hs
  rw [hs] at hr
  dsimp only at hr
  obtain ⟨r, w3, hmach, hr⟩ := RunsTo.bind hr
  refine ⟨r, _, _, hmach, hw1, (L.same .env henv).2.2, (L.same .env henv).1, ?_⟩
  intro res hres hq
  subst hres
  dsimp only at hr
  obtain ⟨_, wa, hlog, hr⟩ := RunsTo.bind hr
  obtain ⟨⟨hva, -, -⟩, -⟩ := L.sameD (.profLog _ _) hlog hq
  obtain ⟨_, wb, hmod, hr⟩ := RunsTo.bind hr
  have hvb := (L.same (.sideModify _ .subModule) hmod).1
  obtain ⟨he, hww⟩ := RunsTo.pure_world hr
  refine ⟨he.symm, ?_⟩
  rw [hww, hvb, hva]

/-! ## `CoreVia` -/

/-- **`CoreVia` is a theorem**, from the route premises: what a run reads of
the declaration (`MachineDefines`, in the run's contexts) and that the
machine synthesis does not fall back (`MachineClosesAt`). -/
theorem coreVia_of (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hH : ∀ L' : RefLaws mref cref, HarnessRel L') {c : Name} {shape : MachineShape}
    (entry : ∀ (mctx : Meta.Context) (cctx : Core.Context),
      MachineDefines mctx mref cctx cref c shape)
    (closes : ∀ (mctx : Meta.Context) (cctx : Core.Context),
      MachineClosesAt mctx mref cctx cref c shape) : CoreVia L c shape := by
  intro mctx cctx w M D w' hw hd hr
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, hget, henv, run, hw3, hd3, hv3, hw4, hv4⟩ :=
    core_reads_val L hB hw hd hr
  obtain ⟨old, miss, _⟩ := entry mctx cctx _ _ _ _ _ _ _ _ _ hget henv henv
  obtain ⟨envR', w7, w8, henv', hmach⟩ := sfc_machine_val L old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry mctx cctx _ _ _ _ _ _ _ _ _ hget henv henv'
  obtain ⟨r, w9, w10, hrun, hw9, hd9, hv9, hres⟩ := hmach shape hshape
  have hd9' : L.dval w9 ≠ 0 := by
    rw [hd9]
    exact hd3
  have hne := closes mctx cctx b _ _ _ (invW_of_invV L hw9) (depthPos_of L hd9') hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have hJ := keeps_runs
      (machine_keeps (mctx := mctx) (cctx := cctx) L.plain (hH _) (L.dval w9)
        (childKeeps_all L.plain (hB _) _ (fun _ => trivial)) b c shape)
      (show J L.plain _ _ from ⟨hw9, rfl, trivial⟩) hrun
    have hq10 : L.quiet w10 := hJ.1.2.2
    obtain ⟨he, hv10⟩ := hres res rfl hq10
    subst he
    exact ⟨b, w9, w10, hrun, hw9, hd9', hv9.trans hv3, hv4.trans hv10⟩

end Tools.ShippingCacheCoherentVia
