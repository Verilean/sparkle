import Tools.ShippingChildBody

variable {tenv : Lean.Environment}

/-! # A successful run of the real entry: what its closings receive

Inversion of ONE returning run of the core entry that starts in a world
satisfying the start condition (`StartW`: the synthesis ref, and depth 0 or
the cache invariant): the invariant is established by the prefix
(`core_reads_inv` — at depth 0 by the clear, from any cache; nested, by
inheritance), carried through the machine route's prefix and its harness
(`harness_inv`; the harness is proved from the translator's condition,
`harnessRel_of`, and the entry's recursion, `Tools/ShippingChildKeeps.lean`), and the closings' children are then
`RealChild`s, call by call (`machine_children_real`). The logger the entry
hands on is its own (`profLogIO b`).

Scope of the `Name` key: a cached `RealChild c r` says `r` came from SOME
real run on `c` in these contexts, starting in an invariant world — not that
a fresh run in the current world (whose environment may differ) would return
it. Consumers use it only together with the child's reflection facts, which
hold for every world of the contexts. -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- The invariant with a CONDITIONAL cache half: the synthesis ref's value,
and the cache's entries when `C` holds. `InvC L True` is `InvV L`; `InvC L
False` is the synthesis ref alone (what an outermost run starts from). -/
def InvC (L : RefLaws mref cref) (C Dp : Prop) (w : Void IO.RealWorld) : Prop :=
  (C → CacheInv mref cref (L.val w)) ∧ L.sval w = some synthesizeChild ∧ L.quiet w ∧
    (Dp → L.dval w ≠ 0)

theorem invV_of_invC (L : RefLaws mref cref) {Dp : Prop} {w} (h : InvC L True Dp w) : InvV L w :=
  ⟨h.1 trivial, h.2.1, h.2.2.1⟩

/-- The values are left and the end world is quiet (an operation's successful
run from a quiet world: `RefLaws.sameOp`). -/
theorem invC_keep (L : RefLaws mref cref) {C Dp : Prop} {w w'}
    (hk : (L.val w' = L.val w ∧ L.sval w' = L.sval w ∧ L.dval w' = L.dval w) ∧ L.quiet w')
    (h : InvC L C Dp w) : InvC L C Dp w' := by
  unfold InvC; rw [hk.1.1, hk.1.2.1, hk.1.2.2]; exact ⟨h.1, h.2.1, hk.2, h.2.2.2⟩

/-- A generic operation's successful run keeps the invariant. -/
theorem invC_framed (L : RefLaws mref cref) {C Dp : Prop} {α : Type} {p : MetaM α} (hp : Framed p)
    {w a w'} (h : RunsTo p mctx mref cctx cref w a w') (hw : InvC L C Dp w) : InvC L C Dp w' :=
  invC_keep L (L.sameOp (.framed hp) h hw.2.2.1) hw

theorem invV_keep (L : RefLaws mref cref) {w w'}
    (hk : (L.val w' = L.val w ∧ L.sval w' = L.sval w ∧ L.dval w' = L.dval w) ∧ L.quiet w')
    (h : InvV L w) : InvV L w' := by
  unfold InvV; rw [hk.1.1, hk.1.2.1]; exact ⟨h.1, h.2.1, hk.2⟩


theorem invV_framed (L : RefLaws mref cref) {α : Type} {p : MetaM α} (hp : Framed p)
    {w a w'} (h : RunsTo p mctx mref cctx cref w a w') (hw : InvV L w) : InvV L w' :=
  invV_keep L (L.sameOp (.framed hp) h hw.2.2) hw

/-! ## One step of the prefix -/

theorem inv_pure (L : RefLaws mref cref) {C Dp : Prop} {α : Type} {a b : α} {w w'}
    (h : RunsTo (Pure.pure a : MetaM α) mctx mref cctx cref w b w') (hw : InvC L C Dp w) :
    InvC L C Dp w' := by
  rw [(RunsTo.pure_world h).2]; exact hw

/-- A framed operation's successful run. -/
theorem inv_framed (L : RefLaws mref cref) {C Dp : Prop} {α : Type} {p : MetaM α}
    {w a w'} (h : RunsTo p mctx mref cctx cref w a w') (hw : InvC L C Dp w)
    (hp : Op p := by first
      | exact Op.framed (Framed.sideSet _ (by constructor))
      | exact Op.framed (Framed.sideGet (by constructor))
      | exact Op.framed (Framed.sideModify _ (by constructor))
      | exact Op.framed (by constructor)
      | exact Op.diag (by constructor)) : InvC L C Dp w' :=
  invC_keep L (L.sameOp hp h hw.2.2.1) hw

/-- The depth's set leaves the cache and the synthesis ref — and from then on
the depth is the value set (nonzero when that is). -/
theorem inv_depthSet (L : RefLaws mref cref) {C Dp : Prop} {v : Nat} {w u w'}
    (h : RunsTo (ST.Ref.set sparkleSynthDepth v : MetaM Unit) mctx mref cctx cref w u w')
    (hw : InvC L C Dp w) : InvC L C (v ≠ 0) w' := by
  obtain ⟨hv, hs, hd⟩ := L.depthSet _ _ _ _ h
  unfold InvC; rw [hv, hs, hd]; exact ⟨hw.1, hw.2.1, L.depthSetQ _ _ _ _ h hw.2.2.1, fun h => h⟩

/-- **The depth-0 clear ESTABLISHES the cache half**, from any cache: only
the synthesis ref's value is carried over. -/
theorem inv_clear (L : RefLaws mref cref) {C Dp : Prop} {w u w'}
    (h : RunsTo (sparkleChildCache.set {} : MetaM Unit) mctx mref cctx cref w u w')
    (hw : InvC L C Dp w) : InvC L True Dp w' := by
  obtain ⟨hv, hs, hd⟩ := L.cacheSet _ _ _ _ h
  refine ⟨fun _ => ?_, ?_, L.cacheSetQ _ _ _ _ h hw.2.2.1, ?_⟩
  · rw [hv]; exact cacheInv_empty
  · rw [hs]; exact hw.2.1
  · rw [hd]; exact hw.2.2.2

/-- The lemma carrying the invariant over one step, by the step's head. -/
meta def stepLemma (prog : Lean.Expr) : Lean.MetaM (Lean.TSyntax `term) := do
  let prog ← Lean.instantiateMVars prog
  if prog.isAppOf ``Pure.pure then return ← `(inv_pure)
  if prog.isAppOf ``ST.Ref.set then
    if (prog.getAppArgs.find? (·.isConstOf ``sparkleChildCache)).isSome then return ← `(inv_clear)
    if (prog.getAppArgs.find? (·.isConstOf ``sparkleSynthDepth)).isSome then
      return ← `(inv_depthSet)
  return ← `(inv_framed)

/-- One bind of the prefix, the invariant carried to the next world. -/
elab "peel_inv " L:term:max h:ident hw:ident : tactic => do
  match ← runHeadIs h.getId ``Bind.bind with
  | some true =>
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      obtain ⟨_, _, $(Lean.mkIdent `step):ident, $h:ident⟩ := RunsTo.bind $h:ident))
    let lem ← Lean.Elab.Tactic.withMainContext do
      let d ← Lean.Meta.getLocalDeclFromUserName `step
      stepLemma (← Lean.instantiateMVars d.type).getAppArgs[1]!
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      (have $hw:ident := $lem $L $(Lean.mkIdent `step):ident $hw
       clear $(Lean.mkIdent `step):ident)))
  | _ => throwError "head is not a bind"

/-- **The entry's prefix ESTABLISHES the invariant** from the start condition.
The run reads the profile variable, logs, and reads the synthesis depth `d`
(none of which touches the three values). If `d = 0` it clears the cache —
which establishes the cache half from ANY cache (`inv_clear`), so only the
synthesis ref's value is needed at the start; otherwise the run is nested and
the start condition's cache half is carried through the other refs' resets.
Then the depth bump, the `try`, `getConstInfo` and `getEnv`. The logger the
entry hands on is its own, `profLogIO b`. -/
theorem core_reads_inv (L : RefLaws mref cref) {declName : Name}
    {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hw : StartV L w) (hq : L.quiet w)
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
        mctx mref cctx cref w3 (M, D) w4 ∧ InvV L w3 ∧ L.dval w3 ≠ 0 := by
  unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨prof, wa, s1, h⟩ := RunsTo.bind h
  obtain ⟨_, wb, s2, h⟩ := RunsTo.bind h
  obtain ⟨d, wc, s3, h⟩ := RunsTo.bind h
  -- the profile logger is a diagnostic operation: its frame is asked in the
  -- quiet start world
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
  by_cases h0 : (d == 0) = true
  · -- outermost: the clear establishes the cache half
    have hw : InvC L False False wc := invC_keep L keep ⟨fun f => f.elim, hw.1, hq, fun f => f.elim⟩
    simp only [h0, ↓reduceIte] at h
    iterate 40 (first | peel_inv L h hw | skip)
    obtain ⟨_, h⟩ := RunsTo.try_finally h
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := invC_framed L (.constInfo _) hget hw
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := invC_framed L .env henv hw
    exact ⟨prof.isSome, env, ci, _, w2, _, _, _, _, hget, henv, h, invV_of_invC L hw,
      hw.2.2.2 (Nat.succ_ne_zero _)⟩
  · -- nested: the start condition's cache half is inherited
    have hc : CacheInv mref cref (L.val w) := by
      rcases hw.2 with hz | hc
      · exact absurd (by rw [hd, hz]; rfl) h0
      · exact hc
    have hw : InvC L True False wc := invC_keep L keep ⟨fun _ => hc, hw.1, hq, fun f => f.elim⟩
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
    iterate 40 (first | peel_inv L h hw | skip)
    obtain ⟨_, h⟩ := RunsTo.try_finally h
    obtain ⟨ci, w2, hget, h⟩ := RunsTo.bind h
    have hw := invC_framed L (.constInfo _) hget hw
    obtain ⟨env, w2b, henv, h⟩ := RunsTo.bind h
    have hw := invC_framed L .env henv hw
    exact ⟨prof.isSome, env, ci, _, w2, _, _, _, _, hget, henv, h, invV_of_invC L hw,
      hw.2.2.2 (Nat.succ_ne_zero _)⟩

/-! ## The memoised entry and the closings -/

/-- **The memoised entry, world by world.** A hit returns a cached entry (a
`RealChild` by the invariant) and leaves the world's values; a miss runs the
real entry from a world satisfying the invariant (so its result is a
`RealChild`; the run keeps the invariant, `entry_inv`) and then modifies the
cache AS IT IS after that run, inserting the result. -/
theorem synthesizeChild_inv (L : RefLaws mref cref)
    (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {c : Name} {w w' : Void IO.RealWorld} {y : Res}
    (hw : InvV L w) (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    RealChild mref cref c y ∧ InvV L w' := by
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hv, hs⟩ := L.get hget
  have hw1 : InvV L w1 := invV_framed L .cacheGet hget hw
  cases hc : m.get? c with
  | some r =>
    simp only [hc] at h
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    refine ⟨?_, hw1⟩
    rw [hm] at hc
    exact hw.1 c _ hc
  | none =>
    simp only [hc] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    have hW1 := invW_of_invV L hw1
    have hw2 := entry_inv L hB hw1 hrun
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    obtain ⟨hv3, hs3, _⟩ := L.cacheModify _ _ _ _ hmod
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    have hr : RealChild mref cref c y :=
      RealChild.of_inv hW1 hrun
    refine ⟨hr, ?_, ?_, L.cacheModifyQ _ _ _ _ hmod hw2.2.2⟩
    · rw [hv3]; exact cacheInv_insert hw2.1 hr
    · rw [hs3]; exact hw2.2.1

/-- A `List.mapM` run whose steps keep `P` and establish `Q` of each result. -/
theorem mapM_loop_hoare {α β : Type} (f : α → MetaM β) (P : Void IO.RealWorld → Prop)
    (Q : α → β → Prop)
    (hf : ∀ x w y w', P w → RunsTo (f x) mctx mref cctx cref w y w' → Q x y ∧ P w') :
    ∀ (l : List α) (acc r : List β) w w', P w →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧ Q l[k] y) ∧ P w'
  | [], acc, r, w, w', hp, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero k), hp⟩
  | x :: xs, acc, r, w, w', hp, h => by
    obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
    obtain ⟨hq, hp1⟩ := hf x w y w1 hp hy
    obtain ⟨ys, hr, hlen, hget, hp'⟩ := mapM_loop_hoare f P Q hf xs (y :: acc) r w1 w' hp1 h
    refine ⟨y :: ys, by simp [hr], by simp [hlen], fun k hk => ?_, hp'⟩
    cases k with
    | zero => exact ⟨y, rfl, hq⟩
    | succ k =>
      obtain ⟨z, hz, hqz⟩ := hget k (by simpa using hk)
      exact ⟨z, by simpa using hz, by simpa using hqz⟩

theorem mapM_hoare {α β : Type} (f : α → MetaM β) (P : Void IO.RealWorld → Prop)
    (Q : α → β → Prop)
    (hf : ∀ x w y w', P w → RunsTo (f x) mctx mref cctx cref w y w' → Q x y ∧ P w')
    (l : List α) (r : List β) {w w'} (hp : P w)
    (h : RunsTo (l.mapM f) mctx mref cctx cref w r w') :
    r.length = l.length ∧ (∀ k (hk : k < l.length), ∃ y, r[k]? = some y ∧ Q l[k] y) ∧ P w' := by
  obtain ⟨ys, hr, hlen, hget, hp'⟩ := mapM_loop_hoare f P Q hf l [] r w w' hp h
  simp only [List.reverse_nil, List.nil_append] at hr
  subst hr
  exact ⟨hlen, hget, hp'⟩

/-- The synthesis ref's read, in an invariant world: `synthesizeChild`. -/
theorem synthRead (L : RefLaws mref cref) {w s w'} (hw : InvV L w)
    (h : RunsTo (sparkleChildSynth.get : MetaM _) mctx mref cctx cref w s w') :
    s = some synthesizeChild ∧ InvV L w' := by
  exact ⟨(L.synthGet _ _ _ h).trans hw.2.1, invV_framed L .synthGet h hw⟩

/-- **The general closing's children, world by world.** -/
theorem closeInstsGM_inv (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape t m₀ d₀ m d} {w w'} (hw : InvV L w)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) = some (m, d) ∧ MemChildren shape children ∧
      ChildrenReal mref cref shape children ∧ InvV L w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := mapM_hoare _ (InvV L)
    (fun (x : Name × List Nat × MixedGateBinder) y =>
      (∀ md, Sparkle.Compiler.MachMemory.memChild? x.1 = some md → y = md) ∧
      (Sparkle.Compiler.MachMemory.memChild? x.1 = some y ∨ RealChild mref cref x.1 y))
    (fun x w y w' hp hy => by
      obtain ⟨c, b, k'⟩ := x
      dsimp only at hy ⊢
      cases hmc : Sparkle.Compiler.MachMemory.memChild? c with
      | some md =>
        rw [hmc] at hy
        obtain ⟨rfl, rfl⟩ := RunsTo.pure_world hy
        exact ⟨⟨fun md' h => by cases h; rfl, Or.inl rfl⟩, hp⟩
      | none =>
        rw [hmc] at hy
        obtain ⟨hrc, hp'⟩ := synthesizeChild_inv L hB hp hy
        exact ⟨⟨fun md' h => (by cases h), Or.inr hrc⟩, hp'⟩)
    shape.insts children hw1 hch
  refine ⟨children, heq.symm, ?_, ⟨hlen, fun k hkl => ?_⟩, hw2⟩
  · intro k c hc md hmd
    have hkl : k < shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
    obtain ⟨y, hky, hm, _⟩ := hk k hkl
    have hck : (shape.insts[k]).1 = c := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hkl] at hc
      simpa using hc
    rw [← hck] at hmd
    rw [hm md hmd] at hky
    exact hky
  · obtain ⟨y, hky, _, hor⟩ := hk k hkl
    exact ⟨y, hky, hor⟩

/-- **The one-output closing's children, world by world.** -/
theorem closeInstsM_inv (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape t m₀ d₀ m d} {w w'} (hw : InvV L w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w (some (m, d)) w') :
    ∃ children, Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) = some (m, d) ∧
      ChildrenReal mref cref shape children ∧ InvV L w' := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨hlen, hk, hw2⟩ := mapM_hoare _ (InvV L)
    (fun (x : Name × List Nat × MixedGateBinder) y =>
      Sparkle.Compiler.MachMemory.memChild? x.1 = some y ∨ RealChild mref cref x.1 y)
    (fun x w y w' hp hy => by
      obtain ⟨hrc, hp'⟩ := synthesizeChild_inv L hB hp hy
      exact ⟨Or.inr hrc, hp'⟩)
    shape.insts children hw1 hch
  exact ⟨children, heq.symm, ⟨hlen, hk⟩, hw2⟩

/-! ## The machine route -/

/-- `synthesizeFromConst_machine`, the invariant carried to the start of the
machine synthesis. -/
theorem synthesizeFromConst_machine_inv (L : RefLaws mref cref)
    {logProf : String → IO Unit} {declName : Name}
    {ci : ConstantInfo} {isInst : Lean.Expr → Bool} {m : Sparkle.IR.AST.Module}
    {d : Sparkle.IR.AST.Design} {w w' : Void IO.RealWorld}
    (old : certifiedShape? false [] ci = none)
    (miss : mixedCertifiedShape? false [] ci isInst = none) (hw : InvV L w)
    (hr : RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) logProf
      declName [] false true ci isInst) mctx mref cctx cref w (m, d) w') :
    ∃ (envR : Environment) (w5 w6 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 ∧
      ∀ shape, machineShape? false [] ci (structEnv envR) = some shape →
        ∃ r w7 w8, RunsTo (synthesizeMachineCertified
            (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
            shape) mctx mref cctx cref w7 r w8 ∧ InvV L w7 ∧ L.dval w7 = L.dval w ∧
          ∀ res, r = some res → res = (m, d) := by
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
  refine ⟨r, _, _, hmach, hw1, (L.same .env henv).2.2, ?_⟩
  intro res hres
  subst hres
  dsimp only at hr
  have hr := hr.mreturns
  peel_bind hr
  peel_bind hr
  exact (MReturns.pure hr).symm

/-- **The machine synthesis, with its children, from an invariant world.**
The harness keeps the invariant (`harness_inv`); the closings' children are
then `RealChild`s (`closeInstsM_inv` / `closeInstsGM_inv`). -/
theorem synthesizeMachineCertified_inv (L : RefLaws mref cref)
    (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hH : ∀ L' : RefLaws mref cref, HarnessRel L')
    {b : Bool} {declName shape m d} {w w'} (hw : InvV L w)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w') :
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      ((shape.insts = [] ∧ m = Sparkle.IR.Machine.closeMachine shape.layout t' ∧ d = d₀) ∨
       (shape.insts ≠ [] ∧ ∃ children,
          CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
          ChildrenReal mref cref shape children)) := by
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d'⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := harness_inv L hB hH hw run
  dsimp only at hr
  split at hr
  · rename_i t' hcl
    split at hr
    · rename_i hi
      have eq := RunsTo.pure_eq hr
      simp only [Option.some.injEq, Prod.mk.injEq] at eq
      obtain ⟨hm, hd⟩ := eq
      exact ⟨t, t', d', run.mreturns, hcl, Or.inl ⟨hi, hm, hd⟩⟩
    · rename_i hi
      have hne : shape.insts ≠ [] := by rw [hi]; exact List.cons_ne_nil _ _
      split at hr
      · rename_i hf
        obtain ⟨children, hc, hreal, _⟩ := closeInstsM_inv L hB hw1 hr
        exact ⟨t, t', d', run.mreturns, hcl, Or.inr ⟨hne, children,
          Or.inl ⟨List.isEmpty_iff.mp hf, hc⟩, hreal⟩⟩
      · rename_i hf
        obtain ⟨children, hc, hmc, hreal, _⟩ := closeInstsGM_inv L hB hw1 hr
        exact ⟨t, t', d', run.mreturns, hcl, Or.inr ⟨hne, children,
          Or.inr ⟨fun h => hf (List.isEmpty_iff.mpr h), hc, hmc⟩, hreal⟩⟩
  · have eq := RunsTo.pure_eq hr
    cases eq

/-- In world `w` the synthesis depth reads nonzero: `w` is INSIDE an entry's
run (the entry bumps the depth before its body). Where the machine synthesis
runs in a real compile this holds; it is what keeps the cache from being
cleared under the children (the clear is the depth-0 entry's). -/
def DepthPos (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) d w1,
    RunsTo (ST.Ref.get sparkleSynthDepth : MetaM Nat) mctx mref cctx cref w d w1 → d ≠ 0

theorem depthPos_of (L : RefLaws mref cref) {w} (h : L.dval w ≠ 0) : DepthPos mref cref w :=
  fun _ _ d w1 hg => by rw [L.depthGet _ _ _ hg]; exact h

theorem dval_ne_of_depthPos (mctx : Meta.Context) (cctx : Core.Context) (L : RefLaws mref cref)
    {w} (h : DepthPos mref cref w) : L.dval w ≠ 0 := by
  obtain ⟨d, w1, hg⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx) (cref := cref)
    sparkleSynthDepth w
  rw [← L.depthGet _ _ _ hg]
  exact h mctx cctx d w1 hg

/-- **The machine synthesis does not fall back — where a real compile runs
it.** Under the generic runtime laws, from a world satisfying the child-cache
invariant, with the compiler's own logger. `MachineCloses` (every world,
every logger) implies it; for a shape with calls only this form can hold: the
calls' closing reads the child-synthesis reference. -/
def MachineClosesAt (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) (declName : Name)
    (shape : MachineShape) : Prop :=
  ∀ {tenv : Lean.Environment}, ∀ (b : Bool) w r w', InvW mref cref w → DepthPos mref cref w →
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w r w' → r ≠ none

theorem machineClosesAt_of_closes {declName : Name} {shape : MachineShape}
    (h : MachineCloses mctx mref cctx cref declName shape) :
    MachineClosesAt mctx mref cctx cref declName shape :=
  fun {tenv} _ w r w' _ _ hr => h _ w r w' hr

/-- **The children of a real compile, from the run's start world.** One
successful run of the real core entry at the machine boundary, STARTING in a
world satisfying the invariant, returns the closing of its transition with
children that are, call by call, built memory modules or `RealChild`s of the
call's declaration — under the generic laws alone (`ChildLaws`). -/
theorem machine_children_realA {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineClosesAt mctx mref cctx cref declName shape)
    (hb : ChildBnd mref cref w) (hi : shape.insts ≠ []) :
    ∃ t t' d₀ children,
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
      ChildrenReal mref cref shape children := by
  obtain ⟨L, hw, hq⟩ := hb
  have hB : ∀ L' : RefLaws mref cref, Tools.ShippingChildInv.BodyRel L' := fun L' => bodyRel L'
  have hH : ∀ L' : RefLaws mref cref, Tools.ShippingChildInv.HarnessRel L' := fun L' => harnessRel_of L' (translateRel L')
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run, hw3, hd3⟩ :=
    core_reads_inv L hw hq hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  obtain ⟨envR', w7, w8, henv', hmach⟩ := synthesizeFromConst_machine_inv L old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w9, w10, hrun, hw9, hd9, hres⟩ := hmach shape hshape
  have hne := closes b _ _ _ (invW_of_invV L hw9) (depthPos_of L (by rw [hd9]; exact hd3)) hrun
  cases r with
  | none => exact absurd rfl hne
  | some res =>
    have := hres res rfl
    subst this
    obtain ⟨t, t', d₀, _, hcl, hmt⟩ := synthesizeMachineCertified_inv L hB hH hw9 hrun
    rcases hmt with ⟨h0, _, _⟩ | ⟨_, children, hcc, hreal⟩
    · exact absurd h0 hi
    · exact ⟨t, t', d₀, children, hcl, hcc, hreal⟩

/-- `machine_children_realA` from the all-worlds premise. -/
theorem machine_children_real {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineCloses mctx mref cctx cref declName shape)
    (hb : ChildBnd mref cref w) (hi : shape.insts ≠ []) :
    ∃ t t' d₀ children,
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
      ChildrenReal mref cref shape children :=
  machine_children_realA hr entry (machineClosesAt_of_closes closes) hb hi

/-- **The machine synthesis inside a real core run**, from a start world
where the boundary holds: the run of `synthesizeMachineCertified` the entry
performed starts in a world satisfying the invariant. -/
theorem machine_run_of_core {declName : Name} {shape : MachineShape}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (hb : ChildBnd mref cref w) :
    ∃ (tenv : Lean.Environment) (b : Bool) (r : Option Res) (w9 w10 : Void IO.RealWorld),
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
        mctx mref cctx cref w9 r w10 ∧ InvW mref cref w9 ∧ DepthPos mref cref w9 ∧
      ∀ res, r = some res → res = (m, d) := by
  obtain ⟨L, hsv, hq⟩ := hb
  obtain ⟨b, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run, hw3, hd3⟩ :=
    core_reads_inv L hsv hq hr
  obtain ⟨old, miss, _⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv
  obtain ⟨envR', w7, w8, henv', hmach⟩ := synthesizeFromConst_machine_inv L old miss hw3 run
  obtain ⟨_, _, hshape⟩ := entry _ _ _ _ _ _ _ _ _ get henv henv'
  obtain ⟨r, w9, w10, hrun, hw9, hd9, hres⟩ := hmach shape hshape
  exact ⟨_, b, r, w9, w10, hrun, invW_of_invV L hw9, depthPos_of L (by rw [hd9]; exact hd3), hres⟩

/-- `synthesizeMachineCertified_inv` from the read-based invariant. -/
theorem synthesizeMachineCertified_runs {b : Bool} {declName shape m d} {w w'}
    (hw : InvW mref cref w)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w') :
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets shape.layout.lets t = some t' ∧
      ((shape.insts = [] ∧ m = Sparkle.IR.Machine.closeMachine shape.layout t' ∧ d = d₀) ∨
       (shape.insts ≠ [] ∧ ∃ children,
          CloseCalls shape t (Sparkle.IR.Machine.closeMachine shape.layout t') d₀ children m d ∧
          ChildrenReal mref cref shape children)) := by
  obtain ⟨L, hv⟩ := invV_of_invW mctx cctx hw
  have hB : ∀ L' : RefLaws mref cref, Tools.ShippingChildInv.BodyRel L' := fun L' => bodyRel L'
  have hH : ∀ L' : RefLaws mref cref, Tools.ShippingChildInv.HarnessRel L' := fun L' => harnessRel_of L' (translateRel L')
  exact synthesizeMachineCertified_inv L hB hH hv hr

end Tools.ShippingChildInv
