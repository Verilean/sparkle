import Tools.ShippingCallsClose

variable {tenv : Lean.Environment}

/-! # Two calls of one declaration get one module — from the run's order

`ChildrenReal` says each child is SOME real compile of its declaration; two
real compiles of one declaration are not known to be equal. What makes two
instances of one child the same module is the child cache, in the order the
closing's `mapM` runs:

* `synthesizeChild_post`: a run of the memoised entry from an invariant world
  leaves its result in the cache under the declaration's name, and returns
  the cached value when there is one (a hit);
* `synthesizeChild_pin`: from a world of POSITIVE synthesis depth, a run of
  the memoised entry keeps every entry the cache has (the invariance theorem
  with the auxiliary predicate "the cache holds `y0` under `c0`": a miss
  inserts under a key that was absent; the clear is the depth-0 entry's and
  does not happen under a positive depth);
* `mapM_loop_all` / `closeInstsM_run_all`: so in the closing's `mapM`, two
  calls of one declaration — with any calls between — get the same child: the
  later is a hit of the entry the earlier left.

The depth is positive where a real compile runs the machine synthesis
(`MachineClosesAt` asks its worlds to be inside an entry: `DepthPos`). -/
namespace Tools.ShippingCallsSame
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInv
open Sparkle.Compiler.Elab

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A run of the memoised entry**: a real child, the invariant kept, the
result in the cache, and the cached value on a hit. -/
theorem synthesizeChild_post (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {c : Name} {w w' : Void IO.RealWorld} {y : Res}
    (hw : InvV L w) (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    RealChild mref cref c y ∧ InvV L w' ∧ (L.val w').get? c = some y ∧
      ∀ y0, (L.val w).get? c = some y0 → y = y0 := by
  obtain ⟨hr, hw'⟩ := synthesizeChild_inv L hB hw h
  unfold synthesizeChild at h
  obtain ⟨m, w1, hget, h⟩ := RunsTo.bind h
  obtain ⟨hm, hv, -⟩ := L.get hget
  cases hc : m.get? c with
  | some r =>
    simp only [hc] at h
    obtain ⟨hry, hww⟩ := RunsTo.pure_world h
    rw [hm] at hc
    refine ⟨hr, hw', ?_, fun y0 h0 => ?_⟩
    · rw [hww, hv, hc, hry]
    · rw [h0] at hc
      exact hry.trans (Option.some.inj hc).symm
  | none =>
    simp only [hc] at h
    obtain ⟨r, w2, hrun, h⟩ := RunsTo.bind h
    obtain ⟨u, w3, hmod, h⟩ := RunsTo.bind h
    obtain ⟨hv3, -, -⟩ := L.cacheModify _ _ _ _ hmod
    obtain ⟨hry, hww⟩ := RunsTo.pure_world h
    refine ⟨hr, hw', ?_, fun y0 h0 => ?_⟩
    · rw [hww, hv3, hry]
      simp
    · rw [hm] at hc
      rw [hc] at h0
      cases h0

/-- The harness keeps the synthesis depth. -/
theorem harness_depth (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    (hH : ∀ L' : RefLaws mref cref, HarnessRel L') {b : Bool} {declName bs body}
    {w r w'} (hw : InvV L w)
    (h : RunsTo (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName bs body)
      mctx mref cctx cref w r w') : L.dval w' = L.dval w := by
  have := hH L.plain (L.dval w) (childKeeps_all L.plain (hB _) _ (fun _ => trivial)) mctx cctx b
    declName bs body w ⟨hw, rfl, trivial⟩
  rw [endW_of_runs h] at this
  exact this.1.2.1

/-! ## One witness: nothing is mixed

`InvV L w`, `StartV L w`, `J L D w` are statements about ONE law witness `L`
(its `val`, `sval`, `dval`, `quiet`). `invW_of_invV L` packs `L` itself as the
world's quiet witness, and `invV_of_invW` hands back a witness with ITS OWN
invariant — the four readings are never taken from two witnesses. Changing
the auxiliary predicate changes none of them. -/

theorem withAux_val (L : RefLaws mref cref) (A hA) : (L.withAux A hA).val = L.val := rfl
theorem withAux_sval (L : RefLaws mref cref) (A hA) : (L.withAux A hA).sval = L.sval := rfl
theorem withAux_dval (L : RefLaws mref cref) (A hA) : (L.withAux A hA).dval = L.dval := rfl
theorem withAux_quiet (L : RefLaws mref cref) (A hA) : (L.withAux A hA).quiet = L.quiet := rfl

/-- The invariant by the values does not depend on the auxiliary predicate. -/
theorem invV_withAux (L : RefLaws mref cref) (A hA) (w : Void IO.RealWorld) :
    InvV (L.withAux A hA) w ↔ InvV L w := Iff.rfl

/-- A witness's invariant world, read back: SOME witness with its own
invariant there (the one `invW_of_invV` packed is such a witness). -/
theorem invV_of_invW_of_invV (mctx : Meta.Context) (cctx : Core.Context) (L : RefLaws mref cref)
    {w : Void IO.RealWorld} (h : InvV L w) : ∃ L' : RefLaws mref cref, InvV L' w :=
  invV_of_invW mctx cctx (invW_of_invV L h)

/-! ## An existing entry survives a child's synthesis — at a positive depth -/

/-- The cache holds `y0` under `c0`. -/
def pin (c0 : Name) (y0 : Res) (m : Std.HashMap Name Res) : Prop := m.get? c0 = some y0

/-- A miss inserts under a key the map did not have: not `c0`. -/
theorem pin_insert (c0 : Name) (y0 : Res) :
    ∀ (m0 m1 : Std.HashMap Name Res) (n : Name) (r : Res),
      pin c0 y0 m0 → m0.get? n = none → pin c0 y0 m1 → pin c0 y0 (m1.insert n r) := by
  intro m0 m1 n r h0 hn h1
  unfold pin at *
  rw [Std.HashMap.get?_insert]
  split
  · rename_i heq
    have : n = c0 := by simpa using heq
    subst this
    rw [hn] at h0
    cases h0
  · exact h1

/-- **A run of the memoised entry keeps every entry the cache has** — for any
fixed key and value — from a world of POSITIVE synthesis depth: the invariance
theorem at the laws with the auxiliary predicate "the cache holds `y0` under
`c0`". (At depth 0 it is false: the entry clears the cache; that case is the
premise `D = 0 → aux {}` of the invariance theorem, here vacuous.) The depth
is kept. -/
theorem synthesizeChild_pin (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {c c0 : Name} {y0 y : Res} {w w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w ≠ 0) (hp : (L.val w).get? c0 = some y0)
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') :
    (L.val w').get? c0 = some y0 ∧ L.dval w' = L.dval w := by
  have := childKeeps_all (L.withAux (pin c0 y0) (pin_insert c0 y0)) (hB _) (L.dval w)
    (fun h => absurd h hd) mctx cctx c w ⟨hw, rfl, hp⟩
  rw [endW_of_runs h] at this
  exact ⟨this.1.2.2, this.1.2.1⟩

/-- The depth is kept by a run of the memoised entry. -/
theorem synthesizeChild_depth (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {c : Name} {y : Res} {w w' : Void IO.RealWorld} (hw : InvV L w)
    (h : RunsTo (synthesizeChild c) mctx mref cctx cref w y w') : L.dval w' = L.dval w := by
  have := childKeeps_all L.plain (hB _) (L.dval w) (fun _ => trivial) mctx cctx c w
    ⟨hw, rfl, trivial⟩
  rw [endW_of_runs h] at this
  exact this.1.2.1

/-- **A `mapM` of the memoised entry, from a world of positive depth**: each
result a real child, and two calls of one key get the same result — the later
one is a hit of the entry the earlier left, which every call between kept. -/
theorem mapM_loop_all {α : Type} (f : α → MetaM Res) (key : α → Name) (L : RefLaws mref cref)
    (hf : ∀ x w y w', InvV L w → L.dval w ≠ 0 → RunsTo (f x) mctx mref cctx cref w y w' →
      RealChild mref cref (key x) y ∧ InvV L w' ∧ L.dval w' = L.dval w ∧
        (L.val w').get? (key x) = some y ∧
        (∀ y0, (L.val w).get? (key x) = some y0 → y = y0) ∧
        (∀ c0 y0, (L.val w).get? c0 = some y0 → (L.val w').get? c0 = some y0)) :
    ∀ (l : List α) (acc r : List Res) w w', InvV L w → L.dval w ≠ 0 →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧ RealChild mref cref (key l[k]) y) ∧
        (∀ (k : Nat) (c : Name) (y0 : Res), (l.map key)[k]? = some c → (L.val w).get? c = some y0 →
          ys[k]? = some y0) ∧
        (∀ (i j : Nat) (c : Name), i < j → (l.map key)[i]? = some c → (l.map key)[j]? = some c →
          ys[i]? = ys[j]?) ∧
        InvV L w'
  | [], acc, r, w, w', hp, _, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero k),
      fun k c y0 hc => by simp at hc, fun i j c _ hc => by simp at hc, hp⟩
  | x :: xs, acc, r, w, w', hp, hd, h => by
    obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
    obtain ⟨hreal, hp1, hd1, hin, hhit, hkeep⟩ := hf x w y w1 hp hd hy
    obtain ⟨ys, hr, hlen, hget, hpinned, hpair, hp'⟩ :=
      mapM_loop_all f key L hf xs (y :: acc) r w1 w' hp1 (by rw [hd1]; exact hd) h
    refine ⟨y :: ys, by simp [hr], by simp [hlen], fun k hk => ?_, ?_, ?_, hp'⟩
    · cases k with
      | zero => exact ⟨y, rfl, hreal⟩
      | succ k => exact hget k (by simpa using hk)
    · intro k c y0 hc h0
      cases k with
      | zero =>
        simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hc
        subst hc
        rw [hhit y0 h0]
        rfl
      | succ k =>
        simp only [List.getElem?_cons_succ]
        exact hpinned k c y0 (by simpa using hc) (hkeep c y0 h0)
    · intro i j c hij hi hj
      cases j with
      | zero => omega
      | succ j =>
        cases i with
        | zero =>
          simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          have := hpinned j (key x) y (by simpa using hj) hin
          simp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
          exact this.symm
        | succ i =>
          simp only [List.getElem?_cons_succ]
          exact hpair i j c (by omega) (by simpa using hi) (by simpa using hj)

/-- **A run of the one-output closing, from an invariant world of positive
depth**: the pure closing of real children, two calls of one declaration
getting the same child. -/
theorem closeInstsM_run_all (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape t m₀ d₀ r} {w w'} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) ∧
      ChildrenReal mref cref shape children ∧
      (∀ (i j : Nat) (c : Name), i < j → (shape.insts.map (·.1))[i]? = some c →
        (shape.insts.map (·.1))[j]? = some c → children[i]? = children[j]?) ∧ InvV L w' := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  have hd1 : L.dval w1 ≠ 0 := by rw [(L.same .synthGet hget).2.2]; exact hd
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨ys, hys, hlen, hk, -, hpair, hw2⟩ := mapM_loop_all _
    (fun (x : Name × List Nat × MixedGateBinder) => x.1) L
    (fun x w y w' hp hdw hy => by
      obtain ⟨h1, h2, h3, h4⟩ := synthesizeChild_post L hB hp hy
      exact ⟨h1, h2, synthesizeChild_depth L hB hp hy, h3, h4,
        fun c0 y0 h0 => (synthesizeChild_pin L hB hp hdw h0 hy).1⟩)
    shape.insts [] children w1 _ hw1 hd1 hch
  simp only [List.reverse_nil, List.nil_append] at hys
  subst hys
  exact ⟨children, heq, ⟨hlen, fun k hkl => by
    obtain ⟨y, hy, hre⟩ := hk k hkl
    exact ⟨y, hy, Or.inr hre⟩⟩, hpair, hw2⟩

end Tools.ShippingCallsSame
