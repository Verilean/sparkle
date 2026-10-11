import Tools.ShippingCallsClose

/-! # Two calls of one declaration get one module — from the run's order

`ChildrenReal` says each child is SOME real compile of its declaration; two
real compiles of one declaration are not known to be equal. What makes two
instances of one child the same module is the child cache, in the order the
closing's `mapM` runs:

* `synthesizeChild_post`: a run of the memoised entry from an invariant world
  leaves its result in the cache under the declaration's name, and returns
  the cached value when there is one (a hit);
* `mapM_loop_adj`: so in a `mapM` of the entry, a call whose declaration is
  the PREVIOUS call's starts in the world that call ended in — a hit — and
  returns the same value;
* `closeInstsM_run_adj`: the one-output closing's children, with that fact;
* `same_of_adj`: for a call list where a declaration's calls are consecutive
  (`sepB`, decided on data), equal declarations give equal children.

NOT covered: equal declarations with OTHER calls between them. Their equality
needs the cache entry to survive the run of the calls between — a miss there
runs a whole child synthesis, and that the synthesis never changes an
existing entry is not among the proved invariants (they are stated for one
invariant, `J`; the entry also clears the cache at depth 0). -/
namespace Tools.ShippingCallsSame
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInv
open Sparkle.Compiler.Elab

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A run of the memoised entry**: a real child, the invariant kept, the
result in the cache, and the cached value on a hit. -/
theorem synthesizeChild_post (L : RefLaws mref cref) (hB : BodyRel L)
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

/-- **A `mapM` of the memoised entry**: each result a real child, and a call
whose key is the previous call's returns the previous result. -/
theorem mapM_loop_adj {α : Type} (f : α → MetaM Res) (key : α → Name) (L : RefLaws mref cref)
    (hf : ∀ x w y w', InvV L w → RunsTo (f x) mctx mref cctx cref w y w' →
      RealChild mref cref (key x) y ∧ InvV L w' ∧ (L.val w').get? (key x) = some y ∧
        ∀ y0, (L.val w).get? (key x) = some y0 → y = y0) :
    ∀ (l : List α) (acc r : List Res) w w', InvV L w →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧ RealChild mref cref (key l[k]) y) ∧
        (∀ c y0, (l.map key)[0]? = some c → (L.val w).get? c = some y0 → ys[0]? = some y0) ∧
        (∀ k c, (l.map key)[k]? = some c → (l.map key)[k + 1]? = some c → ys[k]? = ys[k + 1]?) ∧
        InvV L w'
  | [], acc, r, w, w', hp, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero k),
      fun c y0 hc => by simp at hc, fun k c hc => by simp at hc, hp⟩
  | x :: xs, acc, r, w, w', hp, h => by
    obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
    obtain ⟨hreal, hp1, hin, hhit⟩ := hf x w y w1 hp hy
    obtain ⟨ys, hr, hlen, hget, hhead, hadj, hp'⟩ :=
      mapM_loop_adj f key L hf xs (y :: acc) r w1 w' hp1 h
    refine ⟨y :: ys, by simp [hr], by simp [hlen], fun k hk => ?_, ?_, ?_, hp'⟩
    · cases k with
      | zero => exact ⟨y, rfl, hreal⟩
      | succ k => exact hget k (by simpa using hk)
    · intro c y0 hc h0
      simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      rw [hhit y0 h0]
      rfl
    · intro k c hk hk1
      cases k with
      | zero =>
        simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        have h1 : (xs.map key)[0]? = some (key x) := by simpa using hk1
        have := hhead (key x) y h1 hin
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
        exact this.symm
      | succ k =>
        simp only [List.getElem?_cons_succ]
        exact hadj k c (by simpa using hk) (by simpa using hk1)

/-- **A run of the one-output closing, from an invariant world**: the pure
closing of real children, a call of the previous call's declaration getting
the previous child. -/
theorem closeInstsM_run_adj (L : RefLaws mref cref) (hB : BodyRel L)
    {shape t m₀ d₀ r} {w w'} (hw : InvV L w)
    (hr : RunsTo (closeInstsM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInsts (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        children (m₀, d₀) ∧
      ChildrenReal mref cref shape children ∧
      (∀ k c, (shape.insts.map (·.1))[k]? = some c → (shape.insts.map (·.1))[k + 1]? = some c →
        children[k]? = children[k + 1]?) ∧ InvV L w' := by
  unfold closeInstsM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨ys, hys, hlen, hk, -, hadj, hw2⟩ := mapM_loop_adj _
    (fun (x : Name × List Nat × MixedGateBinder) => x.1) L
    (fun x w y w' hp hy => synthesizeChild_post L hB hp hy) shape.insts [] children w1 _ hw1 hch
  simp only [List.reverse_nil, List.nil_append] at hys
  subst hys
  exact ⟨children, heq, ⟨hlen, fun k hkl => by
    obtain ⟨y, hy, hre⟩ := hk k hkl
    exact ⟨y, hy, Or.inr hre⟩⟩, hadj, hw2⟩

/-! ## Consecutive calls of a declaration -/

/-- Every name is followed by itself or does not occur later: the calls of a
declaration are consecutive. -/
def sepB : List Name → Bool
  | [] => true
  | a :: rest =>
    (match rest with
      | [] => true
      | b :: _ => a == b || !rest.contains a) && sepB rest

/-- **Equal declarations, equal children** — for consecutive calls, from the
adjacent fact. -/
theorem same_of_adj {β : Type} : ∀ (names : List Name) (ch : List β), sepB names = true →
    (∀ k c, names[k]? = some c → names[k + 1]? = some c → ch[k]? = ch[k + 1]?) →
    ∀ (j i : Nat) (c : Name), i ≤ j → names[i]? = some c → names[j]? = some c → ch[i]? = ch[j]?
  | [], _, _, _, _, _, _, _, hi, _ => by simp at hi
  | a :: rest, ch, hs, hadj, j, i, c, hij, hi, hj => by
    simp only [sepB, Bool.and_eq_true] at hs
    have ih := same_of_adj rest ch.tail hs.2 (fun k c h1 h2 => by
      have := hadj (k + 1) c (by simpa using h1) (by simpa using h2)
      simpa [List.getElem?_tail] using this)
    cases i with
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have := ih j i c (by omega) (by simpa using hi) (by simpa using hj)
        simpa [List.getElem?_tail] using this
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        have hj' : rest[j]? = some a := by simpa using hj
        cases rest with
        | nil => simp at hj'
        | cons b rest' =>
          have hmem : (b :: rest').contains a = true := by
            simpa using List.mem_of_getElem? hj'
          have hab : a = b := by
            have := hs.1
            simp only [hmem, Bool.not_true, Bool.or_false, beq_iff_eq] at this
            exact this
          subst hab
          have h01 := hadj 0 a (by simp) (by simp)
          have := ih j 0 a (Nat.zero_le _) (by simp) hj'
          rw [h01]
          simpa [List.getElem?_tail] using this

end Tools.ShippingCallsSame
