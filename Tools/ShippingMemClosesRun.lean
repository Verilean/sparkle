import Tools.ShippingCallsRunG
import Tools.ShippingMemKidCore

/-! # The general closing on a real run, MEMORY entries included (M1, round par/a-18)

`closeInstsGM_run_all` (`Tools/ShippingCallsRunG.lean` 56–91) asks
`hnomem : ∀ c ∈ shape.insts, memChild? c.1 = none` and uses it in ONE place
(75–81): the `mapM` body of `closeInstsGM`
(`Sparkle/Compiler/Elab.lean` 5211–5214)

    fun (c, _, _) => match memChild? c with | some md => pure md | none => synth c

is rewritten to `synthesizeChild`, so that `mapM_loop_all`
(`Tools/ShippingCallsSame.lean` 148–199) applies — its per-element hypothesis
asks every call to leave its result in the child cache, which `pure md` does
not do.

This file removes the hypothesis:

* `mapM_loop_allM`: `mapM_loop_all` for a body that, per element, EITHER
  returns the value a pure table `mem` gives for the key (whatever it does to
  the world, as long as the invariant, the depth and the cache entries are
  kept) OR is a memoised entry (the facts `mapM_loop_all` asks). Two calls of
  one key get the same result: a table key by the table, a memoised key by
  the cache as before.
* `closeInstsGM_run_allM` (M1): a run of `closeInstsGM` from an invariant
  world of positive depth, for ANY shape — the pure closing of children that
  are `Kid`s (`Tools.ShippingMemKid.Kid`: the built memory module for a
  placeholder name, a real child otherwise), with the pairing clause.
* `closeInstsGM_run_all_again`: the statement of `closeInstsGM_run_all`, from
  M1 (with `hnomem` a kid is a real child). The old theorem is unchanged;
  this shows M1 generalises it.

WRITTEN, NOT BUILT (par/a-18). -/
namespace Tools.ShippingMemCloses
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly
open Tools.ShippingGateChildComb Tools.ShippingChildInv Tools.ShippingRankRun
open Tools.ShippingCallsGate Tools.ShippingCallsAssemblyG Tools.ShippingCallsStmtsG
open Tools.ShippingInstStmtG Tools.ShippingCallsSame
open Tools.ShippingCallsRunG
open Tools.ShippingMemKid (Kid)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A `mapM` whose body is, per element, a pure table's value or a memoised
entry, from a world of positive depth**: each result is the table's value for
its key, or a real child of a key the table does not have; two calls of one
key get the same result. `mapM_loop_all` is the case `mem = fun _ => none`. -/
theorem mapM_loop_allM {α : Type} (f : α → MetaM Res) (key : α → Name)
    (mem : Name → Option Res) (L : RefLaws mref cref)
    (hf : ∀ x w y w', InvV L w → L.dval w ≠ 0 → RunsTo (f x) mctx mref cctx cref w y w' →
      InvV L w' ∧ L.dval w' = L.dval w ∧
        (∀ c0 y0, (L.val w).get? c0 = some y0 → (L.val w').get? c0 = some y0) ∧
        (mem (key x) = some y ∨
          (mem (key x) = none ∧ RealChild mref cref (key x) y ∧
            (L.val w').get? (key x) = some y ∧
            (∀ y0, (L.val w).get? (key x) = some y0 → y = y0)))) :
    ∀ (l : List α) (acc r : List Res) w w', InvV L w → L.dval w ≠ 0 →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧
          (mem (key l[k]) = some y ∨
            (mem (key l[k]) = none ∧ RealChild mref cref (key l[k]) y))) ∧
        (∀ (k : Nat) (c : Name) (y0 : Res), (l.map key)[k]? = some c → mem c = none →
          (L.val w).get? c = some y0 → ys[k]? = some y0) ∧
        (∀ (i j : Nat) (c : Name), i < j → (l.map key)[i]? = some c → (l.map key)[j]? = some c →
          ys[i]? = ys[j]?) ∧
        InvV L w'
  | [], acc, r, w, w', hp, _, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], (by simp), rfl, fun k hk => absurd hk (Nat.not_lt_zero k),
      (fun k c y0 hc => by simp at hc), (fun i j c _ hc => by simp at hc), hp⟩
  | x :: xs, acc, r, w, w', hp, hd, h => by
    obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
    obtain ⟨hp1, hd1, hkeep, hcase⟩ := hf x w y w1 hp hd hy
    obtain ⟨ys, hr, hlen, hget, hpinned, hpair, hp'⟩ :=
      mapM_loop_allM f key mem L hf xs (y :: acc) r w1 w' hp1 (by rw [hd1]; exact hd) h
    refine ⟨y :: ys, (by simp [hr]), (by simp [hlen]), fun k hk => ?_, ?_, ?_, hp'⟩
    · cases k with
      | zero =>
        rcases hcase with hm | ⟨hn, hre, -, -⟩
        · exact ⟨y, rfl, Or.inl hm⟩
        · exact ⟨y, rfl, Or.inr ⟨hn, hre⟩⟩
      | succ k => exact hget k (by simpa using hk)
    · intro k c y0 hc hmc h0
      cases k with
      | zero =>
        simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hc
        subst hc
        rcases hcase with hm | ⟨-, -, -, hhit⟩
        · rw [hmc] at hm
          cases hm
        · rw [hhit y0 h0]
          rfl
      | succ k =>
        simp only [List.getElem?_cons_succ]
        exact hpinned k c y0 (by simpa using hc) hmc (hkeep c y0 h0)
    · intro i j c hij hi hj
      cases j with
      | zero => omega
      | succ j =>
        cases i with
        | zero =>
          simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          have hj' : (xs.map key)[j]? = some (key x) := by simpa using hj
          simp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
          rcases hcase with hm | ⟨hn, -, hin, -⟩
          · -- a table key: the later result is the table's value too
            have hjl : j < xs.length := by
              have := (List.getElem?_eq_some_iff.mp hj').1
              simpa using this
            obtain ⟨y', hy', hor⟩ := hget j hjl
            have hkj : key xs[j] = key x := by
              rw [List.getElem?_map, List.getElem?_eq_getElem hjl] at hj'
              simpa using hj'
            rw [hkj] at hor
            rw [hy']
            rcases hor with h1 | ⟨h1, -⟩
            · rw [hm] at h1
              exact h1
            · rw [hm] at h1
              cases h1
          · -- a memoised key: the later call is a hit of what this one left
            exact (hpinned j (key x) y hj' hn hin).symm
        | succ i =>
          simp only [List.getElem?_cons_succ]
          exact hpair i j c (by omega) (by simpa using hi) (by simpa using hj)

/-- **(M1) A run of the general closing, from an invariant world of positive
depth — memory entries included**: the pure closing of children that are
`Kid`s (the built memory module for a placeholder name, a real child
otherwise), two entries of one name getting the same child. -/
theorem closeInstsGM_run_allM (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape t m₀ d₀ r} {w w'} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧
      (children.length = shape.insts.length ∧
        ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
          Kid mref cref (shape.insts[k]).1 y) ∧
      (∀ (i j : Nat) (c : Name), i < j → (shape.insts.map (·.1))[i]? = some c →
        (shape.insts.map (·.1))[j]? = some c → children[i]? = children[j]?) ∧ InvV L w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  have hd1 : L.dval w1 ≠ 0 := by rw [(L.same .synthGet hget).2.2]; exact hd
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨ys, hys, hlen, hk, -, hpair, hw2⟩ := mapM_loop_allM _
    (fun (x : Name × List Nat × MixedGateBinder) => x.1)
    Sparkle.Compiler.MachMemory.memChild? L
    (fun x w y w' hp hdw hy => by
      obtain ⟨c, a, k'⟩ := x
      dsimp only at hy ⊢
      cases hmc : Sparkle.Compiler.MachMemory.memChild? c with
      | some md =>
        rw [hmc] at hy
        obtain ⟨rfl, rfl⟩ := RunsTo.pure_world hy
        exact ⟨hp, rfl, fun _ _ h0 => h0, Or.inl rfl⟩
      | none =>
        rw [hmc] at hy
        obtain ⟨h1, h2, h3, h4⟩ := synthesizeChild_post L hB hp hy
        exact ⟨h2, synthesizeChild_depth L hB hp hy,
          fun c0 y0 h0 => (synthesizeChild_pin L hB hp hdw h0 hy).1,
          Or.inr ⟨rfl, h1, h3, h4⟩⟩)
    shape.insts [] children w1 _ hw1 hd1 hch
  simp only [List.reverse_nil, List.nil_append] at hys
  subst hys
  exact ⟨children, heq, ⟨hlen, hk⟩, hpair, hw2⟩

/-- **The statement of `closeInstsGM_run_all`, from M1**: without a memory
entry every kid is a real child. Not a replacement of the theorem in
`Tools/ShippingCallsRunG.lean` (unchanged): the check that M1 generalises
it. -/
theorem closeInstsGM_run_all_again (L : RefLaws mref cref)
    (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape t m₀ d₀ r} {w w'} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hnomem : ∀ c ∈ shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧
      (children.length = shape.insts.length ∧
        ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
          RealChild mref cref (shape.insts[k]).1 y) ∧
      (∀ (i j : Nat) (c : Name), i < j → (shape.insts.map (·.1))[i]? = some c →
        (shape.insts.map (·.1))[j]? = some c → children[i]? = children[j]?) ∧ InvV L w' := by
  obtain ⟨children, heq, ⟨hlen, hk⟩, hpair, hw2⟩ := closeInstsGM_run_allM L hB hw hd hr
  refine ⟨children, heq, ⟨hlen, fun k hkl => ?_⟩, hpair, hw2⟩
  obtain ⟨y, hy, hkid⟩ := hk k hkl
  exact ⟨y, hy, hkid.real (hnomem _ (List.getElem_mem hkl))⟩

end Tools.ShippingMemCloses
