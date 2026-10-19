import Tools.ShippingCallsRunG
import Tools.ShippingMemKidCore
import Tools.ShippingInstTagged

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

WRITTEN, NOT BUILT (par/a-18).

ORIGIN DISPATCH (patched compiler: `closeInstsGM` maps `shape.instTagged` and
builds a child from the entry's ORIGIN, `InstOrigin.child?`; a declaration
carrying a memory placeholder name is compiled). Restated here:

* `mapM_loop_allT`: `mapM_loop_allM` with the table read per ELEMENT
  (`mem : α → Option Res`), the pairing clause asking the same key AND the same
  table value;
* `closeInstsGM_run_allM` (M1): now about `KidT` of each entry's ORIGIN
  (`originAt shape k`), and two entries of one name get one child when their
  origins build the same (`child?` equal) — the name alone does not decide it
  any more (a memory entry and a declaration of its placeholder name differ);
* `closeInstsGM_run_allM_named`: the previous statement (name-based `Kid`,
  name pairing) for a shape whose names say what their origins build
  (`TagsAgree`, decided per declaration; false for a collision shape);
* `closeInstsGM_run_all_again`: from M1 under the tag condition `hnotag`.

WRITTEN, NOT BUILT against patched compiler (par/o-close). -/
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
open Tools.ShippingInstTagged

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

/-- **`mapM_loop_allM` with the table read per element** (the patched
closing's table is the entry's ORIGIN, not its name): each result is the
table's value for its element, or a real child of the element's key when the
table has none; two elements of one key AND one table value get one result. -/
theorem mapM_loop_allT {α : Type} (f : α → MetaM Res) (key : α → Name)
    (mem : α → Option Res) (L : RefLaws mref cref)
    (hf : ∀ x w y w', InvV L w → L.dval w ≠ 0 → RunsTo (f x) mctx mref cctx cref w y w' →
      InvV L w' ∧ L.dval w' = L.dval w ∧
        (∀ c0 y0, (L.val w).get? c0 = some y0 → (L.val w').get? c0 = some y0) ∧
        (mem x = some y ∨
          (mem x = none ∧ RealChild mref cref (key x) y ∧
            (L.val w').get? (key x) = some y ∧
            (∀ y0, (L.val w).get? (key x) = some y0 → y = y0)))) :
    ∀ (l : List α) (acc r : List Res) w w', InvV L w → L.dval w ≠ 0 →
      RunsTo (List.mapM.loop f l acc) mctx mref cctx cref w r w' →
      ∃ ys, r = acc.reverse ++ ys ∧ ys.length = l.length ∧
        (∀ k (hk : k < l.length), ∃ y, ys[k]? = some y ∧
          (mem l[k] = some y ∨ (mem l[k] = none ∧ RealChild mref cref (key l[k]) y))) ∧
        (∀ (k : Nat) (x : α) (y0 : Res), l[k]? = some x → mem x = none →
          (L.val w).get? (key x) = some y0 → ys[k]? = some y0) ∧
        (∀ (i j : Nat) (x x' : α), i < j → l[i]? = some x → l[j]? = some x' →
          key x = key x' → mem x = mem x' → ys[i]? = ys[j]?) ∧
        InvV L w'
  | [], acc, r, w, w', hp, _, h => by
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    exact ⟨[], (by simp), rfl, fun k hk => absurd hk (Nat.not_lt_zero k),
      (fun k x y0 hx => by simp at hx), (fun i j x x' _ hx => by simp at hx), hp⟩
  | x :: xs, acc, r, w, w', hp, hd, h => by
    obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
    obtain ⟨hp1, hd1, hkeep, hcase⟩ := hf x w y w1 hp hd hy
    obtain ⟨ys, hr, hlen, hget, hpinned, hpair, hp'⟩ :=
      mapM_loop_allT f key mem L hf xs (y :: acc) r w1 w' hp1 (by rw [hd1]; exact hd) h
    refine ⟨y :: ys, (by simp [hr]), (by simp [hlen]), fun k hk => ?_, ?_, ?_, hp'⟩
    · cases k with
      | zero =>
        rcases hcase with hm | ⟨hn, hre, -, -⟩
        · exact ⟨y, rfl, Or.inl hm⟩
        · exact ⟨y, rfl, Or.inr ⟨hn, hre⟩⟩
      | succ k => exact hget k (by simpa using hk)
    · intro k x0 y0 hx hmx h0
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        rcases hcase with hm | ⟨-, -, -, hhit⟩
        · rw [hmx] at hm
          cases hm
        · rw [hhit y0 h0]
          rfl
      | succ k =>
        simp only [List.getElem?_cons_succ]
        exact hpinned k x0 y0 (by simpa using hx) hmx (hkeep _ y0 h0)
    · intro i j x1 x2 hij hi hj hkey hmem
      cases j with
      | zero => omega
      | succ j =>
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          have hj' : xs[j]? = some x2 := by simpa using hj
          simp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
          rcases hcase with hm | ⟨hn, -, hin, -⟩
          · -- a table element: the later result is the table's value too
            obtain ⟨hjl, hx2⟩ := List.getElem?_eq_some_iff.mp hj'
            obtain ⟨y', hy', hor⟩ := hget j hjl
            rw [hx2] at hor
            rw [hy']
            rcases hor with h1 | ⟨h1, -⟩
            · rw [← hmem, hm] at h1
              exact h1
            · rw [← hmem, hm] at h1
              cases h1
          · -- a memoised element: the later call is a hit of what this one left
            rw [hkey] at hin
            exact (hpinned j x2 y hj' (by rw [← hmem]; exact hn) hin).symm
        | succ i =>
          simp only [List.getElem?_cons_succ]
          exact hpair i j x1 x2 (by omega) (by simpa using hi) (by simpa using hj) hkey hmem

/-- **(M1) A run of the general closing, from an invariant world of positive
depth — memory entries included, ORIGIN dispatch**: the pure closing of
children that are `KidT`s of their entries' origins (the built memory module
for a memory origin, a real child of the declaration otherwise — whatever the
name), two entries of one name getting one child when their origins build the
same. -/
theorem closeInstsGM_run_allM (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape t m₀ d₀ r} {w w'} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧
      (children.length = shape.insts.length ∧
        ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
          KidT mref cref (originAt shape k) (shape.insts[k]).1 y) ∧
      (∀ (i j : Nat) (c : Name), i < j → (shape.insts.map (·.1))[i]? = some c →
        (shape.insts.map (·.1))[j]? = some c →
        (originAt shape i).child? = (originAt shape j).child? →
        children[i]? = children[j]?) ∧ InvV L w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  have hd1 : L.dval w1 ≠ 0 := by rw [(L.same .synthGet hget).2.2]; exact hd
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  obtain ⟨ys, hys, hlen, hk, -, hpair, hw2⟩ := mapM_loop_allT _
    (fun (x : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) => x.1)
    (fun (x : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) => x.2.child?) L
    (fun x w y w' hp hdw hy => by
      obtain ⟨c, o⟩ := x
      dsimp only at hy ⊢
      cases hmc : o.child? with
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
    shape.instTagged [] children w1 _ hw1 hd1 hch
  simp only [List.reverse_nil, List.nil_append] at hys
  subst hys
  refine ⟨children, heq, ⟨by rw [hlen, instTagged_length], fun k hkl => ?_⟩,
    fun i j c hij hi hj ho => ?_, hw2⟩
  · have hkT : k < shape.instTagged.length := by rw [instTagged_length]; exact hkl
    obtain ⟨y, hy, hor⟩ := hk k hkT
    refine ⟨y, hy, ?_⟩
    unfold KidT
    rw [← instTagged_getElem_fst shape hkT, ← instTagged_getElem_snd shape hkT]
    exact hor
  · obtain ⟨hil, hic⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hjc⟩ := List.getElem?_eq_some_iff.mp hj
    simp only [List.getElem_map] at hic hjc
    have hiT : i < shape.instTagged.length := by rw [instTagged_length]; simpa using hil
    have hjT : j < shape.instTagged.length := by rw [instTagged_length]; simpa using hjl
    refine hpair i j _ _ hij (List.getElem?_eq_getElem hiT) (List.getElem?_eq_getElem hjT) ?_ ?_
    · show (shape.instTagged[i]).1 = (shape.instTagged[j]).1
      rw [instTagged_getElem_fst shape hiT, instTagged_getElem_fst shape hjT, hic, hjc]
    · show (shape.instTagged[i]).2.child? = (shape.instTagged[j]).2.child?
      rw [instTagged_getElem_snd shape hiT, instTagged_getElem_snd shape hjT]
      exact ho

/-- **The previous statement of M1** (name-based `Kid`, two entries of one
NAME one child), for a shape whose every entry's name decodes to what its
origin builds (`TagsAgree`: decided per declaration; false for a collision
shape, which this theorem then does not cover). -/
theorem closeInstsGM_run_allM_named (L : RefLaws mref cref)
    (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape t m₀ d₀ r} {w w'} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hagree : TagsAgree shape)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧
      (children.length = shape.insts.length ∧
        ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
          Kid mref cref (shape.insts[k]).1 y) ∧
      (∀ (i j : Nat) (c : Name), i < j → (shape.insts.map (·.1))[i]? = some c →
        (shape.insts.map (·.1))[j]? = some c → children[i]? = children[j]?) ∧ InvV L w' := by
  obtain ⟨children, heq, ⟨hlen, hk⟩, hpair, hw2⟩ := closeInstsGM_run_allM L hB hw hd hr
  refine ⟨children, heq, ⟨hlen, fun k hkl => ?_⟩, fun i j c hij hi hj => ?_, hw2⟩
  · obtain ⟨y, hy, hkid⟩ := hk k hkl
    exact ⟨y, hy, kid_of_kidT hkid (agree_at hagree hkl)⟩
  · obtain ⟨hil, hic⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hjc⟩ := List.getElem?_eq_some_iff.mp hj
    simp only [List.getElem_map] at hic hjc
    have hil' : i < shape.insts.length := by simpa using hil
    have hjl' : j < shape.insts.length := by simpa using hjl
    refine hpair i j c hij hi hj ?_
    rw [← agree_at hagree hil', ← agree_at hagree hjl', hic, hjc]

/-- **The statement of `closeInstsGM_run_all`, from M1**: without a memory
ORIGIN every kid is a real child, and two entries of one name build the same
(`none`). The theorem in `Tools/ShippingCallsRunG.lean` is proved directly;
this shows M1 generalises it. -/
theorem closeInstsGM_run_all_again (L : RefLaws mref cref)
    (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape t m₀ d₀ r} {w w'} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hnotag : ∀ o ∈ shape.instTagged, o.2.child?.isNone = true)
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
  refine ⟨children, heq, ⟨hlen, fun k hkl => ?_⟩, fun i j c hij hi hj => ?_, hw2⟩
  · obtain ⟨y, hy, hkid⟩ := hk k hkl
    exact ⟨y, hy, hkid.real (child?_none_of_noMemTag hnotag hkl)⟩
  · have hil : i < shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      simpa using this
    have hjl : j < shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      simpa using this
    refine hpair i j c hij hi hj ?_
    rw [child?_none_of_noMemTag hnotag hil, child?_none_of_noMemTag hnotag hjl]

end Tools.ShippingMemCloses
