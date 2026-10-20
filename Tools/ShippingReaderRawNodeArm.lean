import Tools.ShippingReaderProjChainArm
import Tools.ShippingSparseCasesTac

/-! # `rawNode`'s pair-matcher arm, as theorems about the REAL `rawNode`

WRITTEN, NOT BUILT (branch `fix/reader-p1`; record:
`docs/parallel/P-reader-2.md`). No `sorry`, no axiom, no `native_decide`.
FRAGILE and a leaf: nothing depends on this file.

`Tools/ShippingReaderProjChainArm.lean` STATED `RawNodePairArmGoal` (a
`def … : Prop`) and proved the loop of the arm over the compiler's
`projChain` on a COPY of `rawNode`'s local `build` (`buildC`). This file
proves the goal about `Sparkle.Compiler.MachRawSurface.rawNode` itself.

## The three blockers of the earlier unit, and how they are met

1. The local functions are the constants `rawNode.peel` and `rawNode.build`
   with the types MEASURED by the reader-digest run (`READERDIGEST CONST`):

       rawNode.peel  : Nat → Expr → List (Name × Expr) → Option (List (Name × Expr) × Expr)
       rawNode.build : Nat → Expr → Expr → List Expr → List (Nat × Name × Expr) → Option Expr

   `peel` closes over nothing. `build` closes over `k`, `regs`, `body`, `tys`
   (what its text mentions besides itself and `projChain`), in that order:
   READ in the toolchain (`Lean/Elab/MutualDef.lean`, `mkClosureFor`: the
   free variables are taken in local-context order; `k` is bound by
   `match prodMatch n with | some k`, then `let regs`, `let alt`, then
   `body` by `match peel … with | some (binders, body)`, then `let tys`;
   the two `let`s become parameters, which the measured type confirms — no
   `Array Expr` and no `List (Name × Expr)` parameter). `peel_eq` and
   `build_eq` relate them to the copies `peelC` / `buildC`.
2. The six-arm `match` on `(e.getAppFn, e.getAppArgs)`: after rewriting the
   two discriminants to `Expr.const n us` and `#[m, regs, alt]`, `split`;
   the five earlier arms need 5, 6, 4, 6, 5 arguments, so each of them
   carries an array equation of the wrong length (closed by `simp_all`);
   the catch-all carries the overlap hypothesis of the constant arm (closed
   by applying it, `solve_by_elim`); the constant arm is computed.
3. `peelC`'s count: `peelC_length` (induction on the count).

## What "pair-matcher node" means (exactly the premises below)

* `e.getAppFn = Expr.const n us` — ANY constant (the five earlier arms do
  not apply to three arguments, whatever `n` is);
* `e.getAppArgs = #[m, regs, alt]` — exactly three arguments; `m` (the
  motive) is not read;
* `prodMatch n = some k` — in the compiler `prodMatch` is
  `MachRawSurface.prodMatcherArity? env`;
* `peelC k alt [] = some (binders, body)` — `alt` starts with at least `k`
  syntactic `.lam` binders (no `mdata` between them); then
  `binders.length = k` (`peelC_length_nil`), so the count always matches.

Under these premises `rawNode` IS the loop `buildC` (`rawNode_pairArm`),
hence SUCCEEDS (`rawNode_pairArm_some`); if `alt` has fewer than `k` leading
lambdas it refuses (`rawNode_pairArm_peel_none`); if `prodMatch n = none` it
refuses (`rawNode_pairArm_noMatch`).

PREDICTED axioms: `propext`, `Classical.choice`, `Quot.sound` (through
`split`, `simp_all` and `projChain_callSiteK`). -/
namespace Tools.ShippingReaderRawNodeArm
open Lean
open Tools.ShippingReaderProjChainArm
open Sparkle.Compiler.MachRawSurface (rawNode projChain)

/-! ## The local functions against their copies -/

/-- `rawNode`'s local `peel` is the copy `peelC` (same text; structural on
the count). -/
theorem peel_eq : ∀ (i : Nat) (b : Expr) (acc : List (Name × Expr)),
    Sparkle.Compiler.MachRawSurface.rawNode.peel i b acc = peelC i b acc
  | 0, _, _ => rfl
  | i + 1, .lam nm t b _, acc => peel_eq i b ((nm, t) :: acc)
  | _ + 1, .bvar _, _ => rfl
  | _ + 1, .fvar _, _ => rfl
  | _ + 1, .mvar _, _ => rfl
  | _ + 1, .sort _, _ => rfl
  | _ + 1, .const _ _, _ => rfl
  | _ + 1, .app _ _, _ => rfl
  | _ + 1, .forallE _ _ _ _, _ => rfl
  | _ + 1, .letE _ _ _ _ _, _ => rfl
  | _ + 1, .lit _, _ => rfl
  | _ + 1, .mdata _ _, _ => rfl
  | _ + 1, .proj _ _ _, _ => rfl

/-- `rawNode`'s local `build` (closing over `k`, `regs`, `body`, `tys`, in
that order) is the copy `buildC` (structural on the job list; its `do` block
is two binds of `Option`, which are `Option.bind`). -/
theorem build_eq (k : Nat) (regs body : Expr) (tys : List Expr) :
    ∀ l : List (Nat × Name × Expr),
      Sparkle.Compiler.MachRawSurface.rawNode.build k regs body tys l =
        buildC regs tys k body l
  | [] => rfl
  | (j, nm, t) :: rest => by
    have ih := build_eq k regs body tys rest
    first
      | (rw [buildC_cons, ← ih]; rfl)
      | (rw [buildC_cons, ← ih])
      | (simp only [buildC_cons, ← ih]; rfl)
      | (simp only [buildC_cons, ← ih])

/-! ## `peelC`'s count -/

theorem peelC_length : ∀ (i : Nat) (b : Expr) (acc bs : List (Name × Expr)) (body : Expr),
    peelC i b acc = some (bs, body) → bs.length = i + acc.length
  | 0, b, acc, bs, body, h => by
    have h1 : (acc.reverse, b) = (bs, body) := Option.some.inj h
    have h2 : acc.reverse = bs := congrArg Prod.fst h1
    first
      | (rw [← h2, List.length_reverse, Nat.zero_add])
      | (subst h2; simp)
      | (rw [← h2]; simp)
  | i + 1, .lam nm t b' _, acc, bs, body, h => by
    have ih := peelC_length i b' ((nm, t) :: acc) bs body h
    first
      | (rw [ih, List.length_cons]; omega)
      | (simp only [List.length_cons] at ih; omega)
      | (simp at ih; omega)
  | _ + 1, .bvar _, _, bs, body, h =>
    by first | (simp [peelC] at h) | (cases h) | exact absurd h (by simp [peelC])
  | _ + 1, .fvar _, _, bs, body, h =>
    by first | (simp [peelC] at h) | (cases h) | exact absurd h (by simp [peelC])
  | _ + 1, .mvar _, _, bs, body, h =>
    by first | (simp [peelC] at h) | (cases h) | exact absurd h (by simp [peelC])
  | _ + 1, .sort _, _, bs, body, h =>
    by first | (simp [peelC] at h) | (cases h) | exact absurd h (by simp [peelC])
  | _ + 1, .const _ _, _, bs, body, h =>
    by first | (simp [peelC] at h) | (cases h) | exact absurd h (by simp [peelC])
  | _ + 1, .app _ _, _, bs, body, h =>
    by first | (simp [peelC] at h) | (cases h) | exact absurd h (by simp [peelC])
  | _ + 1, .forallE _ _ _ _, _, bs, body, h =>
    by first | (simp [peelC] at h) | (cases h) | exact absurd h (by simp [peelC])
  | _ + 1, .letE _ _ _ _ _, _, bs, body, h =>
    by first | (simp [peelC] at h) | (cases h) | exact absurd h (by simp [peelC])
  | _ + 1, .lit _, _, bs, body, h =>
    by first | (simp [peelC] at h) | (cases h) | exact absurd h (by simp [peelC])
  | _ + 1, .mdata _ _, _, bs, body, h =>
    by first | (simp [peelC] at h) | (cases h) | exact absurd h (by simp [peelC])
  | _ + 1, .proj _ _ _, _, bs, body, h =>
    by first | (simp [peelC] at h) | (cases h) | exact absurd h (by simp [peelC])

/-- The count of the arm: `k` binders peeled. -/
theorem peelC_length_nil (k : Nat) (alt : Expr) (binders : List (Name × Expr)) (body : Expr)
    (h : peelC k alt [] = some (binders, body)) : binders.length = k :=
  peelC_length k alt [] binders body h

/-! ## `rawNode`'s outer `match` at a three-argument constant node

The toolchain (v4.32.1) does not generate the equation lemmas / splitter of
this `match` (`rawNode.match_15`: "failed to generate equality theorems",
measured), so `split` cannot be used on it. `match15_three` is proved on the
matcher's own definition: unfold it and the sparse case analyses, split the
name by its components and the `dite`s on the component strings and on the
array size; with three arguments every specific arm refuses on the size. -/
set_option maxHeartbeats 2000000 in
theorem match15_three (mot : Expr → Array Expr → Sort u)
    (h1 : (us : List Level) → (dom S τ W r : Expr) →
      mot (Expr.const `Sparkle.Core.Circuit.read us) #[dom, S, τ, W, r])
    (h2 : (us : List Level) → (m inst α β x k : Expr) →
      mot (Expr.const `Bind.bind us) #[m, inst, α, β, x, k])
    (h3 : (us : List Level) → (m inst α a : Expr) → mot (Expr.const `Pure.pure us) #[m, inst, α, a])
    (h4 : (us : List Level) → (dom S head β x k : Expr) →
      mot (Expr.const `Sparkle.Core.Circuit.bind us) #[dom, S, head, β, x, k])
    (h5 : (us : List Level) → (m inst head as f : Expr) →
      mot (Expr.const `List.forM us) #[m, inst, head, as, f])
    (h6 : (n : Name) → (us : List Level) → (args : Array Expr) → mot (Expr.const n us) args)
    (h7 : (x : Expr) → (x_1 : Array Expr) → mot x x_1)
    (n : Name) (us : List Level) (a b c : Expr) :
    Sparkle.Compiler.MachRawSurface.rawNode.match_15 mot (Expr.const n us) #[a, b, c]
      h1 h2 h3 h4 h5 h6 h7 = h6 n us #[a, b, c] := by
  unfold Sparkle.Compiler.MachRawSurface.rawNode.match_15
  rcases n with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p4, s4⟩ | ⟨p4, i4⟩, s3⟩ | ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ |
    ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
  -- the auxiliaries' names are generated per module and CHANGE with the
  -- `prodMatcherArity?` switch (it removes `go`'s, which this matcher reused):
  -- the list measured before the switch first (after it, `go`'s names do not
  -- exist and the list fails to elaborate), else read them off the goal
  all_goals first
    | dsimp only [Sparkle.Compiler.MachRawSurface.listElems._sparseCasesOn_3,
        Sparkle.Compiler.MachRawSurface.prodMatcherArity?.go._sparseCasesOn_2,
        Sparkle.Compiler.MachRawSurface.prodMatcherArity?.go._sparseCasesOn_3,
        Sparkle.Compiler.MachRawSurface.rawNode._sparseCasesOn_15]
    | dsimp_sparse_aux
  all_goals (repeat' split)
  all_goals first
    | rfl
    | (subst_vars; rfl)
    | (exfalso; simp_all; done)
    | (subst_vars; exfalso; simp_all; done)

/-! ## The arm, after `peel` -/

/-- The text of the arm after `peel`, as a function of `peel`'s result (the
`tys` and the job list are `armTys` / `armJobs`, the copies of the earlier
unit; the callee is the REAL local `build`). -/
def armAfter (k : Nat) (regs : Expr) : Option (List (Name × Expr) × Expr) → Option Expr
  | none => none
  | some (binders, body) =>
    Sparkle.Compiler.MachRawSurface.rawNode.build k regs body (armTys binders) (armJobs k binders)

/-- **The pair-matcher arm of the REAL `rawNode`**: at a node whose head is a
constant `n` with `prodMatch n = some k` and exactly three arguments,
`rawNode` is the arm on `peel`'s result. -/
theorem rawNode_pairArm_eq (pm : Name → Option Nat) (e : Expr) (n : Name) (us : List Level)
    (m regs alt : Expr) (k : Nat)
    (h1 : e.getAppFn = Expr.const n us) (h2 : e.getAppArgs = #[m, regs, alt])
    (hk : pm n = some k) :
    rawNode pm e = armAfter k regs (Sparkle.Compiler.MachRawSurface.rawNode.peel k alt []) := by
  first
    | unfold rawNode
    | delta rawNode
    | simp only [rawNode]
  rw [h1, h2, match15_three]
  simp only [hk]
  all_goals first | rfl | exact rfl

/-- At a pair-matcher node whose matcher is not a pair matcher
(`prodMatch n = none`), `rawNode` refuses. -/
theorem rawNode_pairArm_noMatch (pm : Name → Option Nat) (e : Expr) (n : Name)
    (us : List Level) (m regs alt : Expr)
    (h1 : e.getAppFn = Expr.const n us) (h2 : e.getAppArgs = #[m, regs, alt])
    (hk : pm n = none) :
    rawNode pm e = none := by
  first
    | unfold rawNode
    | delta rawNode
    | simp only [rawNode]
  rw [h1, h2, match15_three]
  simp only [hk]
  all_goals first | rfl | exact rfl

/-- **`RawNodePairArmGoal`, PROVED**: at a pair-matcher node `rawNode` is the
loop `buildC` on the peeled alternative. -/
theorem rawNode_pairArm (pm : Name → Option Nat) (e : Expr) (n : Name) (us : List Level)
    (m regs alt : Expr) (k : Nat) (binders : List (Name × Expr)) (body : Expr)
    (h1 : e.getAppFn = Expr.const n us) (h2 : e.getAppArgs = #[m, regs, alt])
    (hk : pm n = some k) (hp : peelC k alt [] = some (binders, body)) :
    rawNode pm e = buildC regs (armTys binders) k body (armJobs k binders) :=
  (rawNode_pairArm_eq pm e n us m regs alt k h1 h2 hk).trans
    ((congrArg (armAfter k regs) ((peel_eq k alt []).trans hp)).trans
      (build_eq k regs body (armTys binders) (armJobs k binders)))

theorem rawNodePairArmGoal_holds : RawNodePairArmGoal :=
  fun pm e n us m regs alt k binders body h1 h2 hk hp =>
    rawNode_pairArm pm e n us m regs alt k binders body h1 h2 hk hp

/-- **The arm SUCCEEDS** at every pair-matcher node (the count of the peeled
binders is `k` by `peelC_length_nil`; every `projChain` call of the loop is
inside `projChain_callSiteK`). -/
theorem rawNode_pairArm_some (pm : Name → Option Nat) (e : Expr) (n : Name) (us : List Level)
    (m regs alt : Expr) (k : Nat) (binders : List (Name × Expr)) (body : Expr)
    (h1 : e.getAppFn = Expr.const n us) (h2 : e.getAppArgs = #[m, regs, alt])
    (hk : pm n = some k) (hp : peelC k alt [] = some (binders, body)) :
    ∃ r, rawNode pm e = some r :=
  match pairArmC_some regs body k binders (peelC_length_nil k alt binders body hp) with
  | ⟨r, hr⟩ => ⟨r, (rawNode_pairArm pm e n us m regs alt k binders body h1 h2 hk hp).trans hr⟩

/-- If the alternative has fewer than `k` leading lambdas, the arm refuses. -/
theorem rawNode_pairArm_peel_none (pm : Name → Option Nat) (e : Expr) (n : Name)
    (us : List Level) (m regs alt : Expr) (k : Nat)
    (h1 : e.getAppFn = Expr.const n us) (h2 : e.getAppArgs = #[m, regs, alt])
    (hk : pm n = some k) (hp : peelC k alt [] = none) :
    rawNode pm e = none :=
  (rawNode_pairArm_eq pm e n us m regs alt k h1 h2 hk).trans
    (congrArg (armAfter k regs) ((peel_eq k alt []).trans hp))

end Tools.ShippingReaderRawNodeArm
