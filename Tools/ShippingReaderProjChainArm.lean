import Tools.ShippingReaderProjChainReal

/-! # One step up: `rawNode`'s pair-matcher arm over the compiler's `projChain`

WRITTEN, NOT BUILT (branch `fix/projchain-total`; record:
`docs/parallel/L-projchain-switch.md`). No `sorry`, no axiom, no
`native_decide`. FRAGILE and a leaf: nothing depends on this file.

`Sparkle.Compiler.MachRawSurface.rawNode` is a plain `def` (it never was
`partial`), and since the switch-over NONE of its callees is `partial`:
`projChain` (now a `def`), `listElems` (structural), the `Lean.Expr`
operations, and `prodMatch`, which is a PARAMETER of `rawNode`. Its
pair-matcher arm is

    | .const n _, args =>
      match prodMatch n with
      | some k =>
        if args.size != 3 then none else
        let regs := args[1]!
        let alt := args[2]!
        let rec peel …                       -- the alternative's k binders
        match peel k alt [] with
        | none => none
        | some (binders, body) =>
          let tys := (binders.zipIdx).map fun ((_, t), i) => t.lowerLooseBVars i i
          let rec build : List (Nat × Name × Lean.Expr) → Option Lean.Expr
            | [] => some body
            | (j, nm, t) :: rest => do
              let v ← projChain (regs.liftLooseBVars 0 j) (tys.map (·.liftLooseBVars 0 j)) j
                (j + 1 == k)
              let r ← build rest
              some (.letE nm t v r false)
          build ((List.range k).zip binders |>.map fun (j, (nm, t)) => (j, nm, t))

## What is PROVED here

About the loop of the arm written over the compiler's `projChain` (the
constant itself — not a copy of `projChain`):

    buildC_some  : tys.length = k → AllLt k l → ∃ r, buildC regs tys k body l = some r
    pairArmC_some : binders.length = k →
      ∃ r, buildC regs (armTys binders) k body (armJobs k binders) = some r

i.e. once the `k` binders of the alternative are peeled, the arm returns a
result: every `projChain` call it makes succeeds (`projChain_callSiteK`).
`Expr.liftLooseBVars` / `lowerLooseBVars` (externs) enter as opaque values;
nothing about them is needed.

`buildC`, `armTys`, `armJobs`, `peelC` ARE copies — of `rawNode`'s local
`build`, of its `tys`, of its job list and of its local `peel`. Only the
callee `projChain` is the real constant.

## What is STATED, NOT PROVED: `RawNodePairArmGoal`

The statement about `rawNode` ITSELF: at a node whose head is a constant
`n` with `prodMatch n = some k` and exactly three arguments, `rawNode`
returns `buildC …` on the peeled alternative. It is a `def … : Prop`, so the
build checks that it is well-formed; it is not a theorem and nothing uses it.

What blocks its proof — NOT a `partial` callee and NOT an extern any more:

1. the local functions of `rawNode` are the constants `rawNode.peel` and
   `rawNode.build`; the parameters Lean gives `rawNode.build` (which of
   `regs`, `tys`, `k`, `body`, and in what order; whether the `let`-bound
   `tys` is a parameter or re-bound inside) cannot be determined by reading.
   `Tests/Compiler/ReaderDigestTest.lean` logs both types
   (`READERDIGEST CONST …`); with them `rawNode.build … = buildC …` and
   `rawNode.peel = peelC` are inductions over the list / the count;
2. the unfolding of `rawNode`'s six-arm `match` on `(e.getAppFn,
   e.getAppArgs)` at a constant head with a three-element array: the five
   arms before this one need 5, 6, 4, 6, 5 arguments, so none applies — a
   case analysis on the compiled matcher that has to be written against
   goals (name-literal and array-literal patterns), not blind.

Both are kernel-provable in principle. `e.getAppFn` and `e.getAppArgs`
appear as PREMISES of the goal (their values at the node), so the private
auxiliary of `Expr.getAppArgs` is not needed.

One more step up nothing transfers yet: `rawNode`'s caller `machNorm` is
`partial`, and `senv.prodMatch` is `prodMatcherArity?` (`partial`).

PREDICTED axioms: those of `projChainW_eq_projChainT` (`propext`,
`Classical.choice`, `Quot.sound`). -/
namespace Tools.ShippingReaderProjChainArm
open Lean
open Tools.ShippingReaderProjChain
open Tools.ShippingReaderProjChainReal
open Sparkle.Compiler.MachRawSurface (projChain rawNode)

/-! ## The loop of the arm, over the compiler's `projChain` -/

/-- A COPY of `rawNode`'s local `build` (its `do` block is these two binds
of `Option`), with what it closes over as parameters. The callee is the
compiler's `projChain`. -/
def buildC (regs : Expr) (tys : List Expr) (k : Nat) (body : Expr) :
    List (Nat × Name × Expr) → Option Expr
  | [] => some body
  | (j, nm, t) :: rest =>
    (projChain (regs.liftLooseBVars 0 j) (tys.map (·.liftLooseBVars 0 j)) j (j + 1 == k)).bind
      fun v => (buildC regs tys k body rest).bind fun r => some (.letE nm t v r false)

theorem buildC_nil (regs : Expr) (tys : List Expr) (k : Nat) (body : Expr) :
    buildC regs tys k body [] = some body := rfl

theorem buildC_cons (regs : Expr) (tys : List Expr) (k : Nat) (body : Expr) (j : Nat)
    (nm : Name) (t : Expr) (rest : List (Nat × Name × Expr)) :
    buildC regs tys k body ((j, nm, t) :: rest) =
      (projChain (regs.liftLooseBVars 0 j) (tys.map (·.liftLooseBVars 0 j)) j (j + 1 == k)).bind
        fun v => (buildC regs tys k body rest).bind fun r => some (.letE nm t v r false) := rfl

/-- Every job's component index is below `k`. -/
def AllLt (k : Nat) : List (Nat × Name × Expr) → Prop
  | [] => True
  | x :: rest => x.1 < k ∧ AllLt k rest

/-- **The loop returns a result**: every call of the compiler's `projChain`
it makes is inside the range of `projChain_callSiteK`. -/
theorem buildC_some (regs : Expr) (tys : List Expr) (k : Nat) (body : Expr)
    (hk : tys.length = k) :
    ∀ (l : List (Nat × Name × Expr)), AllLt k l → ∃ r, buildC regs tys k body l = some r
  | [], _ => ⟨body, rfl⟩
  | (j, nm, t) :: rest, h =>
    have h' : j < k ∧ AllLt k rest := h
    have hlen : (tys.map (·.liftLooseBVars 0 j)).length = k := by
      first
        | exact (List.length_map _).trans hk
        | (rw [List.length_map]; exact hk)
        | simp [hk]
    match projChain_callSiteK (regs.liftLooseBVars 0 j) (tys.map (·.liftLooseBVars 0 j)) j k
        hlen h'.1, buildC_some regs tys k body hk rest h'.2 with
    | ⟨v, hv⟩, ⟨r, hr⟩ =>
      ⟨.letE nm t v r false, by
        first
          | (rw [buildC_cons, hv, hr]
             all_goals rfl)
          | simp [buildC_cons, hv, hr]⟩

/-! ## The arm's arguments -/

/-- A COPY of `rawNode`'s `tys`: binder `i` sits under `i` earlier binders. -/
def armTys (binders : List (Name × Expr)) : List Expr :=
  (binders.zipIdx).map fun ((_, t), i) => t.lowerLooseBVars i i

/-- The function `rawNode` maps over the zipped list (the identity, written
as the source writes it). -/
def jobOf : Nat × Name × Expr → Nat × Name × Expr :=
  fun (j, (nm, t)) => (j, nm, t)

/-- A COPY of the list `rawNode` hands to `build`. -/
def armJobs (k : Nat) (binders : List (Name × Expr)) : List (Nat × Name × Expr) :=
  ((List.range k).zip binders).map jobOf

theorem armTys_length (binders : List (Name × Expr)) (k : Nat) (hlen : binders.length = k) :
    (armTys binders).length = k := by
  first
    | (unfold armTys; rw [List.length_map, List.length_zipIdx]; exact hlen)
    | (simp [armTys]
       exact hlen)
    | simp [armTys, hlen]

def AllLtN (k : Nat) : List Nat → Prop
  | [] => True
  | x :: rest => x < k ∧ AllLtN k rest

theorem allLtN_of_mem (k : Nat) : ∀ (xs : List Nat), (∀ x, x ∈ xs → x < k) → AllLtN k xs
  | [], _ => trivial
  | x :: xs, h =>
    show x < k ∧ AllLtN k xs from
      ⟨h x (List.Mem.head xs),
        allLtN_of_mem k xs fun y hy => h y (List.Mem.tail x hy)⟩

theorem jobs_allLt (k : Nat) : ∀ (xs : List Nat) (bs : List (Name × Expr)), AllLtN k xs →
    AllLt k ((xs.zip bs).map jobOf)
  | [], _, _ => by
    first
      | exact trivial
      | simp [AllLt]
  | _ :: _, [], _ => by
    first
      | exact trivial
      | simp [AllLt]
  | x :: xs, (nm, t) :: bs, h => by
    have h' : x < k ∧ AllLtN k xs := h
    have ih : AllLt k ((xs.zip bs).map jobOf) := jobs_allLt k xs bs h'.2
    first
      | exact (show AllLt k ((x, nm, t) :: (xs.zip bs).map jobOf) from ⟨h'.1, ih⟩)
      | (simp [AllLt, jobOf]
         exact ⟨h'.1, ih⟩)

theorem armJobs_allLt (k : Nat) (binders : List (Name × Expr)) : AllLt k (armJobs k binders) :=
  jobs_allLt k (List.range k) binders
    (allLtN_of_mem k (List.range k) fun _ hx => List.mem_range.mp hx)

/-- **The arm returns a result once `k` binders are peeled**: its loop over
the compiler's `projChain`, at the arguments the arm computes. -/
theorem pairArmC_some (regs body : Expr) (k : Nat) (binders : List (Name × Expr))
    (hlen : binders.length = k) :
    ∃ r, buildC regs (armTys binders) k body (armJobs k binders) = some r :=
  buildC_some regs (armTys binders) k body (armTys_length binders k hlen)
    (armJobs k binders) (armJobs_allLt k binders)

/-! ## The statement about `rawNode` itself — STATED, NOT PROVED -/

/-- A COPY of `rawNode`'s local `peel`. -/
def peelC : Nat → Expr → List (Name × Expr) → Option (List (Name × Expr) × Expr)
  | 0, b, acc => some (acc.reverse, b)
  | i + 1, .lam nm t b _, acc => peelC i b ((nm, t) :: acc)
  | _, _, _ => none

/-- NOT A THEOREM — the statement a later unit has to prove (see the file's
header for what blocks it). At a pair-matcher node with exactly three
arguments `rawNode` is the loop `buildC` on the peeled alternative; with
`pairArmC_some` and `peelC`'s count it then returns a result. -/
def RawNodePairArmGoal : Prop :=
  ∀ (pm : Name → Option Nat) (e : Expr) (n : Name) (us : List Level) (m regs alt : Expr)
    (k : Nat) (binders : List (Name × Expr)) (body : Expr),
    e.getAppFn = Expr.const n us →
    e.getAppArgs = #[m, regs, alt] →
    pm n = some k →
    peelC k alt [] = some (binders, body) →
    rawNode pm e = buildC regs (armTys binders) k body (armJobs k binders)

end Tools.ShippingReaderProjChainArm
