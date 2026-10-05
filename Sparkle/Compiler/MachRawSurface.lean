import Lean
import Sparkle.Core.CircuitMonad

/-! # The raw `runCircuitH` surface, in the form the machine reader takes

A `runCircuitH` body written by hand (instead of with `circuit do`) uses
three surface forms that are definitionally the `circuit do` ones:

* `let (r₀, r₁, …, rest) := regs` — elaborated to an auxiliary matcher, a
  right-nested chain of `Prod.casesOn` — is the `let`s of the projections
  `regs.fst`, `regs.snd.fst`, …, `regs.snd.….snd`;
* `Circuit.read r` is `r.fst` (`Reg` is a pair, `Reg.liveRead r = r.1`);
* the monad's `bind` / `pure` at `Circuit.instMonad` are `Circuit.bind` /
  `Circuit.pure'`.

These rewrites are pure and only replace a term by a definitionally equal
one (delta, beta, structure eta); the endpoint generator's kernel checks
relate the declaration to the reader's terms. -/
namespace Sparkle.Compiler.MachRawSurface
open Lean

/-- The arity `k` of a matcher that destructures ONE right-nested pair,
    `fun motive x h => Prod.casesOn x (fun v₁ s₁ => Prod.casesOn s₁ (fun v₂ s₂
    => … h v₁ v₂ … sₖ₋₁))`: the alternative's `k` parameters are the
    components. Read off the matcher's value. -/
partial def prodMatcherArity? (env : Environment) (n : Name) : Option Nat :=
  match env.find? n with
  | some (.defnInfo d) =>
    match d.value with
    | .lam _ _ (.lam _ _ (.lam _ _ body _) _) _ =>
      -- inside: bvar 0 = h, bvar 1 = x; walk the casesOn chain
      go body 1 [] 0
    | _ => none
  | _ => none
where
  /-- `subj` is the bvar index of the current subject; `vars` the component
      bvar indices met so far (outermost first, relative to the current
      depth `depth` below the three lambdas). -/
  go : Lean.Expr → Nat → List Nat → Nat → Option Nat
    | e, subj, vars, depth =>
      match e.getAppFn, e.getAppArgs with
      | .const ``Prod.casesOn _, #[_, _, _, .bvar t, .lam _ _ (.lam _ _ rest _) _] =>
        if t != subj then none else
        -- under two binders: fst = bvar 1, snd = bvar 0; earlier vars shift by 2
        go rest 0 ((vars.map (· + 2)) ++ [1]) (depth + 2)
      | .bvar hIdx, args =>
        -- `h` sits at index `depth + 0` relative to the walk start (+2 per level)
        if hIdx != depth then none else
        let expected := vars ++ [subj]
        if args.toList == expected.map Lean.Expr.bvar then some args.size else none
      | _, _ => none

/-- The projection chain `regs.snd^j.fst` (or `regs.snd^j` when `last`),
    with the pair types read from the component types `tys` (each a closed
    type at the matcher's context). -/
partial def projChain (regs : Lean.Expr) (tys : List Lean.Expr) (j : Nat) (last : Bool) :
    Option Lean.Expr := do
  -- the pair type at level i: Prod tys[i] (tail i)
  let rec tail : Nat → Option Lean.Expr
    | i => if i + 1 == tys.length - 1 then tys[tys.length - 1]?
      else do
        let a ← tys[i + 1]?
        let b ← tail (i + 1)
        some (mkApp2 (.const ``Prod [.zero, .zero]) a b)
  let mut cur := regs
  for i in [0:j] do
    let a ← tys[i]?
    let b ← tail i
    cur := mkApp3 (.const ``Prod.snd [.zero, .zero]) a b cur
  if last then return cur
  let a ← tys[j]?
  let b ← tail j
  return mkApp3 (.const ``Prod.fst [.zero, .zero]) a b cur

/-- One raw-surface node, rewritten (`none`: not a raw-surface node). -/
def rawNode (prodMatch : Name → Option Nat) (e : Lean.Expr) : Option Lean.Expr :=
  match e.getAppFn, e.getAppArgs with
  -- `Circuit.read r` → `r.fst`
  | .const ``Sparkle.Core.Circuit.read _, #[dom, S, τ, W, r] =>
    some (mkApp3 (.const ``Prod.fst [.zero, .zero])
      (mkApp2 (.const ``Sparkle.Core.Signal.Signal [.zero]) dom τ)
      (mkApp4 (.const ``Sparkle.Core.Circuit.Slot []) dom S W τ) r)
  -- `bind m k` at the Circuit monad → `Circuit.bind m k`
  | .const ``Bind.bind _, #[m, inst, α, β, x, k] =>
    match m.getAppFn, m.getAppArgs, inst.getAppFn with
    | .const ``Sparkle.Core.Circuit _, #[dom, S], .const ``Monad.toBind _ =>
      some (mkAppN (.const ``Sparkle.Core.Circuit.bind []) #[dom, S, α, β, x, k])
    | _, _, _ => none
  -- `pure a` at the Circuit monad → `Circuit.pure' a`
  | .const ``Pure.pure _, #[m, inst, α, a] =>
    match m.getAppFn, m.getAppArgs, inst.getAppFn with
    | .const ``Sparkle.Core.Circuit _, #[dom, S], .const ``Applicative.toPure _ =>
      some (mkAppN (.const ``Sparkle.Core.Circuit.pure' []) #[dom, S, α, a])
    | _, _, _ => none
  -- a pair-destructuring matcher → the `let`s of the projections
  | .const n _, args =>
    match prodMatch n with
    | some k =>
      if args.size != 3 then none else
      let regs := args[1]!
      let alt := args[2]!
      -- the alternative's k binders: names and types
      let rec peel : Nat → Lean.Expr → List (Name × Lean.Expr) → Option (List (Name × Lean.Expr) × Lean.Expr)
        | 0, b, acc => some (acc.reverse, b)
        | i + 1, .lam nm t b _, acc => peel i b ((nm, t) :: acc)
        | _, _, _ => none
      match peel k alt [] with
      | none => none
      | some (binders, body) =>
        -- the component types at the alternative's context: binder i sits
        -- under i earlier binders (non-dependent, so lowered back)
        let tys := (binders.zipIdx).map fun ((_, t), i) => t.lowerLooseBVars i i
        -- build `let v₁ := …; …; let vₖ := …; body`
        let rec build : List (Nat × Name × Lean.Expr) → Option Lean.Expr
          | [] => some body
          | (j, nm, t) :: rest => do
            -- under j earlier lets
            let v ← projChain (regs.liftLooseBVars 0 j) (tys.map (·.liftLooseBVars 0 j)) j
              (j + 1 == k)
            let r ← build rest
            some (.letE nm t v r false)
        build ((List.range k).zip binders |>.map fun (j, (nm, t)) => (j, nm, t))
    | none => none
  | _, _ => none

/-- A projection of a bundle, after the reader substituted the bundle's
    `let`: `(bundle2 a b).fst` is `a`, `.snd` is `b`, and
    `(bundle3 a b c).proj3_k` the `k`-th component, `Signal.map Prod.fst`
    / `Prod.snd` of a `bundle2` too — definitionally (both
    sides unfold to `⟨fun t => (a.val t, …).i⟩`, structure eta), so the
    endpoint generator's kernel checks hold. Anything else is left as is. -/
def bundleIota (e : Lean.Expr) : Lean.Expr :=
  match e.getAppFn, e.getAppArgs with
  | .const p _, #[_, _, _, s] =>
    match s.getAppFn, s.getAppArgs, p with
    | .const ``Sparkle.Core.Signal.bundle2 _, #[_, _, _, a, _],
        ``Sparkle.Core.Signal.Signal.fst => a
    | .const ``Sparkle.Core.Signal.bundle2 _, #[_, _, _, _, b],
        ``Sparkle.Core.Signal.Signal.snd => b
    | _, _, _ => e
  | .const ``Sparkle.Core.Signal.Signal.map _, #[_, _, _, f, s] =>
    -- `Signal.map Prod.fst (bundle2 a b)` (what `Signal.fst` unfolds to)
    match s.getAppFn, s.getAppArgs, f.getAppFn, f.getAppNumArgs with
    | .const ``Sparkle.Core.Signal.bundle2 _, #[_, _, _, a, _], .const ``Prod.fst _, 2 => a
    | .const ``Sparkle.Core.Signal.bundle2 _, #[_, _, _, _, b], .const ``Prod.snd _, 2 => b
    | _, _, _, _ => e
  | .const p _, #[_, _, _, _, s] =>
    match s.getAppFn, s.getAppArgs, p with
    | .const ``Sparkle.Core.Signal.bundle3 _, #[_, _, _, _, a, _, _],
        ``Sparkle.Core.Signal.Signal.proj3_1 => a
    | .const ``Sparkle.Core.Signal.bundle3 _, #[_, _, _, _, _, b, _],
        ``Sparkle.Core.Signal.Signal.proj3_2 => b
    | .const ``Sparkle.Core.Signal.bundle3 _, #[_, _, _, _, _, _, c],
        ``Sparkle.Core.Signal.Signal.proj3_3 => c
    | _, _, _ => e
  | _, _ => e

end Sparkle.Compiler.MachRawSurface
