import Lean
import Sparkle.Compiler.MachRawSurface
import Tools.ShippingReaderSweepCommon
import Tools.ShippingReaderMatcherArity
import Tools.ShippingReaderMatcherArityShadow

/-! # `prodMatcherArity?`: the OLD `partial` function (a verbatim copy) against the compiler's, by compiled code

WRITTEN, NOT BUILT (branch `fix/reader-p1`; record:
`docs/parallel/P-reader-2.md`). A MEASUREMENT: nothing here is a theorem. It
elaborates on poc (before the switch-over) and on the switched tree: it
names no constant that exists on one tree only (the switch is detected by
the unchecked name `Sparkle.Compiler.MachProdMatcher.goS`).

Why a second shadow: after the switch-over the compiler's
`MachRawSurface.prodMatcherArity?` IS the total function, so the existing
`Tools/ShippingReaderMatcherArityShadow.lean` (its `old` is the compiler's
constant) would compare the total function with itself. This file keeps the
OLD function as `prodMatcherArityOld` — the text of
`Sparkle/Compiler/MachRawSurface.lean` 23–52 at c3176ef1, VERBATIM, `partial`
and local `go` included — and compares, on every input:

* `old` — `prodMatcherArityOld` (and `prodMatcherArityOld.go` on the grid);
* `compiler` — whatever `Sparkle.Compiler.MachRawSurface.prodMatcherArity?`
  (and its `go`) is on the tree being built;
* `T` — `prodMatcherArityT` / `goT exprEqv` (total, the compiler's test).

On poc, `old == compiler` measures the copy against its original; on the
switched tree it measures the function the compiler runs now against the one
it ran before. Every comparison is against `old`; a difference THROWS.

    PRODOLD WHICH: old=verbatim copy (partial) compiler=<total|partial> T=goT exprEqv
    PRODOLD START <what>
    PRODOLD GRID: calls=<n> old returned=<n> old!=compiler=<n> old!=T=<n>
    PRODOLD SWEEP: constants=<n> old returned=<n> old!=compiler=<n> old!=T=<n>
    PRODOLD DISAGREE: <one input>                    (at most forty)
    PRODOLD: grid agree=<T|F> sweep agree=<T|F>

PREDICTED (both trees): `GRID: calls=79 old returned=7 old!=compiler=0
old!=T=0`; `SWEEP: … old!=compiler=0 old!=T=0` with `old returned` equal to
`PRODARITY SWEEP`'s `old returned` of the same environment (1890 in H's run,
if the environment is the same); `WHICH … compiler=partial` on poc,
`compiler=total` after the switch. -/
namespace Tools.ShippingReaderMatcherArityOldShadow
open Lean Meta
open Tools.ShippingReaderProjChainShadow (emit bs)
open Tools.ShippingReaderSweep
open Tools.ShippingReaderMatcherArity

/-- The arity `k` of a matcher that destructures ONE right-nested pair,
    `fun motive x h => Prod.casesOn x (fun v₁ s₁ => Prod.casesOn s₁ (fun v₂ s₂
    => … h v₁ v₂ … sₖ₋₁))`: the alternative's `k` parameters are the
    components. Read off the matcher's value. -/
partial def prodMatcherArityOld (env : Environment) (n : Name) : Option Nat :=
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

/-- What a run counted. -/
structure Counts where
  calls : Nat := 0
  returned : Nat := 0
  vsCompiler : Array String := #[]
  vsT : Array String := #[]

def tally (tag : String) (o c t : Option Nat) (k : Counts) : Counts :=
  let k1 : Counts := { k with
    calls := k.calls + 1,
    returned := if o.isSome then k.returned + 1 else k.returned }
  let k2 : Counts :=
    if o == c then k1
    else { k1 with vsCompiler := (k1.vsCompiler.push
      s!"{tag}: old={showNat o} compiler={showNat c}") }
  if o == t then k2
  else { k2 with vsT := (k2.vsT.push s!"{tag}: old={showNat o} T={showNat t}") }

def run : MetaM Unit := do
  let env ← getEnv
  let total : Bool := env.contains `Sparkle.Compiler.MachProdMatcher.goS
  let label : String := if total then "total" else "partial"
  emit s!"PRODOLD WHICH: old=verbatim copy (partial) compiler={label} T=goT exprEqv"
  emit "PRODOLD START grid (the 79 bodies of PRODARITY)"
  let mut g : Counts := {}
  for row in Tools.ShippingReaderMatcherArityShadow.gridBodies 6 do
    let body := row.2.1
    let o := prodMatcherArityOld.go body 1 [] 0
    let c := Sparkle.Compiler.MachRawSurface.prodMatcherArity?.go body 1 [] 0
    let t := goT exprEqv body 1 [] 0
    g := tally row.1 o c t g
  emit s!"PRODOLD GRID: calls={g.calls} old returned={g.returned} old!=compiler={g.vsCompiler.size} old!=T={g.vsT.size}"
  emit "PRODOLD START sweep (every constant of the environment)"
  let names := collectAll env
  let mut s : Counts := {}
  let mut idx : Nat := 0
  for n in names do
    if idx % 20000 == 0 then
      emit s!"PRODOLD START constants from {idx}"
    idx := idx + 1
    let o := prodMatcherArityOld env n
    let c := Sparkle.Compiler.MachRawSurface.prodMatcherArity? env n
    let t := prodMatcherArityT env n
    s := tally s!"SWEEP {n}" o c t s
  emit s!"PRODOLD SWEEP: constants={names.size} old returned={s.returned} old!=compiler={s.vsCompiler.size} old!=T={s.vsT.size}"
  let dis : Array String := g.vsCompiler ++ g.vsT ++ s.vsCompiler ++ s.vsT
  for line in dis.toList.take 40 do
    emit s!"PRODOLD DISAGREE: {line}"
  let gridOk : Bool := g.vsCompiler.isEmpty && g.vsT.isEmpty
  let sweepOk : Bool := s.vsCompiler.isEmpty && s.vsT.isEmpty
  emit s!"PRODOLD: grid agree={bs gridOk} sweep agree={bs sweepOk}"
  if !dis.isEmpty then
    throwError "PRODOLD: the OLD prodMatcherArity? and the compiler's / the total one DISAGREE on {dis.size} measured inputs (the first: {dis[0]!})"

/-- Run the comparison in the current environment. -/
elab "#reader_prodarity_old_shadow" : command =>
  Lean.Elab.Command.liftTermElabM do
    run

end Tools.ShippingReaderMatcherArityOldShadow
