import Lean
import Sparkle.Compiler.Elab
import Tools.ShippingReaderSweepCommon
import Tools.ShippingReaderInstTy

/-! # `machInstanceS.inst`: the reader's call site, and the compiler's function against the total one

WRITTEN, NOT BUILT (par/h-1). Two parts.

## The call site (theorems)

The reader calls `inst ty args` with `(c, kinds, ty, args)` from
`machInstCallS?`: `args.length == kinds.length`, and (`instSignatureS?`)
`kinds` is `telescopeKinds ty`. `telescopeKinds_length`: then `kinds.length`
is the number of leading binders of `ty`. So

    instG_callSite (hsub : ∀ b a, piDepth b ≤ piDepth (subst b a))
        (hk : telescopeKinds ty = some kinds) (hl : args.length = kinds.length) :
      ∃ r, instG subst ty args = some r

— the total function returns a result at every call the reader makes, under
the ONE premise about the substitution (at `instantiate1`: a statement about
the extern, not proved, not assumed). That the reader's `kinds` and `args`
satisfy `hk` and `hl` is READ off `instSignatureS?` / `machInstCallS?`, not
proved here.

## The measurement (no theorem)

`old` — `Sparkle.Compiler.Elab.machInstanceS.inst` (the local function of
the mutual block, as a constant); `W` — `instW` (the compiler's text as a
`def`); `T` — `instT`. Results compared with `Expr.equal`. A difference
THROWS.

* GRID — 60 calls: types with 0 … 5 leading binders against 0 … 7
  arguments (48); a binder under `mdata` against 0 … 3 arguments (4); a
  lambda against 0 … 2 (3); `∀ x, x` instantiated with a two-binder type
  against 0 … 4 (5: the substitution exposes more binders).
* SWEEP — the definitions under the roots that use a `@[hardware_module]`
  (`senv.inst` or `senv.instS` of `structEnv`): at every node, a REAL site if
  `machInstCallS?` returns (the reader's own test and arguments), and a WIDE
  site at every application of a constant (the constant's type against the
  node's arguments).

    INSTTY START <what>                            (also on standard error, flushed, before the operation)
    INSTTY GRID: calls=<n> old returned=<n> disagreements=<n> prediction misses=<n>
    INSTTY COLLECT: definitions=<n>
    INSTTY DECL <declaration>: real sites=<n> wide sites=<n>
    INSTTY NOT COMPARED <declaration>: <the exception>
    INSTTY SWEEP: definitions=<n> with a hardware module=<n> real sites=<n> wide sites=<n> old returned=<n> disagreements=<n> not compared=<n>
    INSTTY DISAGREE: <one input>                   (at most forty)
    INSTTY MISS: <one input>                       (at most forty)
    INSTTY: grid agree=<T or F> sweep agree=<T or F> real call sites compared=<n>

PREDICTED: `INSTTY GRID: calls=60 old returned=27 disagreements=0 prediction
misses=0` (27 = 21 + 1 + 1 + 4, by reading the three clauses); the sweep with
`disagreements=0`; at a REAL site `old` returns (not asserted). The numbers
of sites are NOT predicted — in particular whether the suite's environment
has any structure-result `@[hardware_module]` caller (`real sites` may be 0;
the wide sites then carry the sweep). -/
namespace Tools.ShippingReaderInstTy
open Lean
open Sparkle.Compiler.Elab (MixedGateBinder telescopeKinds mixedGateBinderKind?)

theorem length_of_some_nil {kinds : List MixedGateBinder}
    (h : some ([] : List MixedGateBinder) = some kinds) : kinds.length = 0 := by
  cases h
  rfl

/-- The reader's binder kinds are as many as the type's leading binders. -/
theorem telescopeKinds_length : ∀ (ty : Expr) (kinds : List MixedGateBinder),
    telescopeKinds ty = some kinds → kinds.length = piDepth ty
  | .forallE _ t b _, kinds, h => by
    have h' : (mixedGateBinderKind? t).bind
        (fun k => (telescopeKinds b).map (k :: ·)) = some kinds := h
    cases hk : mixedGateBinderKind? t with
    | none =>
      rw [hk] at h'
      exact absurd h' (by simp)
    | some k =>
      rw [hk] at h'
      cases hb : telescopeKinds b with
      | none =>
        rw [hb] at h'
        exact absurd h' (by simp)
      | some ks =>
        rw [hb] at h'
        have h2 : some (k :: ks) = some kinds := h'
        cases h2
        exact congrArg (· + 1) (telescopeKinds_length b ks hb)
  | .bvar _, _, h => length_of_some_nil h
  | .fvar _, _, h => length_of_some_nil h
  | .mvar _, _, h => length_of_some_nil h
  | .sort _, _, h => length_of_some_nil h
  | .const _ _, _, h => length_of_some_nil h
  | .app _ _, _, h => length_of_some_nil h
  | .lam _ _ _ _, _, h => length_of_some_nil h
  | .letE _ _ _ _ _, _, h => length_of_some_nil h
  | .lit _, _, h => length_of_some_nil h
  | .mdata _ _, _, h => length_of_some_nil h
  | .proj _ _ _, _, h => length_of_some_nil h

/-- **At the reader's call the total function returns a result**, under the
one premise about the substitution. -/
theorem instG_callSite (subst : Expr → Expr → Expr)
    (hsub : ∀ b a, piDepth b ≤ piDepth (subst b a)) (ty : Expr)
    (kinds : List MixedGateBinder) (args : List Expr)
    (hk : telescopeKinds ty = some kinds) (hl : args.length = kinds.length) :
    ∃ r, instG subst ty args = some r :=
  instG_some subst hsub args ty (by
    have h1 := telescopeKinds_length ty kinds hk
    omega)

end Tools.ShippingReaderInstTy

namespace Tools.ShippingReaderInstTyShadow
open Lean Meta
open Tools.ShippingReaderProjChainShadow (emit bs marker sameOpt)
open Tools.ShippingReaderSweep
open Tools.ShippingReaderInstTy

/-- The compiler's local `inst`. -/
def oldInst : Expr → List Expr → Option Expr :=
  Sparkle.Compiler.Elab.machInstanceS.inst

/-- What a run of comparisons counted. -/
structure Counts where
  calls : Nat := 0
  returned : Nat := 0
  disagree : Array String := #[]
  misses : Array String := #[]

/-- ONE call through the three functions. -/
def compare1 (tag : String) (ty : Expr) (args : List Expr) (c : Counts) : Counts :=
  let o := oldInst ty args
  let w := instW ty args
  let t := instT ty args
  let c1 : Counts := { c with
    calls := c.calls + 1,
    returned := if o.isSome then c.returned + 1 else c.returned }
  if sameOpt o w && sameOpt o t then c1
  else { c1 with disagree := (c1.disagree.push
    s!"{tag} arguments={args.length}: returned old={bs o.isSome} W={bs w.isSome} T={bs t.isSome}; old==W {bs (sameOpt o w)} old==T {bs (sameOpt o t)}") }

/-- The same, with what the reading says about success. -/
def compareRead (tag : String) (ty : Expr) (args : List Expr) (expected : Bool) (c : Counts) :
    Counts :=
  let c1 := compare1 tag ty args c
  let o := oldInst ty args
  if o.isSome == expected then c1
  else { c1 with misses := (c1.misses.push
    s!"{tag} arguments={args.length}: old returned={bs o.isSome} read={bs expected}") }

/-- `∀ (x₁ … xₙ : A), R xₙ … x₁` (the body refers to every binder). -/
def piN (n : Nat) : Expr :=
  let body : Expr := mkAppN (marker "instTyR" 0) ((List.range n).map Expr.bvar).toArray
  (List.range n).foldl
    (fun acc i => Expr.forallE (Name.mkSimple s!"x{i}") (marker "instTyA" i) acc .default) body

def gridArgs (k : Nat) : List Expr := (List.range k).map (marker "instTyArg")

/-- The grid (see the file comment). -/
def grid : Counts := Id.run do
  let mut c : Counts := {}
  for n in [0:6] do
    for k in [0:8] do
      c := compareRead s!"GRID binders={n}" (piN n) (gridArgs k) (decide (k ≤ n)) c
  let wrapped : Expr := Expr.mdata MData.empty (piN 2)
  for k in [0:4] do
    c := compareRead "GRID a binder under mdata" wrapped (gridArgs k) (k == 0) c
  let lam : Expr := Expr.lam `x (marker "instTyA" 0) (Expr.bvar 0) .default
  for k in [0:3] do
    c := compareRead "GRID a lambda" lam (gridArgs k) (k == 0) c
  let expose : Expr := Expr.forallE `x (Expr.sort .zero) (Expr.bvar 0) .default
  for k in [0:5] do
    let args : List Expr := (piN 2 :: gridArgs 3).take k
    c := compareRead "GRID the substitution exposes binders" expose args (decide (k ≤ 3)) c
  return c

/-- What the sweep reports. -/
structure SweepResult where
  counts : Counts := {}
  definitions : Nat := 0
  withModule : Nat := 0
  real : Nat := 0
  wide : Nat := 0
  notCompared : Nat := 0

/-- ONE node: a real site (the reader's own test), else a wide site (an
application of a constant). The cell: counts, real sites, wide sites. -/
def compareNode (env : Environment) (senv : Sparkle.Compiler.Elab.StructEnv) (decl : Name)
    (x : Expr) (cur : Counts × Nat × Nat) : Counts × Nat × Nat :=
  match Sparkle.Compiler.Elab.machInstCallS? senv x with
  | some (_, _, ty, args) =>
    (compare1 s!"REAL {decl}" ty args cur.1, cur.2.1 + 1, cur.2.2)
  | none =>
    match x with
    | .app _ _ =>
      match x.getAppFn with
      | .const c _ =>
        match env.find? c with
        | some ci => (compare1 s!"WIDE {decl}" ci.type x.getAppArgs.toList cur.1, cur.2.1, cur.2.2 + 1)
        | none => cur
      | _ => cur
    | _ => cur

/-- The definitions under the roots that use a `@[hardware_module]`. Never
throws. -/
def sweep : MetaM SweepResult := do
  let env ← getEnv
  let senv := Sparkle.Compiler.Elab.structEnv env
  emit "INSTTY START collect (definitions of the modules under Sparkle, Tests, IP, Examples, Tools and of this file)"
  let names := collectDefs env
  emit s!"INSTTY COLLECT: definitions={names.size}"
  let mut res : SweepResult := { definitions := names.size }
  for n in names do
    match env.find? n with
    | some (.defnInfo d) =>
      let used := d.value.getUsedConstants
      if (used.any fun c => (senv.instS c).isSome || (senv.inst c).isSome) then
        emit s!"INSTTY START {n}"
        let before := res.counts
        let cell ← IO.mkRef ((before, 0, 0) : Counts × Nat × Nat)
        let outcome : Option String ←
          try
            d.value.forEach fun x => do
              let cur ← cell.get
              cell.set (compareNode env senv n x cur)
            pure none
          catch ex =>
            let text ← ex.toMessageData.toString
            pure (some text)
        match outcome with
        | none =>
          let fin ← cell.get
          emit s!"INSTTY DECL {n}: real sites={fin.2.1} wide sites={fin.2.2}"
          res := { res with
            counts := fin.1, withModule := res.withModule + 1,
            real := res.real + fin.2.1, wide := res.wide + fin.2.2 }
        | some text =>
          emit s!"INSTTY NOT COMPARED {n}: {flat text}"
          res := { res with
            withModule := res.withModule + 1, notCompared := res.notCompared + 1 }
    | _ => pure ()
  return res

/-- The grid, the sweep, the summary; throws on a measured disagreement only. -/
def run : MetaM Unit := do
  emit "INSTTY START grid (60 calls: binders against arguments, mdata, a lambda, exposed binders)"
  let g := grid
  emit s!"INSTTY GRID: calls={g.calls} old returned={g.returned} disagreements={g.disagree.size} prediction misses={g.misses.size}"
  let s ← sweep
  emit s!"INSTTY SWEEP: definitions={s.definitions} with a hardware module={s.withModule} real sites={s.real} wide sites={s.wide} old returned={s.counts.returned} disagreements={s.counts.disagree.size} not compared={s.notCompared}"
  let all : Array String := g.disagree ++ s.counts.disagree
  for line in all.toList.take 40 do
    emit s!"INSTTY DISAGREE: {line}"
  for line in g.misses.toList.take 40 do
    emit s!"INSTTY MISS: {line}"
  let gridOk : Bool := g.disagree.isEmpty
  let sweepOk : Bool := s.counts.disagree.isEmpty
  emit s!"INSTTY: grid agree={bs gridOk} sweep agree={bs sweepOk} real call sites compared={s.real}"
  if !all.isEmpty then
    throwError "INSTTY: the compiler's machInstanceS.inst and the total one DISAGREE on {all.size} measured inputs (the first: {all[0]!})"

/-- Run the comparison in the current environment. -/
elab "#reader_instty_shadow" : command =>
  Lean.Elab.Command.liftTermElabM do
    run

end Tools.ShippingReaderInstTyShadow
