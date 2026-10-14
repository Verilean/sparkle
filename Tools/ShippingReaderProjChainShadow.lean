import Lean
import Sparkle.Compiler.MachRawSurface
import Tools.ShippingReaderProjChain

/-! # `projChain`: the OLD `partial` function against the compiler's and the total ones, by compiled code

A MEASUREMENT: nothing here is a theorem. The first version was BUILT and
run on poc (par/f-1, `docs/parallel/F-reader-unit.md`); THIS version (branch
`fix/projchain-total`, `docs/parallel/L-projchain-switch.md`) is WRITTEN, NOT
BUILT. It elaborates unchanged BEFORE and AFTER the switch-over of
`Sparkle.Compiler.MachRawSurface.projChain`; what it measures differs.

FOUR functions are run on every input and compared with `Expr.equal`
(binder names and annotations count):

* `old`      — `projChainOld` below: a VERBATIM copy of the compiler's
               `projChain` as it was before the switch (a `partial def` with
               its local `partial` `tail`; the text of MachRawSurface.lean
               56–73 at the base commit `80745d94`). Compiled HERE; the
               compiler does not use it.
* `compiler` — `Sparkle.Compiler.MachRawSurface.projChain`, whatever the tree
               has: before the switch the original `partial` function, after
               it the total definition (the same `do` text over
               `MachProjChain.tailAt`).
* `W`        — `projChainW`: before the switch a copy of that total text in
               `Tools/`; after it an abbreviation of `compiler` (the column
               `old==W` then repeats `old==compiler`).
* `T`        — `projChainT`: structural recursion.

On the tree BEFORE the switch, `old==compiler` measures that the copy kept
here behaves as the function it was copied from (the same source, compiled
in another module), and `old==W`, `old==T` are the first version's
measurement. On the tree AFTER the switch, `old==compiler` is the
measurement that matters: the function the compiler now runs against the
one it ran before, on the grid and at every real call site. Without
`projChainOld` the comparison after the switch would compare the total
function with itself.

What `old` is NOT: the object code the compiler ran before the switch. It is
the same source text compiled again. That the two coincide is the
`old==compiler` column of a run on the pre-switch tree, together with the
recorded runs of the first version, which called the original function
directly (grid 198 calls; sweep 1416 sites, 3521 calls; 0 disagreements).

* GRID — every `(length, j, last)` with length `0 … 8`, `j` `0 … 10`, both
  values of `last`, over distinct marker constants. `projChain` uses its
  expression arguments only as opaque pieces (it never inspects one), so its
  behaviour is a function of these three numbers; the grid covers accepted
  and refused inputs alike. Also checked there: the result exists exactly on
  `Accepts` (`acceptsB`), for `old` and for `T`.
* SWEEP — the REAL call sites: every definition of the environment from a
  module under `Sparkle`, `Tests`, `IP`, `Examples`, `Tools` (and of the
  current file) is scanned for applications of a pair-destructuring matcher
  (`prodMatcherArity?`), i.e. the nodes at which `rawNode` calls `projChain`.
  At each, the arguments are computed as `rawNode` computes them (a COPY of
  its eleven lines: `siteArgs`) and the four functions are compared for
  every component; and — so that the copy itself is checked — the value of
  the `j`-th `let` of the REAL `rawNode`'s result is compared with `T`
  (after the switch that `let` value is produced by the total function, so
  together with `old==T` this reads: the reader's rewritten node is what the
  old function produces).

The sweep never throws: a declaration whose scan raises is counted as "not
compared". `#reader_projchain_shadow` logs the lines and THROWS only on a
measured disagreement.

    PROJCHAIN START <what>                         (also on standard error, flushed, before the operation)
    PROJCHAIN WHICH: old=… compiler=… W=… T=…      (which function is which; `compiler partial=<T or F>` read from the environment)
    PROJCHAIN GRID: calls=<n> old returned=<n> disagreements=<n>
    PROJCHAIN COLLECT: definitions=<n>
    PROJCHAIN DECL <declaration>: sites=<n> calls=<n>
    PROJCHAIN NOT COMPARED <declaration>: <the exception>
    PROJCHAIN SWEEP: definitions=<n> with a pair matcher=<n> sites=<n> calls=<n> old returned=<n> disagreements=<n> not compared=<n>
    PROJCHAIN DISAGREE: <one input>                (at most forty)
    PROJCHAIN: grid agree=<T or F> sweep agree=<T or F> real call sites compared=<n>

PREDICTED: `GRID: calls=198 old returned=65 disagreements=0`; the sweep with
`disagreements=0` and, at every site, `old returned` = `calls` (the reader's
calls are inside `Accepts`, `projChainT_callSite`); `WHICH: … compiler
partial=T` before the switch and `=F` after it. The number of sites is NOT
predicted (MEASURED on poc with the first version: 1416 sites, 3521 calls;
new files add definitions, so the counts move). -/
namespace Tools.ShippingReaderProjChainShadow
open Lean Meta
open Tools.ShippingReaderProjChain

def bs (b : Bool) : String := if b then "T" else "F"

/-- THE OLD FUNCTION, kept for the measurement only. A VERBATIM copy of
`Sparkle.Compiler.MachRawSurface.projChain` as it was before the switch-over
(base `80745d94`, MachRawSurface.lean 56–73: the `partial def` with its local
`partial` `tail`; only the name differs). NOT used by the compiler, and not
to be used by anything but this comparison. -/
partial def projChainOld (regs : Lean.Expr) (tys : List Lean.Expr) (j : Nat) (last : Bool) :
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

def emit (s : String) : MetaM Unit := do
  IO.eprintln s
  (← IO.getStderr).flush
  logInfo m!"{s}"

/-- Both absent, or both present and equal (`Expr.equal`). -/
def sameOpt : Option Expr → Option Expr → Bool
  | some a, some b => a.equal b
  | none, none => true
  | _, _ => false

/-- What a run of comparisons counted. -/
structure Tally where
  calls : Nat := 0
  returned : Nat := 0
  disagree : Array String := #[]

/-- ONE input: the old function (`projChainOld`), the compiler's, the
transcription and the structural function, and the predicted range of
success. Every comparison is against the old function. -/
def compare1 (tag : String) (regs : Expr) (tys : List Expr) (j : Nat) (last : Bool)
    (t : Tally) : Tally :=
  let o := projChainOld regs tys j last
  let c := Sparkle.Compiler.MachRawSurface.projChain regs tys j last
  let w := projChainW regs tys j last
  let n := projChainT regs tys j last
  let acc := acceptsB last tys.length j
  let okC := sameOpt o c
  let okW := sameOpt o w
  let okT := sameOpt o n
  let okO := o.isSome == acc
  let okA := n.isSome == acc
  let t1 : Tally := { t with
    calls := t.calls + 1,
    returned := if o.isSome then t.returned + 1 else t.returned }
  if okC && okW && okT && okO && okA then t1
  else { t1 with disagree := (t1.disagree.push
    s!"{tag} len={tys.length} j={j} last={bs last}: returned old={bs o.isSome} compiler={bs c.isSome} W={bs w.isSome} T={bs n.isSome} Accepts={bs acc}; old==compiler {bs okC} old==W {bs okW} old==T {bs okT}") }

def marker (s : String) (i : Nat) : Expr := .const (Name.mkSimple s!"{s}{i}") []

/-- Every `(length, j, last)` up to the bounds, over marker constants. -/
def grid (maxLen : Nat) : Tally := Id.run do
  let mut t : Tally := {}
  for n in [0:maxLen + 1] do
    let tys := (List.range n).map (marker "projChainTy")
    for j in [0:maxLen + 3] do
      t := compare1 "GRID" (marker "projChainRegs" 0) tys j false t
      t := compare1 "GRID" (marker "projChainRegs" 0) tys j true t
  return t

/-- A copy of `rawNode`'s local `peel` (MachRawSurface.lean, in its pair-matcher arm). -/
def peel : Nat → Expr → List (Name × Expr) → Option (List (Name × Expr) × Expr)
  | 0, b, acc => some (acc.reverse, b)
  | i + 1, .lam nm t b _, acc => peel i b ((nm, t) :: acc)
  | _, _, _ => none

/-- The `regs` and the component types `rawNode` computes at a pair-matcher
node of arity `k` (a copy of the first lines of its pair-matcher arm); `none` where
`rawNode` does not reach `projChain`. -/
def siteArgs (k : Nat) (e : Expr) : Option (Expr × List Expr) :=
  let args := e.getAppArgs
  if args.size != 3 then none else
  match peel k args[2]! [] with
  | none => none
  | some (binders, _) =>
    let tys := (binders.zipIdx).map fun ((_, t), i) => t.lowerLooseBVars i i
    some (args[1]!, tys)

/-- The values of the first `n` `let`s of an expression. -/
def letVals : Nat → Expr → List Expr
  | 0, _ => []
  | n + 1, .letE _ _ v b _ => v :: letVals n b
  | _ + 1, _ => []

/-- ONE pair-matcher node: for every component the four functions on the
arguments `rawNode` passes, and the REAL `rawNode`'s `let` value against the
structural function. The flag: the node is a call site. -/
def compareSite (pm : Name → Option Nat) (decl : Name) (k : Nat) (e : Expr) (t0 : Tally) :
    Tally × Bool :=
  match siteArgs k e with
  | none => (t0, false)
  | some (regs, tys) => Id.run do
    let real : Option (List Expr) :=
      (Sparkle.Compiler.MachRawSurface.rawNode pm e).map (letVals k)
    let mut t := t0
    for j in [0:k] do
      let regs' := regs.liftLooseBVars 0 j
      let tys' := tys.map fun x => x.liftLooseBVars 0 j
      let last : Bool := j + 1 == k
      t := compare1 s!"SITE {decl}" regs' tys' j last t
      let n := projChainT regs' tys' j last
      let r : Option Expr := real.bind fun vs => vs[j]?
      if !sameOpt r n then
        t := { t with disagree := (t.disagree.push
          s!"SITE {decl} component {j} of {k}: the let value of the real rawNode differs from projChainT (rawNode returned={bs real.isSome}, value present={bs r.isSome}, T returned={bs n.isSome})") }
    return (t, true)

/-- The module roots whose definitions are scanned. -/
def roots : List Name := [`Sparkle, `Tests, `IP, `Examples, `Tools]

/-- What the sweep reports. -/
structure SweepResult where
  tally : Tally := {}
  definitions : Nat := 0
  withMatcher : Nat := 0
  sites : Nat := 0
  notCompared : Nat := 0

/-- The definitions of the environment (the roots above and the current
file), each scanned for pair-matcher nodes. Never throws. -/
def sweep : MetaM SweepResult := do
  let env ← getEnv
  let pm : Name → Option Nat := Sparkle.Compiler.MachRawSurface.prodMatcherArity? env
  emit "PROJCHAIN START collect (definitions of the modules under Sparkle, Tests, IP, Examples, Tools and of this file)"
  let names : Array Name := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    match ci with
    | .defnInfo _ =>
      match env.getModuleIdxFor? n with
      | some idx =>
        match env.header.moduleNames[idx.toNat]? with
        | some m => if roots.contains m.getRoot then acc.push n else acc
        | none => acc
      | none => acc.push n
    | _ => acc
  emit s!"PROJCHAIN COLLECT: definitions={names.size}"
  let mut res : SweepResult := { definitions := names.size }
  for n in names do
    match env.find? n with
    | some (.defnInfo d) =>
      let used := d.value.getUsedConstants
      if (used.any fun c => (pm c).isSome) then
        emit s!"PROJCHAIN START {n}"
        let before := res.tally
        let cell ← IO.mkRef ((before, 0) : Tally × Nat)
        let outcome : Option String ←
          try
            d.value.forEach fun e => do
              match e.getAppFn with
              | .const c _ =>
                match pm c with
                | some k =>
                  let cur ← cell.get
                  let step := compareSite pm n k e cur.1
                  cell.set (step.1, if step.2 then cur.2 + 1 else cur.2)
                | none => pure ()
              | _ => pure ()
            pure none
          catch ex =>
            let text ← ex.toMessageData.toString
            pure (some text)
        match outcome with
        | none =>
          let fin ← cell.get
          emit s!"PROJCHAIN DECL {n}: sites={fin.2} calls={fin.1.calls - before.calls}"
          res := { res with
            tally := fin.1, withMatcher := res.withMatcher + 1, sites := res.sites + fin.2 }
        | some text =>
          let flat : String := text.replace "\n" " | "
          emit s!"PROJCHAIN NOT COMPARED {n}: {flat}"
          res := { res with withMatcher := res.withMatcher + 1, notCompared := res.notCompared + 1 }
      else
        pure ()
    | _ => pure ()
  return res

/-- The grid, the sweep, the summary; throws on a measured disagreement only. -/
def run : MetaM Unit := do
  let env ← getEnv
  -- the original `partial def` had a local `tail` (the constant `projChain.tail`);
  -- the total definition has none
  let compilerPartial : Bool :=
    env.contains (``Sparkle.Compiler.MachRawSurface.projChain ++ `tail)
  emit s!"PROJCHAIN WHICH: old=Tools.ShippingReaderProjChainShadow.projChainOld (a verbatim copy of the pre-switch partial function, compiled in this file, not used by the compiler); compiler=Sparkle.Compiler.MachRawSurface.projChain (compiler partial={bs compilerPartial}: T = the original partial function with its local tail, F = the total definition after the switch); W=Tools.ShippingReaderProjChain.projChainW (after the switch an abbreviation of compiler); T=Tools.ShippingReaderProjChain.projChainT (structural). Every disagreement is counted against old."
  emit "PROJCHAIN START grid (lengths 0 to 8, j 0 to 10, both values of last)"
  let g := grid 8
  emit s!"PROJCHAIN GRID: calls={g.calls} old returned={g.returned} disagreements={g.disagree.size}"
  let s ← sweep
  emit s!"PROJCHAIN SWEEP: definitions={s.definitions} with a pair matcher={s.withMatcher} sites={s.sites} calls={s.tally.calls} old returned={s.tally.returned} disagreements={s.tally.disagree.size} not compared={s.notCompared}"
  let all : Array String := g.disagree ++ s.tally.disagree
  for line in all.toList.take 40 do
    emit s!"PROJCHAIN DISAGREE: {line}"
  let gridOk : Bool := g.disagree.isEmpty
  let sweepOk : Bool := s.tally.disagree.isEmpty
  emit s!"PROJCHAIN: grid agree={bs gridOk} sweep agree={bs sweepOk} real call sites compared={s.sites}"
  if !all.isEmpty then
    throwError "PROJCHAIN: the old projChain (projChainOld), the compiler's and the total ones DISAGREE on {all.size} measured inputs (the first: {all[0]!})"

/-- Run the comparison in the current environment. -/
elab "#reader_projchain_shadow" : command =>
  Lean.Elab.Command.liftTermElabM do
    run

end Tools.ShippingReaderProjChainShadow
