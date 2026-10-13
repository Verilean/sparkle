import Lean
import Sparkle.Compiler.MachRawSurface
import Tools.ShippingReaderSweepCommon
import Tools.ShippingReaderMatcherArity

/-! # `prodMatcherArity?`: the compiler's `partial` function against the total one, by compiled code

WRITTEN, NOT BUILT (par/h-1). A MEASUREMENT: nothing here is a theorem. The
reader is not touched: every function is only CALLED.

Compared on every input:

* `old` — `Sparkle.Compiler.MachRawSurface.prodMatcherArity?` (and its local
  `go`, the constant `prodMatcherArity?.go`, on the grid);
* `T` — `prodMatcherArityT` / `goT exprEqv`: structural, the compiler's own
  test `==`;
* `S` — `prodMatcherArityS` / `goT bvarEqv`: structural, the structural test.

`old` against `T` is the comparison of the candidate: a difference THROWS.
`old` against `S` measures the statement about the extern that is not
provable ("`a == .bvar i` exactly when `a` is `.bvar i`"): a difference is
REPORTED (`structural test differs`), it does not throw — `S` is a second
candidate, not the one proposed. `PIECES` compares `headT` / `argsT` with
`Expr.getAppFn` / `Expr.getAppArgs` at every node visited (the link of the
boundary that is not proved): a difference THROWS.

* GRID — synthetic matcher bodies with 0 … 6 `Prod.casesOn` levels: the
  canonical body and eleven variants that the compiler's text refuses by
  READING (wrong first subject, wrong head index, two arguments swapped, an
  argument dropped / added, an argument under `mdata`, another constant for
  `Prod.casesOn`, a constant at the leaf, four / six arguments at the first
  level, a wrong bound variable): 79 bodies, through `go` at `(1, [], 0)`.
  `prediction misses` counts where `old` differs from the reading.
* SWEEP — EVERY constant of the environment (the reader calls `prodMatch` on
  the head constant of any node): the three functions on the name. A `HIT`
  line is logged for the constants under the roots only; the counts are of
  all of them.
* PIECES — every node of the grid bodies, of the value of every constant on
  which a function returns, and of every definition under the roots that
  uses a pair matcher (unit 1's set).

    PRODARITY START <what>                          (also on standard error, flushed, before the operation)
    PRODARITY GRID: calls=<n> old returned=<n> disagreements=<n> structural test differs=<n> prediction misses=<n> pieces nodes=<n> pieces disagreements=<n>
    PRODARITY COLLECT: constants=<n>
    PRODARITY HIT <constant>: arity=<result of old>
    PRODARITY SWEEP: constants=<n> old returned=<n> under the roots=<n> disagreements=<n> structural test differs=<n> arities <k>=<n> …
    PRODARITY NOT COMPARED <declaration>: <the exception>
    PRODARITY PIECES: definitions=<n> nodes=<n> disagreements=<n> not compared=<n>
    PRODARITY DISAGREE: <one input>                 (at most forty)
    PRODARITY STRUCTURAL: <one input>               (at most forty)
    PRODARITY MISS: <one input>                     (at most forty)
    PRODARITY: grid agree=<T or F> sweep agree=<T or F> pieces agree=<T or F> structural test agree=<T or F>

PREDICTED: `GRID: calls=79 old returned=7 disagreements=0 structural test
differs=0 prediction misses=0 … pieces disagreements=0` (7 = the canonical
bodies; the `mdata` rows are refused IF `Expr.eqv` does not look through
`mdata` — the runtime's source is not in this tree; if it does, `old
returned=14`, `prediction misses=7`, `structural test differs=7`, and that is
a finding about the extern, not a failure of `T`). The sweep's numbers are
NOT predicted. -/
namespace Tools.ShippingReaderMatcherArityShadow
open Lean Meta
open Tools.ShippingReaderProjChainShadow (emit bs marker)
open Tools.ShippingReaderSweep
open Tools.ShippingReaderMatcherArity

/-- The compiler's local `go`. -/
def oldGo : Expr → Nat → List Nat → Nat → Option Nat :=
  Sparkle.Compiler.MachRawSurface.prodMatcherArity?.go

/-- What a run of comparisons counted. -/
structure Counts where
  calls : Nat := 0
  returned : Nat := 0
  /-- `old` against `T`. -/
  disagree : Array String := #[]
  /-- `old` against `S`. -/
  structural : Array String := #[]
  /-- `old` against the reading. -/
  misses : Array String := #[]

/-- The variants of a body. -/
inductive Mut where
  | clean | subject | head | swap | drop | extra | mdata | const | leafConst | fourArgs
  | sixArgs | wrongVar
  deriving BEq, Inhabited

def Mut.name : Mut → String
  | .clean => "canonical"
  | .subject => "wrong first subject"
  | .head => "wrong head index"
  | .swap => "two arguments swapped"
  | .drop => "an argument dropped"
  | .extra => "an argument added"
  | .mdata => "an argument under mdata"
  | .const => "another constant for Prod.casesOn"
  | .leafConst => "a constant at the leaf"
  | .fourArgs => "four arguments at the first level"
  | .sixArgs => "six arguments at the first level"
  | .wrongVar => "a wrong bound variable"

/-- The variants that change the leaf (any number of levels). -/
def leafMuts : List Mut := [.head, .drop, .extra, .mdata, .leafConst, .wrongVar]

/-- The variants that need at least one level (`swap`: two arguments). -/
def levelMuts : List Mut := [.swap, .subject, .const, .fourArgs, .sixArgs]

/-- `go`'s `(subj, vars, depth)` after `m` levels from `(1, [], 0)`. -/
def finalState : Nat → Nat × List Nat × Nat
  | 0 => (1, [], 0)
  | m + 1 =>
    match finalState m with
    | (_, vars, depth) => (0, (vars.map (· + 2)) ++ [1], depth + 2)

def swapTwo : List Expr → List Expr
  | a :: b :: rest => b :: a :: rest
  | l => l

def lastMap (f : Expr → Expr) : List Expr → List Expr
  | [] => []
  | [a] => [f a]
  | a :: rest => a :: lastMap f rest

/-- The leaf of a body with `m` levels, under the variant. -/
def gridLeaf (m : Nat) (mu : Mut) : Expr :=
  match finalState m with
  | (subj, vars, depth) =>
    let args0 : List Expr := (vars ++ [subj]).map Expr.bvar
    let args : List Expr :=
      match mu with
      | .swap => swapTwo args0
      | .drop => args0.dropLast
      | .extra => args0 ++ [Expr.bvar 0]
      | .mdata => lastMap (fun x => Expr.mdata MData.empty x) args0
      | .wrongVar => lastMap (fun _ => Expr.bvar (depth + 50)) args0
      | _ => args0
    let hd : Expr :=
      match mu with
      | .head => Expr.bvar (depth + 1)
      | .leafConst => marker "prodArityLeaf" 0
      | _ => Expr.bvar depth
    mkL hd args

/-- Level `i` (the outermost is `0`) around `rest`, under the variant. -/
def gridLevel (i : Nat) (mu : Mut) (rest : Expr) : Expr :=
  let first : Bool := i == 0
  let t : Nat := if first then (if mu == .subject then 0 else 1) else 0
  let c : Name := if first && mu == .const then ``Prod.rec else ``Prod.casesOn
  let a := marker "prodArityA" i
  let b := marker "prodArityB" i
  let mo := marker "prodArityMotive" i
  let alt := Expr.lam `fst a (Expr.lam `snd b rest .default) .default
  let hd := Expr.const c [.zero, .zero, .zero]
  if first && mu == .fourArgs then mkL hd [a, b, Expr.bvar t, alt]
  else if first && mu == .sixArgs then mkL hd [a, b, mo, Expr.bvar t, alt, Expr.bvar 0]
  else mkL hd [a, b, mo, Expr.bvar t, alt]

/-- The levels `i, i + 1, …` (`n` of them) around the leaf. -/
def gridLevels (mu : Mut) (leaf : Expr) : Nat → Nat → Expr
  | 0, _ => leaf
  | n + 1, i => gridLevel i mu (gridLevels mu leaf n (i + 1))

/-- The body with `m` levels, under the variant. -/
def gridBody (m : Nat) (mu : Mut) : Expr := gridLevels mu (gridLeaf m mu) m 0

/-- ONE body, through the three `go`s at `(1, [], 0)`. -/
def compareBody (tag : String) (body : Expr) (expected : Option Nat) (c : Counts) : Counts :=
  let o := oldGo body 1 [] 0
  let t := goT exprEqv body 1 [] 0
  let s := goT bvarEqv body 1 [] 0
  let c1 : Counts := { c with
    calls := c.calls + 1,
    returned := if o.isSome then c.returned + 1 else c.returned }
  let c2 : Counts :=
    if o == t then c1
    else { c1 with disagree := (c1.disagree.push
      s!"{tag}: old={showNat o} T={showNat t}") }
  let c3 : Counts :=
    if o == s then c2
    else { c2 with structural := (c2.structural.push
      s!"{tag}: old={showNat o} S={showNat s}") }
  if o == expected then c3
  else { c3 with misses := (c3.misses.push
    s!"{tag}: old={showNat o} read={showNat expected}") }

/-- The grid: 0 … `maxLevels` levels, every applicable variant. -/
def gridBodies (maxLevels : Nat) : List (String × Expr × Option Nat) := Id.run do
  let mut out : List (String × Expr × Option Nat) := []
  for m in [0:maxLevels + 1] do
    out := out ++ [(s!"GRID levels={m} {Mut.name .clean}", gridBody m .clean, some (m + 1))]
    for mu in leafMuts do
      out := out ++ [(s!"GRID levels={m} {Mut.name mu}", gridBody m mu, none)]
    if m != 0 then
      for mu in levelMuts do
        out := out ++ [(s!"GRID levels={m} {Mut.name mu}", gridBody m mu, none)]
  return out

/-- `headT` / `argsT` against `getAppFn` / `getAppArgs` at one node. -/
def pieceOk (x : Expr) : Bool :=
  (headT x).equal x.getAppFn && sameList (argsT x) x.getAppArgs.toList

/-- Every node of `e` (each once). The cell: nodes, disagreements. -/
def scanPieces (tag : String) (e : Expr) (cell : IO.Ref (Nat × Array String)) : MetaM Unit :=
  e.forEach fun x => do
    let cur ← cell.get
    if pieceOk x then
      cell.set (cur.1 + 1, cur.2)
    else
      cell.set (cur.1 + 1, cur.2.push
        s!"{tag}: headT / argsT differ from getAppFn / getAppArgs at a node with {x.getAppNumArgs} arguments")

/-- What the sweep reports. -/
structure SweepResult where
  counts : Counts := {}
  constants : Nat := 0
  rootHits : Nat := 0
  hist : Array Nat := (List.replicate 10 0).toArray

/-- Every constant of the environment through the three functions. -/
def sweep (cell : IO.Ref (Nat × Array String)) : MetaM SweepResult := do
  let env ← getEnv
  emit "PRODARITY START collect (every constant of the environment)"
  let names := collectAll env
  emit s!"PRODARITY COLLECT: constants={names.size}"
  let mut res : SweepResult := { constants := names.size }
  let mut idx : Nat := 0
  for n in names do
    if idx % 20000 == 0 then
      emit s!"PRODARITY START constants from {idx}"
    idx := idx + 1
    let o := Sparkle.Compiler.MachRawSurface.prodMatcherArity? env n
    let t := prodMatcherArityT env n
    let s := prodMatcherArityS env n
    let c := res.counts
    let c1 : Counts := { c with
      calls := c.calls + 1,
      returned := if o.isSome then c.returned + 1 else c.returned }
    let c2 : Counts :=
      if o == t then c1
      else { c1 with disagree := (c1.disagree.push
        s!"SWEEP {n}: old={showNat o} T={showNat t}") }
    let c3 : Counts :=
      if o == s then c2
      else { c2 with structural := (c2.structural.push
        s!"SWEEP {n}: old={showNat o} S={showNat s}") }
    res := { res with counts := c3 }
    if o.isSome || t.isSome || s.isSome then
      let k : Nat := (o.getD 0)
      let slot : Nat := if k < 9 then k else 9
      res := { res with hist := res.hist.modify slot (· + 1) }
      if underRoots env n then
        emit s!"PRODARITY HIT {n}: arity={showNat o}"
        res := { res with rootHits := res.rootHits + 1 }
      match env.find? n with
      | some (.defnInfo d) =>
        try
          scanPieces s!"PIECES {n}" d.value cell
        catch ex =>
          let text ← ex.toMessageData.toString
          emit s!"PRODARITY NOT COMPARED {n}: {flat text}"
      | _ => pure ()
  return res

/-- `headT` / `argsT` on the definitions under the roots that use a pair
matcher. Returns: definitions scanned, not compared. -/
def piecesSweep (cell : IO.Ref (Nat × Array String)) : MetaM (Nat × Nat) := do
  let env ← getEnv
  emit "PRODARITY START pieces (the definitions under the roots that use a pair matcher)"
  let defs := collectDefs env
  let mut scanned : Nat := 0
  let mut notCompared : Nat := 0
  for n in defs do
    match env.find? n with
    | some (.defnInfo d) =>
      let used := d.value.getUsedConstants
      if (used.any fun c => (Sparkle.Compiler.MachRawSurface.prodMatcherArity? env c).isSome) then
        emit s!"PRODARITY START pieces {n}"
        scanned := scanned + 1
        try
          scanPieces s!"PIECES {n}" d.value cell
        catch ex =>
          let text ← ex.toMessageData.toString
          emit s!"PRODARITY NOT COMPARED {n}: {flat text}"
          notCompared := notCompared + 1
    | _ => pure ()
  return (scanned, notCompared)

def showHist (h : Array Nat) : String :=
  String.intercalate " " ((List.range h.size).map fun i => s!"{i}={h.getD i 0}")

/-- The grid, the sweep, the pieces, the summary; throws on a measured
disagreement of the candidate (`old` against `T`, or the pieces) only. -/
def run : MetaM Unit := do
  emit "PRODARITY START grid (0 to 6 levels, the canonical body and eleven variants)"
  let gcell ← IO.mkRef ((0, #[]) : Nat × Array String)
  let mut g : Counts := {}
  for row in gridBodies 6 do
    g := compareBody row.1 row.2.1 row.2.2 g
    scanPieces row.1 row.2.1 gcell
  let gp ← gcell.get
  emit s!"PRODARITY GRID: calls={g.calls} old returned={g.returned} disagreements={g.disagree.size} structural test differs={g.structural.size} prediction misses={g.misses.size} pieces nodes={gp.1} pieces disagreements={gp.2.size}"
  let cell ← IO.mkRef ((0, #[]) : Nat × Array String)
  let s ← sweep cell
  emit s!"PRODARITY SWEEP: constants={s.constants} old returned={s.counts.returned} under the roots={s.rootHits} disagreements={s.counts.disagree.size} structural test differs={s.counts.structural.size} arities {showHist s.hist}"
  let ps ← piecesSweep cell
  let sp ← cell.get
  emit s!"PRODARITY PIECES: definitions={ps.1} nodes={sp.1} disagreements={sp.2.size} not compared={ps.2}"
  let dis : Array String := g.disagree ++ s.counts.disagree
  let str : Array String := g.structural ++ s.counts.structural
  let pie : Array String := gp.2 ++ sp.2
  for line in dis.toList.take 40 do
    emit s!"PRODARITY DISAGREE: {line}"
  for line in pie.toList.take 40 do
    emit s!"PRODARITY DISAGREE: {line}"
  for line in str.toList.take 40 do
    emit s!"PRODARITY STRUCTURAL: {line}"
  for line in g.misses.toList.take 40 do
    emit s!"PRODARITY MISS: {line}"
  let gridOk : Bool := g.disagree.isEmpty
  let sweepOk : Bool := s.counts.disagree.isEmpty
  let piecesOk : Bool := pie.isEmpty
  let structOk : Bool := str.isEmpty
  emit s!"PRODARITY: grid agree={bs gridOk} sweep agree={bs sweepOk} pieces agree={bs piecesOk} structural test agree={bs structOk}"
  if !dis.isEmpty then
    throwError "PRODARITY: the compiler's prodMatcherArity? and the total one DISAGREE on {dis.size} measured inputs (the first: {dis[0]!})"
  if !pie.isEmpty then
    throwError "PRODARITY: headT / argsT DISAGREE with getAppFn / getAppArgs at {pie.size} measured nodes (the first: {pie[0]!})"

/-- Run the comparison in the current environment. -/
elab "#reader_prodarity_shadow" : command =>
  Lean.Elab.Command.liftTermElabM do
    run

end Tools.ShippingReaderMatcherArityShadow
