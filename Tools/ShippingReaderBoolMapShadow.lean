import Lean
import Sparkle.Compiler.Elab
import Tools.ShippingReaderSweepCommon
import Tools.ShippingReaderBoolMap

/-! # `machBoolMap`: the compiler's `partial` function against the total one, by compiled code

WRITTEN, NOT BUILT (par/h-1). A MEASUREMENT: nothing here is a theorem. The
reader is not touched: both functions are only CALLED.

`old` — `Sparkle.Compiler.Elab.machBoolMap senv dom a wa`; `T` —
`machBoolMapT (machLiftScalarN senv dom [(wa, a)]) dom` (the total
definition at the compiler's own lifting function, so the comparison is of
`machBoolMap`'s recursion and arms only; `machLiftScalarN` is the same
compiled function on both sides). Results compared with `Expr.equal`. A
difference THROWS.

* GRID — 27 bodies over `senv := structEnv env`, variable width 8: six
  bases (an equality of the variable with itself; the same at variable width
  4; another `BEq` instance; a type that is not `BitVec`; an operand that is
  not the variable; a constant), each under 0 … 3 `!`; and the first base
  under another constant, under `mdata`, and as the first of two arguments
  of `!`.
* SWEEP — the definitions under the roots that use `Signal.map` or
  `Functor.map`: at every node `Signal.map f a` / `f <$> a` whose `f` is a
  lambda and whose source type is a `BitVec` of literal width (the nodes at
  which `machNormMap` can reach `machBoolMap`; a superset of its calls), the
  two functions on the lambda's body. The nodes are taken as written in the
  definitions (the reader calls after its own rewriting of the subterms).

    BOOLMAP START <what>                           (also on standard error, flushed, before the operation)
    BOOLMAP GRID: calls=<n> old returned=<n> disagreements=<n> prediction misses=<n>
    BOOLMAP COLLECT: definitions=<n>
    BOOLMAP DECL <declaration>: sites=<n> Bool sites=<n>
    BOOLMAP NOT COMPARED <declaration>: <the exception>
    BOOLMAP SWEEP: definitions=<n> with a map=<n> sites=<n> Bool sites=<n> old returned=<n> disagreements=<n> not compared=<n>
    BOOLMAP DISAGREE: <one input>                  (at most forty)
    BOOLMAP MISS: <one input>                      (at most forty)
    BOOLMAP: grid agree=<T or F> sweep agree=<T or F> sites compared=<n>

PREDICTED: `BOOLMAP GRID: calls=27 old returned=4 disagreements=0 prediction
misses=0` (4 = the first base under 0 … 3 `!`); the sweep with
`disagreements=0`. The numbers of sites are NOT predicted. -/
namespace Tools.ShippingReaderBoolMapShadow
open Lean Meta
open Tools.ShippingReaderProjChainShadow (emit bs marker sameOpt)
open Tools.ShippingReaderSweep
open Tools.ShippingReaderBoolMap

/-- The compiler's function. -/
def oldBM (senv : Sparkle.Compiler.Elab.StructEnv) (dom a : Expr) (wa : Nat) (e : Expr) :
    Option Expr :=
  Sparkle.Compiler.Elab.machBoolMap senv dom a wa e

/-- The total one, at the compiler's lifting function. -/
def newBM (senv : Sparkle.Compiler.Elab.StructEnv) (dom a : Expr) (wa : Nat) (e : Expr) :
    Option Expr :=
  machBoolMapT (Sparkle.Compiler.Elab.machLiftScalarN senv dom [(wa, a)]) dom e

/-- What a run of comparisons counted. -/
structure Counts where
  calls : Nat := 0
  returned : Nat := 0
  disagree : Array String := #[]
  misses : Array String := #[]

/-- ONE body through the two functions. -/
def compare1 (tag : String) (senv : Sparkle.Compiler.Elab.StructEnv) (dom a : Expr) (wa : Nat)
    (e : Expr) (c : Counts) : Counts :=
  let o := oldBM senv dom a wa e
  let t := newBM senv dom a wa e
  let c1 : Counts := { c with
    calls := c.calls + 1,
    returned := if o.isSome then c.returned + 1 else c.returned }
  if sameOpt o t then c1
  else { c1 with disagree := (c1.disagree.push
    s!"{tag} width={wa}: returned old={bs o.isSome} T={bs t.isSome}") }

/-- The same, with what the reading says about success. -/
def compareRead (tag : String) (senv : Sparkle.Compiler.Elab.StructEnv) (dom a : Expr) (wa : Nat)
    (e : Expr) (expected : Bool) (c : Counts) : Counts :=
  let c1 := compare1 tag senv dom a wa e c
  let o := oldBM senv dom a wa e
  if o.isSome == expected then c1
  else { c1 with misses := (c1.misses.push
    s!"{tag} width={wa}: old returned={bs o.isSome} read={bs expected}") }

def bvTy (w : Nat) : Expr := mkApp (.const ``BitVec []) (Sparkle.Compiler.Elab.inlNatLit w)

def beqInst (ty : Expr) : Expr :=
  mkApp2 (.const ``instBEqOfDecidableEq [.zero]) ty (marker "boolMapDec" 0)

def mkBeq (ty inst x y : Expr) : Expr := mkApp4 (.const ``BEq.beq [.zero]) ty inst x y

/-- The bases: a tag, the body, the variable's width, whether the reading
says it is accepted. -/
def bases : List (String × Expr × Nat × Bool) :=
  [ ("an equality of the variable with itself",
      mkBeq (bvTy 8) (beqInst (bvTy 8)) (Expr.bvar 0) (Expr.bvar 0), 8, true),
    ("the same at variable width 4",
      mkBeq (bvTy 8) (beqInst (bvTy 8)) (Expr.bvar 0) (Expr.bvar 0), 4, false),
    ("another BEq instance",
      mkBeq (bvTy 8) (marker "boolMapInst" 0) (Expr.bvar 0) (Expr.bvar 0), 8, false),
    ("a type that is not BitVec",
      mkBeq (marker "boolMapTy" 0) (beqInst (marker "boolMapTy" 0)) (Expr.bvar 0) (Expr.bvar 0),
      8, false),
    ("an operand that is not the variable",
      mkBeq (bvTy 8) (beqInst (bvTy 8)) (Expr.bvar 1) (Expr.bvar 0), 8, false),
    ("a constant", marker "boolMapJunk" 0, 8, false) ]

/-- `!` applied `n` times. -/
def nots : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => Expr.app (Expr.const ``Bool.not []) (nots n e)

/-- The grid (see the file comment). -/
def grid (senv : Sparkle.Compiler.Elab.StructEnv) : Counts := Id.run do
  let dom := marker "boolMapDom" 0
  let a := marker "boolMapSig" 0
  let mut c : Counts := {}
  for row in bases do
    for n in [0:4] do
      c := compareRead s!"GRID {row.1} under {n} nots" senv dom a row.2.2.1 (nots n row.2.1)
        (row.2.2.2) c
  let b1 : Expr := mkBeq (bvTy 8) (beqInst (bvTy 8)) (Expr.bvar 0) (Expr.bvar 0)
  c := compareRead "GRID the equality under another constant" senv dom a 8
    (Expr.app (marker "boolMapOther" 0) b1) false c
  c := compareRead "GRID the equality under mdata" senv dom a 8
    (Expr.mdata MData.empty b1) false c
  c := compareRead "GRID the equality as the first of two arguments of not" senv dom a 8
    (mkApp2 (Expr.const ``Bool.not []) b1 b1) false c
  return c

/-- A `Signal.map f a` / `f <$> a` node whose `f` is a lambda: the domain,
the two types, the lambda's body, the Signal. -/
def mapSite? : Expr → Option (Expr × Expr × Expr × Expr × Expr)
  | .app (.app (.app (.app (.app (.const ``Sparkle.Core.Signal.Signal.map _) dom) tyA) tyB)
      (.lam _ _ body _)) a => some (dom, tyA, tyB, body, a)
  | .app (.app (.app (.app (.app (.app (.const ``Functor.map _)
      (.app (.const ``Sparkle.Core.Signal.Signal _) dom)) _) tyA) tyB) (.lam _ _ body _)) a =>
    some (dom, tyA, tyB, body, a)
  | _ => none

/-- ONE node. The cell: counts, sites, sites whose target type is `Bool`. -/
def compareNode (senv : Sparkle.Compiler.Elab.StructEnv) (decl : Name) (x : Expr)
    (cur : Counts × Nat × Nat) : Counts × Nat × Nat :=
  match mapSite? x with
  | some (dom, tyA, tyB, body, a) =>
    match Sparkle.Compiler.Elab.machBits? tyA with
    | some wa =>
      (compare1 s!"SITE {decl}" senv dom a wa body cur.1, cur.2.1 + 1,
        if tyB.isConstOf ``Bool then cur.2.2 + 1 else cur.2.2)
    | none => cur
  | none => cur

/-- What the sweep reports. -/
structure SweepResult where
  counts : Counts := {}
  definitions : Nat := 0
  withMap : Nat := 0
  sites : Nat := 0
  boolSites : Nat := 0
  notCompared : Nat := 0

/-- The definitions under the roots that use a map. Never throws. -/
def sweep (senv : Sparkle.Compiler.Elab.StructEnv) : MetaM SweepResult := do
  let env ← getEnv
  emit "BOOLMAP START collect (definitions of the modules under Sparkle, Tests, IP, Examples, Tools and of this file)"
  let names := collectDefs env
  emit s!"BOOLMAP COLLECT: definitions={names.size}"
  let mut res : SweepResult := { definitions := names.size }
  for n in names do
    match env.find? n with
    | some (.defnInfo d) =>
      let used := d.value.getUsedConstants
      if (used.any fun c => c == ``Sparkle.Core.Signal.Signal.map || c == ``Functor.map) then
        emit s!"BOOLMAP START {n}"
        let before := res.counts
        let cell ← IO.mkRef ((before, 0, 0) : Counts × Nat × Nat)
        let outcome : Option String ←
          try
            d.value.forEach fun x => do
              let cur ← cell.get
              cell.set (compareNode senv n x cur)
            pure none
          catch ex =>
            let text ← ex.toMessageData.toString
            pure (some text)
        match outcome with
        | none =>
          let fin ← cell.get
          emit s!"BOOLMAP DECL {n}: sites={fin.2.1} Bool sites={fin.2.2}"
          res := { res with
            counts := fin.1, withMap := res.withMap + 1,
            sites := res.sites + fin.2.1, boolSites := res.boolSites + fin.2.2 }
        | some text =>
          emit s!"BOOLMAP NOT COMPARED {n}: {flat text}"
          res := { res with
            withMap := res.withMap + 1, notCompared := res.notCompared + 1 }
    | _ => pure ()
  return res

/-- The grid, the sweep, the summary; throws on a measured disagreement only. -/
def run : MetaM Unit := do
  let env ← getEnv
  let senv := Sparkle.Compiler.Elab.structEnv env
  emit "BOOLMAP START grid (27 bodies: six bases under 0 to 3 nots, three more wrappers)"
  let g := grid senv
  emit s!"BOOLMAP GRID: calls={g.calls} old returned={g.returned} disagreements={g.disagree.size} prediction misses={g.misses.size}"
  let s ← sweep senv
  emit s!"BOOLMAP SWEEP: definitions={s.definitions} with a map={s.withMap} sites={s.sites} Bool sites={s.boolSites} old returned={s.counts.returned} disagreements={s.counts.disagree.size} not compared={s.notCompared}"
  let all : Array String := g.disagree ++ s.counts.disagree
  for line in all.toList.take 40 do
    emit s!"BOOLMAP DISAGREE: {line}"
  for line in g.misses.toList.take 40 do
    emit s!"BOOLMAP MISS: {line}"
  let gridOk : Bool := g.disagree.isEmpty
  let sweepOk : Bool := s.counts.disagree.isEmpty
  emit s!"BOOLMAP: grid agree={bs gridOk} sweep agree={bs sweepOk} sites compared={s.sites}"
  if !all.isEmpty then
    throwError "BOOLMAP: the compiler's machBoolMap and the total one DISAGREE on {all.size} measured inputs (the first: {all[0]!})"

/-- Run the comparison in the current environment. -/
elab "#reader_boolmap_shadow" : command =>
  Lean.Elab.Command.liftTermElabM do
    run

end Tools.ShippingReaderBoolMapShadow
