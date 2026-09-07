/-
  Duplicate-hardware merging by bisimulation (registers included).

  `runCircuitH` evaluates the user's `circuit do` body twice — once
  inside its own `Signal.loop` for the register next-state and once
  outside for the returned value.  A circuit INSTANTIATED inside that
  body (a helper `circuit do`, or `demoPID` inside `closedLoopCircuit`)
  is therefore translated twice by the elaborator, and its registers
  are emitted twice: the outer registers read one copy, the returned
  value reads the other.  Measured: 3 registers for a 2-register
  design, 5 for `closedLoopCircuit`'s 3.  The two copies are
  identical recurrences, so the emitted hardware is genuinely
  doubled.

  The elaborator's expression caches cannot reliably see this: the two
  passes reduce the body differently (an outer register read reaches
  one pass as a `Reg.mk … live` projection and the other as a named
  let wire), so no syntactic key is stable.  This pass merges the
  copies where the question is well-posed — at the IR level — by
  partition refinement: start with every defined node (assigned wire
  or register output) in one class and split classes by the node's
  defining statement with references canonicalised to their classes
  (register: reset, clock, initial value, next-state expression;
  wire: its expression).  The fixpoint is the coarsest bisimulation,
  so two nodes in one class carry equal values at every cycle (by
  induction on cycles: same initial value, same function of
  same-class predecessors).  Merging them is then a sequential-
  equivalence-preserving rewrite — exactly what the wire-level CSE in
  the optimizer does, extended to the cyclic case.  No name is dropped:
  non-representatives become aliases of the representative (module
  outputs are preferred as representatives).

  References to nodes this pass does not classify (module inputs,
  memory read ports, sub-instance outputs) stay as themselves —
  distinct free symbols — so the analysis is conservative.
-/
import Sparkle.IR.AST
import Sparkle.IR.Optimize

namespace Sparkle.IR.RegDedup

open Sparkle.IR.AST Std

/-- Canonical form of an expression under a class map: references to
    classified nodes become their class id, everything else is kept. -/
partial def canonExpr (alias : HashMap String String) (cls : HashMap String Nat) :
    Expr → Expr
  | .ref n =>
    -- an alias `y := x` denotes x: look through alias chains first, so
    -- the two copies' differently-named routes to one wire agree
    let n := Sparkle.IR.Optimize.resolveSubst alias n
    match cls.get? n with
    | some k => .ref s!"#{k}"
    | none => .ref n
  | .op o args => .op o (args.map (canonExpr alias cls))
  | .concat args => .concat (args.map (canonExpr alias cls))
  | .slice e hi lo => .slice (canonExpr alias cls e) hi lo
  | .sliceDim e hi lo => .sliceDim (canonExpr alias cls e) hi lo
  | .index a i => .index (canonExpr alias cls a) (canonExpr alias cls i)
  | e => e

/-- The defining node of a statement, if it defines a single wire. -/
def definedNode : Stmt → Option String
  | .assign lhs _ => some lhs
  | .register out _ _ _ _ => some out
  | _ => none

/-- A node's refinement signature: its own current class (so classes
    only ever split) plus its defining statement with references
    canonicalised. -/
def sigOf (alias : HashMap String String) (cls : HashMap String Nat) (self : Nat) :
    Stmt → String
  | .assign _ rhs => s!"{self}|A|{repr (canonExpr alias cls rhs)}"
  | .register _ clk (rstN, rk) input init =>
    s!"{self}|R|{clk}|{rstN}|{repr rk}|{init}|{repr (canonExpr alias cls input)}"
  | _ => s!"{self}|?"

/-- Merge bisimilar nodes.  Internal (`_tmp_*`) non-representatives become
    plain aliases `n := rep` (a duplicate register's output turns into an
    alias of the surviving register); user-named nodes keep their own
    statement — see `userNamed` below. -/
def mergeDuplicates (m : Module) : Module := Id.run do
  let nodes : List (String × Stmt) := m.body.filterMap fun st =>
    (definedNode st).map fun n => (n, st)
  if nodes.length < 2 then return m
  let outputSet : HashMap String Bool :=
    m.outputs.foldl (fun h p => h.insert p.name true) {}
  -- plain aliases `y := x` (x ≠ y): canonical forms look through them
  let alias : HashMap String String := m.body.foldl (init := {}) fun h st =>
    match st with
    | .assign y (.ref x) => if x != y then h.insert y x else h
    | _ => h
  -- partition refinement from the coarsest partition
  let mut cls : HashMap String Nat := nodes.foldl (fun h (n, _) => h.insert n 0) {}
  let mut nClasses := 1
  for _ in [0:nodes.length + 1] do
    let mut ids : HashMap String Nat := {}
    let mut next : HashMap String Nat := {}
    for (n, st) in nodes do
      let s := sigOf alias cls (cls.getD n 0) st
      let k := match ids.get? s with
        | some k => k
        | none => ids.size
      ids := ids.insert s k
      next := next.insert n k
    let n' := ids.size
    cls := next
    if n' == nClasses then break
    nClasses := n'
  if nClasses == nodes.length then return m
  -- User-named nodes (`_gen_<binder>`, module outputs — anything not an
  -- elaborator-internal `_tmp_*`) are read BY NAME at runtime (the JIT's
  -- wire table: `_gen_trap_taken`, `_gen_done`), and a plain alias would
  -- be folded away by the optimizer's copy propagation.  They therefore
  -- keep their own defining statement (with references renamed); only
  -- internal nodes are aliased.
  -- The representative is the FIRST member in body order: an alias must
  -- point at an already-defined node, or the body's definition-before-use
  -- order (which the certified chain's `woCheck` requires) would break.
  let userNamed (n : String) : Bool := outputSet.contains n || !n.startsWith "_tmp_"
  let mut rep : HashMap Nat String := {}
  for (n, _) in nodes do
    let k := cls.getD n 0
    if !rep.contains k then rep := rep.insert k n
  let mut subst : HashMap String String := {}
  for (n, _) in nodes do
    let r := rep.getD (cls.getD n 0) n
    if r != n && !userNamed n then subst := subst.insert n r
  if subst.isEmpty then return m
  let rename := Sparkle.IR.Optimize.renameRefs subst
  let body := m.body.map fun st =>
    match definedNode st with
    | some n =>
      match subst.get? n with
      | some r => .assign n (.ref r)
      | none => Sparkle.IR.Optimize.mapStmtExprs rename st
    | none => Sparkle.IR.Optimize.mapStmtExprs rename st
  return { m with
    body := body,
    assertions := m.assertions.map fun (n, e) => (n, rename e) }

def mergeDuplicatesDesign (d : Design) : Design :=
  { d with modules := d.modules.map mergeDuplicates }

end Sparkle.IR.RegDedup
