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
  multi-port memory read ports, sub-instance outputs) stay as themselves —
  distinct free symbols — so the analysis is conservative.
-/
import Sparkle.IR.AST
import Sparkle.IR.Optimize
import Sparkle.IR.ReorderInvariance

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
  -- a single-port memory is a node named by its read data: a state node
  -- (the read latch) for a synchronous read, a combinational node
  -- (`contents[ra]`, same cycle) for a combinational read — two copies
  -- with the same write port hold the same contents at every cycle
  -- (both start at 0), so same read address ⇒ same read data either
  -- way (multi-port memories are left alone)
  | .memory _ _ _ _ _ _ _ _ rd _ [] [] => some rd
  | _ => none

/-- A node's refinement signature: its own current class (so classes
    only ever split) plus its defining statement with references
    canonicalised. -/
def sigOf (alias : HashMap String String) (cls : HashMap String Nat) (self : Nat) :
    Stmt → String
  | .assign _ rhs => s!"{self}|A|{repr (canonExpr alias cls rhs)}"
  | .register _ clk (rstN, rk) input init =>
    s!"{self}|R|{clk}|{rstN}|{repr rk}|{init}|{repr (canonExpr alias cls input)}"
  | .memory _ aw dw clk wa wd we ra _ cr _ _ =>
    -- same write port ⇒ same contents at every cycle (both start at 0);
    -- same read address (and read kind) ⇒ same read data
    s!"{self}|M|{cr}|{aw}|{dw}|{clk}|{repr (canonExpr alias cls wa)}|{repr (canonExpr alias cls wd)}|{repr (canonExpr alias cls we)}|{repr (canonExpr alias cls ra)}"
  | _ => s!"{self}|?"

/-! ### Validation of a merge on a combinational body

Instead of proving the implementation below directly, the merge is treated
as an untrusted proposal: for a body made only of `assign`s, its RESULT is
kept only if `validateMerge` accepts it, a pure checker proved sound in
`Tools/ShippingPostSoundness.lean`. If the check fails, the module is returned
unchanged. The checker covers the evaluation of the statement list; the
`assertions` the merge also rewrites are not checked. -/

mutual
/-- Structural equality of IR expressions (the derived `BEq` is not proved lawful). -/
def exprEqB : Expr → Expr → Bool
  | .const v w, .const v' w' => decide (v = v') && decide (w = w')
  | .ref n, .ref n' => decide (n = n')
  | .op o as, .op o' as' => decide (o = o') && listEqB as as'
  | .concat as, .concat as' => listEqB as as'
  | .slice e h l, .slice e' h' l' => exprEqB e e' && decide (h = h') && decide (l = l')
  | .sliceDim e h l, .sliceDim e' h' l' => exprEqB e e' && decide (h = h') && decide (l = l')
  | .index a i, .index a' i' => exprEqB a a' && exprEqB i i'
  | _, _ => false

def listEqB : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => exprEqB a b && listEqB as bs
  | _, _ => false
end

mutual
theorem exprEqB_iff : ∀ a b : Expr, exprEqB a b = true ↔ a = b
  | .const v w, b => by cases b <;> simp [exprEqB]
  | .ref n, b => by cases b <;> simp [exprEqB]
  | .op o as, b => by
    cases b with
    | op o' as' => simp [exprEqB, listEqB_iff as as']
    | _ => simp [exprEqB]
  | .concat as, b => by
    cases b with
    | concat as' => simp [exprEqB, listEqB_iff as as']
    | _ => simp [exprEqB]
  | .slice e h l, b => by
    cases b with
    | slice e' h' l' => simp [exprEqB, exprEqB_iff e e', and_assoc]
    | _ => simp [exprEqB]
  | .sliceDim e h l, b => by
    cases b with
    | sliceDim e' h' l' => simp [exprEqB, exprEqB_iff e e', and_assoc]
    | _ => simp [exprEqB]
  | .index a i, b => by
    cases b with
    | index a' i' => simp [exprEqB, exprEqB_iff a a', exprEqB_iff i i']
    | _ => simp [exprEqB]

theorem listEqB_iff : ∀ as bs : List Expr, listEqB as bs = true ↔ as = bs
  | [], bs => by cases bs <;> simp [listEqB]
  | a :: as, bs => by
    cases bs with
    | nil => simp [listEqB]
    | cons b bs => simp [listEqB, exprEqB_iff a b, listEqB_iff as bs]
end

instance instDecidableEqIRExpr : DecidableEq Expr := fun a b =>
  decidable_of_iff _ (exprEqB_iff a b)

/-- Rename references through a substitution function (pure). -/
def renameE (σ : String → String) : Expr → Expr
  | .const v w => .const v w
  | .ref n => .ref (σ n)
  | .op o args => .op o (renameL σ args)
  | .concat args => .concat (renameL σ args)
  | .slice e hi lo => .slice (renameE σ e) hi lo
  | .sliceDim e hi lo => .sliceDim (renameE σ e) hi lo
  | .index a i => .index (renameE σ a) (renameE σ i)
where
  renameL (σ : String → String) : List Expr → List Expr
    | [] => []
    | a :: rest => renameE σ a :: renameL σ rest

/-- Look a name up in an association list of aliases (itself if absent). -/
def aliasOf (A : List (String × String)) (x : String) : String := (A.lookup x).getD x

/-- The declared width of a wire (`0` if undeclared or not a bit vector). -/
def declWidth (m : Module) (x : String) : Nat :=
  match m.wires.find? (fun p => p.name == x) with
  | some { ty := .bitVector k, .. } => k
  | _ => 0

/-- Validation state: names defined so far, the substitution aliases `S`
(what the output's references use), the value aliases `V` (substitution plus
equal-width plain aliases), and the canonical right-hand side of each
representative. -/
structure MergeCheck where
  defined : List String := []
  S : List (String × String) := []
  V : List (String × String) := []
  R : List (String × Expr) := []

/-- One statement of the old body against the same statement of the new one. -/
def validateStep (wOf : String → Nat) (allLhs : List String) (st : MergeCheck) :
    Stmt → Stmt → Option MergeCheck
  | .assign l e, .assign l' e' =>
    if l' ≠ l ∨ l ∈ st.defined then none
    else if !(Sparkle.IR.Reorder.refsOf e).all (fun x => !allLhs.contains x || st.defined.contains x)
    then none
    else
      let cV := renameE (aliasOf st.V) e
      if e' = renameE (aliasOf st.S) e then
        let V := match e with
          | .ref x => if x ≠ l ∧ wOf l = wOf x then (l, aliasOf st.V x) :: st.V else st.V
          | _ => st.V
        some { defined := l :: st.defined, S := st.S, V := V, R := (l, cV) :: st.R }
      else match e' with
        | .ref y =>
          if y ≠ l ∧ st.defined.contains y ∧ (st.S.lookup y).isNone ∧
              st.R.lookup y = some cV ∧ wOf l = wOf y then
            some { defined := l :: st.defined, S := (l, y) :: st.S,
                   V := (l, aliasOf st.V y) :: st.V, R := st.R }
          else none
        | _ => none
  | _, _ => none

/-- `new` computes the same environment as `old`: checked statement by statement. -/
def validateMerge (wOf : String → Nat) (old new : List Stmt) : Bool :=
  let allLhs := old.filterMap fun st => match st with
    | .assign l _ => some l
    | _ => none
  let rec go (st : MergeCheck) : List Stmt → List Stmt → Bool
    | [], [] => true
    | a :: as, b :: bs =>
      match validateStep wOf allLhs st a b with
      | some st' => go st' as bs
      | none => false
    | _, _ => false
  go {} old new

def isAssign : Stmt → Bool
  | .assign .. => true
  | _ => false

/-- Merge bisimilar nodes.  Internal (`_tmp_*`) non-representatives become
    plain aliases `n := rep` (a duplicate register's output turns into an
    alias of the surviving register); user-named nodes keep their own
    statement is replaced by the alias as well (see below). -/
def mergeDuplicatesRaw (m : Module) : Module := Id.run do
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
  let mut rep : HashMap Nat String := {}
  for (n, _) in nodes do
    let k := cls.getD n 0
    if !rep.contains k then rep := rep.insert k n
  -- Every non-representative becomes an alias — user-named ones too: the
  -- optimizer's DCE keeps observable/output wires, so a name read at
  -- runtime survives as `_gen_x := rep`, and a name nobody declared
  -- observable was never guaranteed to survive CSE anyway.
  let mut subst : HashMap String String := {}
  for (n, _) in nodes do
    let r := rep.getD (cls.getD n 0) n
    if r != n then subst := subst.insert n r
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

/-- The merge, validated on combinational bodies: a combinational module's
merge is kept only if `validateMerge` accepts it (else the module is returned
unchanged). Bodies with registers, memories or instances keep the unvalidated
merge. -/
def mergeDuplicates (m : Module) : Module :=
  let r := mergeDuplicatesRaw m
  if m.body.all isAssign then
    if validateMerge (declWidth m) m.body r.body then
      { m with body := r.body, assertions := r.assertions }
    else m
  else r

def mergeDuplicatesDesign (d : Design) : Design :=
  { d with modules := d.modules.map mergeDuplicates }

end Sparkle.IR.RegDedup
