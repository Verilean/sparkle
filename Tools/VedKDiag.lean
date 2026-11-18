import Lean

/-! Diagnostic only (never changes behaviour): iterative, sharing-preserving size/depth statistics
of a kernel term, written to the file named by the environment variable `VED_KDIAG_OUT`. -/
namespace Tools.VedKDiag
open Lean

structure Stats where
  nodes : Nat
  height : Nat
  /-- path from the root: (kind, head const name or "") -/
  path : Array (String × String)

unsafe def addrOf (e : Expr) : USize := ptrAddrUnsafe e
@[implemented_by addrOf] opaque addr (e : Expr) : USize

def kindOf : Expr → String
  | .app .. => "app" | .lam .. => "lam" | .forallE .. => "forallE" | .letE .. => "letE"
  | .mdata .. => "mdata" | .proj .. => "proj" | .lit .. => "lit" | .const .. => "const"
  | .fvar .. => "fvar" | .bvar .. => "bvar" | .sort .. => "sort" | .mvar .. => "mvar"

def childrenOf : Expr → Array Expr
  | .app f a => #[f, a]
  | .lam _ t b _ => #[t, b]
  | .forallE _ t b _ => #[t, b]
  | .letE _ t v b _ => #[t, v, b]
  | .mdata _ e => #[e]
  | .proj _ _ e => #[e]
  | _ => #[]

/-- iterative post-order over the DAG; `heights` memo (by pointer) of the height, `best` the child
index realising it.  Returns the number of nodes newly visited. -/
unsafe def walkU (root : Expr) (heights : IO.Ref (Std.HashMap USize (Nat × Nat))) : IO Nat := do
  let mut stack : Array (Expr × Bool) := #[(root, false)]
  let mut fresh := 0
  let mut h ← heights.get
  while !stack.isEmpty do
    let (e, done) := stack.back!
    stack := stack.pop
    let k := addrOf e
    if h.contains k then continue
    let cs := childrenOf e
    if !done then
      stack := stack.push (e, true)
      for c in cs do
        if !h.contains (addrOf c) then stack := stack.push (c, false)
    else
      let mut best := 0
      let mut bi := 0
      let mut i := 0
      for c in cs do
        let ch := (h.getD (addrOf c) (0, 0)).1
        if ch > best || i == 0 then best := ch; bi := i
        i := i + 1
      h := h.insert k (best + 1, bi)
      fresh := fresh + 1
  heights.set h
  return fresh

@[implemented_by walkU] opaque walk (root : Expr) (heights : IO.Ref (Std.HashMap USize (Nat × Nat))) : IO Nat

unsafe def lookupU (heights : Std.HashMap USize (Nat × Nat)) (e : Expr) : Nat × Nat :=
  heights.getD (addrOf e) (0, 0)
@[implemented_by lookupU] opaque lookup (heights : Std.HashMap USize (Nat × Nat)) (e : Expr) : Nat × Nat

def headName (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => n.toString
  | _ => ""

/-- deepest path, compressed into runs `kind[head]xN` -/
def deepestPath (root : Expr) (heights : Std.HashMap USize (Nat × Nat)) : IO (Array (String × Nat)) := do
  let mut e := root
  let mut runs : Array (String × Nat) := #[]
  let mut fuel := 100000000
  while fuel > 0 do
    fuel := fuel - 1
    let cs := childrenOf e
    let lbl := match e with
      | .app .. => s!"app[{headName e}]"
      | .const n _ => s!"const[{n}]"
      | .proj s i _ => s!"proj[{s}.{i}]"
      | .lit (.natVal n) => s!"lit[nat {n.log2}bits]"
      | _ => kindOf e
    match runs.back? with
    | some (l, n) => if l == lbl then runs := runs.pop.push (l, n + 1) else runs := runs.push (lbl, 1)
    | none => runs := runs.push (lbl, 1)
    if cs.isEmpty then break
    let (_, bi) := lookup heights e
    e := cs[bi]!
  return runs

def append (msg : String) : IO Unit := do
  match ← IO.getEnv "VED_KDIAG_OUT" with
  | some p => IO.FS.withFile p .append fun h => h.putStrLn msg
  | none => IO.eprintln msg

def summarise (label : String) (root : Expr) : IO Unit := do
  let hs ← IO.mkRef ({} : Std.HashMap USize (Nat × Nat))
  let n ← walk root hs
  let h ← hs.get
  let (ht, _) := lookup h root
  append s!"KDIAG {label}: dagNodes={n} height={ht} approxDepth={root.approxDepth}"
  let runs ← deepestPath root h
  append s!"KDIAG {label}: deepest path runs={runs.size}"
  let mut line := ""
  for (l, c) in runs do
    line := line ++ s!" {l}x{c}"
    if line.length > 1500 then append s!"KDIAG {label}: path{line}"; line := ""
  append s!"KDIAG {label}: path{line}"

/-- constants of `e` (shared traversal) -/
unsafe def constsU (e : Expr) : IO (Array Name) := do
  let mut seen : Std.HashSet USize := {}
  let mut stack := #[e]
  let mut out : Std.HashSet Name := {}
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    if seen.contains (addrOf x) then continue
    seen := seen.insert (addrOf x)
    if let .const n _ := x then out := out.insert n
    for c in childrenOf x do stack := stack.push c
  return out.toArray
@[implemented_by constsU] opaque consts (e : Expr) : IO (Array Name)

unsafe def appsOfU (e : Expr) (names : Std.HashSet Name) : IO (Array Expr) := do
  let mut seen : Std.HashSet USize := {}
  let mut stack := #[e]
  let mut out : Array Expr := #[]
  while !stack.isEmpty do
    let x := stack.back!
    stack := stack.pop
    if seen.contains (addrOf x) then continue
    seen := seen.insert (addrOf x)
    if x.isApp then
      if let .const n _ := x.getAppFn then
        if names.contains n then out := out.push x
    for c in childrenOf x do stack := stack.push c
  return out
@[implemented_by appsOfU] opaque appsOf (e : Expr) (names : Std.HashSet Name) : IO (Array Expr)

/-- the whole diagnostic: pf and expected, and the auxiliary theorems (not from an imported module)
referenced from pf. -/
def run (env : Environment) (pf expected : Expr) : IO Unit := do
  summarise "pf" pf
  summarise "expected" expected
  let cs ← consts pf
  let aux := cs.filter fun n => match env.find? n with
    | some (.thmInfo _) => (env.getModuleIdxFor? n).isNone
    | _ => false
  append s!"KDIAG aux theorems referenced from pf: {aux.size} (all consts {cs.size})"
  let auxS : Std.HashSet Name := aux.foldl (·.insert ·) {}
  let apps ← appsOf pf auxS
  append s!"KDIAG aux applications in pf (shared nodes): {apps.size}"
  -- per aux constant
  let mut rows : Array (Name × Nat × Nat × Nat × Nat) := #[]
  for n in aux do
    if let some (.thmInfo ti) := env.find? n then
      let hT ← IO.mkRef ({} : Std.HashMap USize (Nat × Nat))
      let nT ← walk ti.type hT
      let hV ← IO.mkRef ({} : Std.HashMap USize (Nat × Nat))
      let nV ← walk ti.value hV
      rows := rows.push (n, nT, (lookup (← hT.get) ti.type).1, nV, (lookup (← hV.get) ti.value).1)
  for (n, nT, hT, nV, hV) in rows do
    append s!"KDIAG aux {n}: typeNodes={nT} typeH={hT} valueNodes={nV} valueH={hV}"
  -- application arguments in pf
  let hP ← IO.mkRef ({} : Std.HashMap USize (Nat × Nat))
  let _ ← walk pf hP
  let hp ← hP.get
  let mut cnt := 0
  for a in apps do
    cnt := cnt + 1
    let args := a.getAppArgs
    let mut maxH := 0
    let mut sumN := 0
    let hA ← IO.mkRef ({} : Std.HashMap USize (Nat × Nat))
    for x in args do
      maxH := max maxH (lookup hp x).1
      sumN := sumN + (← walk x hA)
    append s!"KDIAG app {a.getAppFn.constName!} nargs={args.size} argMaxH={maxH} argDagNodes={sumN} appH={(lookup hp a).1}"
end Tools.VedKDiag
