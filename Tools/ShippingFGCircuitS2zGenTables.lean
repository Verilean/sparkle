import Tools.ShippingFGCircuitS2zEnvCheck
import Tools.ShippingFGCircuitS1kStmt
set_option autoImplicit false
-- FG circuit pilot S2z step 2: UNTRUSTED generator of `Sparkle/Compiler/PilotEnvTables.lean` (the rows of `hftDeltaL` / `hftGammaL` as Lean source).
-- Nothing here is trusted: the equality of the generated rows with `hftDeltaL`/`hftGammaL` is a kernel-checked theorem (`Tools.ShippingFGCircuitS2zPin`). No sorry/axiom/native_decide/TRUSTED/law.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Tools.ShippingFGCircuitS2zGenTables
open Lean Tools.ShippingFGCircuitS2zEnvCheck Tools.ShippingFGCircuitS1mCD

inductive N
  | leaf (src : String)
  | app (f a : Nat)
  | lam (n : String) (t b : Nat) (bi : String)
  | pi (n : String) (t b : Nat) (bi : String)
  | letE (n : String) (t v b : Nat) (nd : Bool)
  | proj (s : String) (i x : Nat)
  deriving BEq, Hashable, Inhabited

/-- hash-consing is by FULL structure (binder names included): `Expr`'s own `BEq`/`Hashable` identify alpha-equivalent terms, which are different terms for the kernel -/
structure GS where
  names : Std.HashMap Name String := {}
  nameOrder : Array (String × String) := #[]
  nodes : Array N := #[]
  ids : Std.HashMap N Nat := {}

abbrev G := StateM GS

partial def nameSrc (n : Name) : G String := do
  match n with
  | .anonymous => pure "Name.anonymous"
  | _ =>
    if let some s := (← get).names[n]? then return s
    let body ← match n with
      | .str p s => do pure s!"Name.mkStr {← nameSrc p} {s.quote}"
      | .num p k => do pure s!"Name.mkNum {← nameSrc p} {k}"
      | .anonymous => pure "Name.anonymous"
    let id := s!"nm{(← get).names.size}"
    modify fun st => { st with names := st.names.insert n id, nameOrder := st.nameOrder.push (id, body) }
    pure id

partial def levelSrc : Level → G String
  | .zero => pure "Level.zero"
  | .succ l => do pure s!"(Level.succ {← levelSrc l})"
  | .max a b => do pure s!"(Level.max {← levelSrc a} {← levelSrc b})"
  | .imax a b => do pure s!"(Level.imax {← levelSrc a} {← levelSrc b})"
  | .param n => do pure s!"(Level.param {← nameSrc n})"
  | .mvar _ => pure "(panic! \"mvar level\")"

def biSrc : BinderInfo → String
  | .default => "BinderInfo.default" | .implicit => "BinderInfo.implicit"
  | .strictImplicit => "BinderInfo.strictImplicit" | .instImplicit => "BinderInfo.instImplicit"

def intern (n : N) : G Nat := do
  if let some i := (← get).ids[n]? then return i
  let i := (← get).nodes.size
  modify fun st => { st with nodes := st.nodes.push n, ids := st.ids.insert n i }
  pure i

partial def internE (e : Expr) : G Nat := do
  match e with
  | .bvar i => intern (.leaf s!"Expr.bvar {i}")
  | .sort l => do intern (.leaf s!"Expr.sort {← levelSrc l}")
  | .const n ls => do
      let mut out := #[]
      for l in ls do out := out.push (← levelSrc l)
      intern (.leaf s!"Expr.const {← nameSrc n} [{", ".intercalate out.toList}]")
  | .app f a => do let f ← internE f; let a ← internE a; intern (.app f a)
  | .lam n t b bi => do let n ← nameSrc n; let t ← internE t; let b ← internE b; intern (.lam n t b (biSrc bi))
  | .forallE n t b bi => do let n ← nameSrc n; let t ← internE t; let b ← internE b; intern (.pi n t b (biSrc bi))
  | .letE n t v b nd => do let n ← nameSrc n; let t ← internE t; let v ← internE v; let b ← internE b; intern (.letE n t v b nd)
  | .lit (.natVal k) => intern (.leaf s!"Expr.lit (Literal.natVal {k})")
  | .lit (.strVal s) => intern (.leaf s!"Expr.lit (Literal.strVal {s.quote})")
  | .proj s i x => do let s ← nameSrc s; let x ← internE x; intern (.proj s i x)
  | .mdata _ _ => intern (.leaf "(panic! \"mdata\")")
  | .fvar _ => intern (.leaf "(panic! \"fvar\")")
  | .mvar _ => intern (.leaf "(panic! \"mvar\")")

def kids : N → List Nat
  | .leaf _ => [] | .app f a => [f, a] | .lam _ t b _ => [t, b] | .pi _ t b _ => [t, b]
  | .letE _ t v b _ => [t, v, b] | .proj _ _ x => [x]

/-- the source of a node whose children are referenced by `r` -/
def body (r : Nat → String) : N → String
  | .leaf s => s
  | .app f a => s!"Expr.app {r f} {r a}"
  | .lam n t b bi => s!"Expr.lam {n} {r t} {r b} {bi}"
  | .pi n t b bi => s!"Expr.forallE {n} {r t} {r b} {bi}"
  | .letE n t v b nd => s!"Expr.letE {n} {r t} {r v} {r b} {nd}"
  | .proj s i x => s!"Expr.proj {s} {i} {r x}"

def genSource : String := Id.run do
  let dl := defTuples hftDeltaL
  let gl := ctorTuples hftGammaL
  let act : G (Array (String × List String × Nat) × Array String × String) := do
    let mut rows := #[]
    for (c, lps, v) in dl do
      let mut lp := []
      for p in lps do lp := lp ++ [← nameSrc p]
      rows := rows.push (← nameSrc c, lp, ← internE v)
    let mut ctorRows := #[]
    for (c, ind, np, nf) in gl do
      ctorRows := ctorRows.push s!"  ({← nameSrc c}, {← nameSrc ind}, {np}, {nf})"
    let rootN ← nameSrc Tools.ShippingFGCircuitS1kStmt.hftRoot
    pure (rows, ctorRows, rootN)
  let ((rows, ctorRows, rootN), st) := act.run {}
  -- parents count
  let mut cnt : Array Nat := Array.replicate st.nodes.size 0
  for n in st.nodes do
    for k in kids n do cnt := cnt.modify k (· + 1)
  for (_, _, v) in rows do cnt := cnt.modify v (· + 1)
  let isShared (i : Nat) : Bool := cnt[i]! ≥ 2 && !(match st.nodes[i]! with | .leaf _ => true | _ => false)
  let rec ref (i : Nat) (fuel : Nat) : String :=
    match fuel with
    | 0 => "(panic! \"fuel\")"
    | fuel + 1 => if isShared i then s!"ex{i}" else s!"({body (fun j => ref j fuel) st.nodes[i]!})"
  let mut out := "import Lean\nimport Sparkle.Compiler.EnvTableCheck\n\n"
  out := out ++ "/-! # The pilot's environment tables (GENERATED, untrusted)\n\n"
  out := out ++ "Generated by `Tools/ShippingFGCircuitS2zGenTables.lean` from the rows `hftDeltaL` / `hftGammaL` of `Tools.ShippingFGCircuitS2tHft.hftObCDT_of_tablesT`.\n"
  out := out ++ "Their equality with the tables the final statement mentions is a kernel-checked theorem in `Tools/ShippingFGCircuitS2zPin.lean`; nothing here is trusted. -/\n"
  out := out ++ "namespace Sparkle.Compiler.PilotEnvTables\nopen Lean Sparkle.Compiler.EnvTableCheck\nset_option maxRecDepth 100000\n\n"
  for (id, b) in st.nameOrder do out := out ++ s!"def {id} : Name := {b}\n"
  out := out ++ "\n"
  let mut i := 0
  for n in st.nodes do
    if isShared i then out := out ++ s!"def ex{i} : Expr := {body (fun j => ref j 100000) n}\n"
    i := i + 1
  let defRows := rows.map fun (c, lp, v) => s!"  ({c}, [{", ".intercalate lp}], {ref v 100000})"
  out := out ++ "\ndef hftDefRows : List (Name × List Name × Expr) := [\n" ++ ",\n".intercalate defRows.toList ++ "]\n"
  out := out ++ "\ndef hftCtorRows : List (Name × Name × Nat × Nat) := [\n" ++ ",\n".intercalate ctorRows.toList ++ "]\n"
  out := out ++ "\n/-- the declaration whose start environment is checked -/\ndef hftRootName : Name := " ++ rootN ++ "\n"
  out := out ++ "\n/-- the tables against the environment: definitions, constructors, `List.rec` -/\ndef tablesOkB (env : Environment) : Bool :=\n  defsOkB env hftDefRows && ctorsOkB env hftCtorRows && recOkB env\n"
  out := out ++ "\n/-- the check of the Off entry: the pilot root's start environment must match the tables; every other declaration is unconstrained -/\ndef startEnvOk (declName : Name) (env : Environment) : Bool :=\n  if declName == hftRootName then tablesOkB env else true\n"
  out := out ++ "\nend Sparkle.Compiler.PilotEnvTables\n"
  return out

end Tools.ShippingFGCircuitS2zGenTables
