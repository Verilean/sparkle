/-
  IR Optimization Pass

  Eliminates wide concat/slice chains that arise from tuple packing/unpacking
  in Signal.loop bodies. Transforms:
    _tmp = concat(a, b, c, ...)
    x = _tmp[hi:lo]              -- maps exactly to 'a'
  Into:
    x = a                        -- direct reference

  Also performs dead-code elimination on unused wires.
-/

import Sparkle.IR.AST
import Sparkle.IR.Type
import Std.Data.HashMap

namespace Sparkle.IR.Optimize

open Sparkle.IR.AST
open Sparkle.IR.Type
open Std (HashMap)

instance : Inhabited Expr := ⟨.const 0 0⟩

/-- O(1) lookup maps built from module data -/
abbrev DefMap := HashMap String Expr
abbrev WidthMap := HashMap String Nat

/-- Build a name → defining-expression map from assign statements -/
def buildDefMap (stmts : List Stmt) : DefMap :=
  stmts.foldl (fun m s =>
    match s with
    | .assign lhs rhs => m.insert lhs rhs
    | _ => m
  ) {}

/-- Build name → bit-width map from module ports and wires -/
def buildWidthMap (m : Module) : WidthMap :=
  let addPorts (wm : WidthMap) (ports : List Port) :=
    ports.foldl (fun acc p => acc.insert p.name p.ty.bitWidth) wm
  addPorts (addPorts (addPorts {} m.inputs) m.outputs) m.wires

/-- Infer the bit-width of an expression -/
partial def inferWidth (wm : WidthMap) : Expr → Nat
  | .const _ w => w
  | .ref name => wm.getD name 0
  | .slice _ hi lo => hi - lo + 1
  | .concat args => args.foldl (fun acc a => acc + inferWidth wm a) 0
  | .op .eq _ | .op .lt_u _ | .op .lt_s _ | .op .le_u _
  | .op .le_s _ | .op .gt_u _ | .op .gt_s _ | .op .ge_u _
  | .op .ge_s _ => 1
  | .op .mux args =>
    match args with
    | [_, t, _] => inferWidth wm t
    | _ => 0
  | .op _ args =>
    match args with
    | [a, _] => inferWidth wm a
    | [a] => inferWidth wm a
    | _ => 0
  | .index _ _ => 0

/-- Try to resolve a slice of a concat to a direct reference or narrower slice.

    For concat [a(wa), b(wb), c(wc), ...] with total width T:
    - a occupies [T-1 : T-wa]
    - b occupies [T-wa-1 : T-wa-wb]
    - etc. (MSB-first layout, same as Verilog {a, b, c, ...})

    Returns the replacement if the slice maps entirely within one arg. -/
partial def resolveSliceOfConcatAux
    (remaining : List (Expr × Nat)) (hiEdge : Nat)
    (sliceHi sliceLo : Nat) : Option Expr :=
  match remaining with
  | [] => none
  | (arg, w) :: rest =>
    if w == 0 then resolveSliceOfConcatAux rest hiEdge sliceHi sliceLo
    else
      let argHi := hiEdge - 1
      let argLo := hiEdge - w
      if sliceHi ≤ argHi && sliceLo ≥ argLo then
        if sliceHi == argHi && sliceLo == argLo then
          some arg
        else
          some (.slice arg (sliceHi - argLo) (sliceLo - argLo))
      else if sliceHi < argLo then
        resolveSliceOfConcatAux rest (hiEdge - w) sliceHi sliceLo
      else
        none

def resolveSliceOfConcat (args : List Expr) (widths : List Nat)
    (sliceHi sliceLo : Nat) : Option Expr :=
  let totalWidth := widths.foldl (· + ·) 0
  resolveSliceOfConcatAux (args.zip widths) totalWidth sliceHi sliceLo

/-- Resolve a slice of a named wire through the defMap, recursively following:
    1. Ref aliases:    X = Y       → slice(Y, hi, lo)
    2. Slice chains:  X = Y[h:l]  → slice(Y, l+hi, l+lo)
    3. Concat args:   X = {a, b}  → a (if slice matches exactly)
    Depth-limited to prevent infinite recursion on malformed IR. -/
partial def resolveSlice (dm : DefMap) (wm : WidthMap)
    (name : String) (hi lo : Nat) (fuel : Nat) : Expr :=
  if fuel == 0 then .slice (.ref name) hi lo
  else match dm.get? name with
    | some (.ref otherName) =>
      resolveSlice dm wm otherName hi lo (fuel - 1)
    | some (.slice innerExpr innerHi innerLo) =>
      let newHi := innerLo + hi
      let newLo := innerLo + lo
      if newHi ≤ innerHi then
        match innerExpr with
        | .ref innerName =>
          resolveSlice dm wm innerName newHi newLo (fuel - 1)
        | _ => .slice innerExpr newHi newLo
      else .slice (.ref name) hi lo
    | some (.concat args) =>
      let widths := args.map (inferWidth wm)
      if widths.any (· == 0) then .slice (.ref name) hi lo
      else match resolveSliceOfConcat args widths hi lo with
        | some (.ref resolvedName) => .ref resolvedName
        | some (.slice (.ref innerName) innerHi innerLo) =>
          resolveSlice dm wm innerName innerHi innerLo (fuel - 1)
        | some other => other
        | none => .slice (.ref name) hi lo
    | _ => .slice (.ref name) hi lo

/-- Fold constant expressions -/
def foldConstants : Expr → Expr
  -- mux(true, t, e) = t
  | .op .mux [.const 1 1, t, _] => t
  -- mux(false, t, e) = e
  | .op .mux [.const 0 1, _, e] => e
  -- eq(a, b) where both constants
  | .op .eq [.const a _, .const b _] => .const (if a == b then 1 else 0) 1
  -- add(0, e) = e, add(e, 0) = e
  | .op .add [.const 0 _, e] => e
  | .op .add [e, .const 0 _] => e
  -- or(0, e) = e, or(e, 0) = e
  | .op .or [.const 0 _, e] => e
  | .op .or [e, .const 0 _] => e
  -- and(0, e) = 0, and(e, 0) = 0
  | .op .and [.const 0 w, _] => .const 0 w
  | .op .and [_, .const 0 w] => .const 0 w
  -- mux(0, t, e) = e (0 in any width is false)
  | .op .mux [.const 0 _, _, e] => e
  -- not(not(x)) = x
  | .op .not [.op .not [x]] => x
  -- (const-const folding deferred: Int.toNat loses sign information)
  -- slice of constant
  | .slice (.const v w) hi lo =>
    if hi < w then
      let modulus := (2 : Int) ^ w
      let unsigned := ((v % modulus) + modulus) % modulus
      let shifted := unsigned.toNat / (2 ^ lo)
      let mask := 2 ^ (hi - lo + 1) - 1
      .const (Int.ofNat (shifted &&& mask)) (hi - lo + 1)
    else .slice (.const v w) hi lo
  | e => e

/-- Optimize a single expression by resolving slice chains, folding constants,
    and propagating constant-assigned wires. -/
partial def optimizeExpr (dm : DefMap) (wm : WidthMap) : Expr → Expr
  | .ref name => .ref name  -- Note: constant propagation deferred (needs use-count guard)
  | .slice (.ref name) hi lo => foldConstants (resolveSlice dm wm name hi lo 500)
  | .slice e hi lo => foldConstants (.slice (optimizeExpr dm wm e) hi lo)
  | .op op args => foldConstants (.op op (args.map (optimizeExpr dm wm ·)))
  | .concat args => .concat (args.map (optimizeExpr dm wm ·))
  | .index arr idx => .index (optimizeExpr dm wm arr) (optimizeExpr dm wm idx)
  | e => e

/-- Count uses of each wire name in an expression -/
partial def countExprUses (e : Expr) (counts : HashMap String Nat)
    : HashMap String Nat :=
  match e with
  | .ref name => counts.insert name ((counts.getD name 0) + 1)
  | .const _ _ => counts
  | .slice inner _ _ => countExprUses inner counts
  | .concat args => args.foldl (fun acc a => countExprUses a acc) counts
  | .op _ args => args.foldl (fun acc a => countExprUses a acc) counts
  | .index arr idx => countExprUses idx (countExprUses arr counts)

/-- Count uses of each wire across all statements -/
def countAllUses (stmts : List Stmt) : HashMap String Nat :=
  stmts.foldl (fun counts stmt =>
    match stmt with
    | .assign _ rhs => countExprUses rhs counts
    | .register _ _ _ input _ => countExprUses input counts
    | .memory _ _ _ _ wa wd we ra _ _ =>
      [wa, wd, we, ra].foldl (fun acc e => countExprUses e acc) counts
    | .inst _ _ conns =>
      conns.foldl (fun acc (_, e) => countExprUses e acc) counts
  ) {}

/-- Optimize a single statement's expressions -/
def optimizeStmt (dm : DefMap) (wm : WidthMap) : Stmt → Stmt
  | .assign lhs rhs => .assign lhs (optimizeExpr dm wm rhs)
  | .register output clock reset input initValue =>
    .register output clock reset (optimizeExpr dm wm input) initValue
  | .memory name aw dw clk wa wd we ra rd cr =>
    .memory name aw dw clk
      (optimizeExpr dm wm wa) (optimizeExpr dm wm wd)
      (optimizeExpr dm wm we) (optimizeExpr dm wm ra) rd cr
  | .inst modName instName conns =>
    .inst modName instName (conns.map fun (p, e) => (p, optimizeExpr dm wm e))

/-- Recursively substitute inlinable references with their defining expressions -/
partial def substituteExpr (dm : DefMap) (inlinable : HashMap String Bool)
    (fuel : Nat) : Expr → Expr
  | .ref name =>
    if fuel == 0 then .ref name
    else if inlinable.getD name false then
      match dm.get? name with
      | some defExpr => substituteExpr dm inlinable (fuel - 1) defExpr
      | none => .ref name
    else .ref name
  | .const v w => .const v w
  | .slice e hi lo => .slice (substituteExpr dm inlinable fuel e) hi lo
  | .concat args => .concat (args.map (substituteExpr dm inlinable fuel ·))
  | .op op args => .op op (args.map (substituteExpr dm inlinable fuel ·))
  | .index arr idx =>
    .index (substituteExpr dm inlinable fuel arr) (substituteExpr dm inlinable fuel idx)

/-- Inline single-use wires: replace references with their defining expressions
    and remove the now-dead assign statements. -/
def inlineSingleUseWires (m : Module) (body : List Stmt)
    (observableWires : Option (List String) := none) : List Stmt × List Port :=
  let dm := buildDefMap body
  let useCounts := countAllUses body

  -- Build sets of names that must NOT be inlined
  let outputSet := m.outputs.foldl (fun s p => s.insert p.name true) ({} : HashMap String Bool)
  let registerOutputs := body.foldl (fun s stmt =>
    match stmt with
    | .register output .. => s.insert output true
    | _ => s
  ) ({} : HashMap String Bool)
  let memoryReadData := body.foldl (fun s stmt =>
    match stmt with
    | .memory _ _ _ _ _ _ _ _ rd _ => s.insert rd true
    | _ => s
  ) ({} : HashMap String Bool)

  -- Build inlinable set: used exactly once, not output/register/memory-read/named
  let inlinable := body.foldl (fun s stmt =>
    match stmt with
    | .assign lhs _ =>
      if (useCounts.getD lhs 0) == 1
        && !outputSet.contains lhs
        && !registerOutputs.contains lhs
        && !memoryReadData.contains lhs
        && (match observableWires with
            | some ws => !ws.contains lhs
            | none => !lhs.startsWith "_gen_")  -- _gen_ wires are JIT-observable
      then s.insert lhs true
      else s
    | _ => s
  ) ({} : HashMap String Bool)

  -- Substitute in all statements
  let inlinedBody := body.map fun stmt =>
    match stmt with
    | .assign lhs rhs =>
      .assign lhs (substituteExpr dm inlinable 100 rhs)
    | .register output clock reset input initValue =>
      .register output clock reset (substituteExpr dm inlinable 100 input) initValue
    | .memory name aw dw clk wa wd we ra rd cr =>
      .memory name aw dw clk
        (substituteExpr dm inlinable 100 wa) (substituteExpr dm inlinable 100 wd)
        (substituteExpr dm inlinable 100 we) (substituteExpr dm inlinable 100 ra) rd cr
    | .inst modName instName conns =>
      .inst modName instName (conns.map fun (p, e) => (p, substituteExpr dm inlinable 100 e))

  -- Remove inlined assignments
  let filteredBody := inlinedBody.filter fun stmt =>
    match stmt with
    | .assign lhs _ => !inlinable.getD lhs false
    | _ => true

  -- Remove inlined wires from wire list
  let filteredWires := m.wires.filter fun w => !inlinable.getD w.name false

  (filteredBody, filteredWires)

/-- Optimize a module: eliminate concat/slice chains, then remove dead code -/
def optimizeModule (m : Module)
    (observableWires : Option (List String) := none) : Module :=
  if m.isPrimitive then m
  else
    let wm := buildWidthMap m
    let dm := buildDefMap m.body

    -- Phase 1: Replace slice-of-concat with direct references
    let optimizedBody := m.body.map (optimizeStmt dm wm)

    -- Phase 2: Dead code elimination
    let useCounts := countAllUses optimizedBody
    let outputSet := m.outputs.foldl (fun s p => s.insert p.name true) ({} : HashMap String Bool)

    let prunedBody := optimizedBody.filter fun stmt =>
      match stmt with
      | .assign lhs _ =>
        outputSet.contains lhs || (useCounts.getD lhs 0) > 0
      | _ => true

    let prunedWires := m.wires.filter fun w =>
      (useCounts.getD w.name 0) > 0 || outputSet.contains w.name

    let m2 := { m with body := prunedBody, wires := prunedWires }

    -- Phase 3: Single-use wire inlining
    let (inlinedBody, inlinedWires) := inlineSingleUseWires m2 m2.body observableWires

    -- Phase 4: Dead code elimination (again, to catch newly-dead wires)
    let useCounts2 := countAllUses inlinedBody
    let finalBody := inlinedBody.filter fun stmt =>
      match stmt with
      | .assign lhs _ =>
        outputSet.contains lhs || (useCounts2.getD lhs 0) > 0
      | _ => true

    let finalWires := inlinedWires.filter fun w =>
      (useCounts2.getD w.name 0) > 0 || outputSet.contains w.name

    { m with body := finalBody, wires := finalWires }

/-- Optimize all modules in a design -/
def optimizeDesign (d : Design)
    (observableWires : Option (List String) := none) : Design :=
  { d with modules := d.modules.map (optimizeModule · observableWires) }

end Sparkle.IR.Optimize
