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

/-- Convert Int constant to unsigned Nat using two's complement with given bit width.
    e.g., toUnsigned (-1) 32 = 0xFFFFFFFF, toUnsigned (-1) 8 = 0xFF -/
private def toUnsigned (v : Int) (w : Nat) : Nat :=
  let modulus := (2 : Nat) ^ w
  ((v % modulus + modulus) % modulus).toNat

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
  -- mux(cond, 1, 0) = cond (boolean identity)
  | .op .mux [cond, .const 1 1, .const 0 1] => cond
  -- mux(cond, 0, 1) = not(cond)
  | .op .mux [cond, .const 0 1, .const 1 1] => .op .not [cond]
  -- eq(x, 0) used as boolean → not(x) (only for 1-bit result context)
  -- This is handled in emitExpr instead since foldConstants lacks width context
  -- not(not(x)) = x
  | .op .not [.op .not [x]] => x
  -- and(x, all-ones) = x (identity mask removal)
  | .op .and [x, .const v w] =>
    if v != 0 && v == (2 ^ w - 1 : Int) then x
    else .op .and [x, .const v w]
  | .op .and [.const v w, x] =>
    -- Check const-const case first
    match x with
    | .const b _ => .const (Int.ofNat (toUnsigned v w &&& toUnsigned b w)) w
    | _ => if v != 0 && v == (2 ^ w - 1 : Int) then x
           else .op .and [.const v w, x]
  -- Fully constant binary operations (use toUnsigned for correct two's complement)
  | .op .add [.const a w, .const b _] =>
    let r := toUnsigned a w + toUnsigned b w
    .const (Int.ofNat (r % (2 ^ w))) w
  | .op .sub [.const a w, .const b _] =>
    let r := toUnsigned a w + (2 ^ w) - toUnsigned b w
    .const (Int.ofNat (r % (2 ^ w))) w
  | .op .or [.const a w, .const b _] =>
    .const (Int.ofNat (toUnsigned a w ||| toUnsigned b w)) w
  | .op .xor [.const a w, .const b _] =>
    .const (Int.ofNat (toUnsigned a w ^^^ toUnsigned b w)) w
  | .op .not [.const v w] =>
    .const (Int.ofNat (toUnsigned v w ^^^ ((1 <<< w) - 1))) w
  | .op .shl [.const a w, .const b _] =>
    .const (Int.ofNat ((toUnsigned a w <<< toUnsigned b w) % (2 ^ w))) w
  | .op .shr [.const a w, .const b _] =>
    .const (Int.ofNat (toUnsigned a w >>> toUnsigned b w)) w
  | .op .lt_u [.const a aw, .const b bw] =>
    .const (if toUnsigned a aw < toUnsigned b bw then 1 else 0) 1
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

/-- Collect all reference names from an expression. -/
partial def collectExprRefs : Expr → List String
  | .ref name => [name]
  | .op _ args => args.flatMap collectExprRefs
  | .concat args => args.flatMap collectExprRefs
  | .slice e _ _ => collectExprRefs e
  | .index a i => collectExprRefs a ++ collectExprRefs i
  | .const _ _ => []

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
    (observableWires : Option (List String) := none)
    (protectedWires : HashMap String Bool := {}) : List Stmt × List Port :=
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
        && !protectedWires.contains lhs
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

/-- Propagate constant and simple-ref assignments into all uses.
    x = const → replace all refs to x with const
    x = y     → replace all refs to x with y (alias elimination)
    This runs even for _gen_ (JIT-observable) wires since they're just aliases. -/
def propagateConstants (body : List Stmt) (dm : DefMap) : List Stmt × DefMap :=
  -- Find wires assigned to a constant or simple ref
  let constMap := body.foldl (fun (acc : HashMap String Expr) stmt =>
    match stmt with
    | .assign lhs rhs =>
      match rhs with
      | .const _ _ => acc.insert lhs rhs
      | .ref name =>
        -- Follow chains: if name is also a const/ref, resolve
        match acc.get? name with
        | some resolved => acc.insert lhs resolved
        | none => acc.insert lhs rhs
      | _ => acc
    | _ => acc
  ) {}
  -- Substitute all references
  let subst (e : Expr) : Expr :=
    match e with
    | .ref name => match constMap.get? name with
      | some replacement => replacement
      | none => e
    | _ => e
  let rec substExpr : Expr → Expr
    | .ref name => match constMap.get? name with
      | some replacement => replacement
      | none => .ref name
    | .const v w => .const v w
    | .slice e hi lo => .slice (substExpr e) hi lo
    | .concat args => .concat (args.map substExpr)
    | .op op args => .op op (args.map substExpr)
    | .index arr idx => .index (substExpr arr) (substExpr idx)
  let substStmt : Stmt → Stmt
    | .assign lhs rhs => .assign lhs (substExpr rhs)
    | .register o c r input iv => .register o c r (substExpr input) iv
    | .memory n aw dw clk wa wd we ra rd cr =>
      .memory n aw dw clk (substExpr wa) (substExpr wd) (substExpr we) (substExpr ra) rd cr
    | .inst mn ins conns => .inst mn ins (conns.map fun (p, e) => (p, substExpr e))
  let newBody := body.map substStmt
  let newDm := buildDefMap newBody
  (newBody, newDm)

/-- Optimize a module: eliminate concat/slice chains, then remove dead code -/
def optimizeModule (m : Module)
    (observableWires : Option (List String) := none) : Module :=
  if m.isPrimitive then m
  else
    let wm := buildWidthMap m
    let dm := buildDefMap m.body

    -- Collect wires directly referenced by register inputs (before any optimization).
    -- These must not be inlined away, because CppSim's evalTick generates
    -- them as local variables in the combinational section.
    let registerInputWires := m.body.foldl (fun (s : HashMap String Bool) stmt =>
      match stmt with
      | .register _ _ _ input _ =>
        (collectExprRefs input).foldl (fun acc r => acc.insert r true) s
      | _ => s
    ) {}

    -- Phase 0: Constant and alias propagation
    -- Only propagate constants and aliases to wires that are NOT register outputs.
    -- Register outputs change every cycle and must not be treated as constants.
    let registerOutputs := m.body.foldl (fun (s : HashMap String Bool) stmt =>
      match stmt with
      | .register output .. => s.insert output true
      | _ => s
    ) {}
    let (constPropBody, dm) := propagateConstants m.body dm
      |> fun (body, dm) =>
        -- Verify: don't propagate refs that resolve to register outputs
        -- The propagateConstants already only handles assigns, not registers,
        -- so register outputs themselves are never in constMap.
        -- However, aliases like `x = regOutput` can propagate `regOutput` as a ref.
        -- This is correct: x becomes a ref to regOutput (which is a register member).
        (body, dm)

    -- Phase 0.5: Remove duplicate and identity assigns.
    -- SSA lowering can produce identical assigns from case/if branches,
    -- and identity assigns (x = x) from output reg declarations.
    let dedupBody := Id.run do
      let mut seen : HashMap String (Expr × Nat) := {}  -- lhs → (rhs, position)
      let mut drops : HashMap Nat Bool := {}  -- positions to drop
      let mut pos : Nat := 0
      for s in constPropBody do
        match s with
        | .assign lhs rhs =>
          -- Drop identity assigns (x = ref x)
          let isIdentity := match rhs with | .ref name => name == lhs | _ => false
          if isIdentity then
            drops := drops.insert pos true
          else match seen.get? lhs with
          | some (prevRhs, _) =>
            if prevRhs == rhs then
              drops := drops.insert pos true  -- identical → drop this copy
            else
              seen := seen.insert lhs (rhs, pos)  -- different RHS → update
          | none => seen := seen.insert lhs (rhs, pos)
        | _ => pure ()
        pos := pos + 1
      let mut result : List Stmt := []
      pos := 0
      for s in constPropBody do
        if !drops.contains pos then result := result ++ [s]
        pos := pos + 1
      result

    -- Phase 1: Replace slice-of-concat with direct references
    let optimizedBody := dedupBody.map (optimizeStmt dm wm)

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

    let m2 := { m with body := prunedBody, wires := prunedWires }

    -- Phase 3: Single-use wire inlining
    let (inlinedBody, inlinedWires) := inlineSingleUseWires m2 m2.body observableWires registerInputWires

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
