/-
  Sparkle.Verification.Cost — static cost-budget verification.

  Given a synthesised IR (`Sparkle.IR.AST.Module` + sub-module
  `Design`), compute upper bounds on:
    - **area**:  Σ over all primitive nodes of `costModel(node)`
    - **depth**: longest path between any pair of registers
                 (or input → register), measured in cost units

  No target frequency: the cost model is user-supplied
  coefficients (`addCost`, `mulCost`, `muxCost`, etc.).  This
  is "is this circuit budget X under cost-model Y" rather than
  "does this hit N MHz on the Xilinx Zynq UltraScale+".

  Wired into the elaborator as a `#verify_cost` command:

      def fastAdder (a b : Signal _ (BitVec 16)) : Signal _ (BitVec 16) :=
        Signal.map₂ (· + ·) a b

      #verify_cost fastAdder { area := 32, depth := 16 }

  ⇒ logs `✅ verified: area ≤ 32, depth ≤ 16` or
    `❌ violated: area = 35 (> 32) or depth = 18 (> 16)`.

  See `Tests/Verification/CostDemo.lean` for usage patterns
  and `Tests/Verification/CostInternalTest.lean` for unit
  tests of the pure cost-analysis core.
-/
import Sparkle.IR.AST
import Sparkle.Compiler.Elab

namespace Sparkle.Verification.Cost

open Sparkle.IR.AST

/-! ### Cost model: per-operator coefficients. -/

/-- User-supplied cost coefficients.  Defaults model a
    reasonable ASIC technology library (a 32-bit multiplier
    is ~64× the area of a 32-bit adder, etc.).  Override
    individual fields to retarget for FPGA LUT counts,
    custom ASICs, or coarse-grained DSP-block accounting. -/
structure CostModel where
  /-- Cost of one `op .add` / `op .sub` node, per output bit. -/
  addCost  : Nat := 1
  /-- Cost of one `op .mul` node, per output bit² (multiplier
      area grows quadratically in bit-width). -/
  mulCost  : Nat := 1
  /-- Cost of one `op .mux` node, per output bit. -/
  muxCost  : Nat := 1
  /-- Cost of one `op .{and,or,xor,not}` node, per output bit. -/
  bitCost  : Nat := 1
  /-- Cost of one `op .eq` / `.lt_*` / `.le_*` / `.gt_*` / `.ge_*`
      comparator, per output bit of the input. -/
  cmpCost  : Nat := 1
  /-- Cost of `op .shl` / `.shr` / `.asr` (barrel shifter),
      per output bit × log2(width). -/
  shiftCost : Nat := 1
  /-- Cost of `op .neg`, per output bit. -/
  negCost  : Nat := 1
  /-- Cost of one register (D flip-flop), per stored bit.
      Default 0 so a "free" register doesn't pollute the area
      number.  Set non-zero to budget DFF area. -/
  regCost  : Nat := 0
  /-- Cost of one memory cell (SRAM bit), per bit. -/
  memCost  : Nat := 1
  /-- Cost of crossing one sub-module instance boundary
      (typically 0 — the sub-module's own cost is recursed
      into separately). -/
  instCost : Nat := 0
  deriving Repr

/-- Conservative default: ASIC-ish unit coefficients. -/
def CostModel.default : CostModel := {}

/-! ### Cost-analysis core: pure functions on IR. -/

/-- Compute the bit-width of an `Expr`, given a name→width
    lookup for wires.  Returns 0 when undetermined; the
    cost analysis treats 0-width nodes as cost 0 (consistent
    with `IR.Optimize.optimizeModule` stripping them). -/
partial def exprWidth (env : String → Option Nat) : Expr → Nat
  | .const _ w     => w
  | .ref name      => env name |>.getD 0
  | .op op args    =>
      match op, args with
      | .mux, _ :: t :: _ => exprWidth env t
      | .eq,  _           => 1
      | .lt_u, _ | .lt_s, _ | .le_u, _ | .le_s, _
      | .gt_u, _ | .gt_s, _ | .ge_u, _ | .ge_s, _ => 1
      | _, e :: _         => exprWidth env e
      | _, []             => 0
  | .concat args   => args.foldl (fun acc e => acc + exprWidth env e) 0
  | .slice _ hi lo => if hi ≥ lo then hi - lo + 1 else 0
  | .index arr _   => exprWidth env arr

/-- Approximate `log2(n)` rounded up (used for barrel-shifter cost). -/
def log2Up : Nat → Nat
  | 0     => 0
  | 1     => 0
  | n + 2 => 1 + log2Up ((n + 2) / 2 + ((n + 2) % 2))

/-- Cost (area contribution) of one `Expr` node IN ISOLATION
    — does NOT recurse into arguments.  Recursion is handled
    by `exprArea` so each sub-expression's area is summed
    bottom-up. -/
def opCost (m : CostModel) (env : String → Option Nat) : Expr → Nat
  | .const _ _     => 0
  | .ref _         => 0
  | .op operator args =>
      let w (e : Expr) : Nat := exprWidth env e
      let argW : Nat := match args with
        | e :: _ => w e
        | _      => 0
      match operator with
      | .add | .sub               => m.addCost * argW
      | .mul                      => m.mulCost * argW * argW
      | .mux                      =>
          match args with
          | _ :: t :: _ => m.muxCost * w t
          | _ => 0
      | .and | .or | .xor | .not  => m.bitCost * argW
      | .eq | .lt_u | .lt_s
      | .le_u | .le_s | .gt_u
      | .gt_s | .ge_u | .ge_s     => m.cmpCost * argW
      | .shl | .shr | .asr        => m.shiftCost * argW * log2Up argW
      | .neg                      => m.negCost * argW
  | .concat _      => 0
  | .slice _ _ _   => 0
  | .index _ _     => 0

/-- Recursively sum area over an expression tree (each shared
    sub-expression counted ONCE per syntactic occurrence; the
    IR doesn't share by reference so this is an upper bound). -/
partial def exprArea (m : CostModel) (env : String → Option Nat) : Expr → Nat
  | e@(.op _ args)    => opCost m env e + args.foldl (fun acc a => acc + exprArea m env a) 0
  | .concat args      => args.foldl (fun acc a => acc + exprArea m env a) 0
  | .slice e _ _      => exprArea m env e
  | .index arr idx    => exprArea m env arr + exprArea m env idx
  | .const _ _        => 0
  | .ref _            => 0

/-- Recursively compute combinational depth of an expression
    tree.  Constants and wire refs are depth 0 *unless* the
    ref name appears in `assignMap` — then we descend through
    the assignment to chase the true combinational path.
    Register outputs are deliberately NOT in `assignMap`, so
    depth resets at register boundaries (= register-to-register
    path measurement).

    `cache` memoizes per-name depth lookups — crucial because
    Sparkle's IR often shares `_tmp_*` wires across many fan-out
    sites, which would otherwise re-walk the same sub-tree
    exponentially.  State-monad form to thread the cache. -/
partial def exprDepth (m : CostModel) (env : String → Option Nat)
    (assignMap : String → Option Expr) :
    Expr → StateM (Std.HashMap String Nat) Nat
  | .op op args => do
      let mut best := 0
      for a in args do
        let d ← exprDepth m env assignMap a
        if d > best then best := d
      -- Depth cost is per-operator (NOT per-bit) — bit-level
      -- area is a separate concern.  Physical critical-path
      -- intuition:
      --   add N: carry chain ≈ log2(N) for prefix adders, but
      --   FPGAs use dedicated fast carry chains, so model as 1.
      --   mul N: Wallace/Booth tree ≈ log2(N).
      --   mux: 1 (every operator counts as one LUT level).
      --   shift N: barrel shifter has log2(N) mux stages.
      let argW : Nat := match args with
        | e :: _ => exprWidth env e
        | _      => 0
      let here : Nat := match op with
        | .add | .sub               => m.addCost            -- carry chain ≈ 1 LUT level
        | .mul                      => m.mulCost * log2Up argW  -- Wallace tree
        | .mux                      => m.muxCost            -- one LUT level
        | .and | .or | .xor | .not  => m.bitCost            -- one LUT level
        | .eq | .lt_u | .lt_s
        | .le_u | .le_s | .gt_u
        | .gt_s | .ge_u | .ge_s     => m.cmpCost            -- one LUT + tree reduction
        | .shl | .shr | .asr        => m.shiftCost * log2Up argW  -- barrel-shifter stages
        | .neg                      => m.negCost            -- carry chain
      return here + best
  | .concat args => do
      let mut best := 0
      for a in args do
        let d ← exprDepth m env assignMap a
        if d > best then best := d
      return best
  | .slice e _ _   => exprDepth m env assignMap e
  | .index arr idx => do
      let a ← exprDepth m env assignMap arr
      let b ← exprDepth m env assignMap idx
      return Nat.max a b
  | .const _ _ => return 0
  | .ref name => do
      let cache ← get
      match cache[name]? with
      | some d => return d
      | none =>
        match assignMap name with
        | none => return 0
        | some rhs =>
          -- Tentatively mark as 0 to break any cycle (defensive).
          modify (·.insert name 0)
          let d ← exprDepth m env assignMap rhs
          modify (·.insert name d)
          return d

/-- Top-level entry: discard the cache. -/
def exprDepthOf (m : CostModel) (env : String → Option Nat)
    (assignMap : String → Option Expr) (e : Expr) : Nat :=
  (exprDepth m env assignMap e).run' {}

/-! ### Module-level analysis. -/

/-- Build a `String → Option Nat` width-lookup function from
    a module's ports + internal wires. -/
def buildEnv (mod : Module) : String → Option Nat :=
  let table : List (String × Nat) :=
    (mod.inputs.map (fun p => (p.name, p.ty.bitWidth)))
    ++ (mod.outputs.map (fun p => (p.name, p.ty.bitWidth)))
    ++ (mod.wires.map (fun p => (p.name, p.ty.bitWidth)))
  fun name => (table.find? (fun (n, _) => n == name)).map (·.2)

/-- Area contribution of one statement. -/
def stmtArea (m : CostModel) (env : String → Option Nat) : Stmt → Nat
  | .assign _ rhs => exprArea m env rhs
  | .register _ _ _ input _ =>
      m.regCost * exprWidth env input + exprArea m env input
  | .memory _ aw dw _ wa wd we ra _ _ =>
      m.memCost * (2 ^ aw) * dw
        + exprArea m env wa + exprArea m env wd
        + exprArea m env we + exprArea m env ra
  | .inst _ _ conns =>
      m.instCost + conns.foldl (fun acc (_, e) => acc + exprArea m env e) 0

/-- Depth contribution of one statement, threading a shared
    cache so cross-stmt `_tmp_*` lookups are O(1) after the
    first walk.  For registers, the depth is the input chain
    (register output resets the path elsewhere). -/
def stmtDepthM (m : CostModel) (env : String → Option Nat)
    (assignMap : String → Option Expr) :
    Stmt → StateM (Std.HashMap String Nat) Nat
  | .assign _ rhs => exprDepth m env assignMap rhs
  | .register _ _ _ input _ => exprDepth m env assignMap input
  | .memory _ _ _ _ wa wd we ra _ _ => do
      let a ← exprDepth m env assignMap wa
      let b ← exprDepth m env assignMap wd
      let c ← exprDepth m env assignMap we
      let d ← exprDepth m env assignMap ra
      return Nat.max (Nat.max a b) (Nat.max c d)
  | .inst _ _ conns => do
      let mut best := 0
      for (_, e) in conns do
        let d ← exprDepth m env assignMap e
        if d > best then best := d
      return best

/-- Build an assign-name → RHS map from a module body, so
    `exprDepth` can follow `_tmp_*` wires across the IR.
    Register outputs are intentionally excluded (those reset
    the combinational path). -/
def buildAssignMap (mod : Module) : String → Option Expr :=
  let pairs : List (String × Expr) :=
    mod.body.foldl (fun acc s => match s with
      | .assign lhs rhs => (lhs, rhs) :: acc
      | _ => acc) []
  fun name => (pairs.find? (fun (n, _) => n == name)).map (·.2)

/-- Total area of a module (sum over all statements + own
    primitive cost).  Sub-module instances contribute
    `m.instCost` each; their internal cost should be summed
    separately via `designArea`. -/
def moduleArea (m : CostModel) (mod : Module) : Nat :=
  if mod.isPrimitive then 0
  else
    let env := buildEnv mod
    mod.body.foldl (fun acc s => acc + stmtArea m env s) 0

/-- Worst-case combinational depth of a module — the longest
    register-to-register path (or input port → register input,
    or output port path), measured in `CostModel` units.
    Shares a single cache across all statements so each `_tmp_*`
    wire is walked at most once per module. -/
def moduleDepth (m : CostModel) (mod : Module) : Nat :=
  if mod.isPrimitive then 0
  else
    let env := buildEnv mod
    let assignMap := buildAssignMap mod
    let run : StateM (Std.HashMap String Nat) Nat := do
      let mut best := 0
      for s in mod.body do
        let d ← stmtDepthM m env assignMap s
        if d > best then best := d
      return best
    run.run' {}

/-- Sum the area of every module in a design (top + all
    sub-modules).  Doesn't dedupe by instance count — each
    unique module is counted once at its full area. -/
def designArea (m : CostModel) (d : Design) : Nat :=
  d.modules.foldl (fun acc mod => acc + moduleArea m mod) 0

/-- Worst-case depth across the design: for each module
    consider its own depth + the deepest sub-module it
    instantiates.  This is a coarse approximation
    (no path-through-sub-module modelling). -/
def designDepth (m : CostModel) (d : Design) : Nat :=
  d.modules.foldl (fun acc mod => Nat.max acc (moduleDepth m mod)) 0

/-! ### FPGA-resource estimation (LUT, FF, BRAM, DSP).

    Coarser than the generic `area` model: each operator
    contributes to specific resource pools that map onto
    real FPGA fabric.  Numbers are Gowin-like (the Tang
    Nano 9K / 50K parts) but reasonable for any LUT4-based
    FPGA.  See `Sparkle.Verification.CostTargets` for
    per-part ceiling tables. -/

/-- Per-expression LUT cost (no recursion — caller sums). -/
def lutOf (env : String → Option Nat) : Expr → Nat
  | .op op args =>
      let w (e : Expr) : Nat := exprWidth env e
      let argW := match args with | e :: _ => w e | _ => 0
      match op with
      | .add | .sub               => argW
      | .mul                      => argW * argW / 2
      | .mux                      => argW
      | .and | .or | .xor         => (argW + 3) / 4
      | .not                      => (argW + 7) / 8
      | .eq | .lt_u | .lt_s
      | .le_u | .le_s | .gt_u
      | .gt_s | .ge_u | .ge_s     => (argW + 3) / 4 + 1
      | .shl | .shr | .asr        =>
          -- A shift/rotate by a CONSTANT is free rewiring (0 LUT); only a
          -- variable (data-dependent) shift synthesises to a barrel
          -- shifter.  SHA-256 / Keccak rotations are all constant.
          match args with
          | [_, .const _ _] => 0
          | _               => argW * (log2Up argW + 1)
      | .neg                      => argW
  | _ => 0

partial def exprLUT (env : String → Option Nat) : Expr → Nat
  | e@(.op _ args)    => lutOf env e + args.foldl (fun acc a => acc + exprLUT env a) 0
  | .concat args      => args.foldl (fun acc a => acc + exprLUT env a) 0
  | .slice e _ _      => exprLUT env e
  | .index arr idx    => exprLUT env arr + exprLUT env idx
  | .const _ _        => 0
  | .ref _            => 0

/-- Per-statement LUT contribution. -/
def stmtLUT (env : String → Option Nat) : Stmt → Nat
  | .assign _ rhs     => exprLUT env rhs
  | .register _ _ _ input _ => exprLUT env input
  | .memory _ _ _ _ wa wd we ra _ _ =>
      exprLUT env wa + exprLUT env wd + exprLUT env we + exprLUT env ra
  | .inst _ _ conns   => conns.foldl (fun acc (_, e) => acc + exprLUT env e) 0

/-- Per-statement FF contribution: only `register`. -/
def stmtFF (env : String → Option Nat) : Stmt → Nat
  | .register output _ _ _ _ => env output |>.getD 0
  | _ => 0

/-- Per-statement BRAM contribution (in 9Kb units, ceiling). -/
def stmtBSRAM9k : Stmt → Nat
  | .memory _ aw dw _ _ _ _ _ _ _ =>
      let bits := (2 ^ aw) * dw
      (bits + 9215) / 9216
  | _ => 0

/-- Per-expression DSP18×18 contribution. -/
partial def exprDSP (env : String → Option Nat) : Expr → Nat
  | .op .mul args =>
      let w := match args with | e :: _ => exprWidth env e | _ => 0
      let here := if w ≤ 18 then 1 else 0
      here + args.foldl (fun acc a => acc + exprDSP env a) 0
  | .op _ args     => args.foldl (fun acc a => acc + exprDSP env a) 0
  | .concat args   => args.foldl (fun acc a => acc + exprDSP env a) 0
  | .slice e _ _   => exprDSP env e
  | .index arr idx => exprDSP env arr + exprDSP env idx
  | _ => 0

def stmtDSP (env : String → Option Nat) : Stmt → Nat
  | .assign _ rhs     => exprDSP env rhs
  | .register _ _ _ input _ => exprDSP env input
  | .memory _ _ _ _ wa wd we ra _ _ =>
      exprDSP env wa + exprDSP env wd + exprDSP env we + exprDSP env ra
  | .inst _ _ conns   => conns.foldl (fun acc (_, e) => acc + exprDSP env e) 0

/-- Aggregate FPGA-resource estimate. -/
structure Resources where
  lut      : Nat := 0
  ff       : Nat := 0
  bsram9k  : Nat := 0
  dsp18x18 : Nat := 0
  deriving Repr

def Resources.add (a b : Resources) : Resources :=
  { lut      := a.lut + b.lut
  , ff       := a.ff + b.ff
  , bsram9k  := a.bsram9k + b.bsram9k
  , dsp18x18 := a.dsp18x18 + b.dsp18x18 }

instance : Add Resources where add := Resources.add

def moduleResources (mod : Module) : Resources :=
  if mod.isPrimitive then {} else
  let env := buildEnv mod
  mod.body.foldl (fun acc s =>
    { lut      := acc.lut      + stmtLUT env s
    , ff       := acc.ff       + stmtFF env s
    , bsram9k  := acc.bsram9k  + stmtBSRAM9k s
    , dsp18x18 := acc.dsp18x18 + stmtDSP env s }) {}

def designResources (d : Design) : Resources :=
  d.modules.foldl (fun acc m => acc + moduleResources m) {}

/-! ### Budget verification result. -/

/-- Cost budget.  `area` is the total node-cost upper bound;
    `depth` is the combinational-path upper bound.

    A field set to `0` means **unconstrained** for that
    dimension (size-only or depth-only checks just omit the
    other field).  Set `area := 1` (etc.) if you actually want
    to assert area ≤ 0.  Trade-off framing: a depth check
    talks about *speed* under your cost model, an area check
    talks about *resources*; you can budget either, both, or
    just one. -/
structure Budget where
  area  : Nat := 0
  depth : Nat := 0
  deriving Repr

structure Report where
  area  : Nat
  depth : Nat
  budget : Budget
  deriving Repr

/-- A budget dimension of 0 is treated as "unconstrained". -/
def Report.areaOk  (r : Report) : Bool :=
  r.budget.area = 0 ∨ r.area ≤ r.budget.area
def Report.depthOk (r : Report) : Bool :=
  r.budget.depth = 0 ∨ r.depth ≤ r.budget.depth
def Report.ok      (r : Report) : Bool := r.areaOk ∧ r.depthOk

/-- Compute the cost report for a synthesized module + design.
    `synthesizeCombinational` returns the top module separately;
    `Design.modules` holds only sub-modules reached via `.inst`.
    So total area = top module + every sub-module. -/
def analyze (cm : CostModel) (mod : Module) (d : Design) (b : Budget) : Report :=
  { area  := moduleArea cm mod + designArea cm d
  , depth := Nat.max (moduleDepth cm mod) (designDepth cm d)
  , budget := b }

end Sparkle.Verification.Cost
