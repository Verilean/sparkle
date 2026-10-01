/-
  CUDA within-instance (intra) scheduling — one GPU thread per top-level
  instance.  Design: docs/CudaIntraSim-design.md.

  `toCudaSimDesign` (batch) runs N independent copies of a design, one thread
  each.  This backend makes ONE instance faster: each top-level `.inst` (a PE,
  a core) becomes a thread, and each simulated clock cycle runs as two
  barrier-separated phases:

    Phase 1  per instance, on its own struct only:
               eval_tick  — clock edge, using the inputs pulled in the
                            previous phase 2;
               publish    — top outputs this instance drives (the pre-edge
                            values, as CSim's eval_tick leaves them);
               eval       — output fields of the NEW state.
    Phase 2  per instance: pull its inputs from the producers' output fields.

  A launch starts with a prologue — eval, then every connection and constant
  once — so the first phase 1 sees correct inputs; top inputs cannot change
  during a launch.

  No data race: in phase 1 a thread touches only its own instance struct and
  the top outputs it owns; in phase 2 nobody writes an output field, and each
  input field has exactly one writer.

  Soundness rests on CSim's eval being register-pure (registers latch in tick
  only; memory writes live in tickBody; sync-read address latches are
  last-write-wins), so the stale-input results of phase 1's second eval are
  dead values, recomputed by the next eval_tick before anything latches.  For
  Moore-bounded designs — every cross-instance connection taps an output with
  no combinational input dependence, so it is a function of the state alone —
  the schedule is cycle-exact against CSim's sequential reference; the
  argument is in the design memo §3.

  In the block kernel the state (and the per-instance link tables) are staged
  in shared memory when they fit, and per-thread table lookups are hoisted
  out of the cycle loop: on the 16×16 MAC mesh that is 7.7× the first
  version (three barriers, global memory, per-cycle table reads).

  Scaling is table-driven, not switch-driven: instance offsets, module-kind
  dispatch, and `offsetof`-pair copy descriptors, so a 16K-instance top emits
  kilobytes of tables instead of a 16K-case kernel.

  v1 restrictions (all detected; each error names the offender):
    - Moore-bounded cross-instance connections only (v2: K-round relaxation,
      memo §7);
    - an instance input is a `.ref` (chased through const/ref top assigns),
      a `.const`, or a slice of a TOP INPUT (a bus split across instances);
    - a top output is one of those, or a concatenation of byte-aligned
      ones (a result bus assembled from several instances);
    - the top module contains only `.assign` + `.inst` (no registers,
      memories, or other combinational logic at top);
    - no combinational loops.
-/
import Sparkle.Backend.CudaSim
import Sparkle.IR.Specialize

namespace Sparkle.Backend.CudaIntra

open Sparkle.IR.AST
open Sparkle.IR.Type
open Sparkle.Backend.CSim
open Sparkle.Backend.CudaSim

/-! ### Combinational-dependency analysis (per module) -/

private structure NetMaps where
  inputNames : List String
  assigns    : List (String × Expr)
  regOuts    : List String
  memReads   : List (String × Bool × Expr)  -- (readData, comboRead, readAddr)

private def netMapsOf (m : Module) : NetMaps :=
  { inputNames := m.inputs.map (·.name)
  , assigns := m.body.filterMap fun s => match s with
      | .assign lhs rhs => some (lhs, rhs)
      | _ => none
  , regOuts := m.body.filterMap fun s => match s with
      | .register out .. => some out
      | _ => none
  , memReads := m.body.filterMap fun s => match s with
      | .memory _ _ _ _ _ _ _ ra rd cr .. => some (rd, cr, ra)
      | _ => none }

/-- Walk backwards from `name` through assign chains, collecting the input
    ports it combinationally depends on.  Stops at registers and sync-read
    memories; comboRead memories propagate through their read address. -/
private def combWalk (nm : NetMaps) : Nat → List String → String →
    Except String (List String)
  | 0, path, name =>
    throw s!"combinational chain too deep at '{name}' (suspected loop; path: {String.intercalate " -> " path.reverse})"
  | fuel + 1, path, name => do
    if path.contains name then
      throw s!"combinational loop through '{name}'"
    else if nm.inputNames.contains name then
      return [name]
    else if nm.regOuts.contains name then
      return []
    else
      match nm.memReads.find? (fun e => e.1 == name) with
      | some (_, cr, ra) =>
        if cr then
          (collectExprRefs ra).foldlM (fun acc r => do
            return acc ++ (← combWalk nm fuel (name :: path) r)) []
        else
          return []
      | none =>
        match nm.assigns.find? (fun e => e.1 == name) with
        | some (_, rhs) =>
          (collectExprRefs rhs).foldlM (fun acc r => do
            return acc ++ (← combWalk nm fuel (name :: path) r)) []
        | none => return []   -- undriven: constant-like, no comb dependence

/-- Input ports that output `port` of `m` combinationally depends on.
    `[]` means a Moore output (function of registers/constants only). -/
def combDeps (m : Module) (port : String) : Except String (List String) := do
  let deps ← combWalk (netMapsOf m) (4 * m.body.length + 16) [] port
  return deps.eraseDups

/-! ### Top-level structure -/

/-- One top-level `.inst`, with its resolved module and the fused-struct
    field name CSim gives it (must match `CSim.emitStmt`'s `.inst` naming). -/
structure InstInfo where
  modName  : String
  instName : String
  /-- Sanitised field name inside the top struct. -/
  field    : String
  mod      : Module
  conns    : List (String × Expr)

private def instFieldName (modName instName : String) : String :=
  let c := sanitizeName modName
  let r := sanitizeName instName
  if r == c then r ++ "_inst" else r

/-- Collect the top's instances; reject anything else the v1 top may not
    contain (registers, memories). -/
private def topInsts (d : Design) (top : Module) : Except String (List InstInfo) :=
  top.body.foldlM (fun acc s => do
    match s with
    | .inst modName instName conns =>
      match d.findModule modName with
      | some m =>
        return acc ++ [{ modName, instName, conns, mod := m
                       , field := instFieldName modName instName }]
      | none => throw s!"instance '{instName}': module '{modName}' not found in design"
    | .register out .. =>
      throw s!"top-level register '{out}' — v1 requires the top to contain only assigns and instances; move it into a submodule"
    | .memory nm .. =>
      throw s!"top-level memory '{nm}' — v1 requires the top to contain only assigns and instances; move it into a submodule"
    | .assign _ _ => return acc) []

/-- Wire name → the (instance, output port) that drives it, from `.inst`
    output connections of the `.ref wire` shape (the only shape CSim's own
    lowering honours for outputs). -/
private def outputDrivers (insts : List InstInfo) : List (String × InstInfo × String) :=
  insts.flatMap fun ii =>
    let outs := ii.mod.outputs.map (·.name)
    ii.conns.filterMap fun (port, e) =>
      if outs.contains port then
        match e with
        | .ref w => some (w, ii, port)
        | _ => none
      else none

/-- Where a connection's value comes from, after chasing top-level
    const/ref assign chains. -/
inductive ConnSource where
  | instOutput (producer : InstInfo) (port : String)
  | topInput (port : String)
  /-- Bits `[hi:lo]` of a top input (a bus split across instances). -/
  | topSlice (port : String) (hi lo : Nat)
  | imm (value : Int) (width : Nat)

/-- `x[hi:lo]`, also in the elaborator's masked form `x[hi:lo] & ones`
    (what `extractLsb'` with a non-zero start lowers to). -/
private def sliceOfRef? : Expr → Option (String × Nat × Nat)
  | .slice (.ref n) hi lo => some (n, hi, lo)
  | .op .and [.slice (.ref n) hi lo, .const m _] =>
    let full : Int := Int.ofNat (2 ^ (hi - lo + 1) - 1)
    if hi ≥ lo && (m % (full + 1) == full) then some (n, hi, lo) else none
  | _ => none

private def resolveRef (top : Module) (drivers : List (String × InstInfo × String)) :
    Nat → String → Except String ConnSource
  | 0, n => throw s!"reference chain too deep at '{n}' — loop in top-level assigns?"
  | fuel + 1, n =>
    if top.inputs.any (·.name == n) then
      pure (.topInput n)
    else
      match drivers.find? (fun t => t.1 == n) with
      | some (_, ii, port) => pure (.instOutput ii port)
      | none =>
        let drv : Option Expr := top.body.findSome? (fun s => match s with
          | .assign lhs rhs => if lhs == n then some rhs else none
          | _ => none)
        match drv with
        | some (.ref n') => resolveRef top drivers fuel n'
        | some (.const v w) => pure (.imm v w)
        | some e =>
          match sliceOfRef? e with
          | some (n', hi, lo) =>
            if top.inputs.any (·.name == n') then pure (.topSlice n' hi lo)
            else throw s!"top-level slice of '{n'}' drives '{n}' — only slices of TOP INPUTS are supported at top; move other logic into a submodule"
          | none =>
            throw s!"top-level combinational logic drives '{n}' — v1 supports only const/ref assigns at top; move the logic into a submodule"
        | none => throw s!"'{n}' is undriven at the top level"

private def resolveConn (top : Module) (drivers : List (String × InstInfo × String))
    (fuel : Nat) (e : Expr) : Except String ConnSource :=
  match e with
  | .const v w => pure (.imm v w)
  | .ref n => resolveRef top drivers fuel n
  | e =>
    match sliceOfRef? e with
    | some (n, hi, lo) =>
      if top.inputs.any (·.name == n) then pure (.topSlice n hi lo)
      else throw s!"instance connection slices '{n}', which is not a top input — only slices of top inputs are supported (materialise it in a submodule)"
    | none => throw "instance connection must be a wire/port reference, a slice of a top input, or a constant — got a compound expression (materialise it in a submodule)"

/-! ### Copy / immediate tables -/

/-- Who performs a copy inside the cycle loop.  `static` entries (source is
    a top input) cannot change during a launch and are applied once. -/
inductive CopyRole where
  | static
  /-- An instance input fed by another instance's output: PULLED by the
      consuming instance (index into `insts`) after every clock edge. -/
  | pull (consumer : Nat)
  /-- A top output fed by an instance output: PUBLISHED by the producing
      instance. -/
  | pub (producer : Nat)

structure CopyEnt where
  dstC  : String
  srcC  : String
  bytes : Nat
  role  : CopyRole := .static
  /-- For a `pull`: the consumer's input port, … -/
  port  : String := ""
  /-- … the producing instance (index into `insts`) and its output port. -/
  prod  : Nat := 0
  prodPort : String := ""

structure ImmEnt where
  dstC  : String
  bytes : Nat
  value : String

/-- C storage size of a port, matching CSim's field emission
    (uint8/16/32/64 by width; wide → uint32_t words). -/
private def byteSize : HWType → Except String Nat
  | .bit => pure 1
  | .bitVector w =>
    pure <| if w ≤ 8 then 1 else if w ≤ 16 then 2 else if w ≤ 32 then 4
    else if w ≤ 64 then 8 else 4 * ((w + 31) / 32)
  | .bitVectorDim width =>
    throw s!"CudaIntra requires a concrete bit width, found {width}; specialize retained parameters before CUDA lowering"
  | .array n t => return n * (← byteSize t)

private def portTy (ports : List Port) (name : String) : Option HWType :=
  (ports.find? (·.name == name)).map (·.ty)

private def maskedULL (v : Int) (width : Nat) : String :=
  let w := min width 64
  let m : Int := Int.ofNat (2 ^ w)
  let x := ((v % m) + m) % m
  s!"{x.toNat}ULL"

/-- Build the copy and immediate tables: instance input connections
    (clk/rst copied uniformly, exactly like CSim's `.inst` lowering) plus the
    top output ports for host observation.  Applies the Moore check to every
    cross-instance source. -/
private def buildTables (top : Module) (insts : List InstInfo) :
    Except String (List CopyEnt × List ImmEnt × List String) := do
  let topC := sanitizeName top.name
  let drivers := outputDrivers insts
  let fuel := 2 * top.body.length + 8
  let mut copies : List CopyEnt := []
  let mut imms : List ImmEnt := []
  -- C statements run once per launch: instance inputs fed by a SLICE of a
  -- top input (not a whole-field copy, so not a table entry).
  let mut statics : List String := []

  let mooreCheck (consumerDesc : String) (prod : InstInfo) (pport : String) :
      Except String Unit := do
    let deps ← combDeps prod.mod pport
    if !deps.isEmpty then
      throw s!"Mealy boundary: {consumerDesc} ← '{prod.instName}.{pport}', but output '{pport}' of module '{prod.modName}' combinationally depends on input(s) {deps} — register the output (v1 requires Moore-bounded cross-instance connections)"

  for ii in insts do
    let modC := sanitizeName ii.modName
    let outNames := ii.mod.outputs.map (·.name)
    for (port, e) in ii.conns do
      if outNames.contains port then
        continue   -- output connections become `drivers` entries
      let some ty := portTy ii.mod.inputs port
        | throw s!"instance '{ii.instName}': '{port}' is not an input of module '{ii.modName}'"
      let nbytes ← byteSize ty
      let dstC := s!"offsetof(struct {topC}, {ii.field}) + offsetof(struct {modC}, {sanitizeName port})"
      match ← resolveConn top drivers fuel e with
      | .instOutput prod pport =>
        mooreCheck s!"'{ii.instName}.{port}'" prod pport
        let some pty := portTy prod.mod.outputs pport
          | throw s!"internal: output '{pport}' not found on '{prod.modName}'"
        let pbytes ← byteSize pty
        if pbytes != nbytes then
          throw s!"width mismatch: '{ii.instName}.{port}' ({nbytes} bytes) ← '{prod.instName}.{pport}' ({pbytes} bytes)"
        copies := copies ++ [⟨dstC,
          s!"offsetof(struct {topC}, {prod.field}) + offsetof(struct {sanitizeName prod.modName}, {sanitizeName pport})",
          nbytes, .pull ((insts.findIdx? (·.instName == ii.instName)).getD 0), port,
          (insts.findIdx? (·.instName == prod.instName)).getD 0, pport⟩]
      | .topInput tport =>
        let some tty := portTy top.inputs tport
          | throw s!"internal: top input '{tport}' not found"
        let tbytes ← byteSize tty
        if tbytes != nbytes then
          throw s!"width mismatch: '{ii.instName}.{port}' ({nbytes} bytes) ← top input '{tport}' ({tbytes} bytes)"
        copies := copies ++ [⟨dstC, s!"offsetof(struct {topC}, {sanitizeName tport})", nbytes, .static, "", 0, ""⟩]
      | .topSlice tport hi lo =>
        let some tty := portTy top.inputs tport
          | throw s!"internal: top input '{tport}' not found"
        let some srcW := tty.bitWidth?
          | throw s!"CudaIntra requires a concrete bit width for top input '{tport}'"
        let w := hi - lo + 1
        if hi < lo || hi ≥ srcW then
          throw s!"slice [{hi}:{lo}] of top input '{tport}' ({srcW} bits) is out of range"
        if nbytes > 8 || w > 64 then
          throw s!"'{ii.instName}.{port}' ← {tport}[{hi}:{lo}]: slices wider than 64 bits are unsupported"
        let src := sanitizeName tport
        -- the source is a scalar (≤ 64 bits) or an array of 32-bit words
        let value :=
          if srcW ≤ 64 then s!"((uint64_t)self->{src} >> {lo})"
          else
            let k0 := lo / 32
            let off := lo % 32
            let parts := (List.range (hi / 32 - k0 + 1)).map fun d =>
              if d == 0 then s!"((uint64_t)self->{src}[{k0}] >> {off})"
              else s!"((uint64_t)self->{src}[{k0 + d}] << {32 * d - off})"
            "(" ++ String.intercalate " | " parts ++ ")"
        let masked := if w ≥ 64 then value else s!"({value} & {2 ^ w - 1}ULL)"
        statics := statics ++ [s!"  self->{ii.field}.{sanitizeName port} = {masked};"]
      | .imm v w =>
        if nbytes > 8 then
          throw s!"constant into wide (> 64-bit) input '{ii.instName}.{port}' is unsupported in v1"
        imms := imms ++ [⟨dstC, nbytes, maskedULL v w⟩]

  -- Top output ports: refresh for host observation.  An undriven output is
  -- skipped (it stays at its reset value), but resolvable sources get the
  -- same Moore check — a Mealy output is not a function of the state alone,
  -- so the value published after the clock edge would be stale.
  -- Width of a resolved source, for placing it inside a concatenation.
  let sourceWidth (src : ConnSource) : Except String Nat := match src with
    | .instOutput prod pport =>
      match (portTy prod.mod.outputs pport).bind (·.bitWidth?) with
      | some w => pure w
      | none => throw s!"internal: width of '{prod.instName}.{pport}' unknown"
    | .topInput tport =>
      match (portTy top.inputs tport).bind (·.bitWidth?) with
      | some w => pure w
      | none => throw s!"internal: width of top input '{tport}' unknown"
    | .topSlice _ hi lo => pure (hi - lo + 1)
    | .imm _ w => pure w
  -- One source placed at byte offset `byteOff` of top output `p`.
  let place (p : Port) (byteOff nbytes : Nat) (src : ConnSource) :
      Except String (List CopyEnt × List ImmEnt) := do
    let dstC := s!"offsetof(struct {topC}, {sanitizeName p.name})" ++
      (if byteOff == 0 then "" else s!" + {byteOff}")
    match src with
    | .instOutput prod pport =>
      mooreCheck s!"top output '{p.name}'" prod pport
      pure ([⟨dstC,
        s!"offsetof(struct {topC}, {prod.field}) + offsetof(struct {sanitizeName prod.modName}, {sanitizeName pport})",
        nbytes, .pub ((insts.findIdx? (·.instName == prod.instName)).getD 0), "", 0, ""⟩], [])
    | .topInput tport =>
      pure ([⟨dstC, s!"offsetof(struct {topC}, {sanitizeName tport})", nbytes, .static, "", 0, ""⟩], [])
    | .topSlice tport _ _ =>
      throw s!"top output '{p.name}' is a slice of top input '{tport}' — unsupported; pass it through a submodule"
    | .imm v w =>
      if nbytes ≤ 8 then pure ([], [⟨dstC, nbytes, maskedULL v w⟩])
      else throw s!"constant wider than 64 bits in top output '{p.name}' is unsupported"
  -- Driver of a top-level name after chasing ref-only assigns.
  let rec driverOf (fuel : Nat) (n : String) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let drv : Option Expr := top.body.findSome? (fun st => match st with
          | .assign lhs rhs => if lhs == n then some rhs else none
          | _ => none)
      match drv with
      | some (Expr.ref n') =>
        if top.inputs.any (·.name == n') || drivers.any (·.1 == n') then some (Expr.ref n')
        else driverOf fuel n'
      | other => other

  -- Leaves of a (possibly nested) concatenation, MSB first: `a ++ b ++ c`
  -- elaborates to concat wires feeding concat wires.  Inside a
  -- `Signal.loop` body the inner concatenations arrive inlined and
  -- wrapped in an all-ones mask of their own width (`{a, b} & 16'hffff`);
  -- such a mask changes nothing and is looked through.  (The total width
  -- of the leaves is checked against the port below.)
  let rec leaves (fuel : Nat) (e : Expr) : List Expr :=
    match fuel with
    | 0 => [e]
    | fuel + 1 =>
      match e with
      | .concat es => es.flatMap (leaves fuel)
      | .op .and [.concat es, .const m w] =>
        if m == Int.ofNat (2 ^ w - 1) then es.flatMap (leaves fuel) else [e]
      | .ref n =>
        match driverOf fuel n with
        | some (.concat es) => es.flatMap (leaves fuel)
        | _ => [e]
      | _ => [e]

  -- Top output ports, for host observation.  A whole-port source is one
  -- copy; a concatenation of byte-aligned sources is one copy per element
  -- (a result bus assembled from many instances).  An undriven output is
  -- skipped (it keeps its reset value).  Every instance source gets the
  -- Moore check — a Mealy output is not a function of the state alone, so
  -- the value published after the clock edge would be stale.
  for p in top.outputs do
    match driverOf fuel p.name with
    | none =>
      -- the output IS an instance's output wire (or is undriven)
      match resolveRef top drivers fuel p.name with
      | .ok src =>
        let (cs, is) ← place p 0 (← byteSize p.ty) src
        copies := copies ++ cs
        imms := imms ++ is
      | .error _ => pure ()
    | some (.concat elems) =>
      -- elements are MSB-first; walk from the LSB end
      let mut bit := 0
      for e in (elems.flatMap (leaves fuel)).reverse do
        let src ← resolveConn top drivers fuel e
        let w ← sourceWidth src
        if bit % 8 != 0 || w % 8 != 0 then
          throw s!"top output '{p.name}': concatenation element at bit {bit} (width {w}) is not byte-aligned — unsupported at top; pack it in a submodule"
        let (cs, is) ← place p (bit / 8) (w / 8) src
        copies := copies ++ cs
        imms := imms ++ is
        bit := bit + w
      if let some pw := p.ty.bitWidth? then
        if bit != pw then
          throw s!"top output '{p.name}' is {pw} bits but its concatenation supplies {bit} — unsupported at top; pack it in a submodule"
    | some e =>
      let nbytes ← byteSize p.ty
      let (cs, is) ← place p 0 nbytes (← resolveConn top drivers fuel e)
      copies := copies ++ cs
      imms := imms ++ is

  return (copies, imms, statics)

/-! ### Emission -/

/-- Tables, kind dispatch, the templated two-barrier cycle body, and the two
    kernels (block barrier with the exchange area in shared memory /
    cooperative grid barrier).  Schedule and its correctness argument:
    docs/CudaIntraSim-design.md §3. -/
private def emitIntraSection (top : Module) (insts : List InstInfo)
    (copies : List CopyEnt) (imms : List ImmEnt) (statics : List String) :
    Except String String := do
  let topC := sanitizeName top.name
  let m := insts.length
  let kinds : List String := insts.foldl (fun acc ii =>
    if acc.contains ii.modName then acc else acc ++ [ii.modName]) []
  if kinds.length > 255 then
    throw s!"{kinds.length} distinct instance module types (max 255 for the kind table)"
  let kindOf (ii : InstInfo) : Nat := (kinds.findIdx? (· == ii.modName)).getD 0

  let offEntries := insts.map fun ii =>
    s!"  offsetof(struct {topC}, {ii.field}),"
  let kindEntries := insts.map fun ii => s!"  {kindOf ii},"
  let dispatchCases (fn : String) (indent : String := "  ") : List String :=
    (List.range kinds.length).map fun k =>
      let mc := sanitizeName kinds[k]!
      s!"{indent}case {k}: sparkle_{mc}_{fn}((struct {mc}*)b); break;"
  let copyEntries :=
    if copies.isEmpty then ["  { 0, 0, 0u },"]
    else copies.map fun c => s!"  \{ {c.dstC}, {c.srcC}, {c.bytes}u },"
  let immEntries :=
    if imms.isEmpty then ["  { 0, 0u, 0ULL },"]
    else imms.map fun i => s!"  \{ {i.dstC}, {i.bytes}u, {i.value} },"
  -- Per-instance link lists: entries grouped by the instance that performs
  -- them, with a start table of M+1 offsets.
  let linkEntry (c : CopyEnt) : String :=
    s!"  \{ (unsigned)({c.dstC}), (unsigned)({c.srcC}), {c.bytes}u },"
  let grouped (owner : CopyEnt → Option Nat) : List String × List Nat :=
    (List.range m).foldl (fun (ents, starts) i =>
      let mine := copies.filter fun c => owner c == some i
      (ents ++ mine.map linkEntry, starts ++ [ents.length + mine.length])) ([], [0])
  let (pubEnts, pubStarts) := grouped fun c => match c.role with
    | .pub i => some i | _ => none

  -- ── The exchange area ──────────────────────────────────────────────
  -- What instances pass to each other every cycle, packed: for each
  -- instance the output ports of its module, then one slot for every
  -- pulled port that a particular instance does NOT pull (see below).
  -- It is small — it is what goes into shared memory.
  let alignUp (x a : Nat) : Nat := (x + a - 1) / a * a
  let slotAlign (bytes : Nat) : Nat := if bytes == 8 then 8 else min bytes 4
  let layoutOuts (ports : List Port) : Except String (List (Port × Nat) × Nat) := do
    let mut off := 0
    let mut acc : List (Port × Nat) := []
    for p in ports do
      let b ← byteSize p.ty
      off := alignUp off (slotAlign b)
      acc := acc ++ [(p, off)]
      off := off + b
    return (acc, alignUp off 8)
  let kindOuts : List (List (Port × Nat) × Nat) ← kinds.mapM fun modName =>
    match insts.find? (·.modName == modName) with
    | some ii => layoutOuts ii.mod.outputs
    | none => pure ([], 0)
  let mut exOffArr : Array Nat := #[]
  let mut exTop := 0
  for ii in insts do
    exOffArr := exOffArr.push exTop
    exTop := exTop + (kindOuts.getD (kindOf ii) ([], 0)).2
  let instArr := insts.toArray
  let exOfOutput (prod : Nat) (port : String) : Except String Nat := do
    let some ii := instArr[prod]? | throw s!"internal: producer index {prod} out of range"
    let (outs, _) := kindOuts.getD (kindOf ii) ([], 0)
    match outs.find? (·.1.name == port) with
    | some (_, rel) => pure (exOffArr.getD prod 0 + rel)
    | none => throw s!"internal: output '{port}' not found on '{ii.modName}'"

  -- Pulls are TYPED: each thread keeps its instance in a local variable
  -- and loads the pulled inputs field by field.  For that every instance
  -- of a module needs the same list of ports — the input ports that are
  -- fed by an instance output in AT LEAST ONE instance of the module, in
  -- port order.  Where a particular instance gets such a port from a top
  -- input or a constant instead, it gets a slot of its own in the exchange
  -- area, which it fills once per launch: reloading it is a no-op.
  let pullSrc : Std.HashMap (Nat × String) (String × Nat × String) :=
    copies.foldl (fun h c => match c.role with
      | .pull i => h.insert (i, c.port) (c.srcC, c.prod, c.prodPort)
      | _ => h) {}
  let pulledOfMod : Std.HashSet (String × String) :=
    copies.foldl (fun h c => match c.role with
      | .pull i => match instArr[i]? with
        | some ii => h.insert (ii.modName, c.port)
        | none => h
      | _ => h) {}
  let pulledPorts (modName : String) : List Port :=
    match insts.find? (·.modName == modName) with
    | some ii => ii.mod.inputs.filter fun p => pulledOfMod.contains (modName, p.name)
    | none => []
  let kindPorts : List (List Port) := kinds.map pulledPorts
  let mut pullArr : Array String := #[]
  let mut pullStartArr : Array Nat := #[0]
  let mut i := 0
  for ii in insts do
    let own (port : String) : String :=
      s!"offsetof(struct {topC}, {ii.field}) + offsetof(struct {sanitizeName ii.modName}, {sanitizeName port})"
    for p in kindPorts.getD (kindOf ii) [] do
      let nbytes ← byteSize p.ty
      match pullSrc[(i, p.name)]? with
      | some (srcC, prod, pport) =>
        let x ← exOfOutput prod pport
        pullArr := pullArr.push
          s!"  \{ (unsigned)({own p.name}), (unsigned)({srcC}), {nbytes}u, {x}u },"
      | none =>
        exTop := alignUp exTop (slotAlign nbytes)
        pullArr := pullArr.push
          s!"  \{ (unsigned)({own p.name}), (unsigned)({own p.name}), {nbytes}u, {exTop}u },"
        exTop := exTop + nbytes
    pullStartArr := pullStartArr.push pullArr.size
    i := i + 1
  let pullEnts := pullArr.toList
  let pullStarts := pullStartArr.toList
  let exBytes := max 8 (alignUp exTop 8)

  -- The cycle loop of one module type.  A small instance lives in the
  -- local `L` (registers, once the compiler has taken the struct apart);
  -- a large one (memories, nested instances) stays where it is.  Either
  -- way it talks to the others through the exchange area only.
  let kindLoop (k : Nat) : List String :=
    let modName := kinds[k]!
    let mc := sanitizeName modName
    let outs := (kindOuts.getD k ([], 0)).1
    let ins := kindPorts.getD k []
    let nIns := ins.length
    let field (j : Nat) : String := sanitizeName (ins[j]!).name
    -- `acc`: how the instance is named ("L." / "P->"), `ptr`: its address
    let body (acc ptr : String) (isLocal : Bool) : List String :=
      (List.range nIns).map (fun j =>
        s!"        if (pl[{j}].src == pl[{j}].dst) memcpy(ex + pl[{j}].xsrc, &{acc}{field j}, sizeof({acc}{field j}));") ++
      [ "        for (long c = 0; c < cycles; ++c) {"
      , "          // Phase 1 (own instance only): clock edge with the inputs"
      , "          // pulled in the previous phase 2."
      , s!"          sparkle_{mc}_eval_tick({ptr});"
      , "          if (c == cycles - 1) {"
      , "            // Last cycle: publish the top outputs — the pre-edge values,"
      , "            // as the CPU reference leaves them." ]
      ++ (if isLocal then [s!"            *(struct {mc}*)b = L;"] else []) ++
      [ "            for (unsigned i = pb0; i < pb1; ++i)"
      , s!"              {topC}_intra_copy(base + pubs[i].dst, base + pubs[i].src, pubs[i].bytes);"
      , "          }"
      , "          // Outputs of the NEW state, into the exchange area." ]
      ++ (if isLocal then
            [ "          // Evaluated on a scratch copy of which only the outputs are kept:"
            , "          // the compiler drops everything in `eval` that does not feed an"
            , "          // output (for a module whose outputs are registers: all of it)."
            , s!"          \{ struct {mc} T = L; sparkle_{mc}_eval(&T);" ]
            ++ outs.map (fun (p, rel) =>
                let f := sanitizeName p.name
                s!"            memcpy(&L.{f}, &T.{f}, sizeof(L.{f})); memcpy(xo + {rel}, &T.{f}, sizeof(T.{f}));") ++
            [ "          }" ]
          else
            [ s!"          sparkle_{mc}_eval(P);" ]
            ++ outs.map (fun (p, rel) =>
                let f := sanitizeName p.name
                s!"          memcpy(xo + {rel}, &P->{f}, sizeof(P->{f}));")) ++
      [ "          g.sync();"
      , "          // Phase 2: pull own inputs from the exchange area.  Nobody writes"
      , "          // an output slot in this phase." ]
      ++ (List.range nIns).map (fun j =>
          s!"          memcpy(&{acc}{field j}, x{j}, sizeof({acc}{field j}));") ++
      [ "          g.sync();"
      , "        }" ]
    [ s!"    case {k}: \{" ]
    ++ (List.range nIns).map (fun j => s!"      const char* const x{j} = ex + pl[{j}].xsrc;") ++
    [ s!"      if constexpr (sizeof(struct {mc}) <= SPARKLE_INTRA_LOCAL_BYTES) \{"
    , s!"        struct {mc} L = *(struct {mc}*)b;" ]
    ++ body "L." "&L" true ++
    [ s!"        *(struct {mc}*)b = L;"
    , "      } else {"
    , "        // in place: the same schedule on the instance in the top struct"
    , s!"        struct {mc}* const P = (struct {mc}*)b;" ]
    ++ body "P->" "P" false ++
    [ "      }"
    , "    } break;" ]

  let orDummy (xs : List String) (dummy : String) : List String :=
    if xs.isEmpty then [dummy] else xs
  let startRow (xs : List Nat) : String :=
    "  " ++ String.intercalate ", " (xs.map toString)

  return String.intercalate "\n" <|
    [ "// ── Intra-instance scheduling: one thread per top-level instance ──"
    , "// Two-barrier pull schedule (docs/CudaIntraSim-design.md §3)."
    , "namespace cg = cooperative_groups;"
    , ""
    , s!"enum \{ {topC}_intra_M = {m}, {topC}_intra_nCopies = {copies.length}, {topC}_intra_nImms = {imms.length},"
    , s!"       {topC}_intra_nPulls = {pullEnts.length}, {topC}_intra_nPubs = {pubEnts.length},"
    , s!"       {topC}_intra_exBytes = {exBytes} };"
    , ""
    , s!"static __device__ const size_t {topC}_intra_off[{m}] = \{" ]
    ++ offEntries ++
    [ "};"
    , s!"static __device__ const unsigned char {topC}_intra_kind[{m}] = \{" ]
    ++ kindEntries ++
    [ "};"
    , ""
    , "typedef struct { size_t dst; size_t src; unsigned bytes; } SparkleIntraCopy;"
    , "typedef struct { size_t dst; unsigned bytes; unsigned long long v; } SparkleIntraImm;"
    , "typedef struct { unsigned dst; unsigned src; unsigned bytes; } SparkleIntraLink;"
    , "// dst/src: fields of the top struct; xsrc: where to load from in the exchange area"
    , "typedef struct { unsigned dst; unsigned src; unsigned bytes; unsigned xsrc; } SparkleIntraPull;"
    , "// an instance up to this size is held in a thread-local copy"
    , "#ifndef SPARKLE_INTRA_LOCAL_BYTES"
    , "#define SPARKLE_INTRA_LOCAL_BYTES 512"
    , "#endif"
    , "// every connection (applied once per launch) and every constant input"
    , s!"static __device__ const SparkleIntraCopy {topC}_intra_copies[{max copies.length 1}] = \{" ]
    ++ copyEntries ++
    [ "};"
    , s!"static __device__ const SparkleIntraImm {topC}_intra_imms[{max imms.length 1}] = \{" ]
    ++ immEntries ++
    [ "};"
    , "// per instance, the pulled input ports of its module type: the producer's"
    , "// slot in the exchange area (or the instance's own slot, when this"
    , "// instance gets that port from a top input or a constant: src == dst)"
    , s!"static __device__ const SparkleIntraPull {topC}_intra_pulls[{max pullEnts.length 1}] = \{" ]
    ++ orDummy pullEnts "  { 0u, 0u, 0u, 0u }," ++
    [ "};"
    , s!"static __device__ const unsigned {topC}_intra_pullStart[{m + 1}] = \{"
    , startRow pullStarts
    , "};"
    , "// per instance: where its outputs start in the exchange area"
    , s!"static __device__ const unsigned {topC}_intra_exOff[{m}] = \{"
    , startRow exOffArr.toList
    , "};"
    , "// top outputs fed by instance outputs, grouped by PRODUCER"
    , s!"static __device__ const SparkleIntraLink {topC}_intra_pubs[{max pubEnts.length 1}] = \{" ]
    ++ orDummy pubEnts "  { 0u, 0u, 0u }," ++
    [ "};"
    , s!"static __device__ const unsigned {topC}_intra_pubStart[{m + 1}] = \{"
    , startRow pubStarts
    , "};"
    , ""
    , "// Typed copy: a variable-length memcpy is a byte loop on the GPU."
    , s!"static __device__ inline void {topC}_intra_copy(char* d, const char* s, unsigned n) \{"
    , "  switch (n) {"
    , "  case 1: *(uint8_t*)d = *(const uint8_t*)s; break;"
    , "  case 2: *(uint16_t*)d = *(const uint16_t*)s; break;"
    , "  case 4: *(uint32_t*)d = *(const uint32_t*)s; break;"
    , "  case 8: *(uint64_t*)d = *(const uint64_t*)s; break;"
    , "  default: memcpy(d, s, n);"
    , "  }"
    , "}"
    , ""
    , "// instance inputs fed by a slice of a top input (once per launch)"
    , s!"static __device__ void {topC}_intra_static(struct {topC}* self) \{"
    , "  (void)self;" ]
    ++ statics ++
    [ "}"
    , ""
    , s!"static __device__ void {topC}_intra_eval(struct {topC}* self, unsigned t) \{"
    , s!"  char* b = (char*)self + {topC}_intra_off[t];"
    , s!"  switch ({topC}_intra_kind[t]) \{" ]
    ++ dispatchCases "eval" ++
    [ "  }"
    , "}"
    , ""
    , "// `ex`: the exchange area (shared memory in the block kernel when it"
    , "// fits, else a device buffer)."
    , "template <typename Group>"
    , s!"static __device__ void {topC}_intra_cycles(Group g, struct {topC}* self, char* ex, long cycles) \{"
    , "  const unsigned t  = g.thread_rank();"
    , "  const unsigned sz = g.num_threads();"
    , s!"  const bool live = t < (unsigned){topC}_intra_M;"
    , "  char* const base = (char*)self;"
    , "  // Prologue (once per launch): outputs of the current state, then every"
    , "  // connection and constant — top inputs cannot change during a launch."
    , s!"  if (live) {topC}_intra_eval(self, t);"
    , "  g.sync();"
    , s!"  for (unsigned i = t; i < (unsigned){topC}_intra_nCopies; i += sz) \{"
    , s!"    const SparkleIntraCopy* e = &{topC}_intra_copies[i];"
    , "    memcpy(base + e->dst, base + e->src, e->bytes);"
    , "  }"
    , s!"  for (unsigned i = t; i < (unsigned){topC}_intra_nImms; i += sz) \{"
    , s!"    const SparkleIntraImm* e = &{topC}_intra_imms[i];"
    , "    unsigned long long v = e->v;"
    , "    memcpy(base + e->dst, &v, e->bytes);"
    , "  }"
    , s!"  if (t == 0) {topC}_intra_static(self);"
    , "  g.sync();"
    , "  // Each thread keeps ITS instance in a local variable for the whole"
    , "  // launch (when it is small): the cycle loop then touches memory only"
    , "  // to store its outputs in the exchange area and to load its pulled"
    , "  // inputs from it.  With the instance in the top struct, every wire of"
    , "  // every evaluation is a load or a store there."
    , "  if (live) {"
    , s!"    char* const b = base + {topC}_intra_off[t];"
    , s!"    char* const xo = ex + {topC}_intra_exOff[t];"
    , s!"    const SparkleIntraPull* const pl = {topC}_intra_pulls + {topC}_intra_pullStart[t];"
    , s!"    const SparkleIntraLink* const pubs = {topC}_intra_pubs;"
    , s!"    const unsigned pb0 = {topC}_intra_pubStart[t], pb1 = {topC}_intra_pubStart[t + 1];"
    , "    (void)xo; (void)pl; (void)pubs; (void)pb0; (void)pb1;"
    , s!"    switch ({topC}_intra_kind[t]) \{" ]
    ++ (List.range kinds.length).flatMap kindLoop ++
    [ "    }"
    , "  } else {"
    , "    // padding thread: keep the barriers in step"
    , "    for (long c = 0; c < cycles; ++c) { g.sync(); g.sync(); }"
    , "  }"
    , "}"
    , ""
    , "// Block kernel: one block, cheap barrier.  `stage` bit 0: the exchange"
    , "// area is in shared memory (the host sets it when it fits); otherwise it"
    , "// is the device buffer `gex`.  The launch bound caps the registers per"
    , "// thread at what a block of this many threads can supply (65536 in"
    , "// all) — without it a launch of 1024 threads holding their instances in"
    , "// registers is refused."
    , s!"__global__ void __launch_bounds__({min 1024 (((m + 31) / 32) * 32)}) {topC}_intra_block_kernel(struct {topC}* self, long cycles, int stage, char* gex) \{"
    , "  extern __shared__ unsigned long long sparkle_sm[];"
    , s!"  {topC}_intra_cycles(cg::this_thread_block(), self, (stage & 1) ? (char*)sparkle_sm : gex, cycles);"
    , "}"
    , "// Grid kernel: any number of instances in 256-thread blocks, cooperative"
    , "// grid barrier, exchange area in the device buffer."
    , s!"__global__ void __launch_bounds__(256) {topC}_intra_grid_kernel(struct {topC}* self, long cycles, char* gex) \{"
    , s!"  {topC}_intra_cycles(cg::this_grid(), self, gex, cycles);"
    , "}"
    , "" ]

/-- `jit_intra_run(handle, cycles)`: run instance 0 of a `jit_cuda_alloc`
    handle for `cycles` clock cycles with the intra schedule.  Picks the
    block kernel when the instances fit one block (cheap barrier, exchange
    area in shared memory when it fits), else a cooperative grid launch
    (any size; grid-wide barrier, exchange area in a device buffer).  A
    failed kernel aborts with the CUDA error: it must not look like a run
    that changed nothing. -/
private def emitIntraHostRun (top : Module) : String :=
  let topC := sanitizeName top.name
  let st := s!"struct {topC}"
  String.intercalate "\n"
    [ "extern \"C\" {"
    , ""
    , "// Which kernel the last jit_intra_run used: 1 = block, 2 = grid."
    , "static int sparkle_intra_last_kernel = 0;"
    , "int jit_intra_last_kernel(void) { return sparkle_intra_last_kernel; }"
    , ""
    , "// Run instance 0 for numCycles with the intra (PE-per-thread) schedule."
    , "// The handle comes from jit_cuda_alloc (N=1 recommended); poke/peek via"
    , "// jit_cuda_set_input / jit_cuda_get_output as usual."
    , "void jit_intra_run(void* handle, long numCycles) {"
    , "  CudaHandle* h = (CudaHandle*)handle;"
    , s!"  {st}* d_top = h->d_states;"
    , s!"  cudaMemcpy(d_top, h->h_staging, sizeof({st}), cudaMemcpyHostToDevice);"
    , "  // exchange area on the device (used when it is not in shared memory)"
    , "  static char* d_ex = 0;"
    , s!"  if (!d_ex) cudaMalloc((void**)&d_ex, (size_t){topC}_intra_exBytes);"
    , s!"  static int useBlock = ({topC}_intra_M <= 1024) ? 1 : 0;"
    , "  cudaError_t launchErr = cudaSuccess;"
    , "  if (useBlock) {"
    , s!"    unsigned threads = (((unsigned){topC}_intra_M + 31u) / 32u) * 32u;"
    , "    static size_t shLimit = 0;"
    , "    if (shLimit == 0) {"
    , "      int dev = 0; cudaGetDevice(&dev);"
    , "      cudaDeviceProp prop; cudaGetDeviceProperties(&prop, dev);"
    , "      shLimit = prop.sharedMemPerBlockOptin ? prop.sharedMemPerBlockOptin : prop.sharedMemPerBlock;"
    , "    }"
    , s!"    size_t shBytes = ((size_t){topC}_intra_exBytes <= shLimit) ? (size_t){topC}_intra_exBytes : 0;"
    , "    int stage = shBytes ? 1 : 0;"
    , "    if (shBytes > 48 * 1024)"
    , s!"      cudaFuncSetAttribute({topC}_intra_block_kernel, cudaFuncAttributeMaxDynamicSharedMemorySize, (int)shBytes);"
    , s!"    {topC}_intra_block_kernel<<<1, threads, shBytes>>>(d_top, numCycles, stage, d_ex);"
    , "    launchErr = cudaGetLastError();"
    , "    // refused for resources: use the grid kernel from now on"
    , "    if (launchErr == cudaErrorLaunchOutOfResources) { useBlock = 0; launchErr = cudaSuccess; }"
    , "    else sparkle_intra_last_kernel = 1;"
    , "  }"
    , "  if (!useBlock) {"
    , "    int dev = 0; cudaGetDevice(&dev);"
    , "    int coop = 0; cudaDeviceGetAttribute(&coop, cudaDevAttrCooperativeLaunch, dev);"
    , "    if (!coop) { fprintf(stderr, \"jit_intra_run: cooperative launch unsupported on this device\\n\"); abort(); }"
    , "    const unsigned blockSize = 256;"
    , s!"    unsigned gridSize = ((unsigned){topC}_intra_M + blockSize - 1) / blockSize;"
    , "    int perSm = 0;"
    , s!"    cudaOccupancyMaxActiveBlocksPerMultiprocessor(&perSm, {topC}_intra_grid_kernel, blockSize, (size_t)0);"
    , "    cudaDeviceProp prop; cudaGetDeviceProperties(&prop, dev);"
    , "    if (gridSize > (unsigned)(perSm * prop.multiProcessorCount)) {"
    , "      fprintf(stderr, \"jit_intra_run: %u blocks exceed co-resident capacity %d\\n\","
    , "              gridSize, perSm * prop.multiProcessorCount);"
    , "      abort();"
    , "    }"
    , "    long cyc = numCycles;"
    , "    void* args[] = { (void*)&d_top, (void*)&cyc, (void*)&d_ex };"
    , s!"    cudaLaunchCooperativeKernel((void*){topC}_intra_grid_kernel, dim3(gridSize), dim3(blockSize), args, 0, 0);"
    , "    launchErr = cudaGetLastError();"
    , "    sparkle_intra_last_kernel = 2;"
    , "  }"
    , "  // A refused launch must not look like a run that changed nothing."
    , "  cudaError_t syncErr = cudaDeviceSynchronize();"
    , "  if (launchErr != cudaSuccess || syncErr != cudaSuccess) {"
    , "    fprintf(stderr, \"jit_intra_run: kernel failed (launch: %s, run: %s)\\n\","
    , "            cudaGetErrorString(launchErr), cudaGetErrorString(syncErr));"
    , "    abort();"
    , "  }"
    , s!"  cudaMemcpy(h->h_staging, d_top, sizeof({st}), cudaMemcpyDeviceToHost);"
    , "}"
    , ""
    , "} // extern \"C\""
    , "" ]

/-- Generate the intra `.cu` for a whole `Design`.  The file contains the
    CSim device code (all modules, host+device qualified), the intra tables +
    kernels, AND the batch kernel + host JIT API — one `.so` serves both
    axes.  Compile with `-rdc=true` (cooperative groups). -/
def toCudaIntraDesign (d : Design) : Except String String := do
  if d.modules.any moduleHasSymbolicWidth then
    throw "CudaIntra requires concrete widths; specialize retained parameters before CUDA lowering"
  let some top := d.findModule d.topModule
    | throw s!"top module '{d.topModule}' not found in design"
  let insts ← topInsts d top
  if insts.isEmpty then
    throw s!"top module '{top.name}' has no instances — the intra backend parallelises over top-level .inst; use toCudaSim for a flat module"
  let (copies, imms, statics) ← buildTables top insts
  let intra ← emitIntraSection top insts copies imms statics
  let topC := sanitizeName top.name
  let preamble := String.intercalate "\n"
    [ "// AUTO-GENERATED by Sparkle HDL — CUDA Intra (within-instance) Backend"
    , s!"// Module: {top.name} — {insts.length} top-level instances, one thread each"
    , "//"
    , "// Compile with (relocatable device code is required by grid.sync):"
    , s!"//   nvcc -O3 -std=c++17 -rdc=true -shared -Xcompiler -fPIC -o lib{topC}.so {topC}.cu"
    , ""
    , "#include <cstdint>"
    , "#include <cstring>"
    , "#include <cstddef>"
    , "#include <cstdio>"
    , "#include <cstdlib>"
    , "#include <cuda_runtime.h>"
    , "#include <cooperative_groups.h>"
    , ""
    , "// ── CSim device code (struct + __host__ __device__ module functions) ─" ]
  return String.intercalate "\n"
    [ preamble
    , emitCudaDeviceCodeD d
    , intra
    , "// ── Batch kernel ─────────────────────────────────────────────────"
    , emitCudaBatchKernel top
    , emitCudaJITHostAPI top
    , emitIntraHostRun top ]

/-- Specialize every retained dimension before analysing struct layouts and
    emitting the within-instance copy tables for one fixed configuration. -/
def toCudaIntraDesignWithParameters (d : Design)
    (bindings : Sparkle.IR.Specialize.Bindings) : Except String String := do
  let concrete ← Sparkle.IR.Specialize.specializeDesign d bindings
  toCudaIntraDesign concrete

/-- Like `toCudaIntraDesign`, but renders an analysis error as a `#error`
    line so a build-time generation failure is loud at nvcc time. -/
def toCudaIntraDesign! (d : Design) : String :=
  match toCudaIntraDesign d with
  | .ok s => s
  | .error e => s!"#error \"Sparkle CudaIntra: {e.replace "\"" "'"}\"\n"

/-- String-rendering form of `toCudaIntraDesignWithParameters`; specialization
    and analysis failures remain loud compiler errors in the generated file. -/
def toCudaIntraDesignWithParameters! (d : Design)
    (bindings : Sparkle.IR.Specialize.Bindings) : String :=
  match toCudaIntraDesignWithParameters d bindings with
  | .ok s => s
  | .error e => s!"#error \"Sparkle CudaIntra: {e.replace "\"" "'"}\"\n"

end Sparkle.Backend.CudaIntra
