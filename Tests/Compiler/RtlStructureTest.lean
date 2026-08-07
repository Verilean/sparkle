/-
  Structural lint over EMITTED RTL — the guard rail for miscompiles that
  every Lean-side check misses.

  ## Why this file exists

  Three separate elaborator/backend bugs were found in one week, and all three
  shared a signature: `#synthesizeVerilog` succeeded, the Lean-side tests
  passed, and the *emitted Verilog was wrong*.

  1. `extractWidth` silently defaulted a symbolic width to 8 bits, so a 49-bit
     divisor register was fed through an 8-bit wire and latched zero
     (`IP/Control/DividerQ`, fixed).
  2. An attempted issue-#95 rework collapsed 27 `keccakRcHW` ROM instances to
     1, so every Keccak round used the same round constant and the sponge
     digest broke (reverted).
  3. A projection memo handed a wire allocated in a sub-module's scope back to
     the parent, emitting references to undeclared wires (reverted).

  None of those is expressible as "does it compile" or "does the model agree".
  Each is a property OF THE TEXT: are all referenced wires declared, is each
  sub-module instantiated the expected number of times, does the register
  count match the design.  This file checks exactly those properties, on real
  designs, so the next bug of this class fails a test instead of a digest.

  ## What the checks are

  * `undeclaredWires` — every `_tmp_*` / `_gen_*` identifier appearing in a
    module body must be a declared `logic`, a port, an instance name, or an
    instance's port label.  This is the check that caught bug 3.  It is a
    cheap syntactic approximation, deliberately: it needs no Verilog parser
    and it is exactly strong enough for the failure mode.
  * `countRegisters` / `countInstancesOf` — pinned per design.  These catch
    bugs 1 and 2 (a fused ROM shows up as an instance-count drop, a collapsed
    register file as a register-count drop) without needing to know what the
    right *values* are — only that they don't change silently.

  ## Scope, stated honestly

  These are *structural* checks, not correctness proofs.  A design can pass
  every check here and still compute the wrong function; that is what the
  JIT / iverilog co-sims in `Tests/IP/Control/ControlJITTest.lean` are for.
  What this file buys is that the three bugs above become impossible to land
  silently.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.Observer
import IP.Control.IIRBiquadGen
import IP.Crypto.Keccak256Sponge
import LSpec

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IR.AST
open Sparkle.Backend.Verilog
open Sparkle.Compiler.Elab
open Lean
open LSpec

namespace Sparkle.Tests.Compiler.RtlStructureTest

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

/-! ### Text utilities (no Verilog parser — see the header) -/

private def containsSubstr (s sub : String) : Bool :=
  decide ((s.splitOn sub).length > 1)

/-- Identifier characters, for the crude tokenizer below. -/
private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_'

/-- Split emitted Verilog into `(moduleName, body)` pairs. -/
def splitModules (verilog : String) : List (String × String) :=
  let lines := verilog.splitOn "\n"
  let rec go (ls : List String) (cur : Option (String × List String))
      (acc : List (String × String)) : List (String × String) :=
    match ls with
    | [] =>
      match cur with
      | some (n, body) => acc ++ [(n, String.intercalate "\n" body.reverse)]
      | none => acc
    | l :: rest =>
      if l.startsWith "module " then
        -- NB: shadowing `rest` here would break the recursion (it is the
        -- remaining LINES).  Name the char list separately.
        let nameChars := l.toList.drop 7
        let name := String.mk (nameChars.takeWhile isIdentChar)
        let acc' := match cur with
          | some (n, body) => acc ++ [(n, String.intercalate "\n" body.reverse)]
          | none => acc
        go rest (some (name.trim, [l])) acc'
      else
        match cur with
        | some (n, body) =>
          if containsSubstr l "endmodule" then
            go rest none (acc ++ [(n, String.intercalate "\n" (l :: body).reverse)])
          else go rest (some (n, l :: body)) acc
        | none => go rest none acc
  go lines none []

/-- All `_tmp_*` / `_gen_*` identifiers occurring in a body. -/
def identsIn (body : String) : List String :=
  let cs := body.toList
  let rec go (cs : List Char) (cur : List Char) (acc : List String) : List String :=
    match cs with
    | [] =>
      let w := String.mk cur.reverse
      if w.startsWith "_tmp_" || w.startsWith "_gen_" then w :: acc else acc
    | c :: rest =>
      if isIdentChar c then go rest (c :: cur) acc
      else
        let w := String.mk cur.reverse
        let acc' := if w.startsWith "_tmp_" || w.startsWith "_gen_" then w :: acc else acc
        go rest [] acc'
  (go cs [] []).eraseDups

/-- Names bound by a `logic …;` declaration, a port, an instance name, or an
    instance port label (`.foo(bar)` — `foo` is the CHILD's port, not a wire
    of this module). -/
def boundNames (body : String) : List String := Id.run do
  let mut out : List String := []
  for line in body.splitOn "\n" do
    let t := line.trim
    -- `logic [7:0] name;`  /  `logic name;`
    if t.startsWith "logic " then
      let afterBracket : String :=
        if containsSubstr t "]" then (t.splitOn "]").getLast!
        else String.mk (t.toList.drop 6)
      let nm := ((afterBracket.splitOn ";").head!).trim
      if nm != "" then out := nm :: out
    -- ports: `input logic [..] name,` / `output logic name`
    if t.startsWith "input " || t.startsWith "output " then
      let afterBracket :=
        if containsSubstr t "]" then (t.splitOn "]").getLast!
        else t
      let cleaned := ((afterBracket.replace "," "").replace ")" "").trim
      let nm := ((cleaned.splitOn " ").getLast!).trim
      if nm != "" then out := nm :: out
    -- instance line: `Child _tmp_inst_x (.a(b), .c(d));`
    -- bind the instance name AND every `.label(` (child-side port names).
    if containsSubstr t "_tmp_inst_" then
      for tok in identsIn t do
        if tok.startsWith "_tmp_inst_" then out := tok :: out
    for seg in t.splitOn "." do
      if containsSubstr seg "(" then
        let lbl := (seg.splitOn "(").head!.trim
        if lbl != "" then out := lbl :: out
  return out.eraseDups

/-- Identifiers referenced but never bound — a miscompile signature. -/
def undeclaredWires (body : String) : List String :=
  let bound := boundNames body
  (identsIn body).filter (fun i => !bound.contains i)

/-- Declared output ports of a module body. -/
def outputPorts (body : String) : List String := Id.run do
  let mut out : List String := []
  for line in body.splitOn "\n" do
    let t := line.trim
    if t.startsWith "output " then
      let afterBracket := if containsSubstr t "]" then (t.splitOn "]").getLast! else t
      let cleaned := ((afterBracket.replace "," "").replace ")" "").trim
      let nm := ((cleaned.splitOn " ").getLast!).trim
      if nm != "" then out := nm :: out
  return out.eraseDups

/-- Output ports that are declared but never driven — i.e. the module has a
    dangling primary output.

    This is a MISCOMPILE the `undeclaredWires` check cannot see: the port is
    declared, so nothing is "undeclared"; it simply has no `assign` and no
    `always_ff` writing it, so downstream logic reads Z/X.  Found exactly this
    in the `#sim` `.sv` sidecar for multi-output records projected off a nested
    engine (`divSim`, `tvkSim`): both declare their ports and drive neither,
    while the same designs through `#synthesizeVerilog` DO emit
    `assign out = …`.  yosys reports it as "Wire … is used but has no driver". -/
def undrivenOutputs (body : String) : List String :=
  let outs := outputPorts body
  outs.filter fun o =>
    let drivenByAssign := containsSubstr body s!"assign {o} ="
    let drivenByReg := containsSubstr body s!"{o} <="
    -- an instance connection `.o(wire)` on the CHILD side does not drive OUR o
    !(drivenByAssign || drivenByReg)

def countRegisters (body : String) : Nat :=
  (body.splitOn "always_ff").length - 1

def countInstancesOf (verilog : String) (childModule : String) : Nat :=
  ((verilog.splitOn s!"{childModule} _tmp_inst_").length) - 1

/-! ### Designs under test

Real control IP, chosen to cover the shapes the three bugs lived in:
symbolic-width datapath (`DividerQ`), a nested engine consumed through a
multi-output record (`tvKalman`), and a plain flat FSM (`biquad`). -/

def divTop (num den : Signal defaultDomain (BitVec 32)) (start : Signal defaultDomain Bool)
    : Signal defaultDomain (BitVec 32) :=
  projN! (Sparkle.IP.Control.DividerQ.dividerQ15_16 num den start) 2 0

def tvkTop (y u : Signal defaultDomain (BitVec 32)) (tick : Signal defaultDomain Bool)
    : Signal defaultDomain (BitVec 32) :=
  Sparkle.IP.Control.Observer.tvKalman 32 16 y u tick

def biqTop (x : Signal defaultDomain (BitVec 32)) : Signal defaultDomain (BitVec 32) :=
  Sparkle.IP.Control.IIRBiquadGen.stableQ15_16 x

/-- Synthesize a whole design (top + sub-modules) to Verilog text. -/
def designText (declName : Name) : MetaM String := do
  let design ← synthesizeHierarchical declName
  return toVerilogDesign design

/-! ### The checks, run at elaboration time

`run_meta` so a violation fails `lake build` — these are compiler guard rails,
so they should break the build, not merely a test run. -/

run_meta do
  for declName in [``divTop, ``tvkTop, ``biqTop] do
    let text ← designText declName
    let mods := splitModules text
    if mods.isEmpty then
      throwError s!"RTL structure: {declName} produced no modules"
    for (mname, body) in mods do
      let undriven := undrivenOutputs body
      unless undriven.isEmpty do
        throwError s!"RTL structure: {declName} module {mname} declares output \
port(s) {undriven} that are NEVER DRIVEN.\n\nDownstream logic reads Z/X. \
yosys reports this as \"used but has no driver\".  Fix the backend; do not \
relax this check."
      let bad := undeclaredWires body
      unless bad.isEmpty do
        throwError s!"RTL structure: {declName} module {mname} references \
undeclared wires {bad}.\n\nThis is a MISCOMPILE signature: the elaborator \
emitted a reference to a wire it never declared (typically a wire allocated \
in another module's scope leaking through a cache/memo).  Fix the elaborator; \
do not relax this check."
    IO.println s!"[rtl-structure] {declName}: {mods.length} module(s), \
regs={mods.foldl (fun a (_, b) => a + countRegisters b) 0}, no undeclared wires"

/-! ### Pinned structural counts

These numbers are *observations*, recorded so a silent change fails.  If a
legitimate design change moves one, update it in the same commit and say why —
that is the whole point of pinning. -/

run_meta do
  let text ← designText ``divTop
  let mods := splitModules text
  let total := mods.foldl (fun a (_, b) => a + countRegisters b) 0
  -- DividerQ.SigState is counter, rem, quot, den, negate, done = 6 registers,
  -- but `divTop` only exposes the quotient — it never reads `done`.  The
  -- Phase-4.5 output-reachability prune therefore drops the `done` register,
  -- leaving 5.  That is a genuine removal, not a fusion: the 22-case divider
  -- co-sim in `Tests/IP/Control/ControlJITTest.lean` still matches `divQref`
  -- through the full handshake, and `tvkTop` (which DOES consume `done`)
  -- keeps all 6.
  unless total == 5 do
    throwError s!"RTL structure: divTop register count changed: {total} (pinned 5). \
A DROP means state was fused (the bug that collapsed 27 Keccak ROMs to 1); \
a RISE means state was duplicated (the bug that copied a nested engine per \
output field).  Investigate before repinning."
  IO.println s!"[rtl-structure] divTop registers = {total} (pinned)"

run_meta do
  let text ← designText ``biqTop
  let mods := splitModules text
  let total := mods.foldl (fun a (_, b) => a + countRegisters b) 0
  -- Direct-Form-II-transposed biquad: s1, s2.
  unless total == 2 do
    throwError s!"RTL structure: biqTop register count changed: {total} (pinned 2)"
  IO.println s!"[rtl-structure] biqTop registers = {total} (pinned)"

/-! `tvKalman` currently emits **76** registers, not the 16 its design implies
(10 FSM + one 6-register `dividerQ` engine): the engine is duplicated ELEVEN
times.  This lint found that in committed code, and the cause is structural,
not a cache miss.

`Sparkle.Core.runCircuitH` calls the user's `body` **twice** — once inside
`Signal.loop` to build the register next-state, once outside to take the
return value:

    let stateLoop := Signal.loop (fun live => … body (mkRegList live …) … )
    …
    (body (mkRegList stateLoop …) id).fst

So `let e := dividerQ w f …` inside a `circuit do` is elaborated into two
INDEPENDENT expressions (they close over different `live`: the loop binder vs
`stateLoop`), which cannot share a structural cache entry — and each
additional *use* of a projection multiplies the walk further.  Measured
directly: one use of each projection → 2 engine copies; `tvKalman`'s six uses
→ 11.

This is area-only, not a functional error: every copy is fed identical inputs
and computes identically, which is why the JIT and iverilog co-sims
(`Tests/IP/Control/ControlJITTest.lean`) pass and the digest is right.  It is
also the same duplication mechanism that made the reverted issue-#95 rework
produce a WRONG digest — there the copies stopped being benign.

Pinned at the measured value so the number cannot drift silently in either
direction.  Lowering it is a real optimisation (≈11× the divider area) and
should update this pin with a note. -/
run_meta do
  let text ← designText ``tvkTop
  let mods := splitModules text
  let total := mods.foldl (fun a (_, b) => a + countRegisters b) 0
  -- 16 = 10 FSM + ONE 6-register divider engine.  This is the design's own
  -- answer: the duplication is gone.  Getting here took three fixes —
  -- the fvar-abstracted `let` cache key (76 → 28), the flat pending-write
  -- accumulator (28 → 22), and the Phase-4.5 output-reachability prune
  -- (22 → 16).  A RISE means duplication regressed.
  unless total == 16 do
    throwError s!"RTL structure: tvkTop register count changed: {total} \
(pinned 16 = 10 FSM + 1 divider engine — the fully-deduplicated value)."
  IO.println s!"[rtl-structure] tvkTop registers = {total} \
(pinned; single engine — duplication fully eliminated)"

/-! ### The unsupported pattern, documented as a test

An untagged (non-`@[hardware_module]`) nested `circuit do` engine consumed
through a multi-output record does not synthesize.  This is a REAL limitation,
not a bug in the test: the projection path can reduce a record-producing
*application* to its constructor, but not a `let`-bound fvar, and only the
tagged path consults `sparkleFvarValueMap` to recover the call.

The failure mode is confusing — the error names the FIELD (`Cannot instantiate
Eng2Out.done: not a hardware module definition`) rather than the missing tag —
so the shape is recorded here with the cure.  Tag the engine
`@[hardware_module]` and it synthesizes as a shared sub-module instance.

`Tests/Compiler/MultiOutputSubModuleHangRepro.lean` documents the neighbouring
hang; this documents the projection gap. -/

structure Eng2Out (dom : DomainConfig) where
  cnt : Signal dom (BitVec 8)
  done : Signal dom Bool

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Eng2Out dom) dom := ⟨⟩

/-- The engine, TAGGED — this is the supported spelling. -/
@[hardware_module] def eng2 (start : Signal defaultDomain Bool) : Eng2Out defaultDomain :=
  circuit do
    let c ← Signal.reg (0#8)
    let d ← Signal.reg false
    let cS := (c : Signal defaultDomain (BitVec 8))
    c <~ Signal.mux start (Signal.lit defaultDomain 1#8)
          (cS + (Signal.lit defaultDomain 1#8))
    d <~ (cS === (Signal.lit defaultDomain 5#8))
    return { cnt := cS, done := (d : Signal defaultDomain Bool) }

structure Outer2Out (dom : DomainConfig) where
  latched : Signal dom (BitVec 8)
  innerCnt : Signal dom (BitVec 8)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (Outer2Out dom) dom := ⟨⟩

/-- Outer register drives the engine; BOTH engine fields are consumed — one
    through a register write, one as a direct output leaf.  This is the shape
    Keccak's sponge has, and the shape the reverted rework broke. -/
def outerShared (go : Signal defaultDomain Bool) : Outer2Out defaultDomain :=
  circuit do
    let kick ← Signal.reg false
    let lat ← Signal.reg (0#8)
    let e := eng2 (kick : Signal defaultDomain Bool)
    kick <~ go
    lat <~ Signal.mux e.done e.cnt (lat : Signal defaultDomain (BitVec 8))
    return { latched := lat, innerCnt := e.cnt }

run_meta do
  let text ← designText ``outerShared
  let mods := splitModules text
  let total := mods.foldl (fun a (_, b) => a + countRegisters b) 0
  let insts := countInstancesOf text "eng2"
  -- 4 registers total (kick, lat + the engine's c, d) and EXACTLY ONE engine
  -- instance shared by both consumed fields.
  unless total == 4 do
    throwError s!"RTL structure: outerShared registers = {total} (want 4). \
A rise means the engine was instantiated per projected field."
  unless insts == 1 do
    throwError s!"RTL structure: outerShared has {insts} eng2 instances (want 1). \
Both `e.done` and `e.cnt` must come from ONE shared instance."
  for (mname, body) in mods do
    let bad := undeclaredWires body
    unless bad.isEmpty do
      throwError s!"RTL structure: outerShared module {mname} undeclared wires {bad}"
  IO.println s!"[rtl-structure] outerShared: regs={total}, eng2 instances={insts} (shared)"

/-! ### The `let`-binding cache win, pinned

`runCircuitH` calls the user's `body` twice (once inside `Signal.loop` for the
register next-state, once outside for the return value), and the hardware-`let`
handler used to translate its value with `isNamed := true` — which bypasses the
expression cache in both directions.  Every `let e := <engine> …` inside a
`circuit do` was therefore walked twice, emitting a second copy of the engine's
registers, plus one more per additional use of a projection.

The handler now consults the cache before doing the named translation.  When
the engine's inputs do NOT depend on the registers, the two walks produce
structurally identical expressions and collapse to one instance.

`engineFromInputs` below is that case: one 6-register `dividerQ` engine driven
straight from module inputs, its two projections both consumed.  Correct is
7 registers (1 accumulator + 6 engine) and ONE engine.  Before the fix this
was 13 registers / 2 engines.

The residual case is when the engine's arguments derive from register reads.
`tvkTop` above is still pinned at 76 because of it, and the reason is a hard
one — established by instrumenting the elaborator rather than by guessing:

* the 11 `let engine := dividerQ 32 16 divNum s startDiv` occurrences PRINT
  identically but every one has a distinct `Expr.hash`;
* the difference is invisible to the pretty-printer: `divNum`/`s`/`startDiv`
  are distinct *fvar objects* sharing a user name, one set per walk;
* those upstream `let divNum := …` bindings are themselves all distinct
  (11 occurrences, 11 hashes, zero cache hits), and each resolves to a
  freshly-allocated wire (`_gen_divNum`, `_gen_divNum_1`, …);
* keying on the engine's argument wires therefore cannot work either — that
  was tried and reverted.

Contrast a binding that DOES dedupe: `let phase := …` (a direct register read)
has the same hash nine times out of eleven occurrences, so the cache collapses
it.  The divergence is injected downstream of the register reads and amplifies.

Candidate keys that were checked and rejected, so nobody re-treads them:
`(binderName)` alone — unsafe, `IP/Crypto/AESHW` has three different
`let a := _ ^^^ _` in one `circuit do`; `(binderName, callee, arity)` — unsafe
for the same reason (all three share `HXor.hXor`/2); a per-name ordinal — the
two walks are not symmetric (11 engine bindings is odd).

So merging these needs an identity that survives re-walking — not another
cache key.  Two further approaches were implemented and MEASURED, and both are
recorded here as dead ends:

* **IR-level CSE** (same rhs → reuse one lhs, iterated to a fixpoint): merges
  nothing on `tvKalman`.  The duplicate registers are MUTUALLY RECURSIVE —
  `_gen_counterNext` references `_tmp_a_61` (its own register) while the copy's
  `_gen_counterNext_1` references `_tmp_a_201` — so they are identical only up
  to renaming and literal `BEq` never fires.  Note the existing dedupe in
  `optimizeModule` keys on same-LHS, a different (and also insufficient) rule.
* **Bisimulation / partition refinement** (seed same-shape registers into one
  class, split on input disagreement until stable): got 76 → 66 registers but
  was WRONG — it merged non-equivalent registers and every Keccak digest went
  to all-zero.  Getting the refinement sound (correct seeding, correct
  propagation of splits through the recursive cone) is real work, not a tweak.

## Fixed (partly): fvar-abstracted `let` cache key

The `.letE` handler now keys its wire cache on the value ABSTRACTED over its
free variables — each fvar rewritten to a constant named after the wire it
denotes — instead of on the raw expression.  Raw hashing cannot work because
each consumer of a `circuit do` body re-instantiates binders with fresh fvars,
so two occurrences denoting identical hardware hash differently (measured:
2079038327 vs 1490760256 for two `let num` occurrences whose fvars both mapped
to `_gen_pS`, `_gen_y`).

Measured effect:

    regDependentEngine   27 regs / 4 engines  →  21 / 3
    tvkTop               76 regs / 11 engines →  28 / 3
    yosys on tvkTop      1144 flip-flops      →  850   (−26 %)
                         50 216 cells         →  49 349 (−1.7 %)

The cell number is the honest one to quote: yosys already merged most of the
duplicated COMBINATIONAL logic on its own, so the real saving is in flip-flops,
which it cannot merge.  The earlier "≈21 % of the design" estimate assumed no
downstream sharing and was too optimistic.

Residual: 3 engines rather than 1.  Localised exactly, by logging the cache key
per consumer:

    consumer 1   LK pS key=3590432345   wires=[_tmp_loop_0, …]        (miss)
    consumer 2   LK pS key=3590432345   wires=[_tmp_loop_0, …]        (HIT)
    consumer 3   LK pS key=1267503053   wires=[UNMAPPED(_uniq.3705), …]
    consumer 4   LK pS key=771491018    …

Consumers 1–2 share every key.  From consumer 3 the register read `pS` itself
changes key, and everything downstream follows.  Printing the two values shows
they differ in exactly one position:

    consumer 3:  Reg.mk ((fun s => Signal.map Prod.fst (idRead s)) live)
    consumer 4:  Reg.mk ((fun s => Signal.map Prod.fst (idRead s)) stateLoop)

`live` (the `Signal.loop` binder, wire `_tmp_loop_0`) versus `stateLoop` (the
loop term itself, wire `_tmp_loop_body_134`).  These DENOTE THE SAME SIGNAL —
`stateLoop` is the loop's fixpoint — but are given different wires, so every
register read behind them diverges and re-emits the engine.

Sharing the loop wire was implemented and measured: no effect, because the four
loop terms also carry four distinct `Expr.hash`es (each consumer re-instantiates
the loop term too).  Reverted.  That is the FOURTH distinct expression-keyed
approach to fail for the same underlying reason, which is now conclusive:

    Every consumer of a `circuit do` body re-instantiates the ENTIRE term —
    lets, loop binders and loop terms alike — so nothing keyed on expression
    identity can ever merge them.

The fix must therefore make `live` and `stateLoop` resolve to ONE wire by
construction — i.e. translate the body once into a shared wire environment and
have consumers read from it — rather than detect the coincidence afterwards.

### The rebuild was attempted, and measured

`packRegister` is where the multiplication happens: each slot re-projects the
shared next-state term (`Signal.map Prod.fst next` / `… Prod.snd next`), so
`next` — the whole body computation — appears once per slot.  Confirmed by
counting: `regDependentEngine` has ONE return leaf yet three engine copies, so
`splitReturnLeaves` is not the multiplier; and the `next` mentions carry
distinct `Expr.hash`es per slot, so the elaborator cannot share them either.

The flat per-slot accumulator (`Circuit.SigList`, from the reverted #95 work)
addresses this directly, and it does improve the numbers — with the three
elaborator gaps it needs re-applied (PUnit chain terminator, `SigList` in the
Prod.mk accumulator detection, `Seq.seq`/`Functor.map` spine normalisation):

    regDependentEngine   21 regs / 3 engines  →  15 / 2
    tvkTop               28 regs / 3 engines  →  22 / 2

But the Keccak sponge digest breaks — all four fixtures, including the two
(`empty`, `abc`) that pass on main.  Same failure that caused the original
revert of #95, so the three re-applied elaborator fixes are NOT the whole gap.
Reverted again; digests verified restored.

Conclusion for the next attempt: the flat accumulator is the right direction
(it is the only change that has moved these numbers), but landing it requires
first finding what it breaks in the sponge — a nested `@[hardware_module]`
engine (`wKeccakF`) driven from an FSM, which neither `regDependentEngine` nor
`tvkTop` covers.  A sponge-shaped structural test should exist BEFORE the next
attempt, so the failure is localised in seconds rather than by digest bisection.

## The cost, measured with yosys (not "harmless")

`synth -flatten` on `tvkTop`:

    50 216 cells,  572 flip-flops,  49 509 wires

and one `dividerQ15_16` alone:

    1 058 cells,  137 flip-flops

So the 11 copies are ≈11 600 cells — about **21 % of the whole design** — and
removing 10 of them would save ≈10 600 cells.  For scale, a Tang Nano 20K has
roughly 20 k LUTs: at 50 k cells this ONE drone-axis Kalman filter does not
fit.  Calling it "functionally harmless" understates it; in hardware, area is
part of correctness, and this duplication is the difference between fitting on
the target board and not.

### Correction: the multiplier is CONSUMERS, not the two body walks

An earlier version of this note blamed the duplication on `runCircuitH` calling
`body` twice.  Instrumenting every hardware-`let` shows that is wrong, and the
real number is worse-behaved:

    HWLET stateLoop  ×1     HWLET nextState ×1
    HWLET e          ×4     HWLET res ×4    HWLET dn ×4   HWLET num ×4  …

`stateLoop`/`nextState` appear ONCE, yet everything inside them jumps straight
to 4 — and 4 = **3 register writes + 1 returned output**, i.e. the number of
CONSUMERS of the shared `let` chain.  `packRegister` builds each register's
input independently, and every one of those traversals re-enters the same
`let e := dividerQ …`.  So the growth is (number of consumers), and the two
body walks are a constant factor on top, not the cause.

That also explains why every expression-keyed attempt fails: each consumer's
traversal instantiates the binder with a FRESH fvar, so the four `let e` nodes
have four distinct `Expr.hash`es (verified).  Memoizing the whole `.letE` node
was tried too — same result, same reason.

### Routes assessed for a sound fix

* put `ρ` in the loop state — needs `Inhabited`/`Wireable ρ` at every call
  site.  Measured surface: **173 `circuit do` sites**, 56 returning a bare
  `Signal` and ~115 returning records (`MulOut`, `RxOut`, `SpongeOut`, …).  A
  real API change, but a mechanical one.
* have the loop body reuse the outer `regs` (so `body` is called once) — NOT
  well-founded in Lean: `Signal.loop (fun _ => f stateLoop)` where `stateLoop`
  is the loop itself fails termination checking.  Verified, not assumed.

A third route, given the corrected diagnosis: make the elaborator translate a
`circuit do` body ONCE into a shared wire environment, and have each consumer
read wires out of it rather than re-traverse the term.  That is a change to how
`splitReturnLeaves`/`packRegister` consume the body, and it is where the next
attempt should start — not at another cache key.

Until one lands, these pins are the tripwire. -/

def engineFromInputs (n d : Signal defaultDomain (BitVec 32))
    (st : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 32) :=
  circuit do
    let acc ← Signal.reg (0#32)
    let e := Sparkle.IP.Control.DividerQ.dividerQ 32 16 n d st
    acc <~ Signal.mux (Signal.snd e) (Signal.fst e)
             (acc : Signal defaultDomain (BitVec 32))
    return acc

run_meta do
  let text ← designText ``engineFromInputs
  let mods := splitModules text
  let total := mods.foldl (fun a (_, b) => a + countRegisters b) 0
  unless total == 7 do
    throwError s!"RTL structure: engineFromInputs registers = {total} (pinned 7 \
= 1 accumulator + 6 divider).  A rise to 13 means the hardware-`let` handler \
stopped consulting the expression cache and `runCircuitH`'s double body call \
is duplicating the engine again."
  for (mname, body) in mods do
    let bad := undeclaredWires body
    unless bad.isEmpty do
      throwError s!"RTL structure: engineFromInputs module {mname} undeclared {bad}"
  IO.println s!"[rtl-structure] engineFromInputs registers = {total} \
(pinned; let-binding cache dedupe intact)"

/-! ### The register-dependent duplication, as a small reproducer

`tvkTop` (76 registers / 11 engines) is unwieldy to iterate on.  This is the
same bug in 20 lines: a `dividerQ` engine whose arguments derive from REGISTER
reads, so the two `runCircuitH` body walks produce structurally different
expressions and the `let`-cache fix of da4daa7 cannot collapse them.

Correct is 9 registers (3 FSM + 6 engine) and ONE engine.  Currently 27 / 4.

Pinned at the broken value deliberately: when someone fixes the double body
walk, THIS is the test that should flip first, and 27 → 9 is the signal that
the fix works.  Measured area (yosys `synth -flatten`) for the full-size case
is in the `tvkTop` note above: ≈21 % of the design is duplicate dividers. -/

def regDependentEngine (y : Signal defaultDomain (BitVec 32))
    : Signal defaultDomain (BitVec 32) :=
  circuit do
    let p ← Signal.reg (0#32)
    let ph ← Signal.reg (0#3)
    let acc ← Signal.reg (0#32)
    let pS := (p : Signal defaultDomain (BitVec 32))
    let phS := (ph : Signal defaultDomain (BitVec 3))
    let num := pS + y
    let den := pS + (Signal.lit defaultDomain 1#32)
    let stt := phS === (Signal.lit defaultDomain 1#3)
    let e := Sparkle.IP.Control.DividerQ.dividerQ 32 16 num den stt
    let res := Signal.fst e
    let dn := Signal.snd e
    p <~ Signal.mux dn res pS
    ph <~ Signal.mux dn (Signal.lit defaultDomain 2#3) phS
    acc <~ Signal.mux dn res (acc : Signal defaultDomain (BitVec 32))
    return acc

run_meta do
  let text ← designText ``regDependentEngine
  let mods := splitModules text
  let total := mods.foldl (fun a (_, b) => a + countRegisters b) 0
  -- 9 = 3 FSM + one 6-register engine, which is correct.  Was 27, then 21
  -- (fvar-abstracted `let` cache key), then 15 (flat pending-write
  -- accumulator), now 9 (Phase-4.5 output-reachability prune).  Pinned
  -- exactly: this reproducer is the canary for consumer duplication, so any
  -- movement in either direction should fail.
  unless total == 9 do
    throwError s!"RTL structure: regDependentEngine registers = {total} \
(expected 15 = current, or 9 = fully fixed).  Was 21 before the flat \
pending-write accumulator, 27 before the \
fvar-abstracted `let` cache key."
  IO.println s!"[rtl-structure] regDependentEngine = {total} \
(pinned; 3 FSM + 1 engine — consumer duplication eliminated)"

/-! ### Sponge-shaped structural test

The one design shape that repeatedly breaks when `runCircuitH` is restructured
is Keccak's sponge: an FSM that drives a nested `@[hardware_module]` engine
(`wKeccakF`) and consumes several of its output fields.  Both attempts at the
flat pending-writes accumulator produced a wrong sponge digest while
`regDependentEngine` and `tvkTop` looked fine, so those two do not cover it.

This pins the sponge's STRUCTURE, which is checkable in seconds — unlike the
digest, which needs a JIT build and a full co-sim run.  A restructuring that
changes these counts is changing the sponge's hardware, and that is the signal
to stop and look before spending a co-sim cycle. -/

run_meta do
  let text ← designText ``Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW
  let mods := splitModules text
  let total := mods.foldl (fun a (_, b) => a + countRegisters b) 0
  let rcInst := countInstancesOf text "Sparkle_IP_Crypto_Keccak256HW_keccakRcHW"
  let kfInst := countInstancesOf text "Sparkle_IP_Crypto_Keccak256Sponge_wKeccakF"
  for (mname, body) in mods do
    let bad := undeclaredWires body
    unless bad.isEmpty do
      throwError s!"RTL structure: sponge module {mname} undeclared wires {bad}"
    let undriven := undrivenOutputs body
    unless undriven.isEmpty do
      throwError s!"RTL structure: sponge module {mname} undriven outputs {undriven}"
  -- 59 registers / 1 permutation instance / 2 round-constant ROM instances.
  --
  -- These counts are DIGEST-VERIFIED: with them, `keccak256-sponge-jit-test`
  -- reproduces the reference hashes for `empty` and `abc`.  (The 136B/200B
  -- multi-block fixtures fail identically on `main` — a separate,
  -- pre-existing bug, not covered by these pins.)
  --
  -- Was 84 before the Phase-4.5 output-reachability prune removed the
  -- unreachable duplicate register banks.
  --
  -- They replaced an earlier 57/1/27 pin taken while the `.proj` handler was
  -- silently miscompiling wide records: field `idx ≥ 1` of an N>2-field
  -- record underflowed `(1 - idx)` in `Nat` and sliced the LOW bits of field
  -- 0, so `kf.done` (field 26 of 27) became `lane0 & 1`.  That aliasing is
  -- what made the register count look smaller.  Don't "restore" 57 — it
  -- encodes the bug.
  unless total == 59 do
    throwError s!"RTL structure: sponge register count = {total} (pinned 59). \
The sponge is the design that breaks when `runCircuitH` is restructured — \
run `lake exe keccak256-sponge-jit-test` and confirm the `empty`/`abc` \
digests before repinning."
  unless kfInst == 1 do
    throwError s!"RTL structure: sponge has {kfInst} wKeccakF instances (want 1)"
  unless rcInst == 2 do
    throwError s!"RTL structure: sponge has {rcInst} keccakRcHW ROM instances \
(want 2)."
  IO.println s!"[rtl-structure] sponge: regs={total}, wKeccakF={kfInst}, \
keccakRcHW={rcInst} (pinned)"

/-! ### Dead register banks, as a property rather than a pinned number

Every pin above is a specific number for a specific design, so each one only
catches a regression in that design.  This check is the general form of the
bug they were all circling: a register whose value can never reach an output.

Duplicated sub-engines show up exactly this way.  The second copy of
`dividerQ`'s register bank fed only a `packRegister` concat chain that nothing
read — the registers were live by use-count (they reference each other) but
dead by reachability.  A plain use-count cannot see that; a fixed point from
the outputs can.

Stated as a property over every design in this file, so a NEW design that
grows an unreachable bank fails here without anyone remembering to pin it. -/

/-- Registers in `body` that cannot reach any output port.

    This must be a REACHABILITY analysis, not a use-count.  A dead register
    bank is self-referential — each register's input mentions its siblings —
    so "is this name read anywhere" reports every one of them as live and
    misses the bug entirely.  (Checked: with the prune disabled, a use-count
    version of this function reports nothing while the pinned counts
    correctly jump 16 → 22.)

    So: start from the output ports, walk backwards through `assign` RHSs and
    register inputs to a fixed point, and report the registers never reached. -/
def unreachableRegisters (body : String) : List String := Id.run do
  let lines := body.splitOn "\n"
  -- name → the expression text that defines it (assign RHS or register input)
  let mut defOf : List (String × String) := []
  let mut regs : List String := []
  for l in lines do
    let t := l.trim
    if containsSubstr t "<=" then
      -- first `<=` only, same reason as the `assign` case below
      let lhs := ((t.splitOn "<=").head!).trim
      let rhs := match t.splitOn "<=" with
        | _ :: rest@(_ :: _) => (String.intercalate "<=" rest).trim
        | _ => ""
      -- the reset arm (`x <= 8'd0;`) carries no dependency, so it simply
      -- contributes no idents
      if lhs.startsWith "_tmp_" || lhs.startsWith "_gen_" then
        unless regs.contains lhs do regs := lhs :: regs
        unless (identsIn rhs).isEmpty do defOf := (lhs, rhs) :: defOf
    else if t.startsWith "assign " then
      let body' := String.mk (t.toList.drop 7)
      -- Split on the FIRST `=` only.  `getLast!` on `splitOn "="` breaks on
      -- any RHS containing `==`, `<=` or a second `=`, which silently drops
      -- the real dependencies and makes everything look reachable.
      match body'.splitOn "=" with
      | lhs :: rest@(_ :: _) =>
        defOf := (lhs.trim, (String.intercalate "=" rest).trim) :: defOf
      | _ => pure ()
  -- seeds: output ports, plus everything feeding an instance port (an
  -- instance connection is an observable side effect from this module's view)
  let mut work : List String := outputPorts body
  for l in lines do
    let t := l.trim
    if containsSubstr t "_tmp_inst_" then
      work := work ++ identsIn t
  -- fixed point
  let mut live : List String := []
  let mut fuel := lines.length * 8 + 256
  while fuel > 0 do
    match work with
    | [] => fuel := 0
    | w :: rest =>
      fuel := fuel - 1
      work := rest
      unless live.contains w do
        live := w :: live
        for (n, rhs) in defOf do
          if n == w then work := work ++ identsIn rhs
  return regs.filter (fun r => !live.contains r)

run_meta do
  for declName in [``divTop, ``tvkTop, ``biqTop, ``regDependentEngine,
                   ``Sparkle.IP.Crypto.Keccak256Sponge.keccak256SpongeHW] do
    let text ← designText declName
    for (mname, body) in splitModules text do
      let dead := unreachableRegisters body
      unless dead.isEmpty do
        throwError s!"RTL structure: {declName} module {mname} has \
{dead.length} register(s) that no output can reach: {dead}.\n\n\
A register bank that is live by use-count but dead by reachability is the \
signature of a DUPLICATED sub-engine — the extra copy drives only a \
`packRegister` concat chain nothing reads.  Phase 4.5 of \
`Sparkle/IR/Optimize.lean` prunes these; if they are back, either that pass \
regressed or the elaborator grew a new way to produce them."
  IO.println "[rtl-structure] no unreachable register banks in any pinned design"

/-! ### LSpec surface

The checks above already fail the build.  This suite re-exposes the two
cheap ones so `lake test` reports them by name alongside everything else. -/

def suite : TestSeq :=
  group "RTL structure lint" <|
    test "undeclaredWires flags a leaked wire"
      (undeclaredWires "module m (\n  input logic clk\n);\n  logic _tmp_a;\n  assign _tmp_a = _tmp_leaked;\nendmodule"
        == ["_tmp_leaked"]) $
    test "undeclaredWires accepts a well-formed body"
      ((undeclaredWires "module m (\n  input logic [7:0] _gen_x\n);\n  logic [7:0] _tmp_a;\n  assign _tmp_a = _gen_x;\nendmodule").isEmpty) $
    test "undeclaredWires ignores instance port labels"
      ((undeclaredWires "module m (\n  input logic clk\n);\n  logic _tmp_q;\n  child _tmp_inst_c (.clk(clk), .out(_tmp_q));\nendmodule").isEmpty) $
    test "countRegisters counts always_ff blocks"
      (countRegisters "always_ff @(posedge clk) begin end\nalways_ff @(posedge clk) begin end" == 2)

def main : IO UInt32 := do
  lspecIO (Std.HashMap.ofList [("all", [suite])]) []

/-- `IO Unit` wrapper for `Tests/AllTests.lean`. -/
def mainUnit : IO Unit := do
  let code ← main
  if code != 0 then IO.Process.exit 1

end Sparkle.Tests.Compiler.RtlStructureTest
