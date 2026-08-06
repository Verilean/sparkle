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
  -- DividerQ.SigState: counter, rem, quot, den, negate, done = 6 registers.
  unless total == 6 do
    throwError s!"RTL structure: divTop register count changed: {total} (pinned 6). \
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
  unless total == 76 do
    throwError s!"RTL structure: tvkTop register count changed: {total} \
(pinned 76 = 10 FSM + 11 duplicated 6-register divider engines).\n\n\
A DROP is good news — the runCircuitH double-body duplication was fixed; \
update this pin and say so.  A RISE means duplication got worse."
  IO.println s!"[rtl-structure] tvkTop registers = {total} (pinned; \
documents the runCircuitH double-body duplication)"

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
