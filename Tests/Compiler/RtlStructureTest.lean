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
  -- 9 is correct; 27 is the current (buggy) value.  Accept either so the test
  -- documents the gap without blocking the build, but SHOUT when it changes.
  unless total == 27 || total == 9 do
    throwError s!"RTL structure: regDependentEngine registers = {total} \
(expected 27 = current double-walk duplication, or 9 = fixed)."
  if total == 9 then
    IO.println "[rtl-structure] regDependentEngine = 9 — DOUBLE BODY WALK FIXED, \
update the tvkTop pin too"
  else
    IO.println s!"[rtl-structure] regDependentEngine = {total} \
(3 FSM + 4×6 duplicated engine; 9 would be correct — see the tvkTop note)"

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
