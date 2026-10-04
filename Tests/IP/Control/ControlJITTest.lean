/-
  JIT (CSim) real-cycle co-sim for the control estimators — the native
  compiled-C path, complementing both the `Signal.val` co-sim in
  `ObserverTest.lean` and the hand-run iverilog checks documented there.

  Three backends now cross-check the same circuits against the same pure
  models:

      Signal.val   — Lean closure evaluation   (ObserverTest.cosim)
      CSim JIT     — synthesizeHierarchical → C → dlopen   (this file)
      iverilog     — the emitted Verilog      (documented in ObserverTest)

  A disagreement isolates the faulty layer immediately: val-vs-pure blames
  the evaluator, JIT-vs-pure blames CSim codegen, Verilog-vs-pure blames the
  Verilog backend.  The `extractWidth` miscompile was exactly a case where
  the third differed while the first two agreed.

  Fixtures (all deterministic):
    * dividerQ15_16 — the 20-case signed/zero/saturation sweep vs `divQref`,
      each division driven through the real 50-cycle handshake;
    * tvKalman — five full FSM samples vs `tvkStep` (the on-chip Riccati,
      divider engine included);
    * kalmanQ15_16 — 40 cycles vs `obsRun`;
    * both biquads — impulse response vs `IIRBiquadGen.run`, including the
      naive resonator's sustained limit cycle, in compiled C.
-/

import Sparkle
import Sparkle.Compiler.Elab
import IP.Control.Observer
import IP.Control.IIRBiquadGen

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.IP.Control.FixedPointGen
open Sparkle.IP.Control.DividerQ
open Sparkle.IP.Control.Observer
open Sparkle.IP.Control.IIRBiquadGen

namespace Sparkle.Tests.IP.Control.ControlJITTest

set_option maxRecDepth 100000
set_option maxHeartbeats 400000000

/-! ### Sim tops (each `#sim` generates a `<name>.Sim` namespace with
`load` / `step` / `read`).  Outputs are wrapped in `HasDomain` records so the
generated `SimOutput` has named fields. -/

structure DivOut (dom : DomainConfig) where
  result : Signal dom (BitVec 32)
  done : Signal dom Bool

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (DivOut dom) dom := ⟨⟩

def divSim (num den : Signal defaultDomain (BitVec 32)) (start : Signal defaultDomain Bool)
    : DivOut defaultDomain :=
  let e := dividerQ15_16 num den start
  { result := projN! e 2 0, done := projN! e 2 1 }

#sim divSim

structure X1Out (dom : DomainConfig) where
  x1 : Signal dom (BitVec 32)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (X1Out dom) dom := ⟨⟩

def tvkSim (y u : Signal defaultDomain (BitVec 32)) (tick : Signal defaultDomain Bool)
    : X1Out defaultDomain :=
  { x1 := tvKalman 32 16 y u tick }

#sim tvkSim

def kalmanSim (y u : Signal defaultDomain (BitVec 32)) : X1Out defaultDomain :=
  { x1 := kalmanQ15_16 y u }

#sim kalmanSim

structure BiqOut (dom : DomainConfig) where
  yStable : Signal dom (BitVec 32)
  yNaive : Signal dom (BitVec 32)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (BiqOut dom) dom := ⟨⟩

def biqSim (x : Signal defaultDomain (BitVec 32)) : BiqOut defaultDomain :=
  { yStable := stableQ15_16 x, yNaive := marginalQ15_16 x }

#sim biqSim

/-! ### Drivers -/

def qv (n d : Int) : BitVec 32 := q 32 16 n d

/-- Drive one full division through the JIT engine's handshake. -/
def runDivJIT (sim : divSim.Sim.Simulator) (num den : BitVec 32) : IO (BitVec 32) := do
  -- start pulse
  sim.step { _gen_num := num, _gen_den := den, _gen_start := 1#1 }
  let mut out ← sim.read
  let mut cyc := 0
  while out.done == 0#1 && cyc < 80 do
    sim.step { _gen_num := num, _gen_den := den, _gen_start := 0#1 }
    out ← sim.read
    cyc := cyc + 1
  pure out.result

def divCases : List (Int × Int) :=
  [(256, 256), (256, 128), (100, 300), (-256, 256), (256, -256), (-256, -256),
   (1, 3), (-1, 3), (1, -3), (5000, 7), (-5000, 7), (30000, 1), (-30000, 1),
   (0, 5), (7, 0), (-7, 0), (32767, 2), (-32767, 2), (1, 32767), (12345, -67),
   (65536, 196608), (-491520, 163840)]

def main : IO Unit := do
  IO.println "=== Control JIT co-sim (CSim native) ==="
  (← IO.getStdout).flush
  let mut ok := true

  -- 1) divider vs divQref, real handshake per case
  let dsim ← divSim.Sim.load
  let mut divBad := 0
  for (a, b) in divCases do
    let num := BitVec.ofInt 32 a
    let den := BitVec.ofInt 32 b
    let got ← runDivJIT dsim num den
    let ref := divQref 32 16 num den
    if got != ref then
      IO.println s!"  ✗ divider {a}/{b}: JIT {got.toInt} ≠ ref {ref.toInt}"
      divBad := divBad + 1
  dsim.destroy
  if divBad == 0 then
    IO.println s!"  ✓ divider: {divCases.length} cases match divQref through the 50-cycle handshake"
  else ok := false

  -- 2) tvKalman: five full samples vs tvkStep (y = 1.0 held, u = 0)
  let tsim ← tvkSim.Sim.load
  let mut pureTvk : TVK 32 := default
  let mut tvBad := 0
  for _k in [1:6] do
    -- tick cycle
    tsim.step { _gen_y := qv 1 1, _gen_u := 0#32, _gen_tick := 1#1 }
    -- FSM runs ~115 cycles; give it 130
    for _ in [0:130] do
      tsim.step { _gen_y := qv 1 1, _gen_u := 0#32, _gen_tick := 0#1 }
    let out ← tsim.read
    pureTvk := tvkStep 32 16 pureTvk (qv 1 1) 0#32
    if out.x1 != pureTvk.x1 then
      IO.println s!"  ✗ tvKalman sample: JIT {out.x1.toInt} ≠ pure {pureTvk.x1.toInt}"
      tvBad := tvBad + 1
  tsim.destroy
  if tvBad == 0 then
    IO.println "  ✓ tvKalman: 5 full FSM samples (divider engine incl.) match tvkStep bit-for-bit"
  else ok := false

  -- 3) fixed-gain Kalman observer, 40 cycles vs obsRun
  let ksim ← kalmanSim.Sim.load
  let ys := (List.range 40).map fun t => if t < 3 then (0#32 : BitVec 32) else qv 1 1
  let pureStates := obsRun 32 16 (kfK1 32 16) (kfK2 32 16) default (ys.map fun y => (y, 0#32))
  -- CSim read-after-step semantics: outputs are evaluated with the current
  -- inputs and the PRE-clock registers (the biquad section below confirms
  -- this — its combinational output aligns at index t).  So a registered
  -- output read after step t equals the pure state after t steps.
  let mut obsBad := 0
  for t in [0:40] do
    let y := ys[t]!
    ksim.step { _gen_y := y, _gen_u := 0#32 }
    let out ← ksim.read
    let expected :=
      if t == 0 then (0#32 : BitVec 32)
      else (pureStates[t-1]?).map (·.x1) |>.getD 0#32
    if out.x1 != expected then obsBad := obsBad + 1
  ksim.destroy
  if obsBad == 0 then
    IO.println "  ✓ kalman observer: 40 cycles match obsRun"
  else
    IO.println s!"  ✗ kalman observer: {obsBad}/40 cycle mismatches"
    ok := false

  -- 4) biquads: 41-sample impulse response vs the pure `run`, both filters.
  --    The naive resonator's limit cycle must appear in compiled C too.
  let bsim ← biqSim.Sim.load
  let impulse := (qv 1 1) :: List.replicate 40 (0#32)
  let refStable := run 32 16 (quantize 32 16 stableCoeffs) (limOf 32 16) ⟨0#32, 0#32⟩ impulse
  let refNaive := run 32 16 (quantize 32 16 marginalCoeffs) (limOf 32 16) ⟨0#32, 0#32⟩ impulse
  let mut bqBad := 0
  let mut idx := 0
  for x in impulse do
    bsim.step { _gen_x := x }
    let out ← bsim.read
    let es := refStable[idx]?.getD 0#32
    let en := refNaive[idx]?.getD 0#32
    if out.yStable != es || out.yNaive != en then bqBad := bqBad + 1
    idx := idx + 1
  bsim.destroy
  if bqBad == 0 then
    IO.println "  ✓ biquads: 41-cycle impulse responses (incl. the naive limit cycle) match run"
  else
    IO.println s!"  ✗ biquads: {bqBad}/41 cycle mismatches"
    ok := false

  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

/-- AllTests wrapper (this main is already `IO Unit` + exit-on-fail). -/
def mainUnit : IO Unit := main

end Sparkle.Tests.IP.Control.ControlJITTest
