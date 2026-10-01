/-
  `torus_grid%` — a periodic lattice of cells that read each other's
  registered outputs (`Sparkle/Core/Grid.lean`).

    1. Cross-check: a 2 × 3 lattice written with the macro equals the same
       lattice with its six cells and every neighbour slice written out by
       hand, cycle by cycle.  (2 × 3 so that rows and columns, north and
       south, east and west cannot be confused without the test noticing.)
    2. JIT == `Signal.val`, cycle by cycle.  This is a regression test for
       the C simulation backend: instances connected in a cycle were
       evaluated and clocked one after the other, so each cell saw some
       neighbours a cycle late — a ring of four cells diverged from
       `Signal.val` in its second cycle.
    3. Hierarchical Verilog and the GPU intra kernel are emitted (one cell
       module, six instances, direct cell-to-cell wires).
    4. Macro errors.
-/

import Sparkle
import Sparkle.Compiler.Elab

open Sparkle.Core.Domain
open Sparkle.Core.Signal
open Sparkle.Core.Sim

namespace Sparkle.Tests.TorusGridTest

structure MixOut (dom : DomainConfig) where
  a : Signal dom (BitVec 8)
  b : Signal dom (BitVec 8)

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (MixOut dom) dom := ⟨⟩

/-- A cell with two registers, each a different mix of neighbour fields
    (no symmetry between the directions, on purpose). -/
@[hardware_module] def mixCell {dom : DomainConfig}
    (n s w e nw : Signal dom (BitVec 8)) (seed : Signal dom (BitVec 8))
    (load : Signal dom Bool) : MixOut dom :=
  circuit do
    let ra ← Signal.reg 0#8
    let rb ← Signal.reg 0#8
    let aS := (ra : Signal dom (BitVec 8))
    let bS := (rb : Signal dom (BitVec 8))
    ra <~ Signal.mux load seed (n + w + w + bS)
    rb <~ Signal.mux load (seed + 1#8) (s - e + nw + nw + nw)
    return ({ a := aS, b := bS } : MixOut dom)

def seedOf (i j : Nat) : BitVec 8 := BitVec.ofNat 8 (i * 16 + j * 3 + 1)

/-- With the macro … -/
def mixGrid (load : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 96) :=
  torus_grid% 2 3
    (fields := a b) (width := 8)
    (cell i j nb => mixCell nb.n.a nb.s.b nb.w.a nb.e.b nb.nw.a (Signal.pure (seedOf i j)) load)

/-- Field `f` (0 = a, 1 = b) of cell `k` (= 3·i + j) of the packed state. -/
def fieldAt {n : Nat} (st : Signal defaultDomain (BitVec n)) (k f : Nat) :
    Signal defaultDomain (BitVec 8) :=
  st.map (BitVec.extractLsb' ((k * 2 + f) * 8) 8 ·)

/-- … and written out by hand.  Neighbours of cell (i, j) on the 2 × 3
    torus: north = south = the other row; west = column j−1, east = j+1. -/
def mixGridManual (load : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 96) :=
  Signal.loop fun st =>
    --                  n.a            s.b            w.a            e.b            nw.a
    let c00 := mixCell (fieldAt st 3 0) (fieldAt st 3 1) (fieldAt st 2 0) (fieldAt st 1 1) (fieldAt st 5 0)
      (Signal.pure (seedOf 0 0)) load
    let c01 := mixCell (fieldAt st 4 0) (fieldAt st 4 1) (fieldAt st 0 0) (fieldAt st 2 1) (fieldAt st 3 0)
      (Signal.pure (seedOf 0 1)) load
    let c02 := mixCell (fieldAt st 5 0) (fieldAt st 5 1) (fieldAt st 1 0) (fieldAt st 0 1) (fieldAt st 4 0)
      (Signal.pure (seedOf 0 2)) load
    let c10 := mixCell (fieldAt st 0 0) (fieldAt st 0 1) (fieldAt st 5 0) (fieldAt st 4 1) (fieldAt st 2 0)
      (Signal.pure (seedOf 1 0)) load
    let c11 := mixCell (fieldAt st 1 0) (fieldAt st 1 1) (fieldAt st 3 0) (fieldAt st 5 1) (fieldAt st 0 0)
      (Signal.pure (seedOf 1 1)) load
    let c12 := mixCell (fieldAt st 2 0) (fieldAt st 2 1) (fieldAt st 4 0) (fieldAt st 3 1) (fieldAt st 1 0)
      (Signal.pure (seedOf 1 2)) load
    c12.b ++ c12.a ++ c11.b ++ c11.a ++ c10.b ++ c10.a ++
      c02.b ++ c02.a ++ c01.b ++ c01.a ++ c00.b ++ c00.a

section SynthesisChecks
#synthesizeVerilogDesign mixGrid
#synthesizeVerilogDesign mixGridManual
#writeCudaIntraDesign mixGrid ".lake/build/gen/cuda/torus_mix.cu"
end SynthesisChecks

#sim mixGrid

/-! ### Macro errors -/

/-- error: torus_grid%: unknown direction 'up' (use n s w e nw ne sw se) -/
#guard_msgs in
example (load : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 96) :=
  torus_grid% 2 3
    (fields := a b) (width := 8)
    (cell i j nb => mixCell nb.up.a nb.s.b nb.w.a nb.e.b nb.nw.a (Signal.pure (seedOf i j)) load)

/-- error: torus_grid%: 'c' is not one of the fields [a, b] -/
#guard_msgs in
example (load : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 96) :=
  torus_grid% 2 3
    (fields := a b) (width := 8)
    (cell i j nb => mixCell nb.n.c nb.s.b nb.w.a nb.e.b nb.nw.a (Signal.pure (seedOf i j)) load)

/-- error: torus_grid%: write `nb.<direction>.<field>` (directions: n s w e nw ne sw se) -/
#guard_msgs in
example (load : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 96) :=
  torus_grid% 2 3
    (fields := a b) (width := 8)
    (cell i j nb => mixCell nb.n nb.s.b nb.w.a nb.e.b nb.nw.a (Signal.pure (seedOf i j)) load)

def check (label : String) (ok : Bool) (detail : String := "") : IO Bool := do
  if ok then IO.println s!"  PASS {label}" else IO.println s!"  FAIL {label} {detail}"
  return ok

def main : IO Unit := do
  IO.println "--- torus_grid% ---"
  let mut ok := true
  let load : Signal defaultDomain Bool := ⟨fun t => t == 0 || t == 9⟩
  let cycles := 16
  let viaMacro := (List.range cycles).map fun t => ((mixGrid load).val t).toNat
  let byHand := (List.range cycles).map fun t => ((mixGridManual load).val t).toNat
  ok := (← check s!"2×3 macro == hand-written ({cycles} cycles, reloaded at cycle 9)"
    (viaMacro == byHand) s!"macro {viaMacro.take 4} hand {byHand.take 4}") && ok
  -- the state really moves (cycles 1..9 all differ), and reloading at
  -- cycle 9 replays the same run
  let firstRun := (viaMacro.drop 1).take 9
  ok := (← check "the lattice evolves: 9 distinct states before the reload"
    (firstRun.eraseDups.length == 9 && !firstRun.contains 0)) && ok
  ok := (← check "reloading replays the run"
    (viaMacro.drop 10 == firstRun.take (cycles - 10))) && ok
  -- JIT: `read` after the k-th `step` is cycle k−1
  let sim ← mixGrid.Sim.load
  let mut jit : List Nat := []
  for t in [0:cycles] do
    Sim.step sim ({ _gen_load := if t == 0 || t == 9 then 1 else 0 } : mixGrid.Sim.SimInput)
    let o ← Sim.read sim
    jit := jit ++ [o.out.toNat]
  Sim.destroy sim
  ok := (← check s!"JIT == Signal.val, every cycle (instances connected in a cycle)"
    (jit == viaMacro) s!"jit {jit.take 4} val {viaMacro.take 4}") && ok
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.TorusGridTest
