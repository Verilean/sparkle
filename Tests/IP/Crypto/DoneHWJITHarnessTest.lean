/-
  Controls for `DoneHWJITHarness.doneErrors` on synthetic traces (no JIT): the
  clean trace must be accepted and every single defect the checker is meant to
  find (spurious / missing / double / early / late / wide `done`, `done` before
  the first start or after the last request, wrong value, value changing after
  `done`, latency differing between requests) must be rejected.
-/
import Tests.IP.Crypto.DoneHWJITHarness

namespace Sparkle.Tests.IP.Crypto.DoneHWJITHarnessTest

open Sparkle.Tests.IP.Crypto.DoneHW

def spec : Spec := { name := "synthetic", minLat := 3, maxLat := 8, fixedLatency := true }

/-- Ideal trace: requests at `starts`, done pulse at start + lat, outputs
    [value i] from `done` on until the next start (0 before the first). -/
def ideal (starts : Array Nat) (lat : Nat) (n : Nat) : Array Obs := Id.run do
  let mut tr : Array Obs := Array.replicate n { done := false, outs := #[0] }
  for i in [0:starts.size] do
    let hi := if i + 1 < starts.size then starts[i+1]! else n
    for c in [starts[i]! + lat:hi] do tr := tr.modify c fun o => { o with outs := #[i + 10] }
    tr := tr.modify (starts[i]! + lat) fun o => { o with done := true }
  return tr

def exps : Array (Option (Array Nat)) := #[some #[10], some #[11], some #[12]]

def main : IO Unit := do
  IO.println "=== DoneHWJITHarness — checker controls (synthetic traces) ==="
  let starts := #[6, 30, 52]
  let n := 80
  let good := ideal starts 5 n
  let errs := fun (t : Array Obs) => doneErrors spec t starts exps
  let mut ok := true
  ok := (← check "clean trace accepted" (errs good).isEmpty) && ok
  let other := (List.range 17).foldl (fun t i => t.modify (35 + i) fun o => { o with outs := #[99] }) good
  ok := (← check "request with expect = none is not compared"
    (doneErrors spec other starts #[some #[10], none, some #[12]]).isEmpty) && ok
  ok := (← check "second done pulse rejected" (!(errs (good.modify 40 fun o => { o with done := true })).isEmpty)) && ok
  ok := (← check "done 2 cycles wide rejected" (!(errs (good.modify 36 fun o => { o with done := true })).isEmpty)) && ok
  ok := (← check "missing done rejected" (!(errs (good.modify 35 fun o => { o with done := false })).isEmpty)) && ok
  ok := (← check "done before minLat rejected"
    (!(errs ((good.modify 35 fun o => { o with done := false }).modify 32 fun o => { o with done := true })).isEmpty)) && ok
  ok := (← check "done after maxLat rejected"
    (!(errs ((good.modify 35 fun o => { o with done := false }).modify 40 fun o => { o with done := true })).isEmpty)) && ok
  ok := (← check "done before the first start rejected" (!(errs (good.modify 2 fun o => { o with done := true })).isEmpty)) && ok
  ok := (← check "done after the last request rejected" (!(errs (good.modify 70 fun o => { o with done := true })).isEmpty)) && ok
  ok := (← check "wrong value at done rejected" (!(errs (good.modify 35 fun o => { o with outs := #[77] })).isEmpty)) && ok
  ok := (← check "value changing after done rejected" (!(errs (good.modify 45 fun o => { o with outs := #[0] })).isEmpty)) && ok
  ok := (← check "latency differing between requests rejected (fixedLatency)"
    (!(errs ((good.modify 57 fun o => { o with done := false }).modify 58 fun o => { o with done := true })).isEmpty)) && ok
  ok := (← check "differing latency accepted without fixedLatency"
    (doneErrors { spec with fixedLatency := false }
      ((good.modify 57 fun o => { o with done := false }).modify 58 fun o => { o with done := true }) starts exps).isEmpty) && ok
  ok := (← check "sticky done (wide) accepted only with maxWidth"
    ((doneErrors { spec with maxWidth := 4 } (good.modify 36 fun o => { o with done := true }) starts exps).isEmpty
      && !(errs (good.modify 36 fun o => { o with done := true })).isEmpty)) && ok
  if !ok then
    IO.println "\nFAIL"
    IO.Process.exit 1
  IO.println "\nALL PASS"

end Sparkle.Tests.IP.Crypto.DoneHWJITHarnessTest
