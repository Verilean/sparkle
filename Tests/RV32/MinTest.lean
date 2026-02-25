-- Test: does importing SoC.lean (our modified version) overflow?
import Examples.RV32.SoC

def main : IO Unit := do
  IO.println "SoC import OK"
