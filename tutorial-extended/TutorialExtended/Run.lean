/-
  Tutorial Extended runner.

  Runs all 4 steps' demos and prints their outputs.
-/

import TutorialExtended.Step1_SimpleCounter
import TutorialExtended.Step2_MultipleOutputs
import TutorialExtended.Step3_ModuleComposition
import TutorialExtended.Step4_NamedObservability

def main : IO UInt32 := do
  IO.println "═══════════════════════════════════════════════════════"
  IO.println "  Tutorial Extended — module composition + named I/O"
  IO.println "═══════════════════════════════════════════════════════"

  IO.println "\n── Step 1: simple counter ──"
  TutorialExtended.Step1.runDemo

  IO.println "\n── Step 2: multi-output (anon vs let-named vs record) ──"
  TutorialExtended.Step2.runDemo

  IO.println "\n── Step 3: 3-module composition with named record ──"
  TutorialExtended.Step3.runDemo

  IO.println "\n── Step 4: observability via let-binding / record ──"
  TutorialExtended.Step4.runDemo

  IO.println "\n═══════════════════════════════════════════════════════"
  IO.println "  All steps ran. See docs/Tutorial_Extended.md for the"
  IO.println "  walkthrough that explains each pattern."
  IO.println "═══════════════════════════════════════════════════════"
  return 0
