/-
  Tutorial Extended runner.

  Runs all 7 steps' demos and prints their outputs.

  Steps 1-4 cover module structure and named record I/O.
  Steps 5-7 cover LTL temporal-logic verification:
    Step 5: LTL basics — invariants, K-cycle preservation, induction.
    Step 6: bug-localization framework (multi-premise + contrapositive).
    Step 7: pointer to the production RV32 LTL proof catalog.
-/

import TutorialExtended.Step1_SimpleCounter
import TutorialExtended.Step2_MultipleOutputs
import TutorialExtended.Step3_ModuleComposition
import TutorialExtended.Step4_NamedObservability
import TutorialExtended.Step5_LTL_Basics
import TutorialExtended.Step6_LTL_BugLocalization
import TutorialExtended.Step7_LTL_RV32_Pointers

def main : IO UInt32 := do
  IO.println "═══════════════════════════════════════════════════════"
  IO.println "  Tutorial Extended — module composition + named I/O + LTL"
  IO.println "═══════════════════════════════════════════════════════"

  IO.println "\n── Step 1: simple counter ──"
  TutorialExtended.Step1.runDemo

  IO.println "\n── Step 2: multi-output (anon vs let-named vs record) ──"
  TutorialExtended.Step2.runDemo

  IO.println "\n── Step 3: 3-module composition with named record ──"
  TutorialExtended.Step3.runDemo

  IO.println "\n── Step 4: observability via let-binding / record ──"
  TutorialExtended.Step4.runDemo

  IO.println "\n── Step 5: LTL basics — saturating counter invariants ──"
  TutorialExtended.Step5.runDemo

  IO.println "\n── Step 6: LTL bug localization — write→hold→read ──"
  TutorialExtended.Step6.runDemo

  IO.println "\n── Step 7: RV32 LTL theorem catalog (pointers) ──"
  TutorialExtended.Step7.runDemo

  IO.println "\n═══════════════════════════════════════════════════════"
  IO.println "  All steps ran. See docs/Tutorial_Extended.md and"
  IO.println "  docs/Tutorial_LTL.md for the walkthrough."
  IO.println "═══════════════════════════════════════════════════════"
  return 0
