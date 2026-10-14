import Sparkle
import Sparkle.Compiler.SimNames

/-! # `#sim` / `#writeDesign` output paths and generated names (finding J5)

Before: `#sim f` made its two files and its namespace from the LAST
component of the declaration name, sanitised. `A.f` and `B.f` (or `fé` and
`fè`) shared `.lake/build/gen/sim/f_jit.c`: in one environment the second
command failed AFTER it had replaced the first command's files; in two files
the replacement was silent.

Now (`Sparkle/Compiler/SimNames.lean`) both come from the qualified name.
What this file checks, all at elaboration time and without any external tool
(the C text is written, never compiled here):

1. `#guard` rows on the pure functions: file stems, namespaces, the bounded
   length, private names, the two paths of `#writeDesign`, the `sim!` stems.
2. The REAL command on `SimNamesTestA.snDup` and `SimNamesTestB.snDup` in ONE
   environment (before: an error): two paths, two namespaces, and after both
   ran each file still holds its own design.
3. The real command on `«snUé»` / `«snUè»`, which the old sanitiser mapped to
   one string.
4. The same command AGAIN on the same declaration in the same environment:
   the documented behaviour is an error ("already declared": the wrappers
   exist), files unchanged in content, current namespace as before.
5. `#writeDesign` with a C path that lacks `_cppsim.h`: two files, the JIT
   text where it was, the C text beside it.

Two FILES (two Lean processes) and the re-run in a FRESH environment are
rows of the driver `scripts/shipping-coverage/tagged_names_sim.sh`
(`simdup`, `simrerun`); a `private` top is its row `simcmd-privself`.

A failure throws. WRITTEN, NOT BUILT/RUN. -/

open Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Sparkle.Compiler.SimNames

namespace SimNamesTestA
def snDup (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))
end SimNamesTestA

namespace SimNamesTestB
def snDup (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 2#8 : Signal defaultDomain (BitVec 8))
end SimNamesTestB

def «snUé» (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 16#8 : Signal defaultDomain (BitVec 8))

def «snUè» (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  x + (Signal.pure 32#8 : Signal defaultDomain (BitVec 8))

namespace Tests.Compiler.SimNamesTest

/-! ### 1. The pure functions -/

-- same last component, two namespaces: two stems, two namespaces
#guard declFileKey `SimNamesTestA.snDup == "SimNamesTestA_snDup"
#guard declFileKey `SimNamesTestB.snDup == "SimNamesTestB_snDup"
#guard declNamespace `SimNamesTestA.snDup == "«SimNamesTestA».«snDup»"
#guard declNamespace `SimNamesTestB.snDup == "«SimNamesTestB».«snDup»"

-- a root-level plain name keeps the stem it had (`counter_jit.c`)
#guard declFileKey `counter == "counter"
#guard declNamespace `counter == "«counter»"

-- names the old sanitiser merged (`snU_`)
#guard declFileKey (Lean.Name.mkSimple "snUé") == "Sp$D$snU_233_"
#guard declFileKey (Lean.Name.mkSimple "snUè") == "Sp$D$snU_232_"
#guard declNamespace (Lean.Name.mkSimple "snUé") == "«snUé»"
#guard declNamespace (Lean.Name.mkSimple "snUè") == "«snUè»"

-- `a.b` / `a_b`, keyword, digit-initial
#guard declFileKey `a.b != declFileKey `a_b
#guard declNamespace `a.b != declNamespace `a_b
#guard declNamespace (Lean.Name.mkSimple "module") == "«module»"
#guard declNamespace (Lean.Name.mkSimple "1bad") == "«1bad»"

-- an uncut stem has no `-`
#guard !(declFileKey `SimNamesTestA.snDup).toList.contains '-'
#guard !(declFileKey (Lean.Name.mkSimple "snUé")).toList.contains '-'

-- private declarations: the namespace is the user-facing one, the stems of
-- two files differ, and the wrappers are generated private
#guard declNamespace (Lean.mkPrivateNameCore `Some.ModuleX `A.f) == "«A».«f»"
#guard declIsPrivate (Lean.mkPrivateNameCore `Some.ModuleX `A.f)
#guard !declIsPrivate `A.f
#guard declFileKey (Lean.mkPrivateNameCore `Some.ModuleX `A.f) !=
  declFileKey (Lean.mkPrivateNameCore `Some.ModuleY `A.f)
#guard declFileKey (Lean.mkPrivateNameCore `Some.ModuleX `A.f) != declFileKey `A.f
#guard withVisibility true "def load : IO Simulator := x" == "private def load : IO Simulator := x"
#guard withVisibility true "structure S where" == "private structure S where"
#guard withVisibility true "instance : C S where" == "private instance : C S where"
#guard withVisibility true "namespace «A».Sim" == "namespace «A».Sim"
#guard withVisibility false "def load : IO Simulator := x" == "def load : IO Simulator := x"

-- a name that cannot be written component by component: one quoted component
#guard declNamespace (Lean.Name.mkNum `a 3) ==
  "«" ++ Sparkle.IR.ModuleName.ofDecl (Lean.Name.mkNum `a 3) ++ "»"

/-- A name whose module name is longer than `maxKeyLength`. -/
def longName (last : String) : Lean.Name :=
  Lean.Name.mkStr
    ((List.replicate 30 "Abcdefghij").foldl Lean.Name.mkStr Lean.Name.anonymous) last

#guard (Sparkle.IR.ModuleName.ofDecl (longName "f")).length > maxKeyLength
#guard (declFileKey (longName "f")).length ≤ 150
#guard (declFileKey (longName "f")).toList.contains '-'
#guard declFileKey (longName "f") != declFileKey (longName "g")

-- `#writeDesign`: the two C paths always differ
#guard writeDesignPaths "d/x_cppsim.h" == ("d/x_cppsim.h", "d/x_jit.c")
#guard writeDesignPaths "d/x.c" == ("d/x.c_cppsim.h", "d/x.c")
#guard writeDesignPaths "d/x_jit.c" == ("d/x_jit.c_cppsim.h", "d/x_jit.c")

-- `sim!`: a stem with the hash of the C text; never a declaration's stem
#guard svFileKey "counter" "text A" != svFileKey "counter" "text B"
#guard svFileKey "counter" "text A" == svFileKey "counter" "text A"
#guard svFileKey "a$b" "t" != svFileKey "a_b" "t"
#guard (svFileKey "counter" "text A").toList.contains '-'
#guard svNamespace "counter" == "counter"
#guard svNamespace "a$b" == "«a$b»"
#guard svNamespace "a_b" == "a_b"

end Tests.Compiler.SimNamesTest

/-! ### 2, 3. The real command -/

#sim SimNamesTestA.snDup
#sim SimNamesTestB.snDup
#sim «snUé»
#sim «snUè»

/-! ### 5. `#writeDesign` with a C path that lacks `_cppsim.h` -/

#writeDesign SimNamesTestA.snDup
  ".lake/build/gen/simnames-test/wd.sv"
  ".lake/build/gen/simnames-test/wd.c"

namespace Tests.Compiler.SimNamesTest

def hasSub (s pat : String) : Bool := (s.splitOn pat).length > 1

open Lean Elab Command in
/-- Elaborate a command given as text. `true` if it threw or logged an error;
the messages it logged are dropped. -/
def cmdFails (text : String) : CommandElabM Bool := do
  let env ← getEnv
  match Parser.runParserCategory env `command text with
  | .error e => throwError "SIMNAMES: parse error in the test: {e}"
  | .ok stx =>
    let saved := (← get).messages
    modify fun st => { st with messages := {} }
    let threw ←
      try
        elabCommand stx
        pure false
      catch _ =>
        pure true
    let logged := (← get).messages.hasErrors
    modify fun st => { st with messages := saved }
    pure (threw || logged)

open Lean Elab Command in
run_cmd do
  let mut errs : Array String := #[]
  -- 2. two namespaces, one last component
  logInfo m!"SIMNAMES: START same last component, one environment"
  let pA := SimNamesTestA.snDup.Sim.jitCppPath
  let pB := SimNamesTestB.snDup.Sim.jitCppPath
  let vA := SimNamesTestA.snDup.Sim.svPath
  let vB := SimNamesTestB.snDup.Sim.svPath
  if pA == pB then errs := errs.push s!"one JIT path for both: {pA}"
  if vA == vB then errs := errs.push s!"one sv path for both: {vA}"
  let cA ← IO.FS.readFile pA
  let cB ← IO.FS.readFile pB
  let sA ← IO.FS.readFile vA
  let sB ← IO.FS.readFile vB
  if !(hasSub cA "SimNamesTestA_snDup") || hasSub cA "SimNamesTestB_snDup" then
    errs := errs.push s!"{pA} does not hold the design of SimNamesTestA.snDup"
  if !(hasSub cB "SimNamesTestB_snDup") || hasSub cB "SimNamesTestA_snDup" then
    errs := errs.push s!"{pB} does not hold the design of SimNamesTestB.snDup"
  if !(hasSub sA "module SimNamesTestA_snDup") || hasSub sA "SimNamesTestB_snDup" then
    errs := errs.push s!"{vA} does not hold the design of SimNamesTestA.snDup"
  if !(hasSub sB "module SimNamesTestB_snDup") || hasSub sB "SimNamesTestA_snDup" then
    errs := errs.push s!"{vB} does not hold the design of SimNamesTestB.snDup"
  if SimNamesTestA.snDup.Sim.topModuleName != "SimNamesTestA_snDup" then
    errs := errs.push "topModuleName of SimNamesTestA.snDup"
  logInfo m!"SIMNAMES: same last component: {pA} | {pB} | {vA} | {vB}"
  -- 3. names the old sanitiser merged
  logInfo m!"SIMNAMES: START non-ASCII last components"
  let pE := «snUé».Sim.jitCppPath
  let pG := «snUè».Sim.jitCppPath
  if pE == pG then errs := errs.push s!"one JIT path for snUé and snUè: {pE}"
  let cE ← IO.FS.readFile pE
  let cG ← IO.FS.readFile pG
  if !(hasSub cE "Sp$D$snU_233_") || hasSub cE "Sp$D$snU_232_" then
    errs := errs.push s!"{pE} does not hold the design of snUé"
  if !(hasSub cG "Sp$D$snU_232_") || hasSub cG "Sp$D$snU_233_" then
    errs := errs.push s!"{pG} does not hold the design of snUè"
  logInfo m!"SIMNAMES: non-ASCII: {pE} | {pG}"
  -- 4. the same command again, same environment
  logInfo m!"SIMNAMES: START the same command again in the same environment"
  let ns0 ← getCurrNamespace
  let failed ← cmdFails "#sim SimNamesTestA.snDup"
  let ns1 ← getCurrNamespace
  let cA2 ← IO.FS.readFile pA
  let sA2 ← IO.FS.readFile vA
  let cB2 ← IO.FS.readFile pB
  if !failed then
    errs := errs.push "the second #sim on one declaration in one environment did not report an error"
  if cA2 != cA then errs := errs.push s!"{pA} changed on the second run"
  if sA2 != sA then errs := errs.push s!"{vA} changed on the second run"
  if cB2 != cB then errs := errs.push s!"{pB} changed when the command ran on the other declaration"
  if ns1 != ns0 then errs := errs.push s!"current namespace {ns0} became {ns1} after the failed command"
  logInfo m!"SIMNAMES: second run: reported an error = {toString failed}; files unchanged = {toString (cA2 == cA && sA2 == sA)}; namespace kept = {toString (ns1 == ns0)}"
  -- 5. `#writeDesign` with a C path without `_cppsim.h`
  logInfo m!"SIMNAMES: START #writeDesign paths"
  let jitP := ".lake/build/gen/simnames-test/wd.c"
  let cP := ".lake/build/gen/simnames-test/wd.c_cppsim.h"
  let jitT ← IO.FS.readFile jitP
  let cT ← IO.FS.readFile cP
  if !(hasSub jitT "jit_vtable") then errs := errs.push s!"{jitP} is not the JIT text"
  if hasSub cT "jit_vtable" then errs := errs.push s!"{cP} is the JIT text, not the C text"
  if !(hasSub cT "SimNamesTestA_snDup") then errs := errs.push s!"{cP} is not the C text of the design"
  logInfo m!"SIMNAMES: #writeDesign: JIT text {jitT.length} characters at {jitP}, C text {cT.length} characters at {cP}"
  unless errs.isEmpty do throwError "SIMNAMES FAILED: {errs}"
  logInfo m!"SIMNAMES: two declarations with one last component, and two that the old sanitiser merged, have their own files and namespaces; a second run on one declaration is an error that changes no file; #writeDesign writes two C files"

end Tests.Compiler.SimNamesTest
