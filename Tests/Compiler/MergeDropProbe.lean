import Tests.Compiler.LeafDeadInitTest

/-! # PROBE (not in AllTests): does the register merge drop a NONZERO-init register?

For `tgtSt2` (Tools/ShippingLeafSat.lean) the case "merge accepted drops a register, optimizer rejected or
identity" matters. Candidates: two registers with the same reset value and the same next-value shape. Logs, per
candidate: registers of `drop raw` and of `b`, `b == drop raw`, `refineCheck (drop raw) b`, registers of
`o = checkedOptimize b`, `o == b`, `refineCheck b o`. -/

namespace Sparkle.Tests.Compiler.MergeDropProbe
open Lean Elab Command Meta Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- Two identical counters (reset 5), both read. -/
def twin5 (en : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (st : Signal defaultDomain (BitVec 8 × BitVec 8)) =>
    let a := Signal.fst st
    let c := Signal.snd st
    bundle2
      (Signal.register 5#8 (Signal.mux en (a + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) a))
      (Signal.register 5#8 (Signal.mux en (c + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))) c))
  (Signal.fst st) ^^^ (Signal.snd st)

/-- Two identical shift registers of the input (reset 9). -/
def twinIn9 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  let st := Signal.loop fun (_st : Signal defaultDomain (BitVec 8 × BitVec 8)) =>
    bundle2 (Signal.register 9#8 x) (Signal.register 9#8 x)
  (Signal.fst st) + (Signal.snd st)

def regsOf (m : Sparkle.IR.AST.Module) : List (String × Int) :=
  m.body.filterMap fun st => match st with
    | .register o _ _ _ iv => some (o, iv)
    | _ => none

def probe (tag : String) (n : Name) : TermElabM Unit := do
  try
    sparkleSynthDepth.set 0
    sparkleChildCache.set {}
    let (raw, _) ← synthesizeCombinationalCore n [] false
    sparkleSynthDepth.set 0
    sparkleChildCache.set {}
    let (b, _) ← synthesizeCombinational n
    let dr := Sparkle.IR.ZeroWidth.dropZeroWidthModule raw
    let o := Sparkle.IR.OptCheck.checkedOptimize b
    let md := Sparkle.IR.RegDedup.mergeDuplicates dr
    logInfo m!"MERGEDROP {tag} raw merge: mergeDuplicates regs {regsOf md}; refineCheck dr md: {Sparkle.IR.RefineCheck.refineCheck dr md}; printOk: {Sparkle.IR.PrintGuard.printOk md}"
    logInfo m!"MERGEDROP {tag}: drop raw regs {regsOf dr}; b regs {regsOf b}; b == drop raw: {b == dr}; refineCheck (drop raw) b: {Sparkle.IR.RefineCheck.refineCheck dr b}; o regs {regsOf o}; o == b: {o == b}; refineCheck b o: {Sparkle.IR.RefineCheck.refineCheck b o}"
  catch e => logInfo m!"MERGEDROP {tag} FAILED: {e.toMessageData}"
  finally
    sparkleSynthDepth.set 0
    sparkleChildCache.set {}

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  probe "twin5" ``twin5
  probe "twinIn9" ``twinIn9

end Sparkle.Tests.Compiler.MergeDropProbe
