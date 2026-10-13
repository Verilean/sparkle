import Lean.Elab.Command
import Tests.Compiler.MixDeepOutermostTest
import Tools.ShippingNoRepeat

/-! # `noRepeat` on the transitions of the `mixDeep` family (a measurement)

WRITTEN, NOT BUILT (par/a-40). Target-only; not in `Tests.AllTests`. Nothing
here is a theorem about the compiler and nothing asserts: the file LOGS five
pairs of Booleans. It tells whether option 2 of
`docs/parallel/A-det-decision.md` (a side condition in place of a law about
the run-local translation cache) can cover the family at all.

## How the Booleans are obtained

NOT by compiled evaluation of reflected data (that crashed Lean's code
generator, par/a-36). The command `#norepeat_log "<tag>" <term>` elaborates
— in a scratch copy of the command state, restored afterwards —

    example : <term> = true  := by first | decide | decide +kernel
    example : <term> = false := by first | decide | decide +kernel

and logs which of the two the KERNEL accepted:

    NOREPEAT START <tag>
    NOREPEAT <tag> = true | false | UNDECIDED (neither `decide` went through)

`START` goes to standard error (flushed) before each attempt. `UNDECIDED`
means the kernel could not reduce the term (e.g. a definition that does not
unfold); it is not a verdict.

## PREDICTED (by reading the five sources and `machineShape?`; NOT observed)

| declaration | `noRepeat` | `noRepeatNonLit` | why |
|---|---|---|---|
| `rcH` | true | true | `mux (x == 0) 1 (x + x)`: five different nodes |
| `cnt` | true | true | one Bool field (`hit`) packed once; literals `7#8`, `1#8`, `1#1`, `0#1` once each |
| `midH` | true | true | its call's argument is a BitVec (`rs`): one Bool packing (`hit`) |
| `mid2` | **false** | true | TWO Bool fields are packed — the call's argument `en` (a `let` field) and the result `hit` — each as `mux b 1#1 0#1` (`machBoolBits`): the literals `1#1` and `0#1` occur twice |
| `mixDeep` | true | true | the three calls share ONE argument `let` (`machLetIndex` finds the equal value), the result is a BitVec: one Bool packing |

If `mid2` is `false` as predicted, option 2 as stated does not cover the
family: `Det mid2` is needed for `mixDeep` (`machineClosesAt_of_det`, with
`S = {mid2, midH, rcH, cnt}`), and a repeated literal is exactly a lookup
whose answer depends on what the translation cache's read returns.

The explicit pairs, should the command not elaborate (keep the polarity
that compiles; each line is a kernel `decide`):

    -- example : noRepeat rcH.gateTerm = true := by decide
    -- example : noRepeat rcH.gateTerm = false := by decide
    -- example : noRepeat cnt.machineData.packed = true := by decide
    -- example : noRepeat cnt.machineData.packed = false := by decide
    -- example : noRepeat midH.machineData.packed = true := by decide
    -- example : noRepeat midH.machineData.packed = false := by decide
    -- example : noRepeat (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).packed = true := by decide
    -- example : noRepeat (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).packed = false := by decide
    -- example : noRepeat (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).packed = true := by decide
    -- example : noRepeat (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).packed = false := by decide

(and the same ten with `noRepeatNonLit`). -/
namespace Tests.Compiler.NoRepeatFamilyTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Tests.Compiler.ShippingMachineDepthHTest
open Tools.ShippingNoRepeat

open Lean Elab Command in
/-- Elaborate `example : t = <b> := by decide` in a scratch copy of the
command state; `true` when it went through without an error. -/
def decidesTo (t : TSyntax `term) (b : Bool) : CommandElabM Bool := do
  let saved ← get
  modify fun s => { s with messages := {} }
  let stx ←
    if b then `(command| example : $t = true := by first | decide | decide +kernel)
    else `(command| example : $t = false := by first | decide | decide +kernel)
  let ok : Bool ←
    try
      elabCommand stx
      pure (!(← get).messages.hasErrors)
    catch _ => pure false
  set saved
  pure ok

open Lean Elab Command in
/-- Log which of `t = true`, `t = false` the kernel decides. -/
elab "#norepeat_log " tag:str t:term : command => do
  let name := tag.getString
  IO.eprintln s!"NOREPEAT START {name}"
  (← IO.getStderr).flush
  let verdict : String ←
    if ← decidesTo t true then pure "true"
    else if ← decidesTo t false then pure "false"
    else pure "UNDECIDED (neither `decide` went through)"
  IO.eprintln s!"NOREPEAT {name} = {verdict}"
  (← IO.getStderr).flush
  logInfo m!"NOREPEAT {name} = {verdict}"

-- the command on closed terms first: one `true`, one `false`
#norepeat_log "sanity (expected true)"
  (noRepeat (.binary .add (.bitsInput 8 0) (.bitsInput 8 0) :
    Tools.ShippingUnifiedSource.Term (.bits 8)))
#norepeat_log "sanity (expected false)"
  (noRepeat (.binary .add (.bitsLit 8 1) (.bitsLit 8 1) :
    Tools.ShippingUnifiedSource.Term (.bits 8)))

#norepeat_log "rcH noRepeat" (noRepeat rcH.gateTerm)
#norepeat_log "rcH noRepeatNonLit" (noRepeatNonLit rcH.gateTerm)
#norepeat_log "cnt noRepeat" (noRepeat cnt.machineData.packed)
#norepeat_log "cnt noRepeatNonLit" (noRepeatNonLit cnt.machineData.packed)
#norepeat_log "midH noRepeat" (noRepeat midH.machineData.packed)
#norepeat_log "midH noRepeatNonLit" (noRepeatNonLit midH.machineData.packed)
#norepeat_log "mid2 noRepeat"
  (noRepeat (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).packed)
#norepeat_log "mid2 noRepeatNonLit"
  (noRepeatNonLit (Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.machineData).packed)
#norepeat_log "mixDeep noRepeat"
  (noRepeat (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).packed)
#norepeat_log "mixDeep noRepeatNonLit"
  (noRepeatNonLit (Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep.machineData).packed)

end Tests.Compiler.NoRepeatFamilyTest
