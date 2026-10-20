import Tests.Compiler.MixDeepOutermostTest
import Tools.ShippingEntryOkCommand

/-! # `#entry_ok` on the `mixDeep` family: the generated theorems against the hand-written ones

WRITTEN, NOT BUILT (par/a-41). Target-only; not in `Tests.AllTests`.

The sweep (never an error) over `rcH` (a gate leaf), `cnt` (a machine leaf),
`midH` (a parent of a gate leaf), `mid2` (a parent of a parent), and — one
step beyond the four — `mixDeep`:

    ENTRYOK ROW <f>: GENERATED (<kind>); <n> premises, all reflections; …
    ENTRYOK ROW <f>: <REFUSED|FAILED> (<kind>) — <why>
    ENTRYOK SUMMARY of 5: …

then the generated statements against the hand-written theorems, by
`isDefEq` (an ERROR when one differs — these four must reproduce):

    ENTRYOK SAME <generated> / <hand-written>: T

| generated | against |
|---|---|
| `rcH.entry_ok` | `rcH_expected` below: `(L) (K) : EntryDefines … rcH rcH.gateValue → EntryOk L rcH K` (the hand-written `CacheChainMidHTest.rcH_entryOk` still carries `EntryStill rcH` as a premise; its closed use is inline in `mid2_entryOk`) |
| `cnt.entry_ok` | `MixDeepOutermostTest.cnt_entryOk` |
| `midH.entry_ok` | `CacheChainClosedTest.midH_entryOk_closed` |
| `mid2.entry_ok` | `MixDeepOutermostTest.mid2_entryOk` |

## PREDICTED

`rcH`, `cnt`, `midH`, `mid2`: `GENERATED` with 1, 1, 2, 3 premises; the four
`SAME` lines `T`. `mixDeep`: NOT generated — `FAILED … no closing theorem`:
`EntryOk` of a machine parent goes through `CoreVia`, which needs the
declaration's closing at every invariant world, and `mixDeep` has only the
relative `closes_shared` (the open premise of its endpoint;
`docs/parallel/A-det-decision.md`). That row is the boundary of this unit,
shown on purpose.

Not certain, in order: the closing of `midH` / `mid2` (`apply f.closes_deep`
then the reflections by `exact`); the three `decide`s of `hout_of_data` at
`nDecl` read by the generator; `seqChild_of_real` on `cnt` (the text of the
hand proof); statement equality up to the ORDER of premises and of the key
set (the generator's order — callees in call-entry order, each followed by
its descendants — is the hand-written order for these four, by reading). -/
namespace Tests.Compiler.EntryOkFamilyTest
open Sparkle.Tests.Compiler.ShippingMachineSeqTest
open Sparkle.Tests.Compiler.ShippingMachineDepthHTest

#entry_ok_sweep Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH
#entry_ok_sweep Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt
#entry_ok_sweep Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH
#entry_ok_sweep Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2
#entry_ok_sweep Sparkle.Tests.Compiler.ShippingChildBoundaryTest.mixDeep

#entry_ok_summary

/-- The statement `rcH.entry_ok` must have. -/
def rcH_expected : Prop :=
  ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Tools.ShippingChildInv.RefLaws mref cref) (K : Lean.Name → Prop),
    Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref ``rcH rcH.gateValue →
    Tools.ShippingCacheCoherentCert.EntryOk L ``rcH K

#entry_ok_same Sparkle.Tests.Compiler.ShippingMachineDepthHTest.rcH.entry_ok
  Tests.Compiler.EntryOkFamilyTest.rcH_expected
#entry_ok_same Sparkle.Tests.Compiler.ShippingMachineSeqTest.cnt.entry_ok
  Tests.Compiler.MixDeepOutermostTest.cnt_entryOk
#entry_ok_same Sparkle.Tests.Compiler.ShippingMachineDepthHTest.midH.entry_ok
  Tests.Compiler.CacheChainClosedTest.midH_entryOk_closed
#entry_ok_same Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.entry_ok
  Tests.Compiler.MixDeepOutermostTest.mid2_entryOk

#print axioms Sparkle.Tests.Compiler.ShippingDesignSVTest.mid2.entry_ok

end Tests.Compiler.EntryOkFamilyTest
