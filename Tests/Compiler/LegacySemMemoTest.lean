import Tools.ShippingLegacySemMemoWalk
import Tools.ShippingMemoInv

/-! # The memo in the runtime boundary: the axiom audit

The theorems of `Tools/ShippingMemoLaws.lean`,
`Tools/ShippingLegacySemMemoWalk.lean` and `Tools/ShippingMemoInv.lean` are
stated under `RefLawsM` — a HYPOTHESIS (a structure of laws, never proved
against the runtime), not an axiom. This test checks the other half: none of
them depends on an axiom beyond the three standard ones. It THROWS otherwise.

It does not check, and nothing checks, that `RefLawsM` is satisfiable by the
real runtime. -/
namespace Sparkle.Tests.Compiler.LegacySemMemoTest
open Lean

-- The acceptance check: standard axioms only. This one THROWS.
run_cmd Lean.Elab.Command.liftTermElabM do
  let audited : List Name := [
    ``Tools.ShippingMemo.outer_reset_reaches,
    ``Tools.ShippingMemo.RefLawsM.setOther,
    ``Tools.ShippingMemo.RefLawsM.constInfoSame,
    ``Tools.ShippingMemo.RefLawsM.envSame,
    ``Tools.ShippingMemo.RefLawsM.read,
    ``Tools.ShippingMemo.get?_empty,
    ``Tools.ShippingMemo.ChildLawsM.toChildLaws,
    ``Tools.ShippingMemo.ChildBndM.toChildBnd,
    ``Tools.ShippingLegacySem.legacy_entry_walk_at,
    ``Tools.ShippingLegacySem.legacy_entry_walk_start,
    ``Tools.ShippingLegacySem.list_entry_outputDN_at,
    ``Tools.ShippingLegacySem.proj_entry_output_at,
    ``Tools.ShippingLegacySem.proj_entry_output_miss,
    ``Tools.ShippingLegacySem.outer_miss,
    ``Tools.ShippingLegacySem.entryConst_legacy_kept,
    ``Tools.ShippingLegacySem.entryConstIs_of_reads,
    ``Tools.ShippingLegacySem.proj_entry_output_outer,
    ``Tools.ShippingMemo.memoInv_of_empty,
    ``Tools.ShippingMemo.memoInv_same,
    ``Tools.ShippingMemo.memoInv_reset,
    ``Tools.ShippingMemo.memoInv_frame,
    ``Tools.ShippingMemo.memoInv_read,
    ``Tools.ShippingMemo.memoInv_hit,
    ``Tools.ShippingMemo.memoInv_write]
  for n in audited do
    let axs ← Lean.collectAxioms n
    if axs.any fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound) then
      throwError "{n} depends on a non-standard axiom: {axs}"
  logInfo m!"MEMO BOUNDARY, AXIOM AUDIT: {audited} depend on no axiom beyond propext, Classical.choice, Quot.sound (they are stated UNDER the hypothesis RefLawsM, which is not proved against the runtime)"

end Sparkle.Tests.Compiler.LegacySemMemoTest
