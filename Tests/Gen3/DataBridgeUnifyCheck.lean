import Tools.ShippingGen2ServedDataBridgeCopy
import Tools.ShippingGen2DataBridge
set_option autoImplicit false
-- NOT BUILT yet. One-off check, deleted together with the copy in the next commit (SERVED_FREEZE rev1 §4.4 step 1).

/-! # D2 unify check (scripts/gen2/SERVED_FREEZE.md rev1 §4.4 step 1)

Before `Tools/ShippingGen2ServedDataBridgeCopy.lean` is deleted, this file shows, at the S1 combined SHA, that each
copied declaration equals its `par/gen2-spec` source in `Tools/ShippingGen2DataBridge.lean`:
- the two definitions by `rfl` (as functions, at every `ι dom`);
- the statements of the two theorems (and of `OneOutNoMemRow_eq`) by kernel definitional equality of their types
  (`Meta.isDefEq` at default transparency, which unfolds the two namespaces' definitions; the definitions are equal by
  the `rfl`s above). -/
namespace Tests.Gen3.DataBridgeUnifyCheck
open Lean Meta

theorem noMemRowS_eq :
    @Tools.ShippingGen2ServedDataBridgeCopy.noMemRowS = @Tools.ShippingGen2DataBridge.noMemRowS := rfl

theorem oneOutNoMemRow_eq {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} :
    @Tools.ShippingGen2ServedDataBridgeCopy.OneOutNoMemRow ι dom = @Tools.ShippingGen2DataBridge.OneOutNoMemRow ι dom :=
  rfl

/-- The copy's statement and the source's statement are definitionally equal. -/
def sameType (a b : Name) : MetaM Unit := do
  let ta := (← getConstInfo a).type
  let tb := (← getConstInfo b).type
  unless (← isDefEq ta tb) do throwError "UNIFY MISMATCH {a} vs {b}"
  logInfo m!"UNIFY OK {a} = {b}"

run_meta do
  sameType ``Tools.ShippingGen2ServedDataBridgeCopy.OneOutNoMemRow_eq ``Tools.ShippingGen2DataBridge.OneOutNoMemRow_eq
  sameType ``Tools.ShippingGen2ServedDataBridgeCopy.hord_of_rowS ``Tools.ShippingGen2DataBridge.hord_of_rowS
  sameType ``Tools.ShippingGen2ServedDataBridgeCopy.hord_of_row ``Tools.ShippingGen2DataBridge.hord_of_row

end Tests.Gen3.DataBridgeUnifyCheck

#print axioms Tests.Gen3.DataBridgeUnifyCheck.noMemRowS_eq
#print axioms Tests.Gen3.DataBridgeUnifyCheck.oneOutNoMemRow_eq
