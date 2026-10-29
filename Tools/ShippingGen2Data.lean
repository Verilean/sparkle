import Tools.ShippingGen2Defs
import Tools.ShippingMachineClosesData
import Tools.ShippingCallsShape
set_option autoImplicit false

/-! # Gen2 U0: the concrete data condition `DataOkB` (GENERAL_SPEC.md §4.4)

A conjunction of Bool checks over a package's data, the rows of §4.4 that are functions of `p.d` and `p.kD` alone.
`DataOk p := DataOkB p = true` is what the `…Stmt`s are instantiated with. Each row is classified in the spec as E
(already a `GenFacts` field), or D (decidable only; generator `decide` per declaration; generic coverage G-DATA, part
of G3-GEN). Rows that need the served results' tables (MemCalleeData kid tables) are NOT here: they are facts of the
run (`ServedP`), supplied in M2-a. -/
namespace Tools.ShippingGen2

variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}

def DataOkB (p : SrcPkg ι dom) : Bool :=
  p.d.ok && p.d.letsAliasOk && p.d.callsOk p.kD &&
  decide (p.d.ss.length = p.d.shape.layout.slots.length) &&
  decide (∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width) &&
  decide (∀ o ∈ p.d.shape.layout.outs, o.name.toList.head? ≠ some 'i')

def DataOk (p : SrcPkg ι dom) : Prop := DataOkB p = true

end Tools.ShippingGen2
