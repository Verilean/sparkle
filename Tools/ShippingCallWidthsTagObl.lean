import Tools.ShippingCallWidthsStructExist

/-! # Call widths with the obligation selected by the STORED origin tag

BUILT (integrator, 2026-10-19, origin-tag compiler; ig4 exit 0 after one fix: missing `open Tools.ShippingCallWidthsEntry`; axioms run axo standard).

`KindObl` (`Tools/ShippingCallWidthsEntryFM.lean`) asks, for every entry, the
obligation of EVERY origin whose facts match the entry (an entry under a memory
placeholder name with a one-Signal signature matches both the ordinary and the
memory arm). With the compiler's explicit tag (`MachineShape.instOrigins`,
`Sparkle.Compiler.MachInstOrigin`) the closing builds an entry's child from the
tag, so only the TAG's obligation is needed (`TagObl`):

| stored tag | obligation | gives |
|---|---|---|
| `.ord` | `ChildLinkOrdD` (callee's own candidate shape) | `KidOutsOk`, `out` exists, unique, width of the kind |
| `.field i` | `ChildLinkStructEx` at the shape's field name | `KidOutsOk`, that field exists, unique, width of the kind |
| `.mem combo aw dw` | `ChildOutTys (kidOuts k) (memModule combo aw dw).1` | `KidOutsOk`, `out` exists, unique, width `dw` |

The tag is read with `instOrigins[k]?` and exists for every entry of a
reader-produced shape (`machineShapeF_tag_exists`; lengths aligned,
`machineShapeF_instOrigins_length`): the `getD k .ord` default of
`MachineShape.instTagged` plays no part. The final theorem keeps the selected
output's existence and uniqueness in its CONCLUSION next to `callWidthsStrict`
(`callWidthsTag`).

Premises: the parent's candidate link `LinkPF`; per entry, the obligation of its
stored tag. For `.field`, `ChildLinkStructEx` is derived from the callee's real
layout by `childLinkStructEx_real`, which still assumes `StructResAt` (open;
`Tools/ShippingCallWidthsStructRes.lean` splits it). -/
namespace Tools.ShippingCallWidthsTagObl
open Lean
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingCallWidthsStrict Tools.ShippingCallWidthsEntry
open Tools.ShippingCallWidthsEntryFM
open Tools.ShippingCallWidthsStructExist
open Tools.ShippingReaderFuelProv (OrdOrigin StructOriginI MemOriginI)
open Tools.ShippingReaderFuelShapeProv (OriginTAt machineShapeF_originT machineShapeF_tag_exists)
open Tools.ShippingReaderFuel (machineShapeF)

/-- The obligation of entry `k` selected by its stored tag `o`. -/
def TagObl (env : Environment) (d : MachineData) (kidOuts : Nat → List OutField) (k : Nat)
    (e : Name × List Nat × MixedGateBinder) : Sparkle.Compiler.MachInstOrigin.InstOrigin → Prop
  | .ord => ChildLinkOrdD env kidOuts k e.1
  | .field _ => ∀ nm : String, d.shape.instFields[k]? = some nm →
      ChildLinkStructEx kidOuts k nm e.2.2
  | .mem combo aw dw => Tools.ShippingChildIfaceTy.ChildOutTys (kidOuts k)
      (Sparkle.Compiler.MachMemory.memModule combo aw dw).1

/-- The output name the closing connects for entry `k` with tag `o`: the
shape's field name for a structure field, `out` otherwise. -/
def SelName (d : MachineData) (k : Nat) : Sparkle.Compiler.MachInstOrigin.InstOrigin → String
  | .field _ => d.shape.instFields[k]?.getD "out"
  | _ => "out"

section
variable {env : Environment} {d : MachineData} {kidOuts : Nat → List OutField}
  {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal} {allowP : Bool}

/-- **One entry**: from its stored tag's facts and the tag's obligation, the
closing's width condition (`KidOutsOk`) AND the selected output exists, is
unique and has the entry kind's width. -/
theorem tagObl_entry {k : Nat} {e : Name × List Nat × MixedGateBinder}
    {o : Sparkle.Compiler.MachInstOrigin.InstOrigin}
    (hT : OriginTAt (structEnv env) e d.shape.instFields[k]? o) (C : TagObl env d kidOuts k e o) :
    KidOutsOk d kidOuts k e.2.2 ∧ SelOut (kidOuts k) (SelName d k o) (kindTy e.2.2).bitWidth := by
  cases o with
  | ord =>
    obtain ⟨hO, _⟩ := hT
    exact ⟨kidOutsOk_of_ord hO C, childLinkOrdEx_of_ord hO C⟩
  | field i =>
    obtain ⟨nm, _, hnm⟩ := hT
    have CS : ChildLinkStructEx kidOuts k nm e.2.2 := C nm hnm
    refine ⟨kidOutsOk_of_struct hnm (childLinkStruct_of_ex CS), ?_⟩
    show SelOut (kidOuts k) (d.shape.instFields[k]?.getD "out") (kindTy e.2.2).bitWidth
    rw [hnm]
    exact CS
  | mem combo aw dw =>
    obtain ⟨⟨_, hr, _, _⟩, _⟩ := hT
    have hw : (kindTy e.2.2).bitWidth = dw := by rw [hr]; rfl
    have C' : Tools.ShippingChildIfaceTy.ChildOutTys (kidOuts k)
        (Sparkle.Compiler.MachMemory.memModule combo aw dw).1 := C
    refine ⟨?_, ?_⟩
    · rw [hr]
      exact kidOutsOk_of_mem (childLinkMem_of_outTys C')
    · show SelOut (kidOuts k) "out" (kindTy e.2.2).bitWidth
      rw [hw]
      exact childLinkMemEx_of_outTys C'

/-- **Call widths with tag-selected obligations, existence and uniqueness kept
in the conclusion.** For a parent with a candidate link, if every entry meets
the obligation of ITS STORED tag, then the closing's width check passes, and
every entry has a tag (read directly, no default) whose selected output exists,
is unique and has the entry kind's width. -/
theorem callWidthsTag
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) (structEnv env) allowP =
      some (some d.shape))
    (C : ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder)
      (o : Sparkle.Compiler.MachInstOrigin.InstOrigin),
      d.shape.insts[k]? = some e → d.shape.instOrigins[k]? = some o → TagObl env d kidOuts k e o) :
    callWidthsStrict d (closingNDecl d.shape) kidOuts = true ∧
      ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder), d.shape.insts[k]? = some e →
        ∃ o, d.shape.instOrigins[k]? = some o ∧
          SelOut (kidOuts k) (SelName d k o) (kindTy e.2.2).bitWidth := by
  have H : ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder), d.shape.insts[k]? = some e →
      ∃ o, d.shape.instOrigins[k]? = some o ∧ KidOutsOk d kidOuts k e.2.2 ∧
        SelOut (kidOuts k) (SelName d k o) (kindTy e.2.2).bitWidth := by
    intro k e he
    obtain ⟨o, ho⟩ := machineShapeF_tag_exists LinkPF he
    exact ⟨o, ho, tagObl_entry (machineShapeF_originT LinkPF k e o he ho) (C k e o he ho)⟩
  refine ⟨callWidthsStrict_of_kidOutsOk LinkPF fun k e he => ?_, fun k e he => ?_⟩
  · obtain ⟨_, _, h, _⟩ := H k e he
    exact h
  · obtain ⟨o, ho, _, h⟩ := H k e he
    exact ⟨o, ho, h⟩

end

end Tools.ShippingCallWidthsTagObl
