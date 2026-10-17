import Tools.ShippingCallWidthsEntryF

/-! # `callWidthsStrict` with candidate links, HETEROGENEOUS children

UNVERIFIED: BUILT on poc a6573291 (runs `k1`, `k2`) (worker K, branch `par/r-15`, from poc
`20304f50`; reviewer 2026-10-17 item 2(a)). No `sorry`, no axiom, no
`native_decide`. New ALTERNATIVE theorem; `callWidthsStrict_of_linksF` and
`callWidthsStrict_of_links` are unchanged.

`callWidthsStrict_of_linksF` fixes ONE child (`dC`, its candidate link to ONE
shape `sc`, ONE result kind `res`) for every call entry. Here every call entry
`k` has its own child: its own declaration `dC`, its own candidate link
`machineShapeF nC … (.defnInfo dC) … = some (some sc)` (own fuel, own
signature table, own flags), its own result kind `res` (`ChildLinkF`).

Premises per entry `k < d.shape.insts.length` (inside `ChildLinkF`): the
child's candidate link, `ResC`, `hkid`, `R1k`. Parent: `LinkPF` only (no
`NIN`, no `R5ok` — those are discharged by the candidate's reader state,
`entryStrict_of_linksF`). See docs/parallel/R-reader-switch-boundary.md,
section "Call widths, heterogeneous children", for the premise table.

SCOPE. CANDIDATE wrapper only; not counted for the old compiler (O1/O2).

Predicted axioms: those of `entryStrict_of_linksF` (`propext`, possibly
`Quot.sound`). -/
namespace Tools.ShippingCallWidthsEntryFH
open Lean
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingCallWidthsStrict
open Tools.ShippingReaderResultKind Tools.ShippingInstSignature
open Tools.ShippingMachineShapeUnfold Tools.ShippingShapeDecomp
open Tools.ShippingCallWidthsDeclared Tools.ShippingR5Check
open Tools.ShippingCallWidthsEntry
open Tools.ShippingCallWidthsEntryF
open Tools.ShippingReaderFuel (machineShapeF)

/-- **The child of call entry `k`, candidate-linked**: some definition `dC`
whose candidate result is the shape `sc` the consumer's `kidOuts k` reads,
whose type has the one-Signal result kind `res`, and `res` is entry `k`'s
kind in the parent (`R1k`). -/
def ChildLinkF (d : MachineData) (kidOuts : Nat → List OutField) (k : Nat) : Prop :=
  ∃ (dC : DefinitionVal) (nC : Nat) (symC : Bool) (paramsC : List (String × Nat))
    (senvC : StructEnv) (allowC : Bool) (sc : MachineShape) (res : MixedGateBinder),
    machineShapeF nC symC paramsC (.defnInfo dC) senvC allowC = some (some sc) ∧
    machResultKind? dC.type = some res ∧
    kidOuts k = sc.layout.outs ∧
    (d.shape.insts.map (·.2.2))[k]? = some res

/-- One conjunct from the entry's own child. -/
theorem entryStrict_of_childLinkF {d : MachineData} {kidOuts : Nat → List OutField} {k : Nat}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {senvP : StructEnv} {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) senvP allowP = some (some d.shape))
    (hk : k < d.shape.insts.length) (C : ChildLinkF d kidOuts k) :
    entryStrict d (closingNDecl d.shape) kidOuts k = true := by
  obtain ⟨_, _, _, _, _, _, _, _, LinkCF, ResC, hkid, R1k⟩ := C
  exact entryStrict_of_linksF LinkPF LinkCF ResC hkid hk R1k

/-- **The whole condition, candidate links, a child PER call entry** (no
`NIN`, no `R5ok`; children, shapes and result kinds may differ between
entries). -/
theorem callWidthsStrict_of_linksFH {d : MachineData} {kidOuts : Nat → List OutField}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {senvP : StructEnv} {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) senvP allowP = some (some d.shape))
    (C : ∀ k, k < d.shape.insts.length → ChildLinkF d kidOuts k) :
    callWidthsStrict d (closingNDecl d.shape) kidOuts = true :=
  callWidthsStrict_of_entries fun k hk => entryStrict_of_childLinkF LinkPF hk (C k hk)

/-- The same with the children given as FUNCTIONS of the entry index. -/
theorem callWidthsStrict_of_linksFH' {d : MachineData} {kidOuts : Nat → List OutField}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {senvP : StructEnv} {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) senvP allowP = some (some d.shape))
    (dC : Nat → DefinitionVal) (nC : Nat → Nat) (symC : Nat → Bool)
    (paramsC : Nat → List (String × Nat)) (senvC : Nat → StructEnv) (allowC : Nat → Bool)
    (sc : Nat → MachineShape) (res : Nat → MixedGateBinder)
    (LinkCF : ∀ k, k < d.shape.insts.length →
      machineShapeF (nC k) (symC k) (paramsC k) (.defnInfo (dC k)) (senvC k) (allowC k) =
        some (some (sc k)))
    (ResC : ∀ k, k < d.shape.insts.length → machResultKind? (dC k).type = some (res k))
    (hkid : ∀ k, k < d.shape.insts.length → kidOuts k = (sc k).layout.outs)
    (R1k : ∀ k, k < d.shape.insts.length → (d.shape.insts.map (·.2.2))[k]? = some (res k)) :
    callWidthsStrict d (closingNDecl d.shape) kidOuts = true :=
  callWidthsStrict_of_linksFH LinkPF fun k hk =>
    ⟨dC k, nC k, symC k, paramsC k, senvC k, allowC k, sc k, res k,
      LinkCF k hk, ResC k hk, hkid k hk, R1k k hk⟩

/-- The homogeneous theorem is the special case (sanity check of the
generalisation). -/
theorem callWidthsStrict_of_linksF_via_FH {d : MachineData} {kidOuts : Nat → List OutField}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {senvP : StructEnv} {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) senvP allowP = some (some d.shape))
    {res : MixedGateBinder} {dC : DefinitionVal}
    {nC : Nat} {symC : Bool} {paramsC : List (String × Nat)} {senvC : StructEnv}
    {allowC : Bool} {sc : MachineShape}
    (LinkCF : machineShapeF nC symC paramsC (.defnInfo dC) senvC allowC = some (some sc))
    (ResC : machResultKind? dC.type = some res)
    (hkid : ∀ k, k < d.shape.insts.length → kidOuts k = sc.layout.outs)
    (R1all : ∀ kd ∈ d.shape.insts.map (·.2.2), kd = res) :
    callWidthsStrict d (closingNDecl d.shape) kidOuts = true :=
  callWidthsStrict_of_linksFH LinkPF fun k hk =>
    ⟨dC, nC, symC, paramsC, senvC, allowC, sc, res, LinkCF, ResC, hkid k hk,
      getElem?_of_forall_mem R1all (by rw [List.length_map]; exact hk)⟩

end Tools.ShippingCallWidthsEntryFH
