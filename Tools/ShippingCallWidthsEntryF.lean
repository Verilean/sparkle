import Tools.ShippingCallWidthsEntry
import Tools.ShippingReaderFuelShapeR5

/-! # `entryStrict_of_links` with the CANDIDATE wrapper's R5: `NIN` and `R5ok` disappear

BUILT on poc after fbb445d0 (run `h1`; integrator fixes in okO_run_inv and shapePost_decomp) (worker H, branch `par/r-12`; reviewer ruling 2026-10-16
"wrapper-level R5"). No `sorry`, no axiom, no `native_decide`. New
ALTERNATIVE lemmas next to the old ones in
`Tools/ShippingCallWidthsEntry.lean`; the old ones are not changed.

The old consumer `entryStrict_of_links` takes, besides the reflection links
`LinkP` / `LinkC` (results of the old `machineShape?`),

* `NIN : d.nIn = bs.length + d.shape.insts.length` for the peel `bs` — the
  generator's meta-level knowledge, no kernel statement gives it;
* `R5ok : d.r5Ok = true` — a `decide` on the reflected parent;

and needs them ONLY to obtain R5 for `ShapeDecomp.callBinder`.

`entryStrict_of_linksF` takes the links as results of the fuel CANDIDATE
wrapper `machineShapeF` (`LinkPF`, `LinkCF`). R5 then comes from the
candidate's own reader state (`machineShapeF_callBinder`,
`Tools/ShippingReaderFuelShapeR5.lean`), so **both `NIN` and `R5ok` are
gone**. Remaining: `ResC`, `hkid`, `hk`, `R1k` (unchanged), and the links.

`callWidthsStrict_of_linksF` is the whole condition the same way (drops
`NIN`, `R5ok`). `r5Ok_of_linkF` shows that, for a candidate-linked parent,
the data check `d.r5Ok` is IMPLIED by `NIN` (so it is not an independent
condition any more); `shapeR5Ok_of_linkF` gives the count at the peel with
no data at all.

SCOPE. These are statements about the CANDIDATE wrapper. They do NOT
discharge `NIN` / `R5ok` for the old compiler: for that, `LinkPF` must be
obtained from the old `LinkP` (O1/O2), which is not done here. -/
namespace Tools.ShippingCallWidthsEntryF
open Lean
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingCallWidthsStrict
open Tools.ShippingReaderResultKind Tools.ShippingInstSignature
open Tools.ShippingMachineShapeUnfold Tools.ShippingShapeDecomp
open Tools.ShippingCallWidthsDeclared Tools.ShippingR5Check
open Tools.ShippingCallWidthsEntry
open Tools.ShippingReaderFuelShapeR5
open Tools.ShippingReaderFuel (machineShapeF)

/-- **The child side, candidate link** (alternative to
`entryStrict_of_child`; same premises with `LinkC` replaced by `LinkCF`). -/
theorem entryStrict_of_childF {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    {k : Nat} {res : MixedGateBinder} {dC : DefinitionVal}
    {nC : Nat} {symC : Bool} {paramsC : List (String × Nat)} {senvC : StructEnv}
    {allowC : Bool} {sc : MachineShape}
    (LinkCF : machineShapeF nC symC paramsC (.defnInfo dC) senvC allowC = some (some sc))
    (ResC : machResultKind? dC.type = some res)
    (hkid : kidOuts k = sc.layout.outs)
    (PB : (d.shape.binders[nDecl + k]?).map (fun bn => kindTy bn.2) = some (machHWType res)) :
    entryStrict d nDecl kidOuts k = true := by
  obtain ⟨_, hout⟩ := machineShapeF_single_out LinkCF ResC
  exact entryStrict_of_single (hkid.trans hout) PB

/-- **One conjunct at the closing's `nDecl`, candidate links: NO `NIN`, NO
`R5ok`** (alternative to `entryStrict_of_links`). -/
theorem entryStrict_of_linksF {d : MachineData} {kidOuts : Nat → List OutField} {k : Nat}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {senvP : StructEnv} {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) senvP allowP = some (some d.shape))
    {res : MixedGateBinder} {dC : DefinitionVal}
    {nC : Nat} {symC : Bool} {paramsC : List (String × Nat)} {senvC : StructEnv}
    {allowC : Bool} {sc : MachineShape}
    (LinkCF : machineShapeF nC symC paramsC (.defnInfo dC) senvC allowC = some (some sc))
    (ResC : machResultKind? dC.type = some res)
    (hkid : kidOuts k = sc.layout.outs)
    (hk : k < d.shape.insts.length)
    (R1k : (d.shape.insts.map (·.2.2))[k]? = some res) :
    entryStrict d (closingNDecl d.shape) kidOuts k = true := by
  have hres : res ≠ .domain := machResultKind?_ne_domain _ res ResC
  -- R5 of the parent from the candidate's reader state: the binder at `nDecl + k`
  have hkind := (machineShapeF_callBinder LinkPF hk).trans R1k
  exact entryStrict_of_childF LinkCF ResC hkid (r1_of_kind hkind hres)

/-- **The whole condition, candidate links: NO `NIN`, NO `R5ok`**
(alternative to `callWidthsStrict_of_links`). -/
theorem callWidthsStrict_of_linksF {d : MachineData} {kidOuts : Nat → List OutField}
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
  callWidthsStrict_of_entries fun k hk =>
    entryStrict_of_linksF LinkPF LinkCF ResC (hkid k hk) hk
      (getElem?_of_forall_mem R1all (by rw [List.length_map]; exact hk))

/-- The binder-count check at the peel, for a candidate-linked shape (no
reflected data needed). -/
theorem shapeR5Ok_of_linkF {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)}
    {dP : DefinitionVal} {senvP : StructEnv} {allowP : Bool} {sp : MachineShape}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) senvP allowP = some (some sp)) :
    ∃ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs dP.value) = some (bs, e) ∧
      shapeR5Ok sp bs.length = true := by
  obtain ⟨bs, e, hpeel, hc⟩ := machineShapeF_binderCount LinkPF
  exact ⟨bs, e, hpeel, decide_eq_true hc⟩

/-- For a candidate-linked parent the data check `r5Ok` is implied by `NIN`
(it carries no information beyond `NIN`). -/
theorem r5Ok_of_linkF {d : MachineData} {nP : Nat} {symP : Bool}
    {paramsP : List (String × Nat)} {dP : DefinitionVal} {senvP : StructEnv} {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) senvP allowP = some (some d.shape))
    (NIN : ∀ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs dP.value) = some (bs, e) →
      d.nIn = bs.length + d.shape.insts.length) :
    d.r5Ok = true := by
  obtain ⟨bs, e, hpeel, hc⟩ := machineShapeF_binderCount LinkPF
  have hn := NIN bs e hpeel
  exact decide_eq_true (by omega)

end Tools.ShippingCallWidthsEntryF
