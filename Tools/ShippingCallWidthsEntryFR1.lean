import Tools.ShippingCallWidthsEntryFH
import Tools.ShippingReaderFuelShapeR1

/-! # Heterogeneous candidate call widths with `R1k` DERIVED from the candidate reader

UNVERIFIED: BUILT on poc a6573291 (runs `k1`, `k2`) (worker K, branch `par/r-15`, from poc
`20304f50`; reviewer 2026-10-17 item 2(a)+(b)). No `sorry`, no axiom, no
`native_decide`. New ALTERNATIVE theorems; nothing old changed.

`Tools/ShippingCallWidthsEntryFH.lean` still assumes `R1k` per entry. Here it
is DERIVED (`machineShapeF_r1k`, `Tools/ShippingReaderFuelShapeR1.lean`) when
the parent was read by the candidate with the REAL signature table
`structEnv env`, from

* `hcallee` — entry `k`'s callee is `c` (`(insts.map (·.1))[k]? = some c`);
* `hinst` — `c` has the one-Signal signature `(kinds, res)` in `env`;
* `MemR1 (structEnv env)` — the ONE fact about the reader's call sites the
  candidate reader does not establish: the memory placeholder names
  `memChildName combo aw dw` carry no one-Signal signature with a result other
  than `.bits dw` in `env` (true when no `@[hardware_module]` declaration has
  such a name; `memR1_of_none`). `SigDisj` is PROVED for `structEnv env`.

Two forms:

* `callWidthsStrict_of_linksFH_sig` — `ResC` per entry still assumed (any
  constant `dC` the child's shape was read from, e.g. the unfolded entry
  constant; `ResC` for that is P5);
* `callWidthsStrict_of_linksFH_declared` — `ResC` from the DECLARED constant
  (`resC_of_declared`: `env.find? c = some (.defnInfo dC)`), the child linked
  at that declared constant.

SCOPE. CANDIDATE wrapper only; not counted for the old compiler (O1/O2).

Predicted axioms: `propext` (possibly `Quot.sound`, `Classical.choice` via
core list/array lemmas). -/
namespace Tools.ShippingCallWidthsEntryFR1
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
open Tools.ShippingCallWidthsEntryFH
open Tools.ShippingReaderFuelR1 (MemR1 sigDisj_structEnv)
open Tools.ShippingReaderFuelShapeR1 (machineShapeF_r1k)
open Tools.ShippingReaderFuel (machineShapeF)

/-- **`R1k` from the candidate**, for the entry whose callee is `c`. -/
theorem r1k_of_linkF {env : Environment} {d : MachineData} {k : Nat}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) (structEnv env) allowP =
      some (some d.shape))
    (hM : MemR1 (structEnv env)) {c : Name} {kinds : List MixedGateBinder}
    {res : MixedGateBinder}
    (hcallee : (d.shape.insts.map (·.1))[k]? = some c)
    (hinst : (structEnv env).inst c = some (kinds, res)) :
    (d.shape.insts.map (·.2.2))[k]? = some res :=
  machineShapeF_r1k hM (sigDisj_structEnv env) LinkPF hcallee hinst

/-- **The child of entry `k`, by its callee's signature**: `R1k` replaced by
`hcallee` + `hinst`. -/
def ChildLinkFS (env : Environment) (d : MachineData) (kidOuts : Nat → List OutField)
    (k : Nat) : Prop :=
  ∃ (c : Name) (kinds : List MixedGateBinder) (res : MixedGateBinder) (dC : DefinitionVal)
    (nC : Nat) (symC : Bool) (paramsC : List (String × Nat)) (senvC : StructEnv)
    (allowC : Bool) (sc : MachineShape),
    (d.shape.insts.map (·.1))[k]? = some c ∧
    (structEnv env).inst c = some (kinds, res) ∧
    machineShapeF nC symC paramsC (.defnInfo dC) senvC allowC = some (some sc) ∧
    machResultKind? dC.type = some res ∧
    kidOuts k = sc.layout.outs

/-- **The child of entry `k`, DECLARED constant**: `R1k` and `ResC` replaced
by `hcallee` + `hinst` + `hfind`. -/
def ChildLinkFD (env : Environment) (d : MachineData) (kidOuts : Nat → List OutField)
    (k : Nat) : Prop :=
  ∃ (c : Name) (kinds : List MixedGateBinder) (res : MixedGateBinder) (dC : DefinitionVal)
    (nC : Nat) (symC : Bool) (paramsC : List (String × Nat)) (senvC : StructEnv)
    (allowC : Bool) (sc : MachineShape),
    (d.shape.insts.map (·.1))[k]? = some c ∧
    (structEnv env).inst c = some (kinds, res) ∧
    env.find? c = some (.defnInfo dC) ∧
    machineShapeF nC symC paramsC (.defnInfo dC) senvC allowC = some (some sc) ∧
    kidOuts k = sc.layout.outs

theorem childLinkF_of_S {env : Environment} {d : MachineData} {kidOuts : Nat → List OutField}
    {k : Nat} {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) (structEnv env) allowP =
      some (some d.shape))
    (hM : MemR1 (structEnv env)) (C : ChildLinkFS env d kidOuts k) : ChildLinkF d kidOuts k := by
  obtain ⟨c, kinds, res, dC, nC, symC, paramsC, senvC, allowC, sc,
    hcallee, hinst, LinkCF, ResC, hkid⟩ := C
  exact ⟨dC, nC, symC, paramsC, senvC, allowC, sc, res, LinkCF, ResC, hkid,
    r1k_of_linkF LinkPF hM hcallee hinst⟩

theorem childLinkFS_of_D {env : Environment} {d : MachineData} {kidOuts : Nat → List OutField}
    {k : Nat} (C : ChildLinkFD env d kidOuts k) : ChildLinkFS env d kidOuts k := by
  obtain ⟨c, kinds, res, dC, nC, symC, paramsC, senvC, allowC, sc,
    hcallee, hinst, hfind, LinkCF, hkid⟩ := C
  exact ⟨c, kinds, res, dC, nC, symC, paramsC, senvC, allowC, sc, hcallee, hinst, LinkCF,
    resC_of_declared hinst hfind, hkid⟩

/-- **One conjunct, candidate links, `R1k` derived** (`ResC` assumed). -/
theorem entryStrict_of_linksF_sig {env : Environment} {d : MachineData}
    {kidOuts : Nat → List OutField} {k : Nat}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) (structEnv env) allowP =
      some (some d.shape))
    (hM : MemR1 (structEnv env)) (hk : k < d.shape.insts.length)
    (C : ChildLinkFS env d kidOuts k) :
    entryStrict d (closingNDecl d.shape) kidOuts k = true :=
  entryStrict_of_childLinkF LinkPF hk (childLinkF_of_S LinkPF hM C)

/-- **The whole condition, heterogeneous children, `R1k` derived from the
candidate reader** (`ResC` per entry assumed). -/
theorem callWidthsStrict_of_linksFH_sig {env : Environment} {d : MachineData}
    {kidOuts : Nat → List OutField}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) (structEnv env) allowP =
      some (some d.shape))
    (hM : MemR1 (structEnv env))
    (C : ∀ k, k < d.shape.insts.length → ChildLinkFS env d kidOuts k) :
    callWidthsStrict d (closingNDecl d.shape) kidOuts = true :=
  callWidthsStrict_of_linksFH LinkPF fun k hk => childLinkF_of_S LinkPF hM (C k hk)

/-- **The whole condition, heterogeneous DECLARED children: `R1k` and `ResC`
both derived** (`R1k` from the candidate reader, `ResC` from the declared
constant). -/
theorem callWidthsStrict_of_linksFH_declared {env : Environment} {d : MachineData}
    {kidOuts : Nat → List OutField}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) (structEnv env) allowP =
      some (some d.shape))
    (hM : MemR1 (structEnv env))
    (C : ∀ k, k < d.shape.insts.length → ChildLinkFD env d kidOuts k) :
    callWidthsStrict d (closingNDecl d.shape) kidOuts = true :=
  callWidthsStrict_of_linksFH_sig LinkPF hM fun k hk => childLinkFS_of_D (C k hk)

end Tools.ShippingCallWidthsEntryFR1
