import Tools.ShippingCallWidthsEntryFR1
import Tools.ShippingReaderFuelShapeProv

/-! # Candidate call widths for MIXED call entries (ordinary / structure field / memory)

BUILT as written: run `p2` exit 0 (poc 6f216c4e); axioms run `axp`: [propext, Classical.choice, Quot.sound] (worker S-PROV, branch par/s-prov, from poc 3a1938a3;
reviewer milestone 1). No `sorry`, no axiom, no `native_decide`. New
ALTERNATIVE theorems; nothing old changed.

SCOPE. CANDIDATE wrapper `machineShapeF` only; not counted for the old
compiler (O1/O2 outside).

## What `entryStrict` asks, exactly (`entryStrict_iff_kidOutsOk`)

For a parent linked by the candidate (`LinkPF`), the binder at the closing's
`nDecl + k` carries entry `k`'s kind `r` (`machineShapeF_callBinder`, no
premise). So conjunct `k` of `callWidthsStrict` is EQUIVALENT to

  `KidOutsOk d kidOuts k r`: every `o ∈ kidOuts k` either has a name other
  than the field `d.shape.instFields[k]? = some f` the closing connects, or
  has `o.ty.bitWidth = (kindTy r).bitWidth`.

## Per-kind obligations (selected by the entry's PROVEN origin,
`machineShapeF_origin`, `Tools/ShippingReaderFuelShapeProv.lean`)

* ordinary entry (`OrdOrigin`, `senv.inst c = some (kinds, r)`):
  `ChildLinkOrdD env kidOuts k c` — the declared constant of `c`, its
  candidate link, `kidOuts k` = its layout outputs (as `ChildLinkFD` minus
  `hcallee`/`hinst`, which the origin supplies). Then `kidOuts k` is the
  single `out` of type `machHWType r` (both closings fine).
* structure field entry (`StructOrigin … nm`, and the shape HAS the field
  list: `instFields[k]? = some nm`, proved): `ChildLinkStruct kidOuts k nm r` —
  every child output NAMED `nm` has width `(kindTy r).bitWidth` (outputs with
  other names are unconstrained). This is exactly `KidOutsOk` at that
  `instFields`. NOT derived here from the struct child's own candidate link
  (that needs the child's struct layout = `machOuts?` field list, open).
* memory entry (`MemOrigin`, `c = memChildName combo aw dw`, `r = .bits dw`):
  `ChildLinkMem kidOuts k dw` — every `o ∈ kidOuts k` has
  `o.ty.bitWidth = dw`. Discharged for the REAL memory child: any `kidOuts k`
  with `ChildOutTys (kidOuts k) (memModule combo aw dw).1` satisfies it
  (`childLinkMem_of_outTys`; `memModule`'s only output is `out : bitVector dw`).
  Needs no field list (the memory child has one output).

No kind is blocked by `entryStrict` as defined. Note (not a blocker): for an
ordinary entry the obligation does not depend on `instFields`; for a structure
entry `instFields[k]? = some nm` is NECESSARY (with `instFields = []` every
output of a multi-field child would have to have the field's width), and it is
PROVED by provenance (`instStruct` is set by the structure call).

## Theorems

* `entryStrict_of_kidOutsOk`, `kidOutsOk_of_entryStrict`, `entryStrict_iff_kidOutsOk`;
* `callWidthsStrict_of_kidOutsOk` — the whole condition from `KidOutsOk` per
  entry (any `senvP`);
* `callWidthsStrict_of_linksFM` — the MIXED theorem: parent `LinkPF` with
  `structEnv env`, per entry `KindObl` (the obligation of every origin the
  entry has). NO `MemR1`, NO `SigDisj`.
* `callWidthsStrict_of_linksFH_declared_viaFM` — the existing
  `callWidthsStrict_of_linksFH_declared` (all entries ordinary declared
  children), re-derived from the mixed theorem (same premises: `LinkPF`,
  `MemR1`, `ChildLinkFD` per entry). `MemR1` is used ONLY for a memory-named
  callee that ALSO has a one-Signal signature; `SigDisj` (proved) rules out
  a structure origin of an entry whose callee has an `inst` signature.

Premises of the mixed theorem: `LinkPF` (candidate link of the parent, read
with `structEnv env`) and, per entry index, `KindObl`. -/
namespace Tools.ShippingCallWidthsEntryFM
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
open Tools.ShippingCallWidthsEntryFR1
open Tools.ShippingReaderFuelShapeR5
open Tools.ShippingReaderFuelProv (OrdOrigin StructOrigin MemOrigin)
open Tools.ShippingReaderFuelShapeProv (OriginAt machineShapeF_origin)
open Tools.ShippingReaderFuelR1 (MemR1 sigDisj_structEnv)
open Tools.ShippingReaderFuel (machineShapeF)

/-! ## The exact per-entry obligation -/

/-- **What conjunct `k` asks of the child's outputs**, for an entry of kind `r`. -/
def KidOutsOk (d : MachineData) (kidOuts : Nat → List OutField) (k : Nat)
    (r : MixedGateBinder) : Prop :=
  ∀ o ∈ kidOuts k, (∃ f, d.shape.instFields[k]? = some f ∧ o.name ≠ f) ∨
    o.ty.bitWidth = (kindTy r).bitWidth

/-- The parent's binder at the closing's `nDecl + k` has the width of entry
`k`'s kind (candidate link; no premise). -/
theorem binderWidth_of_linkF {d : MachineData} {k : Nat}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {senvP : StructEnv} {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) senvP allowP = some (some d.shape))
    (hk : k < d.shape.insts.length) {r : MixedGateBinder}
    (hr : (d.shape.insts.map (·.2.2))[k]? = some r) :
    (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
      some (kindTy r).bitWidth := by
  have hkind : (d.shape.binders.map (·.2))[closingNDecl d.shape + k]? = some r :=
    (machineShapeF_callBinder LinkPF hk).trans hr
  rw [List.getElem?_map] at hkind
  cases hb : d.shape.binders[closingNDecl d.shape + k]? with
  | none =>
    rw [hb] at hkind
    first
      | cases hkind
      | (simp at hkind)
  | some bn =>
    rw [hb] at hkind
    have e : bn.2 = r := Option.some.inj hkind
    show some (kindTy bn.2).bitWidth = some (kindTy r).bitWidth
    rw [e]

/-- **`KidOutsOk` gives the conjunct.** -/
theorem entryStrict_of_kidOutsOk {d : MachineData} {kidOuts : Nat → List OutField} {k : Nat}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {senvP : StructEnv} {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) senvP allowP = some (some d.shape))
    (hk : k < d.shape.insts.length) {r : MixedGateBinder}
    (hr : (d.shape.insts.map (·.2.2))[k]? = some r) (H : KidOutsOk d kidOuts k r) :
    entryStrict d (closingNDecl d.shape) kidOuts k = true := by
  have hw := binderWidth_of_linkF LinkPF hk hr
  unfold entryStrict
  refine List.all_eq_true.mpr fun o ho => ?_
  try dsimp only
  rcases H o ho with ⟨f, hf, hne⟩ | hwo
  · have h1 : (d.shape.instFields[k]?).any (fun f => o.name != f) = true := by
      rw [hf]
      exact bne_iff_ne.mpr hne
    rw [Bool.or_eq_true]
    exact Or.inl h1
  · have hdec : decide ((d.shape.binders[closingNDecl d.shape + k]?).map
        (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth) = true := by
      rw [hwo]
      exact decide_eq_true hw
    rw [Bool.or_eq_true]
    exact Or.inr hdec

/-- **The conjunct gives `KidOutsOk`** (so `KidOutsOk` is the EXACT
obligation). -/
theorem kidOutsOk_of_entryStrict {d : MachineData} {kidOuts : Nat → List OutField} {k : Nat}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {senvP : StructEnv} {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) senvP allowP = some (some d.shape))
    (hk : k < d.shape.insts.length) {r : MixedGateBinder}
    (hr : (d.shape.insts.map (·.2.2))[k]? = some r)
    (h : entryStrict d (closingNDecl d.shape) kidOuts k = true) : KidOutsOk d kidOuts k r := by
  have hw := binderWidth_of_linkF LinkPF hk hr
  intro o ho
  unfold entryStrict at h
  have h2 : ((d.shape.instFields[k]?).any (fun f => o.name != f) ||
      decide ((d.shape.binders[closingNDecl d.shape + k]?).map
        (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth)) = true :=
    List.all_eq_true.mp h o ho
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · cases hf : d.shape.instFields[k]? with
    | none =>
      rw [hf] at h2
      exact absurd h2 Bool.false_ne_true
    | some f =>
      rw [hf] at h2
      have h3 : (o.name != f) = true := h2
      exact Or.inl ⟨f, rfl, bne_iff_ne.mp h3⟩
  · have h3 := of_decide_eq_true h2
    rw [hw] at h3
    exact Or.inr (Option.some.inj h3).symm

theorem entryStrict_iff_kidOutsOk {d : MachineData} {kidOuts : Nat → List OutField} {k : Nat}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {senvP : StructEnv} {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) senvP allowP = some (some d.shape))
    (hk : k < d.shape.insts.length) {r : MixedGateBinder}
    (hr : (d.shape.insts.map (·.2.2))[k]? = some r) :
    entryStrict d (closingNDecl d.shape) kidOuts k = true ↔ KidOutsOk d kidOuts k r :=
  ⟨kidOutsOk_of_entryStrict LinkPF hk hr, entryStrict_of_kidOutsOk LinkPF hk hr⟩

/-- Entry `k`'s kind, read off the entry. -/
theorem kind_of_entry {sp : MachineShape} {k : Nat} {e : Name × List Nat × MixedGateBinder}
    (he : sp.insts[k]? = some e) : (sp.insts.map (·.2.2))[k]? = some e.2.2 := by
  rw [List.getElem?_map, he]
  rfl

/-- **The whole condition from `KidOutsOk` per entry** (any `senvP`). -/
theorem callWidthsStrict_of_kidOutsOk {d : MachineData} {kidOuts : Nat → List OutField}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {senvP : StructEnv} {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) senvP allowP = some (some d.shape))
    (H : ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder), d.shape.insts[k]? = some e →
      KidOutsOk d kidOuts k e.2.2) :
    callWidthsStrict d (closingNDecl d.shape) kidOuts = true :=
  callWidthsStrict_of_entries fun k hk => by
    obtain ⟨e, he⟩ : ∃ e, d.shape.insts[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    exact entryStrict_of_kidOutsOk LinkPF hk (kind_of_entry he) (H k e he)

/-! ## Per-kind child links -/

/-- **Ordinary entry, declared child**: the constant `env` holds for the callee
`c`, its candidate link, and `kidOuts k` its layout outputs. -/
def ChildLinkOrdD (env : Environment) (kidOuts : Nat → List OutField) (k : Nat) (c : Name) :
    Prop :=
  ∃ (dC : DefinitionVal) (nC : Nat) (symC : Bool) (paramsC : List (String × Nat))
    (senvC : StructEnv) (allowC : Bool) (sc : MachineShape),
    env.find? c = some (.defnInfo dC) ∧
    machineShapeF nC symC paramsC (.defnInfo dC) senvC allowC = some (some sc) ∧
    kidOuts k = sc.layout.outs

/-- **Structure field entry**: every child output NAMED like the field has the
field kind's width. -/
def ChildLinkStruct (kidOuts : Nat → List OutField) (k : Nat) (nm : String)
    (r : MixedGateBinder) : Prop :=
  ∀ o ∈ kidOuts k, o.name = nm → o.ty.bitWidth = (kindTy r).bitWidth

/-- **Memory entry**: every child output has width `dw`. -/
def ChildLinkMem (kidOuts : Nat → List OutField) (k : Nat) (dw : Nat) : Prop :=
  ∀ o ∈ kidOuts k, o.ty.bitWidth = dw

/-- A single `out` of a non-domain kind `r` meets `KidOutsOk` (either closing). -/
theorem kidOutsOk_of_single {d : MachineData} {kidOuts : Nat → List OutField} {k W : Nat}
    {r : MixedGateBinder}
    (hout : kidOuts k = [{ name := "out", lo := W, width := machWidth r, ty := machHWType r }])
    (hr : r ≠ .domain) : KidOutsOk d kidOuts k r := by
  intro o ho
  rw [hout] at ho
  have e := List.mem_singleton.mp ho
  subst e
  refine Or.inr ?_
  show (machHWType r).bitWidth = (kindTy r).bitWidth
  rw [kindTy_eq_machHWType hr]

theorem kidOutsOk_of_ord {env : Environment} {d : MachineData} {kidOuts : Nat → List OutField}
    {k : Nat} {c : Name} {r : MixedGateBinder}
    (ho : OrdOrigin (structEnv env) c r) (C : ChildLinkOrdD env kidOuts k c) :
    KidOutsOk d kidOuts k r := by
  obtain ⟨kinds, hi⟩ := ho
  obtain ⟨dC, _, _, _, _, _, sc, hfind, LinkCF, hkid⟩ := C
  have ResC : machResultKind? dC.type = some r := resC_of_declared hi hfind
  obtain ⟨_, hout⟩ := machineShapeF_single_out LinkCF ResC
  exact kidOutsOk_of_single (hkid.trans hout) (machResultKind?_ne_domain _ r ResC)

theorem kidOutsOk_of_struct {d : MachineData} {kidOuts : Nat → List OutField} {k : Nat}
    {nm : String} {r : MixedGateBinder} (hnm : d.shape.instFields[k]? = some nm)
    (C : ChildLinkStruct kidOuts k nm r) : KidOutsOk d kidOuts k r := by
  intro o ho
  by_cases hn : o.name = nm
  · exact Or.inr (C o ho hn)
  · exact Or.inl ⟨nm, hnm, hn⟩

theorem kidOutsOk_of_mem {d : MachineData} {kidOuts : Nat → List OutField} {k dw : Nat}
    (C : ChildLinkMem kidOuts k dw) : KidOutsOk d kidOuts k (MixedGateBinder.bits dw) :=
  fun o ho => Or.inr (C o ho)

/-- **The real memory child meets `ChildLinkMem`**: `memModule`'s only output
is `out : bitVector dw`. -/
theorem childLinkMem_of_outTys {kidOuts : Nat → List OutField} {k : Nat} {combo : Bool}
    {aw dw : Nat}
    (h : Tools.ShippingChildIfaceTy.ChildOutTys (kidOuts k)
      (Sparkle.Compiler.MachMemory.memModule combo aw dw).1) :
    ChildLinkMem kidOuts k dw := by
  intro o ho
  have hm : ({ name := o.name, ty := o.ty } : Port) ∈
      (kidOuts k).map (fun o => ({ name := o.name, ty := o.ty } : Port)) :=
    List.mem_map.mpr ⟨o, ho, rfl⟩
  have hm2 : ({ name := o.name, ty := o.ty } : Port) ∈
      (Sparkle.Compiler.MachMemory.memModule combo aw dw).1.outputs := by
    rw [h.outputs]
    exact hm
  have hm' : ({ name := o.name, ty := o.ty } : Port) ∈
      [({ name := "out", ty := .bitVector dw } : Port)] := hm2
  have e := List.mem_singleton.mp hm'
  have ety : o.ty = .bitVector dw := congrArg Port.ty e
  rw [ety]
  try rfl

/-! ## The mixed theorem -/

/-- **The obligation of entry `k` = `e`, selected by its origin**: one
implication per origin (an entry has at least one, `machineShapeF_origin`). -/
def KindObl (env : Environment) (d : MachineData) (kidOuts : Nat → List OutField) (k : Nat)
    (e : Name × List Nat × MixedGateBinder) : Prop :=
  (OrdOrigin (structEnv env) e.1 e.2.2 → ChildLinkOrdD env kidOuts k e.1) ∧
  (∀ nm : String, StructOrigin (structEnv env) e.1 e.2.2 nm →
    d.shape.instFields[k]? = some nm → ChildLinkStruct kidOuts k nm e.2.2) ∧
  (∀ (combo : Bool) (aw dw : Nat),
    e.1 = Sparkle.Compiler.MachMemory.memChildName combo aw dw →
    e.2.2 = MixedGateBinder.bits dw → ChildLinkMem kidOuts k dw)

/-- One conjunct from the entry's origin and its obligation. -/
theorem kidOutsOk_of_origin {env : Environment} {d : MachineData}
    {kidOuts : Nat → List OutField} {k : Nat} {e : Name × List Nat × MixedGateBinder}
    (ho : OriginAt (structEnv env) e d.shape.instFields[k]?) (C : KindObl env d kidOuts k e) :
    KidOutsOk d kidOuts k e.2.2 := by
  rcases ho with ⟨ho, _⟩ | ⟨nm, ho, hnm⟩ | ⟨ho, _⟩
  · exact kidOutsOk_of_ord ho (C.1 ho)
  · exact kidOutsOk_of_struct hnm (C.2.1 nm ho hnm)
  · obtain ⟨combo, aw, dw, hc, hr, _, _⟩ := ho
    have hM := C.2.2 combo aw dw hc hr
    rw [hr]
    exact kidOutsOk_of_mem hM

/-- **MIXED call widths, candidate links**: ordinary, structure-field and
memory entries in one parent, each discharged by the obligation of its PROVEN
origin. No `MemR1`, no `SigDisj`, no `NIN`, no `R5ok`. -/
theorem callWidthsStrict_of_linksFM {env : Environment} {d : MachineData}
    {kidOuts : Nat → List OutField}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) (structEnv env) allowP =
      some (some d.shape))
    (C : ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder), d.shape.insts[k]? = some e →
      KindObl env d kidOuts k e) :
    callWidthsStrict d (closingNDecl d.shape) kidOuts = true :=
  callWidthsStrict_of_kidOutsOk LinkPF fun k e he =>
    kidOutsOk_of_origin (machineShapeF_origin LinkPF k e he) (C k e he)

/-! ## The existing all-ordinary theorem as a corollary -/

/-- `ChildLinkFD` at entry `k` = `e` gives `KindObl` (`MemR1` for a
memory-named callee with a one-Signal signature; `SigDisj` for structure
origins). -/
theorem kindObl_of_childLinkFD {env : Environment} {d : MachineData}
    {kidOuts : Nat → List OutField} {k : Nat} {e : Name × List Nat × MixedGateBinder}
    (hM : MemR1 (structEnv env)) (he : d.shape.insts[k]? = some e)
    (C : ChildLinkFD env d kidOuts k) : KindObl env d kidOuts k e := by
  obtain ⟨c, kinds, res, dC, nC, symC, paramsC, senvC, allowC, sc,
    hcallee, hinst, hfind, LinkCF, hkid⟩ := C
  have hc : c = e.1 := by
    rw [List.getElem?_map, he] at hcallee
    exact (Option.some.inj hcallee).symm
  subst hc
  refine ⟨fun _ => ⟨dC, nC, symC, paramsC, senvC, allowC, sc, hfind, LinkCF, hkid⟩, ?_, ?_⟩
  · intro nm hS
    obtain ⟨kS, ty, _, _, _, _, _, hS1, _⟩ := hS
    exact (sigDisj_structEnv env e.1 (kS, ty) (kinds, res) hS1 hinst).elim
  · intro combo aw dw hc _
    have hinst' : (structEnv env).inst (Sparkle.Compiler.MachMemory.memChildName combo aw dw) =
        some (kinds, res) := by
      rw [← hc]
      exact hinst
    have hres : res = MixedGateBinder.bits dw := hM combo aw dw kinds res hinst'
    have ResC : machResultKind? dC.type = some res := resC_of_declared hinst hfind
    obtain ⟨_, hout⟩ := machineShapeF_single_out LinkCF ResC
    intro o ho
    rw [hkid.trans hout] at ho
    have e1 := List.mem_singleton.mp ho
    subst e1
    show (machHWType res).bitWidth = dw
    rw [hres]
    try rfl

/-- **`callWidthsStrict_of_linksFH_declared`, re-derived from the mixed
theorem** (same premises). -/
theorem callWidthsStrict_of_linksFH_declared_viaFM {env : Environment} {d : MachineData}
    {kidOuts : Nat → List OutField}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) (structEnv env) allowP =
      some (some d.shape))
    (hM : MemR1 (structEnv env))
    (C : ∀ k, k < d.shape.insts.length → ChildLinkFD env d kidOuts k) :
    callWidthsStrict d (closingNDecl d.shape) kidOuts = true :=
  callWidthsStrict_of_linksFM LinkPF fun k e he =>
    kindObl_of_childLinkFD hM he (C k (by
      obtain ⟨hk, _⟩ := List.getElem?_eq_some_iff.mp he
      exact hk))

end Tools.ShippingCallWidthsEntryFM
