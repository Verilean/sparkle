import Tools.ShippingCallWidthsStructLink

/-! # Child-link obligations with EXISTENCE and UNIQUENESS of the selected output

WRITTEN, NOT BUILT (worker O-EXIST, branch `par/o-exist`, from poc b0183932).
No `sorry`, no new `axiom`, no `native_decide`. New file; nothing existing is
changed.

## Why (reviewer)

`ChildLinkStruct kidOuts k nm r` (`Tools/ShippingCallWidthsEntryFM.lean`) says
"every child output NAMED `nm` has width `(kindTy r).bitWidth`", and
`KidOutsOk` likewise only constrains outputs with the connected name. Both
hold VACUOUSLY when no output of the child is named `nm`. (The real closing
does not then connect nothing: `instStmtG` (MachineInstG.lean 37–38) rejects a
field with no output of that name, so `closeInstsG` returns none and the
machine route is refused — `docs/parallel/O-prod-result-audit.md`.) Matching
width alone is therefore not an interface guarantee on the proof side.

## The strengthened obligation

`SelOut outs nm w` := some output of `outs` is named `nm` and has width `w`,
AND the output names of `outs` are `Nodup`. Consequences (pure, proved):

* `SelOut.unique` — any two outputs named `nm` are EQUAL (so the selected
  output is unique among outputs named `nm`);
* `SelOut.selected` — `∃ o`, `o ∈ outs ∧ o.name = nm ∧ width w`, and every
  output named `nm` is that `o` (an explicit `∃!`);
* `SelOut.width` — every output named `nm` has width `w` (the old, vacuous
  form).

Instances:

* `ChildLinkStructEx kidOuts k nm r := SelOut (kidOuts k) nm (kindTy r).bitWidth`
  (structure-field entry);
* `ChildLinkOrdEx kidOuts k r := SelOut (kidOuts k) "out" (kindTy r).bitWidth`
  (ordinary entry: the child's one output `out`);
* `ChildLinkMemEx kidOuts k dw := SelOut (kidOuts k) "out" dw` (memory entry).

## Theorems

* `childLinkStruct_of_ex` — `ChildLinkStructEx → ChildLinkStruct` (so every
  existing theorem stated with `ChildLinkStruct` is a corollary);
  `kidOutsOk_of_structEx`;
* `childLinkStructEx_of_layout` — PURE: `kidOuts k = machOutFields W outs`,
  `(nm, r) ∈ outs`, `(outs.map (·.1)).Nodup`, `r ≠ .domain`;
* `childLinkStructEx_of_reader` — from the callee's reader result at `dE`; the
  `Nodup` of names is the wrapper's own `outsTest` (`machineShape?_outsTest`,
  `outsTest_facts`), PROVED, not assumed;
* `childLinkStructEx_of_origin`, `childLinkStructEx_real` — mirroring
  `childLinkStruct_of_origin` / `childLinkStruct_real` with the SAME premises;
* `childLinkOrdEx_of_single`, `childLinkOrdEx_of_ord` — ordinary entry, from
  `OrdOrigin` and `ChildLinkOrdD` (the premises of `kidOutsOk_of_ord`);
* `childLinkMemEx_of_outTys` — memory entry, from
  `ChildOutTys (kidOuts k) (memModule combo aw dw).1` alone (the premise of
  `childLinkMem_of_outTys`), using `memModule`'s definition (one output
  `out : bitVector dw`);
* `KindOblEx`, `kindObl_of_ex`, `callWidthsStrict_of_linksFMEx` — the mixed
  theorem with the strengthened per-entry obligation (corollary of
  `callWidthsStrict_of_linksFM`); `kindOblEx_of_real` discharges the
  structure conjunct from the real child and derives the ordinary/memory
  existence facts from the old obligations.

## Premises that remain (HONEST STATUS)

| premise | status |
|---|---|
| `StructResAt` (callee entry constant declares every field the parent reads) | OPEN, ASSUMED, EXPLICIT — the same obligation as in `ShippingCallWidthsStructLink`. This file is NOT general structure coverage: existence of the selected output rests on `StructResAt` exactly as the width fact did |
| `MachineDefines … c sc` (callee reflection boundary) | ASSUMED, unchanged |
| `RealChild` of the callee | as in `childLinkStruct_real` (discharged from a parent run by `machine_children_realA` upstream) |
| `kidOuts k = sc.layout.outs` | DEFINITIONAL for the real callee shapes |
| `StructOrigin` (parent side) | PROVED for the candidate (`machineShapeF_origin`) |
| names `Nodup` of the callee's outputs | PROVED (wrapper's `outsTest`) |
| ordinary: `OrdOrigin`, `ChildLinkOrdD` | as in `kidOutsOk_of_ord` (`ChildLinkOrdD` ASSUMED) |
| memory: `ChildOutTys (kidOuts k) (memModule combo aw dw).1` | as in `childLinkMem_of_outTys` (ASSUMED here) |

Note (Prod results): see the corrected note in `ShippingCallWidthsStructLink`
and `docs/parallel/O-prod-result-audit.md` — a pair OF Signals has `out_0`/`out_1`
on both sides; the strengthened obligation is what rules out the vacuous case
(no output named `nm`) in general, wherever `StructResAt` fails.

## Unsure spots (for the integrator)

See the `-- UNSURE` comments: `eq_of_mem_nodup_map` (auto-generalisation in
`induction`, `rw [← ha']`), `childLinkOrdEx_of_single` (`List.nodup_singleton`
against an unreduced `map`), `childLinkMemEx_of_outTys` (defeq unfolding of
`memModule`'s outputs; `rw [h.outputs, List.map_map]` possibly closing the
goal itself). -/
namespace Tools.ShippingCallWidthsStructExist
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv
open Tools.ShippingCallWidthsStrict Tools.ShippingCallWidthsDeclared Tools.ShippingCallWidthsEntry
open Tools.ShippingReaderResultKind
open Tools.ShippingReaderFuelShapeR5
open Tools.ShippingCallWidthsChildReal
open Tools.ShippingCallWidthsEntryFM
open Tools.ShippingCallWidthsStructLink
open Tools.ShippingMachineShapeUnfold (declOuts?)
open Tools.ShippingReaderOutNames (machineShape?_outsTest outsTest_facts machOutFields_names)
open Tools.ShippingReaderFuelProv (OrdOrigin StructOrigin)
open Tools.ShippingReaderFuel (machineShapeF)

/-! ## The selected output: existence + Nodup names -/

/-- **The selected output exists and is unique**: some output of `outs` is
named `nm` with width `w`, and the output names are `Nodup`. -/
def SelOut (outs : List OutField) (nm : String) (w : Nat) : Prop :=
  (∃ o ∈ outs, o.name = nm ∧ o.ty.bitWidth = w) ∧ (outs.map (·.name)).Nodup

/-- Two members of a list on which `f` is `Nodup` with equal `f`-images are
equal. -/
theorem eq_of_mem_nodup_map {α β : Type} {f : α → β} {l : List α} {a b : α}
    (hnd : (l.map f).Nodup) (ha : a ∈ l) (hb : b ∈ l) (hab : f a = f b) : a = b := by
  -- UNSURE: relies on `induction` reverting `hnd ha hb` (as `eq_of_mem_nodup_fst`)
  induction l with
  | nil => cases ha
  | cons p rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnot, hnd'⟩ := hnd
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · exact ha'.trans hb'.symm
    · have hm : f p ∈ rest.map f := by
        rw [← ha', hab]
        exact List.mem_map.mpr ⟨b, hb', rfl⟩
      exact (hnot hm).elim
    · have hm : f p ∈ rest.map f := by
        rw [← hb', ← hab]
        exact List.mem_map.mpr ⟨a, ha', rfl⟩
      exact (hnot hm).elim
    · exact ih hnd' ha' hb'

/-- **Uniqueness**: two outputs named `nm` are equal. -/
theorem SelOut.unique {outs : List OutField} {nm : String} {w : Nat} (h : SelOut outs nm w)
    {o1 o2 : OutField} (h1 : o1 ∈ outs) (h2 : o2 ∈ outs) (hn1 : o1.name = nm)
    (hn2 : o2.name = nm) : o1 = o2 :=
  eq_of_mem_nodup_map h.2 h1 h2 (hn1.trans hn2.symm)

/-- **Every output named `nm` has width `w`** (the old, vacuous-if-absent
form). -/
theorem SelOut.width {outs : List OutField} {nm : String} {w : Nat} (h : SelOut outs nm w) :
    ∀ o ∈ outs, o.name = nm → o.ty.bitWidth = w := by
  intro o ho hn
  obtain ⟨o', ho', hn', hw⟩ := h.1
  rw [h.unique ho ho' hn hn']
  exact hw

/-- **The selected output, as an explicit `∃!`**. -/
theorem SelOut.selected {outs : List OutField} {nm : String} {w : Nat} (h : SelOut outs nm w) :
    ∃ o, (o ∈ outs ∧ o.name = nm ∧ o.ty.bitWidth = w) ∧
      ∀ o', o' ∈ outs → o'.name = nm → o' = o := by
  obtain ⟨o, ho, hn, hw⟩ := h.1
  exact ⟨o, ⟨ho, hn, hw⟩, fun o' ho' hn' => h.unique ho' ho hn' hn⟩

/-- Building `SelOut` from a name witness, `Nodup` names and the width of
every output so named. -/
theorem selOut_of {outs : List OutField} {nm : String} {w : Nat}
    (hex : ∃ o ∈ outs, o.name = nm) (hnd : (outs.map (·.name)).Nodup)
    (hw : ∀ o ∈ outs, o.name = nm → o.ty.bitWidth = w) : SelOut outs nm w := by
  obtain ⟨o, ho, hn⟩ := hex
  exact ⟨⟨o, ho, hn, hw o ho hn⟩, hnd⟩

/-! ## Per-kind strengthened obligations -/

/-- **Structure-field entry**: the output named `nm` exists, is unique, and has
the width of the entry's kind. -/
def ChildLinkStructEx (kidOuts : Nat → List OutField) (k : Nat) (nm : String)
    (r : MixedGateBinder) : Prop :=
  SelOut (kidOuts k) nm (kindTy r).bitWidth

/-- **Ordinary entry**: the child's `out` exists, is unique, and has the width
of the entry's kind. -/
def ChildLinkOrdEx (kidOuts : Nat → List OutField) (k : Nat) (r : MixedGateBinder) : Prop :=
  SelOut (kidOuts k) "out" (kindTy r).bitWidth

/-- **Memory entry**: the child's `out` exists, is unique, and has width
`dw`. -/
def ChildLinkMemEx (kidOuts : Nat → List OutField) (k : Nat) (dw : Nat) : Prop :=
  SelOut (kidOuts k) "out" dw

/-- **The strengthened obligation implies the old one.** -/
theorem childLinkStruct_of_ex {kidOuts : Nat → List OutField} {k : Nat} {nm : String}
    {r : MixedGateBinder} (h : ChildLinkStructEx kidOuts k nm r) :
    ChildLinkStruct kidOuts k nm r :=
  SelOut.width h

theorem kidOutsOk_of_structEx {d : MachineData} {kidOuts : Nat → List OutField} {k : Nat}
    {nm : String} {r : MixedGateBinder} (hnm : d.shape.instFields[k]? = some nm)
    (h : ChildLinkStructEx kidOuts k nm r) : KidOutsOk d kidOuts k r :=
  kidOutsOk_of_struct hnm (childLinkStruct_of_ex h)

/-! ## Structure entry from the child's layout -/

/-- **`ChildLinkStructEx` from the child's layout** (pure). -/
theorem childLinkStructEx_of_layout {kidOuts : Nat → List OutField} {k W : Nat} {nm : String}
    {r : MixedGateBinder} {outs : List (String × MixedGateBinder)}
    (hkid : kidOuts k = machOutFields W outs) (hmem : (nm, r) ∈ outs)
    (hnd : (outs.map (·.1)).Nodup) (hr : r ≠ .domain) : ChildLinkStructEx kidOuts k nm r := by
  have C : ChildLinkStruct kidOuts k nm r :=
    childLinkStruct_of_layout hkid (fun k' hk' => eq_of_mem_nodup_fst hnd hk' hmem) hr
  have hnames : (kidOuts k).map (·.name) = outs.map (·.1) := by
    rw [hkid]
    exact machOutFields_names W outs
  refine selOut_of ?_ ?_ C
  · have hn : nm ∈ (kidOuts k).map (·.name) := by
      rw [hnames]
      exact List.mem_map.mpr ⟨(nm, r), hmem, rfl⟩
    obtain ⟨o, ho, hon⟩ := List.mem_map.mp hn
    exact ⟨o, ho, hon⟩
  · rw [hnames]
    exact hnd

/-- **`ChildLinkStructEx` from the callee's reader result** at the constant
`dE` its shape was read from; `Nodup` names from the wrapper's own test. -/
theorem childLinkStructEx_of_reader {kidOuts : Nat → List OutField} {k : Nat}
    {sym : Bool} {params : List (String × Nat)} {dE : DefinitionVal}
    {senvC : StructEnv} {allow : Bool} {sc : MachineShape} {nm : String} {r : MixedGateBinder}
    (hL : machineShape? sym params (.defnInfo dE) senvC allow = some sc)
    (hkid : kidOuts k = sc.layout.outs)
    (hmem : ∀ (ctor? : Option Name) (outs : List (String × MixedGateBinder)),
      declOuts? senvC dE.type = some (ctor?, outs) → (nm, r) ∈ outs)
    (hr : r ≠ .domain) : ChildLinkStructEx kidOuts k nm r := by
  obtain ⟨_, _, ctor?, outs, _, kinds, _, _, D⟩ := Tools.ShippingShapeDecomp.machineShape?_decomp hL
  obtain ⟨o, ho, ht⟩ := machineShape?_outsTest hL
  have he : o = (ctor?, outs) := Option.some.inj (ho.symm.trans D.outsEq)
  subst he
  obtain ⟨_, _, hnd⟩ := outsTest_facts (outs := outs) ht
  exact childLinkStructEx_of_layout (hkid.trans D.layoutOuts) (hmem ctor? outs D.outsEq) hnd hr

/-- **`ChildLinkStructEx` from the entry's structure origin** and the OPEN
link `StructRes`. -/
theorem childLinkStructEx_of_origin {kidOuts : Nat → List OutField} {k : Nat}
    {senvP : StructEnv} {c : Name} {r : MixedGateBinder} {nm : String}
    {sym : Bool} {params : List (String × Nat)} {dE : DefinitionVal}
    {senvC : StructEnv} {allow : Bool} {sc : MachineShape}
    (hS : StructOrigin senvP c r nm) (SR : StructRes senvP c senvC dE)
    (hL : machineShape? sym params (.defnInfo dE) senvC allow = some sc)
    (hkid : kidOuts k = sc.layout.outs) : ChildLinkStructEx kidOuts k nm r := by
  obtain ⟨kinds, ty, args, resTy, ctor, fields, i, h1, h2, h3, h4, h5⟩ := hS
  have hmemF : (nm, r) ∈ fields := List.mem_of_getElem? h5
  have hr : r ≠ .domain := ne_domain_of_any (p := (nm, r)) h4 hmemF
  exact childLinkStructEx_of_reader hL hkid
    (fun ctor? outs hd => SR kinds ty args resTy ctor fields h1 h2 h3 ctor? outs hd (nm, r) hmemF)
    hr

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`ChildLinkStructEx` for the child really compiled** (premises of
`childLinkStruct_real`; `StructResAt` OPEN). -/
theorem childLinkStructEx_real {kidOuts : Nat → List OutField} {k : Nat}
    {senvP : StructEnv} {c : Name} {r : MixedGateBinder} {nm : String}
    {sc : MachineShape} {y : Res}
    (entry : MachineDefines mctx mref cctx cref c sc)
    (SR : StructResAt mref cref senvP c) (hy : RealChild mref cref c y)
    (hS : StructOrigin senvP c r nm) (hkid : kidOuts k = sc.layout.outs) :
    ChildLinkStructEx kidOuts k nm r := by
  obtain ⟨mctx', cctx', w1, ci, w2, w5, envR, w6, dE, get, henv, hE, hshape⟩ :=
    entryLink_real entry hy
  exact childLinkStructEx_of_origin hS (SR mctx' cctx' w1 ci w2 w5 envR w6 dE get henv hE)
    hshape hkid

/-- `childLinkStruct_real` re-derived as a corollary. -/
theorem childLinkStruct_real_viaEx {kidOuts : Nat → List OutField} {k : Nat}
    {senvP : StructEnv} {c : Name} {r : MixedGateBinder} {nm : String}
    {sc : MachineShape} {y : Res}
    (entry : MachineDefines mctx mref cctx cref c sc)
    (SR : StructResAt mref cref senvP c) (hy : RealChild mref cref c y)
    (hS : StructOrigin senvP c r nm) (hkid : kidOuts k = sc.layout.outs) :
    ChildLinkStruct kidOuts k nm r :=
  childLinkStruct_of_ex (childLinkStructEx_real entry SR hy hS hkid)

/-! ## Ordinary entry -/

/-- A single `out` of a non-domain kind meets `ChildLinkOrdEx`. -/
theorem childLinkOrdEx_of_single {kidOuts : Nat → List OutField} {k W : Nat}
    {r : MixedGateBinder}
    (hout : kidOuts k = [{ name := "out", lo := W, width := machWidth r, ty := machHWType r }])
    (hr : r ≠ .domain) : ChildLinkOrdEx kidOuts k r := by
  refine ⟨⟨{ name := "out", lo := W, width := machWidth r, ty := machHWType r }, ?_, rfl, ?_⟩, ?_⟩
  · rw [hout]
    exact List.mem_singleton.mpr rfl
  · show (machHWType r).bitWidth = (kindTy r).bitWidth
    rw [kindTy_eq_machHWType hr]
  · rw [hout]
    -- UNSURE: `nodup_singleton` against the unreduced `map`
    first
      | exact List.nodup_singleton _
      | simp
      | decide

/-- **Ordinary entry from its origin and `ChildLinkOrdD`** (premises of
`kidOutsOk_of_ord`). -/
theorem childLinkOrdEx_of_ord {env : Environment} {kidOuts : Nat → List OutField}
    {k : Nat} {c : Name} {r : MixedGateBinder}
    (ho : OrdOrigin (structEnv env) c r) (C : ChildLinkOrdD env kidOuts k c) :
    ChildLinkOrdEx kidOuts k r := by
  obtain ⟨kinds, hi⟩ := ho
  obtain ⟨dC, _, _, _, _, _, sc, hfind, LinkCF, hkid⟩ := C
  have ResC : machResultKind? dC.type = some r := resC_of_declared hi hfind
  obtain ⟨_, hout⟩ := machineShapeF_single_out LinkCF ResC
  exact childLinkOrdEx_of_single (hkid.trans hout) (machResultKind?_ne_domain _ r ResC)

/-! ## Memory entry -/

/-- **The real memory child**: from `ChildOutTys (kidOuts k) (memModule …).1`
alone, `out` exists, is unique, and has width `dw` (`memModule`'s only output
is `out : bitVector dw`). -/
theorem childLinkMemEx_of_outTys {kidOuts : Nat → List OutField} {k : Nat} {combo : Bool}
    {aw dw : Nat}
    (h : Tools.ShippingChildIfaceTy.ChildOutTys (kidOuts k)
      (Sparkle.Compiler.MachMemory.memModule combo aw dw).1) :
    ChildLinkMemEx kidOuts k dw := by
  have hW : ChildLinkMem kidOuts k dw := childLinkMem_of_outTys h
  -- existence: `memModule`'s `out` port is the image of some child output
  have h0 : ({ name := "out", ty := .bitVector dw } : Port) ∈
      [({ name := "out", ty := .bitVector dw } : Port)] := List.mem_singleton.mpr rfl
  -- UNSURE: defeq unfolding of `memModule`'s outputs
  have h1 : ({ name := "out", ty := .bitVector dw } : Port) ∈
      (Sparkle.Compiler.MachMemory.memModule combo aw dw).1.outputs := h0
  rw [h.outputs] at h1
  obtain ⟨o, ho, hf⟩ := List.mem_map.mp h1
  have hn : o.name = "out" := congrArg Port.name hf
  -- names: the child's output names are `memModule`'s, i.e. `["out"]`
  have e : (kidOuts k).map (·.name) =
      ((Sparkle.Compiler.MachMemory.memModule combo aw dw).1.outputs).map (·.name) := by
    -- UNSURE: `rw` may close the goal by `rfl` itself
    rw [h.outputs, List.map_map]
    try rfl
  refine ⟨⟨o, ho, hn, hW o ho⟩, ?_⟩
  rw [e]
  first
    | exact List.nodup_singleton _
    | decide
    | simp [Sparkle.Compiler.MachMemory.memModule]

/-! ## The mixed theorem with the strengthened obligation -/

/-- **The strengthened obligation of entry `k` = `e`**: the old ordinary
premise (from which `ChildLinkOrdEx` is DERIVED, `childLinkOrdEx_of_ord`),
`ChildLinkStructEx` for structure origins, and for memory entries both
`ChildLinkMem` and `ChildLinkMemEx`. -/
def KindOblEx (env : Environment) (d : MachineData) (kidOuts : Nat → List OutField) (k : Nat)
    (e : Name × List Nat × MixedGateBinder) : Prop :=
  (OrdOrigin (structEnv env) e.1 e.2.2 → ChildLinkOrdD env kidOuts k e.1) ∧
  (∀ nm : String, StructOrigin (structEnv env) e.1 e.2.2 nm →
    d.shape.instFields[k]? = some nm → ChildLinkStructEx kidOuts k nm e.2.2) ∧
  (∀ (combo : Bool) (aw dw : Nat),
    e.1 = Sparkle.Compiler.MachMemory.memChildName combo aw dw →
    e.2.2 = MixedGateBinder.bits dw → ChildLinkMem kidOuts k dw ∧ ChildLinkMemEx kidOuts k dw)

theorem kindObl_of_ex {env : Environment} {d : MachineData} {kidOuts : Nat → List OutField}
    {k : Nat} {e : Name × List Nat × MixedGateBinder} (h : KindOblEx env d kidOuts k e) :
    KindObl env d kidOuts k e :=
  ⟨h.1, fun nm hS hn => childLinkStruct_of_ex (h.2.1 nm hS hn),
    fun combo aw dw h1 h2 => (h.2.2 combo aw dw h1 h2).1⟩

/-- The ordinary existence fact from `KindOblEx` (derived, not assumed). -/
theorem KindOblEx.ordEx {env : Environment} {d : MachineData} {kidOuts : Nat → List OutField}
    {k : Nat} {e : Name × List Nat × MixedGateBinder} (h : KindOblEx env d kidOuts k e)
    (ho : OrdOrigin (structEnv env) e.1 e.2.2) : ChildLinkOrdEx kidOuts k e.2.2 :=
  childLinkOrdEx_of_ord ho (h.1 ho)

/-- **MIXED call widths, strengthened obligations** (corollary of
`callWidthsStrict_of_linksFM`). -/
theorem callWidthsStrict_of_linksFMEx {env : Environment} {d : MachineData}
    {kidOuts : Nat → List OutField}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) (structEnv env) allowP =
      some (some d.shape))
    (C : ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder), d.shape.insts[k]? = some e →
      KindOblEx env d kidOuts k e) :
    callWidthsStrict d (closingNDecl d.shape) kidOuts = true :=
  callWidthsStrict_of_linksFM LinkPF fun k e he => kindObl_of_ex (C k e he)

/-- **`KindOblEx` for the real children**: the structure conjunct from the
callee's `MachineDefines` shape, `RealChild` and the OPEN `StructResAt`; the
memory conjunct from `ChildOutTys` of `memModule`; the ordinary conjunct as
before. -/
theorem kindOblEx_of_real {env : Environment} {d : MachineData}
    {kidOuts : Nat → List OutField} {k : Nat} {e : Name × List Nat × MixedGateBinder}
    (Ord : OrdOrigin (structEnv env) e.1 e.2.2 → ChildLinkOrdD env kidOuts k e.1)
    (Struct : (∃ nm : String, StructOrigin (structEnv env) e.1 e.2.2 nm) →
      ∃ (sc : MachineShape) (y : Res), kidOuts k = sc.layout.outs ∧
        MachineDefines mctx mref cctx cref e.1 sc ∧ RealChild mref cref e.1 y ∧
        StructResAt mref cref (structEnv env) e.1)
    (Mem : ∀ (combo : Bool) (aw dw : Nat),
      e.1 = Sparkle.Compiler.MachMemory.memChildName combo aw dw →
      e.2.2 = MixedGateBinder.bits dw →
      Tools.ShippingChildIfaceTy.ChildOutTys (kidOuts k)
        (Sparkle.Compiler.MachMemory.memModule combo aw dw).1) :
    KindOblEx env d kidOuts k e := by
  refine ⟨Ord, fun nm hS _ => ?_, fun combo aw dw h1 h2 => ?_⟩
  · obtain ⟨sc, y, hkid, entry, hy, SR⟩ := Struct ⟨nm, hS⟩
    exact childLinkStructEx_real entry SR hy hS hkid
  · have hT := Mem combo aw dw h1 h2
    exact ⟨childLinkMem_of_outTys hT, childLinkMemEx_of_outTys hT⟩

end Tools.ShippingCallWidthsStructExist
