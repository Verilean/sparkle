import Tools.ShippingCallWidthsEntryFM
import Tools.ShippingCallWidthsChildReal
import Tools.ShippingReaderOutNames

/-! # `ChildLinkStruct` from the structure child's own layout (reviewer milestone)

WRITTEN, NOT BUILT (worker S-STRUCT, branch `par/s-struct`, from poc
ed579dc4). No `sorry`, no axiom, no `native_decide`. New file; nothing
existing is changed.

## What this replaces

`Tools.ShippingCallWidthsEntryFM.ChildLinkStruct kidOuts k nm r` (every child
output NAMED `nm` has width `(kindTy r).bitWidth`) is an ASSUMED per-entry
premise of `callWidthsStrict_of_linksFM` for the structure-field entries
(`StructOrigin`). Here it is DERIVED from the child really compiled:

* the parent's entries of one structure call are pushed by `machInstanceS`
  (`Sparkle/Compiler/Elab.lean` 4079–4121) one per field of
  `machOuts? senv resTy = some (some ctor, fields)`, `resTy` the callee's
  `instS` type instantiated at the call's arguments; `StructOrigin` records
  exactly that (`fields[i]? = some (nm, r)`, no field of kind `.domain`);
* the callee's shape output layout is `machOutFields W outs` with
  `declOuts? senvC dE.type = some (ctor?, outs)` (`ShapeDecomp.layoutOuts`,
  `outsEq`, built), `dE` the ENTRY constant its run compiles
  (`link_of_defines`), and the wrapper's test makes the names of `outs`
  `Nodup` (`machineShape?_outsTest`, `outsTest_facts`, built);
* `machOutFields` writes, for each `(nm', k') ∈ outs`, a field named `nm'`
  of type `machHWType k'` (`machOutFields_mem`, here). With `(nm, r) ∈ outs`
  and the names `Nodup`, the ONE output named `nm` has kind `r`
  (`eq_of_mem_nodup_fst`), and `machHWType r` has the width of `kindTy r`
  since `r ≠ .domain` (`kindTy_eq_machHWType`).

The only link between the two sides that is not proved is `StructRes`: the
field list the PARENT read off the call's result type is contained in the
output list the CALLEE's entry constant declares.

## Theorems

* `machOutFields_mem`, `eq_of_mem_nodup_fst`, `ne_domain_of_any` (pure);
* `childLinkStruct_of_layout` — pure: `kidOuts k = machOutFields W outs`,
  `FieldsAgree outs nm r`, `r ≠ .domain` ⟹ `ChildLinkStruct kidOuts k nm r`;
* `fieldsAgree_of_reader` — `FieldsAgree` from the reader result and
  `(nm, r) ∈ outs` (Nodup from the wrapper's own test);
* `childLinkStruct_of_reader` — from the callee's reader result at `dE`;
* `childLinkStruct_of_origin` — from `StructOrigin senvP c r nm` (parent side,
  PROVED by `machineShapeF_origin` for the candidate) and `StructRes`;
* `childLinkStruct_real` — `kidOuts k` the layout of the shape
  `MachineDefines` pins for the callee, any `RealChild` of the callee, and
  the run-level `StructResAt`;
* `kindObl_struct_real` — the structure conjunct of `KindObl`;
* `callWidthsStrict_of_linksFMS` — the MIXED theorem with the structure
  conjunct DISCHARGED: ordinary and memory obligations as in
  `callWidthsStrict_of_linksFM`, structure entries from the real child.

## Remaining premises (of `callWidthsStrict_of_linksFMS`)

| premise | status |
|---|---|
| `LinkPF` (candidate link of the parent, `structEnv env`) | as in `callWidthsStrict_of_linksFM` |
| `hreal : ChildrenReal` (the children the closing consumes) | DISCHARGED from one parent run by `machine_children_realA` (as in `parent_children_widths_real`) |
| `Ord` (ordinary entries: `ChildLinkOrdD`) | ASSUMED, unchanged from `KindObl` |
| `Mem` (memory entries: `ChildLinkMem`) | ASSUMED, unchanged; discharged for the real memory child by `childLinkMem_of_outTys` |
| structure entries: `kidOuts k = sc.layout.outs` | DEFINITIONAL when `kidOuts` is taken as the real callee shapes (as in `callWidthsStrict_real`) |
| structure entries: `MachineDefines … e.1 sc` | ASSUMED — the existing reflection boundary of the callee |
| structure entries: `memChild? e.1 = none` | ASSUMED — decidable (a function of the name) |
| structure entries: `StructResAt` (`StructRes` at the entry constant of every callee run) | ASSUMED, EXPLICIT. Field lists are `senv.fields s` of the result type's head constant `s` (`machOuts?`), so it holds when (i) the call's instantiated result type and the callee entry constant's type have the same head structure (type preservation through `instRes`, and through `userInliner` on the unfolding branch of `entryConst` — the same gap as `P5At`), (ii) `machTupleKinds? dE.type = none`, (iii) the parent's and the callee run's `structEnv` agree on `fields s`. None of (i)–(iii) is proved here |
| `ResDeclAt` / `P5At` | NOT NEEDED for structure entries (they are about one-Signal result kinds) |

Note (Prod results): `machOuts?` reads a pair of Signals as `(some Prod.mk,
[out_0, out_1])`, while the callee's `declOuts?` reads a TUPLE result as one
packed `out` (`machTupleKinds?` first). For such a callee `StructRes` FAILS,
but `ChildLinkStruct` holds vacuously (no output named `out_0`); the closing
then connects no port for that entry — outside this file's scope.

## Unsure spots (for the integrator)

`eq_of_mem_nodup_fst` (`induction` auto-generalising `hnd ha hb`;
`List.nodup_cons`), `ne_domain_of_any` (the closing `beq` alternatives),
`childLinkStruct_of_layout` (`rw [← e1]` rewriting `nm`), the `rw [hke] at`
steps in `callWidthsStrict_of_linksFMS`. -/
namespace Tools.ShippingCallWidthsStructLink
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv
open Tools.ShippingCallWidthsStrict Tools.ShippingCallWidthsDeclared Tools.ShippingCallWidthsEntry
open Tools.ShippingCallWidthsChildReal
open Tools.ShippingCallWidthsEntryFM
open Tools.ShippingMachineShapeUnfold (declOuts?)
open Tools.ShippingReaderOutNames (machineShape?_outsTest outsTest_facts)
open Tools.ShippingReaderFuelProv (OrdOrigin StructOrigin)
open Tools.ShippingReaderFuel (machineShapeF)

/-! ## Pure facts -/

/-- Every field `machOutFields` writes comes from an entry of the list: its
name, and the hardware type of its kind. -/
theorem machOutFields_mem (w : Nat) : ∀ (l : List (String × MixedGateBinder)) (o : OutField),
    o ∈ machOutFields w l → ∃ p ∈ l, o.name = p.1 ∧ o.ty = machHWType p.2
  | [], o, h => by
    first
      | (simp [machOutFields] at h)
      | cases h
      | exact absurd h List.not_mem_nil
  | (nm, k) :: rest, o, h => by
    simp only [machOutFields, List.mem_cons] at h
    rcases h with he | hr
    · subst he
      exact ⟨(nm, k), List.mem_cons_self .., rfl, rfl⟩
    · obtain ⟨p, hp, h1, h2⟩ := machOutFields_mem w rest o hr
      exact ⟨p, List.mem_cons_of_mem _ hp, h1, h2⟩

/-- Two entries with the same name in a list whose names are `Nodup` have the
same kind. -/
theorem eq_of_mem_nodup_fst {l : List (String × MixedGateBinder)} {nm : String}
    {a b : MixedGateBinder} (hnd : (l.map (·.1)).Nodup) (ha : (nm, a) ∈ l)
    (hb : (nm, b) ∈ l) : a = b := by
  induction l with
  | nil => cases ha
  | cons p rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnot, hnd'⟩ := hnd
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · subst ha'
      cases hb'
      rfl
    · subst ha'
      exact (hnot (List.mem_map.mpr ⟨(nm, b), hb', rfl⟩)).elim
    · subst hb'
      exact (hnot (List.mem_map.mpr ⟨(nm, a), ha', rfl⟩)).elim
    · exact ih hnd' ha' hb'

/-- No field of a list without `.domain` fields (`machInstanceS`'s test) is
`.domain`. -/
theorem ne_domain_of_any {fields : List (String × MixedGateBinder)}
    {p : String × MixedGateBinder}
    (h : fields.any (fun f => f.2 == MixedGateBinder.domain) = false) (hp : p ∈ fields) :
    p.2 ≠ .domain := by
  intro hd
  have hb : (p.2 == MixedGateBinder.domain) = true := by
    rw [hd]
    all_goals first
      | exact beq_self_eq_true _
      | rfl
      | decide
  have ht : fields.any (fun f => f.2 == MixedGateBinder.domain) = true :=
    List.any_eq_true.mpr ⟨p, hp, hb⟩
  rw [h] at ht
  cases ht

/-- **Name/kind agreement** of an output list at a field: every output entry
named `nm` has kind `r`. -/
def FieldsAgree (outs : List (String × MixedGateBinder)) (nm : String) (r : MixedGateBinder) :
    Prop :=
  ∀ k', (nm, k') ∈ outs → k' = r

/-- **`ChildLinkStruct` from the child's layout** (pure). -/
theorem childLinkStruct_of_layout {kidOuts : Nat → List OutField} {k W : Nat} {nm : String}
    {r : MixedGateBinder} {outs : List (String × MixedGateBinder)}
    (hkid : kidOuts k = machOutFields W outs) (hagree : FieldsAgree outs nm r)
    (hr : r ≠ .domain) : ChildLinkStruct kidOuts k nm r := by
  intro o ho hn
  rw [hkid] at ho
  obtain ⟨p, hp, h1, h2⟩ := machOutFields_mem W outs o ho
  have e1 : p.1 = nm := h1.symm.trans hn
  have hp' : (nm, p.2) ∈ outs := by
    rw [← e1]
    exact hp
  have e2 : p.2 = r := hagree p.2 hp'
  rw [h2, e2, ← kindTy_eq_machHWType hr]

/-! ## The callee's reader result -/

/-- **Agreement from membership**: the wrapper's own test makes the names of
the output list `Nodup`. -/
theorem fieldsAgree_of_reader {sym : Bool} {params : List (String × Nat)} {dE : DefinitionVal}
    {senvC : StructEnv} {allow : Bool} {sc : MachineShape} {nm : String} {r : MixedGateBinder}
    (hL : machineShape? sym params (.defnInfo dE) senvC allow = some sc)
    (hmem : ∀ (ctor? : Option Name) (outs : List (String × MixedGateBinder)),
      declOuts? senvC dE.type = some (ctor?, outs) → (nm, r) ∈ outs) :
    ∀ (ctor? : Option Name) (outs : List (String × MixedGateBinder)),
      declOuts? senvC dE.type = some (ctor?, outs) → FieldsAgree outs nm r := by
  intro ctor? outs hd k' hk'
  obtain ⟨o, ho, ht⟩ := machineShape?_outsTest hL
  have he : o = (ctor?, outs) := Option.some.inj (ho.symm.trans hd)
  subst he
  obtain ⟨_, _, hnd⟩ := outsTest_facts (outs := outs) ht
  exact eq_of_mem_nodup_fst hnd hk' (hmem ctor? outs hd)

/-- **`ChildLinkStruct` from the callee's reader result** at the constant
`dE` its shape was read from. -/
theorem childLinkStruct_of_reader {kidOuts : Nat → List OutField} {k : Nat}
    {sym : Bool} {params : List (String × Nat)} {dE : DefinitionVal}
    {senvC : StructEnv} {allow : Bool} {sc : MachineShape} {nm : String} {r : MixedGateBinder}
    (hL : machineShape? sym params (.defnInfo dE) senvC allow = some sc)
    (hkid : kidOuts k = sc.layout.outs)
    (hmem : ∀ (ctor? : Option Name) (outs : List (String × MixedGateBinder)),
      declOuts? senvC dE.type = some (ctor?, outs) → (nm, r) ∈ outs)
    (hr : r ≠ .domain) : ChildLinkStruct kidOuts k nm r := by
  obtain ⟨_, _, ctor?, outs, _, kinds, _, _, D⟩ := Tools.ShippingShapeDecomp.machineShape?_decomp hL
  exact childLinkStruct_of_layout (hkid.trans D.layoutOuts)
    (fieldsAgree_of_reader hL hmem ctor? outs D.outsEq) hr

/-! ## The link between the parent's call and the callee's declaration -/

/-- **The explicit link** (NOT proved): every field list the PARENT reads off
a structure call of `c` (`machInstanceS`: `senvP.instS c`, the type
instantiated at the call's arguments, `machOuts?`) is contained in the output
list the CALLEE's constant `dE` declares (`declOuts?`, what the callee's
`machineShape?` lays out). -/
def StructRes (senvP : StructEnv) (c : Name) (senvC : StructEnv) (dE : DefinitionVal) : Prop :=
  ∀ (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (resTy : Lean.Expr)
    (ctor : Name) (fields : List (String × MixedGateBinder)),
    senvP.instS c = some (kinds, ty) → Tools.ShippingReaderFuel.instRes ty args = some resTy →
    machOuts? senvP resTy = some (some ctor, fields) →
    ∀ (ctor? : Option Name) (outs : List (String × MixedGateBinder)),
      declOuts? senvC dE.type = some (ctor?, outs) → ∀ p ∈ fields, p ∈ outs

/-- **`ChildLinkStruct` from the entry's structure origin.** -/
theorem childLinkStruct_of_origin {kidOuts : Nat → List OutField} {k : Nat}
    {senvP : StructEnv} {c : Name} {r : MixedGateBinder} {nm : String}
    {sym : Bool} {params : List (String × Nat)} {dE : DefinitionVal}
    {senvC : StructEnv} {allow : Bool} {sc : MachineShape}
    (hS : StructOrigin senvP c r nm) (SR : StructRes senvP c senvC dE)
    (hL : machineShape? sym params (.defnInfo dE) senvC allow = some sc)
    (hkid : kidOuts k = sc.layout.outs) : ChildLinkStruct kidOuts k nm r := by
  obtain ⟨kinds, ty, args, resTy, ctor, fields, i, h1, h2, h3, h4, h5⟩ := hS
  have hmemF : (nm, r) ∈ fields := List.mem_of_getElem? h5
  have hr : r ≠ .domain := ne_domain_of_any (p := (nm, r)) h4 hmemF
  exact childLinkStruct_of_reader hL hkid
    (fun ctor? outs hd => SR kinds ty args resTy ctor fields h1 h2 h3 ctor? outs hd (nm, r) hmemF)
    hr

/-! ## At the callee's real runs -/

section Defs
variable (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)

/-- **`StructRes` at callee `c`**, for the entry constant of every run of the
callee's entry (same form as `P5At`). -/
def StructResAt (senvP : StructEnv) (c : Name) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w1 : Void IO.RealWorld) (ci : ConstantInfo)
    (w2 w5 : Void IO.RealWorld) (envR : Environment) (w6 : Void IO.RealWorld)
    (dE : DefinitionVal),
    RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) =
      .defnInfo dE →
    StructRes senvP c (structEnv envR) dE

end Defs

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **The callee's real entry run**: from a `RealChild` of `c`, the reads of
one run of its entry, the entry constant `dE` it computes, and the shape
`MachineDefines` pins as the reader's result on `dE` (the prefix of
`childLink_real`, with the run facts kept). -/
theorem entryLink_real {c : Name} {sc : MachineShape} {y : Res}
    (entry : MachineDefines mctx mref cctx cref c sc)
    (hy : RealChild mref cref c y) :
    ∃ (mctx' : Meta.Context) (cctx' : Core.Context) (w1 : Void IO.RealWorld) (ci : ConstantInfo)
      (w2 w5 : Void IO.RealWorld) (envR : Environment) (w6 : Void IO.RealWorld)
      (dE : DefinitionVal),
      RunsTo (getConstInfo c) mctx' mref cctx' cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx' mref cctx' cref w5 envR w6 ∧
      entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) =
        .defnInfo dE ∧
      machineShape? false [] (.defnInfo dE) (structEnv envR) = some sc := by
  obtain ⟨M', D'⟩ := y
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := hy.inv
  obtain ⟨M, D, w1, hcore, -, -⟩ := Tools.ShippingGateChildComb.synthesizeCombinational_parts hr
  obtain ⟨L, hv⟩ := invV_of_invW mctx' cctx' hw
  obtain ⟨_, envR, ci, w1', w2', _, _, w5', w6', get, henv, _, _, _⟩ :=
    core_reads_inv L (startV_of_invV L hv) hv.2.2 hcore
  have entry' : MachineDefines mctx' mref cctx' cref c sc :=
    Tools.ShippingReflectCtx.MachineDefines.ctx entry
  obtain ⟨dE, hE, hshape⟩ := link_of_defines entry' get henv henv
  exact ⟨mctx', cctx', w1', ci, w2', w5', envR, w6', dE, get, henv, hE, hshape⟩

/-- **`ChildLinkStruct` for the child really compiled**: `kidOuts k` the
layout of the shape `MachineDefines` pins for the callee `c`, any
`RealChild` of `c`, and `StructResAt`. -/
theorem childLinkStruct_real {kidOuts : Nat → List OutField} {k : Nat}
    {senvP : StructEnv} {c : Name} {r : MixedGateBinder} {nm : String}
    {sc : MachineShape} {y : Res}
    (entry : MachineDefines mctx mref cctx cref c sc)
    (SR : StructResAt mref cref senvP c) (hy : RealChild mref cref c y)
    (hS : StructOrigin senvP c r nm) (hkid : kidOuts k = sc.layout.outs) :
    ChildLinkStruct kidOuts k nm r := by
  obtain ⟨mctx', cctx', w1, ci, w2, w5, envR, w6, dE, get, henv, hE, hshape⟩ :=
    entryLink_real entry hy
  exact childLinkStruct_of_origin hS (SR mctx' cctx' w1 ci w2 w5 envR w6 dE get henv hE)
    hshape hkid

/-- **The structure conjunct of `KindObl`**, from the real child. -/
theorem kindObl_struct_real {env : Environment} {d : MachineData}
    {kidOuts : Nat → List OutField} {k : Nat} {e : Name × List Nat × MixedGateBinder}
    {sc : MachineShape} {y : Res}
    (entry : MachineDefines mctx mref cctx cref e.1 sc)
    (SR : StructResAt mref cref (structEnv env) e.1) (hy : RealChild mref cref e.1 y)
    (hkid : kidOuts k = sc.layout.outs) :
    ∀ nm : String, StructOrigin (structEnv env) e.1 e.2.2 nm →
      d.shape.instFields[k]? = some nm → ChildLinkStruct kidOuts k nm e.2.2 :=
  fun _ hS _ => childLinkStruct_real entry SR hy hS hkid

/-! ## The mixed theorem, structure conjunct discharged -/

/-- **MIXED call widths, structure entries from the real child.** As
`callWidthsStrict_of_linksFM`, with the structure obligation replaced by:
`kidOuts k` is the layout of the callee's `MachineDefines` shape, the callee
is not a memory, and `StructResAt`. The children are those the closing
consumes (`ChildrenReal`). -/
theorem callWidthsStrict_of_linksFMS {env : Environment} {d : MachineData}
    {kidOuts : Nat → List OutField} {children : List Res}
    {nP : Nat} {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal}
    {allowP : Bool}
    (LinkPF : machineShapeF nP symP paramsP (.defnInfo dP) (structEnv env) allowP =
      some (some d.shape))
    (hreal : ChildrenReal mref cref d.shape children)
    (Ord : ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder), d.shape.insts[k]? = some e →
      OrdOrigin (structEnv env) e.1 e.2.2 → ChildLinkOrdD env kidOuts k e.1)
    (Mem : ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder), d.shape.insts[k]? = some e →
      ∀ (combo : Bool) (aw dw : Nat),
        e.1 = Sparkle.Compiler.MachMemory.memChildName combo aw dw →
        e.2.2 = MixedGateBinder.bits dw → ChildLinkMem kidOuts k dw)
    (Struct : ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder), d.shape.insts[k]? = some e →
      (∃ nm : String, StructOrigin (structEnv env) e.1 e.2.2 nm) →
      ∃ sc : MachineShape, kidOuts k = sc.layout.outs ∧
        MachineDefines mctx mref cctx cref e.1 sc ∧
        Sparkle.Compiler.MachMemory.memChild? e.1 = none ∧
        StructResAt mref cref (structEnv env) e.1) :
    callWidthsStrict d (closingNDecl d.shape) kidOuts = true :=
  callWidthsStrict_of_linksFM LinkPF fun k e he => by
    refine ⟨Ord k e he, fun nm hS hnm => ?_, Mem k e he⟩
    obtain ⟨sc, hkid, entry, hnomem, SR⟩ := Struct k e he ⟨nm, hS⟩
    obtain ⟨hk, hke⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨y, hy, _⟩ := hreal.2 k hk
    have hnomem' : Sparkle.Compiler.MachMemory.memChild? (d.shape.insts[k]).1 = none := by
      rw [hke]
      exact hnomem
    have hyR := realChild_of_childrenReal hreal hk hnomem' hy
    rw [hke] at hyR
    exact kindObl_struct_real (d := d) entry SR hyR hkid nm hS hnm

end Tools.ShippingCallWidthsStructLink
