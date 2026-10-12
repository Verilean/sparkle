import Tools.ShippingShapeDecomp
import Tools.ShippingCallWidthsStrict

/-! # `callWidthsStrict` per entry, for a one-Signal callee read from its DECLARED constant

`callWidthsStrict d nDecl kidOuts` (`Tools/ShippingCallWidthsStrict.lean`)
is a conjunction over the call entries; `entryStrict d nDecl kidOuts k` is
its `k`-th conjunct (`callWidthsStrict_eq_all`, `callWidthsStrict_of_entries`).

`entryStrict_of_single` discharges ONE conjunct from

* the child side — `kidOuts k` is the single output `out` of type
  `machHWType res` (what `ShapeDecomp.single_out` / `callee_single_out`
  prove for a callee whose shape is read from its declared constant), and
* **R1**, an EXPLICIT hypothesis: the type of the parent's binder at
  `nDecl + k` is `machHWType res`.

`entryStrict_declared` assembles what is proved today and leaves visible
what is not: its hypotheses are the two readers' results, the callee's
signature and constant in the environment, **R5** of the parent (slot
binders as many as slots), and **R1** in its reader form — the kind of the
parent's call entry `k` is the kind `(structEnv env).inst c` gives. R1 is a
fact about the result of the `partial` `machInstance`; R5 about the reader
state; neither is proved.

NOT a replacement of any existing `decide` (see
`docs/parallel/B-readerinv.md` §7): no existing endpoint decides a
call-width condition for a one-Signal callee, and the shapes here are
`machineShape?` results, while the endpoints' data conditions are about
REFLECTED shapes (`MachineData`); `hp` / `hc` below are that link, as
hypotheses.

UNVERIFIED: not built. -/
namespace Tools.ShippingCallWidthsDeclared
open Lean
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingCallWidthsStrict
open Tools.ShippingReaderResultKind Tools.ShippingInstSignature
open Tools.ShippingMachineShapeUnfold Tools.ShippingShapeDecomp

/-- The `k`-th conjunct of `callWidthsStrict`. -/
def entryStrict (d : MachineData) (nDecl : Nat) (kidOuts : Nat → List OutField) (k : Nat) : Bool :=
  (kidOuts k).all fun o =>
    (d.shape.instFields[k]?).any (fun f => o.name != f) ||
      decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
        some o.ty.bitWidth)

theorem callWidthsStrict_eq_all (d : MachineData) (nDecl : Nat) (kidOuts : Nat → List OutField) :
    callWidthsStrict d nDecl kidOuts =
      (List.range d.shape.insts.length).all (entryStrict d nDecl kidOuts) := rfl

/-- The whole condition from its conjuncts. -/
theorem callWidthsStrict_of_entries {d : MachineData} {nDecl : Nat}
    {kidOuts : Nat → List OutField}
    (h : ∀ k, k < d.shape.insts.length → entryStrict d nDecl kidOuts k = true) :
    callWidthsStrict d nDecl kidOuts = true := by
  rw [callWidthsStrict_eq_all]
  exact List.all_eq_true.mpr fun k hk => h k (List.mem_range.mp hk)

/-- The type of a non-domain kind is its hardware type. -/
theorem kindTy_eq_machHWType {k : MixedGateBinder} (hk : k ≠ .domain) :
    kindTy k = machHWType k := by
  cases k with
  | domain => exact absurd rfl hk
  | bool => rfl
  | bits n => rfl

/-- **One conjunct, from the child's single output and R1.** -/
theorem entryStrict_of_single {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    {k W : Nat} {res : MixedGateBinder}
    (hout : kidOuts k =
      [{ name := "out", lo := W, width := machWidth res, ty := machHWType res }])
    (R1 : (d.shape.binders[nDecl + k]?).map (fun bn => kindTy bn.2) = some (machHWType res)) :
    entryStrict d nDecl kidOuts k = true := by
  unfold entryStrict
  rw [hout]
  have hw : (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
      some (machHWType res).bitWidth := by
    cases hb : d.shape.binders[nDecl + k]? with
    | none =>
      rw [hb] at R1
      simp at R1
    | some bn =>
      rw [hb] at R1
      have e : kindTy bn.2 = machHWType res := Option.some.inj R1
      exact congrArg (fun t : Sparkle.IR.Type.HWType => some t.bitWidth) e
  refine List.all_eq_true.mpr fun o ho => ?_
  have ho' : o = { name := "out", lo := W, width := machWidth res, ty := machHWType res } :=
    List.mem_singleton.mp ho
  have hdec : decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
      some o.ty.bitWidth) = true := by
    rw [ho']
    exact decide_eq_true hw
  first
    | exact (Bool.or_eq_true _ _).mpr (Or.inr hdec)
    | (simp only [Bool.or_eq_true]; exact Or.inr hdec)
    | simp [hdec]

/-- R1 in its reader form gives R1 in the form `entryStrict_of_single`
takes: a binder whose KIND is `res` (not the domain) has the type
`machHWType res`. -/
theorem r1_of_kind {binders : List (Name × MixedGateBinder)} {i : Nat} {res : MixedGateBinder}
    (hkind : (binders.map (·.2))[i]? = some res) (hres : res ≠ .domain) :
    (binders[i]?).map (fun bn => kindTy bn.2) = some (machHWType res) := by
  rw [List.getElem?_map] at hkind
  cases hb : binders[i]? with
  | none =>
    rw [hb] at hkind
    simp at hkind
  | some bn =>
    rw [hb] at hkind
    have e : bn.2 = res := Option.some.inj hkind
    show some (kindTy bn.2) = some (machHWType res)
    rw [e, kindTy_eq_machHWType hres]

/-- **The declared one-Signal subset, assembled.** For a parent shape
`d.shape` and a callee `c` with a one-Signal signature whose shape `sc` was
read from its declared constant: conjunct `k` of `callWidthsStrict` at the
closing's `nDecl`, against the child's layout outputs.

What is PROVED inside: the child's layout is the single `out` of
`machHWType res` (P1 + P2 + the decomposition), the parent's binder at
`nDecl + k` carries the kind of call entry `k` (the decomposition + `nDecl`
under R5), a non-domain kind's type is its hardware type.

What is ASSUMED, by name:
* `hp`, `hc` — the two shapes are `machineShape?` results on these
  constants (for an endpoint: `MachineDefines`, with the entry constant; a
  child compiled from its UNFOLDING is not covered — P5);
* `R5` — the parent's slot binders are as many as its layout's slots;
* `R1` — the kind of the parent's call entry `k` is the callee's signature
  kind `res` (the result of the `partial` `machInstance`). -/
theorem entryStrict_declared {env : Environment} {c : Name}
    {d : MachineData} {kidOuts : Nat → List OutField} {k : Nat}
    {symP : Bool} {paramsP : List (String × Nat)} {dP : DefinitionVal} {senvP : StructEnv}
    {allowP : Bool}
    {bs : List (Name × MixedGateBinder)} {e : Lean.Expr} {ctor? : Option Name}
    {outs : List (String × MixedGateBinder)} {names : List Name}
    {kindsP : List MixedGateBinder} {inits : List Nat} {letB : List (Name × MixedGateBinder)}
    (DP : ShapeDecomp dP senvP d.shape bs e ctor? outs names kindsP inits letB)
    {kinds : List MixedGateBinder} {res : MixedGateBinder} {dC : DefinitionVal}
    {symC : Bool} {paramsC : List (String × Nat)} {senvC : StructEnv} {allowC : Bool}
    {sc : MachineShape}
    (hinst : (structEnv env).inst c = some (kinds, res))
    (hfind : env.find? c = some (.defnInfo dC))
    (hc : machineShape? symC paramsC (.defnInfo dC) senvC allowC = some sc)
    (hkid : kidOuts k = sc.layout.outs)
    (hk : k < d.shape.insts.length)
    (R5 : (names.zip kindsP).length = d.shape.layout.slots.length)
    (R1 : (d.shape.insts.map (·.2.2))[k]? = some res) :
    entryStrict d
      (d.shape.binders.length - d.shape.insts.length - d.shape.layout.slots.length -
        d.shape.layout.lets) kidOuts k = true := by
  -- the callee's signature is read off its constant (P1)
  rw [structEnv_inst] at hinst
  obtain ⟨_, ci, hci, _, hr⟩ := instSignature?_some hinst
  rw [hfind] at hci
  cases hci
  have hres : res ≠ .domain := machResultKind?_ne_domain _ res hr
  -- the child's layout: the single output `out` (P2 + the decomposition)
  obtain ⟨_, _, _, _, _, kindsC, _, _, DC⟩ := machineShape?_decomp hc
  have hout := hkid.trans (DC.single_out hr)
  -- the parent's binder at `nDecl + k` has the entry's kind (R5), which is `res` (R1)
  have hkind := (DP.callBinder R5 hk).trans R1
  exact entryStrict_of_single hout (r1_of_kind hkind hres)

end Tools.ShippingCallWidthsDeclared
