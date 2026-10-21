import Tools.Prototype.ReaderFixpointNorm
import Tools.ShippingReaderFuelShapeR5
import Tools.ShippingReaderFuelShapeR1
import Tools.ShippingReaderFuelShapeProv
import Tools.ShippingLetsReaderInvMain

/-! # Unit LC12 prototype: SPECIFICATION lemmas for the kernel-visible reader `machineShapeN`

BUILT/UNBUILT: see REPORT-LC12.md (run names + exits).  No sorry / axiom / native_decide.  Production
unchanged; `machineShapeN` is the prototype wrapper of LC11b (`shapeW` against `execNorm` + `execBlock`), NOT the
shipped `machineShape?`; `TwinCoverAt` and `machNorm = execNorm` stay OPEN.

## Part 1 (premise-free transfer)
Every property of a successful result that is PROVED for the fuel wrapper `machineShapeF` is a property of
`machineShapeN`, by `machineShapeN_fuel` (`machineShapeN … = some r → ∃ n, machineShapeF n … = some r`, LC11b).
The lemmas below are those transfers (layout / binder-count / slot / output widths, `ShapeDecomp`, call-entry
R1 and provenance, origin tags).  They add NOTHING that was not already proved for `machineShapeF`; their value
is that the subject is now the kernel-visible executable reader.

## Part 2 (new): the `let`-table properties of the result
`machineShapeN_lets` (conditional on `ShapeInOk`, the wrapper-level form of LC3's INPUT condition `LetOk 0`, and
on the five named premises of LC3/LC5) — the final reader state `st` of any successful run has an alias-free
`let` table (`NoLetAlias st.lets`, the Expr-level half of `letsAliasOk`) and `st` is a `RdOk` state in which the
body value `v` is in range (`LetOk st.lets.size v`), and the shape is `shapePost … st v`.  See the docstring there
for the exact input condition and the one field (`startDom`) that is a genuine gap of the invariant. -/
namespace Tools.Prototype.ReaderExec
open Lean Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv
open Tools.ShippingLetsAliasInv Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk
open Tools.ShippingShapeDecomp Tools.ShippingReaderFuelProv Tools.ShippingReaderFuelShapeProv

/-! ## Part 1: transfers from `machineShapeF` -/

section Transfer
variable {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {senv : StructEnv}
  {ai : Bool} {sp : MachineShape}

/-- The phases of a successful run (executable reader), with every intermediate state, at ONE common fuel. -/
theorem machineShapeN_steps (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0)
          (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp := by
  obtain ⟨n, hn⟩ := machineShapeN_fuel h
  obtain ⟨p, en, st0, env, st1, st, v, h1, h2, h3, h4, h5, h6⟩ := machineShapeF_steps hn
  exact ⟨n, p, en, st0, env, st1, st, v, h1, h2, h3, h4, h5, h6⟩

theorem machineShapeN_lenOk (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      st0.LenOk ∧ st1.LenOk ∧ st.LenOk ∧
      shapePost ai p (shapeMid senv p en) st v = some sp :=
  machineShapeF_lenOk (machineShapeN_fuel h).choose_spec

theorem machineShapeN_origins_aligned (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    sp.instOrigins.length = sp.insts.length :=
  machineShapeF_origins_aligned (machineShapeN_fuel h).choose_spec

theorem machineShapeN_decomp (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (d : DefinitionVal) (bs : List (Name × MixedGateBinder)) (e : Lean.Expr)
      (ctor? : Option Name) (outs : List (String × MixedGateBinder)) (names : List Name)
      (kinds : List MixedGateBinder) (inits : List Nat) (letB : List (Name × MixedGateBinder)),
      ci = .defnInfo d ∧ ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB ∧
      names.length = kinds.length ∧ inits.length = kinds.length :=
  machineShapeF_decomp (machineShapeN_fuel h).choose_spec

theorem machineShapeN_r5 (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (d : DefinitionVal) (bs : List (Name × MixedGateBinder)) (e : Lean.Expr)
      (ctor? : Option Name) (outs : List (String × MixedGateBinder)) (names : List Name)
      (kinds : List MixedGateBinder) (inits : List Nat) (letB : List (Name × MixedGateBinder)),
      ci = .defnInfo d ∧ ShapeDecomp d senv sp bs e ctor? outs names kinds inits letB ∧
      (names.zip kinds).length = sp.layout.slots.length :=
  machineShapeF_r5 (machineShapeN_fuel h).choose_spec

section Defn
variable {d : DefinitionVal}

/-- Binder count of the shape: declared inputs + call entries + slots + lets. -/
theorem machineShapeN_binderCount (h : machineShapeN sm ps (.defnInfo d) senv ai = some (some sp)) :
    ∃ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      sp.binders.length =
        bs.length + sp.insts.length + sp.layout.slots.length + sp.layout.lets :=
  machineShapeF_binderCount (machineShapeN_fuel h).choose_spec

theorem machineShapeN_nDecl (h : machineShapeN sm ps (.defnInfo d) senv ai = some (some sp)) :
    ∃ (bs : List (Name × MixedGateBinder)) (e : Lean.Expr),
      mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value) = some (bs, e) ∧
      sp.binders.length - sp.insts.length - sp.layout.slots.length - sp.layout.lets =
        bs.length :=
  machineShapeF_nDecl (machineShapeN_fuel h).choose_spec

/-- The binder at a call entry's position carries the entry's result kind (`PB`-type fact). -/
theorem machineShapeN_callBinder (h : machineShapeN sm ps (.defnInfo d) senv ai = some (some sp))
    {k : Nat} (hk : k < sp.insts.length) :
    (sp.binders.map (·.2))[(sp.binders.length - sp.insts.length - sp.layout.slots.length -
        sp.layout.lets) + k]? = (sp.insts.map (·.2.2))[k]? :=
  machineShapeF_callBinder (machineShapeN_fuel h).choose_spec hk

theorem machineShapeN_slots_length (h : machineShapeN sm ps (.defnInfo d) senv ai = some (some sp)) :
    ∃ (names : List Name) (kinds : List MixedGateBinder) (inits : List Nat),
      sp.layout.slots.length = kinds.length ∧ names.length = kinds.length ∧
      inits.length = kinds.length ∧
      sp.layout.slots = machSlotFields ((kinds.map machWidth).zip inits) :=
  machineShapeF_slots_length (machineShapeN_fuel h).choose_spec

theorem machineShapeN_single_out (h : machineShapeN sm ps (.defnInfo d) senv ai = some (some sp))
    {k : MixedGateBinder} (hres : machResultKind? d.type = some k) :
    ∃ kinds : List MixedGateBinder,
      sp.layout.outs = [{ name := "out", lo := (kinds.map machWidth).sum, width := machWidth k,
                          ty := machHWType k }] :=
  machineShapeF_single_out (machineShapeN_fuel h).choose_spec hres

end Defn

/-- Call-entry provenance (per index). -/
theorem machineShapeN_origin (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder),
      sp.insts[k]? = some e → OriginAt senv e sp.instFields[k]? :=
  machineShapeF_origin (machineShapeN_fuel h).choose_spec

theorem machineShapeN_origin_mem (h : machineShapeN sm ps ci senv ai = some (some sp))
    {e : Name × List Nat × MixedGateBinder} (he : e ∈ sp.insts) :
    OrdOrigin senv e.1 e.2.2 ∨ (∃ nm : String, StructOrigin senv e.1 e.2.2 nm) ∨
      MemOrigin e.1 e.2.2 :=
  machineShapeF_origin_mem (machineShapeN_fuel h).choose_spec he

theorem machineShapeN_originT (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∀ (k : Nat) (e : Name × List Nat × MixedGateBinder)
      (o : Sparkle.Compiler.MachInstOrigin.InstOrigin),
      sp.insts[k]? = some e → sp.instOrigins[k]? = some o →
        OriginTAt senv e sp.instFields[k]? o :=
  machineShapeF_originT (machineShapeN_fuel h).choose_spec

theorem machineShapeN_tag_exists (h : machineShapeN sm ps ci senv ai = some (some sp))
    {k : Nat} {e : Name × List Nat × MixedGateBinder} (hk : sp.insts[k]? = some e) :
    ∃ o, sp.instOrigins[k]? = some o :=
  machineShapeF_tag_exists (machineShapeN_fuel h).choose_spec hk

/-- Call-entry R1: a reader-produced entry's result kind is its callee's declared result kind. -/
theorem machineShapeN_instR1 (hM : Tools.ShippingReaderFuelR1.MemR1 senv)
    (hD : Tools.ShippingReaderFuelR1.SigDisj senv)
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∀ (c : Name) (js : List Nat) (r : MixedGateBinder), (c, js, r) ∈ sp.insts →
      ∀ (kinds : List MixedGateBinder) (r' : MixedGateBinder),
        senv.inst c = some (kinds, r') → r = r' :=
  Tools.ShippingReaderFuelShapeR1.machineShapeF_instR1 hM hD (machineShapeN_fuel h).choose_spec

end Transfer

#print axioms machineShapeN_steps
#print axioms machineShapeN_binderCount
#print axioms machineShapeN_originT
#print axioms machineShapeN_instR1

end Tools.Prototype.ReaderExec
