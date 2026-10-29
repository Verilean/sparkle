import Tools.ShippingGen2FitChain   -- Tools.ShippingGen2.OneOutWidth, Pkg, Pkgs
import Tools.ShippingCallWidthsStrict -- callWidthsStrict, callWidthsStrict_at
import Tools.ShippingChildInv       -- notag_at
set_option autoImplicit false

/-! # Supplier-local data bridges for one-output parents (scripts/gen2/S4_PMEM_FREEZE.md §4, S4_WID_SUPPLY.md §3 (b))

UNBUILT when written (no build was run by the author; the caller builds). Standalone: nothing here edits or strengthens a
shared definition (`DataOkB`, `T1Hyp`, `OneOutWidth` are unchanged). Both results are SUPPLIER-LOCAL: each turns a
decided per-declaration Bool row into the property a consumer needs. They are NOT a coverage guarantee: a row is still an
extra premise under an abstract `P` (or an abstract package), and whether every successful compilation's row is true is
a separate, unmeasured coverage obligation (G-DATA / G-ONEOUT-WID). FG is not narrowed by this file.

* P-MEM: `OneOutNoMemRow` (the implication-form row) and `hord_of_row`, restricted to the range `k < insts.length`
  (`instTagged` only covers `insts`' range; a shape with extra `instOrigins` beyond `insts` is not claimed). The NAME half
  of the existing `hnomem` (`memChild? x.1 = none`) is NOT implied and is not part of the row.
* WID: `kidOutsP` (the b1 table read through `P`), its agreement lemma `kidOutsP_eq`, the vacuous case `kidOutsP_none`,
  and `oneOutWidth_of_strict` (from `callWidthsStrict_at`, `nDecl = p.kD`) concluding `∀ k, OneOutWidth P p k`;
  `oneOutWidth_of_strictP` is the b1 instance. Call EXISTENCE (`P c = some q`) is not given by the row: with `P c = none`
  the table entry is `[]` and the row is vacuously true; existence comes from `hdec`/the supplier.

No sorry / axiom / native_decide. -/
namespace Tools.ShippingGen2DataBridge
open Lean
open Sparkle.Compiler.Elab
open Sparkle.Core.Domain

variable {ι : Type} {dom : ι → DomainConfig}

/-! ## P-MEM: the implication-form row -/

/-- The row on a shape: with no field list (the one-output closing), no call entry has a memory origin. -/
def noMemRowS (s : MachineShape) : Bool :=
  !s.instFields.isEmpty || s.instTagged.all (fun x => x.2.child?.isNone)

/-- **The P-MEM row** of a package (implication form: memory parents, whose `instFields ≠ []`, pass it). -/
def OneOutNoMemRow (p : Tools.ShippingGen2.Pkg ι dom) : Bool :=
  !p.d.shape.instFields.isEmpty || p.d.shape.instTagged.all (fun x => x.2.child?.isNone)

theorem OneOutNoMemRow_eq (p : Tools.ShippingGen2.Pkg ι dom) : OneOutNoMemRow p = noMemRowS p.d.shape := rfl

/-- The shape form of `hord_of_row`. -/
theorem hord_of_rowS {s : MachineShape} (h : noMemRowS s = true) (hf : s.instFields = [])
    {k : Nat} (hk : k < s.insts.length) :
    (s.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none := by
  have hall : s.instTagged.all (fun x => x.2.child?.isNone) = true := by
    have h0 := h
    unfold noMemRowS at h0
    rw [hf] at h0
    first
      | exact h0
      | (simp only [List.isEmpty_nil, Bool.not_true, Bool.false_or] at h0; exact h0)
      | simpa using h0
  exact Tools.ShippingChildInv.notag_at (fun o ho => List.all_eq_true.mp hall o ho) hk

/-- **`hord_of_row`**: the row and an empty field list give the `.ord`-like origin at every entry IN RANGE. -/
theorem hord_of_row {p : Tools.ShippingGen2.Pkg ι dom} (h : OneOutNoMemRow p = true)
    (hf : p.d.shape.instFields = []) (k : Nat) (hk : k < p.d.shape.insts.length) :
    (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none :=
  hord_of_rowS (s := p.d.shape) h hf hk

/-! ## WID: the b1 table and the strict-row bridge -/

/-- The b1 table: entry `k`'s callee's layout outputs, read through `P` (`[]` off the range or for `P c = none`).
Same meaning as the `match` of S4_WID_SUPPLY.md §3 (b), written with `Option.bind`/`getD`. -/
def kidOutsP (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom) (k : Nat) :
    List Sparkle.IR.Machine.OutField :=
  ((((p.d.shape.insts.map (·.1))[k]?).bind P).map (fun q => q.d.shape.layout.outs)).getD []

theorem insts_map_fst_getElem? (s : MachineShape) {k : Nat} (hk : k < s.insts.length) :
    (s.insts.map (·.1))[k]? = some (s.insts[k]).1 := by
  first
    | (rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl)
    | simp [hk]

/-- **Agreement of the b1 table** with the served package at an entry in range. -/
theorem kidOutsP_eq (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom) {k : Nat}
    (hk : k < p.d.shape.insts.length) {q : Tools.ShippingGen2.Pkg ι dom} (hq : P (p.d.shape.insts[k]).1 = some q) :
    kidOutsP P p k = q.d.shape.layout.outs := by
  have h1 := insts_map_fst_getElem? p.d.shape hk
  have h2 : kidOutsP P p k =
      ((P (p.d.shape.insts[k]).1).map (fun q => q.d.shape.layout.outs)).getD [] := by
    unfold kidOutsP
    rw [h1]
    rfl
  rw [h2, hq]
  rfl

/-- The vacuous case: no package for the callee gives the empty entry. -/
theorem kidOutsP_none (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom) {k : Nat}
    (hk : k < p.d.shape.insts.length) (hn : P (p.d.shape.insts[k]).1 = none) :
    kidOutsP P p k = [] := by
  have h1 := insts_map_fst_getElem? p.d.shape hk
  have h2 : kidOutsP P p k =
      ((P (p.d.shape.insts[k]).1).map (fun q => q.d.shape.layout.outs)).getD [] := by
    unfold kidOutsP
    rw [h1]
    rfl
  rw [h2, hn]
  rfl

/-- An assignment with no packages gives the empty table everywhere. -/
theorem kidOutsP_allNone (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom)
    (hP : ∀ c, P c = none) : kidOutsP P p = fun _ => [] := by
  funext k
  unfold kidOutsP
  generalize (p.d.shape.insts.map (·.1))[k]? = oc
  cases oc with
  | none => rfl
  | some c =>
    show ((P c).map (fun q => q.d.shape.layout.outs)).getD [] = []
    rw [hP c]
    rfl

/-- The empty table passes the strict row (vacuously). -/
theorem callWidthsStrict_empty (d : Tools.ShippingMachineAuto.MachineData) (n : Nat) :
    Tools.ShippingCallWidthsStrict.callWidthsStrict d n (fun _ => []) = true := by
  unfold Tools.ShippingCallWidthsStrict.callWidthsStrict
  exact List.all_eq_true.mpr (fun _ _ => rfl)

/-- **`oneOutWidth_of_strict`**: a decided strict row over ANY table that agrees with the served packages gives
`OneOutWidth` at every `k` (the name side is vacuous because `instFields = []`; `nDecl = p.kD`). -/
theorem oneOutWidth_of_strict (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom)
    (kidOuts : Nat → List Sparkle.IR.Machine.OutField)
    (hcw : Tools.ShippingCallWidthsStrict.callWidthsStrict p.d p.kD kidOuts = true)
    (hsimple : p.d.shape.instFields = [])
    (hkid : ∀ k (hk : k < p.d.shape.insts.length) (q : Tools.ShippingGen2.Pkg ι dom),
      P (p.d.shape.insts[k]).1 = some q → kidOuts k = q.d.shape.layout.outs) :
    ∀ k, Tools.ShippingGen2.OneOutWidth P p k := by
  intro k
  unfold Tools.ShippingGen2.OneOutWidth
  intro hk q hq o ho
  have hmem : o ∈ kidOuts k := by
    rw [hkid k hk q hq, ho]
    exact List.mem_singleton_self o
  exact Tools.ShippingCallWidthsStrict.callWidthsStrict_at hcw hk hmem
    (fun f hf => by
      rw [hsimple] at hf
      exact absurd hf (by simp))

/-- The b1 instance: the table read through `P` itself (`hkid` by `kidOutsP_eq`). -/
theorem oneOutWidth_of_strictP (P : Tools.ShippingGen2.Pkgs ι dom) (p : Tools.ShippingGen2.Pkg ι dom)
    (hcw : Tools.ShippingCallWidthsStrict.callWidthsStrict p.d p.kD (kidOutsP P p) = true)
    (hsimple : p.d.shape.instFields = []) :
    ∀ k, Tools.ShippingGen2.OneOutWidth P p k :=
  oneOutWidth_of_strict P p (kidOutsP P p) hcw hsimple (fun _ hk _ hq => kidOutsP_eq P p hk hq)

end Tools.ShippingGen2DataBridge
