import Tools.ShippingMachineCloses
import Tools.ShippingMachineAuto

/-! # `MachineCloses` from a machine's data

`machineCloses_of_lets` for a `MachineData`: the premises about the shape are
those of the endpoint's check `MachineData.ok` and its body equation, and one
more check (`MachineData.letsOk`): the shape has no call, and a `let` whose
field is the variable of another `let` reads a `let` whose field is a
variable too. Both are decided by the kernel on the generated data. -/
namespace Tools.ShippingMachineClosesData
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingUnifiedSpine Tools.ShippingSpineOrder Tools.ShippingMachineCloses

/-- A term that reads only accepted inputs uses only accepted inputs. -/
theorem uses_of_reads {okB okV : Nat → Bool} {ub uv : Nat → Prop} {kb kv : Nat} {vw : Nat → Nat}
    (hB : ∀ j, j < kb → okB j = true → ub j) (hV : ∀ j, j < kv → okV j = true → uv j) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → reads okB okV e = true → Uses ub uv e
  | _, .boolInput j, h, r => hB j h r
  | _, .bitsInput _ j, h, r => ⟨hV j h.1 r, trivial, trivial⟩
  | _, .boolLit _, _, _ => trivial
  | _, .bitsLit _ _, _, _ => trivial
  | _, .bitsNum _ _, _, _ => trivial
  | _, .binary _ a b, h, r => by
    simp only [reads, Bool.and_eq_true] at r
    exact ⟨uses_of_reads hB hV a h.1 r.1, uses_of_reads hB hV b h.2 r.2⟩
  | _, .compare _ a b, h, r => by
    simp only [reads, Bool.and_eq_true] at r
    exact ⟨uses_of_reads hB hV a h.1 r.1, uses_of_reads hB hV b h.2 r.2⟩
  | _, .boolBinary _ a b, h, r => by
    simp only [reads, Bool.and_eq_true] at r
    exact ⟨uses_of_reads hB hV a h.1 r.1, uses_of_reads hB hV b h.2 r.2⟩
  | _, .boolNot a, h, r => uses_of_reads hB hV a h r
  | _, .boolEq a b, h, r => by
    simp only [reads, Bool.and_eq_true] at r
    exact ⟨uses_of_reads hB hV a h.1 r.1, uses_of_reads hB hV b h.2 r.2⟩
  | _, .mux c a b, h, r => by
    simp only [reads, Bool.and_eq_true] at r
    exact ⟨uses_of_reads hB hV c h.1 r.1.1, uses_of_reads hB hV a h.2.1 r.1.2,
      uses_of_reads hB hV b h.2.2 r.2⟩
  | _, .setw _ a, h, r => ⟨uses_of_reads hB hV a h.1 r, trivial⟩
  | _, .appCompare _ a b, h, r => by
    simp only [reads, Bool.and_eq_true] at r
    exact ⟨uses_of_reads hB hV a h.1 r.1, uses_of_reads hB hV b h.2 r.2⟩
  | _, .appBool _ a b, h, r => by
    simp only [reads, Bool.and_eq_true] at r
    exact ⟨uses_of_reads hB hV a h.1 r.1, uses_of_reads hB hV b h.2 r.2⟩
  | _, .appBool2 _ a b, h, r => by
    simp only [reads, Bool.and_eq_true] at r
    exact ⟨uses_of_reads hB hV a h.1 r.1, uses_of_reads hB hV b h.2 r.2⟩
  | _, .slice _ _ _ a, h, r => ⟨uses_of_reads hB hV a h.1 r, trivial, trivial⟩
  | _, .concat a b, h, r => by
    simp only [reads, Bool.and_eq_true] at r
    exact ⟨uses_of_reads hB hV a h.1 r.1, uses_of_reads hB hV b h.2 r.2⟩
  | _, .concatLitHi _ _ b, h, r => ⟨uses_of_reads hB hV b h.1 r, trivial, trivial⟩
  | _, .concatLitLo a _ _, h, r => ⟨uses_of_reads hB hV a h.1 r, trivial, trivial⟩
  | _, .zextMap _ _ a, h, r => ⟨uses_of_reads hB hV a h.1 r, trivial⟩
  | _, .sliceF _ _ _ a, h, r => ⟨uses_of_reads hB hV a h.1 r, trivial, trivial⟩

/-- The endpoint's scoping check gives the per-field scope of
`machineCloses_of_lets`: field `k` is well formed and uses only the
variables bound before `let k`. -/
theorem fieldsOK_of_scoped {bpos vpos : Nat → Nat} {kb kv : Nat} {vw : Nat → Nat} (base : Nat) :
    ∀ (fs : List (Σ w : Nat, Term (.bits w))) (bs : List (Name × MixedGateBinder)) (i : Nat)
      {c : Nat} (core : Term (.bits c)), LetsScoped bpos vpos (base + i) bs fs →
      (packLets fs core).2.WF kb kv vw →
      FieldsOK (fun k j => j < kb ∧ bpos j < base + k) (fun k j => j < kv ∧ vpos j < base + k)
        kb kv vw i fs
  | [], _, _, _, _, _, _ => trivial
  | f :: fs, b :: bs, i, _, core, hs, hw =>
    ⟨hw.1,
      uses_of_reads (fun j hj h => ⟨hj, of_decide_eq_true h⟩)
        (fun j hj h => ⟨hj, of_decide_eq_true h⟩) f.2 hw.1 hs.1,
      fieldsOK_of_scoped base fs bs (i + 1) core hs.2.2.2 hw.2⟩
  | _ :: _, [], _, _, _, hs, _ => hs.elim

/-- The scoping check: as many fields as `let` binders, each as wide as its
binder, none a domain. -/
theorem scoped_fit {bpos vpos : Nat → Nat} :
    ∀ (bs : List (Name × MixedGateBinder)) (fs : List (Σ w : Nat, Term (.bits w))) (p : Nat),
      LetsScoped bpos vpos p bs fs →
      fs.length = bs.length ∧
        ∀ (k : Nat) (b : Name × MixedGateBinder) (f : Σ w : Nat, Term (.bits w)),
          bs[k]? = some b → fs[k]? = some f → machWidth b.2 = f.1
  | [], [], _, _ => ⟨rfl, by intro k b f hb; simp at hb⟩
  | b :: bs, f :: fs, p, h => by
    obtain ⟨hl, hf⟩ := scoped_fit bs fs (p + 1) h.2.2.2
    refine ⟨by simp [hl], ?_⟩
    intro k b' f' hb hf'
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hf'
      subst hb; subst hf'
      exact h.2.1
    | succ k => exact hf k b' f' (by simpa using hb) (by simpa using hf')
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-! ## The check on `let`s that are variables -/

/-- The term is an input variable. -/
def isVarB : {s : SType} → Term s → Bool
  | _, .boolInput _ => true
  | _, .bitsInput _ _ => true
  | _, _ => false

/-- The binder position of the input variable the term is. -/
def varPos? (bpos vpos : Nat → Nat) : {s : SType} → Term s → Option Nat
  | _, .boolInput q => some (bpos q)
  | _, .bitsInput _ q => some (vpos q)
  | _, _ => none

theorem isVar_of_isVarB : ∀ {s : SType} (e : Term s), isVarB e = true → IsVar e := by
  intro s e h
  cases e <;> first | trivial | exact absurd h (by simp [isVarB])

theorem varPos?_of_varPos {bpos vpos : Nat → Nat} :
    ∀ {s : SType} (e : Term s) (n : Nat), VarPos bpos vpos e n → varPos? bpos vpos e = some n := by
  intro s e n h
  cases e <;> first | exact congrArg some h | exact h.elim

/-- A field that is the variable of a `let` (a position from `base` on) reads
a `let` whose field is a variable. -/
def aliasOk (bpos vpos : Nat → Nat) (base : Nat) (fs : List (Σ w : Nat, Term (.bits w))) : Bool :=
  fs.all fun fi =>
    match varPos? bpos vpos fi.2 with
    | none => true
    | some n => decide (n < base) ||
      match fs[n - base]? with
      | some fj => isVarB fj.2
      | none => true

theorem aliasOk_sound {bpos vpos : Nat → Nat} {base : Nat}
    {fs : List (Σ w : Nat, Term (.bits w))} (h : aliasOk bpos vpos base fs = true) :
    ∀ (i j : Nat) (fi fj : Σ w : Nat, Term (.bits w)), fs[i]? = some fi → fs[j]? = some fj →
      VarPos bpos vpos fi.2 (base + j) → IsVar fj.2 := by
  intro i j fi fj hi hj hv
  have hall := List.all_eq_true.mp h fi (List.mem_of_getElem? hi)
  rw [varPos?_of_varPos fi.2 _ hv] at hall
  simp only [Nat.add_sub_cancel_left, hj, Bool.or_eq_true, decide_eq_true_eq] at hall
  rcases hall with hlt | hvar
  · omega
  · exact isVar_of_isVarB fj.2 hvar

end Tools.ShippingMachineClosesData

namespace Tools.ShippingMachineAuto.MachineData
open Tools.ShippingMachineClosesData

/-- A `let` that is the variable of another `let` reads one whose field is a
variable. -/
def letsAliasOk (d : MachineData) : Bool :=
  aliasOk d.bpos d.vpos (d.nIn + d.ss.length) d.letFields

/-- No call, and `letsAliasOk`. -/
def letsOk (d : MachineData) : Bool := d.shape.insts.isEmpty && d.letsAliasOk

end Tools.ShippingMachineAuto.MachineData

namespace Tools.ShippingMachineClosesData
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineCloses

/-- **`closeLets` accepts every transition, from the endpoint's own checks** —
for a machine with or without calls whose data pass `ok` (the endpoint's
check), whose body is the quotation of the packed term (the endpoint's body
equation), and that passes `letsAliasOk`. -/
theorem letsClose_of_data {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) :
    Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape := by
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, _, letKinds, _, _, _, hwf, hb, hv,
    _, _, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  have hlenB : (d.bsIn ++ d.slotBs).length = d.nIn + d.ss.length := by
    simp only [List.length_append, MachineData.bsIn, MachineData.slotBs, List.length_take,
      List.length_drop]
    omega
  obtain ⟨hfitL, hfit⟩ := scoped_fit d.letBs d.letFields _ hscoped
  refine letsClose_of_lets (dom := d.dom) (kb := d.kb) (kv := d.kv) (vw := d.vw)
    (bpos := d.bpos) (vpos := d.vpos) (bsIn := d.bsIn ++ d.slotBs) (letBs := d.letBs)
    ?_ d.letFields d.core.2 hwf ?_ ?_ hbody d.binders_split hlets letKinds hfitL hfit ?_ ?_
  · intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  · intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  · intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  · rw [hlenB]
    exact fieldsOK_of_scoped (d.nIn + d.ss.length) d.letFields d.letBs 0 d.core.2 hscoped hwf
  · rw [hlenB]
    exact aliasOk_sound halias

/-- **`MachineCloses` from the endpoint's own checks**, for a machine without
calls (`letsOk`): the machine synthesis closes the `let`s in every context,
for every run. -/
theorem closes_of_data {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hl : d.letsOk = true)
    (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) :
    MachineCloses mctx mref cctx cref declName d.shape := by
  simp only [MachineData.letsOk, Bool.and_eq_true, List.isEmpty_iff] at hl
  exact Tools.ShippingClosesSplit.machineCloses_of_letsClose hl.1
    (letsClose_of_data d ok hbody hl.2 mctx mref cctx cref)

end Tools.ShippingMachineClosesData

namespace Tools.ShippingMachineClosesData
open Lean Sparkle.Compiler.Elab
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto

/-- **With calls, what is left of `MachineCloses` is the calls' closing.** For
a machine whose data pass `ok`, the body equation and `letsAliasOk`:
`MachineCloses` follows from `CallsClose` alone — `closeLets` accepting the
transition is proved (`letsClose_of_data`). `CallsClose` is NOT derived. -/
theorem closes_of_data_calls {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (hc : Tools.ShippingClosesSplit.CallsClose mctx mref cctx cref declName d.shape) :
    MachineCloses mctx mref cctx cref declName d.shape :=
  Tools.ShippingClosesSplit.machineCloses_iff.mpr
    ⟨letsClose_of_data d ok hbody halias mctx mref cctx cref, fun _ => hc⟩

end Tools.ShippingMachineClosesData
