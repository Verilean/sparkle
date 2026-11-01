import Tools.ShippingGen5ReaderTraceDirect
import Tools.ShippingGen5ReaderTraceShape2
set_option autoImplicit false
-- Built in Pod (kjob lake build Tools.ShippingGen5ReaderTraceDirect2, exit 0) on the tree of 237f86d9179ae02cd11f4a9766bcb668fb4bdeab (Lean content identical; this header is comment-only). Clean build is the coder's. No sorry / axiom / native_decide in source.
-- Written against freeze rev20 §3 `scripts/gen5/DG_READERTRACE_FREEZE_REV20.md` (`nDeclOfCi`, `bs_len_eq`, `hbs_of_nDeclOfCi`, `shapeInputs_of'`, `shapeInputs_of_direct'`).

/-! # DG-READERTRACE rev20: `hbs` removed by `nDeclOfCi`, primed `shapeInputs_of` / `shapeInputs_of_direct` (no `hdom`, no `hbs` binder)

`nDeclOfCi ci` is the count `generator` (`ShippingMachineCommand.lean:459-460`) uses for `nDecl`; `bs_len_eq` shows `p.bs.length = nDeclOfCi ci` for every accepted `shapePre`, so `hbs` becomes a theorem for
`nDecl := nDeclOfCi ci`. The same content is then carried by `hnD : nDecl = kDOf d` (DG-DATAOF), which this file does not supply. `hdom`/`DomAtomic` do not occur (`MidInputs'`).
The rev19 `shapeInputs_of` / `shapeInputs_of_direct` are unchanged. Conditional (intermediate) result: the conditions of `shapeInputs_of_direct'` (`DeclValuePh`, `PackTupleInputsBridge`, `RawNodePh`, `NormNodePh`,
`CiDirect`, `ZeroLitAgrees0`, `LiftAgrees`, `Inst1Agrees`) are not claimed true. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.ShippingReaderFuel
open Sparkle.Compiler.MachTupleIn Tools.ShippingGen5ReaderTracePack Tools.ShippingReaderFuelShapeR5

def nDeclOfCi (ci : Lean.ConstantInfo) : Nat :=
  match ci with
  | .defnInfo d =>
    ((mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value)).map (fun x => x.1.length)).getD 0
  | _ => 0

theorem bs_len_eq {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {senv : StructEnv}
    {p : ShapePre} (h : shapePre sm ps ci senv = some p) : p.bs.length = nDeclOfCi ci := by
  obtain ⟨hci, hpeel, -⟩ := shapePre_facts h
  subst hci
  simp [nDeclOfCi, hpeel]

theorem hbs_of_nDeclOfCi (sm : Bool) (ps : List (String × Nat)) (ci : Lean.ConstantInfo) (senv : StructEnv) :
    ∀ p : ShapePre, shapePre sm ps ci senv = some p → p.bs.length ≤ nDeclOfCi ci :=
  fun _ h => Nat.le_of_eq (bs_len_eq h)

theorem shapeInputs_of' (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hrf : RootFloatAgrees)
    {nDecl : Nat} {senv : StructEnv} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {n : Nat}
    (hdecl : ∀ d, ci = ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true)
    (hpack : ∀ (L : Nat) (e : Lean.Expr), NoPh e = true → BvarLt L e = true →
      NoPh (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true ∧
        BvarLt L (Sparkle.Compiler.MachTupleIn.packTupleInputs e) = true)
    (hnorm : ∀ (L : Nat) (e en : Lean.Expr), NoPh e = true → BvarLt L e = true → machNormF n senv e = some en →
      NoPh en = true ∧ BvarLt L en = true)
    (hbs : ∀ p : ShapePre, shapePre sm ps ci senv = some p → p.bs.length ≤ nDecl) :
    ShapeInputs' nDecl senv sm ps ci n := by
  intro p en hp hen
  obtain ⟨hci, hpeel, -⟩ := shapePre_facts hp
  have hd := hdecl p.d hci
  have h1 := hpack 0 _ hd.1 hd.2
  have h2 := mixedGatePeel_ph (L := 0) _ p.bs p.e hpeel h1.1 h1.2
  rw [Nat.zero_add] at h2
  have h3 := hnorm p.bs.length p.e en h2.1 h2.2 hen
  have hm := shapeMid_ph hz hrf senv p h3.1 h3.2
  have hle := hbs p hp
  refine ⟨hle, ?_, ?_, ?_⟩
  · intro k x hx
    have := hm.1 k x hx
    exact ⟨this.1, bvarLt_mono (by omega) this.2⟩
  · intro dom αs ie b hr
    have := hm.2.1 dom αs ie b hr
    exact ⟨this.1, bvarLt_mono (by omega) this.2.1, this.2.2.1, bvarLt_mono (by omega) this.2.2.2⟩
  · intro hr
    have := hm.2.2 hr
    exact ⟨this.1, bvarLt_mono (by omega) this.2⟩

theorem shapeInputs_of_direct'
    (hz : Tools.Assume.N3Extern.ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : Tools.Assume.EnvDeclValue.DeclValuePh env)
    {ci : Lean.ConstantInfo} (hci : CiDirect env ci)
    (hbr : Tools.Assume.PackTupleBridge.PackTupleInputsBridge)
    (hraw : Tools.Assume.NormNodePh.RawNodePh (structEnv env))
    (hnode : Tools.Assume.NormNodePh.NormNodePh (structEnv env))
    {sm : Bool} {ps : List (String × Nat)} {n : Nat} :
    ShapeInputs' (nDeclOfCi ci) (structEnv env) sm ps ci n := by
  have hrf : RootFloatAgrees := Tools.PartialTotal.Agree.rootFloatAgrees hla
  have hdecl : ∀ d, ci = ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true := by
    intro d hd
    obtain ⟨c, hc⟩ := hci
    rw [hd] at hc
    exact hv c d hc
  intro p en hp hen
  obtain ⟨hci', hpeel, -⟩ := shapePre_facts hp
  have hd := hdecl p.d hci'
  have h1 : NoPh (Sparkle.Compiler.MachTupleIn.packTupleInputs p.d.value) = true ∧
      BvarLt 0 (Sparkle.Compiler.MachTupleIn.packTupleInputs p.d.value) = true := by
    rw [hbr _ hd.1 hd.2]
    exact packTupleInputsF_ph hla hi1 _ 0 _ hd.1 hd.2
  have h2 := mixedGatePeel_ph (L := 0) _ p.bs p.e hpeel h1.1 h1.2
  rw [Nat.zero_add] at h2
  have h3 := machNormF_ph hi1 (structEnv env) hraw hnode n p.bs.length p.e en h2.1 h2.2 hen
  have hm := shapeMid_ph hz hrf (structEnv env) p h3.1 h3.2
  have hle := hbs_of_nDeclOfCi sm ps ci (structEnv env) p hp
  refine ⟨hle, ?_, ?_, ?_⟩
  · intro k x hx
    have := hm.1 k x hx
    exact ⟨this.1, bvarLt_mono (by omega) this.2⟩
  · intro dom αs ie b hr
    have := hm.2.1 dom αs ie b hr
    exact ⟨this.1, bvarLt_mono (by omega) this.2.1, this.2.2.1, bvarLt_mono (by omega) this.2.2.2⟩
  · intro hr
    have := hm.2.2 hr
    exact ⟨this.1, bvarLt_mono (by omega) this.2⟩

end Tools.ShippingGen5ReaderTrace
