import Tools.ShippingMachineChild
import Tools.ShippingUnifiedExecutionSoundness
import Tools.ShippingInlineSoundness

/-! # A child the certified gate compiles, as what its instances compute

`machine_linked` (ShippingMachineCompose) composes a parent with its
children under the hypothesis that every call's module computes some
function of its argument ports (`ChildFn`). For a combinational child on the
MACHINE route that hypothesis is `child_full` (ShippingMachineChild). This
file gives it for a child the certified combinational GATE compiles: the
gate's harness (`synthesizeMixedCertified`, the same one the machine route's
transition goes through) fixes the module's input ports (`transition_facts`)
and its value (`RawValueAt`), so at one cycle, on an environment whose
argument ports hold in-range values, the module drives its output with the
unified term's value on those values, decoded. -/
namespace Tools.ShippingGateChild
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineCompose
open Tools.ShippingMachineChild
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingEntrySoundness (RunsTo EnvDefines entry_kept synthesizeCombinationalCore_reads
  MReturns)
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingUnifiedMeaning (pack)
open Tools.ShippingInlineSoundness (EntryDefines)

/-- The gate's entry: a run of `synthesizeFromConst` that the unified gate
accepts is a run of the harness on the gate's binders and body. -/
theorem synthesizeFromConst_mixed_run {logProf declName ci bs body m d}
    {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName [] false true
        ci isInst) (m, d)) :
    MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d) := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact run

/-- **The gate's core run, with its ports.** A run of the core entry on a
declaration the unified gate accepts (its value peels to the quote of a
well-formed term; `EntryDefines`: the constant the entry hands on, the
declaration as read or its unfolding) returns a module whose value on admissible inputs is the
term's (`RawValueAt`) and whose input ports are the binder walk's. -/
theorem gate_core_facts {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)),
      ids.Nodup ∧ ids.length = bs.length ∧
      (∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (initial : Env)
          (mems : MEnv),
        SourceInputs declName bs ids cache bools bits initial →
        RawValueAt srt.width bs m initial mems
          (pack srt (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w) e)).toNat) ∧
      (∀ bools bits, m.inputs = inputPorts bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)) ∧
      Tools.ShippingMixedEntrySoundness.PositiveBinders bs := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  obtain ⟨d, hd, definition⟩ := entry w1 ci w2 w5 envR w6 get henv
  rw [hd] at run
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have shape := term_gate (d := d) (by rw [definition]; exact peel) he hb hv
  have core := synthesizeFromConst_mixed_run oldGate (shape _) run.mreturns
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, _, nameLegal⟩ :=
    synthesizeMixedCertified_returns core
  obtain ⟨vals, _, ins⟩ := transition_facts nd len hrun hm nameLegal he hb hv rfl
  exact ⟨ids, cache, nd, len, vals, ins,
    Tools.ShippingMixedPrintSoundness.mixedShape_positive (shape (fun _ => false))⟩

/-- The all-zero environment is admissible for the all-`false`, all-zero
inputs. -/
theorem admissible_zero (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup) :
    Admissible (fun _ => false) (fun _ n => 0#n) (fun _ => 0) L a := by
  induction L generalizing a with
  | nil => trivial
  | cons b rest ih =>
    obtain ⟨⟨name, kind⟩, id⟩ := b
    refine ⟨?_, ih _⟩
    cases kind <;> simp [InputValue, Tools.ShippingMuxLoweringSoundness.encodeBool]

/-- **The gate's core module computes the term on its argument ports.** On
an environment whose argument ports hold in-range values (and reset low),
the module drives its single output with `F` of those values, `F` being the
term's value on them decoded; and its body is assignments only. -/
theorem gate_childFn {declName : Name} {m : Sparkle.IR.AST.Module}
    {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {srt : SType} {e : Term srt} {bpos vpos : Nat → Nat}
    (nd : ids.Nodup) (len : ids.length = bs.length)
    (vals : ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (initial : Env)
        (mems : MEnv),
      SourceInputs declName bs ids cache bools bits initial →
      RawValueAt srt.width bs m initial mems
        (pack srt (eval (fun j => bools (bpos j)) (fun j w => bits (vpos j) w) e)).toNat)
    (ins : ∀ bools bits, m.inputs = inputPorts bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString))
    (positive : Tools.ShippingMixedEntrySoundness.PositiveBinders bs)
    {F : List Nat → Nat}
    (hF : ∀ vs, InRange vs (bs.filter fun b => b.2 != .domain) →
      F vs = (pack srt (eval (fun j => decB bs vs (bpos j)) (fun j w => decV bs vs (vpos j) w) e)).toNat) :
    ChildFn m (fun vs => InRange vs (bs.filter fun b => b.2 != .domain)) F ∧
      m.body.all Sparkle.IR.RegDedup.isAssign = true := by
  -- the facts that do not depend on the inputs, at the all-zero environment
  obtain ⟨_, _, _, _, simple, _, _, _, pb⟩ := vals (fun _ => false) (fun _ n => 0#n) (fun _ => 0)
    (fun _ _ => 0) (admissible_zero _ _)
  have pb := pb positive
  have hall : m.body.all Sparkle.IR.RegDedup.isAssign = true := by
    rw [List.all_eq_true]
    intro st hs
    obtain ⟨l, r, rfl, _⟩ := simple st hs
    rfl
  refine ⟨?_, hall⟩
  obtain ⟨ty, hout⟩ := pb.output
  refine ⟨{ name := "out", ty := ty }, hout, ?_⟩
  intro mems env _ hP
  -- the argument ports are the binder walk's
  have hargs : argPorts m = machPorts declName ids cache bs := by
    unfold argPorts machPorts
    rw [ins (fun _ => false) (fun _ n => 0#n)]
    apply List.filter_eq_self.mpr
    intro p hp
    have hpi : p ∈ m.inputs := by rw [ins (fun _ => false) (fun _ n => 0#n)]; exact hp
    have alloc : Sparkle.IR.NameHints.Allocated p.name := pb.wireNames p (pb.inputWires p hpi)
    have hc : p.name ≠ "clk" := fun h => by
      have := (h ▸ alloc : Sparkle.IR.NameHints.Allocated "clk").2
      revert this; decide
    have hr : p.name ≠ "rst" := fun h =>
      Tools.ShippingRegisterSoundness.not_allocated_rst (h ▸ alloc)
    simp [hc, hr]
  let vs := (argPorts m).map fun p => env p.name
  let bools : Nat → Bool := fun p => decB bs vs p
  let bits : (j : Nat) → (n : Nat) → BitVec n := fun p n => decV bs vs p n
  have hlenIn : bs.length ≤ ids.length := by omega
  have hsi : SourceInputs declName bs ids cache bools bits env := by
    unfold SourceInputs
    apply admissible_of_portsD
    rw [show inputPorts (boolValues ids bools) (bitValues ids bits) (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString) =
        machPorts declName ids cache bs from inputPorts_congr _ _ _ rfl, ← hargs]
    have hlenP : (argPorts m).length =
        ((bs.zip ids).filter fun b => b.1.2 != .domain).length := by
      rw [hargs, machPorts_length _ hlenIn, ← zip_filter_fst _ _ hlenIn, List.length_map]
    apply Zip₂.of_get hlenP
    intro q p b hp hb
    obtain ⟨pos, hpos, hcnt⟩ := filter_getElem_pos _ _ q b hb
    obtain ⟨⟨nm, kind⟩, id⟩ := b
    obtain ⟨hb1, hb2⟩ := List.getElem?_zip_eq_some.mp hpos
    have hidx : ids.idxOf id = pos := by
      have hlt : pos < ids.length := (List.getElem?_eq_some_iff.mp hb2).1
      have hg : ids[pos]! = id := by simp [List.getElem!_eq_getElem?_getD, hb2]
      rw [← hg]; exact index_fresh ids nd pos hlt
    have hport : portIdx bs pos = q := by
      unfold portIdx
      have hpl : pos < bs.length := (List.getElem?_eq_some_iff.mp hb1).1
      rw [← hcnt, show (bs.zip ids).take pos = (bs.take pos).zip (ids.take pos) from
        List.take_zipWith, ← zip_filter_fst (bs.take pos) (ids.take pos)
        (by simp only [List.length_take]; omega), List.length_map]
    have hval : vs.getD q 0 = env p.name := by
      simp [vs, List.getD_eq_getElem?_getD, hp]
    have hfq : (bs.filter fun b => b.2 != .domain)[q]? = some (nm, kind) := by
      rw [← zip_filter_fst _ _ hlenIn, List.getElem?_map, hb]; rfl
    have hr := inRange_get hP q (nm, kind) hfq
    rw [hval] at hr
    simp only [binderEnc]
    cases kind with
    | domain =>
      have := (List.mem_filter.mp (List.mem_of_getElem? hb)).2
      simp at this
    | bool =>
      simp only [boolValues, hidx, bools, decB, hport, hval]
      simp only [Tools.ShippingMuxLoweringSoundness.encodeBool]
      simp only at hr
      split <;> simp_all <;> omega
    | bits n =>
      simp only [bitValues, hidx, bits, decV, hport, hval]
      simp only at hr
      simp [Nat.mod_eq_of_lt hr]
  obtain ⟨result, hev, hres, _, _, hwe, _, _, _⟩ := vals bools bits env mems hsi
  refine ⟨result, ?_, ?_⟩
  · have : Sparkle.IR.RegDedup.declWidth m = moduleWidths m := by
      rw [← hwe]; rfl
    rw [this]; exact hev
  · rw [hres, hF vs hP]

/-- **A gate child at the full entry.** A run of the full entry on a
declaration the unified gate accepts returns a module that — when the run's
zero-width cleanup changes nothing — computes `F` on its argument ports, `F`
being the term's value on them decoded (`ChildFn`, as `machine_linked` uses
it): the gate analogue of `child_full`. -/
theorem gate_child_full {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Design}
    {value dom : Lean.Expr} {bs : List (Name × MixedGateBinder)}
    {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {srt : SType} {e : Term srt}
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (entry : EntryDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs,
      quote dom (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) e))
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hv : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j)))
    {F : List Nat → Nat}
    (hF : ∀ vs, InRange vs (bs.filter fun b => b.2 != .domain) →
      F vs = (pack srt (eval (fun j => decB bs vs (bpos j)) (fun j w => decV bs vs (vpos j) w) e)).toNat) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw = raw →
        ChildFn b (fun vs => InRange vs (bs.filter fun b => b.2 != .domain)) F) := by
  obtain ⟨M, D, w1, hcore, hpost⟩ := Tools.ShippingMachineShipping.synthesizeCombinational_checked hr
  obtain ⟨ids, cache, nd, len, vals, ins, positive⟩ := gate_core_facts hcore entry old peel he hb hv
  obtain ⟨hfn, hall⟩ := gate_childFn nd len vals ins positive hF
  exact ⟨M, hpost, fun hdz => childFn_full hfn hall hpost hdz⟩

/-! ## The positions of a generated instance, by evaluation -/

/-- The Bool positions `ps` of the binders, checked by evaluation. -/
def boolPositionsOk (bs : List (Name × MixedGateBinder)) (ps : List Nat) : Bool :=
  ps.all fun p => match bs[p]? with
    | some (_, .bool) => true
    | _ => false

/-- The BitVec positions `ps` of widths `ws`, checked by evaluation. -/
def bitsPositionsOk (bs : List (Name × MixedGateBinder)) (ps ws : List Nat) : Bool :=
  ps.length == ws.length && (ps.zip ws).all fun (p, w) => match bs[p]? with
    | some (_, .bits n) => n == w
    | _ => false

theorem bool_positions {bs : List (Name × MixedGateBinder)} {ps : List Nat}
    (h : boolPositionsOk bs ps = true) :
    ∀ j, j < ps.length → ∃ name, bs[ps.getD j 0]? = some (name, .bool) := by
  intro j hj
  unfold boolPositionsOk at h
  have hm := List.all_eq_true.mp h (ps.getD j 0) (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj)
  revert hm
  cases hb : bs[ps.getD j 0]? with
  | none => simp
  | some b =>
    obtain ⟨name, kind⟩ := b
    cases kind <;> simp

theorem bits_positions {bs : List (Name × MixedGateBinder)} {ps ws : List Nat}
    (h : bitsPositionsOk bs ps ws = true) :
    ∀ j, j < ps.length → ∃ name, bs[ps.getD j 0]? = some (name, .bits (ws.getD j 0)) := by
  intro j hj
  unfold bitsPositionsOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hl, h⟩ := h
  have hjw : j < ws.length := by omega
  have hz : (ps.getD j 0, ws.getD j 0) ∈ ps.zip ws := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hjw, Option.getD_some, Option.getD_some]
    have : (ps.zip ws)[j]'(by simp; omega) = (ps[j], ws[j]) := List.getElem_zip
    rw [← this]; exact List.getElem_mem _
  have hm := List.all_eq_true.mp h _ hz
  revert hm
  cases hb : bs[ps.getD j 0]? with
  | none => simp
  | some b =>
    obtain ⟨name, kind⟩ := b
    cases kind with
    | bits n => simp only [beq_iff_eq]; intro hn; exact ⟨name, by rw [hn]⟩
    | _ => simp

end Tools.ShippingGateChild
