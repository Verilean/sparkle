import Tools.ShippingGen2C6
import Tools.ShippingGen2MemData
import Tools.ShippingPortWidthsPure
set_option autoImplicit false
-- WRITTEN, NOT BUILT (2026-10-29). To be confirmed by `kjob lake build Tools.ShippingGen3PortWidthsCore`.
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # U-CHILD-PORTTYS core split (scripts/gen3/UCHILD_PORTTYS_TABLE.md rev3 §R3.4): move-ready copy of N-A/N-B

The pure part of Tools/ShippingGen3ChildPortWidths.lean, in a file that the `ChildShips` PRODUCERS can import at the
shared edit (S3 of rev3 §R3.3): its imports are only `Tools.ShippingGen2C6`, `Tools.ShippingGen2MemData` and
`Tools.ShippingPortWidthsPure`, none of which imports Leaf, SlotlessLeaf, MemShips, OneOut or GroupServed (checked
by an import-closure script over the source tree at e8a41c70; to be confirmed by the build).

**Nothing is moved yet.** Tools/ShippingGen3ChildPortWidths.lean is UNCHANGED and keeps its own copies. Plan at the
shared edit: `ChildPortWidths` moves into Tools/ShippingGen2Defs.lean; ChildPortWidths.lean switches its import to this
file and its N-A/N-B copies are deleted (P1-P4 stay as thin corollaries).

**Differences from the ChildPortWidths.lean copies (statements only; the proofs are verbatim):**
* namespace `Tools.ShippingGen3PortWidthsCore` (no clash with the built copies when both are imported);
* no `ChildPortWidths` definition here (it belongs in Defs); the two lemmas that concluded `ChildPortWidths`
  (`childPortWidths_of_tys`, `noCalls_childPortWidths`) conclude its BODY
  `(argPorts b).map (fun x => x.ty.bitWidth) = p.ports.map (fun b => (kindTy b.2).bitWidth)`, which is
  `ChildPortWidths p b` by unfolding once it is in Defs;
* P1-P4 are not copied (they are corollaries of `noCalls_childPortWidths` and N-B under the producers' premises).

**Not claimed.** These lemmas do not supply the S5 slotless parents with calls (`slots = []`, `insts ≠ []`): N-A needs
`insts = []`, N-B needs `slots ≠ []` (rev3 §R3.1). -/

namespace Tools.ShippingGen3PortWidthsCore
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingGen2

/-! ## Widths from a producer-local port identity -/

/-- `machPorts_tys` projected to widths, for a module whose argument ports ARE the declaration's ports. -/
theorem argPortWidths_of_eq {declName : Name} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    {bs : List (Name × MixedGateBinder)} {m : Module}
    (h : argPorts m = machPorts declName ids cache bs) (hl : bs.length ≤ ids.length) :
    (argPorts m).map (fun p => p.ty.bitWidth) =
      (bs.filter fun b => b.2 != .domain).map (fun b => (kindTy b.2).bitWidth) := by
  have ht := congrArg (List.map (fun t : Sparkle.IR.Type.HWType => t.bitWidth))
    (Tools.ShippingPortWidthsPure.machPorts_tys declName ids cache bs hl)
  simp only [List.map_map] at ht
  rw [h]
  exact ht

/-- The type form (candidate T) implies the width form (W), stated as `ChildPortWidths`' body. The converse is not
claimed. -/
theorem childPortWidths_of_tys {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (mc : Module)
    (h : (argPorts mc).map (fun p => p.ty) = q.ports.map (fun b => kindTy b.2)) :
    (argPorts mc).map (fun x => x.ty.bitWidth) = q.ports.map (fun b => (kindTy b.2).bitWidth) := by
  have ht := congrArg (List.map (fun t : Sparkle.IR.Type.HWType => t.bitWidth)) h
  simp only [List.map_map] at ht
  exact ht

/-! ## N-A: call-free modules -/

/-- **N-A**: the argument ports of a call-free machine module are its declaration's ports (LeafSeq:58-67, factored). -/
theorem argPorts_noCalls_of_wired {declName : Name} {d : MachineData} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName d.shape ids cache m dsn regs lets)
    (hnoI : d.shape.insts = []) (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets) :
    argPorts m = machPorts declName ids cache d.bsIn := by
  obtain ⟨-, -, -, -, -, -, -, -, hins, -⟩ := wired
  -- LeafSeq:58-65, verbatim
  have hbsIn : d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length -
      d.shape.layout.lets) = d.bsIn := by
    have hb := d.binders_split
    rw [← hSlen, ← hLlen]
    conv => lhs; rw [hb]
    simp only [List.length_append]
    rw [show d.bsIn.length + d.slotBs.length + d.letBs.length - d.slotBs.length - d.letBs.length =
      d.bsIn.length by omega, List.append_assoc, List.take_left]
  unfold Tools.ShippingMachineCompose.argPorts
  rw [hins hnoI, hbsIn]

/-- N-A after the post-processing `hpost` (LeafSeq:70-74: the cleanup and the checked merge keep the inputs). -/
theorem argPorts_noCalls_post {declName : Name} {d : MachineData} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {raw b : Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName d.shape ids cache raw dsn regs lets)
    (hnoI : d.shape.insts = []) (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    argPorts b = machPorts declName ids cache d.bsIn := by
  have hargs := argPorts_noCalls_of_wired wired hnoI hSlen hLlen
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hclean, -⟩ := wired
  obtain ⟨⟨-, -, hi, -⟩, -⟩ := hclean hnoI houtTy
  have hbIn : b.inputs = raw.inputs := by
    rcases hpost with rfl | rfl
    · exact hi
    · exact (Sparkle.IR.RefineCheck.mergeChecked_ports _).1.trans hi
  rw [← hargs]
  unfold Tools.ShippingMachineCompose.argPorts
  rw [hbIn]

/-! ## N-B: the C6 child module -/

/-- **N-B**: the port widths of the C6 child module (C6:29-56 premises in C6's order, without the run-only ones
`hextB`, `hext`, `i`, `dsn`, `hEA`, `hNI`; proof C6:57-85 with `machPorts_tys` in place of `machPorts_length`). -/
theorem childPortWidths_of_composedNW (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Nat → Signal (dom i) Bool}
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl : d.shape.layout.slots ≠ []) (hI0 : 0 < d.shape.insts.length)
    (hkD : kD ≤ d.bsIn.length) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    {mc raw : Module} {D : Design}
    (hcomp : Tools.ShippingMachineDepthRun.ComposedNW n c d kD raw D dom src ext extB)
    (hpost : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      mc = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    (argPorts mc).map (fun p => p.ty.bitWidth) =
      ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).map (fun b => (kindTy b.2).bitWidth) := by
  -- C6:57-85
  obtain ⟨ids, _nd, len, cache, regs, _, _, lets, _, wired, _H⟩ := hcomp
  obtain ⟨_hnd_in, _hclk, _hrst, _hdisj, hargs, _hslotNI⟩ :=
    Tools.ShippingMachineDepthChild.calls_ports wired len hsl houtOk kD hkD hIlen hSL hSlen hLlen hNIn
  obtain ⟨-, -, _regsIn, -, calls1, -, -, _houts, -, -, -, -, gCalls, -, -, hcleanG, -, _hW1, -⟩ := wired
  obtain ⟨hb, _hw, hi, _ho⟩ := hcleanG houtTy
  -- the core module has an instance, so the full entry kept it (C6:65-77, verbatim)
  have hInst : Tools.ShippingMachineShipsHier.hasInst (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) := by
    by_cases hfe : d.shape.instFields = []
    · -- one-output combinational calls (`closeInsts`)
      obtain ⟨args, mc', st, _, hst, _, hcall⟩ := calls1 hfe 0 hI0
      obtain ⟨_, _, _, iname, _, _, _, _, _, _, _, _, _, heq⟩ := hcall
      subst heq
      exact ⟨_, _, _, by rw [hb]; exact hst⟩
    · obtain ⟨st, hst, args, outs, mc', hcall, _⟩ := gCalls hfe 0 hI0
      obtain ⟨_, _, iname, _, _, _, _, _, _, _, _, _, _, _, heq⟩ := hcall
      subst heq
      exact ⟨_, _, _, by rw [hb]; exact hst⟩
  have hmc : mc = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · rw [h, Tools.ShippingMachineDepthRun.mergeChecked_of_hasInst hInst]
  subst hmc
  have hargsMc : argPorts (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) = argPorts raw := by
    unfold Tools.ShippingMachineCompose.argPorts; rw [hi]
  have hlenIn : (d.bsIn.take kD).length ≤ ids.length := by
    rw [len, d.binders_split]; simp; omega
  -- C6:85 with `machPorts_tys` in place of `machPorts_length`
  rw [hargsMc]
  exact argPortWidths_of_eq hargs hlenIn

/-! ## The call-free producers' common lemma (P1/P2 are its instances) -/

/-- The call-free producers (P1, P2): the widths from the trace's `MachineWired`, N-A and the post-processing,
stated as `ChildPortWidths p b`'s body. -/
theorem noCalls_childPortWidths {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    (argPorts b).map (fun x => x.ty.bitWidth) = p.ports.map (fun b => (kindTy b.2).bitWidth) := by
  obtain ⟨ids, _, len, cache, regs, _, _, lets, _, wired, _⟩ := id hL
  have hargs := argPorts_noCalls_post wired hnoI (data_hSlen p.d hok hSS) (data_hLlen p.d hok) houtTy hpost
  have hlenIn : p.d.bsIn.length ≤ ids.length := by
    rw [len]; simp only [Tools.ShippingMachineAuto.MachineData.bsIn, List.length_take]; omega
  unfold Pkg.ports
  rw [htake]
  exact argPortWidths_of_eq hargs hlenIn

end Tools.ShippingGen3PortWidthsCore
