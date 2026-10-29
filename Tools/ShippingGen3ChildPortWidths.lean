import Tools.ShippingGen2OneOut
import Tools.ShippingPortWidthsPure
set_option autoImplicit false
-- NOT BUILT (written without running Lean; the integrator builds it on the cluster).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # U-CHILD-PORTTYS (step 1, U-CHILD-PORTW-P): the served child's argument-port widths, as standalone facts
(scripts/gen3/UCHILD_PORTTYS_TABLE.md, approved as a scoped change-site table; issue `sparkle-gen3-uchild-porttys`)

**No interface change.** `ChildPortWidths` is defined HERE, in an independent file; `ChildShips`, `ChildRunN`,
`SeqChildRunN`, `CombChildRunN`, `ShipsRes`, `T1Hyp`, `DataOkB`, FG, GEN2_DEFS and PkgCompat are unchanged. Nothing here
is a conjunct of `ChildShips` yet (that is U-CHILD-PORTW-DEF, after review).

* `ChildPortWidths q mc` (table §1, variant W): width-only. The right-hand side is `Pkg.portWidths q` (Adapt:80) by
  definition; written inline (no Adapt import).
* `argPortWidths_of_eq`: a producer-local `argPorts m = machPorts c ids cache bs` gives the widths (`machPorts_tys`,
  PortWidthsPure:142-147, projected to widths).
* `childPortWidths_of_tys`: the type form (candidate T) implies W.
* **N-A** `argPorts_noCalls_of_wired`: the argument ports of a call-free machine module are its declaration's
  (LeafSeq:58-67, factored). `argPorts_noCalls_post`: the same after the post-processing `hpost` (LeafSeq:70-74).
* **N-B** `childPortWidths_of_composedNW`: the C6 child module's port widths (C6:29-56 premises; C6:57-85 with
  `machPorts_tys` in place of `machPorts_length`).
* **P1-P4**: each producer's width fact from (a subset of) that producer's existing premises:
  P1 `leaf_childPortWidths` (Leaf:241-266), P2 `slotlessLeaf_childPortWidths` (SlotlessLeaf:283-), both through
  `noCalls_childPortWidths`; P3 `memParent_childPortWidths` (MemShips:39-), P4 `oneOut_childPortWidths`
  (OneOut:288-332), both through N-B. Premises of the producers that the width fact does not use are left out.

**Not claimed.** P1-P4 alone do NOT complete the FG supply (M3/S3/M4 producers, UCHILD table impact rows, UNCHECKED).
`ChildPortWidths` is the sufficient width guarantee used here; its minimality is not proved. The consumer's L6 / source
width equality stays in SRC-ARGW. This is the CHILD side; UARGW supplies the parent side, UARITY the index range; only
with SRC-ARGW's width equality for the same call do they reach `callArgsOkAt`.

**AUDIT.** Expected types: Tests/Gen3/ChildPortWidthsCheck.lean (mechanical, with mutants). Axioms: standard only. -/

namespace Tools.ShippingGen3ChildPortWidths
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingGen2
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildBndCore (dv)

/-! ## The definition (width-only; NOT a conjunct of `ChildShips`) -/

/-- G-CHILD-PORTW: the served module's argument ports have the package's declared port widths. -/
def ChildPortWidths {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (mc : Module) : Prop :=
  (argPorts mc).map (fun p => p.ty.bitWidth) = q.ports.map (fun b => (kindTy b.2).bitWidth)

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

/-- The type form (candidate T) implies the width form (W). The converse is not claimed. -/
theorem childPortWidths_of_tys {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (mc : Module)
    (h : (argPorts mc).map (fun p => p.ty) = q.ports.map (fun b => kindTy b.2)) :
    ChildPortWidths q mc := by
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

/-! ## P1-P4: each producer's width fact -/

variable {ι : Type} {dom : ι → DomainConfig}

/-- The call-free producers (P1, P2): the widths from the trace's `MachineWired`, N-A and the post-processing. -/
theorem noCalls_childPortWidths (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    ChildPortWidths p b := by
  obtain ⟨ids, _, len, cache, regs, _, _, lets, _, wired, _⟩ := id hL
  have hargs := argPorts_noCalls_post wired hnoI (data_hSlen p.d hok hSS) (data_hLlen p.d hok) houtTy hpost
  have hlenIn : p.d.bsIn.length ≤ ids.length := by
    rw [len]; simp only [Tools.ShippingMachineAuto.MachineData.bsIn, List.length_take]; omega
  unfold ChildPortWidths Pkg.ports
  rw [htake]
  exact argPortWidths_of_eq hargs hlenIn

/-- **P1** the register leaf (`leaf_childShips_of_LB`, Leaf:241-266; its premises `hL`, `hnoI`, `hok`, `hSS`,
`houtTy`, `htake`, `hpost`). -/
theorem leaf_childPortWidths (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    ChildPortWidths p b :=
  noCalls_childPortWidths p hL hnoI hok hSS houtTy htake hpost

/-- **P2** the slotless leaf (`slotlessLeaf_childShips_of_LB`, SlotlessLeaf:283-; its premises `hL`, `hnoI`, `hsl0`,
`hok`, `hSS`, `houtTy`, `htake`, `hpost`). -/
theorem slotlessLeaf_childPortWidths (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) :
    ChildPortWidths p b :=
  noCalls_childPortWidths p hL hnoI hok hSS houtTy htake hpost

/-- **P3** memory parents (`memParent_childShips`, MemShips:39-; C8's `ComposedNW` then N-B). -/
theorem memParent_childPortWidths {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context} {w : Void IO.RealWorld}
    {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p) (hmo : MemOrigin p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hmd : ∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) (n : Nat) :
    ChildPortWidths p b := by
  obtain ⟨hok, hco, hslots, houtTy, hdomB⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have hNW := pkg_memComposedNW L p hA hfe hkD hdomB hIlen hSL hSlen hLlen hNIn hmd hmo n ran
  have hI0 : 0 < p.d.shape.insts.length := by
    cases h : p.d.shape.insts with
    | nil => exact absurd h hins
    | cons _ _ => simp
  exact childPortWidths_of_composedNW n houtTy (ok_outNameOk p.d hok) hsl hI0 hkD hIlen hSL hSlen hLlen hNIn
    hNW hpost

/-- **P4** one-output parents (`oneOut_childShips`, OneOut:288-332; `oneOut_composedNW` then N-B). -/
theorem oneOut_childPortWidths {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context} {w : Void IO.RealWorld} {raw b : Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat) :
    ChildPortWidths p b := by
  obtain ⟨hok, hco, hslots, houtTy, -⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have hNW := oneOut_composedNW L P p hdata hins hsimple hA ran hdec h n
  have hI0 : 0 < p.d.shape.insts.length := by
    cases h : p.d.shape.insts with
    | nil => exact absurd h hins
    | cons _ _ => simp
  exact childPortWidths_of_composedNW n houtTy (ok_outNameOk p.d hok) hsl hI0 hkD hIlen hSL hSlen hLlen hNIn
    hNW hpost

end Tools.ShippingGen3ChildPortWidths
