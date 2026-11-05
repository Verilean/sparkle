import Tools.ShippingGen2SlotlessParent
import Tools.ShippingGen3PortWidthsCore
import Tools.ShippingGen2GroupServed
set_option autoImplicit false
-- Built: g3nc-ce4c32a4 (clean snapshot, exit 0, standard axioms). No `sorry`, no `axiom`, no `native_decide`.

/-! # U-CHILD-PORTTYS N-C: the S5 slotless parents' port widths (scripts/gen3/UCHILD_PORTTYS_TABLE.md rev3 §R3.1)

Supplies N-C for the EXISTING producers B2 `oneOutSl_childShips` and B3 `groupSl_childShips`
(Tools/ShippingGen2SlotlessParentRun.lean), as required before S3 (§R3.1 "S3 gate"). **This is NOT the shared
change:** `ChildShips`, `ChildRunN`, Defs, FG, the compiler and GEN2_DEFS are unchanged; nothing here is a conjunct of
`ChildShips`. B2/B3 are unchanged.

* **N-C** `childPortWidths_of_composedNW_sl` (namespace `Tools.ShippingGen3SlotlessPortWidths`): N-B
  (`Tools.ShippingGen3PortWidthsCore.childPortWidths_of_composedNW`) with `hsl : slots ≠ []` replaced by
  `hsl0 : slots = []`. The proof is N-B's text with A1 `calls_ports_sl` (SlotlessParent, statement :68-85) in place of
  `calls_ports`; its fourth conjunct `argPorts m = machPorts declName ids cache (d.bsIn.take kD)` holds in BOTH case S
  (clock/reset inputs) and case C (neither). The other steps (`hInst` from `calls1`/`gCalls`, `hmc`, `hargsMc`,
  `hlenIn`) are N-B's verbatim; none uses `hsl`.
* **Corollaries** (namespace `Tools.ShippingGen2.SlotlessPortWidths`, conclusion
  `Tools.ShippingGen2.ChildPortWidths p b` (Defs)): `oneOutSl_childPortWidths` (B2's premises that the fact
  uses; `hNW` = `oneOut_composedNW …`, SlotlessParentRun:311) and `groupSl_childPortWidths` (B3's; `hNW` =
  `group_composedNW …`, :361). `hI0` from `hins` as B2/B3. Left out (unused by the width fact): `hext` (both), and for
  B3 `hA`, `ran` (with `mctx`, `cctx`, `w`).

No new premise. In particular no compat premise `hpw : ChildPortWidths …` is added to any producer.

At S3: B2/B3 prove the new conjunct by the same N-C term (all arguments are already in scope in their proofs);
`ChildPortWidths` then comes from Defs and these corollaries become thin or are deleted.

**AUDIT.** Expected types and mutants: Tests/Gen3/SlotlessPortWidthsCheck.lean. Axioms: standard only (to be confirmed
by the build). -/

namespace Tools.ShippingGen3SlotlessPortWidths
-- the opens of Tools/ShippingGen3PortWidthsCore.lean (the N-B statement elaborates under them)
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingGen2

/-- **N-C**: the port widths of a slotless parent with calls (N-B with A1 `calls_ports_sl` in place of
`calls_ports`). -/
theorem childPortWidths_of_composedNW_sl (n : Nat) {c : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Nat → Signal (dom i) Bool}
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (hsl0 : d.shape.layout.slots = []) (hI0 : 0 < d.shape.insts.length)
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
  -- N-B (PortWidthsCore) with A1 in place of `calls_ports`
  obtain ⟨ids, _nd, len, cache, regs, _, _, lets, _, wired, _H⟩ := hcomp
  -- CHANGED: A1 `calls_ports_sl` (5 conjuncts; the clock/reset disjunction is case S or case C)
  obtain ⟨_hnd_in, _hcr, _hdisj, hargs, _hslotNI⟩ :=
    Tools.ShippingGen2SlotlessParent.calls_ports_sl wired len hsl0 houtOk kD hkD hIlen hSL hSlen hLlen hNIn
  obtain ⟨-, -, _regsIn, -, calls1, -, -, _houts, -, -, -, -, gCalls, -, -, hcleanG, -, _hW1, -⟩ := wired
  obtain ⟨hb, _hw, hi, _ho⟩ := hcleanG houtTy
  -- the core module has an instance, so the full entry kept it (N-B verbatim)
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
  rw [hargsMc]
  exact Tools.ShippingGen3PortWidthsCore.argPortWidths_of_eq hargs hlenIn

end Tools.ShippingGen3SlotlessPortWidths

namespace Tools.ShippingGen2.SlotlessPortWidths
-- a sub-namespace (enclosing `Tools.ShippingGen2` names resolve), as Tools/ShippingGen3GroupPortWidths.lean;
-- a later B2/B3-side lemma of the same name cannot clash with these
-- GroupServed:247-266 (the subset used here)
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildBndCore (dv)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **N-C for B2**: the one-output slotless parent's port widths (`oneOutSl_childShips`' premises that the fact uses;
`hNW` as SlotlessParentRun:311, then N-C). -/
theorem oneOutSl_childPortWidths (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat) :
    ChildPortWidths p b := by
  -- SlotlessParentRun:304-311 verbatim
  obtain ⟨hok, hco, hslots, houtTy, -⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have hNW := oneOut_composedNW L P p hdata hins hsimple hA ran hdec h n
  -- SlotlessParentRun:320-323 verbatim
  have hI0 : 0 < p.d.shape.insts.length := by
    cases h : p.d.shape.insts with
    | nil => exact absurd h hins
    | cons _ _ => simp
  -- the ONE N-C application (the term the shared edit puts into `oneOutSl_childShips`)
  exact Tools.ShippingGen3SlotlessPortWidths.childPortWidths_of_composedNW_sl n houtTy (ok_outNameOk p.d hok) hsl0
    hI0 hkD hIlen hSL hSlen hLlen hNIn hNW hpost

/-- **N-C for B3**: the group slotless parent's port widths (`groupSl_childShips`' premises that the fact uses;
`hNW` as SlotlessParentRun:361, then N-C). -/
theorem groupSl_childPortWidths (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl0 : p.d.shape.layout.slots = [])
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc) :
    ChildPortWidths p b := by
  -- SlotlessParentRun:354-361 verbatim
  obtain ⟨hok, hco, hslots, houtTy, -⟩ := hdata.rows
  have hkD := data_hkD p.d p.kD hok hco
  have hIlen := data_hIlen p.d p.kD hok hco
  have hSL := data_hSL p.d hok
  have hSlen := data_hSlen p.d hok hslots
  have hLlen := data_hLlen p.d hok
  have hNIn := data_hNIn p.d p.kD hok hco hslots
  have hNW := group_composedNW L P p hdata hfe hdec n h
  -- SlotlessParentRun:373-376 verbatim
  have hI0 : 0 < p.d.shape.insts.length := by
    cases h : p.d.shape.insts with
    | nil => exact absurd h hins
    | cons _ _ => simp
  -- the ONE N-C application (the term the shared edit puts into `groupSl_childShips`)
  exact Tools.ShippingGen3SlotlessPortWidths.childPortWidths_of_composedNW_sl n houtTy (ok_outNameOk p.d hok) hsl0
    hI0 hkD hIlen hSL hSlen hLlen hNIn hNW hpost

end Tools.ShippingGen2.SlotlessPortWidths
