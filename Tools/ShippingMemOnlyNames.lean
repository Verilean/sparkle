import Tools.ShippingMemOnlyCloses
import Tools.ShippingNameDischarge
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # The closing of a MEMORY-ONLY parent without name hypotheses (round par/b-29)

WRITTEN, NOT BUILT.

`Tools.ShippingMemOnlyCloses.machineClosesAt_memOnly` (BUILT) asks two name
hypotheses over `memNameAt` (the name of call entry `k`'s memory module):

    hsep    : memNameAt d k = memNameAt d k' → (d.shape.insts[k]).1 = (d.shape.insts[k']).1
    hparent : memNameAt d k ≠ Sparkle.IR.ModuleName.ofDecl declName

Its header says why they stayed hypotheses: "`memNameAt` injective on
placeholders — it would need `Nat.repr` injective". They were discharged per
declaration: `sep_of_one` (one placeholder), a kernel string comparison of
two module names (`mixedMems`: `names_ne`), and `name_not_mem` / the
candidate renderings for the parent.

Since b7dc0ec4 the memory module's name is `ofMem combo aw dw` of the
injective encoding. Both hypotheses follow from the theorem's OTHER
hypothesis `hmem` (every call entry is a memory placeholder) alone:

* `memOnly_parent` — `memNameAt d k = ofMem cb aw dw`, and no declaration
  has a memory module's name (`ofDecl_ne_ofMem`): for EVERY parent
  declaration, whatever it is called. No hypothesis on names.
* `memOnly_sep` — `ofMem` is injective (`ofMem_injective`), and a
  placeholder is determined by its parameters (`memChild_name_of`: read off
  `memChild?`). No hypothesis on names.

So `machineClosesAt_memOnly_names` / `machineClosesAt_of_memOnlyData_names`
are the built theorems WITHOUT `hsep` and `hparent`, and with nothing in
their place. The remaining hypotheses are the built ones, unchanged
(reader data: `ok`, the body equation, `letsAliasOk`, `callsOk`, the slots,
the late binders, `instFields ≠ []`, `hmem`, the argument counts, the field
`out`, `hargsNd`, and `hout` — no output of the parent starts with `i`,
which is `hfresh`, a port-against-instance condition, NOT a declaration-name
condition; it stays).

Nothing here says anything about a parent with a memory entry beside a
declaration child (`machineClosesAt_of_kidsDM` with leaf callees: the
generator `Tools/ShippingNoPortsMemSeqCommand.lean`); the pure lemmas for
that are in `Tools/ShippingNameDischarge.lean`, the connection is not
written. -/
namespace Tools.ShippingMemOnlyNames
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingCallsGate Tools.ShippingCallsRunG Tools.ShippingSeqChildIface
open Tools.ShippingInstStmtG Tools.ShippingCallsStmtsG Tools.ShippingDesignWith
open Tools.ShippingDesignWithG Tools.ShippingCallsSeqKids
open Tools.ShippingCallsKidsD
open Tools.ShippingMemOnlyCloses (memNameAt memNameAt_eq machineClosesAt_memOnly
  machineClosesAt_of_memOnlyData MemOnlyCloseData)
open Sparkle.Compiler.MachMemory (memModule memChild? memChildName)
open Sparkle.IR.ModuleName (ofDecl ofMem)

/-- The built memory module is named by the memory form of the encoding
(`Sparkle/Compiler/MachMemory.lean`, `memModule`). -/
theorem memModule_name (cb : Bool) (aw dw : Nat) :
    (memModule cb aw dw).1.name = ofMem cb aw dw := by
  first
    | rfl
    | (unfold memModule; rfl)
    | simp [memModule]

/-- **What a memory placeholder is**: a name with a child is the placeholder
of that child's parameters (`memChild?` read backwards). -/
theorem memChild_shape {c : Name} {md : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design}
    (h : memChild? c = some md) :
    ∃ (cb : Bool) (aw dw : Nat), c = memChildName cb aw dw ∧ md = memModule cb aw dw := by
  unfold memChild? at h
  split at h
  · split at h
    · rename_i hk
      first
        | (have e := eq_of_beq hk; subst e; cases h; first | exact ⟨true, _, _, rfl, rfl⟩ | (subst_vars; exact ⟨true, _, _, rfl, rfl⟩))
        | (have e : _ = "combo" := by simpa using hk; subst e; cases h; first | exact ⟨true, _, _, rfl, rfl⟩ | (subst_vars; exact ⟨true, _, _, rfl, rfl⟩))
        | (subst hk; cases h; first | exact ⟨true, _, _, rfl, rfl⟩ | (subst_vars; exact ⟨true, _, _, rfl, rfl⟩))
    · split at h
      · rename_i hk
        first
          | (have e := eq_of_beq hk; subst e; cases h; first | exact ⟨false, _, _, rfl, rfl⟩ | (subst_vars; exact ⟨false, _, _, rfl, rfl⟩))
          | (have e : _ = "sync" := by simpa using hk; subst e; cases h; first | exact ⟨false, _, _, rfl, rfl⟩ | (subst_vars; exact ⟨false, _, _, rfl, rfl⟩))
          | (subst hk; cases h; first | exact ⟨false, _, _, rfl, rfl⟩ | (subst_vars; exact ⟨false, _, _, rfl, rfl⟩))
      · cases h
  · cases h

/-- A placeholder whose child is the module of `cb aw dw` is THE placeholder
of `cb aw dw`. -/
theorem memChild_name_of {c : Name} {cb : Bool} {aw dw : Nat}
    (h : memChild? c = some (memModule cb aw dw)) : c = memChildName cb aw dw := by
  obtain ⟨cb', aw', dw', hc, hm⟩ := memChild_shape h
  have hn0 : (memModule cb aw dw).1.name = (memModule cb' aw' dw').1.name :=
    congrArg (fun (m : Sparkle.IR.AST.Module × Sparkle.IR.AST.Design) => m.1.name) hm
  have hn : ofMem cb aw dw = ofMem cb' aw' dw' :=
    (memModule_name cb aw dw).symm.trans (hn0.trans (memModule_name cb' aw' dw'))
  obtain ⟨e1, e2, e3⟩ := Tools.ShippingModuleName.ofMem_injective hn
  subst e1
  subst e2
  subst e3
  exact hc

/-- The name of a memory entry's module, in the encoding's memory form. -/
theorem memNameAt_ofMem (d : MachineData) {k : Nat} (hk : k < d.shape.insts.length)
    {cb : Bool} {aw dw : Nat}
    (hc : memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw)) :
    memNameAt d k = ofMem cb aw dw :=
  (memNameAt_eq d hk hc).trans (memModule_name cb aw dw)

/-- **`hparent` of a memory-only parent**, for every parent declaration: no
memory module is named as a declaration. -/
theorem memOnly_parent (declName : Name) (d : MachineData)
    (hmem : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      ∃ (cb : Bool) (aw dw : Nat), memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw)) :
    ∀ (k : Nat), k < d.shape.insts.length → memNameAt d k ≠ ofDecl declName := by
  intro k hk e
  obtain ⟨cb, aw, dw, hc⟩ := hmem k hk
  exact Tools.ShippingModuleName.ofDecl_ne_ofMem declName cb aw dw
    (e.symm.trans (memNameAt_ofMem d hk hc))

/-- **`hsep` of a memory-only parent**: two entries whose memory modules have
one name are entries of one placeholder. -/
theorem memOnly_sep (d : MachineData)
    (hmem : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      ∃ (cb : Bool) (aw dw : Nat), memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw)) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), memNameAt d k = memNameAt d k' →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1 := by
  intro k hk k' hk' he
  obtain ⟨cb, aw, dw, hc⟩ := hmem k hk
  obtain ⟨cb', aw', dw', hc'⟩ := hmem k' hk'
  have hn : ofMem cb aw dw = ofMem cb' aw' dw' :=
    (memNameAt_ofMem d hk hc).symm.trans (he.trans (memNameAt_ofMem d hk' hc'))
  obtain ⟨e1, e2, e3⟩ := Tools.ShippingModuleName.ofMem_injective hn
  subst e1
  subst e2
  subst e3
  exact (memChild_name_of hc).trans (memChild_name_of hc').symm

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **`MachineClosesAt` of a memory-only parent, without name hypotheses**:
`machineClosesAt_memOnly` with `hsep` and `hparent` derived from `hmem`. -/
theorem machineClosesAt_memOnly_names {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (hmem : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      ∃ (cb : Bool) (aw dw : Nat), memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw))
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (d.shape.insts[k]).2.1.length = 4)
    (hfield : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" = "out")
    (hargsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 → k = k')
    (hout : ∀ o ∈ d.shape.layout.outs, o.name.toList.head? ≠ some 'i')
    (hagree : Tools.ShippingInstTagged.TagsAgree d.shape) :
    MachineClosesAt mctx mref cctx cref declName d.shape :=
  machineClosesAt_memOnly d ok hbody halias hC hslots hdomB hfne hmem hargsN hfield hargsNd
    (memOnly_sep d hmem) (memOnly_parent declName d hmem) hout hagree

/-- `hmem` in the general theorem's form, from the built `MemOnlyData` (one
pair of widths for all entries). -/
theorem memAll_of_data {d : MachineData} {nDecl aw dw : Nat}
    (D : Tools.ShippingMemOnly.MemOnlyData d nDecl aw dw) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length),
      ∃ (cb : Bool) (aw dw : Nat), memChild? (d.shape.insts[k]).1 = some (memModule cb aw dw) :=
  fun k hk => (D.mem k hk).elim fun cb h => Exists.intro cb (Exists.intro aw (Exists.intro dw h))

/-- **`MachineClosesAt` of a memory-only parent over the built `MemOnlyData`,
without name hypotheses**: `machineClosesAt_of_memOnlyData` with `hsep` and
`hparent` derived. For every parent declaration name. -/
theorem machineClosesAt_of_memOnlyData_names {declName : Name} {d : MachineData}
    {nDecl aw dw : Nat}
    (D : Tools.ShippingMemOnly.MemOnlyData d nDecl aw dw) (C : MemOnlyCloseData d) :
    MachineClosesAt mctx mref cctx cref declName d.shape :=
  machineClosesAt_of_memOnlyData D C
    (memOnly_sep d (memAll_of_data D)) (memOnly_parent declName d (memAll_of_data D))

end Tools.ShippingMemOnlyNames
