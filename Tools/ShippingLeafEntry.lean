import Tools.ShippingLeafTyped
import Tools.ShippingPortsMatchRawLeaf
import Tools.ShippingMachineShipsW
import Tools.ShippingMachineShipsComb
import Tools.ShippingDesignSV

/-! # A LEAF register machine as an ENTRY: the three check premises of `machine_ships_wired` (G1, round par/a-23)

`f.machine_ships_wired` (`Tools.ShippingMachineShipsW.machine_ships_wired`,
`Tools/ShippingMachineShipsW.lean` 41–74) ends, under `∃ raw`, in

    ∀ wof, simpleBody b = false →
      seqCheck wof (weOf wof) (checkedOptimize b).body = true →
      ((seqNames (checkedOptimize b).body).all fun n =>
        declWidth (checkedOptimize b) n == weOf wof n) = true →
      MachineShips declName d (dropZeroWidthModule raw) b (checkedOptimize b) wof dom src

Three check premises. This file derives them — at the emitter's own width
map `wof = wofOf (checkedOptimize b)` — from the run of the full entry of a
leaf register machine (`LeafKid`: no call, a slot), as far as the built
statements go. They do NOT go all the way: TWO facts about the compiler's
post-passes are missing, and they stay hypotheses here, each in the form a
fallback guard would prove.

## What is derived from the run, with no hypothesis about a module

* `leaf_entry_raw`: for the module `b` the full entry returns —
  `b.body.all seqStmtOk`, conjuncts 2 and 3 of `textCheckI` AT `b`
  (`seqCheck (wofOf b) (weS b) b.body`, the width tables on `seqNames`), and
  `b = m0 ∨ b = mergeChecked m0` for a module `m0` with a register. (The
  entry form of what `leaf_real_kidK_reg` has for a CHILD; the merged case by
  `mergeChecked_print`, the guard of round par/a-1.)

## What is NOT derived, and why

`checkedOptimize` (`Sparkle/IR/RefineCheck.lean` 381–396) has, for an
assignments-and-registers body that is not of the simple shape, the branch

    else if m.body.all seqStmtOk then
      if RefineCheck.refineCheck m o then o else m          -- o = optimizeModule m

* **(G-opt) the accepted optimizer candidate of an instance-free module is
  not print-guarded.** The instance branch keeps a candidate only through
  `keepGuarded` (which asks `printOk`); this branch asks `refineCheck` only,
  and `refineCheck` has no name / declaredness / operand-width conjunct
  (`docs/parallel/G1-designCheck-text.md`, section D). So conjuncts 2 and 3
  at `checkedOptimize b` follow only when `checkedOptimize b = b`. Missing
  statement:

      checkedOptimize b = b ∨ printOk (checkedOptimize b) = true
        (for b.body.all seqStmtOk = true, simpleBody b = false)

  Here: hypothesis `hoptPrint`. With `&& PrintGuard.printOk o` in that
  branch it is the analogue of `mergeChecked_print`. NOTE: where the
  candidate IS accepted, `hoptPrint` is `printOk` of the shipped module —
  the content of the two text checks. It removes nothing for such a
  declaration; it only says where the obligation sits.

* **(G-reg) the checked merge is not known to keep a register.**
  `simpleBody b = false` holds when `b` has a non-assignment statement.
  `m0` has a register; `b = mergeChecked m0` is `m0` or the merge accepted by
  `refineCheck m0 b && masksKept && printOk`. `refineCheck m o` pairs every
  register of `o` with one of `m` (`RefineCheck.lean` 161–168) — not the
  converse: it accepts an `o` with no register. That `mergeDuplicatesRaw`
  keeps one (it aliases duplicates to a representative) is not a theorem
  (`mergeDuplicatesParts` is an `Id.run do` over hash maps). Missing
  statement:

      m.body.all isAssign = false → (mergeChecked m).body.all isAssign = false

  Here: hypothesis `hmergeReg`.

Also: `leaf_run_typedIn` asks `InvW mref cref w` of the run's start world
(it uses it once, as `ChildBnd.of_invW mctx cctx hw`,
`Tools/ShippingLeafTyped.lean` 377). So do the theorems here. `ChildBnd` is
the allowed boundary; generalising that one hypothesis is a one-line change
of an existing file (not made here).

## The statements

* `leaf_entry_textChecks`: the three antecedents at
  `wofOf (checkedOptimize b)`, from `LeafKid`, the run, `InvW`, `hmergeReg`,
  `hoptPrint`.
* `leaf_entry_textChecks_id`: the same when neither post-pass changed the
  module (no gap hypothesis of the two forms above; two equations instead).
* `leaf_entry_ships_of`: the wired endpoint's conclusion with its three
  antecedents discharged at `wofOf (checkedOptimize b)`.
* `leaf_entry_ships`: `machine_ships_wired` with those hypotheses instead of
  the three checks.
* `designSV0_of_leaf` (pure): for an assignments-and-registers module, a run
  of its emitted text IS `DesignSV C 0` of it, for every child map — the
  oracle seeding is the seeding (`oracle_seq`), the three instance clauses
  are vacuous.

The SLOTLESS case (`machine_ships_comb`, `simpleBody b = true`) is NOT
written: see `docs/parallel/A-leaf-entry.md`.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingLeafEntry
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingSeqOptSoundness Tools.ShippingRefineSoundness
open Tools.ShippingSeqSVSoundness Tools.ShippingPipelineSoundness
open Sparkle.IR.RegDedup (declWidth)

/-! ## Pure -/

/-- A body with a statement that is not an assignment is not of the simple
shape. -/
theorem simpleBody_false_of {m : Sparkle.IR.AST.Module}
    (h : m.body.all Sparkle.IR.RegDedup.isAssign = false) :
    Sparkle.IR.OptCheck.simpleBody m = false := by
  cases hs : Sparkle.IR.OptCheck.simpleBody m with
  | false => rfl
  | true =>
    have h1 := Tools.ShippingMachineShipsComb.simpleBody_assigns hs
    exact Tools.ShippingChecksDerived.ff_absurd (h.symm.trans h1)

/-- **Conjuncts 2 and 3 of `textCheckI` of the full entry's module**, from
the typed cleaned module with a register: the module itself, or its checked
merge — unchanged, or accepted with the print guard. -/
theorem text_post_reg {m0 b : Sparkle.IR.AST.Module}
    (hpost : b = m0 ∨ b = Sparkle.IR.RefineCheck.mergeChecked m0)
    (hT : Tools.ShippingTextTyped.TypedIn m0)
    (hna : m0.body.all Sparkle.IR.RegDedup.isAssign = false) :
    Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
        (Tools.ShippingDesignSV.weS b) b.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames b.body).all
        (fun x => Sparkle.IR.RegDedup.declWidth b x == Tools.ShippingDesignSV.weS b x) =
          true := by
  rcases hpost with e | e
  · rw [e]
    exact hT.seqCheck
  · rcases Sparkle.IR.RefineCheck.mergeChecked_print hna with e' | hp
    · rw [e, e']
      exact hT.seqCheck
    · rw [e]
      exact Tools.ShippingPrintGuard.printOk_sound hp

/-- Conjuncts 2 and 3 of the SHIPPED module from the same of the input
module, when the shipped module is the input module or passes the print
guard (`Tools.ShippingTextShipped.text_shipped_of` with the disjunction as a
hypothesis instead of `hierGate`). -/
theorem text_shipped_of_print {b : Sparkle.IR.AST.Module}
    (hraw : Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
        (Tools.ShippingDesignSV.weS b) b.body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames b.body).all
        (fun x => Sparkle.IR.RegDedup.declWidth b x == Tools.ShippingDesignSV.weS b x) = true)
    (hopt : Sparkle.IR.OptCheck.checkedOptimize b = b ∨
      Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize b) = true) :
    Tools.SVParser.EmitSem.seqCheck
        (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b))
        (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b))
        (Sparkle.IR.OptCheck.checkedOptimize b).body = true ∧
      (Tools.ShippingSeqSVSoundness.seqNames (Sparkle.IR.OptCheck.checkedOptimize b).body).all
        (fun x => Sparkle.IR.RegDedup.declWidth (Sparkle.IR.OptCheck.checkedOptimize b) x ==
          Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) x) = true := by
  rcases hopt with e | e
  · rw [e]
    exact hraw
  · exact Tools.ShippingPrintGuard.printOk_sound e

/-- The shipped module of an assignments-and-registers module not of the
simple shape is an assignments-and-registers module. -/
theorem checkedOptimize_seqBody {b : Sparkle.IR.AST.Module}
    (hs : Sparkle.IR.OptCheck.simpleBody b = false)
    (hok : b.body.all Sparkle.IR.OptCheck.seqStmtOk = true) :
    (Sparkle.IR.OptCheck.checkedOptimize b).body.all Sparkle.IR.OptCheck.seqStmtOk = true := by
  rcases Sparkle.IR.OptCheck.checkedOptimize_seqOk hs hok with h | h
  · exact Tools.ShippingMachineShipping.refineCheck_stmtOk_o h
  · rw [h]
    exact hok

/-! ## From the run of the full entry -/

/-- **The full entry's module of a leaf register machine**, over every run:
its statement kinds, conjuncts 2 and 3 of `textCheckI` at the module itself,
and that it is a module with a register or the checked merge of one. No
hypothesis about a module. -/
theorem leaf_entry_raw {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : Tools.ShippingChildInv.InvW mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w') :
    b.body.all Sparkle.IR.OptCheck.seqStmtOk = true ∧
      (Tools.SVParser.EmitSem.seqCheck (Tools.ShippingDesignSV.wofOf b)
          (Tools.ShippingDesignSV.weS b) b.body = true ∧
        (Tools.ShippingSeqSVSoundness.seqNames b.body).all
          (fun x => Sparkle.IR.RegDedup.declWidth b x == Tools.ShippingDesignSV.weS b x) =
            true) ∧
      ∃ m0 : Sparkle.IR.AST.Module,
        (b = m0 ∨ b = Sparkle.IR.RefineCheck.mergeChecked m0) ∧
          m0.body.all Sparkle.IR.RegDedup.isAssign = false := by
  obtain ⟨m0, hpost, hT, -, -, hs, hna⟩ :=
    Tools.ShippingLeafTyped.leaf_run_typedIn (nDecl := dk.nIn) dk K.ok K.body K.calls K.dom
      K.leaf K.ss K.outTy hw hr K.entry (K.closes mctx cctx) K.outName K.outScalar
  have hna' : m0.body.all Sparkle.IR.RegDedup.isAssign = false := hna K.slots
  have htext := text_post_reg hpost hT hna'
  exact ⟨hs, htext, m0, hpost, hna'⟩

/-- **The three check premises of `machine_ships_wired`, at the emitter's own
width map of the shipped module**, from the run of the full entry of a leaf
register machine. Two hypotheses are NOT derived (file header): `hmergeReg`
(the checked merge keeps a non-assignment statement) and `hoptPrint` (the
shipped module is the input module or passes the print guard). -/
theorem leaf_entry_textChecks {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : Tools.ShippingChildInv.InvW mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w')
    (hmergeReg : ∀ m0 : Sparkle.IR.AST.Module, b = Sparkle.IR.RefineCheck.mergeChecked m0 →
      m0.body.all Sparkle.IR.RegDedup.isAssign = false →
      b.body.all Sparkle.IR.RegDedup.isAssign = false)
    (hoptPrint : Sparkle.IR.OptCheck.checkedOptimize b = b ∨
      Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize b) = true) :
    Sparkle.IR.OptCheck.simpleBody b = false ∧
      Tools.SVParser.EmitSem.seqCheck
        (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b))
        (Tools.SVParser.EmitSem.weOf
          (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)))
        (Sparkle.IR.OptCheck.checkedOptimize b).body = true ∧
      ((Tools.ShippingSeqSVSoundness.seqNames (Sparkle.IR.OptCheck.checkedOptimize b).body).all
        fun n => Sparkle.IR.RegDedup.declWidth (Sparkle.IR.OptCheck.checkedOptimize b) n ==
          Tools.SVParser.EmitSem.weOf
            (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)) n) = true := by
  obtain ⟨-, htext, m0, hpost, hna⟩ := leaf_entry_raw K hw hr
  have hsB : Sparkle.IR.OptCheck.simpleBody b = false := by
    rcases hpost with e | e
    · rw [e]
      exact simpleBody_false_of hna
    · exact simpleBody_false_of (hmergeReg m0 e hna)
  obtain ⟨h2, h3⟩ := text_shipped_of_print htext hoptPrint
  exact ⟨hsB, h2, h3⟩

/-- The same when neither post-pass changed the module: the merge returned
its input and the optimizer's candidate was not kept. -/
theorem leaf_entry_textChecks_id {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : Tools.ShippingChildInv.InvW mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w')
    (hmergeId : ∀ m0 : Sparkle.IR.AST.Module, b = Sparkle.IR.RefineCheck.mergeChecked m0 →
      b = m0)
    (hsame : Sparkle.IR.OptCheck.checkedOptimize b = b) :
    Sparkle.IR.OptCheck.simpleBody b = false ∧
      Tools.SVParser.EmitSem.seqCheck
        (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b))
        (Tools.SVParser.EmitSem.weOf
          (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)))
        (Sparkle.IR.OptCheck.checkedOptimize b).body = true ∧
      ((Tools.ShippingSeqSVSoundness.seqNames (Sparkle.IR.OptCheck.checkedOptimize b).body).all
        fun n => Sparkle.IR.RegDedup.declWidth (Sparkle.IR.OptCheck.checkedOptimize b) n ==
          Tools.SVParser.EmitSem.weOf
            (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)) n) = true :=
  leaf_entry_textChecks K hw hr
    (fun m0 e hna => by
      rw [hmergeId m0 e]
      exact hna)
    (Or.inl hsame)

/-- The shipped module of a leaf register machine is an
assignments-and-registers module (under `hmergeReg` only). -/
theorem leaf_entry_shipped_seq {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {c : Name} {dk : Tools.ShippingMachineAuto.MachineData}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref c dk)
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : Tools.ShippingChildInv.InvW mref cref w)
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational c)
      mctx mref cctx cref w (b, design) w')
    (hmergeReg : ∀ m0 : Sparkle.IR.AST.Module, b = Sparkle.IR.RefineCheck.mergeChecked m0 →
      m0.body.all Sparkle.IR.RegDedup.isAssign = false →
      b.body.all Sparkle.IR.RegDedup.isAssign = false) :
    (Sparkle.IR.OptCheck.checkedOptimize b).body.all Sparkle.IR.OptCheck.seqStmtOk = true := by
  obtain ⟨hs, -, m0, hpost, hna⟩ := leaf_entry_raw K hw hr
  have hsB : Sparkle.IR.OptCheck.simpleBody b = false := by
    rcases hpost with e | e
    · rw [e]
      exact simpleBody_false_of hna
    · exact simpleBody_false_of (hmergeReg m0 e hna)
  exact checkedOptimize_seqBody hsB hs

/-! ## The wired endpoint without its three antecedents -/

/-- **The conclusion of `machine_ships_wired` with its three antecedents
discharged at the emitter's own width map.** `hships` is what
`f.machine_ships_wired` gives for the run; `hchk` is
`leaf_entry_textChecks`. -/
theorem leaf_entry_ships_of {declName : Name} {d : MachineData}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {b : Sparkle.IR.AST.Module}
    (hships : ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      ∀ (wof : String → Option Nat),
        simpleBody b = false →
        Tools.SVParser.EmitSem.seqCheck wof (Tools.SVParser.EmitSem.weOf wof)
          (checkedOptimize b).body = true →
        ((seqNames (checkedOptimize b).body).all fun n =>
          declWidth (checkedOptimize b) n == Tools.SVParser.EmitSem.weOf wof n) = true →
        MachineShips declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b
          (checkedOptimize b) wof dom src)
    (hchk : Sparkle.IR.OptCheck.simpleBody b = false ∧
      Tools.SVParser.EmitSem.seqCheck
        (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b))
        (Tools.SVParser.EmitSem.weOf
          (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)))
        (Sparkle.IR.OptCheck.checkedOptimize b).body = true ∧
      ((Tools.ShippingSeqSVSoundness.seqNames (Sparkle.IR.OptCheck.checkedOptimize b).body).all
        fun n => Sparkle.IR.RegDedup.declWidth (Sparkle.IR.OptCheck.checkedOptimize b) n ==
          Tools.SVParser.EmitSem.weOf
            (Tools.ShippingDesignSV.wofOf (Sparkle.IR.OptCheck.checkedOptimize b)) n) = true) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      MachineShips declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b
        (checkedOptimize b) (Tools.ShippingDesignSV.wofOf (checkedOptimize b)) dom src := by
  obtain ⟨raw, hpost, H⟩ := hships
  obtain ⟨h1, h2, h3⟩ := hchk
  exact ⟨raw, hpost, H (Tools.ShippingDesignSV.wofOf (checkedOptimize b)) h1 h2 h3⟩

/-- **A leaf register machine at the full entry, to the emitted Verilog at
the emitter's own width map — `machine_ships_wired` without its three check
premises.** Premises: the wired trace theorem of the declaration, the
premises about the declaration (`LeafKid`: decided data, the reflection, the
closing), the run, `InvW` at its start — and the two underived hypotheses
`hmergeReg`, `hoptPrint` (file header). -/
theorem leaf_entry_ships {declName : Name} (d : MachineData)
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      MachineTraceL declName d m design dom src (fun _ _ bits => bits) lsrc)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {b : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (K : Tools.ShippingPortsMatchRawLeaf.LeafKid mctx mref cctx cref declName d)
    (hw : Tools.ShippingChildInv.InvW mref cref w)
    (hr : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, design) w')
    (hmergeReg : ∀ m0 : Sparkle.IR.AST.Module, b = Sparkle.IR.RefineCheck.mergeChecked m0 →
      m0.body.all Sparkle.IR.RegDedup.isAssign = false →
      b.body.all Sparkle.IR.RegDedup.isAssign = false)
    (hoptPrint : Sparkle.IR.OptCheck.checkedOptimize b = b ∨
      Sparkle.IR.PrintGuard.printOk (Sparkle.IR.OptCheck.checkedOptimize b) = true) :
    ∃ raw : Sparkle.IR.AST.Module,
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) ∧
      MachineShips declName d (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw) b
        (checkedOptimize b) (Tools.ShippingDesignSV.wofOf (checkedOptimize b)) dom src :=
  leaf_entry_ships_of
    (Tools.ShippingMachineShipsW.machine_ships_wired d @soundL K.leaf K.slots K.ss K.outTy hr
      K.entry (K.closes mctx cctx))
    (leaf_entry_textChecks K hw hr hmergeReg hoptPrint)

/-! ## The design-level statement at depth 0 of a module without instances -/

/-- On an assignments-and-registers body there is no instance-driven wire:
the oracle seeding is the seeding. -/
theorem oracle_seq (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
    {body : List Sparkle.IR.AST.Stmt}
    (hs : body.all Sparkle.IR.OptCheck.seqStmtOk = true)
    (E : Nat → Sparkle.IR.Semantics.Env)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) :
    Tools.ShippingHierSVRun.oracle C body E seed = seed := by
  funext k st n
  have hb := Tools.ShippingLeafTyped.bodyInstOuts_seq C body hs
  first
    | (show (if (Tools.ShippingHierOpen.bodyInstOuts C body).contains n then E k n
          else seed k st n) = seed k st n
       rw [hb]
       rfl)
    | simp [Tools.ShippingHierSVRun.oracle, Tools.ShippingHierOpen.seedOuts, hb]

/-- **`DesignSV` at depth 0 of a module without instances is the run of its
own emitted text**, for every child map and every children's state: the
oracle seeding is the seeding, and the resolution, connection-width and
per-instance clauses are vacuous. -/
theorem designSV0_of_leaf
    (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv))
    {o : Sparkle.IR.AST.Module} (hs : o.body.all Sparkle.IR.OptCheck.seqStmtOk = true)
    {seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env} {T : Nat}
    {s : Tools.ShippingHierStateG.KState (Tools.ShippingHierStateG.KT 0)}
    {envs : List Sparkle.IR.Semantics.Env}
    (h : Tools.ShippingDesignSV.TextRun o seed T s.st s.mems envs) :
    Tools.ShippingDesignSV.DesignSV C 0 o seed T s envs := by
  have e := oracle_seq C hs (Tools.ShippingDesignSV.envAt envs T) seed
  have h' : Tools.ShippingDesignSV.TextRun o
      (Tools.ShippingHierSVRun.oracle C o.body (Tools.ShippingDesignSV.envAt envs T) seed)
      T s.st s.mems envs := by
    rw [e]
    exact h
  refine ⟨h', ?_, ?_, ?_⟩
  · intro mn iname conns hm
    exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hs _ hm)
  · intro mn iname conns child cwe hm
    exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hs _ hm)
  · intro mn iname conns child cwe hm
    exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp hs _ hm)

end Tools.ShippingLeafEntry
