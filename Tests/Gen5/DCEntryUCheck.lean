import Lean
import Tools.ShippingGen5DCEntryU
import Tests.Gen3.ExpectedType
import Tests.Gen5.DeclConnectCheck
set_option autoImplicit false
-- Counts (agent incremental build, NOT clean; measured): TYPE 3 + self-comparison 3; SOURCE-PIN 5 + PIN-NEG 5; MUT 28 (thm1 12, thm2 4, thm3 12; single change); BLOCK 0; CONJ 0; AX 3 standard only; CLOSURE 3 roots. Binder comparisons pass via isDefEq only because of local abbrevs (Mod/Dsg/WE/En), logged as GEN3 DEFEQ.

/-! # DC-CONNECT U-CORENR: checks

TYPE: `ExpNC`/`ExpHL`/`ExpCT` written from the prose of the freeze §3 (not copied from the source), compared binder by binder; plus constant-type
pins of `postEntry_lookup_ne`, `core_closeInstsA`, `machineRunJQC_of_closesA`, `machineRanA_of_runJQC`, `Start`. MUTANT: well-typed
single-change variants rejected by the SAME comparator -- signature/defeq rejections, NOT semantic counterexamples. BLOCK: none. CONJ: none. -/
open Lean Meta Tests.Gen3.ExpectedType
open Tools.ShippingGen5DCEntryR (NoRawBelow)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingHierStateG (KState KT KSn runModuleTG)
open Sparkle.IR.Machine (moduleByName)

namespace Tests.Gen5.DCEntryUCheck

abbrev Mod := Sparkle.IR.AST.Module
abbrev Dsg := Sparkle.IR.AST.Design
abbrev WE := Sparkle.IR.Semantics.WEnv
abbrev En := Sparkle.IR.Semantics.Env

/-- EXPECTED: NoRawBelow for the core run's (raw, D) at every depth, from Start, the run, MachineDefines, MachineClosesAtA, insts ≠ [], instFields = []. -/
def ExpNC : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Mod} {D : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = []),
    ∀ k : Nat, NoRawBelow D raw.name k raw

/-- EXPECTED: lookup agreement away from raw.name from PostEntry. -/
def ExpHL : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : Tools.ShippingGen5DCEntryD.PostEntry b raw D D'),
    ∀ mn : String, mn ≠ raw.name →
      moduleByName D'.modules mn = moduleByName D.modules mn

/-- EXPECTED: run of raw.body over the D' child map equals the run over the D child map. -/
def ExpCT : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed T s =
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) raw.body seed T s

/-- MUTANT: hS dropped -/
def MutNCnoHS : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Mod} {D : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = []),
    ∀ k : Nat, NoRawBelow D raw.name k raw

/-- MUTANT: hdef dropped -/
def MutNCnoHdef : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Mod} {D : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = []),
    ∀ k : Nat, NoRawBelow D raw.name k raw

/-- MUTANT: hcl dropped -/
def MutNCnoHcl : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Mod} {D : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = []),
    ∀ k : Nat, NoRawBelow D raw.name k raw

/-- MUTANT: hins dropped -/
def MutNCnoHins : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Mod} {D : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hf : d.shape.instFields = []),
    ∀ k : Nat, NoRawBelow D raw.name k raw

/-- MUTANT: hf dropped -/
def MutNCnoHf : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Mod} {D : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ []),
    ∀ k : Nat, NoRawBelow D raw.name k raw

/-- MUTANT: hf replaced by instFields ≠ [] -/
def MutNCfNe : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Mod} {D : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields ≠ []),
    ∀ k : Nat, NoRawBelow D raw.name k raw

/-- MUTANT: raw.name replaced by declName.toString -/
def MutNCdeclName : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Mod} {D : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = []),
    ∀ k : Nat, NoRawBelow D declName.toString k raw

/-- MUTANT: depth fixed to 0 -/
def MutNCzero : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Mod} {D : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = []),
    NoRawBelow D raw.name 0 raw

/-- MUTANT: RunsTo ... [] true -/
def MutNCtrue : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Mod} {D : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] true) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = []),
    ∀ k : Nat, NoRawBelow D raw.name k raw

/-- MUTANT: Start replaced by JQC L.O 0 w alone -/
def MutNCjqcOnly : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Mod} {D : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingChildCacheA.JQC L.O 0 w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = []),
    ∀ k : Nat, NoRawBelow D raw.name k raw

/-- MUTANT: D replaced by an unrelated design -/
def MutNCunrel : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw : Mod} {D D2 : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = []),
    ∀ k : Nat, NoRawBelow D2 raw.name k raw

/-- MUTANT: NoRawBelow of a free module m2 instead of raw -/
def MutNCrawWrong : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {raw m2 : Mod} {D : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = []),
    ∀ k : Nat, NoRawBelow D raw.name k m2

/-- MUTANT: hne dropped -/
def MutHLnoHne : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : Tools.ShippingGen5DCEntryD.PostEntry b raw D D'),
    ∀ mn : String, 
      moduleByName D'.modules mn = moduleByName D.modules mn

/-- MUTANT: D' / D swapped in the conclusion -/
def MutHLswap : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : Tools.ShippingGen5DCEntryD.PostEntry b raw D D'),
    ∀ mn : String, mn ≠ raw.name →
      moduleByName D.modules mn = moduleByName D'.modules mn

/-- MUTANT: PostEntry b raw D' D -/
def MutHLpostSwap : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    (h : Tools.ShippingGen5DCEntryD.PostEntry b raw D' D),
    ∀ mn : String, mn ≠ raw.name →
      moduleByName D'.modules mn = moduleByName D.modules mn

/-- MUTANT: PostEntry dropped -/
def MutHLnoPost : Prop := ∀ {b raw : Mod} {D D' : Dsg}
    ,
    ∀ mn : String, mn ≠ raw.name →
      moduleByName D'.modules mn = moduleByName D.modules mn

/-- MUTANT: hpost dropped -/
def MutCTnoPost : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed T s =
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) raw.body seed T s

/-- MUTANT: hS dropped -/
def MutCTnoHS : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed T s =
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) raw.body seed T s

/-- MUTANT: hr dropped -/
def MutCTnoHr : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
     
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed T s =
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) raw.body seed T s

/-- MUTANT: hdef dropped -/
def MutCTnoHdef : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed T s =
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) raw.body seed T s

/-- MUTANT: hcl dropped -/
def MutCTnoHcl : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed T s =
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) raw.body seed T s

/-- MUTANT: hins dropped -/
def MutCTnoHins : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hf : d.shape.instFields = [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed T s =
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) raw.body seed T s

/-- MUTANT: hf dropped -/
def MutCTnoHf : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed T s =
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) raw.body seed T s

/-- MUTANT: (checkedOptimize b).body on the left only -/
def MutCTopt : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) (Sparkle.IR.OptCheck.checkedOptimize b).body seed T s =
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) raw.body seed T s

/-- MUTANT: right side over D' -/
def MutCTrhsD : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed T s =
      runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed T s

/-- MUTANT: sides swapped -/
def MutCTswap : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) raw.body seed T s =
      runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed T s

/-- MUTANT: T fixed to 0 -/
def MutCTzero : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D D')
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed 0 s =
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) raw.body seed 0 s

/-- MUTANT: PostEntry b raw D' D -/
def MutCTpostSwap : Prop := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {L : Tools.ShippingGen2.Laws mref cref} {mctx : Lean.Meta.Context} {cctx : Lean.Core.Context}
    {w w1 : Void IO.RealWorld} {declName : Lean.Name}
    {b raw : Mod} {D D' : Dsg}
    (d : Tools.ShippingMachineAuto.MachineData)
    (hS : Tools.ShippingGen2.Start L mctx cctx w)
    (hr : Tools.ShippingEntrySoundness.RunsTo
      (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : Tools.ShippingGen5DCEntryD.PostEntry b raw D' D)
    (hdef : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName d.shape)
    (hcl : Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) L.O mctx cctx declName d.shape)
    (hins : d.shape.insts ≠ [])
    (hf : d.shape.instFields = [])
    (n : Nat) (we : WE)
    (seed : Nat → (String → Nat) → En) (T : Nat)
    (s : KState (KT n)),
    runModuleTG (KSn (childMap D'.modules) n) we (childMap D'.modules) raw.body seed T s =
      runModuleTG (KSn (childMap D.modules) n) we (childMap D.modules) raw.body seed T s

/-! ## source pins: constant TYPES, written independently -/
def PinPLN : Prop := ∀ {b raw : Mod} {D D' : Dsg} {mn : String},
  (h : Tools.ShippingGen5DCEntryD.PostEntry b raw D D') → (hne : mn ≠ raw.name) →
    moduleByName D'.modules mn = moduleByName D.modules mn ∧ childMap D'.modules mn = childMap D.modules mn
def PinPLNMut : Prop := ∀ {b raw : Mod} {D D' : Dsg} {mn : String},
  (h : Tools.ShippingGen5DCEntryD.PostEntry b raw D' D) → (hne : mn ≠ raw.name) →
    moduleByName D'.modules mn = moduleByName D.modules mn ∧ childMap D'.modules mn = childMap D.modules mn

def PinStart : Type := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State},
  (L : Tools.ShippingGen2.Laws mref cref) → (mctx : Lean.Meta.Context) → (cctx : Lean.Core.Context) → (w : Void IO.RealWorld) → Prop
def PinStartMut : Type 1 := ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State},
  (L : Tools.ShippingGen2.Laws mref cref) → (mctx : Lean.Meta.Context) → (cctx : Lean.Core.Context) → (w : Void IO.RealWorld) → Type

def PinRRA : Prop := ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
  (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref),
  (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx) →
  (T : Tools.ShippingChildInvA.RefLawsATele O.quiet mref cref) →
  ∀ {D : Nat} {c : Lean.Name} {shape : Sparkle.Compiler.Elab.MachineShape} {M : Mod} {Ds : Dsg},
    (h : Tools.ShippingServedRealA.MachineRunJQC O mctx cctx (D + 1) c shape M Ds) →
    Tools.ShippingParentRanA.MachineRanA O mctx cctx c shape M Ds
def PinRRAMut : Prop := ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
  (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref),
  (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx) →
  (T : Tools.ShippingChildInvA.RefLawsATele O.quiet mref cref) →
  ∀ {D : Nat} {c : Lean.Name} {shape : Sparkle.Compiler.Elab.MachineShape} {M : Mod} {Ds : Dsg},
    (h : Tools.ShippingServedRealA.MachineRunJQC O mctx cctx D c shape M Ds) →
    Tools.ShippingParentRanA.MachineRanA O mctx cctx c shape M Ds

def PinMRJ : Prop := ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
  (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref),
  (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx) →
  ∀ {declName : Lean.Name} {shape : Sparkle.Compiler.Elab.MachineShape} {D : Nat} {w w' : Void IO.RealWorld}
    {m : Mod} {d : Dsg},
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false)
      mctx mref cctx cref w (m, d) w') →
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName shape) →
    (closes : Tools.ShippingChildRunAKids.MachineClosesAtA O mctx cctx declName shape) →
    (hw : Tools.ShippingChildVCA.JQ O.quiet D w) →
    (hc : D = 0 ∨ Tools.ShippingChildCacheA.CacheInvA O (Tools.ShippingChildBndCore.cv w)) →
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx (D + 1) declName shape m d
def PinMRJMut : Prop := ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
  (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref),
  (hA : Tools.ShippingChildInvA.AdmCtx O.quiet mctx cctx) →
  ∀ {declName : Lean.Name} {shape : Sparkle.Compiler.Elab.MachineShape} {D : Nat} {w w' : Void IO.RealWorld}
    {m : Mod} {d : Dsg},
    (hr : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore declName [] false)
      mctx mref cctx cref w (m, d) w') →
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref declName shape) →
    (closes : Tools.ShippingChildRunAKids.MachineClosesAtA O mctx cctx declName shape) →
    (hw : Tools.ShippingChildVCA.JQ O.quiet D w) →
    (hc : D = 0 ∨ Tools.ShippingChildCacheA.CacheInvA O (Tools.ShippingChildBndCore.cv w)) →
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx D declName shape m d

def PinCCI : Prop := ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
  (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Lean.Name}
  (d : Tools.ShippingMachineAuto.MachineData),
  (hins : d.shape.insts ≠ []) → (hf : d.shape.instFields = []) →
  ∀ {M : Mod} {D : Dsg}, (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) →
    ∃ (tenv : Lean.Environment) (logProf : String → IO Unit) (t t' : Mod) (d₀ : Dsg)
      (children : List (Mod × Dsg)),
      Tools.ShippingEntrySoundness.MReturns (Sparkle.Compiler.Elab.synthesizeMixedCertified
        (fun e hint top named => Sparkle.Compiler.Elab.translateExprToWire tenv e hint top named) logProf c
        d.shape.binders d.shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets d.shape.layout.lets t = some t' ∧
      Sparkle.IR.Machine.closeInsts (Tools.ShippingMachineEntry.machNIn d.shape) d.shape.insts.length
        d.shape.layout.slots.length (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) children
        (Sparkle.IR.Machine.closeMachine d.shape.layout t', d₀) = some (M, D) ∧
      Tools.ShippingChildRunAKids.ChildrenRealA O d.shape children
def PinCCIMut : Prop := ∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
  (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) {c : Lean.Name}
  (d : Tools.ShippingMachineAuto.MachineData),
  (hins : d.shape.insts ≠ []) → (hf : d.shape.instFields ≠ []) →
  ∀ {M : Mod} {D : Dsg}, (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D) →
    ∃ (tenv : Lean.Environment) (logProf : String → IO Unit) (t t' : Mod) (d₀ : Dsg)
      (children : List (Mod × Dsg)),
      Tools.ShippingEntrySoundness.MReturns (Sparkle.Compiler.Elab.synthesizeMixedCertified
        (fun e hint top named => Sparkle.Compiler.Elab.translateExprToWire tenv e hint top named) logProf c
        d.shape.binders d.shape.body) (t, d₀) ∧
      Sparkle.IR.Machine.closeLets d.shape.layout.lets t = some t' ∧
      Sparkle.IR.Machine.closeInsts (Tools.ShippingMachineEntry.machNIn d.shape) d.shape.insts.length
        d.shape.layout.slots.length (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) children
        (Sparkle.IR.Machine.closeMachine d.shape.layout t', d₀) = some (M, D) ∧
      Tools.ShippingChildRunAKids.ChildrenRealA O d.shape children

/-- the TYPE of constant `c` against the expected telescope `e` (a definition's value). -/
def checkPin (c e : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let ex ← stmtOf e
  cmpTele s!"{c} (constant type)" ci.type ex
  logInfo m!"PIN OK {c} against {e}"
def checkPinNeg (c e : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let ex ← stmtOf e
  let accepted ← withoutModifyingState do
    try cmpTele s!"{c} vs {e}" ci.type ex; pure true catch _ => pure false
  if accepted then throwError "PIN NEG ACCEPTED: {e} matches the type of {c}"
  logInfo m!"PIN NEG REJECTED {e} (against {c})"

def pins : List (Name × Name × Name) :=
  [(``Tools.ShippingGen5DCEntryN.postEntry_lookup_ne, ``PinPLN, ``PinPLNMut),
   (``Tools.ShippingGen2.Start, ``PinStart, ``PinStartMut),
   (``Tools.ShippingRanABridge.machineRanA_of_runJQC, ``PinRRA, ``PinRRAMut),
   (``Tools.ShippingServedRealA.machineRunJQC_of_closesA, ``PinMRJ, ``PinMRJMut),
   (``Tools.ShippingParentDesignA.core_closeInstsA, ``PinCCI, ``PinCCIMut)]

def table : List (Name × Name × List Name) :=
  [(``Tools.ShippingGen5DCEntryU.noRawBelow_of_coreRun, ``ExpNC,
      [``MutNCnoHS, ``MutNCnoHdef, ``MutNCnoHcl, ``MutNCnoHins, ``MutNCnoHf, ``MutNCfNe, ``MutNCdeclName, ``MutNCzero,
       ``MutNCtrue, ``MutNCjqcOnly, ``MutNCunrel, ``MutNCrawWrong]),
   (``Tools.ShippingGen5DCEntryU.hlk_of_postEntry, ``ExpHL, [``MutHLnoHne, ``MutHLswap, ``MutHLpostSwap, ``MutHLnoPost]),
   (``Tools.ShippingGen5DCEntryU.coreRun_transport, ``ExpCT,
      [``MutCTnoPost, ``MutCTnoHS, ``MutCTnoHr, ``MutCTnoHdef, ``MutCTnoHcl, ``MutCTnoHins, ``MutCTnoHf, ``MutCTopt,
       ``MutCTrhsD, ``MutCTswap, ``MutCTzero, ``MutCTpostSwap])]

/-! ## closure -/
open Tests.Gen5.DeclConnectCheck (reach reachRaw violations)

def requiredOf : List (Name × List Name) :=
  [(``Tools.ShippingGen5DCEntryU.noRawBelow_of_coreRun,
      [``Tools.ShippingServedRealA.machineRunJQC_of_closesA, ``Tools.ShippingRanABridge.machineRanA_of_runJQC,
       ``Tools.ShippingParentDesignA.core_closeInstsA, ``Tools.ShippingGen5DCEntryS.noRawBelow_of_closeInsts]),
   (``Tools.ShippingGen5DCEntryU.hlk_of_postEntry, [``Tools.ShippingGen5DCEntryN.postEntry_lookup_ne]),
   (``Tools.ShippingGen5DCEntryU.coreRun_transport,
      [``Tools.ShippingGen5DCEntryT.runModuleTG_transport, ``Tools.ShippingGen5DCEntryU.hlk_of_postEntry,
       ``Tools.ShippingGen5DCEntryU.noRawBelow_of_coreRun])]

def missingOf (r : Tests.Gen5.DeclConnectCheck.Reach) (req : List Name) : List Name := req.filter (!r.seen.contains ·)

/-- negative control: mentions `postEntry` but never `postEntry_lookup_ne` -/
theorem negNoLemma {b raw : Mod} {D D' : Dsg} (h : Tools.ShippingGen5DCEntryD.PostEntry b raw D D') :
    Tools.ShippingGen5DCEntryD.PostEntry b raw D D' := h
/-- clean control: `hlk_of_postEntry` through a helper -/
theorem cleanU {b raw : Mod} {D D' : Dsg} (h : Tools.ShippingGen5DCEntryD.PostEntry b raw D D') :
    ∀ mn : String, mn ≠ raw.name → moduleByName D'.modules mn = moduleByName D.modules mn :=
  Tools.ShippingGen5DCEntryU.hlk_of_postEntry h

def ghostTy : Name := `Tests.Gen5.DCEntryUCheck.ghost_unknown_in_type
def ghostVal : Name := `Tests.Gen5.DCEntryUCheck.ghost_unknown_in_value
def fixEnv (env : Environment) : MetaM Environment := do
  let add (env : Environment) (n : Name) (ty v : Lean.Expr) : MetaM Environment :=
    match env.addDeclCore 0 (.defnDecl { name := n, levelParams := [], type := ty, value := v, hints := .abbrev, safety := .safe }) none (doCheck := false) with
    | .ok e => pure e
    | .error _ => throwError "fixture environment: could not add {n}"
  let nat := Lean.mkConst ``Nat
  let env ← add env `fixHelperTy (Lean.mkConst ghostTy) (Lean.mkConst ``Nat.zero)
  let env ← add env `fixHelperVal nat (Lean.mkConst ghostVal)
  let env ← add env `fixRootUsesTy nat (Lean.mkApp (Lean.mkConst ``id [1]) (Lean.mkConst `fixHelperTy))
  let env ← add env `fixRootUsesVal nat (Lean.mkApp (Lean.mkConst ``id [1]) (Lean.mkConst `fixHelperVal))
  add env `fixRootClean nat (Lean.mkConst ``Nat.zero)

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut nType : Nat := 0
  let mut nMut : Nat := 0
  let mut nPin : Nat := 0
  let mut nPinNeg : Nat := 0
  -- positive controls (self-comparison, not counted)
  for e in [``ExpNC, ``ExpHL, ``ExpCT] do withReducible <| checkExpected e e
  for (thm, e, ms) in table do
    withReducible <| checkExpected thm e
    nType := nType + 1
    for m in ms do
      withReducible <| checkMutant thm m
      nMut := nMut + 1
  for (c, e, m) in pins do
    withReducible <| checkPin c e
    nPin := nPin + 1
    withReducible <| checkPinNeg c m
    nPinNeg := nPinNeg + 1
  let targets := [``Tools.ShippingGen5DCEntryU.noRawBelow_of_coreRun, ``Tools.ShippingGen5DCEntryU.hlk_of_postEntry,
    ``Tools.ShippingGen5DCEntryU.coreRun_transport]
  for n in targets do checkAxioms n
  let mut nClosure : Nat := 0
  for (n, req) in requiredOf do
    let r ← reach env n
    unless r.axioms.isEmpty do throwError "CLOSURE FAILED {n}: axiom constants {r.axioms}"
    let v := violations env r
    unless v.isEmpty do throwError "CLOSURE FAILED {n}: forbidden {v}"
    let miss := missingOf r req
    unless miss.isEmpty do throwError "CLOSURE FAILED {n}: required constants not reached {miss}"
    nClosure := nClosure + 1
    logInfo m!"CLOSURE OK {n}: reached {r.seen.size}, opaque {r.opaques}, required {req}"
  let lemmaN := ``Tools.ShippingGen5DCEntryN.postEntry_lookup_ne
  let rn ← reach env ``negNoLemma
  unless (missingOf rn [lemmaN]).contains lemmaN do
    throwError "CLOSURE CONTROL NOT DETECTED negNoLemma"
  logInfo m!"CLOSURE CONTROL DETECTED negNoLemma (postEntry_lookup_ne not reached)"
  let rc ← reach env ``cleanU
  unless (violations env rc).isEmpty && (missingOf rc [lemmaN]).isEmpty do
    throwError "CLOSURE CLEAN CONTROL FAILED"
  logInfo m!"CLOSURE CLEAN CONTROL OK cleanU"
  unless (violations env (← reach env ``Tests.Gen5.DeclConnectCheck.negDirect)).isEmpty == false do
    throwError "CLOSURE CONTROL NOT DETECTED negDirect (forbidden mention)"
  logInfo m!"CLOSURE CONTROL DETECTED negDirect (forbidden mention)"
  withoutModifyingEnv do
    setEnv (← fixEnv env)
    let envF ← getEnv
    for (root, ghost, what) in [(`fixRootUsesTy, ghostTy, "TYPE"), (`fixRootUsesVal, ghostVal, "VALUE")] do
      let raw ← reachRaw envF root
      unless raw.unknown == #[ghost] do
        throwError "UNKNOWN-NAME FIXTURE: expected exactly {ghost} unknown (the helper's {what}), got {raw.unknown}"
      let failed ← try let _ ← reach envF root; pure false catch _ => pure true
      unless failed do throwError "UNKNOWN-NAME FIXTURE: `reach` did not fail for {root}"
      logInfo m!"UNKNOWN-NAME FIXTURE DETECTED {root} (only the helper's {what} is unknown: {raw.unknown}), reach fails"
    let rcl ← reach envF `fixRootClean
    unless rcl.unknown.isEmpty do throwError "UNKNOWN-NAME FIXTURE CLEAN CONTROL FAILED"
    logInfo m!"UNKNOWN-NAME FIXTURE CLEAN CONTROL OK fixRootClean"
  let cur ← getEnv
  unless [`fixHelperTy, `fixHelperVal, `fixRootUsesTy, `fixRootUsesVal, `fixRootClean].all (cur.find? · |>.isNone) do
    throwError "fixture leaked into the environment"
  logInfo m!"COUNTS: TYPE {nType} (3 theorems; plus 3 self-comparisons not counted), SOURCE-PIN {nPin} (constant types of postEntry_lookup_ne, Start, machineRanA_of_runJQC, machineRunJQC_of_closesA, core_closeInstsA), PIN-NEG {nPinNeg} (changed expected pin rejected), MUTANT {nMut} (well-typed single change, signature/defeq rejection under withReducible, not semantic counterexamples), BLOCK 0, CONJ 0, AXIOMS {targets.length}, CLOSURE {nClosure} roots + 1 missing-requirement control + 1 forbidden-mention control + 1 clean control + unknown-name fixtures (2 detect: type-only, value-only; 1 clean)"
  logInfo m!"STATUS: NOT supplied by this unit: MachineDefines / MachineClosesAtA / Start themselves (real EntryWitness, ReflectsAll), leaf case insts = [], (a3) checkedOptimize body vs raw, TopShips on D', O3 (b1)(b2), (c4 import)(c5)(c6)(c7), parametrised-route post-processing, Post adoption, FG"

end Tests.Gen5.DCEntryUCheck
