import Tools.ShippingGen2Served
import Tests.Gen3.ServedExpectedType
import Tests.Gen2.LeafInstance
set_option autoImplicit false
-- Built: g3sv-b5be62e6 (clean snapshot, exit 0, standard axioms); written by reading at 96cbd548. No `sorry`, no `axiom`, no `native_decide`.

/-! # G-SERVED checks (scripts/gen2/SERVED_FREEZE.md rev1 §4.2)

1. **C1 expected types.** Each statement below is compared MECHANICALLY with `checkExpected` (local copy
   `Tests.Gen3.ServedExpectedType`): binder by binder, with names, binder infos, types and the conclusion. The
   comparison is against an independent `Expected…` text written from rev1 §1.5. Meaning-changing MUTANTS must be
   REJECTED (`checkMutant`):
   - `SoundXAt` without `outsNodup`;
   - `ChildrenShipsI` without the `Reach →` guard;
   - `hreach` without its `child? = none` antecedent;
   - no `hord1`;
   - `servedShips0_proved` without `hrow`;
   - `t1_of_stepPF_served` without `hPF`.
2. **C2.** `T1Stmt` from exactly `hrow`, `StepStmt`, `PostFactsStmt`.
3. **C3.** The old boundary (`ServedRealA`) is still derivable from the new trace.
4. **C4 rows** (data only, on shapes): positive one-output `.ord` shape, negative `memShape0`, implication form
   `memShape1`, out of range `memShapeX`. Copies of the `par/gen2-spec` Tests/Gen2/DataBridgeCheck.lean shapes.
5. **C5 SINGLE-INSTANCE control for `hrow`.** `leaf16Pkg` (Tests/Gen2/LeafInstance.lean, a callless leaf) has row
   `true`, so `hrow` holds at `DataOk := (· = leaf16Pkg)`. This is ONE INSTANCE ONLY. It is NOT supply of `hrow`,
   NOT coverage over successful compilations, and NOT non-vacuity of the universal premise at an abstract or real
   `DataOk`. It shows only that the premise is not contradictory at that one point.
6. **Axioms.** `checkAxioms` (standard axioms only) and `#print axioms` of every root.

Every result here that takes `hrow` is CONDITIONAL. None completes G-SERVED, T1 or FG. -/

namespace Tests.Gen3.ServedCheck
open Tools.ShippingGen2
open Tests.Gen3.ServedExpectedType
open Sparkle.Core.Domain

/-! ## 1. Expected statements (rev1 §1.5 text) -/

section Expected
open Lean hiding Module
open Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingMixedEntrySoundness (PositiveBinders)
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildCacheA (JQC RealChildA)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildInv (Res profLogIO)
open Tools.ShippingChildRunAKids (MachineClosesAtA)

def ExpectedSoundXAt (X : List FVarId → IO.Ref (ExprStructMap String) → Prop) (declName : Name)
    (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Design) : Prop :=
  ∀ (bsIn slotBs letBs : List (Name × MixedGateBinder)),
    shape.binders = bsIn ++ slotBs ++ letBs → shape.layout.lets = letBs.length →
    PositiveBinders shape.binders → (∀ b ∈ slotBs, b.2 ≠ .domain) → (∀ b ∈ letBs, b.2 ≠ .domain) →
    Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2) shape.layout.slots slotBs →
    (∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true) →
    (shape.layout.outs.map (·.name)).Nodup →
    MachinePreservesX X declName shape bsIn slotBs letBs m dsn

/-- MUTANT: `outsNodup` dropped. -/
def MutSoundXAt_noNodup (X : List FVarId → IO.Ref (ExprStructMap String) → Prop) (declName : Name)
    (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Design) : Prop :=
  ∀ (bsIn slotBs letBs : List (Name × MixedGateBinder)),
    shape.binders = bsIn ++ slotBs ++ letBs → shape.layout.lets = letBs.length →
    PositiveBinders shape.binders → (∀ b ∈ slotBs, b.2 ≠ .domain) → (∀ b ∈ letBs, b.2 ≠ .domain) →
    Zip₂ (fun (f : SlotField) (b : Name × MixedGateBinder) => f.width = machWidth b.2) shape.layout.slots slotBs →
    (∀ o ∈ shape.layout.outs, 0 < o.width ∧ outNameOk o.name = true) →
    MachinePreservesX X declName shape bsIn slotBs letBs m dsn

def ExpectedMachineRunInv {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (mctx : Meta.Context)
    (cctx : Core.Context) (n : Nat) (c : Name) (shape : MachineShape) (M : Sparkle.IR.AST.Module)
    (D : Design) : Prop :=
  ∃ (tenv : Lean.Environment), ∃ (b : Bool) (w9 w10 : Void IO.RealWorld),
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) c shape)
      mctx mref cctx cref w9 (some (M, D)) w10 ∧ InvAt L P Reach n w9

def ExpectedChildrenShipsI {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (shape : MachineShape)
    (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    ((shape.instOrigins.getD k .ord).child? = some y ∨
      (RealChildA L.O (shape.insts[k]).1 y ∧ (Reach (shape.insts[k]).1 → ShipsRes L P (shape.insts[k]).1 y)))

/-- MUTANT: the `Reach →` guard dropped (every ordinary child ships, reached or not). -/
def MutChildrenShipsI_noGuard {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (shape : MachineShape)
    (children : List Res) : Prop :=
  children.length = shape.insts.length ∧
  ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
    ((shape.instOrigins.getD k .ord).child? = some y ∨
      (RealChildA L.O (shape.insts[k]).1 y ∧ ShipsRes L P (shape.insts[k]).1 y))

def ExpectedSynthesizeChildShips : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {D : Nat} {n : Name} {w w' : Void IO.RealWorld} {r : Res}
    (hw : InvAt L P Reach D w) (hIH : IHAt L P Reach D) (hKI : ChildKeepsInv L P Reach D)
    (h : RunsTo (synthesizeChild n) mctx mref cctx cref w r w'),
    RealChildA L.O n r ∧ (Reach n → ShipsRes L P n r) ∧ InvAt L P Reach D w'

def ExpectedMachineRunInvOfCloses0 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {declName : Name} {shape : MachineShape} {D : Nat}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w')
    (entry : MachineDefines mctx mref cctx cref declName shape)
    (closes : MachineClosesAtA L.O mctx cctx declName shape)
    (hw : JQC L.O D w) (hc : D = 0 ∨ CacheShips L P Reach (cv w)),
    MachineRunInv L P Reach mctx cctx (D + 1) declName shape m d

def ExpectedRunsS : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {n : Nat} {tenv : Lean.Environment}
    (hIH : IHAt L P Reach n) (hKI : ChildKeepsInv L P Reach n)
    {b : Bool} {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module}
    {d : Design} {w w' : Void IO.RealWorld}
    (hw : InvAt L P Reach n w)
    (hr : RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w (some (m, d)) w'),
    ∃ t t' d₀, MReturns (synthesizeMixedCertified
        (fun e hint top named => translateExprToWire tenv e hint top named) (profLogIO b) declName
        shape.binders shape.body) (t, d₀) ∧
      closeLets shape.layout.lets t = some t' ∧
      ((shape.insts = [] ∧ m = closeMachine shape.layout t' ∧ d = d₀) ∨
       (shape.insts ≠ [] ∧ ∃ children,
          CloseCalls shape t (closeMachine shape.layout t') d₀ children m d ∧
          ChildrenShipsI L P Reach shape children))

def ExpectedSoundXShipsRan : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {n : Nat} {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {d : Design}
    (ran : MachineRunInv L P Reach mctx cctx n declName shape m d)
    (hIH : IHAt L P Reach n) (hKI : ChildKeepsInv L P Reach n)
    (hreach : ∀ k (hk : k < shape.insts.length),
      (shape.instOrigins.getD k .ord).child? = none → Reach (shape.insts[k]).1)
    (hord1 : shape.instFields = [] → ∀ k, k < shape.insts.length →
      (shape.instOrigins.getD k .ord).child? = none),
    SoundXAt (ServedP (ShipsRes L P) declName shape m d) declName shape m d

/-- MUTANT: `hreach` without its `child? = none` antecedent (every entry reached). -/
def MutSoundX_hreachStrong : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {n : Nat} {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {d : Design}
    (ran : MachineRunInv L P Reach mctx cctx n declName shape m d)
    (hIH : IHAt L P Reach n) (hKI : ChildKeepsInv L P Reach n)
    (hreach : ∀ k (hk : k < shape.insts.length), Reach (shape.insts[k]).1)
    (hord1 : shape.instFields = [] → ∀ k, k < shape.insts.length →
      (shape.instOrigins.getD k .ord).child? = none),
    SoundXAt (ServedP (ShipsRes L P) declName shape m d) declName shape m d

/-- MUTANT: `hord1` dropped (the G-ONEOUT-REACH gap silently assumed away). -/
def MutSoundX_noHord1 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    {mctx : Meta.Context} {cctx : Core.Context} (hA : AdmCtx L.O.quiet mctx cctx)
    {n : Nat} {declName : Name} {shape : MachineShape} {m : Sparkle.IR.AST.Module} {d : Design}
    (ran : MachineRunInv L P Reach mctx cctx n declName shape m d)
    (hIH : IHAt L P Reach n) (hKI : ChildKeepsInv L P Reach n)
    (hreach : ∀ k (hk : k < shape.insts.length),
      (shape.instOrigins.getD k .ord).child? = none → Reach (shape.insts[k]).1),
    SoundXAt (ServedP (ShipsRes L P) declName shape m d) declName shape m d

def ExpectedServedShips0Proved : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true),
    ServedShips0Stmt L P Reach DataOk

/-- MUTANT: the unconditional statement (no `hrow`), i.e. G-SERVED closed. -/
def MutServed_noRow : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop),
    ServedShips0Stmt L P Reach DataOk

def ExpectedT1Served : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hStep : StepStmt L P DataOk) (hPF : PostFactsStmt L P Reach DataOk),
    T1Stmt L P Reach DataOk

/-- MUTANT: `PostFactsStmt` dropped. -/
def MutT1_noPF : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hStep : StepStmt L P DataOk),
    T1Stmt L P Reach DataOk

def ExpectedPkgTraceX : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom)
    {X : List FVarId → IO.Ref (ExprStructMap String) → Prop} {m : Sparkle.IR.AST.Module} {design : Design}
    (hX : SoundXAt X p.decl p.d.shape m design),
    Tools.ShippingMachineTraceX.MachineTraceLBX X p.decl p.d m design dom p.src p.extS p.extBS p.lsrc

end Expected

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``Tools.ShippingGen2.SoundXAt ``ExpectedSoundXAt
  checkExpected ``Tools.ShippingGen2.MachineRunInv ``ExpectedMachineRunInv
  checkExpected ``Tools.ShippingGen2.ChildrenShipsI ``ExpectedChildrenShipsI
  checkExpected ``Tools.ShippingGen2.synthesizeChild_ships ``ExpectedSynthesizeChildShips
  checkExpected ``Tools.ShippingGen2.machineRunInv_of_closes0 ``ExpectedMachineRunInvOfCloses0
  checkExpected ``Tools.ShippingGen2.synthesizeMachineCertified_runsS ``ExpectedRunsS
  checkExpected ``Tools.ShippingGen2.soundX_ships_ran ``ExpectedSoundXShipsRan
  checkExpected ``Tools.ShippingGen2.servedShips0_proved ``ExpectedServedShips0Proved
  checkExpected ``Tools.ShippingGen2.t1_of_stepPF_served ``ExpectedT1Served
  checkExpected ``Tools.ShippingGen2.Pkg.traceX ``ExpectedPkgTraceX
  checkMutant ``Tools.ShippingGen2.SoundXAt ``MutSoundXAt_noNodup
  checkMutant ``Tools.ShippingGen2.ChildrenShipsI ``MutChildrenShipsI_noGuard
  checkMutant ``Tools.ShippingGen2.soundX_ships_ran ``MutSoundX_hreachStrong
  checkMutant ``Tools.ShippingGen2.soundX_ships_ran ``MutSoundX_noHord1
  checkMutant ``Tools.ShippingGen2.servedShips0_proved ``MutServed_noRow
  checkMutant ``Tools.ShippingGen2.t1_of_stepPF_served ``MutT1_noPF

/-! ## 2. C2 / C1 as terms: the premises are exactly the listed ones -/

section Terms
open Lean hiding Module
open Meta

/-- C2: `T1Stmt` from exactly `hrow`, `StepStmt`, `PostFactsStmt` (CONDITIONAL; not T1 completion). -/
example {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true)
    (hStep : StepStmt L P DataOk) (hPF : PostFactsStmt L P Reach DataOk) :
    T1Stmt L P Reach DataOk :=
  t1_of_stepPF_served L P Reach DataOk hrow hStep hPF

/-- C1 as a term: the frozen `ServedShips0Stmt` (T1.lean:112) under `hrow` only (CONDITIONAL). -/
example {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (DataOk : Pkg ι dom → Prop)
    (hrow : ∀ q : Pkg ι dom, DataOk q → Tools.ShippingGen2DataBridge.OneOutNoMemRow q = true) :
    ServedShips0Stmt L P Reach DataOk :=
  servedShips0_proved L P Reach DataOk hrow

/-- C3: the old boundary `ServedRealA` is still derivable from the new trace (same witnesses). -/
example {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) (raw : Sparkle.IR.AST.Module)
    (D : Sparkle.IR.AST.Design)
    (htr : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (Tools.ShippingServedRealA.ServedRealA L.O p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc :=
  machineTraceLBX_mono
    (fun _ _ h => servedRealA_of_servedP (L := L) (Q := ShipsRes L P) (fun _ _ hs => shipsRes_real hs) h) htr

end Terms

/-! ## 3. C4 row controls on shapes (data only; copies of the `par/gen2-spec` DataBridgeCheck shapes) -/

section Rows
open Tools.ShippingGen2DataBridge

/-- Synthetic shape: one call entry with a MEMORY origin and no field list. -/
def memShape0 : Sparkle.Compiler.Elab.MachineShape :=
  { binders := [], body := .bvar 0,
    layout := { slots := [], outs := [], resetKind := .synchronous },
    insts := [(`m, [], .bits 8)], instOrigins := [.mem false 4 8] }

/-- Positive, one-output: the same entry with an ORDINARY origin (`.ord`), no field list. -/
def ordShape1 : Sparkle.Compiler.Elab.MachineShape := { memShape0 with instOrigins := [.ord] }

theorem ordShape1_row : noMemRowS ordShape1 = true := by
  first | decide | decide +kernel

theorem ordShape1_noFields : ordShape1.instFields = [] := by
  first | rfl | decide

theorem ordShape1_hord :
    (ordShape1.instOrigins.getD 0 Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none :=
  hord_of_rowS ordShape1_row ordShape1_noFields (k := 0) (by first | decide | simp [ordShape1, memShape0])

/-- **Negative**: the row is FALSE on the memory-origin, no-field shape. -/
theorem memShape0_row : noMemRowS memShape0 = false := by
  first | decide | decide +kernel

/-- Implication form: the same entry WITH a field list (a memory parent) passes. -/
def memShape1 : Sparkle.Compiler.Elab.MachineShape := { memShape0 with instFields := ["out"] }

theorem memShape1_row : noMemRowS memShape1 = true := by
  first | decide | decide +kernel

/-- Out of range: an origin beyond `insts` is not covered; the row passes but the origin at `0` builds a child, so
`hord_of_row` is stated for `k < insts.length` only. -/
def memShapeX : Sparkle.Compiler.Elab.MachineShape := { memShape0 with insts := [] }

theorem memShapeX_row : noMemRowS memShapeX = true := by
  first | decide | decide +kernel

theorem memShapeX_outOfRange :
    (memShapeX.instOrigins.getD 0 Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child?.isSome = true := by
  first | rfl | decide

end Rows

/-! ## 4. C5: SINGLE-INSTANCE control for `hrow` (one package; NOT supply, NOT coverage, NOT universal non-vacuity) -/

section Single
open Tools.ShippingGen2DataBridge

/-- The row of the ONE concrete package `leaf16Pkg` (a callless leaf: `instFields = []`, `insts = []`). -/
theorem leaf16_row : OneOutNoMemRow Tests.Gen2.LeafInstance.leaf16Pkg = true := by
  first | decide | decide +kernel | rfl

/-- SINGLE INSTANCE ONLY: `hrow` at `DataOk := (· = leaf16Pkg)`. This is not a supply of `hrow` for any `DataOk`
used by T1, and says nothing about other packages or successful compilations. -/
theorem hrow_single_instance :
    ∀ q : Pkg Unit Tests.Gen2.LeafInstance.U,
      (fun q => q = Tests.Gen2.LeafInstance.leaf16Pkg) q → OneOutNoMemRow q = true := by
  intro q hq
  have hq' : q = Tests.Gen2.LeafInstance.leaf16Pkg := hq
  subst hq'
  exact leaf16_row

end Single

/-! ## 5. Axioms -/

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkAxioms ``Tools.ShippingGen2.core_reads_invAt0
  checkAxioms ``Tools.ShippingGen2.machineRunInv_of_coreA
  checkAxioms ``Tools.ShippingGen2.machineRunInv_of_closes0
  checkAxioms ``Tools.ShippingGen2.synthesizeChild_ships
  checkAxioms ``Tools.ShippingGen2.closeInstsM_ships
  checkAxioms ``Tools.ShippingGen2.closeInstsGM_ships
  checkAxioms ``Tools.ShippingGen2.synthesizeMachineCertified_runsS
  checkAxioms ``Tools.ShippingGen2.soundX_ships_ran
  checkAxioms ``Tools.ShippingGen2ServedTrace.machine_trace_lets_of_streamBRX
  checkAxioms ``Tools.ShippingGen2ServedTrace.genTraceX
  checkAxioms ``Tools.ShippingGen2ServedTrace.genTraceLX
  checkAxioms ``Tools.ShippingGen2.Pkg.traceX
  checkAxioms ``Tools.ShippingGen2.servedShips0_proved
  checkAxioms ``Tools.ShippingGen2.t1_of_stepPF_served
  checkAxioms ``Tools.ShippingGen2DataBridge.hord_of_row
  checkAxioms ``ordShape1_hord
  checkAxioms ``hrow_single_instance

#print axioms Tools.ShippingGen2.soundX_ships_ran
#print axioms Tools.ShippingGen2.Pkg.traceX
#print axioms Tools.ShippingGen2.servedShips0_proved
#print axioms Tools.ShippingGen2.t1_of_stepPF_served
#print axioms ordShape1_hord
#print axioms memShape0_row
#print axioms memShape1_row
#print axioms memShapeX_row
#print axioms memShapeX_outOfRange
#print axioms leaf16_row
#print axioms hrow_single_instance

end Tests.Gen3.ServedCheck
