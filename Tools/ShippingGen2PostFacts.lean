import Tools.ShippingGen2Defs
import Tools.ShippingGen2Connect
import Tools.ShippingCallsShape
set_option autoImplicit false
-- BUILT: g3pf-28476add at 28476add (exit 0; scripts/gen2/GPOST_FREEZE.md §2, §4, §11).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # G-POST statements (scripts/gen2/GPOST_FREEZE.md)

* `PostFactsStmt` (§2): on one run of a reached declaration, (i) no module of the core design is named as the core
  module, and (ii) `InstClosed` of the FULL entry's result. A STATEMENT only; its producer `postFacts_proved` is NOT
  written here (§5, MISSING; open premises P1, P2, P7, U1, U2).
* `DataRows` (§11, S1 decision): an UNSUPPLIED sufficient data condition the producer will take as an explicit
  premise. It does not resolve G-POST and does not narrow FG. `DataOkB` is unchanged.
* §4: frozen copies of the pre-`InstClosed` texts (`ShipsResOld`, `CacheShipsOld`, `InvAtOld`, `StepStmtOld`) and the
  projections new → old (`shipsRes_old`, `cacheShips_old`, `invAt_old`, `servedP_old`, `stepStmt_of_old`).
  `IHAt` vs the old one is incomparable (no lemma); `ChildKeepsInv`/`KeepChildStmt`/`ServedShips0Stmt` are re-proved,
  not transported. -/

namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineEntry
open Tools.ShippingChildInvA (RefLawsAOps AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildInv (Res)

variable {ι : Type} {dom : ι → DomainConfig}

/-! ## 1. `PostFactsStmt` (freeze §2) -/

/-- **G-POST** (premise of `ihAt_stepPF`): (i) no top-named module, and (ii) `InstClosed` of the FULL entry's
result, on one run (the full-entry relation is the output of `synthesizeCombinational_designTop`,
ShippingDesignWriterRun.lean:69-79, from the same start `u`). -/
def PostFactsStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) : Prop :=
  T1Hyp L P Reach DataOk →
  ∀ (q : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (u u' w1 : Void IO.RealWorld)
    (M' raw : Sparkle.IR.AST.Module) (Dg' Dg : Design),
    Reach q.decl → P q.decl = some q → DataOk q → AdmCtx L.O.quiet mctx cctx →
    InvAt L P Reach (dv u) u →
    IHAt L P Reach (dv u + 1) → ChildKeepsInv L P Reach (dv u + 1) →
    RunsTo (synthesizeCombinational q.decl) mctx mref cctx cref u (M', Dg') u' →
    RunsTo (synthesizeCombinationalCore q.decl [] false) mctx mref cctx cref u (raw, Dg) w1 →
    (M' = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      M' = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    Dg'.topModule = Dg.topModule →
    ((∀ x ∈ Dg.modules, x.name ≠ raw.name) → Dg'.modules = Dg.modules) →
    MachineTaken L mctx cctx (dv u + 1) q.decl q.d.shape raw Dg →
    (∀ x ∈ Dg.modules, x.name ≠ raw.name) ∧ InstClosed (M', Dg')

/-! ## 2. `DataRows` (freeze §11, S1: explicit, UNSUPPLIED premise of the future producer) -/

/-- The data rows `closedBody_kinds_of_run` (P3) needs: `callsOk`, the slot-type count, and the non-domain property
of every binder after the declaration's own inputs. `ok` is `Pkg.ok q` (not a field). UNSUPPLIED at generic
`DataOk` (`DataOkB` lacks the third row; `MemParentDataOk.rows` has all three). -/
def DataRows (q : Pkg ι dom) : Prop :=
  q.d.callsOk q.kD = true ∧ q.d.ss.length = q.d.shape.layout.slots.length ∧
  (∀ b ∈ q.d.shape.binders.drop q.kD, b.2 ≠ .domain)

/-! ## 3. Frozen pre-`InstClosed` texts and the projections new → old (freeze §4) -/

/-- The former `ShipsRes` (Defs:128 before G-POST), verbatim. -/
def ShipsResOld {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (c : Name) (r : Res) : Prop :=
  RealChildA L.O c r ∧ ∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2

/-- The former `CacheShips`, over `ShipsResOld`. -/
def CacheShipsOld {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, Reach c → m.get? c = some r → ShipsResOld L P c r

/-- The former `InvAt`, over `CacheShipsOld`. -/
def InvAtOld {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) :
    Void IO.RealWorld → Prop :=
  fun w => JQC L.O D w ∧ CacheShipsOld L P Reach (cv w)

/-- The former `StepStmt`, verbatim over `ShipsResOld`. -/
def StepStmtOld {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (DataOk : Pkg ι dom → Prop) : Prop :=
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    P p.decl = some p → DataOk p → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsResOld L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc →
    ∃ n, TopShips p n p.decl b raw D ∧ ChildShips p n b D

theorem shipsRes_old {mref cref} {L : Laws mref cref} {P : Pkgs ι dom} {c : Name} {r : Res}
    (h : ShipsRes L P c r) : ShipsResOld L P c r :=
  ⟨h.1, h.2.1⟩

theorem cacheShips_old {mref cref} {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {m : Std.HashMap Name Res} (h : CacheShips L P Reach m) : CacheShipsOld L P Reach m :=
  fun c r hR hg => shipsRes_old (h c r hR hg)

theorem invAt_old {mref cref} {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop} {D : Nat}
    {w : Void IO.RealWorld} (h : InvAt L P Reach D w) : InvAtOld L P Reach D w :=
  ⟨h.1, fun c r hR hg => shipsRes_old (h.2 c r hR hg)⟩

theorem servedP_old {mref cref} {L : Laws mref cref} {P : Pkgs ι dom} {declName : Name}
    {shape : MachineShape} {m : Sparkle.IR.AST.Module} {dsn : Design} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)}
    (h : ServedP (ShipsRes L P) declName shape m dsn ids cache) :
    ServedP (ShipsResOld L P) declName shape m dsn ids cache :=
  servedP_mono (Q := ShipsRes L P) (Q' := ShipsResOld L P) (fun _ _ hq => shipsRes_old hq) h

/-- The old one-level rule gives the new one: the new trace premise is mapped to the old by `servedP_old`. -/
theorem stepStmt_of_old {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (DataOk : Pkg ι dom → Prop)
    (h : StepStmtOld L P DataOk) : StepStmt L P DataOk := by
  intro p mctx cctx w w1 raw b D hP hD hA hj hr hb hdef htk hdec htr
  exact h p mctx cctx w w1 raw b D hP hD hA hj hr hb hdef htk hdec
    (machineTraceLBX_mono (X := ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      (Y := ServedP (ShipsResOld L P) p.decl p.d.shape raw D) (fun _ _ hx => servedP_old hx) htr)

end Tools.ShippingGen2
