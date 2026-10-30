import Tools.ShippingGen2MemShips
import Tools.ShippingGen2CallField
set_option autoImplicit false

/-! # loop-pkg step 2: compatibility of the `Pkg` refactor (LOOPPKG_FREEZE.md §6 rules)

`Tools.ShippingGen2.Old.*` are the OLD texts (git f1a4367f) of every changed definition, verbatim (unchanged
definitions — `Laws`, `MachineTaken`, `ServedP`, … — are the current ones). Checks:
* pointwise definitions: `X (.gen p) … = Old.X p …` by `rfl`;
* definitions taking a package assignment: equal at `Pkgs.lift P` (functions, by `funext`/`propext`);
* `T1Hyp`: iff, with `DataOkLiftCompat` (compatibility tests only);
* statements quantifying over all packages: NEW → OLD only (the new ones include the loop case).
A-COMB (STEP_IFACE_FREEZE.md rev3) changed `ChildShips`; the affected checks are classified in the A-COMB section.
CALLFIELD (scripts/gen2/CALLFIELD_FREEZE.md §4) changed `CallDec`; the affected checks are classified in the CALLFIELD
section. -/
namespace Tools.ShippingGen2.Old
open Lean hiding Module Expr
open Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain

open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildInv (Res Keeps profLogIO)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingServedRealA (MachineRunJQC)
open Tools.ShippingInstTagged (originAt)
open Sparkle.Compiler.MachMemory (memModule)

variable {ι : Type} {dom : ι → DomainConfig}

abbrev Pkgs (ι : Type) (dom : ι → DomainConfig) := Name → Option (SrcPkg ι dom)

def ChildShips (q : SrcPkg ι dom) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Design) : Prop :=
  ∀ (dsn : Design), (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) →
    moduleByName dsn.modules mc.name = some mc →
    ∀ (i : ι), SeqChildRunN (childMap dsn.modules) dsn n mc (q.d.bsIn.take q.kD) q.d.shape.layout.outs (q.S i)

def CallDec (p q : SrcPkg ι dom) (k : Nat) : Prop :=
  (p.d.shape.instOrigins.getD k .ord).child? = none ∧
  ∃ args, (p.d.shape.insts.map (·.2.1))[k]? = some args ∧
    args.length = q.ports.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      (∀ r (hr : r < args.length), args[r] < p.d.ls.length ∧ ∃ g, (p.lsrc i bools bits)[args[r]]? = some g) ∧
      (∀ τ, InRange (valsOf (p.lsrc i bools bits) args τ) q.ports) ∧
      ∃ (k' : Nat) (o : OutField) (f : Nat → Nat), q.d.shape.layout.outs[k']? = some o ∧ o.name = p.d.shape.instFields.getD k "" ∧
        (q.S i (valsOf (p.lsrc i bools bits) args))[k']? = some f ∧
        ∀ τ, posEnc (fun r => (p.extBS i bools bits r).val τ) (fun r n => (p.extS i bools bits r n).val τ)
          (p.kD + k) (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) = f τ

def MemDec (p : SrcPkg ι dom) (k : Nat) (c : Name) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    MemFacts p.d.shape (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extS i bools bits) k c

def ShipsRes {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (c : Name) (r : Res) : Prop :=
  RealChildA L.O c r ∧ ∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2

def CacheShips {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, Reach c → m.get? c = some r → ShipsRes L P c r

def ShipsAt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (n : Nat) (c : Name) (r : Res) : Prop :=
  RealChildA L.O c r ∧ ∃ q, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2

def InvAt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) :
    Void IO.RealWorld → Prop :=
  fun w => JQC L.O D w ∧ CacheShips L P Reach (cv w)

def IHAt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context) (u u' : Void IO.RealWorld) (r : Res),
    AdmCtx L.O.quiet mctx cctx → InvAt L P Reach D u →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref u r u' →
    ShipsRes L P c r

def BodyKeepsInv {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∀ (declName : Name) (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Keeps mctx mref cctx cref (InvAt L P Reach D)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)

def ChildKeepsInv {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) : Prop :=
  Tools.ShippingChildFrontCP.ChildSynthA L.O (InvAt L P Reach D)

def KeepBodyStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ D, ChildKeepsInv L P Reach D → BodyKeepsInv L P Reach D

def KeepChildStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ D, 1 ≤ D → (D < sparkleSynthDepthLimit → BodyKeepsInv L P Reach (D + 1)) →
    IHAt L P Reach D → ChildKeepsInv L P Reach D

structure T1Hyp {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : SrcPkg ι dom → Prop) : Prop where
  /-- G3-GEN: a package for every reached declaration. -/
  pkg : ∀ c, Reach c → ∃ q, P c = some q ∧ q.decl = c ∧ DataOk q
  /-- G3-SHAPE: its shape reflection, in every admissible context. -/
  defines : ∀ c, Reach c → ∀ q, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
    MachineDefines mctx mref cctx cref c q.d.shape
  /-- **T1 scope (route 3)**: the machine synthesis of every reached declaration returns (it does not fall back).
  Coverage obligation G-CLOSES: derive from the data (`memCallee_closesA`, Srm3Callee.lean:91, for memory callees;
  `closes_of_data`, Tools/ShippingMachineClosesData.lean, in general); declarations where it fails are route 4 (M4),
  not removed from FG. -/
  closes : ∀ c, Reach c → ∀ q, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
    MachineClosesAtA L.O mctx cctx c q.d.shape
  /-- G-CALLDEC / G-MEMCALLS: the decodings (to be derived; GENERAL_SPEC §4.2). -/
  dec : ∀ c, Reach c → ∀ q, P c = some q → ∀ k (hk : k < q.d.shape.insts.length),
    MemDec q k (q.d.shape.insts[k]).1 ∨ ∃ q', P (q.d.shape.insts[k]).1 = some q' ∧ CallDec q q' k
  /-- Static call closure of `Reach` (its match with the translator's actual child calls is G-REACH). -/
  closed : ∀ c, Reach c → ∀ q, P c = some q → ∀ k (hk : k < q.d.shape.insts.length),
    (q.d.shape.instOrigins.getD k .ord).child? = none → Reach (q.d.shape.insts[k]).1

def ServedShipsStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : SrcPkg ι dom → Prop) : Prop :=
  T1Hyp L P Reach DataOk →
  ∀ (p : SrcPkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld)
    (raw : Sparkle.IR.AST.Module) (D : Design),
    Reach p.decl → P p.decl = some p → AdmCtx L.O.quiet mctx cctx → InvAt L P Reach (dv w) w →
    IHAt L P Reach (dv w + 1) → ChildKeepsInv L P Reach (dv w + 1) →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w' →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
        p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc

def TopShips (p : SrcPkg ι dom) (n : Nat) (declName : Name) (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = p.d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
        (fun j => (p.extBS i bools bits j).val (T - 1 - t))
        (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
      (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
      (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        p.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ResetNk n raw D kids →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
        st0 x < 2 ^ declWidth b x) →
      ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
          (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          p.d.shape.layout.outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]'hj) o.name = f j

def StepStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (DataOk : SrcPkg ι dom → Prop) : Prop :=
  ∀ (p : SrcPkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    P p.decl = some p → DataOk p → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) →
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc →
    ∃ n, TopShips p n p.decl b raw D ∧ ChildShips p n b D

def MemParentStmt {mref cref} (L : Laws mref cref) (DataOk : SrcPkg ι dom → Prop) : Prop :=
  ∀ (p : SrcPkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    DataOk p → p.d.shape.layout.slots ≠ [] → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) →
    ∀ n, TopShips p (n + 1) p.decl b raw D ∧ ChildShips p (n + 1) b D

def LeafStmt {mref cref} (L : Laws mref cref) (DataOk : SrcPkg ι dom → Prop) : Prop :=
  ∀ (p : SrcPkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    DataOk p → p.d.shape.insts = [] → AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    ∀ n, TopShips p n p.decl b raw D ∧ ChildShips p n b D

def T1Stmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : SrcPkg ι dom → Prop) : Prop :=
  T1Hyp L P Reach DataOk →
  ∀ (c : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld) (raw b : Sparkle.IR.AST.Module) (D : Design),
    Reach c → Start L mctx cctx w →
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    ∃ q n, P c = some q ∧ TopShips q n c b raw D

def MemParentDataOkB (p : SrcPkg ι dom) : Bool :=
  p.d.ok && p.d.callsOk p.kD &&
  decide (p.d.ss.length = p.d.shape.layout.slots.length) &&
  decide (∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width) &&
  decide (∀ b ∈ p.d.shape.binders.drop p.kD, b.2 ≠ .domain)

def MemParentDataOk (p : SrcPkg ι dom) : Prop := MemParentDataOkB p = true

def ExtInS (p : SrcPkg ι dom) : Prop :=
  (∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (j : Nat), j < p.kD → p.extBS i bools bits j = bools j) ∧
  (∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (j n' : Nat), j < p.kD → p.extS i bools bits j n' = bits j n')

def MemOrigin (p : SrcPkg ι dom) : Prop :=
  ∀ (k : Nat) (hk : k < p.d.shape.insts.length), ∃ (cb : Bool) (aw dw : Nat),
    (originAt p.d.shape k).child? = some (memModule cb aw dw) ∧
    ((p.d.bsIn.drop p.kD)[k]?.map (·.2)) = some (.bits dw)

def MemParentStmt' {mref cref} (L : Laws mref cref) : Prop :=
  ∀ (p : SrcPkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    MemParentDataOk p → ExtInS p → MemOrigin p →
    p.d.shape.insts ≠ [] → p.d.shape.instFields ≠ [] → p.d.shape.layout.slots ≠ [] →
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ k (hk : k < p.d.shape.insts.length), MemDec p k (p.d.shape.insts[k]).1) →
    ∀ n, TopShips p (n + 1) p.decl b raw D ∧ ChildShips p (n + 1) b D

end Tools.ShippingGen2.Old

namespace Tests.Gen2.PkgCompat
open Tools.ShippingGen2
open Sparkle.Core.Domain

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-! ## pointwise: `rfl` at `.gen` (definitions not touched by A-COMB or CALLFIELD) -/
example (p : SrcPkg ι dom) (k : Nat) (c : Lean.Name) : MemDec (.gen p) k c = Old.MemDec p k c := rfl
example (p : SrcPkg ι dom) (n : Nat) (c : Lean.Name) (b raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) :
    TopShips (.gen p) n c b raw D = Old.TopShips p n c b raw D := rfl
example (p : SrcPkg ι dom) : MemParentDataOk (.gen p) = Old.MemParentDataOk p := rfl
example (p : SrcPkg ι dom) : ExtInS (.gen p) = Old.ExtInS p := rfl
example (p : SrcPkg ι dom) : MemOrigin (.gen p) = Old.MemOrigin p := rfl

/-! ## CALLFIELD (scripts/gen2/CALLFIELD_FREEZE.md §4): pointwise `CallDec` CHANGED, conditional

The former `CallDec (.gen p) (.gen q) k = Old.CallDec p q k := rfl` is withdrawn. For a group parent
(`instFields ≠ []`) the two texts are equivalent (`callDec_gen_group`); for a one-output parent (`instFields = []`)
they are INCOMPARABLE (old: `o.name = ""`; new: `outs = [o]`) and no relation is claimed. `CallDec` is positive in
`T1Hyp.dec` and negative in `StepStmt` (premise) and in `T1Stmt`/`ServedShipsStmt` (through `T1Hyp`). `t1Hyp_iff` and
`t1Stmt_compat` now hold under `GroupOnly` (used ONLY by these old-version compatibility tests; never a T1/FG
restriction). `StepStmt` is already MIXED/withdrawn (A-COMB below); no new claim. -/

/-- The frozen old text is `CallDecOld` at `.gen` (definitional). -/
example (p q : SrcPkg ι dom) (k : Nat) : Old.CallDec p q k = CallDecOld (.gen p) (.gen q) k := rfl

theorem callDec_gen_group (p q : SrcPkg ι dom) (k : Nat) (hG : p.d.shape.instFields ≠ []) :
    CallDec (.gen p) (.gen q) k ↔ Old.CallDec p q k :=
  ⟨fun h => callDec_group_old (p := .gen p) (q := .gen q) (k := k) hG h,
   fun h => callDecOld_group (p := .gen p) (q := .gen q) (k := k) hG h⟩

/-- Every reached package is a group parent or has no calls (compatibility tests ONLY). -/
def GroupOnly (P : Lean.Name → Option (SrcPkg ι dom)) (Reach : Lean.Name → Prop) : Prop :=
  ∀ c, Reach c → ∀ q, P c = some q → q.d.shape.instFields ≠ [] ∨ q.d.shape.insts = []

theorem groupOnly_fields {P : Lean.Name → Option (SrcPkg ι dom)} {Reach : Lean.Name → Prop}
    (hGO : GroupOnly P Reach) {c : Lean.Name} (hc : Reach c) {q : SrcPkg ι dom} (hq : P c = some q) {k : Nat}
    (hk : k < q.d.shape.insts.length) : q.d.shape.instFields ≠ [] :=
  (hGO c hc q hq).resolve_right (fun he => absurd hk (by simp [he]))

/-! ## A-COMB (STEP_IFACE_FREEZE.md rev3 §3): `ChildShips` and its positive positions, `Old → new` only

`ChildShips` now takes `ChildRunN = SeqChildRunN ∨ CombChildRunN`, a weaker child guarantee. The frozen `Old.*` texts
are kept; the equalities they had are not re-established by a re-baseline. Classification of the checks this
changes:
* positive positions (`ChildShips`, `ShipsRes`, `ShipsAt`, `CacheShips`, `InvAt`): `Old → new` below (since G-POST,
  `ShipsRes`/`CacheShips`/`InvAt` with the new `InstClosed` conjunct as an explicit premise);
* mixed positions — `IHAt` (`InvAt` premise, `ShipsRes` conclusion), `BodyKeepsInv`/`ChildKeepsInv` (`InvAt` pre and
  post), `KeepBodyStmt`/`KeepChildStmt`, `StepStmt` (`ServedP (ShipsRes …)` premise, `ChildShips` conclusion),
  `ServedShipsStmt`: CHANGED, MIXED — no relation is claimed in either direction (the former `iHAt_eq`,
  `bodyKeepsInv_eq`, `childKeepsInv_eq`, `keepBody_eq`, `keepChild_eq`, `stepStmt_compat`, `servedShips_compat`
  are withdrawn; their acceptance at earlier SHAs stays valid as history);
* statements over all packages with `ChildShips` only in the conclusion (`MemParentStmt'`, `MemParentStmt`,
  `LeafStmt`): the `.gen`-restricted forms below (`Old` quantifies over `SrcPkg`, so it gives nothing for `.loop`);
* `T1Hyp`, `T1Stmt`: unaffected by A-COMB (no `ChildShips`); CALLFIELD makes `t1Hyp_iff` conditional on `GroupOnly`
  and `t1Stmt_compat` NEW → OLD under `GroupOnly` (section above). -/

theorem childShips_gen (q : SrcPkg ι dom) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Sparkle.IR.AST.Design) :
    Old.ChildShips q n mc Dc → ChildShips (.gen q) n mc Dc :=
  fun h dsn h1 h2 i => Or.inl (h dsn h1 h2 i)

/-! ## package assignments: positive transport at the lift -/
theorem lift_some {P : Lean.Name → Option (SrcPkg ι dom)} {c : Lean.Name} {q' : Pkg ι dom} :
    Pkgs.lift P c = some q' ↔ ∃ q, P c = some q ∧ q' = .gen q := by
  simp only [Pkgs.lift, Option.map_eq_some_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩

/- G-POST (scripts/gen2/GPOST_FREEZE.md §2): `ShipsRes` gained a third conjunct `InstClosed r`, which the frozen
`Old.ShipsRes` (git f1a4367f text) does not give. CHANGED: `shipsRes_lift`, `cacheShips_lift`, `invAt_lift` now take
that conjunct as an EXPLICIT premise (`hic`); `InstClosed` is not derived from `Old`. `shipsAt_lift` is unchanged
(`ShipsAt` has no `InstClosed`). -/
theorem shipsRes_lift (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (c : Lean.Name)
    (r : Tools.ShippingChildInv.Res) (hic : InstClosed r) :
    Old.ShipsRes L P c r → ShipsRes L (Pkgs.lift P) c r := by
  rintro ⟨h1, q, n, hq, hd, hc⟩
  exact ⟨h1, ⟨.gen q, n, lift_some.mpr ⟨q, hq, rfl⟩, hd, childShips_gen q n _ _ hc⟩, hic⟩

theorem shipsAt_lift (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (n : Nat) (c : Lean.Name)
    (r : Tools.ShippingChildInv.Res) : Old.ShipsAt L P n c r → ShipsAt L (Pkgs.lift P) n c r := by
  rintro ⟨h1, q, hq, hd, hc⟩
  exact ⟨h1, .gen q, lift_some.mpr ⟨q, hq, rfl⟩, hd, childShips_gen q n _ _ hc⟩

theorem cacheShips_lift (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (Reach : Lean.Name → Prop)
    (m : Std.HashMap Lean.Name Tools.ShippingChildInv.Res)
    (hic : ∀ c r, Reach c → m.get? c = some r → InstClosed r) :
    Old.CacheShips L P Reach m → CacheShips L (Pkgs.lift P) Reach m :=
  fun h c r hR hm => shipsRes_lift L P c r (hic c r hR hm) (h c r hR hm)

theorem invAt_lift (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (Reach : Lean.Name → Prop)
    (D : Nat) (w : Void IO.RealWorld)
    (hic : ∀ c r, Reach c → (Tools.ShippingChildBndCore.cv w).get? c = some r → InstClosed r) :
    Old.InvAt L P Reach D w → InvAt L (Pkgs.lift P) Reach D w :=
  fun h => ⟨h.1, cacheShips_lift L P Reach (Tools.ShippingChildBndCore.cv w) hic h.2⟩

theorem t1Hyp_iff (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (Reach : Lean.Name → Prop)
    (DataOk : SrcPkg ι dom → Prop) (hGO : GroupOnly P Reach) :
    T1Hyp L (Pkgs.lift P) Reach (DataOkLiftCompat DataOk) ↔ Old.T1Hyp L P Reach DataOk := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨q', hq', hd, hdo⟩ := h.pkg c hc
      obtain ⟨q, hq, rfl⟩ := lift_some.mp hq'
      exact ⟨q, hq, hd, hdo⟩
    · intro c hc q hq; exact h.defines c hc (.gen q) (lift_some.mpr ⟨q, hq, rfl⟩)
    · intro c hc q hq; exact h.closes c hc (.gen q) (lift_some.mpr ⟨q, hq, rfl⟩)
    · intro c hc q hq k hk
      have hGq := groupOnly_fields hGO hc hq hk
      rcases h.dec c hc (.gen q) (lift_some.mpr ⟨q, hq, rfl⟩) k hk with hm | ⟨q2', hq2', hcd⟩
      · exact Or.inl hm
      · obtain ⟨q2, hq2, rfl⟩ := lift_some.mp hq2'
        exact Or.inr ⟨q2, hq2, (callDec_gen_group q q2 k hGq).mp hcd⟩
    · intro c hc q hq k hk hn; exact h.closed c hc (.gen q) (lift_some.mpr ⟨q, hq, rfl⟩) k hk hn
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨q, hq, hd, hdo⟩ := h.pkg c hc
      exact ⟨.gen q, lift_some.mpr ⟨q, hq, rfl⟩, hd, hdo⟩
    · intro c hc q' hq'
      obtain ⟨q, hq, rfl⟩ := lift_some.mp hq'
      exact h.defines c hc q hq
    · intro c hc q' hq'
      obtain ⟨q, hq, rfl⟩ := lift_some.mp hq'
      exact h.closes c hc q hq
    · intro c hc q' hq' k hk
      obtain ⟨q, hq, rfl⟩ := lift_some.mp hq'
      have hGq := groupOnly_fields hGO hc hq hk
      rcases h.dec c hc q hq k hk with hm | ⟨q2, hq2, hcd⟩
      · exact Or.inl hm
      · exact Or.inr ⟨.gen q2, lift_some.mpr ⟨q2, hq2, rfl⟩, (callDec_gen_group q q2 k hGq).mpr hcd⟩
    · intro c hc q' hq' k hk hn
      obtain ⟨q, hq, rfl⟩ := lift_some.mp hq'
      exact h.closed c hc q hq k hk hn

/-! ## statements over all packages: `.gen`-restricted forms (A-COMB; STEP_IFACE_FREEZE.md rev3 §3, R2) -/
theorem memParentStmt'_gen (L : Laws mref cref) : Old.MemParentStmt' (ι := ι) (dom := dom) L →
    ∀ (q : SrcPkg ι dom) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (w w1 : Void IO.RealWorld)
      (raw b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      MemParentDataOk (.gen q) → ExtInS (.gen q) → MemOrigin (.gen q) →
      q.d.shape.insts ≠ [] → q.d.shape.instFields ≠ [] → q.d.shape.layout.slots ≠ [] →
      Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx →
      Tools.ShippingChildCacheA.JQC L.O (Tools.ShippingChildBndCore.dv w) w →
      Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore q.decl [] false)
        mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref q.decl q.d.shape →
      MachineTaken L mctx cctx (Tools.ShippingChildBndCore.dv w + 1) q.decl q.d.shape raw D →
      (∀ k (hk : k < q.d.shape.insts.length), MemDec (.gen q) k (q.d.shape.insts[k]).1) →
      ∀ n, TopShips (.gen q) (n + 1) q.decl b raw D ∧ ChildShips (.gen q) (n + 1) b D := by
  intro h q mctx cctx w w1 raw b D h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 n
  have := h q mctx cctx w w1 raw b D h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 n
  exact ⟨this.1, childShips_gen q _ _ _ this.2⟩

theorem memParentStmt_gen (L : Laws mref cref) (DataOk : SrcPkg ι dom → Prop) :
    Old.MemParentStmt L DataOk →
    ∀ (q : SrcPkg ι dom) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (w w1 : Void IO.RealWorld)
      (raw b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      DataOkLiftCompat DataOk (.gen q) → q.d.shape.layout.slots ≠ [] →
      Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx →
      Tools.ShippingChildCacheA.JQC L.O (Tools.ShippingChildBndCore.dv w) w →
      Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore q.decl [] false)
        mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref q.decl q.d.shape →
      MachineTaken L mctx cctx (Tools.ShippingChildBndCore.dv w + 1) q.decl q.d.shape raw D →
      (∀ k (hk : k < q.d.shape.insts.length), MemDec (.gen q) k (q.d.shape.insts[k]).1) →
      ∀ n, TopShips (.gen q) (n + 1) q.decl b raw D ∧ ChildShips (.gen q) (n + 1) b D := by
  intro h q mctx cctx w w1 raw b D h1 h2 h3 h4 h5 h6 h7 h8 h9 n
  have := h q mctx cctx w w1 raw b D h1 h2 h3 h4 h5 h6 h7 h8 h9 n
  exact ⟨this.1, childShips_gen q _ _ _ this.2⟩

theorem leafStmt_gen (L : Laws mref cref) (DataOk : SrcPkg ι dom → Prop) :
    Old.LeafStmt L DataOk →
    ∀ (q : SrcPkg ι dom) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (w w1 : Void IO.RealWorld)
      (raw b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      DataOkLiftCompat DataOk (.gen q) → q.d.shape.insts = [] →
      Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx cctx →
      Tools.ShippingChildCacheA.JQC L.O (Tools.ShippingChildBndCore.dv w) w →
      Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore q.decl [] false)
        mctx mref cctx cref w (raw, D) w1 →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
        b = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref q.decl q.d.shape →
      MachineTaken L mctx cctx (Tools.ShippingChildBndCore.dv w + 1) q.decl q.d.shape raw D →
      ∀ n, TopShips (.gen q) n q.decl b raw D ∧ ChildShips (.gen q) n b D := by
  intro h q mctx cctx w w1 raw b D h1 h2 h3 h4 h5 h6 h7 h8 n
  have := h q mctx cctx w w1 raw b D h1 h2 h3 h4 h5 h6 h7 h8 n
  exact ⟨this.1, childShips_gen q _ _ _ this.2⟩

theorem t1Stmt_compat (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (Reach : Lean.Name → Prop)
    (DataOk : SrcPkg ι dom → Prop) (hGO : GroupOnly P Reach) :
    T1Stmt L (Pkgs.lift P) Reach (DataOkLiftCompat DataOk) → Old.T1Stmt L P Reach DataOk := by
  intro h hT c mctx cctx w w1 raw b D hR hS hcore hpost
  obtain ⟨q', n, hq', hts⟩ := h ((t1Hyp_iff L P Reach DataOk hGO).mpr hT) c mctx cctx w w1 raw b D hR hS hcore hpost
  obtain ⟨q, hq, rfl⟩ := lift_some.mp hq'
  exact ⟨q, n, hq, hts⟩

#print axioms callDec_gen_group
#print axioms groupOnly_fields
#print axioms childShips_gen
#print axioms shipsRes_lift
#print axioms invAt_lift
#print axioms memParentStmt'_gen
#print axioms memParentStmt_gen
#print axioms leafStmt_gen
#print axioms t1Hyp_iff
#print axioms t1Stmt_compat

end Tests.Gen2.PkgCompat
