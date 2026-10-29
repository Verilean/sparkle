import Tools.ShippingGen2MemShips
set_option autoImplicit false

/-! # loop-pkg step 2: compatibility of the `Pkg` refactor (LOOPPKG_FREEZE.md §6 rules)

`Tools.ShippingGen2.Old.*` are the OLD texts (git f1a4367f) of every changed definition, verbatim (unchanged
definitions — `Laws`, `MachineTaken`, `ServedP`, … — are the current ones). Checks:
* pointwise definitions: `X (.gen p) … = Old.X p …` by `rfl`;
* definitions taking a package assignment: equal at `Pkgs.lift P` (functions, by `funext`/`propext`);
* `T1Hyp`: iff, with `DataOkLiftCompat` (compatibility tests only);
* statements quantifying over all packages: NEW → OLD only (the new ones include the loop case). -/
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

/-! ## pointwise: `rfl` at `.gen` -/
example (q : SrcPkg ι dom) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Sparkle.IR.AST.Design) :
    ChildShips (.gen q) n mc Dc = Old.ChildShips q n mc Dc := rfl
example (p q : SrcPkg ι dom) (k : Nat) : CallDec (.gen p) (.gen q) k = Old.CallDec p q k := rfl
example (p : SrcPkg ι dom) (k : Nat) (c : Lean.Name) : MemDec (.gen p) k c = Old.MemDec p k c := rfl
example (p : SrcPkg ι dom) (n : Nat) (c : Lean.Name) (b raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) :
    TopShips (.gen p) n c b raw D = Old.TopShips p n c b raw D := rfl
example (p : SrcPkg ι dom) : MemParentDataOk (.gen p) = Old.MemParentDataOk p := rfl
example (p : SrcPkg ι dom) : ExtInS (.gen p) = Old.ExtInS p := rfl
example (p : SrcPkg ι dom) : MemOrigin (.gen p) = Old.MemOrigin p := rfl

/-! ## package assignments: equal at the lift -/
theorem lift_some {P : Lean.Name → Option (SrcPkg ι dom)} {c : Lean.Name} {q' : Pkg ι dom} :
    Pkgs.lift P c = some q' ↔ ∃ q, P c = some q ∧ q' = .gen q := by
  simp only [Pkgs.lift, Option.map_eq_some_iff]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩

theorem shipsRes_eq (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) :
    ShipsRes L (Pkgs.lift P) = Old.ShipsRes L P := by
  funext c r
  apply propext
  constructor
  · rintro ⟨h1, q', n, hq', hd, hc⟩
    obtain ⟨q, hq, rfl⟩ := lift_some.mp hq'
    exact ⟨h1, q, n, hq, hd, hc⟩
  · rintro ⟨h1, q, n, hq, hd, hc⟩
    exact ⟨h1, .gen q, n, lift_some.mpr ⟨q, hq, rfl⟩, hd, hc⟩

theorem shipsAt_eq (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) :
    ShipsAt L (Pkgs.lift P) = Old.ShipsAt L P := by
  funext n c r
  apply propext
  constructor
  · rintro ⟨h1, q', hq', hd, hc⟩
    obtain ⟨q, hq, rfl⟩ := lift_some.mp hq'
    exact ⟨h1, q, hq, hd, hc⟩
  · rintro ⟨h1, q, hq, hd, hc⟩
    exact ⟨h1, .gen q, lift_some.mpr ⟨q, hq, rfl⟩, hd, hc⟩

theorem cacheShips_eq (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) :
    CacheShips L (Pkgs.lift P) = Old.CacheShips L P := by
  funext Reach m
  unfold CacheShips Old.CacheShips
  rw [shipsRes_eq]

theorem invAt_eq (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) :
    InvAt L (Pkgs.lift P) = Old.InvAt L P := by
  funext Reach D
  unfold InvAt Old.InvAt
  rw [cacheShips_eq]

theorem iHAt_eq (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) :
    IHAt L (Pkgs.lift P) = Old.IHAt L P := by
  funext Reach D
  unfold IHAt Old.IHAt
  rw [invAt_eq, shipsRes_eq]

theorem bodyKeepsInv_eq (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) :
    BodyKeepsInv L (Pkgs.lift P) = Old.BodyKeepsInv L P := by
  funext Reach D
  unfold BodyKeepsInv Old.BodyKeepsInv
  rw [invAt_eq]

theorem childKeepsInv_eq (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) :
    ChildKeepsInv L (Pkgs.lift P) = Old.ChildKeepsInv L P := by
  funext Reach D
  unfold ChildKeepsInv Old.ChildKeepsInv
  rw [invAt_eq]

theorem keepBody_eq (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (Reach : Lean.Name → Prop) :
    KeepBodyStmt L (Pkgs.lift P) Reach = Old.KeepBodyStmt L P Reach := by
  unfold KeepBodyStmt Old.KeepBodyStmt
  rw [childKeepsInv_eq, bodyKeepsInv_eq]

theorem keepChild_eq (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (Reach : Lean.Name → Prop) :
    KeepChildStmt L (Pkgs.lift P) Reach = Old.KeepChildStmt L P Reach := by
  unfold KeepChildStmt Old.KeepChildStmt
  rw [bodyKeepsInv_eq, iHAt_eq, childKeepsInv_eq]

theorem t1Hyp_iff (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (Reach : Lean.Name → Prop)
    (DataOk : SrcPkg ι dom → Prop) :
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
      rcases h.dec c hc (.gen q) (lift_some.mpr ⟨q, hq, rfl⟩) k hk with hm | ⟨q2', hq2', hcd⟩
      · exact Or.inl hm
      · obtain ⟨q2, hq2, rfl⟩ := lift_some.mp hq2'
        exact Or.inr ⟨q2, hq2, hcd⟩
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
      rcases h.dec c hc q hq k hk with hm | ⟨q2, hq2, hcd⟩
      · exact Or.inl hm
      · exact Or.inr ⟨.gen q2, lift_some.mpr ⟨q2, hq2, rfl⟩, hcd⟩
    · intro c hc q' hq' k hk hn
      obtain ⟨q, hq, rfl⟩ := lift_some.mp hq'
      exact h.closed c hc q hq k hk hn

/-! ## statements over all packages: NEW → OLD -/
theorem memParentStmt'_compat (L : Laws mref cref) :
    MemParentStmt' (ι := ι) (dom := dom) L → Old.MemParentStmt' (ι := ι) (dom := dom) L :=
  fun h p => h (.gen p)

theorem memParentStmt_compat (L : Laws mref cref) (DataOk : SrcPkg ι dom → Prop) :
    MemParentStmt L (DataOkLiftCompat DataOk) → Old.MemParentStmt L DataOk :=
  fun h p => h (.gen p)

theorem leafStmt_compat (L : Laws mref cref) (DataOk : SrcPkg ι dom → Prop) :
    LeafStmt L (DataOkLiftCompat DataOk) → Old.LeafStmt L DataOk :=
  fun h p => h (.gen p)

theorem stepStmt_compat (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (DataOk : SrcPkg ι dom → Prop) :
    StepStmt L (Pkgs.lift P) (DataOkLiftCompat DataOk) → Old.StepStmt L P DataOk := by
  intro h p mctx cctx w w1 raw b D hP hd hA hjqc hcore hpost hdef ht hdec htr
  refine h (.gen p) mctx cctx w w1 raw b D (lift_some.mpr ⟨p, hP, rfl⟩) hd hA hjqc hcore hpost hdef ht ?_ ?_
  · intro k hk
    rcases hdec k hk with hm | ⟨q, hq, hc⟩
    · exact Or.inl hm
    · exact Or.inr ⟨.gen q, lift_some.mpr ⟨q, hq, rfl⟩, hc⟩
  · rw [shipsRes_eq]; exact htr

theorem t1Stmt_compat (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (Reach : Lean.Name → Prop)
    (DataOk : SrcPkg ι dom → Prop) :
    T1Stmt L (Pkgs.lift P) Reach (DataOkLiftCompat DataOk) → Old.T1Stmt L P Reach DataOk := by
  intro h hT c mctx cctx w w1 raw b D hR hS hcore hpost
  obtain ⟨q', n, hq', hts⟩ := h ((t1Hyp_iff L P Reach DataOk).mpr hT) c mctx cctx w w1 raw b D hR hS hcore hpost
  obtain ⟨q, hq, rfl⟩ := lift_some.mp hq'
  exact ⟨q, n, hq, hts⟩

theorem servedShips_compat (L : Laws mref cref) (P : Lean.Name → Option (SrcPkg ι dom)) (Reach : Lean.Name → Prop)
    (DataOk : SrcPkg ι dom → Prop) :
    ServedShipsStmt L (Pkgs.lift P) Reach (DataOkLiftCompat DataOk) → Old.ServedShipsStmt L P Reach DataOk := by
  intro h hT p mctx cctx w w' raw D hR hP hA hinv hih hck hcore
  have := h ((t1Hyp_iff L P Reach DataOk).mpr hT) (.gen p) mctx cctx w w' raw D hR (lift_some.mpr ⟨p, hP, rfl⟩) hA
    (by rw [invAt_eq]; exact hinv) (by rw [iHAt_eq]; exact hih) (by rw [childKeepsInv_eq]; exact hck) hcore
  rw [shipsRes_eq] at this
  exact this

#print axioms shipsRes_eq
#print axioms t1Hyp_iff
#print axioms stepStmt_compat
#print axioms t1Stmt_compat
#print axioms servedShips_compat
#print axioms keepChild_eq

end Tests.Gen2.PkgCompat
