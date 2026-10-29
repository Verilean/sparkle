-- scripts/gen2/GEN2_DEFS.lean.txt — exact text of the gen2 definitions and statements (GENERAL_SPEC.md rev1 §1, §3, §8).
-- Status: elaborated verbatim as Tools/ShippingGen2Defs.lean (cmp-identical; GENERAL_SPEC.md §8.1 lists the builds).
-- Every `…Stmt` is a `def … : Prop` (a statement, no proof, no sorry). Non-semantic corrections (names, opens,
-- annotations) are made in U0 and collected for the result review; semantic changes are listed in GENERAL_SPEC §0.

import Tools.ShippingSrm33Core
import Tools.ShippingMachineDepthRunRA
import Tools.ShippingMachineCallsLinkedTNR
import Tools.ShippingQuadComposed
import Tools.ShippingServedRealA

set_option autoImplicit false

namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
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

/-! ## 1. The source package of one declaration (G3, per declaration; §6 inventory G3-GEN) -/

/-- The generated facts of one declaration as one package: `Tests.Compiler.CDef.GenPkg` (CDefTest.lean:33) moved
to `Tools` unchanged, plus `kD`, the number of declared (non-call-result) binders. -/
structure SrcPkg (ι : Type) (dom : ι → DomainConfig) where
  decl : Name
  d : MachineData
  kD : Nat
  ρ : ι → Type
  inh : Inhabited (HList (tys d.ss))
  inits : HList (tys d.ss)
  body : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
    Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i)
  obsR : (i : ι) → ρ i → List (Nat → Nat)
  ext : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)
  extB : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys d.ss)) → Nat → Signal (dom i) Bool
  src : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    List (Nat → Nat)
  gen : @GenFacts d ι dom ρ inh inits body obsR ext extB src

variable {ι : Type} {dom : ι → DomainConfig}

noncomputable def SrcPkg.extS (p : SrcPkg ι dom) := fun i bools bits =>
  p.ext i bools bits (@stateLoop _ _ _ p.inh p.inits (p.body i bools bits))
noncomputable def SrcPkg.extBS (p : SrcPkg ι dom) := fun i bools bits =>
  p.extB i bools bits (@stateLoop _ _ _ p.inh p.inits (p.body i bools bits))
noncomputable def SrcPkg.lsrc (p : SrcPkg ι dom) :=
  @Tools.ShippingMachineCausal.letObsB p.d ι dom p.inh p.ρ p.inits p.body p.ext p.extB
/-- The declared, non-domain ports of `p` (the child interface's binder list). -/
def SrcPkg.ports (p : SrcPkg ι dom) : List (Name × MixedGateBinder) :=
  (p.d.bsIn.take p.kD).filter fun b => b.2 != .domain
/-- The child-interface source function: `p.src` on the boolean/bit-vector signals decoded from port values
(the shape of C4's `tieSrcC`, CDefTest.lean:111). -/
noncomputable def SrcPkg.S (p : SrcPkg ι dom) (i : ι) : (Nat → List Nat) → List (Nat → Nat) :=
  fun vals => p.src i (boolsOf (D := dom i) (p.d.bsIn.take p.kD) vals)
    (bitsOf (D := dom i) (p.d.bsIn.take p.kD) vals)

/-- A package assignment: the package of every declaration a run reaches, or `none`. The G3 premise is that it is
correct where it is `some` (`PkgOk`). -/
abbrev Pkgs (ι : Type) (dom : ι → DomainConfig) := Name → Option (SrcPkg ι dom)

/-! ## 2. Runtime laws (G5) — kept apart from the start conditions -/

/-- The uniform runtime laws (G5): the same for every declaration. -/
structure Laws (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State) where
  O : RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref
  T : RefLawsATele O.quiet mref cref

/-- The start conditions of an OUTERMOST compilation: admissible contexts and the depth-0 world with its cache
invariant. They are conditions on the start, not laws. -/
def Start {mref cref} (L : Laws mref cref) (mctx : Meta.Context) (cctx : Core.Context) (w : Void IO.RealWorld) : Prop :=
  AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w

/-! ## 3. The child interface (what a parent consumes) and the call decoding (what the parent's package provides) -/

/-- **ChildShips** (the IH content of `c`, for THE result `(mc, Dc)` a parent was served): for every design `dsn`
that contains `Dc`'s modules and `mc`, the child run interface at height `n`, with the interface data taken from
`c`'s own package `q`. Built-in transport: it is stated for every extending `dsn`, so the producer proves the
transport once (gap G-TRANSPORT). -/
def ChildShips (q : SrcPkg ι dom) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Design) : Prop :=
  ∀ (dsn : Design), (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) →
    moduleByName dsn.modules mc.name = some mc →
    ∀ (i : ι), SeqChildRunN (childMap dsn.modules) dsn n mc (q.d.bsIn.take q.kD) q.d.shape.layout.outs (q.S i)

/-- **CallDec** (gap G-CALLDEC; the non-run conjuncts of `SeqFactsRN`, CallsLinkedTNR.lean:23): the parent `p`'s
ordinary call `k` to `c` (package `q`) has its arguments among `p`'s lets, in range for `q`'s ports, and the
parent's call-result signal at position `p.kD + k` equals `q`'s source output named by the call's field. -/
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

/-- The memory side of one entry: `MemFacts` of the parent's own package (it mentions the parent's call arguments,
so it is a fact of the PARENT, not a child interface; gap G-MEMCALLS supplies it). -/
def MemDec (p : SrcPkg ι dom) (k : Nat) (c : Name) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    MemFacts p.d.shape (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extS i bools bits) k c

/-! ## 4. Route evidence, T1 hypotheses, the IH, and the served-child evidence -/

open Tools.ShippingChildBndCore (cv dv)
open Tools.ShippingChildInv (Res Keeps profLogIO)
open Tools.ShippingChildRunAKids (MachineClosesAtA)
open Tools.ShippingServedRealA (MachineRunJQC)

/-- **Route evidence of THIS run**: the machine synthesis the core run performs returned the run's result
(`MachineRunJQC`, ServedRealA.lean:86) — the machine route was TAKEN, not only read (`MachineDefines` alone says
`machineShape? = some`; it does not exclude the fall-back to the legacy route). -/
abbrev MachineTaken {mref cref} (L : Laws mref cref) (mctx : Meta.Context) (cctx : Core.Context) (n : Nat)
    (c : Name) (shape : MachineShape) (raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  MachineRunJQC L.O mctx cctx n c shape raw D

/-- A result `r` of `c` with the package and height it ships at. -/
def ShipsRes {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (c : Name) (r : Res) : Prop :=
  RealChildA L.O c r ∧ ∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2

/-- The child-cache invariant, ON THE REACHED declarations: every `sparkleChildCache` entry of a reached name ships.
Entries of other names (children the translator synthesises on other routes) are unconstrained, so their insertion
keeps it. `sparkleSubModuleCache` (the memo of route 5) is a different map and is NOT covered (gap G-MEMO). -/
def CacheShips {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (m : Std.HashMap Name Res) : Prop :=
  ∀ c r, Reach c → m.get? c = some r → ShipsRes L P c r

/-- `ShipsRes` at a FIXED height `n` (what consumer 2 needs at its `n`; `ShipsRes` gives some height, G-LIFT
bridges). -/
def ShipsAt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (n : Nat) (c : Name) (r : Res) : Prop :=
  RealChildA L.O c r ∧ ∃ q, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2

/-- **The cache/child invariant at depth `D`**: `JQC` and `CacheShips` on the reached names. -/
def InvAt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) :
    Void IO.RealWorld → Prop :=
  fun w => JQC L.O D w ∧ CacheShips L P Reach (cv w)

/-- **The success half of the induction hypothesis at depth `D`**: every SUCCESSFUL run of a REACHED declaration's
entry from an `InvAt D` world, in an admissible context, ships. (The all-outcome cache half is `ChildKeepsInv` /
`BodyKeepsInv`; `IHAt` alone says nothing about throwing runs.) -/
def IHAt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ c, Reach c → ∀ (mctx : Meta.Context) (cctx : Core.Context) (u u' : Void IO.RealWorld) (r : Res),
    AdmCtx L.O.quiet mctx cctx → InvAt L P Reach D u →
    RunsTo (synthesizeCombinational c) mctx mref cctx cref u r u' →
    ShipsRes L P c r

/-- **All-outcome keep of the body at depth `D`** (the `BodyKeepsP` shape, ChildPinC.lean:305, with `JQP` replaced by
`InvAt`): the synthesis body of EVERY declaration, on every route, keeps `InvAt` — returning or throwing (`Keeps`
constrains `endW` of every outcome and asks `ErrOk`, ChildInv.lean:306-316). -/
def BodyKeepsInv {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context), AdmCtx L.O.quiet mctx cctx →
    ∀ (declName : Name) (tenv : Lean.Environment) (b : Bool) (ci : ConstantInfo) (isInst : Lean.Expr → Bool),
      Keeps mctx mref cctx cref (InvAt L P Reach D)
        (synthesizeFromConst (fun e h t n => translateExprToWire tenv e h t n) (profLogIO b)
          declName [] false true ci isInst)

/-- **All-outcome keep of the child entry at depth `D`**, for EVERY name (`ChildSynthA`, ChildFrontCP.lean:240). -/
def ChildKeepsInv {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) (D : Nat) : Prop :=
  Tools.ShippingChildFrontCP.ChildSynthA L.O (InvAt L P Reach D)

/-- **G-KEEP-BODY** (generalises `bodyKeepsP_of_tele`, ChildPinC.lean:329, whose components take a `StableA`
invariant): the child hook at `D` gives the body's all-outcome keep at `D`. -/
def KeepBodyStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ D, ChildKeepsInv L P Reach D → BodyKeepsInv L P Reach D

/-- **G-KEEP-CHILD** (generalises `childKeepsP_of_body`, ChildPinC.lean:346): the child entry at `D` keeps `InvAt D`
on every outcome, from the body's keep one level deeper (the nested run, including a child that throws after
partially synthesising its own children) and, for the insertion of a REACHED name's result, the SUCCESS semantics
`IHAt` of that run. -/
def KeepChildStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop) : Prop :=
  ∀ D, 1 ≤ D → (D < sparkleSynthDepthLimit → BodyKeepsInv L P Reach (D + 1)) →
    IHAt L P Reach D → ChildKeepsInv L P Reach D

/-- **The hypotheses of T1 on the reached declarations.** `DataOk` is a PLACEHOLDER Prop parameter: U0 fixes it to
a concrete conjunction of Bool checks over `q.d` (GENERAL_SPEC §4.4); no unit may instantiate it so that a statement
becomes vacuous, and every unit's acceptance includes a vacuity audit (a concrete package satisfying it). -/
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

/-- `ServedRealGA` (ServedRealA.lean:45-58) with `RealChildA O` replaced by `Q`; every other part VERBATIM (the
`connsG` instance, the `machPorts` map of `outs`, `∃ e ∈ outs, e.1 = k`, the same `ids`/`cache`). -/
def ServedGP (Q : Name → Res → Prop) (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) : Prop :=
  shape.instFields ≠ [] →
  ∀ k (hk : k < shape.insts.length) (mc : Sparkle.IR.AST.Module) (iname : String)
    (argWs : List String) (outs : List (Nat × String)) (outWs : List String),
    Stmt.inst mc.name iname (Tools.ShippingMachineLinkedT.connsG mc argWs outs outWs) ∈ m.body →
    outs.mapM (fun (j, _) =>
      ((machPorts declName ids cache shape.binders).map (·.name))[machNIn shape + j]?) = some outWs →
    (∃ e ∈ outs, e.1 = k) →
    moduleByName dsn.modules mc.name = some mc →
    (∃ md, (shape.instOrigins.getD k .ord).child? = some md ∧ mc = md.1) ∨
      ∃ Dc, Q (shape.insts[k]).1 (mc, Dc) ∧ ∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g

/-- `ServedReal1A` (ServedRealA.lean:60-72) with `RealChildA O` replaced by `Q`; every other part VERBATIM
(`CallStmt … k args mc st`). -/
def Served1P (Q : Name → Res → Prop) (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) : Prop :=
  shape.instFields = [] →
  ∀ k (hk : k < shape.insts.length) (args : List Nat) (mc : Sparkle.IR.AST.Module) (st : Stmt),
    (shape.insts.map (·.2.1))[k]? = some args → st ∈ m.body →
    Tools.ShippingMachineInst.CallStmt (machNIn shape) shape.insts.length shape.layout.slots.length
      ((machPorts declName ids cache shape.binders).map (·.name)) k args mc st →
    moduleByName dsn.modules mc.name = some mc →
    (∃ md, (shape.instOrigins.getD k .ord).child? = some md ∧ mc = md.1) ∨
      ∃ Dc, Q (shape.insts[k]).1 (mc, Dc) ∧ ∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g

def ServedP (Q : Name → Res → Prop) (declName : Name) (shape : MachineShape) (m : Sparkle.IR.AST.Module) (dsn : Design)
    (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) : Prop :=
  ServedGP Q declName shape m dsn ids cache ∧ Served1P Q declName shape m dsn ids cache

/-- **G-SERVED**: the existing producer of `MachineTraceLBX (ServedRealA O …)` (`genTrace` on the run,
QuadComposed.lean:156, through `synthesizeCombinationalCore_machine_soundRA_A`) generalised to
`X := ServedP (ShipsRes L P)`: in a run of a reached declaration from a `CacheShips` world, under both halves of the IH one level
deeper, the trace holds with every served non-memory instance shipping — THE `(mc, Dc)` of call `k`, with the same
`ids`/`cache` witness as the trace. (`CacheShips` at the end is `BodyKeepsInv`'s, not this statement's.) -/
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

/-- `PC` for consumer 2 from the served evidence (the right disjunct of `ServedGP`): the module is in the design and is
served to call `k`'s callee by a `Q` result whose modules are in the design. -/
def ServedPC (Q : Name → Res → Prop) (dsn : Design) : Name → Sparkle.IR.AST.Module → Prop :=
  fun c mc => moduleByName dsn.modules mc.name = some mc ∧
    ∃ Dc, Q c (mc, Dc) ∧ ∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g

/-! ## 5. The one-level rule and the first theorems (statements) -/

/-- The top-level conclusion for package `p` at height `n`: exactly the conclusion of
`machine_ships_hierC_noHstR` (Srm33Core.lean:85-114) with `d := p.d`, `src := p.src`, `ext := p.extS`,
`extB := p.extBS`, `kD := p.kD`. -/
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

/-- **The one-level rule** (M2-b): a machine-route run (route evidence `MachineTaken`) of `p.decl` whose every entry
is a memory call with `MemDec` or an ordinary call with `CallDec`, and whose trace has every served non-memory
instance shipping (`ServedP (ShipsRes L P)`, the output of G-SERVED, k ↔ instance kept), ships at the top and as a
child at some height (one more than the children's, after G-LIFT). -/
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

/-- **First proof unit** (M2-a, `memParent_ships`): every entry a memory call. No served-children premise: the
trace with `ServedRealA` comes from `genTrace` on the run. Route evidence: the premise `MachineTaken`; for this case
it is also derivable from `memCallee_closesA` (Srm3Callee.lean:91) + `machineRunJQC_of_closesA` (ServedRealA.lean:97)
when `DataOk` contains `MemCalleeData`'s rows — a corollary, recorded, not a replacement of the premise. -/
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

/-- **Base case** (M2-a', a separate unit): an ordinary leaf (`insts = []`) ships at every height. -/
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

/-- **T1** (M3): every successful outermost compilation of a reached declaration ships, under `T1Hyp` (G3 per
reached declaration, the route-3 scope `closes`, the decodings, the static call closure). The route evidence of
each run is derived from `T1Hyp.defines`/`closes` (`machineRunJQC_of_closesA`); G-REACH, G-SERVED, G-CACHE and
G-MEMO are lemmas of its proof. -/
def T1Stmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : SrcPkg ι dom → Prop) : Prop :=
  T1Hyp L P Reach DataOk →
  ∀ (c : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld) (raw b : Sparkle.IR.AST.Module) (D : Design),
    Reach c → Start L mctx cctx w →
    RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    ∃ q n, P c = some q ∧ TopShips q n c b raw D

end Tools.ShippingGen2
