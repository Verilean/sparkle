import Tools.ShippingGen4IfaceR
import Tools.ShippingGen4GateLeafR
import Tools.ShippingGen4GateIfaceR
import Tools.ShippingGen4GateOutTyR
import Tools.ShippingGen4FirstLeafR
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT. U-GC0 (scripts/gen2/GATE_GC0_FREEZE.md §4): checks of the gate Lean transferred to base 15cd9d1f.

/-! # U-GC0 checks
1. TYPE: each moved/changed declaration against an independent statement written here from the base `ChildShips` /
   `ShipsRes` (Tools/ShippingGen2Defs.lean), not from the transferred files.
2. MUTANT: signature/defeq rejections of well-typed propositions by the same comparer, NOT semantic counterexamples.
3. BINDER SET: the fully qualified constants of each statement's type, restricted to the gate vocabulary, equal an expected
   set; decoy declarations with the same short names in `Tests.Gen4.GateGC0Check.Decoy` must be rejected by that check.
4. CLOSURE: from the main theorems, over all namespaces and explicit bodies, no `Laws.T` / `T1Hyp` / `T1HypND` /
   `RefLawsATele` is reached (opaque bodies are not traversed and are listed).
5. AXIOMS: propext / Classical.choice / Quot.sound only. -/

namespace Tests.Gen4.GateGC0Check
open Sparkle.IR.Type (HWType)
open Tools.ShippingMachineEntry (kindTy)
open Lean Meta
open Sparkle.Core.Domain (DomainConfig)
open Sparkle.Compiler.Elab (MixedGateBinder)
open Sparkle.IR.Machine (moduleByName)
open Sparkle.IR.AST (Design)
open Tools.ShippingChildInv (Res)
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingChildInvA (RefLawsAOps)
open Tools.ShippingChildFresh (MkRefd)
open Tools.ShippingEntrySoundness (quoteDecl)
open Tools.ShippingGen2
open Tests.Gen3.ExpectedType

variable {ι : Type} {dom : ι → DomainConfig}

/-! ## 1. Expected statements -/
def ExpPortWidthsI : ChildIface ι → Sparkle.IR.AST.Module → Prop :=
  fun I mc => (Tools.ShippingMachineCompose.argPorts mc).map (fun p => p.ty.bitWidth) =
    I.ports.map (fun b => (kindTy b.2).bitWidth)

def ExpChildShipsI : ChildIface ι → Nat → Sparkle.IR.AST.Module → Design → Prop :=
  fun I n mc Dc =>
    (Tools.ShippingMachineCompose.argPorts mc).map (fun p => p.ty.bitWidth) =
      I.ports.map (fun b => (kindTy b.2).bitWidth) ∧
    ∀ (dsn : Design), (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) →
      moduleByName dsn.modules mc.name = some mc →
      ∀ (i : ι), ChildRunN (childMap dsn.modules) dsn n mc I.bsC I.outsC (I.S i)

def ExpShipsResI {mref cref} : Laws mref cref → IfaceMap ι → Name → Res → Prop :=
  fun L Q c r => RealChildA L.O c r ∧
    (∃ (I : ChildIface ι) (n : Nat), Q c = some I ∧ I.decl = c ∧ ChildShipsI I n r.1 r.2) ∧ InstClosed r

def ExpPortWidthsOfPkg : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (mc : Sparkle.IR.AST.Module),
    ChildPortWidthsI (ChildIface.ofPkg q) mc ↔ ChildPortWidths q mc

def ExpChildShipsIOfPkg : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (q : Pkg ι dom) (n : Nat) (mc : Sparkle.IR.AST.Module) (Dc : Design),
    ChildShipsI (ChildIface.ofPkg q) n mc Dc ↔ ChildShips q n mc Dc

def ExpShipsResIIface : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (c : Name) (r : Res),
    ShipsResI L P.iface c r ↔ ShipsRes L P c r

def ExpInstClosedNil : Prop :=
  ∀ (y : Res) (hm : y.2.modules = []), InstClosed y

def ExpGatePortWidths : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (g : GateLeaf ι)
    (entry : EntryDefines mctx mref cctx cref g.decl g.value) {y : Res} (h : RealChildA O g.decl y) (ty : HWType),
    ChildPortWidthsI (g.ifaceOf ty) y.1

def ExpGateChildShips : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (g : GateLeaf ι)
    (entry : EntryDefines mctx mref cctx cref g.decl g.value) {y : Res} (h : RealChildA O g.decl y),
    y.2.modules = [] ∧ ∃ ty : HWType, y.1.outputs = [{ name := "out", ty := ty }] ∧
      ∀ n, ChildShipsI (g.ifaceOf ty) n y.1 y.2

def ExpGateShipsResI : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (g : GateLeaf ι) (Q : IfaceMap ι) {y : Res} {ty : HWType}
    (hQ : Q g.decl = some (g.ifaceOf ty)) (h : RealChildA L.O g.decl y)
    (hchild : ∀ n, ChildShipsI (g.ifaceOf ty) n y.1 y.2) (hinst : InstClosed y), ShipsResI L Q g.decl y

def ExpGateShipsResIOfReal : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (g : GateLeaf ι) (Q : IfaceMap ι)
    (entry : EntryDefines mctx mref cctx cref g.decl g.value) {y : Res} (h : RealChildA L.O g.decl y)
    (hQ : ∀ ty : HWType, y.1.outputs = [{ name := "out", ty := ty }] → Q g.decl = some (g.ifaceOf ty)),
    ShipsResI L Q g.decl y

def ExpOutTy : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (g : GateLeaf ι)
    (entry : EntryDefines mctx mref cctx cref g.decl g.value) {y : Res} (h : RealChildA O g.decl y)
    (hw1 : g.srt.width ≠ 1),
    ∃ w : Nat, w = g.srt.width ∧ y.1.outputs = [{ name := "out", ty := .bitVector w }]

def ExpFirstPortWidths : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (f : FirstLeaf ι)
    (entry : EntryDefines mctx mref cctx cref f.decl (quoteDecl f.dn f.names f.n f.fe)) {y : Res}
    (h : RealChildA O f.decl y), ChildPortWidthsI f.ifaceOf y.1

def ExpFirstChildShips : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (f : FirstLeaf ι)
    (entry : EntryDefines mctx mref cctx cref f.decl (quoteDecl f.dn f.names f.n f.fe)) {y : Res}
    (h : RealChildA O f.decl y),
    y.2.modules = [] ∧ y.1.outputs = [{ name := "out", ty := .bitVector f.n }] ∧
      ∀ n, ChildShipsI f.ifaceOf n y.1 y.2

def ExpFirstShipsResI : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (f : FirstLeaf ι) (Q : IfaceMap ι) {y : Res}
    (hQ : Q f.decl = some f.ifaceOf) (h : RealChildA L.O f.decl y)
    (hchild : ∀ n, ChildShipsI f.ifaceOf n y.1 y.2) (hinst : InstClosed y), ShipsResI L Q f.decl y

def ExpFirstShipsResIOfReal : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (f : FirstLeaf ι) (Q : IfaceMap ι)
    (entry : EntryDefines mctx mref cctx cref f.decl (quoteDecl f.dn f.names f.n f.fe)) {y : Res}
    (h : RealChildA L.O f.decl y) (hQ : Q f.decl = some f.ifaceOf), ShipsResI L Q f.decl y

/-! ## 2. Mutants (well-typed, one clause changed) -/
/-- `ChildShipsI` without the port-width conjunct (the old g6 shape). -/
def MutChildShipsINoPW : ChildIface ι → Nat → Sparkle.IR.AST.Module → Design → Prop :=
  fun I n mc Dc => ∀ (dsn : Design), (∀ g ∈ Dc.modules, moduleByName dsn.modules g.name = some g) →
    moduleByName dsn.modules mc.name = some mc →
    ∀ (i : ι), ChildRunN (childMap dsn.modules) dsn n mc I.bsC I.outsC (I.S i)

/-- `ShipsResI` without `InstClosed` (the old g6 shape). -/
def MutShipsResINoInst {mref cref} : Laws mref cref → IfaceMap ι → Name → Res → Prop :=
  fun L Q c r => RealChildA L.O c r ∧ ∃ (I : ChildIface ι) (n : Nat), Q c = some I ∧ I.decl = c ∧ ChildShipsI I n r.1 r.2

/-- port widths over the unfiltered binders. -/
def MutPortWidthsUnfiltered : ChildIface ι → Sparkle.IR.AST.Module → Prop :=
  fun I mc => (Tools.ShippingMachineCompose.argPorts mc).map (fun p => p.ty.bitWidth) =
    I.bsC.map (fun b => (kindTy b.2).bitWidth)

def MutGateShipsResINoInst : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (g : GateLeaf ι) (Q : IfaceMap ι) {y : Res} {ty : HWType}
    (hQ : Q g.decl = some (g.ifaceOf ty)) (h : RealChildA L.O g.decl y)
    (hchild : ∀ n, ChildShipsI (g.ifaceOf ty) n y.1 y.2), ShipsResI L Q g.decl y

def MutFirstShipsResINoInst : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (f : FirstLeaf ι) (Q : IfaceMap ι) {y : Res}
    (hQ : Q f.decl = some f.ifaceOf) (h : RealChildA L.O f.decl y)
    (hchild : ∀ n, ChildShipsI f.ifaceOf n y.1 y.2), ShipsResI L Q f.decl y

def MutFirstChildShipsOutBit : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (f : FirstLeaf ι)
    (entry : EntryDefines mctx mref cctx cref f.decl (quoteDecl f.dn f.names f.n f.fe)) {y : Res}
    (h : RealChildA O f.decl y),
    y.2.modules = [] ∧ y.1.outputs = [{ name := "out", ty := .bit }] ∧
      ∀ n, ChildShipsI f.ifaceOf n y.1 y.2

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``ChildPortWidthsI ``ExpPortWidthsI
  checkExpected ``ChildShipsI ``ExpChildShipsI
  checkExpected ``ShipsResI ``ExpShipsResI
  checkExpected ``childPortWidthsI_ofPkg ``ExpPortWidthsOfPkg
  checkExpected ``childShipsI_ofPkg ``ExpChildShipsIOfPkg
  checkExpected ``shipsResI_iface ``ExpShipsResIIface
  checkExpected ``instClosed_of_nil ``ExpInstClosedNil
  checkExpected ``gateLeaf_childPortWidthsI ``ExpGatePortWidths
  checkExpected ``gateLeaf_childShips ``ExpGateChildShips
  checkExpected ``gateLeaf_shipsResI ``ExpGateShipsResI
  checkExpected ``gateLeaf_shipsResI_of_real ``ExpGateShipsResIOfReal
  checkExpected ``gateLeaf_outTy ``ExpOutTy
  checkExpected ``firstLeaf_childPortWidthsI ``ExpFirstPortWidths
  checkExpected ``firstLeaf_childShips ``ExpFirstChildShips
  checkExpected ``firstLeaf_shipsResI ``ExpFirstShipsResI
  checkExpected ``firstLeaf_shipsResI_of_real ``ExpFirstShipsResIOfReal
  checkMutant ``ChildShipsI ``MutChildShipsINoPW
  checkMutant ``ShipsResI ``MutShipsResINoInst
  checkMutant ``ChildPortWidthsI ``MutPortWidthsUnfiltered
  checkMutant ``gateLeaf_shipsResI ``MutGateShipsResINoInst
  checkMutant ``firstLeaf_shipsResI ``MutFirstShipsResINoInst
  checkMutant ``firstLeaf_childShips ``MutFirstChildShipsOutBit
  logInfo "U-GC0 COUNTS: TYPE 16, MUTANT 6 (signature/defeq rejections of well-typed propositions by the same comparer; not semantic counterexamples)"

/-! ## 3. Binder set by fully qualified names, with decoys -/
namespace Decoy
/-- same short names as the real ones, different constants. -/
def ChildShipsI (_I : ChildIface ι) (_n : Nat) (_mc : Sparkle.IR.AST.Module) (_Dc : Design) : Prop := True
def ShipsResI {mref cref} (_L : Laws mref cref) (_Q : IfaceMap ι) (_c : Name) (_r : Res) : Prop := True
def InstClosed (_r : Res) : Prop := True
theorem gateLeaf_shipsResI {ι : Type} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (g : GateLeaf ι) (Q : IfaceMap ι) {y : Res} {ty : HWType}
    (_hQ : Q g.decl = some (g.ifaceOf ty)) (_h : RealChildA L.O g.decl y)
    (_hchild : ∀ n, ChildShipsI (g.ifaceOf ty) n y.1 y.2) (_hinst : InstClosed y) : ShipsResI L Q g.decl y :=
  trivial
end Decoy

/-- Gate vocabulary of the statements: the constants whose identity matters. -/
def vocab : List Name :=
  [``ChildShipsI, ``ShipsResI, ``InstClosed, ``ChildPortWidthsI, ``ChildIface.ofPkg, ``GateLeaf.ifaceOf,
   ``FirstLeaf.ifaceOf, ``RealChildA, ``ChildShips, ``ShipsRes, ``ChildPortWidths,
   ``Decoy.ChildShipsI, ``Decoy.ShipsResI, ``Decoy.InstClosed]

/-- The vocabulary constants (fully qualified) in the statement of `thm` (type of a theorem, value of a definition) must be exactly `expected`. -/
def checkVocab (thm : Name) (expected : List Name) : MetaM Unit := do
  let used := (← stmtOf thm).getUsedConstants.toList.filter vocab.contains
  let ok := used.all expected.contains && expected.all used.contains
  unless ok do throwError "U-GC0 BINDER SET FAILED {thm}: vocabulary {used}, expected {expected}"
  logInfo m!"U-GC0 BINDER SET OK {thm}: {used}"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkVocab ``gateLeaf_shipsResI [``ChildShipsI, ``ShipsResI, ``InstClosed, ``GateLeaf.ifaceOf, ``RealChildA]
  checkVocab ``firstLeaf_shipsResI [``ChildShipsI, ``ShipsResI, ``InstClosed, ``FirstLeaf.ifaceOf, ``RealChildA]
  checkVocab ``ShipsResI [``ChildShipsI, ``InstClosed, ``RealChildA]
  checkVocab ``ChildShipsI [``ChildPortWidthsI]
  checkVocab ``shipsResI_iface [``ShipsResI, ``ShipsRes]
  checkVocab ``childShipsI_ofPkg [``ChildShipsI, ``ChildShips, ``ChildIface.ofPkg]
  -- decoy: the same statement shape over the decoy constants must be rejected against the real expectation
  let rejected ← try
      checkVocab ``Decoy.gateLeaf_shipsResI [``ChildShipsI, ``ShipsResI, ``InstClosed, ``GateLeaf.ifaceOf, ``RealChildA]
      pure false
    catch _ => pure true
  unless rejected do throwError "U-GC0 DECOY ACCEPTED: Decoy.gateLeaf_shipsResI matched the real binder set"
  let accepted ← try
      checkVocab ``Decoy.gateLeaf_shipsResI
        [``Decoy.ChildShipsI, ``Decoy.ShipsResI, ``Decoy.InstClosed, ``GateLeaf.ifaceOf, ``RealChildA]
      pure true
    catch _ => pure false
  unless accepted do throwError "U-GC0 DECOY CONTROL BROKEN: the decoy's own vocabulary was not recognised"
  logInfo "U-GC0 BINDER SET: 6 real statements matched by fully qualified names; decoy rejected against the real set, accepted against its own (control)"

/-! ## 4. Closure -/
structure ReachRes where
  seen : NameSet := {}
  opaques : Array Name := #[]
  axioms : Array Name := #[]

partial def projRefs (env : Environment) (e : Expr) : StateM (Std.HashSet Expr × Array Name) Unit := do
  if (← get).1.contains e then return
  modify fun (v, r) => (v.insert e, r)
  match e with
  | .proj s i b =>
    if isStructure env s then
      if let some f := (getStructureFields env s)[i]? then
        modify fun (v, r) => (v, r.push (s ++ f))
    projRefs env b
  | .app f a => projRefs env f; projRefs env a
  | .lam _ t b _ => projRefs env t; projRefs env b
  | .forallE _ t b _ => projRefs env t; projRefs env b
  | .letE _ t v b _ => projRefs env t; projRefs env v; projRefs env b
  | .mdata _ b => projRefs env b
  | _ => pure ()

def refsOfExpr (env : Environment) (e : Expr) : List Name :=
  e.getUsedConstants.toList ++ ((projRefs env e).run ({}, #[])).2.2.toList

partial def reachGo (todo : List Name) (r : ReachRes) : MetaM ReachRes := do
  match todo with
  | [] => pure r
  | n :: rest =>
    if r.seen.contains n then reachGo rest r else
    let r := { r with seen := r.seen.insert n }
    let env ← getEnv
    let some ci := env.find? n | reachGo rest r
    let (bodies, r) := match ci with
      | .thmInfo t => ([t.value], r)
      | .defnInfo d => ([d.value], r)
      | .opaqueInfo _ => ([], { r with opaques := r.opaques.push n })
      | .axiomInfo _ => ([], { r with axioms := r.axioms.push n })
      | _ => ([], r)
    reachGo ((ci.type :: bodies).foldl (fun acc e => refsOfExpr env e ++ acc) [] ++ rest) r

def forbiddenLaw : List Name := [``Laws.T, ``T1Hyp, `Tools.ShippingGen2.T1HypND, ``Tools.ShippingChildInvA.RefLawsATele]

def reachesForbidden (n : Name) : MetaM (Option Name × ReachRes) := do
  let r ← reachGo [n] {}
  return (forbiddenLaw.find? r.seen.contains, r)

namespace Ctl
def helperT {mref cref} (L : Laws mref cref) := L.T
def viaHelper {mref cref} (L : Laws mref cref) := helperT L
def okHelper {mref cref} (L : Laws mref cref) := L.O
end Ctl

run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [`Tests.Gen4.GateGC0Check.Ctl.helperT, `Tests.Gen4.GateGC0Check.Ctl.viaHelper] do
    unless (← reachesForbidden n).1 == some ``Laws.T do throwError "U-GC0 CLOSURE CONTROL: negative {n} NOT detected"
  if let some f := (← reachesForbidden `Tests.Gen4.GateGC0Check.Ctl.okHelper).1 then
    throwError "U-GC0 CLOSURE CONTROL: positive flagged ({f})"
  let roots := [``ChildShipsI, ``ShipsResI, ``shipsResI_iface, ``gateLeaf_childShips, ``gateLeaf_shipsResI,
    ``gateLeaf_shipsResI_of_real, ``gateLeaf_outTy, ``firstLeaf_childShips, ``firstLeaf_shipsResI,
    ``firstLeaf_shipsResI_of_real]
  for n in roots do
    let (hit, r) ← reachesForbidden n
    if let some f := hit then throwError "U-GC0 CLOSURE FAILED {n}: reaches {f}"
    logInfo m!"U-GC0 CLOSURE {n}: {r.seen.size} constants, none of Laws.T/T1Hyp/T1HypND/RefLawsATele; opaque boundaries NOT traversed: {r.opaques}; axioms reached: {r.axioms}"
  logInfo s!"U-GC0 CLOSURE COUNTS: roots {roots.length}, controls 2 negatives + 1 positive"

/-! ## 5. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := [``ChildPortWidthsI, ``ChildShipsI, ``ShipsResI, ``childPortWidthsI_ofPkg, ``childShipsI_ofPkg,
    ``shipsResI_iface, ``instClosed_of_nil, ``gateLeaf_childPortWidthsI, ``gateLeaf_childShips, ``gateLeaf_shipsResI,
    ``gateLeaf_shipsResI_of_real, ``gateLeaf_outTy, ``firstLeaf_childPortWidthsI, ``firstLeaf_childShips,
    ``firstLeaf_shipsResI, ``firstLeaf_shipsResI_of_real]
  for n in ns do checkAxioms n
  logInfo s!"U-GC0 AXIOMS COUNTS: {ns.length} constants, standard axioms only"

end Tests.Gen4.GateGC0Check
