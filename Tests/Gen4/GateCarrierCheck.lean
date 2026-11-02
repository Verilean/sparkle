import Tools.ShippingGen4GateCarrier
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT. U-GC1 (scripts/gen2/GATE_CARRIER_FREEZE.md §3.1, §4, §6): checks of the gate carrier.

/-! # U-GC1 checks
1. DEF: each carrier definition's value (and each constructor type) against an independent definition written here.
2. TYPE: the theorems against independent statements written here that use the carrier entities compared in step 1.
3. MUTANT: signature/defeq rejections of well-typed propositions by the same comparer, NOT semantic counterexamples.
4. BINDER SET: the fully qualified constants of each statement, restricted to the carrier vocabulary, equal an expected
   set; decoys with the same short names in `Tests.Gen4.GateCarrierCheck.Decoy` must be rejected by that check.
5. CLOSURE: from the main theorem, `gateLeaf_outTy` and the carrier definitions, over all namespaces and explicit bodies,
   no `Laws.T` / `T1Hyp` / `T1HypND` / `RefLawsATele` is reached. An unknown name in the closure is an ERROR, never skipped
   (opaque bodies are not traversed and are listed).
6. AXIOMS: propext / Classical.choice / Quot.sound only. -/

namespace Tests.Gen4.GateCarrierCheck
open Lean Meta Sparkle.Compiler.Elab
open Sparkle.IR.Type (HWType)
open Tools.ShippingGen2
open Tools.ShippingChildCacheA (RealChildA)
open Tools.ShippingChildInv (Res)
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingUnifiedSource (SType Term quote)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Tools.ShippingEntrySoundness (FExpr quoteDecl)
open Tools.ShippingGen4GateCarrier
open Tests.Gen3.ExpectedType

/-! ## 1. Expected definitions (written from the freeze's statements, not copied from the carrier file) -/
def ExpOld : GateData → Prop := fun g =>
  ∀ d : Lean.DefinitionVal, d.value = g.value → certifiedShape? false [] (.defnInfo d) = none
def ExpPeel : GateData → Prop := fun g =>
  mixedGatePeel g.value = some (g.bs, quote g.domE (fun j => inputExpr g.bs.length (g.bpos j)) (fun j => inputExpr g.bs.length (g.vpos j)) g.e)
def ExpHe : GateData → Prop := fun g => g.e.WF g.kb g.kv g.vw
def ExpHb : GateData → Prop := fun g => ∀ j, j < g.kb → ∃ name, g.bs[g.bpos j]? = some (name, .bool)
def ExpHv : GateData → Prop := fun g => ∀ j, j < g.kv → ∃ name, g.bs[g.vpos j]? = some (name, .bits (g.vw j))
def ExpFirstValue : FirstData → Lean.Expr := fun f => quoteDecl f.dn f.names f.n f.fe
def ExpGateRecDecl : GateRec → Name
  | .mixed g => g.decl
  | .first f => f.decl
def ExpGateRecValue : GateRec → Lean.Expr
  | .mixed g => g.value
  | .first f => f.value
noncomputable def ExpGateRecIface (ι : Type) : GateRec → ChildIface ι
  | .mixed g => ⟨g.decl, g.bs, [GateLeaf.outField (.bitVector g.srt.width)], fun _ => gateS g.bs g.e g.bpos g.vpos⟩
  | .first f => ⟨f.decl, Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n, [GateLeaf.outField (.bitVector f.n)],
      fun _ => gateS (Tools.ShippingFirstGateChild.firstBs f.dn f.names f.n) (Tools.ShippingUnifiedSource.ofF f.n f.fe) (fun _ => 0) (fun j => j + 1)⟩
noncomputable def ExpGateQ : (ι : Type) → GateTable → IfaceMap ι := fun ι GT => fun c => (GT c).map (GateRec.iface ι)
def ExpEntryRow : ST.Ref IO.RealWorld Lean.Meta.State → ST.Ref IO.RealWorld Lean.Core.State → GateTable → Prop :=
  fun mref cref GT => ∀ c r, GT c = some r → r.decl = c ∧
    ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context), EntryDefines mctx mref cctx cref c r.value
def ExpFirstDataRow : GateTable → Prop := fun GT => ∀ c f, GT c = some (.first f) → f.fe.WF f.names.length f.n ∧ 0 < f.n
def ExpOldRow : GateTable → Prop := fun GT => ∀ c g, GT c = some (.mixed g) → g.Old
def ExpPeelRow : GateTable → Prop := fun GT => ∀ c g, GT c = some (.mixed g) → g.Peel
def ExpHeRow : GateTable → Prop := fun GT => ∀ c g, GT c = some (.mixed g) → g.He
def ExpHbvRow : GateTable → Prop := fun GT => ∀ c g, GT c = some (.mixed g) → g.Hb ∧ g.Hv
def ExpWidthRow : GateTable → Prop := fun GT => ∀ c g, GT c = some (.mixed g) → g.srt.width ≠ 1
def ExpReflects : ST.Ref IO.RealWorld Lean.Meta.State → ST.Ref IO.RealWorld Lean.Core.State → GateTable → Prop :=
  fun mref cref GT => GateEntryRow mref cref GT ∧ GateFirstDataRow GT ∧ GateOldRow GT ∧ GatePeelRow GT ∧
    GateHeRow GT ∧ GateHbvRow GT ∧ GateWidthRow GT

/-- constructor types (the field lists of the three data types). -/
def ExpGateDataMk : Type := ∀ (decl : Name) (value domE : Lean.Expr) (bs : List (Name × MixedGateBinder)) (kb kv : Nat)
  (vw bpos vpos : Nat → Nat) (srt : SType) (e : Term srt), GateData
def ExpFirstDataMk : Type := ∀ (decl dn : Name) (names : List Name) (n : Nat) (fe : FExpr), FirstData
def ExpMixedMk : Type := ∀ (g : GateData), GateRec
def ExpFirstMk : Type := ∀ (f : FirstData), GateRec

/-! ## 2. Expected theorem statements (over the carrier entities compared above) -/
def ExpMain : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (GT : GateTable) (hG : GateReflects mref cref GT) (c : Name) (r : GateRec)
    (hr : GT c = some r) {y : Res} (h : RealChildA L.O c y), ShipsResI L (gateQ ι GT) c y

def ExpEmpty : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State},
    GateReflects mref cref (fun _ => none)

def ExpToLeafData : Prop :=
  ∀ {ι : Type} (g : GateLeaf ι), (GateLeaf.data g).toLeaf g.old g.peel g.he g.hb g.hv = g

def ExpQNone : Prop := ∀ {ι : Type} (GT : GateTable) (c : Name) (h : GT c = none), gateQ ι GT c = none

def ExpRealChildACtx : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref} {c : Name} {y : Res}
    (h : RealChildA O c y), ∃ (_ : Lean.Meta.Context) (_ : Lean.Core.Context), True

/-- the gate-leaf output type lemma that the main theorem consumes (re-stated, as in U-GC0). -/
def ExpOutTy : Prop :=
  ∀ {ι : Type} {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : Tools.ShippingChildInvA.RefLawsAOps Tools.ShippingChildFresh.MkRefd mref cref) (g : GateLeaf ι)
    (entry : EntryDefines mctx mref cctx cref g.decl g.value) {y : Res} (h : RealChildA O g.decl y)
    (hw1 : g.srt.width ≠ 1),
    ∃ w : Nat, w = g.srt.width ∧ y.1.outputs = [{ name := "out", ty := .bitVector w }]

/-! ## 3. Mutants (well-typed, one clause changed) -/
def MutReflectsNoWidth : ST.Ref IO.RealWorld Lean.Meta.State → ST.Ref IO.RealWorld Lean.Core.State → GateTable → Prop :=
  fun mref cref GT => GateEntryRow mref cref GT ∧ GateFirstDataRow GT ∧ GateOldRow GT ∧ GatePeelRow GT ∧
    GateHeRow GT ∧ GateHbvRow GT
def MutReflectsRowsSwapped : ST.Ref IO.RealWorld Lean.Meta.State → ST.Ref IO.RealWorld Lean.Core.State → GateTable → Prop :=
  fun mref cref GT => GateEntryRow mref cref GT ∧ GateFirstDataRow GT ∧ GatePeelRow GT ∧ GateOldRow GT ∧
    GateHeRow GT ∧ GateHbvRow GT ∧ GateWidthRow GT
def MutWidthRowZero : GateTable → Prop := fun GT => ∀ c g, GT c = some (.mixed g) → g.srt.width ≠ 0
def MutHbvOnlyHb : GateTable → Prop := fun GT => ∀ c g, GT c = some (.mixed g) → g.Hb
def MutQEmpty : IfaceMap Unit := fun _ => none
def MutMainQEmpty : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (GT : GateTable) (hG : GateReflects mref cref GT) (c : Name) (r : GateRec)
    (hr : GT c = some r) {y : Res} (h : RealChildA L.O c y), ShipsResI L (fun _ => (none : Option (ChildIface ι))) c y
def MutMainNoReflect : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (GT : GateTable) (c : Name) (r : GateRec)
    (hr : GT c = some r) {y : Res} (h : RealChildA L.O c y), ShipsResI L (gateQ ι GT) c y

run_cmd Lean.Elab.Command.liftTermElabM do
  -- DEF OK: value of each carrier definition against the independent one
  checkExpected ``GateData.Old ``ExpOld
  checkExpected ``GateData.Peel ``ExpPeel
  checkExpected ``GateData.He ``ExpHe
  checkExpected ``GateData.Hb ``ExpHb
  checkExpected ``GateData.Hv ``ExpHv
  checkExpected ``FirstData.value ``ExpFirstValue
  checkExpected ``GateRec.decl ``ExpGateRecDecl
  checkExpected ``GateRec.value ``ExpGateRecValue
  checkExpected ``GateRec.iface ``ExpGateRecIface
  checkExpected ``gateQ ``ExpGateQ
  checkExpected ``GateEntryRow ``ExpEntryRow
  checkExpected ``GateFirstDataRow ``ExpFirstDataRow
  checkExpected ``GateOldRow ``ExpOldRow
  checkExpected ``GatePeelRow ``ExpPeelRow
  checkExpected ``GateHeRow ``ExpHeRow
  checkExpected ``GateHbvRow ``ExpHbvRow
  checkExpected ``GateWidthRow ``ExpWidthRow
  checkExpected ``GateReflects ``ExpReflects
  logInfo "U-GC1 DEF OK: 18 carrier definitions compared (value, binder names and infos)"
  -- constructor types
  let ctor (c : Name) : MetaM Expr := return (← getConstInfo c).type
  cmpTele "GateData.mk" (← ctor ``GateData.mk) (← stmtOf ``ExpGateDataMk)
  cmpTele "FirstData.mk" (← ctor ``FirstData.mk) (← stmtOf ``ExpFirstDataMk)
  cmpTele "GateRec.mixed" (← ctor ``GateRec.mixed) (← stmtOf ``ExpMixedMk)
  cmpTele "GateRec.first" (← ctor ``GateRec.first) (← stmtOf ``ExpFirstMk)
  logInfo "U-GC1 CTOR OK: GateData.mk, FirstData.mk, GateRec.mixed, GateRec.first"
  -- TYPE OK
  checkExpected ``gateReflects_shipsResI ``ExpMain
  checkExpected ``gateReflects_empty ``ExpEmpty
  checkExpected ``toLeaf_data ``ExpToLeafData
  checkExpected ``gateQ_none ``ExpQNone
  checkExpected ``realChildA_ctx ``ExpRealChildACtx
  checkExpected ``gateLeaf_outTy ``ExpOutTy
  -- MUTANT (signature/defeq rejection only)
  checkMutant ``GateReflects ``MutReflectsNoWidth
  checkMutant ``GateReflects ``MutReflectsRowsSwapped
  checkMutant ``GateWidthRow ``MutWidthRowZero
  checkMutant ``GateHbvRow ``MutHbvOnlyHb
  checkMutant ``gateReflects_shipsResI ``MutMainQEmpty
  checkMutant ``gateReflects_shipsResI ``MutMainNoReflect
  logInfo "U-GC1 COUNTS: DEF 18, CTOR 4, TYPE 6, MUTANT 6 (signature/defeq rejections of well-typed propositions by the same comparer; not semantic counterexamples)"

/-! ## 4. Binder set by fully qualified names, with decoys -/
namespace Decoy
def GateTable : Type := Name → Option Nat
def GateRec : Type := Nat
def GateReflects (_mref : ST.Ref IO.RealWorld Lean.Meta.State) (_cref : ST.Ref IO.RealWorld Lean.Core.State) (_GT : GateTable) : Prop := True
def ShipsResI {ι : Type} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (_L : Laws mref cref) (_Q : IfaceMap ι) (_c : Name) (_r : Res) : Prop := True
def gateQ (ι : Type) (_GT : GateTable) : IfaceMap ι := fun _ => none
theorem gateReflects_shipsResI {ι : Type} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (L : Laws mref cref) (GT : GateTable) (_hG : GateReflects mref cref GT)
    (c : Name) (r : GateRec) (_hr : GT c = some r) {y : Res} (_h : RealChildA L.O c y) :
    ShipsResI L (gateQ ι GT) c y := trivial
end Decoy

def vocab : List Name :=
  [``GateTable, ``GateRec, ``GateData, ``FirstData, ``GateReflects, ``GateEntryRow, ``GateFirstDataRow, ``GateOldRow,
   ``GatePeelRow, ``GateHeRow, ``GateHbvRow, ``GateWidthRow, ``gateQ, ``ShipsResI, ``RealChildA, ``Laws,
   ``GateRec.mixed, ``GateRec.first, ``GateRec.decl, ``GateRec.value, ``GateData.Old, ``GateData.Peel, ``GateData.He,
   ``GateData.Hb, ``GateData.Hv, ``EntryDefines,
   ``Decoy.GateTable, ``Decoy.GateRec, ``Decoy.GateReflects, ``Decoy.ShipsResI, ``Decoy.gateQ]

/-- The vocabulary constants (fully qualified) in the statement of `thm` must be exactly `expected`. -/
def checkVocab (thm : Name) (expected : List Name) : MetaM Unit := do
  let used := (← stmtOf thm).getUsedConstants.toList.filter vocab.contains
  let ok := used.all expected.contains && expected.all used.contains
  unless ok do throwError "U-GC1 BINDER SET FAILED {thm}: vocabulary {used}, expected {expected}"
  logInfo m!"U-GC1 BINDER SET OK {thm}: {used}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let mainSet := [``GateTable, ``GateRec, ``GateReflects, ``ShipsResI, ``RealChildA, ``Laws, ``gateQ]
  checkVocab ``gateReflects_shipsResI mainSet
  checkVocab ``gateReflects_empty [``GateReflects, ``GateRec]
  checkVocab ``gateQ_none [``GateTable, ``GateRec, ``gateQ]
  checkVocab ``GateReflects [``GateTable, ``GateEntryRow, ``GateFirstDataRow, ``GateOldRow, ``GatePeelRow, ``GateHeRow, ``GateHbvRow, ``GateWidthRow]
  checkVocab ``GateEntryRow [``GateTable, ``GateRec, ``GateRec.decl, ``GateRec.value, ``EntryDefines]
  checkVocab ``GateOldRow [``GateTable, ``GateRec, ``GateData, ``GateRec.mixed, ``GateData.Old]
  checkVocab ``GatePeelRow [``GateTable, ``GateRec, ``GateData, ``GateRec.mixed, ``GateData.Peel]
  checkVocab ``GateHeRow [``GateTable, ``GateRec, ``GateData, ``GateRec.mixed, ``GateData.He]
  checkVocab ``GateHbvRow [``GateTable, ``GateRec, ``GateData, ``GateRec.mixed, ``GateData.Hb, ``GateData.Hv]
  checkVocab ``GateFirstDataRow [``GateTable, ``GateRec, ``FirstData, ``GateRec.first]
  checkVocab ``GateWidthRow [``GateTable, ``GateRec, ``GateData, ``GateRec.mixed]
  -- decoy: the same statement shape over the decoy constants must be rejected against the real set
  let rejected ← try
      checkVocab ``Decoy.gateReflects_shipsResI mainSet
      pure false
    catch _ => pure true
  unless rejected do throwError "U-GC1 DECOY ACCEPTED: Decoy.gateReflects_shipsResI matched the real binder set"
  let accepted ← try
      checkVocab ``Decoy.gateReflects_shipsResI
        [``Decoy.GateTable, ``Decoy.GateRec, ``Decoy.GateReflects, ``Decoy.ShipsResI, ``RealChildA, ``Laws, ``Decoy.gateQ]
      pure true
    catch _ => pure false
  unless accepted do throwError "U-GC1 DECOY CONTROL BROKEN: the decoy's own vocabulary was not recognised"
  logInfo "U-GC1 BINDER SET: 11 real statements matched by fully qualified names; decoy rejected against the real set, accepted against its own (control)"

/-! ## 5. Closure (an unknown name is an error) -/
structure ReachRes where
  seen : NameSet := {}
  opaques : Array Name := #[]
  axioms : Array Name := #[]
  /-- `.proj S i _` whose projection function `S.f` is not a constant (e.g. `Lean.Environment.base`): the structure `S` is
  followed, the missing function is LISTED here and in the log (never silently dropped). -/
  projMissing : Array Name := #[]

partial def projRefs (env : Environment) (e : Expr) : StateM (Std.HashSet Expr × Array Name × Array Name) Unit := do
  if (← get).1.contains e then return
  modify fun (v, r, m) => (v.insert e, r, m)
  match e with
  | .proj s i b =>
    modify fun (v, r, m) => (v, r.push s, m)
    if isStructure env s then
      if let some f := (getStructureFields env s)[i]? then
        if env.contains (s ++ f) then modify fun (v, r, m) => (v, r.push (s ++ f), m)
        else modify fun (v, r, m) => (v, r, m.push (s ++ f))
    projRefs env b
  | .app f a => projRefs env f; projRefs env a
  | .lam _ t b _ => projRefs env t; projRefs env b
  | .forallE _ t b _ => projRefs env t; projRefs env b
  | .letE _ t v b _ => projRefs env t; projRefs env v; projRefs env b
  | .mdata _ b => projRefs env b
  | _ => pure ()

def refsOfExpr (env : Environment) (e : Expr) : List Name × List Name :=
  let st := ((projRefs env e).run ({}, #[], #[])).2
  (e.getUsedConstants.toList ++ st.2.1.toList, st.2.2.toList)

partial def reachGo (todo : List Name) (r : ReachRes) : MetaM ReachRes := do
  match todo with
  | [] => pure r
  | n :: rest =>
    if r.seen.contains n then reachGo rest r else
    let r := { r with seen := r.seen.insert n }
    let env ← getEnv
    let some ci := env.find? n | throwError "U-GC1 CLOSURE ERROR: unknown name {n} reached (not skipped)"
    let (bodies, r) := match ci with
      | .thmInfo t => ([t.value], r)
      | .defnInfo d => ([d.value], r)
      | .opaqueInfo _ => ([], { r with opaques := r.opaques.push n })
      | .axiomInfo _ => ([], { r with axioms := r.axioms.push n })
      | _ => ([], r)
    let (refs, miss) := (ci.type :: bodies).foldl
      (fun (acc : List Name × List Name) e => let (a, m) := refsOfExpr env e; (a ++ acc.1, m ++ acc.2)) ([], [])
    reachGo (refs ++ rest) { r with projMissing := r.projMissing ++ miss.toArray }

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
  for n in [`Tests.Gen4.GateCarrierCheck.Ctl.helperT, `Tests.Gen4.GateCarrierCheck.Ctl.viaHelper] do
    unless (← reachesForbidden n).1 == some ``Laws.T do throwError "U-GC1 CLOSURE CONTROL: negative {n} NOT detected"
  if let some f := (← reachesForbidden `Tests.Gen4.GateCarrierCheck.Ctl.okHelper).1 then
    throwError "U-GC1 CLOSURE CONTROL: positive flagged ({f})"
  -- an unknown name must raise, not be skipped
  let raised ← try
      let _ ← reachGo [`Tests.Gen4.GateCarrierCheck.NoSuchConstant] {}
      pure false
    catch _ => pure true
  unless raised do throwError "U-GC1 CLOSURE CONTROL: an unknown name was silently skipped"
  let roots := [``gateReflects_shipsResI, ``gateLeaf_outTy, ``gateQ, ``GateReflects, ``GateRec.iface, ``GateData.toLeaf,
    ``FirstData.toLeaf, ``gateReflects_empty, ``toLeaf_data, ``gateQ_none, ``realChildA_ctx]
  for n in roots do
    let (hit, r) ← reachesForbidden n
    if let some f := hit then throwError "U-GC1 CLOSURE FAILED {n}: reaches {f}"
    logInfo m!"U-GC1 CLOSURE {n}: {r.seen.size} constants, none of Laws.T/T1Hyp/T1HypND/RefLawsATele; opaque boundaries NOT traversed: {r.opaques}; axioms reached: {r.axioms}; projection functions not constants (structure followed, listed): {r.projMissing.toList.eraseDups}"
  logInfo s!"U-GC1 CLOSURE COUNTS: roots {roots.length}, controls 2 negatives + 1 positive + 1 unknown-name"

/-! ## 6. Axioms -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let ns := [``gateReflects_shipsResI, ``gateReflects_empty, ``toLeaf_data, ``gateQ_none, ``realChildA_ctx,
    ``gateLeaf_outTy, ``gateQ, ``GateReflects, ``GateRec.iface, ``GateData.toLeaf, ``FirstData.toLeaf]
  for n in ns do checkAxioms n
  logInfo s!"U-GC1 AXIOMS COUNTS: {ns.length} constants, standard axioms only"

end Tests.Gen4.GateCarrierCheck
