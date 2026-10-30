import Lean
import Tools.ShippingGen5DeclConnect
import Tests.Gen3.ExpectedType
import Tests.Compiler.ShippingMachineCommandTest
set_option autoImplicit false
-- NOT BUILT (header updated by a comment-only commit after a successful agent build; clean issue-linked build is the coder's).

/-! # DC-CONNECT concrete units: checks (scripts/gen5/DC_CONNECT_FREEZE.md rev5 §C.8)

All comparisons are signature / defeq / run-on-a-finite-battery results. A "mutant" is a well-typed one-change variant rejected by the SAME
comparator; it is NOT a semantic counterexample.

1. TYPE: each theorem's type (and each definition's VALUE, for the non-recursive definitions) is compared with an independently written
   `Exp*` by `Tests.Gen3.ExpectedType.checkExpected` (binder by binder: names, binder infos, types).
2. MUTANT: per target one (or two) well-typed one-change `Mut*`; `checkMutant` must reject it.
3. AXIOMS: `checkAxioms` on every theorem and definition.
4. BEHAVIOUR: `sigShape?`/`shapeOf` on a battery of local declarations with independently written expected `Option SigShape`; one-change copies of the
   recognizer (domain term not checked; zero width allowed) must DISAGREE on the battery (finite battery, not an equivalence proof). Corpus controls
   on real `circuit do` declarations of `Tests.Compiler.ShippingMachineEntryTest` / `ShippingMachineCommandTest`, and `ShapeMatches` against the
   generated `mThree.machineData`.
5. CLOSURE: an explicit transitive walk over `ConstantInfo` bodies and types, following `Expr.proj` structure names too (`getUsedConstants` does not);
   core modules (`Init`/`Std`/`Lean`) are leaves. No reached constant belongs to DG-SEM/DG-DATAOF/DG-ACC/DG-ENV, `ConstValueE`, a prim table or
   a `genP`-like name; the non-core modules reached are a stated list; exact module/constant sets for the small pure targets. Negative controls:
   direct mention, a helper in another namespace, a helper theorem, an `Expr.proj`-only mention (collector unit control); clean controls. -/
open Lean Meta Tools.ShippingGen5DeclConnect Tests.Gen3.ExpectedType Tools.ShippingGen2 Tools.ShippingMachineAuto
open Sparkle.Compiler.Elab Sparkle.Core.Domain Sparkle.Core.Signal

namespace Tests.Gen5.DeclConnectCheck

/-! ## 1. Independent expected statements (TYPE) and one-change mutants (MUTANT) -/

abbrev CVR := Environment → Name → (α : Type) → α → Prop

def ExpDeclConnectEq : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (CV : CVR) (env₀ : Environment) (P : Name → Option (Pkg ι dom))
    (Tgt : Name → Prop), DeclConnect CV env₀ P Tgt = (∀ X, Tgt X → ∀ p, P X = some p →
      ∃ (ci : ConstantInfo) (sh : SigShape) (v : sh.Ty), env₀.find? X = some ci ∧ shapeOf ci = some sh ∧ ShapeMatches sh p.d p.kD ∧
        CV env₀ X sh.Ty v ∧ ∀ i bools bits, sh.obs (dom := dom) v i bools bits = p.src i bools bits)
/-- one change: the `ShapeMatches` conjunct dropped. -/
def MutDeclConnectEq : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (CV : CVR) (env₀ : Environment) (P : Name → Option (Pkg ι dom))
    (Tgt : Name → Prop), DeclConnect CV env₀ P Tgt = (∀ X, Tgt X → ∀ p, P X = some p →
      ∃ (ci : ConstantInfo) (sh : SigShape) (v : sh.Ty), env₀.find? X = some ci ∧ shapeOf ci = some sh ∧
        CV env₀ X sh.Ty v ∧ ∀ i bools bits, sh.obs (dom := dom) v i bools bits = p.src i bools bits)

def ExpMono : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (CV : CVR) (env₀ : Environment) (P : Name → Option (Pkg ι dom))
    {Tgt Tgt' : Name → Prop} (h : ∀ X, Tgt' X → Tgt X), DeclConnect CV env₀ P Tgt → DeclConnect CV env₀ P Tgt'
/-- one change: inclusion reversed. -/
def MutMono : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (CV : CVR) (env₀ : Environment) (P : Name → Option (Pkg ι dom))
    {Tgt Tgt' : Name → Prop} (h : ∀ X, Tgt X → Tgt' X), DeclConnect CV env₀ P Tgt → DeclConnect CV env₀ P Tgt'

def ExpNotEmpty : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (env₀ : Environment) (P : Name → Option (Pkg ι dom))
    (Tgt : Name → Prop) {X : Name} {p : Pkg ι dom} (hT : Tgt X) (hP : P X = some p), ¬ DeclConnect (fun _ _ _ _ => False) env₀ P Tgt
/-- one change: `¬` dropped. -/
def MutNotEmpty : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (env₀ : Environment) (P : Name → Option (Pkg ι dom))
    (Tgt : Name → Prop) {X : Name} {p : Pkg ι dom} (hT : Tgt X) (hP : P X = some p), DeclConnect (fun _ _ _ _ => False) env₀ P Tgt

def ExpRows : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (CV : CVR) (env₀ : Environment) (P : Name → Option (Pkg ι dom))
    (Tgt : Name → Prop) {R : Name → Name → Prop} (hAcc : ∀ X, Tgt X → Acc R X) (hclosed : ∀ X c, Tgt X → R c X → Tgt c)
    (hstep : ∀ X, Tgt X → (∀ c, R c X → Tgt c → DeclConnectAt CV env₀ P c) → DeclConnectAt CV env₀ P X), DeclConnect CV env₀ P Tgt
/-- one change: the accessibility premise dropped. -/
def MutRows : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} (CV : CVR) (env₀ : Environment) (P : Name → Option (Pkg ι dom))
    (Tgt : Name → Prop) {R : Name → Name → Prop} (hclosed : ∀ X c, Tgt X → R c X → Tgt c)
    (hstep : ∀ X, Tgt X → (∀ c, R c X → Tgt c → DeclConnectAt CV env₀ P c) → DeclConnectAt CV env₀ P X), DeclConnect CV env₀ P Tgt

def ExpTelescope : Prop := ∀ {ty : Lean.Expr} {sh : SigShape} (h : sigShape? ty = some sh),
    telescopeKinds ty = some (MixedGateBinder.domain :: sh.args.map Scalar.binder)
/-- one change: the leading domain kind dropped. -/
def MutTelescope : Prop := ∀ {ty : Lean.Expr} {sh : SigShape} (h : sigShape? ty = some sh),
    telescopeKinds ty = some (sh.args.map Scalar.binder)

def ExpMachOuts : Prop := ∀ (senv : StructEnv) {ty : Lean.Expr} {sh : SigShape} (h : sigShape? ty = some sh),
    machOuts? senv ty = some (sh.res.ctor?, sh.res.ports)
/-- one change: the constructor component forced to `none`. -/
def MutMachOuts : Prop := ∀ (senv : StructEnv) {ty : Lean.Expr} {sh : SigShape} (h : sigShape? ty = some sh),
    machOuts? senv ty = some (none, sh.res.ports)

def ExpOutPorts : Prop := ∀ (r : ResShape) (slotsW : Nat),
    r.outPorts = (machOutFields slotsW r.ports).map (fun o => (o.name, o.ty, o.width))
/-- one change: `slotsW` shifted by one. -/
def MutOutPorts : Prop := ∀ (r : ResShape) (slotsW : Nat),
    r.outPorts = (machOutFields (slotsW + 1) r.ports).map (fun o => (o.name, o.ty, o.width))

def ExpApplyCons : Prop := ∀ {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (k : Scalar) (ks : List Scalar) (q : Nat) (R : Type) (f : ArgsTy D (k :: ks) R),
    applyArgs bools bits (k :: ks) q R f = applyArgs bools bits ks (q + 1) R (f (k.arg bools bits q))
/-- one change: the position is not advanced. -/
def MutApplyCons : Prop := ∀ {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (k : Scalar) (ks : List Scalar) (q : Nat) (R : Type) (f : ArgsTy D (k :: ks) R),
    applyArgs bools bits (k :: ks) q R f = applyArgs bools bits ks q R (f (k.arg bools bits q))

def ExpApplyNil : Prop := ∀ {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (q : Nat) (R : Type) (f : ArgsTy D [] R), applyArgs bools bits [] q R f = f
-- no mutant: `applyArgs … [] (q + 1) R f = f` is DEFEQ to the statement (q is unused for `[]`), so a position change is not rejectable by a defeq comparator.

/-! Definitions pinned by VALUE (non-recursive ones). -/

def ExpShapeMatches := fun (sh : SigShape) (d : MachineData) (kD : Nat) =>
  (d.bsIn.take kD).map (·.2) = MixedGateBinder.domain :: sh.args.map Scalar.binder ∧
  d.shape.layout.outs.map (fun o => (o.name, o.ty, o.width)) = sh.res.outPorts
/-- one change: the leading domain kind dropped. -/
def MutShapeMatchesDom := fun (sh : SigShape) (d : MachineData) (kD : Nat) =>
  (d.bsIn.take kD).map (·.2) = sh.args.map Scalar.binder ∧
  d.shape.layout.outs.map (fun o => (o.name, o.ty, o.width)) = sh.res.outPorts
/-- one change: the output conjunct dropped. -/
def MutShapeMatchesOut := fun (sh : SigShape) (d : MachineData) (kD : Nat) =>
  (d.bsIn.take kD).map (·.2) = MixedGateBinder.domain :: sh.args.map Scalar.binder

def ExpObs := fun {ι : Type} {dom : ι → DomainConfig} (sh : SigShape) (v : sh.Ty) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) =>
  sh.res.obs (applyArgs bools bits sh.args 1 (sh.res.Ty (dom i)) (v (dom i)))
/-- one change: the first argument position is 0 (the domain binder's). -/
def MutObs := fun {ι : Type} {dom : ι → DomainConfig} (sh : SigShape) (v : sh.Ty) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) =>
  sh.res.obs (applyArgs bools bits sh.args 0 (sh.res.Ty (dom i)) (v (dom i)))

def ExpShapeOf := fun (ci : ConstantInfo) => if ci.levelParams.isEmpty then sigShape? ci.type else none
/-- one change: `levelParams` ignored. -/
def MutShapeOf := fun (ci : ConstantInfo) => sigShape? ci.type

def ExpDeclConnectVal := fun {ι : Type} {dom : ι → DomainConfig} (CV : CVR) (env₀ : Environment) (P : Name → Option (Pkg ι dom))
    (Tgt : Name → Prop) => Tools.ShippingGen5DeclConnectAbs.DCGen (fun e n => e.find? n) CV shapeOf (fun sh p => MatchC sh p)
      (fun p sh v => ObsC p sh v) P env₀ Tgt
/-- one change: `DCImp` (the implication form, true for the empty relation) instead of `DCGen`. -/
def MutDeclConnectVal := fun {ι : Type} {dom : ι → DomainConfig} (CV : CVR) (env₀ : Environment) (P : Name → Option (Pkg ι dom))
    (Tgt : Name → Prop) => Tools.ShippingGen5DeclConnectAbs.DCImp (fun e n => e.find? n) CV shapeOf (fun sh p => MatchC sh p)
      (fun p sh v => ObsC p sh v) P env₀ Tgt

def ExpObsC := fun {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (sh : SigShape) (v : sh.Ty) =>
  ∀ i bools bits, sh.obs (dom := dom) v i bools bits = p.src i bools bits
/-- one change: the package side observed against itself. -/
def MutObsC := fun {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (sh : SigShape) (v : sh.Ty) =>
  ∀ i bools bits, p.src i bools bits = p.src i bools bits

/-- (target, expected, mutants) -/
def table : List (Name × Name × List Name) :=
  [(``declConnect_eq, ``ExpDeclConnectEq, [``MutDeclConnectEq]), (``declConnect_mono, ``ExpMono, [``MutMono]),
   (``not_declConnect_of_empty, ``ExpNotEmpty, [``MutNotEmpty]), (``declConnect_of_rows, ``ExpRows, [``MutRows]),
   (``sigShape?_telescope, ``ExpTelescope, [``MutTelescope]), (``sigShape?_machOuts, ``ExpMachOuts, [``MutMachOuts]),
   (``outPorts_eq, ``ExpOutPorts, [``MutOutPorts]), (``applyArgs_cons, ``ExpApplyCons, [``MutApplyCons]),
   (``applyArgs_nil, ``ExpApplyNil, []),
   (``ShapeMatches, ``ExpShapeMatches, [``MutShapeMatchesDom, ``MutShapeMatchesOut]), (``SigShape.obs, ``ExpObs, [``MutObs]),
   (``shapeOf, ``ExpShapeOf, [``MutShapeOf]), (``DeclConnect, ``ExpDeclConnectVal, [``MutDeclConnectVal]),
   (``ObsC, ``ExpObsC, [``MutObsC])]

/-! ## 2. Behaviour: recognizer battery, one-change recognizer copies, corpus controls -/

section Battery
open Sparkle.Core.Domain

def tA {dom : DomainConfig} (_a : Signal dom Bool) (_b : Signal dom (BitVec 8)) : Signal dom Bool := Signal.pure false
def tB {dom : DomainConfig} (_a : Signal dom Bool) : Signal dom Bool × Signal dom (BitVec 4) := (Signal.pure false, Signal.pure 0)
def tC {d1 d2 : DomainConfig} (_a : Signal d1 Bool) : Signal d1 Bool := Signal.pure false
def tD (_a : Signal defaultDomain Bool) : Signal defaultDomain Bool := Signal.pure false
def tE {dom : DomainConfig} {α : Type} (_a : Signal dom Bool) : Signal dom Bool := Signal.pure false
def tF {dom : DomainConfig} (_a : Signal dom Bool) : Signal dom Bool × Signal dom Bool × Signal dom Bool :=
  (Signal.pure false, Signal.pure false, Signal.pure false)
def tG {dom : DomainConfig} (_a : Signal dom Bool) : Signal dom (BitVec 0) := Signal.pure 0
def tH {dom : DomainConfig} (_a : Signal dom Bool) : Signal dom (BitVec 4 × BitVec 4) := Signal.pure (0, 0)
/-- the argument's domain is a closed term, not the first binder -/
def tI {dom : DomainConfig} (_a : Signal defaultDomain Bool) : Signal dom Bool := Signal.pure false
def tJ {dom : DomainConfig} {n : Nat} (_a : Signal dom (BitVec n)) : Signal dom Bool := Signal.pure false
/-- an explicit universe parameter that the type does not mention: `levelParams ≠ []`, `sigShape? = some` -/
def tK.{u} {dom : DomainConfig} (_a : Signal dom Bool) : Signal dom Bool :=
  let _x : ULift.{u} Nat := ULift.up 0
  Signal.pure false

def battery : List (Name × Option SigShape × Option SigShape) :=
  [(``tA, some ⟨[.bool, .bits 8], .one .bool⟩, some ⟨[.bool, .bits 8], .one .bool⟩),
   (``tB, some ⟨[.bool], .pair .bool (.bits 4)⟩, some ⟨[.bool], .pair .bool (.bits 4)⟩),
   (``tC, none, none), (``tD, none, none), (``tE, none, none), (``tF, none, none), (``tG, none, none), (``tH, none, none),
   (``tI, none, none), (``tJ, none, none),
   (``tK, some ⟨[.bool], .one .bool⟩, none)]   -- (name, expected sigShape? of the type, expected shapeOf of the constant)

/-- ONE-CHANGE COPIES of the recognizer. `(chkDom := true, allowZero := false)` is the original; each mutant switches one check off. -/
def scalarM (chkDom allowZero : Bool) (depth : Nat) : Lean.Expr → Option Scalar
  | .app (.app (.const ``Sparkle.Core.Signal.Signal _) d) (.const ``Bool _) =>
    if !chkDom || domAt depth d then some .bool else none
  | .app (.app (.const ``Sparkle.Core.Signal.Signal _) d) (.app (.const ``BitVec _) wE) =>
    if !chkDom || domAt depth d then (canonicalNatLitValue? wE).bind fun n => if allowZero || 0 < n then some (.bits n) else none else none
  | _ => none
def resShapeM (chkDom allowZero : Bool) (depth : Nat) : Lean.Expr → Option ResShape
  | .app (.app (.const ``Prod _) a) b => do
    let ka ← scalarM chkDom allowZero depth a
    let kb ← scalarM chkDom allowZero depth b
    pure (.pair ka kb)
  | e => (scalarM chkDom allowZero depth e).map .one
def sigGoM (chkDom allowZero : Bool) : Nat → List Scalar → Lean.Expr → Option SigShape
  | depth, acc, .forallE _ ty b _ => (scalarM chkDom allowZero depth ty).bind fun k => sigGoM chkDom allowZero (depth + 1) (acc ++ [k]) b
  | depth, acc, e => (resShapeM chkDom allowZero depth e).map fun r => { args := acc, res := r }
def sigShapeM (chkDom allowZero : Bool) : Lean.Expr → Option SigShape
  | .forallE _ ty b _ => if ty.isConstOf ``Sparkle.Core.Domain.DomainConfig then sigGoM chkDom allowZero 1 [] b else none
  | _ => none

end Battery

open Sparkle.Tests.Compiler

/-- corpus controls: (declaration, expected `shapeOf`, why it is in the list). Real `circuit do` / combinational declarations that the
machine-route tests compile (`#machine_endpoint` in `ShippingMachineCommandTest`). -/
def corpus : List (Name × Option SigShape × String) :=
  [(``ShippingMachineEntryTest.mThree, some ⟨[.bool, .bits 4], .one (.bits 4)⟩, "machine route, 3 slots of 2 kinds, mixed Bool/BitVec arguments, one BitVec result"),
   (``ShippingMachineEntryTest.twoFlag, some ⟨[.bool], .one .bool⟩, "machine route, one Bool result obtained from a structure-returning callee"),
   (``ShippingMachineEntryTest.twoCnt, some ⟨[.bool], .one (.bits 8)⟩, "same callee, one BitVec result"),
   (``ShippingMachineEntryTest.linChk, some ⟨[.bool, .bits 8, .bool], .one (.bits 8)⟩, "IP-library machine (LIN checksum), 3 arguments, one BitVec result"),
   (``ShippingMachineCommandTest.plain, some ⟨[.bits 8, .bits 8], .one (.bits 8)⟩, "combinational (non-machine) route, two BitVec arguments"),
   (``ShippingMachineEntryTest.twoHW, none, "user-structure result (TwoOut): outside the fragment, extension of ResShape needed (DC-COVER)"),
   (``ShippingMachineCommandTest.toggle, none, "closed `defaultDomain` declaration: no leading DomainConfig binder"),
   (``ShippingMachineEntryTest.linChkDefault, none, "same body as linChk at `defaultDomain`: closed domain")]

/-! ## 3. CLOSURE machinery -/

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
def isCoreMod (m : Name) : Bool := [`Init, `Std, `Lean].any (·.isPrefixOf m)

/-- all constants an Expr mentions, INCLUDING the structure name of an `Expr.proj` (`Expr.getUsedConstants` does not return it) -/
def usedConsts (e : Lean.Expr) : MetaM NameSet := do
  let r ← IO.mkRef ({} : NameSet)
  let _ ← Core.transform e (pre := fun x => do
    match x with
    | .const n _ => r.modify (·.insert n)
    | .proj s _ _ => r.modify (·.insert s)
    | _ => pure ()
    return .continue)
  r.get

structure Reach where
  seen : NameSet := {}
  opaques : Array Name := #[]
  axioms : Array Name := #[]

/-- transitive walk; core modules are leaves; thm/defn values and types, inductive constructors; opaque/axiom bodies are not followed (reported). -/
partial def walk (env : Environment) (st : IO.Ref Reach) (n : Name) : MetaM Unit := do
  if (← st.get).seen.contains n then return
  st.modify fun s => { s with seen := s.seen.insert n }
  match moduleOf env n with
  | some m => if isCoreMod m then return
  | none => pure ()
  let some ci := env.find? n | return
  let mut refs : NameSet ← usedConsts ci.type
  match ci with
  | .thmInfo v => refs := (← usedConsts v.value).toList.foldl (fun a c => a.insert c) refs
  | .defnInfo v => refs := (← usedConsts v.value).toList.foldl (fun a c => a.insert c) refs
  | .inductInfo v => for c in v.ctors do refs := refs.insert c
  | .opaqueInfo _ => st.modify fun s => { s with opaques := s.opaques.push n }
  | .axiomInfo _ => st.modify fun s => { s with axioms := s.axioms.push n }
  | _ => pure ()
  for r in refs do walk env st r

def reach (env : Environment) (n : Name) : MetaM Reach := do
  let st ← IO.mkRef ({} : Reach)
  walk env st n
  st.get

/-- the owners whose results this issue must not use, by name prefix or fragment -/
def forbiddenPrefixes : List Name :=
  [`Tools.ShippingGen5Sem, `Tools.ShippingGen5Acc, `Tools.ShippingGen5DataOf, `Tools.ShippingGen5Env, `Tools.ShippingGen5T2]
def forbiddenFragments : List String := ["ConstValueE", "primTable", "genP", "genSem", "dataOf", "FG_COMPLETE"]

def violations (env : Environment) (r : Reach) : Array Name :=
  r.seen.toList.foldl (init := #[]) fun acc n =>
    let s := n.toString
    let bad := forbiddenPrefixes.any (·.isPrefixOf n) || forbiddenFragments.any (fun f => (s.splitOn f).length > 1) ||
      (match moduleOf env n with | some m => forbiddenPrefixes.any (·.isPrefixOf m) | none => false)
    if bad then acc.push n else acc

def foreignModules (env : Environment) (r : Reach) : List Name :=
  (r.seen.toList.filterMap (moduleOf env)).eraseDups.filter fun m =>
    !isCoreMod m && m != `Tools.ShippingGen5DeclConnect && m != `Tools.ShippingGen5DeclConnectAbs

/-- non-core modules the large targets (`DeclConnect`, `declConnect_of_rows`) may reach: the Pkg / MachineData / Signal vocabulary of `Tools.ShippingGen2Defs`. -/
def allowedModules : List Name :=
  [`Sparkle.Compiler.Elab, `Tools.ShippingUnifiedSource, `Tools.ShippingMachineDenote, `Sparkle.Core.Signal, `Tools.ShippingEntrySoundness,
   `Sparkle.IR.Machine, `Sparkle.IR.Type, `Tools.ShippingMuxTypeSoundness, `Tools.ShippingMachineAuto, `Tools.ShippingBoolSourceSoundness,
   `Tools.ShippingGen2Loop, `Tools.ShippingGen2SrcPkg, `Sparkle.Compiler.MachInstOrigin, `Sparkle.Core.CircuitMonad, `Tools.ShippingMachineRef,
   `Tools.ShippingScalarSoundness, `Sparkle.Core.Domain, `Tools.ShippingBoolLiteralSoundness, `Tools.ShippingGen2Defs, `Tools.ShippingMachineEntry,
   `Tools.ShippingMachineSource, `Tools.ShippingGen2Pkg, `Sparkle.Core.Wireable, `Tools.ShippingGen2CombPkg, `Tools.ShippingQuadComposed,
   `Tools.ShippingMuxLoweringSoundness, `Tools.ShippingSeqParentLemmas, `Tools.ShippingMixedSourceBridge, `Tools.ShippingReaderOutsInv]

-- Negative controls (live in this file; their names are forbidden-prefixed on purpose, in other namespaces than the target).
end Tests.Gen5.DeclConnectCheck
namespace Tools.ShippingGen5Acc
def fakeGenP : Nat := 0
structure FakeKit where
  x : Nat
end Tools.ShippingGen5Acc
namespace Tests.Gen5.DeclConnectCheck
namespace Elsewhere
def helper : Nat := Tools.ShippingGen5Acc.fakeGenP
theorem helperThm : Tools.ShippingGen5Acc.fakeGenP = 0 := rfl
abbrev KAlias := Tools.ShippingGen5Acc.FakeKit
end Elsewhere
def negDirect : Nat := Tools.ShippingGen5Acc.fakeGenP
def negOtherNs : Nat := Elsewhere.helper
theorem negThm : True := by
  have _h := Elsewhere.helperThm
  trivial
def negAlias (k : Elsewhere.KAlias) : Nat := k.x
def cleanDef (n : Nat) : Nat := n + 1
theorem cleanThm : cleanDef 1 = 2 := rfl

/-! ## Run -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  -- TYPE and MUTANT
  for (thm, e, ms) in table do
    checkExpected thm e
    for m in ms do checkMutant thm m
  -- AXIOMS: theorems and definitions
  for n in [``declConnect_eq, ``declConnect_mono, ``not_declConnect_of_empty, ``declConnect_of_rows, ``sigShape?_telescope,
            ``sigShape?_machOuts, ``outPorts_eq, ``applyArgs_cons, ``applyArgs_nil, ``scalar?_kind, ``sigGo_tele, ``sigGo_outs,
            ``scalar?_outs, ``resShape?_outs, ``sigShape?, ``shapeOf, ``ShapeMatches, ``SigShape.obs, ``DeclConnect, ``DeclConnectAt,
            ``MatchC, ``ObsC, ``Scalar.obs, ``ResShape.obs, ``ResShape.outPorts, ``applyArgs] do
    checkAxioms n
  -- BEHAVIOUR: battery
  for (n, expSig, expShape) in battery do
    let ci ← getConstInfo n
    let got := sigShape? ci.type
    unless got == expSig do throwError "BATTERY FAILED sigShape? {n}: {repr got} expected {repr expSig}"
    unless shapeOf ci == expShape do throwError "BATTERY FAILED shapeOf {n}"
    unless sigShapeM true false ci.type == got do throwError "BATTERY: recognizer copy (true,true) differs from sigShape? on {n}"
    -- agreement with the compiler's readers on every accepted type
    if let some sh := got then
      unless telescopeKinds ci.type == some (MixedGateBinder.domain :: sh.args.map Scalar.binder) do throwError "telescopeKinds disagrees on {n}"
      unless (machOuts? { proj := fun _ => none, fields := fun _ => none } ci.type).isSome do throwError "machOuts? none on {n}"
    logInfo m!"BATTERY OK {n}: sigShape? {repr got}, shapeOf {repr (shapeOf ci)}"
  for (label, cd, az) in [("domain term not checked", false, false), ("zero width allowed", true, true)] do
    let mut differs : List Name := []
    for (n, _, _) in battery do
      let ci ← getConstInfo n
      if sigShapeM cd az ci.type != sigShape? ci.type then differs := n :: differs
    if differs.isEmpty then throwError "RECOGNIZER MUTANT NOT REJECTED ({label})"
    logInfo m!"RECOGNIZER MUTANT REJECTED ({label}) on {differs} (finite battery, not a semantic counterexample)"
  -- CORPUS controls
  for (n, exp, why) in corpus do
    let ci ← getConstInfo n
    unless shapeOf ci == exp do throwError "CORPUS FAILED {n}: {repr (shapeOf ci)} expected {repr exp}"
    logInfo m!"CORPUS OK {n}: {repr (shapeOf ci)} ({why})"
  -- CLOSURE
  let targets := [``declConnect_eq, ``declConnect_mono, ``not_declConnect_of_empty, ``declConnect_of_rows, ``sigShape?_telescope,
                  ``sigShape?_machOuts, ``outPorts_eq, ``applyArgs_cons, ``applyArgs_nil, ``sigShape?, ``shapeOf, ``ShapeMatches, ``SigShape.obs, ``DeclConnect]
  for n in targets do
    let r ← reach env n
    let v := violations env r
    unless v.isEmpty do throwError "CLOSURE FAILED {n}: forbidden {v}"
    unless r.axioms.isEmpty do throwError "CLOSURE FAILED {n}: axiom constants {r.axioms}"
    let fm := foreignModules env r
    let bad := fm.filter (!allowedModules.contains ·)
    unless bad.isEmpty do throwError "CLOSURE FAILED {n}: modules outside the stated list {bad}"
    logInfo m!"CLOSURE OK {n}: reached {r.seen.size}, foreign modules {fm}, opaque {r.opaques}"
  -- exact module sets for the pure targets
  for (n, mods) in [(``sigShape?, [`Sparkle.Compiler.Elab]), (``shapeOf, [`Sparkle.Compiler.Elab]), (``sigShape?_telescope, [`Sparkle.Compiler.Elab]),
                    (``sigShape?_machOuts, [`Sparkle.Compiler.Elab])] do
    let fm := foreignModules env (← reach env n)
    unless fm.length == mods.length && mods.all fm.contains do throwError "CLOSURE EXACT FAILED {n}: {fm}"
    logInfo m!"CLOSURE EXACT OK {n}: foreign modules exactly {fm}"
  let rs ← reach env ``sigShape?
  unless rs.seen.contains ``Sparkle.Compiler.Elab.canonicalNatLitValue? do throwError "WALK: sigShape? does not reach canonicalNatLitValue?"
  logInfo m!"CLOSURE sigShape? reaches canonicalNatLitValue?"
  -- walk depth: DeclConnect reaches Pkg / MachineData vocabulary and the Abs core
  let rd ← reach env ``DeclConnect
  for c in [``Tools.ShippingGen2.Pkg.src, ``Tools.ShippingGen2.Pkg.kD, ``Tools.ShippingMachineAuto.MachineData.bsIn,
            ``Tools.ShippingGen5DeclConnectAbs.DCGen] do
    unless rd.seen.contains c do throwError "WALK-DEPTH: DeclConnect does not reach {c}"
  logInfo m!"CLOSURE WALK-DEPTH OK (DeclConnect reaches Pkg.src, Pkg.kD, MachineData.bsIn, DCGen)"
  -- negative controls
  for (c, why) in [(``negDirect, "direct mention"), (``negOtherNs, "helper definition in another namespace"),
                   (``negThm, "helper theorem body"), (``negAlias, "structure projection through an alias")] do
    let v := violations env (← reach env c)
    if v.isEmpty then throwError "CLOSURE CONTROL NOT DETECTED {c} ({why})"
    logInfo m!"CLOSURE CONTROL DETECTED {c} ({why}): {v}"
  -- the `Expr.proj`-only collector control: `getUsedConstants` misses the structure name, `usedConsts` finds it
  let pe := Lean.Expr.proj ``Tools.ShippingGen5Acc.FakeKit 0 (.bvar 0)
  unless !(pe.getUsedConstants.contains ``Tools.ShippingGen5Acc.FakeKit) do throwError "control premise: getUsedConstants unexpectedly sees the proj structure"
  unless (← usedConsts pe).contains ``Tools.ShippingGen5Acc.FakeKit do throwError "CLOSURE CONTROL NOT DETECTED (raw Expr.proj)"
  logInfo m!"CLOSURE CONTROL DETECTED raw Expr.proj structure name (getUsedConstants alone does not return it)"
  -- clean controls
  for c in [``cleanDef, ``cleanThm] do
    let v := violations env (← reach env c)
    unless v.isEmpty do throwError "CLOSURE CLEAN CONTROL FAILED {c}: {v}"
    logInfo m!"CLOSURE CLEAN CONTROL OK {c}"

/-! ## ShapeMatches against a generated `MachineData` (the machine route's own data for `mThree`) -/

open Sparkle.Tests.Compiler.ShippingMachineEntryTest in
example : ShapeMatches ⟨[.bool, .bits 4], .one (.bits 4)⟩ mThree.machineData mThree.machineData.nIn := by decide
open Sparkle.Tests.Compiler.ShippingMachineEntryTest in
/-- the swapped argument order is rejected by the same predicate -/
example : ¬ ShapeMatches ⟨[.bits 4, .bool], .one (.bits 4)⟩ mThree.machineData mThree.machineData.nIn := by decide
open Sparkle.Tests.Compiler.ShippingMachineEntryTest in
/-- the wrong result shape is rejected -/
example : ¬ ShapeMatches ⟨[.bool, .bits 4], .one .bool⟩ mThree.machineData mThree.machineData.nIn := by decide

end Tests.Gen5.DeclConnectCheck
