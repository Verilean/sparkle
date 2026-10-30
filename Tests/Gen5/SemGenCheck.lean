import Tools.ShippingGen5SemGen
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- Built in g5sm-u3 at 4ebc4067 (Pod `kjob lake build`, exit 0; SemGenCheck: TYPE 5, MUTANT 3, AXIOMS standard, CLOSURE OK). Clean build is the coder's. No sorry / axiom / native_decide.

/-! # DG-SEM unit U3 (P3) checks (Tools/ShippingGen5SemGen.lean; scripts/gen5/DG_SEM_FREEZE_REV3.md §1, §1.4)

TYPE: the three theorems and the two definitions' types are compared (`checkExpected`) with independently written `Expected…`
statements (the theorems through the accessors of the `SrcSem` value rather than `refBodyE`; `refBodyE`/`genSemGenE` against the
fully unfolded `Circuit` type). MUTANT: one-place changes, well-typed, rejected by `checkMutant` — a signature / defeq rejection,
NOT a semantic counterexample. AXIOMS: standard axioms only (`Lean.collectAxioms`). CLOSURE: a separate walk over the constants the
unit's declarations mention, rejecting the named forbidden constants (`sorryAx`, the native-reduction axioms). The axiom audit and
the closure audit are different checks and are reported under different markers. -/

namespace Tests.Gen5.SemGenCheck
open Lean Meta Elab
open Tools.ShippingGen5Sem Tests.Gen3.ExpectedType
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineSource (valsAt stateLoop)
open Tools.ShippingMachineDenote (typedVal evalTerms enc tys)
open Tools.ShippingUnifiedSource (eval)

section Expected
variable {ι : Type} {dom : ι → DomainConfig}

def ExpectedWrites : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (X : Lean.Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat),
    valsAt (tys g.d.ss) ((genSemGenE X g eb ev).body i bools bits
        (mkRegList S (tys g.d.ss) (fun s => s) (fun f => f)) (mkHolds (tys g.d.ss) S)).snd t =
      evalTerms
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).v (g.d.vpos j) w)
        g.d.nexts

def ExpectedResult : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (X : Lean.Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat),
    ((genSemGenE X g eb ev).obsR i ((genSemGenE X g eb ev).body i bools bits
        (mkRegList S (tys g.d.ss) (fun s => s) (fun f => f)) (mkHolds (tys g.d.ss) S)).fst).map (fun f => f t) =
      g.d.outs.map fun o => enc o.1 (eval
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).v (g.d.vpos j) w) o.2)

def ExpectedSource : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (X : Lean.Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    (genSemGenE X g eb ev).src i bools bits =
      (genSemGenE X g eb ev).obsR i
        (let _ : Inhabited (HList (tys g.d.ss)) := ⟨g.inits⟩
         let b := (genSemGenE X g eb ev).body i bools bits
         let S := stateLoop g.inits b
         (b (mkRegList S (tys g.d.ss) (fun s => s) (fun f => f)) (mkHolds (tys g.d.ss) S)).fst)

/-- Independent type of `refBodyE`: the `Circuit` function type fully unfolded (`W → α × W`). -/
noncomputable def ExpectedRefBodyE (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    RegList (dom i) (HList (tys g.d.ss)) (Circuit.SigList (dom i) (tys g.d.ss)) (tys g.d.ss) →
    Circuit.SigList (dom i) (tys g.d.ss) → (List (Nat → Nat) × Circuit.SigList (dom i) (tys g.d.ss)) :=
  refBodyE g eb ev i bools bits

/-- Independent type of `genSemGenE`. -/
noncomputable def ExpectedGenSemGenE (X : Lean.Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) :
    Tools.ShippingGen5Sem.SrcSem ι dom := genSemGenE X g eb ev

/-- Mutant: the writes read one cycle late. -/
def MutWritesShift : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (X : Lean.Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat),
    valsAt (tys g.d.ss) (refBodyE g eb ev i bools bits
        (mkRegList S (tys g.d.ss) (fun s => s) (fun f => f)) (mkHolds (tys g.d.ss) S)).snd t =
      evalTerms
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) (t + 1) (S.val (t + 1))).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) (t + 1) (S.val (t + 1))).v (g.d.vpos j) w)
        g.d.nexts

/-- Mutant: the outputs are read in reverse order. -/
def MutResultReversed : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (X : Lean.Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat),
    ((refBodyE g eb ev i bools bits (mkRegList S (tys g.d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys g.d.ss) S)).fst).map (fun f => f t) =
      g.d.outs.reverse.map fun o => enc o.1 (eval
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).v (g.d.vpos j) w) o.2)

/-- Mutant: `source` with the observation dropped (`[]`). -/
def MutSourceEmpty : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (X : Lean.Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
    (genSemGenE X g eb ev).src i bools bits = []

end Expected

run_cmd Lean.Elab.Command.liftTermElabM do
  checkExpected ``genSemGenE_writes ``ExpectedWrites
  checkExpected ``genSemGenE_result ``ExpectedResult
  checkExpected ``genSemGenE_source ``ExpectedSource
  checkExpected ``refBodyE ``ExpectedRefBodyE
  checkExpected ``genSemGenE ``ExpectedGenSemGenE
  checkMutant ``genSemGenE_writes ``MutWritesShift
  checkMutant ``genSemGenE_result ``MutResultReversed
  checkMutant ``genSemGenE_source ``MutSourceEmpty

-- Axiom audit (standard axioms only).
run_cmd Lean.Elab.Command.liftTermElabM do
  for n in [``genSemGenE_writes, ``genSemGenE_result, ``genSemGenE_source, ``refBodyE, ``genSemGenE,
      ``valAtE, ``nextFnE, ``resultFnE, ``GenWF, ``kDOf] do
    checkAxioms n

/-! ## Closure audit (separate from the axiom audit)

`closureOf` walks the constants a root mentions, reading the type AND the body explicitly per kind (`thmInfo.value`, `defnInfo.value`,
`opaqueInfo.value`). Nothing is skipped silently: a name the environment does not know, an `opaque` (whose logical `value` is followed but whose
`@[implemented_by]` / `@[extern]` target and compiled code are NOT), and the kinds that carry no body (axiom, quot, inductive, constructor,
recursor — their *type* is walked) are recorded in the result and logged. Scope: kernel-level constant references of types and bodies in the
current environment; not source text, not compiled IR, not instances resolved at run time. -/

structure Closure where
  seen    : NameSet := {}
  missing : Array Name := #[]     -- referenced but not found in the environment
  opaques : Array Name := #[]     -- opaque: logical value followed, implementation target not followed
  bodyless : Array Name := #[]    -- axiom/quot/inductive/ctor/rec: type only
  deriving Inhabited

partial def closureOf (env : Environment) (root : Name) : StateT Closure MetaM Unit := do
  if (← get).seen.contains root then return
  modify fun c => { c with seen := c.seen.insert root }
  let walk (e : Expr) : StateT Closure MetaM Unit := do
    for c in e.getUsedConstants do closureOf env c
  match env.find? root with
  | none => modify fun c => { c with missing := c.missing.push root }
  | some (.thmInfo v) => walk v.type; walk v.value
  | some (.defnInfo v) => walk v.type; walk v.value
  | some (.opaqueInfo v) =>
    modify fun c => { c with opaques := c.opaques.push root }
    walk v.type; walk v.value
  | some ci =>
    modify fun c => { c with bodyless := c.bodyless.push root }
    walk ci.type

/-- Closure of `roots`; fails (never silently succeeds) if a referenced constant is unknown. -/
def closureRun (roots : List Name) : MetaM Closure := do
  let env ← getEnv
  let (_, c) ← (roots.forM (closureOf env)).run {}
  unless c.missing.isEmpty do
    throwError "GEN5 CLOSURE FAILED: unresolved constants {c.missing}"
  return c

def forbiddenConsts : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler, ``Lean.reduceBool, ``Lean.reduceNat]

def forbiddenIn (c : Closure) : List Name := forbiddenConsts.filter c.seen.contains

/-- Detector control entry: the forbidden constants the closure of `roots` reaches. -/
def detect (roots : List Name) : MetaM (List Name) := do return forbiddenIn (← closureRun roots)

-- Controls (no sorry / native_decide: the forbidden constants are only *referenced*; the deprecation lint is silenced for them).
set_option linter.deprecated false
namespace Ctl
theorem direct : ∀ a b, Lean.reduceBool a = b → a = b := fun a b h => Lean.ofReduceBool a b h
opaque viaOpaque : Nat := Lean.reduceNat 1
namespace OtherNs
theorem helperThm : ∀ a b, Lean.reduceBool a = b → a = b := fun a b h => Lean.ofReduceBool a b h
def helperDef : Nat := Lean.reduceNat 2
end OtherNs
namespace ThirdNs
theorem viaThm : ∀ a b, Lean.reduceBool a = b → a = b := OtherNs.helperThm
theorem viaDef : OtherNs.helperDef = OtherNs.helperDef := rfl
end ThirdNs
def helperClean : Nat := 3
theorem cleanThm : helperClean + 1 = 4 := rfl
namespace Unrelated
def cleanHelper (n : Nat) : Nat := n + 1
theorem cleanFact : cleanHelper 1 = 2 := rfl
end Unrelated
theorem cleanVia : Unrelated.cleanHelper 1 = 2 := Unrelated.cleanFact
end Ctl
set_option linter.deprecated true

run_cmd Lean.Elab.Command.liftTermElabM do
  -- negative controls: must be DETECTED
  for (r, want) in [(``Ctl.direct, ``Lean.ofReduceBool), (``Ctl.viaOpaque, ``Lean.reduceNat),
      (``Ctl.ThirdNs.viaThm, ``Lean.ofReduceBool), (``Ctl.ThirdNs.viaDef, ``Lean.reduceNat)] do
    let f ← detect [r]
    unless f.contains want do throwError "GEN5 CLOSURE CONTROL FAILED: {r} not detected as reaching {want} (got {f})"
  -- clean controls: must NOT be flagged
  for r in [``Ctl.cleanThm, ``Ctl.cleanVia, ``Ctl.Unrelated.cleanFact] do
    let f ← detect [r]
    unless f.isEmpty do throwError "GEN5 CLOSURE CONTROL FAILED: clean {r} falsely flagged {f}"
  logInfo m!"GEN5 CLOSURE CONTROLS OK: 4 forbidden uses detected (direct, opaque body, helper theorem and helper def in another namespace), 3 clean roots not flagged"

run_cmd Lean.Elab.Command.liftTermElabM do
  let roots := [``genSemGenE_writes, ``genSemGenE_result, ``genSemGenE_source, ``genSemGenE]
  let c ← closureRun roots
  let f := forbiddenIn c
  unless f.isEmpty do throwError "GEN5 CLOSURE FAILED: forbidden constants {f}"
  -- the unit does not mention the (unbuilt) suppliers
  for n in c.seen.toList do
    let s := n.toString
    if (s.splitOn "dataOf").length > 1 || (s.splitOn "genS_some").length > 1 || (s.splitOn "native").length > 1 then
      throwError "GEN5 CLOSURE FAILED: unexpected constant {n}"
  logInfo m!"GEN5 CLOSURE OK: {c.seen.toList.length} constants (types and bodies read by thm/defn/opaque kind), no forbidden/supplier constant; \
    opaque ({c.opaques.size}, logical value followed, implemented_by/extern/compiled code not followed): {c.opaques}; \
    body-less kinds (type only): {c.bodyless.size}; unresolved: 0"

-- Reach: the freeze's dependencies are actually reached from the proofs' bodies.
run_cmd Lean.Elab.Command.liftTermElabM do
  let reach (r : Name) (need : List Name) : MetaM Unit := do
    let c ← closureRun [r]
    for n in need do
      unless c.seen.contains n do throwError "GEN5 CLOSURE REACH FAILED: {r} does not reach {n}"
  reach ``genSemGenE_writes [``Tools.ShippingGen5Sem.valsAt_sigListOfFn, ``Tools.ShippingGen5Sem.reconState_mkHolds,
    ``Tools.ShippingGen5Sem.refBodyE, ``Tools.ShippingGen5Sem.nextFnE]
  reach ``genSemGenE_result [``Tools.ShippingGen5Sem.reconState_mkHolds, ``List.map_map,
    ``Tools.ShippingGen5Sem.refBodyE, ``Tools.ShippingGen5Sem.resultFnE]
  reach ``genSemGenE_source [``Tools.ShippingGen5Sem.refBodyE, ``Tools.ShippingGen5Sem.genSemGenE]
  logInfo m!"GEN5 CLOSURE REACH OK: writes -> P1 (valsAt_sigListOfFn) + P2 (reconState_mkHolds); result -> P2 + List.map_map; source -> refBodyE/genSemGenE"

#print axioms genSemGenE_writes
#print axioms genSemGenE_result
#print axioms genSemGenE_source

end Tests.Gen5.SemGenCheck
