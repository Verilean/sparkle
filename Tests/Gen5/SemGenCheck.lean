import Tools.ShippingGen5SemGen
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT (U3 check; clean build is the coder's). No sorry / axiom / native_decide.

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

-- Closure audit: the constants the unit mentions (transitively, through definitions and theorems) do not include forbidden ones.
partial def closureOf (env : Environment) (root : Name) : StateT NameSet MetaM Unit := do
  if (← get).contains root then return
  modify (·.insert root)
  match env.find? root with
  | none => pure ()
  | some ci =>
    for c in ci.type.getUsedConstants do closureOf env c
    match ci.value? with
    | some v => for c in v.getUsedConstants do closureOf env c
    | none => pure ()

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let roots := [``genSemGenE_writes, ``genSemGenE_result, ``genSemGenE_source, ``genSemGenE]
  let (_, seen) ← (roots.forM (closureOf env)).run {}
  let forbidden : List Name := [``sorryAx, ``Lean.ofReduceBool, ``Lean.trustCompiler]
  for f in forbidden do
    if seen.contains f then throwError "GEN5 CLOSURE FAILED: forbidden constant {f}"
  -- the unit does not mention the (unbuilt) suppliers
  for n in seen.toList do
    let s := n.toString
    if (s.splitOn "dataOf").length > 1 || (s.splitOn "genS_some").length > 1 || (s.splitOn "native").length > 1 then
      throwError "GEN5 CLOSURE FAILED: unexpected constant {n}"
  logInfo m!"GEN5 CLOSURE OK: {seen.toList.length} constants, no forbidden/supplier constant"

#print axioms genSemGenE_writes
#print axioms genSemGenE_result
#print axioms genSemGenE_source

end Tests.Gen5.SemGenCheck
