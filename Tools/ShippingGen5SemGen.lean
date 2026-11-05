import Tools.ShippingGen5SemRef
import Tools.ShippingGen5SemPkg
set_option autoImplicit false
-- Built in g5sm-u3 at 4ebc4067 (Pod `kjob lake build`, exit 0; SemGenCheck: TYPE 5, MUTANT 3, AXIOMS standard, CLOSURE OK). Clean build is the coder's. No sorry / axiom / native_decide.

/-! # DG-SEM unit U3 (P3): the generated reference body `refBodyE`, `genSemGenE`, and the three `GenFacts` instances

Implements `scripts/gen5/DG_SEM_FREEZE_REV3.md` §1 as frozen (with the §1.2 type correction: `refBodyE : RegList … → Circuit …`, one state
argument). `GenIn` is rev1 §1 and `GenWF` is rev2 §1 (RowA/RowB/RowC); they are only *stated* here, no row is supplied for any real run
(DG-WFCOVER) and nothing about `dataOf` (DG-DATAOF) is used. U3 is abstract in the extension families `eb`/`ev`. -/
namespace Tools.ShippingGen5Sem
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineRef (reads)
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge Sparkle.Compiler.MachInstOrigin

/-! ## `GenWF` (rev2 §1) and `GenIn` (rev1 §1) -/

def kDOf (d : MachineData) : Nat := d.nIn - d.shape.insts.length
def callArgs (d : MachineData) (k : Nat) : List Nat := ((d.shape.insts.map (·.2.1))[k]?).getD []
def callKind (d : MachineData) (k : Nat) : MixedGateBinder := (((d.bsIn.drop (kDOf d))[k]?).map (·.2)).getD .domain
def letSort (d : MachineData) (l : Nat) : Option SType := (d.ls[l]?).map (·.1)
def originOf (d : MachineData) (k : Nat) : InstOrigin := d.shape.instOrigins.getD k .ord

def RowA (d : MachineData) : Bool :=
  decide (d.shape.insts.length ≤ d.nIn) &&
  decide (d.shape.instOrigins.length = d.shape.insts.length) &&
  (List.range d.shape.insts.length).all fun k =>
    (callArgs d k).all (· < d.ls.length) &&
    (match originOf d k with
     | .mem _ _ _ => decide ((callArgs d k).length = 4)
     | _ => true)

def RowB (d : MachineData) : Bool :=
  (List.range d.shape.insts.length).all fun k =>
    (match callKind d k with | .domain => false | _ => true) &&
    (match originOf d k, callArgs d k with
     | .mem _ aw dw, [l0, l1, l2, l3] =>
         decide (callKind d k = .bits dw) &&
         decide (letSort d l0 = some (.bits aw)) && decide (letSort d l1 = some (.bits dw)) &&
         decide (letSort d l2 = some .bool) && decide (letSort d l3 = some (.bits aw))
     | .mem _ _ _, _ => false
     | _, _ => true)

def posOk (d : MachineData) (k : Nat) (clean : List Bool) (p : Nat) : Bool :=
  decide (p < kDOf d + k) ||
  (decide (d.nIn ≤ p) && decide (p < d.nIn + d.ss.length)) ||
  (decide (d.nIn + d.ss.length ≤ p) && clean.getD (p - (d.nIn + d.ss.length)) false)

def cleanLets (d : MachineData) (k : Nat) : List Bool :=
  d.ls.foldl (fun clean l =>
    clean ++ [reads (fun j => posOk d k clean (d.bpos j)) (fun j => posOk d k clean (d.vpos j)) l.2]) []

def RowC (d : MachineData) : Bool :=
  (List.range d.shape.insts.length).all fun k => (callArgs d k).all fun l => (cleanLets d k)[l]? == some true

def GenWF (d : MachineData) : Bool := RowA d && RowB d && RowC d

/-- Everything `genSem` reads from the reader data (rev1 §1). -/
structure GenIn where
  d      : MachineData
  wf     : GenWF d = true
  inits  : HList (tys d.ss)
  ok     : d.ok = true
  bodyEq : d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
                                      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  init   : d.initOk inits = true

/-! ## U3 (rev3 §1) -/

abbrev ExtB (ι : Type) (dom : ι → DomainConfig) (ss : List SType) : Type :=
  (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys ss)) → Nat → Signal (dom i) Bool
abbrev ExtV (ι : Type) (dom : ι → DomainConfig) (ss : List SType) : Type :=
  (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Signal (dom i) (HList (tys ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)

variable {ι : Type} {dom : ι → DomainConfig}

noncomputable def valAtE (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat) : TVal :=
  typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)

noncomputable def nextFnE (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat) : HList (tys g.d.ss) :=
  evalTerms (fun j => (valAtE g eb ev i bools bits S t).b (g.d.bpos j))
            (fun j w => (valAtE g eb ev i bools bits S t).v (g.d.vpos j) w) g.d.nexts

noncomputable def resultFnE (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) : List (Nat → Nat) :=
  g.d.outs.map fun o t => enc o.1 (eval (fun j => (valAtE g eb ev i bools bits S t).b (g.d.bpos j))
                                        (fun j w => (valAtE g eb ev i bools bits S t).v (g.d.vpos j) w) o.2)

/-- `ρ i := List (Nat → Nat)`; the state is rebuilt from `holds` (P2); the pending writes are packed (P1). -/
noncomputable def refBodyE (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    RegList (dom i) (HList (tys g.d.ss)) (Circuit.SigList (dom i) (tys g.d.ss)) (tys g.d.ss) →
    Circuit (dom i) (Circuit.SigList (dom i) (tys g.d.ss)) (List (Nat → Nat)) :=
  fun _regs holds =>
    let S := reconState (tys g.d.ss) holds
    (resultFnE g eb ev i bools bits S, sigListOfFn (tys g.d.ss) (nextFnE g eb ev i bools bits S))

noncomputable def genSemGenE (X : Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) : SrcSem ι dom :=
  { decl := X, d := g.d, kD := kDOf g.d, ρ := fun _ => List (Nat → Nat), inh := ⟨g.inits⟩, inits := g.inits,
    body := refBodyE g eb ev, obsR := fun _ r => r, ext := ev, extB := eb,
    src := fun i bools bits =>
      (refBodyE g eb ev i bools bits
        (mkRegList (@stateLoop _ _ _ ⟨g.inits⟩ g.inits (refBodyE g eb ev i bools bits)) (tys g.d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys g.d.ss) (@stateLoop _ _ _ ⟨g.inits⟩ g.inits (refBodyE g eb ev i bools bits)))).fst }

theorem genSemGenE_writes (X : Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat) :
    valsAt (tys g.d.ss) (refBodyE g eb ev i bools bits
        (mkRegList S (tys g.d.ss) (fun s => s) (fun f => f)) (mkHolds (tys g.d.ss) S)).snd t =
      evalTerms
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).v (g.d.vpos j) w)
        g.d.nexts := by
  unfold refBodyE
  dsimp only
  rw [reconState_mkHolds, valsAt_sigListOfFn]
  rfl

theorem genSemGenE_result (X : Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (t : Nat) :
    ((refBodyE g eb ev i bools bits (mkRegList S (tys g.d.ss) (fun s => s) (fun f => f))
        (mkHolds (tys g.d.ss) S)).fst).map (fun f => f t) =
      g.d.outs.map fun o => enc o.1 (eval
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits S) (ev i bools bits S) t (S.val t)).v (g.d.vpos j) w) o.2) := by
  unfold refBodyE
  dsimp only
  rw [reconState_mkHolds]
  unfold resultFnE valAtE
  rw [List.map_map]
  rfl

theorem genSemGenE_source (X : Name) (g : GenIn) (eb : ExtB ι dom g.d.ss) (ev : ExtV ι dom g.d.ss) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    (genSemGenE X g eb ev).src i bools bits =
      (genSemGenE X g eb ev).obsR i
        ((genSemGenE X g eb ev).body i bools bits
          (mkRegList (@stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGenE X g eb ev).body i bools bits))
            (tys g.d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys g.d.ss) (@stateLoop _ _ _ ⟨g.inits⟩ g.inits ((genSemGenE X g eb ev).body i bools bits)))).fst :=
  rfl

end Tools.ShippingGen5Sem
