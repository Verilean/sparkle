import Tools.ShippingFGCircuitS2vLink
import Tests.Gen5.FGCircuitPilotCheck37
import Tests.Gen5.FGCircuitCmp
set_option autoImplicit false
-- FG circuit pilot S2v check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §46.

/-! # FGCircuitPilotCheck42 (light; ONE criterion `FGCircuitCmp.stmtEq` for every expected statement and every mutant, as in Check37)

1. FINAL3: `synth_hftPcieOutByte_finalOffCombined3_{Z,Y,X}` (18 explicit hypotheses, `hlink` gone) against Check37's independently written `ExpFinal2` family with its `HftRootLink` binder removed (`dropLink`: the binder whose domain is `HftRootLink`); every Check37 mutant (with the same removal) is rejected; the statement WITH `hlink` (the v2 one) and the S2k/S2h/... ones are rejected.
2. LINK: the type of `hftRootLink` against an independently written `ExpLink` (+ mutants).
3. STATES: the complete type of the general lemma `machine_states_of_tele_ext` (`ExpStatesGen`), the specialisation `root_states` (`ExpRoot`), mutants; `machine_states` of the root is the general lemma applied.
4. AXIOMS. -/
namespace Tests.Gen5.FGCircuitPilotCheck42
open Lean Meta Elab Command Term
open Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingMachineTele Tools.ShippingMachineTeleNest Tools.ShippingMachineTeleStates
open Tools.ShippingMachineNest (happendT castSS)
open Tools.ShippingUnifiedSource (eval)
open Tools.ShippingGen5Sem Tools.ShippingGen2
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1uSrc
open Tools.ShippingFGCircuit (monoObs)
open Tools.ShippingFGCircuitS1tFinal (cdvZ cdvY CDRel)
open Tools.ShippingFGCircuitS1rCD (HftObCDZ)
open Tools.ShippingFGCircuitS2vLink

variable {ι₀ : Type}

/-! ## independently written statements -/

def ExpLink : Prop :=
  ∀ {ι : Type} (gi : GenIn), gi.d = synth_hftPcieOutByte.machineData → ∀ (i : ι) (bools : Nat → Signal defaultDomain Bool)
    (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) (S : Signal defaultDomain (HList (tys gi.d.ss))),
    S.val 0 = gi.inits →
    (∀ t, S.val (t + 1) = evalTerms
      (fun j => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).b (gi.d.bpos j))
      (fun j w => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).v (gi.d.vpos j) w) gi.d.nexts) →
    ∀ t, (monoObs shHft synth_hftPcieOutByte bools bits).map (fun f => f t) = gi.d.outs.map fun o => enc o.1 (eval
      (fun j => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).b (gi.d.bpos j))
      (fun j w => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).v (gi.d.vpos j) w) o.2)

def MuLinkNoInit : Prop :=
  ∀ {ι : Type} (gi : GenIn), gi.d = synth_hftPcieOutByte.machineData → ∀ (i : ι) (bools : Nat → Signal defaultDomain Bool)
    (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) (S : Signal defaultDomain (HList (tys gi.d.ss))),
    (∀ t, S.val (t + 1) = evalTerms
      (fun j => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).b (gi.d.bpos j))
      (fun j w => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).v (gi.d.vpos j) w) gi.d.nexts) →
    ∀ t, (monoObs shHft synth_hftPcieOutByte bools bits).map (fun f => f t) = gi.d.outs.map fun o => enc o.1 (eval
      (fun j => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).b (gi.d.bpos j))
      (fun j w => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).v (gi.d.vpos j) w) o.2)

def MuLinkNoGi : Prop :=
  ∀ {ι : Type} (gi : GenIn), True → ∀ (i : ι) (bools : Nat → Signal defaultDomain Bool)
    (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) (S : Signal defaultDomain (HList (tys gi.d.ss))),
    S.val 0 = gi.inits →
    (∀ t, S.val (t + 1) = evalTerms
      (fun j => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).b (gi.d.bpos j))
      (fun j w => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).v (gi.d.vpos j) w) gi.d.nexts) →
    ∀ t, (monoObs shHft synth_hftPcieOutByte bools bits).map (fun f => f t) = gi.d.outs.map fun o => enc o.1 (eval
      (fun j => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).b (gi.d.bpos j))
      (fun j w => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).v (gi.d.vpos j) w) o.2)

def MuLinkSucc : Prop :=
  ∀ {ι : Type} (gi : GenIn), gi.d = synth_hftPcieOutByte.machineData → ∀ (i : ι) (bools : Nat → Signal defaultDomain Bool)
    (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) (S : Signal defaultDomain (HList (tys gi.d.ss))),
    S.val 0 = gi.inits →
    (∀ t, S.val (t + 1) = evalTerms
      (fun j => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).b (gi.d.bpos j))
      (fun j w => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).v (gi.d.vpos j) w) gi.d.nexts) →
    ∀ t, (monoObs shHft synth_hftPcieOutByte bools bits).map (fun f => f (t + 1)) = gi.d.outs.map fun o => enc o.1 (eval
      (fun j => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).b (gi.d.bpos j))
      (fun j w => (typedVal gi.d.nIn gi.d.bpos gi.d.vpos gi.d.ss gi.d.ls (extBOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S)
        (extOf (dom := fun _ => defaultDomain) (hftKids (ι := ι)) gi i bools bits S) t (S.val t)).v (gi.d.vpos j) w) o.2)


def ExpStatesGen : Prop :=
  ∀ {ι : Type} {declName : Name} (d : MachineData)
    (dom : ι → DomainConfig) (ss₂ : List SType) [Inhabited (HList (tys ss₂))]
    (l : TeleT ι dom ss₂ (fun _ => [])) (hss : ss₂ ++ l.sss = d.ss) {ρ : ι → Type}
    (inits : HList (tys ss₂))
    (body : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys ss₂)) (Circuit.SigList (dom i) (tys ss₂)) (tys ss₂) →
      HList (Tele.ρs (l.at i bools bits)) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys ss₂)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys ss₂)) → Tele.Sigs (l.at i bools bits) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk (castSS hss (happendT ss₂ l.sss inits l.initsT)) = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      castSS hss (l.fstate i bools bits
        (valsAt (tys ss₂) (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss)
          (mkHolds (tys ss₂) S)).snd t)
        (Tele.writesAt (regsOf (tys ss₂) S) (l.at i bools bits) () Ss t)) =
      evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
          (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).b
          (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
          (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).v
          (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      (obsR i (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss)
          (mkHolds (tys ss₂) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (resOn (Tools.ShippingMachineTele.fusedBody (l.at i bools bits)
        (body i bools bits))
        (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))))
    (hext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t p w : Nat),
      (ext i bools bits S Ss p w).val t =
        (ext i bools bits ⟨fun _ => S.val t⟩
          (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits) Ss t)) p w).val t)
    (hI : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)), Tele.InitOk (l.at i bools bits)) ,
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      ∃ (S₂ : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)),
        teleState l hss i bools bits S₂ Ss 0 = castSS hss (happendT ss₂ l.sss inits l.initsT) ∧
        (∀ t, teleState l hss i bools bits S₂ Ss (t + 1) = evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).v (d.vpos j) w) d.nexts) ∧
        ∀ t, (src i bools bits).map (fun f => f t) = d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).b (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).v (d.vpos k) w) o.2) 
def MuGenStep : Prop :=
  ∀ {ι : Type} {declName : Name} (d : MachineData)
    (dom : ι → DomainConfig) (ss₂ : List SType) [Inhabited (HList (tys ss₂))]
    (l : TeleT ι dom ss₂ (fun _ => [])) (hss : ss₂ ++ l.sss = d.ss) {ρ : ι → Type}
    (inits : HList (tys ss₂))
    (body : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys ss₂)) (Circuit.SigList (dom i) (tys ss₂)) (tys ss₂) →
      HList (Tele.ρs (l.at i bools bits)) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys ss₂)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys ss₂)) → Tele.Sigs (l.at i bools bits) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk (castSS hss (happendT ss₂ l.sss inits l.initsT)) = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      castSS hss (l.fstate i bools bits
        (valsAt (tys ss₂) (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss)
          (mkHolds (tys ss₂) S)).snd t)
        (Tele.writesAt (regsOf (tys ss₂) S) (l.at i bools bits) () Ss t)) =
      evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
          (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).b
          (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
          (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).v
          (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      (obsR i (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss)
          (mkHolds (tys ss₂) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (resOn (Tools.ShippingMachineTele.fusedBody (l.at i bools bits)
        (body i bools bits))
        (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))))
    (hext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t p w : Nat),
      (ext i bools bits S Ss p w).val t =
        (ext i bools bits ⟨fun _ => S.val t⟩
          (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits) Ss t)) p w).val t)
    (hI : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)), Tele.InitOk (l.at i bools bits)) ,
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      ∃ (S₂ : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)),
        teleState l hss i bools bits S₂ Ss 0 = castSS hss (happendT ss₂ l.sss inits l.initsT) ∧
        (∀ t, teleState l hss i bools bits S₂ Ss t = evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).v (d.vpos j) w) d.nexts) ∧
        ∀ t, (src i bools bits).map (fun f => f t) = d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).b (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).v (d.vpos k) w) o.2) 
def MuGenInit : Prop :=
  ∀ {ι : Type} {declName : Name} (d : MachineData)
    (dom : ι → DomainConfig) (ss₂ : List SType) [Inhabited (HList (tys ss₂))]
    (l : TeleT ι dom ss₂ (fun _ => [])) (hss : ss₂ ++ l.sss = d.ss) {ρ : ι → Type}
    (inits : HList (tys ss₂))
    (body : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys ss₂)) (Circuit.SigList (dom i) (tys ss₂)) (tys ss₂) →
      HList (Tele.ρs (l.at i bools bits)) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys ss₂)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys ss₂)) → Tele.Sigs (l.at i bools bits) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk (castSS hss (happendT ss₂ l.sss inits l.initsT)) = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      castSS hss (l.fstate i bools bits
        (valsAt (tys ss₂) (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss)
          (mkHolds (tys ss₂) S)).snd t)
        (Tele.writesAt (regsOf (tys ss₂) S) (l.at i bools bits) () Ss t)) =
      evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
          (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).b
          (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
          (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).v
          (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      (obsR i (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss)
          (mkHolds (tys ss₂) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (resOn (Tools.ShippingMachineTele.fusedBody (l.at i bools bits)
        (body i bools bits))
        (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))))
    (hext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t p w : Nat),
      (ext i bools bits S Ss p w).val t =
        (ext i bools bits ⟨fun _ => S.val t⟩
          (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits) Ss t)) p w).val t)
    (hI : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)), Tele.InitOk (l.at i bools bits)) ,
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      ∃ (S₂ : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)),
        teleState l hss i bools bits S₂ Ss 1 = castSS hss (happendT ss₂ l.sss inits l.initsT) ∧
        (∀ t, teleState l hss i bools bits S₂ Ss (t + 1) = evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).v (d.vpos j) w) d.nexts) ∧
        ∀ t, (src i bools bits).map (fun f => f t) = d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).b (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).v (d.vpos k) w) o.2) 
def MuGenSrc : Prop :=
  ∀ {ι : Type} {declName : Name} (d : MachineData)
    (dom : ι → DomainConfig) (ss₂ : List SType) [Inhabited (HList (tys ss₂))]
    (l : TeleT ι dom ss₂ (fun _ => [])) (hss : ss₂ ++ l.sss = d.ss) {ρ : ι → Type}
    (inits : HList (tys ss₂))
    (body : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys ss₂)) (Circuit.SigList (dom i) (tys ss₂)) (tys ss₂) →
      HList (Tele.ρs (l.at i bools bits)) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys ss₂)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys ss₂)) → Tele.Sigs (l.at i bools bits) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk (castSS hss (happendT ss₂ l.sss inits l.initsT)) = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      castSS hss (l.fstate i bools bits
        (valsAt (tys ss₂) (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss)
          (mkHolds (tys ss₂) S)).snd t)
        (Tele.writesAt (regsOf (tys ss₂) S) (l.at i bools bits) () Ss t)) =
      evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
          (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).b
          (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
          (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).v
          (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      (obsR i (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss)
          (mkHolds (tys ss₂) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (resOn (Tools.ShippingMachineTele.fusedBody (l.at i bools bits)
        (body i bools bits))
        (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))))
    (hext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t p w : Nat),
      (ext i bools bits S Ss p w).val t =
        (ext i bools bits ⟨fun _ => S.val t⟩
          (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits) Ss t)) p w).val t)
    (hI : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)), Tele.InitOk (l.at i bools bits)) ,
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      ∃ (S₂ : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)),
        teleState l hss i bools bits S₂ Ss 0 = castSS hss (happendT ss₂ l.sss inits l.initsT) ∧
        (∀ t, teleState l hss i bools bits S₂ Ss (t + 1) = evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).v (d.vpos j) w) d.nexts) ∧
        ∀ t, (src i bools bits).map (fun f => f (t + 1)) = d.outs.map fun o => enc o.1 (eval
          (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).b (d.bpos k))
          (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S₂ Ss) t
            (teleState l hss i bools bits S₂ Ss t)).v (d.vpos k) w) o.2) 

def ExpRoot : Prop :=
  ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n)),
    ∃ (S₂ : Signal defaultDomain (HList (tys [SType.bits 6]))) (Ss : Tele.Sigs (synth_hftPcieOutByte.machineInners.at i bools bits))
      (X : Nat → HList (tys synth_hftPcieOutByte.machineData.ss)),
      (∀ t, X t = teleState synth_hftPcieOutByte.machineInners
        (show [SType.bits 6] ++ synth_hftPcieOutByte.machineInners.sss = synth_hftPcieOutByte.machineData.ss from rfl) i bools bits S₂ Ss t) ∧
      X 0 = castSS (show [SType.bits 6] ++ synth_hftPcieOutByte.machineInners.sss = synth_hftPcieOutByte.machineData.ss from rfl)
        (happendT [SType.bits 6] synth_hftPcieOutByte.machineInners.sss synth_hftPcieOutByte.machineInits synth_hftPcieOutByte.machineInners.initsT) ∧
      (∀ t, X (t + 1) = evalTerms
        (fun j => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).b
          (synth_hftPcieOutByte.machineData.bpos j))
        (fun j w => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).v
          (synth_hftPcieOutByte.machineData.vpos j) w) synth_hftPcieOutByte.machineData.nexts) ∧
      ∀ t, (synth_hftPcieOutByte.machineSource i bools bits).map (fun f => f t) = synth_hftPcieOutByte.machineData.outs.map fun o => enc o.1 (eval
        (fun k => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).b
          (synth_hftPcieOutByte.machineData.bpos k))
        (fun k w => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).v
          (synth_hftPcieOutByte.machineData.vpos k) w) o.2) 
def MuRootStep : Prop :=
  ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n)),
    ∃ (S₂ : Signal defaultDomain (HList (tys [SType.bits 6]))) (Ss : Tele.Sigs (synth_hftPcieOutByte.machineInners.at i bools bits))
      (X : Nat → HList (tys synth_hftPcieOutByte.machineData.ss)),
      (∀ t, X t = teleState synth_hftPcieOutByte.machineInners
        (show [SType.bits 6] ++ synth_hftPcieOutByte.machineInners.sss = synth_hftPcieOutByte.machineData.ss from rfl) i bools bits S₂ Ss t) ∧
      X 0 = castSS (show [SType.bits 6] ++ synth_hftPcieOutByte.machineInners.sss = synth_hftPcieOutByte.machineData.ss from rfl)
        (happendT [SType.bits 6] synth_hftPcieOutByte.machineInners.sss synth_hftPcieOutByte.machineInits synth_hftPcieOutByte.machineInners.initsT) ∧
      (∀ t, X t = evalTerms
        (fun j => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).b
          (synth_hftPcieOutByte.machineData.bpos j))
        (fun j w => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).v
          (synth_hftPcieOutByte.machineData.vpos j) w) synth_hftPcieOutByte.machineData.nexts) ∧
      ∀ t, (synth_hftPcieOutByte.machineSource i bools bits).map (fun f => f t) = synth_hftPcieOutByte.machineData.outs.map fun o => enc o.1 (eval
        (fun k => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).b
          (synth_hftPcieOutByte.machineData.bpos k))
        (fun k w => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).v
          (synth_hftPcieOutByte.machineData.vpos k) w) o.2) 
def MuRootInit : Prop :=
  ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n)),
    ∃ (S₂ : Signal defaultDomain (HList (tys [SType.bits 6]))) (Ss : Tele.Sigs (synth_hftPcieOutByte.machineInners.at i bools bits))
      (X : Nat → HList (tys synth_hftPcieOutByte.machineData.ss)),
      (∀ t, X t = teleState synth_hftPcieOutByte.machineInners
        (show [SType.bits 6] ++ synth_hftPcieOutByte.machineInners.sss = synth_hftPcieOutByte.machineData.ss from rfl) i bools bits S₂ Ss t) ∧
      X 1 = castSS (show [SType.bits 6] ++ synth_hftPcieOutByte.machineInners.sss = synth_hftPcieOutByte.machineData.ss from rfl)
        (happendT [SType.bits 6] synth_hftPcieOutByte.machineInners.sss synth_hftPcieOutByte.machineInits synth_hftPcieOutByte.machineInners.initsT) ∧
      (∀ t, X (t + 1) = evalTerms
        (fun j => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).b
          (synth_hftPcieOutByte.machineData.bpos j))
        (fun j w => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).v
          (synth_hftPcieOutByte.machineData.vpos j) w) synth_hftPcieOutByte.machineData.nexts) ∧
      ∀ t, (synth_hftPcieOutByte.machineSource i bools bits).map (fun f => f t) = synth_hftPcieOutByte.machineData.outs.map fun o => enc o.1 (eval
        (fun k => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).b
          (synth_hftPcieOutByte.machineData.bpos k))
        (fun k w => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).v
          (synth_hftPcieOutByte.machineData.vpos k) w) o.2) 
def MuRootSrc : Prop :=
  ∀ (i : Unit) (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n)),
    ∃ (S₂ : Signal defaultDomain (HList (tys [SType.bits 6]))) (Ss : Tele.Sigs (synth_hftPcieOutByte.machineInners.at i bools bits))
      (X : Nat → HList (tys synth_hftPcieOutByte.machineData.ss)),
      (∀ t, X t = teleState synth_hftPcieOutByte.machineInners
        (show [SType.bits 6] ++ synth_hftPcieOutByte.machineInners.sss = synth_hftPcieOutByte.machineData.ss from rfl) i bools bits S₂ Ss t) ∧
      X 0 = castSS (show [SType.bits 6] ++ synth_hftPcieOutByte.machineInners.sss = synth_hftPcieOutByte.machineData.ss from rfl)
        (happendT [SType.bits 6] synth_hftPcieOutByte.machineInners.sss synth_hftPcieOutByte.machineInits synth_hftPcieOutByte.machineInners.initsT) ∧
      (∀ t, X (t + 1) = evalTerms
        (fun j => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).b
          (synth_hftPcieOutByte.machineData.bpos j))
        (fun j w => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).v
          (synth_hftPcieOutByte.machineData.vpos j) w) synth_hftPcieOutByte.machineData.nexts) ∧
      ∀ t, (synth_hftPcieOutByte.machineSource i bools bits).map (fun f => f (t + 1)) = synth_hftPcieOutByte.machineData.outs.map fun o => enc o.1 (eval
        (fun k => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).b
          (synth_hftPcieOutByte.machineData.bpos k))
        (fun k w => (typedVal synth_hftPcieOutByte.machineData.nIn synth_hftPcieOutByte.machineData.bpos synth_hftPcieOutByte.machineData.vpos
          synth_hftPcieOutByte.machineData.ss synth_hftPcieOutByte.machineData.ls bools (synth_hftPcieOutByte.machineExt i bools bits S₂ Ss) t (X t)).v
          (synth_hftPcieOutByte.machineData.vpos k) w) o.2) 

/-! ## the comparison (the same normalisation and criterion as Check37) -/
open Tests.Gen5.FGCircuitPilotCheck37 (norm37 tyOf)

/-- the type with the first binder whose domain is the constant `HftRootLink` removed (it does not occur in the rest) -/
partial def dropLink : Lean.Expr → Lean.Expr
  | .forallE n d b bi =>
    if d.isConstOf ``HftRootLink then b.lowerLooseBVars 1 1 else .forallE n d (dropLink b) bi
  | e => e

def unfoldLink (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    if e.isConstOf ``HftRootLink then
      if let some e' ← unfoldDefinition? e then return .done e'
    return .done e)

def sameC (what : String) (a exp : Lean.Expr) : MetaM Unit := Tests.Gen5.FGCircuitCmp.checkSame what a (← norm37 exp)
def diffC (what : String) (a exp : Lean.Expr) : MetaM Unit := Tests.Gen5.FGCircuitCmp.checkDiff what a (← norm37 exp)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := Lean.mkConst n
  let q37 (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck37 ++ Name.mkSimple n)
  let exp3 (mu : String) (ob cv : Name) : MetaM Lean.Expr := do pure (dropLink (← norm37 (mkApp2 (q37 mu) (C ob) (C cv))))
  let finZ ← norm37 (← tyOf ``synth_hftPcieOutByte_finalOffCombined3_Z)
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined3_Z" finZ (dropLink (← norm37 (mkApp2 (q37 "FD_real") (C ``HftObCDZ) (C ``cdvZ))))
  let finY ← norm37 (← tyOf ``synth_hftPcieOutByte_finalOffCombined3_Y)
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined3_Y" finY (dropLink (← norm37 (mkApp2 (q37 "FD_real") (C ``Tools.ShippingFGCircuitS1rCD.HftObCDY) (C ``cdvY))))
  let finX ← norm37 (← tyOf ``synth_hftPcieOutByte_finalOffCombined3_X)
  Tests.Gen5.FGCircuitCmp.checkSame "finalOffCombined3_X" finX (dropLink (← norm37 (mkApp2 (q37 "FD_real") (C ``Tools.ShippingFGCircuitS1rCD.HftObCDX) (C ``Tools.ShippingFGCircuitS1tFinal.cdvX))))
  let mut nm : Nat := 0
  for mu in ["FD_no_Adm", "FD_no_Down", "FD_no_D", "FD_no_G", "FD_no_T", "FD_no_S", "FD_no_0", "FD_no_Kgf", "FD_no_Hcd", "FD_hfind", "FD_hdec", "FD_hdecTrue", "FD_hmiss", "FD_hdecAndHmiss", "FD_hmissAndHfind", "FD_profOn", "FD_dNoReach", "FD_dNoReads", "FD_dStart", "FD_gNoReach", "FD_gAsD", "FD_tPlain", "FD_tNoReach", "FD_downUp", "FD_downId", "FD_psNoReach", "FD_psStart", "FD_psAny", "FD_adm_envEnd", "FD_adm_env0", "FD_adm_envIndep", "FD_reach_fromEnd", "FD_reach_fromIndep", "FD_prof_atEnd", "FD_prof_atIndep", "FD_kgf_envEnd", "FD_kgf_env0", "FD_kgf_envIndep", "FD_hcd_envEnd", "FD_hcd_env0", "FD_concl_envEnd", "FD_concl_env0", "FD_kgfSwap", "FD_kgfSwapName", "FD_kgfHttpTwice", "FD_kgfTlpTwice", "FD_kgfHttpOnly", "FD_kgfTlpOnly", "FD_kgfWholeBoth", "FD_kgfTrue", "FD_readersSwapped", "FD_readerShapes", "FD_diag", "FD_oldArt", "FD_noC1", "FD_noC2", "FD_noConcl", "FD_root", "FD_postRoot", "FD_output", "FD_refM", "FD_refC", "FD_ctxM", "FD_ctxC", "FD_design"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined3_Z vs {mu} (hlink removed)" finZ (← exp3 mu ``HftObCDZ ``cdvZ); nm := nm + 1
  for mu in ["FD_carrierY", "FD_carrierOld", "FD_obY"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined3_Z vs {mu} (hlink removed)" finZ (dropLink (← norm37 (q37 mu))); nm := nm + 1
  -- the statement WITH hlink (v2), and without the removal, are NOT the new one
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined3_Z vs the v2 statement (with hlink)" finZ (← norm37 (mkApp2 (q37 "FD_real") (C ``HftObCDZ) (C ``cdvZ))); nm := nm + 1
  Tests.Gen5.FGCircuitCmp.checkDiff "finalOffCombined3_Z vs the real v2 theorem type" finZ (← norm37 (← tyOf `Tools.ShippingFGCircuitS2rFinal.synth_hftPcieOutByte_finalOffCombined2_Z)); nm := nm + 1
  for (old, what) in [(`Tools.ShippingFGCircuitS2kFinal.synth_hftPcieOutByte_finalOffCombined_Z, "S2k combined"), (`Tools.ShippingFGCircuitS2hHist.synth_hftPcieOutByte_finalOffLNKH_Z, "S2h"),
      (`Tools.ShippingFGCircuitS2jTop.synth_hftPcieOutByte_finalOffLNKKGT_Z, "S2j"), (`Tools.ShippingFGCircuitS2gGates.synth_hftPcieOutByte_finalOffLNKKG_Z, "S2g"),
      (`Tools.ShippingFGCircuitS2dKids.synth_hftPcieOutByte_finalOffLNKK_Z, "S2d")] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"finalOffCombined3_Z vs the {what} statement" finZ (← norm37 (← tyOf old)); nm := nm + 1
  logInfo m!"FGCIRCUIT42 SIGNATURES-FINAL3: the complete type of synth_hftPcieOutByte_finalOffCombined3_Z/Y/X (18 explicit hypotheses: L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd hadm hdown hD hG hT hs h0 hkgfacts; hlink is gone) equals Check37's independently written ExpFinal2 with its HftRootLink binder removed, under ONE criterion (FGCircuitCmp.stmtEq; binder kinds at all depths); {nm} mutants rejected with the same criterion (Check37's 66 mutants with the same removal, the v2 statement with hlink, the real v2 theorem type, the older final statements)"

run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := Lean.mkConst n
  let Q (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck42 ++ Name.mkSimple n)
  let a ← norm37 (← unfoldLink (← tyOf ``hftRootLink))
  Tests.Gen5.FGCircuitCmp.checkSame "hftRootLink" a (← norm37 (Q "ExpLink"))
  let a2 ← norm37 (← unfoldLink (← tyOf ``Tools.ShippingFGCircuitS2kLink.hftRootLink))
  Tests.Gen5.FGCircuitCmp.checkSame "S2kLink.hftRootLink" a2 (← norm37 (Q "ExpLink"))
  let mut nm := 0
  for mu in ["MuLinkNoInit", "MuLinkNoGi", "MuLinkSucc"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"hftRootLink vs {mu}" a (← norm37 (Q mu)); nm := nm + 1
  logInfo m!"FGCIRCUIT42 SIGNATURES-LINK: the type of Tools.ShippingFGCircuitS2kLink.hftRootLink (HftRootLink, now a THEOREM) equals the independently written ExpLink under the same criterion; {nm} mutants rejected (no initial-state premise, no GenIn-data premise, observation at t+1)"

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
run_cmd liftTermElabM do
  let C (n : Name) : Lean.Expr := Lean.mkConst n
  let Q (n : String) : Lean.Expr := Lean.mkConst (`Tests.Gen5.FGCircuitPilotCheck42 ++ Name.mkSimple n)
  let g ← norm37 (← tyOf ``Tools.ShippingMachineTeleStates.machine_states_of_tele_ext)
  Tests.Gen5.FGCircuitCmp.checkSame "machine_states_of_tele_ext" g (← norm37 (Q "ExpStatesGen"))
  let mut nm := 0
  for mu in ["MuGenStep", "MuGenInit", "MuGenSrc"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"machine_states_of_tele_ext vs {mu}" g (← norm37 (Q mu)); nm := nm + 1
  let r ← norm37 (← tyOf ``root_states)
  Tests.Gen5.FGCircuitCmp.checkSame "root_states" r (← norm37 (Q "ExpRoot"))
  for mu in ["MuRootStep", "MuRootInit", "MuRootSrc"] do
    Tests.Gen5.FGCircuitCmp.checkDiff s!"root_states vs {mu}" r (← norm37 (Q mu)); nm := nm + 1
  -- `machine_states` of the root is the general lemma applied (its proof term), and `root_states` is proved from it
  let env ← getEnv
  let some ms := env.find? `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte.machine_states | throwError "machine_states missing"
  let some v := ms.value? | throwError "machine_states has no value"
  unless v.getAppFn.isConstOf ``Tools.ShippingMachineTeleStates.machine_states_of_tele_ext do throwError "machine_states is not the general lemma applied"
  let some rv := (env.find? ``root_states).bind (·.value?) | throwError "root_states has no value"
  unless rv.getUsedConstants.contains `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte.machine_states do throwError "root_states does not use machine_states"
  unless rv.getUsedConstants.contains ``Tools.ShippingFGCircuitS2kLink.states_abs do throwError "root_states does not use states_abs"
  logInfo m!"FGCIRCUIT42 SIGNATURES-STATES: the complete type of the general lemma machine_states_of_tele_ext equals the independently written ExpStatesGen, and the type of the root specialisation root_states (the fused state as an abstract stream X, with X t = teleState machineInners ..., over machineData / machineExt / machineSource / machineInits) equals ExpRoot, under the same criterion; {nm} mutants rejected (step at t instead of t+1, initial state at 1, observation at t+1); the value of synth_hftPcieOutByte.machine_states is the general lemma applied (head machine_states_of_tele_ext) and root_states is proved from machine_states and states_abs"

run_cmd liftTermElabM do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo : List Name := [``synth_hftPcieOutByte_finalOffCombined3_Z, ``synth_hftPcieOutByte_finalOffCombined3_Y, ``synth_hftPcieOutByte_finalOffCombined3_X, ``root_states, ``Tools.ShippingFGCircuitS2kLink.hftRootLink, ``Tools.ShippingFGCircuitS2kLink.link_concl, ``Tools.ShippingFGCircuitS2kLink.states_abs]
  let mut axs : NameSet := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some (.axiomInfo _) => axs := axs.insert n
    | some ci =>
      todo := ci.type.getUsedConstants.toList ++ todo
      if let some v := ci.value? then todo := v.getUsedConstants.toList ++ todo
    | none => pure ()
  let bad := axs.toList.filter fun n => ![``propext, ``Classical.choice, ``Quot.sound].contains n
  unless bad.isEmpty do throwError "non-standard axioms: {bad}"
  logInfo m!"FGCIRCUIT42 AXIOMS: the final statement 3 (Z/Y/X), hftRootLink, link_concl, states_abs and root_states depend on standard axioms only ({axs.toList}); no sorryAx, no native_decide"

end Tests.Gen5.FGCircuitPilotCheck42
