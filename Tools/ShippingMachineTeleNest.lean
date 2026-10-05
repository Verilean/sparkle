import Tools.ShippingMachineTele
import Tools.ShippingMachineNest

/-! # The trace theorem of a `circuit do` with a CHAIN of sub-machines

`machine_trace_of_nested_ext` (ShippingMachineNest) for sub-machines that
read the earlier ones' results (`Tele`, ShippingMachineTele): the parser /
emitter chain of `hftStrategy`. Per declaration the generator supplies the
chain (`TeleT`: slot sorts, result type, reset values, body reading the
enclosing handles and the earlier results, latest first), the enclosing
body over the tuple of the results, and the same `rfl`s. -/
namespace Tools.ShippingMachineTeleNest
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMachineNest (happendT splitL splitR splitL_happendT splitR_happendT happendT_split castSS)
open Tools.ShippingMachineTele
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness

/-- A chain of sub-machines, for every domain and inputs: each body reads the
enclosing handles (`ss₂`) and the earlier results (`pre`, latest first). -/
inductive TeleT (ι : Type) (dom : ι → DomainConfig) (ss₂ : List SType) :
    (ι → List Type) → Type 1 where
  | nil {pre : ι → List Type} : TeleT ι dom ss₂ pre
  | cons {pre : ι → List Type} (ss : List SType) (inh : Inhabited (HList (tys ss)))
      (ρ : ι → Type) (inits : HList (tys ss))
      (body : (i : ι) → (Nat → Signal (dom i) Bool) →
        ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
        RegList (dom i) (HList (tys ss₂)) (Circuit.SigList (dom i) (tys ss₂)) (tys ss₂) →
        HList (pre i) →
        RegList (dom i) (HList (tys ss)) (Circuit.SigList (dom i) (tys ss)) (tys ss) →
        Circuit (dom i) (Circuit.SigList (dom i) (tys ss)) (ρ i))
      (rest : TeleT ι dom ss₂ (fun i => ρ i :: pre i)) : TeleT ι dom ss₂ pre
  | loop {pre : ι → List Type} (ss : List SType) (inh : Inhabited (HList (tys ss)))
      (α : ι → Type) (inhα : ∀ i, Inhabited (α i)) (ρ : ι → Type)
      (enc : ∀ i, α i → HList (tys ss)) (dec : ∀ i, HList (tys ss) → α i)
      (hed : ∀ i x, enc i (dec i x) = x) (inits : HList (tys ss))
      (f : (i : ι) → (Nat → Signal (dom i) Bool) →
        ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
        RegList (dom i) (HList (tys ss₂)) (Circuit.SigList (dom i) (tys ss₂)) (tys ss₂) →
        HList (pre i) → Signal (dom i) (α i) → Signal (dom i) (α i))
      (res : (i : ι) → (Nat → Signal (dom i) Bool) →
        ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
        RegList (dom i) (HList (tys ss₂)) (Circuit.SigList (dom i) (tys ss₂)) (tys ss₂) →
        HList (pre i) → Signal (dom i) (α i) → ρ i)
      (rest : TeleT ι dom ss₂ (fun i => ρ i :: pre i)) : TeleT ι dom ss₂ pre

variable {ι : Type} {dom : ι → DomainConfig} {ss₂ : List SType}

/-- The chain in one domain, for given inputs. -/
def TeleT.at : {pre : ι → List Type} → TeleT ι dom ss₂ pre → (i : ι) →
    (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    Tele (dom i) (tys ss₂) (pre i)
  | _, .nil, _, _, _ => .nil
  | _, .cons ss inh ρ inits body rest, i, bools, bits =>
    .cons (tys ss) inh (ρ i) inits (body i bools bits) (rest.at i bools bits)
  | _, .loop ss inh α inhα ρ enc dec hed inits f res rest, i, bools, bits =>
    .loop (tys ss) inh (α i) (inhα i) (ρ i) (enc i) (dec i) (hed i) inits (f i bools bits)
      (res i bools bits) (rest.at i bools bits)

/-- The slot sorts of the chain, in order. -/
def TeleT.sss : {pre : ι → List Type} → TeleT ι dom ss₂ pre → List SType
  | _, .nil => []
  | _, .cons ss _ _ _ _ rest => ss ++ rest.sss
  | _, .loop ss _ _ _ _ _ _ _ _ _ _ rest => ss ++ rest.sss

/-- The reset values of the chain, flattened. -/
def TeleT.initsT : {pre : ι → List Type} → (l : TeleT ι dom ss₂ pre) → HList (tys l.sss)
  | _, .nil => ()
  | _, .cons ss _ _ inits _ rest => happendT ss rest.sss inits rest.initsT
  | _, .loop ss _ _ _ _ _ _ _ inits _ _ rest => happendT ss rest.sss inits rest.initsT

section
variable (i : ι) (bools : Nat → Signal (dom i) Bool)
  (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))

/-- The chain's states, flattened. -/
def TeleT.flat : {pre : ι → List Type} → (l : TeleT ι dom ss₂ pre) →
    HList (Tele.σs (l.at i bools bits)) → HList (tys l.sss)
  | _, .nil, _ => ()
  | _, .cons ss _ _ _ _ rest, xs => happendT ss rest.sss xs.1 (rest.flat xs.2)
  | _, .loop ss _ _ _ _ _ _ _ _ _ _ rest, xs => happendT ss rest.sss xs.1 (rest.flat xs.2)

/-- The chain's states from the flattened tuple. -/
def TeleT.unflat : {pre : ι → List Type} → (l : TeleT ι dom ss₂ pre) →
    HList (tys l.sss) → HList (Tele.σs (l.at i bools bits))
  | _, .nil, _ => ()
  | _, .cons ss _ _ _ _ rest, x => (splitL ss rest.sss x, rest.unflat (splitR ss rest.sss x))
  | _, .loop ss _ _ _ _ _ _ _ _ _ _ rest, x => (splitL ss rest.sss x, rest.unflat (splitR ss rest.sss x))

theorem TeleT.unflat_flat : ∀ {pre : ι → List Type} (l : TeleT ι dom ss₂ pre)
    (xs : HList (Tele.σs (l.at i bools bits))),
    l.unflat i bools bits (l.flat i bools bits xs) = xs
  | _, .nil, _ => rfl
  | _, .cons ss _ _ _ _ rest, xs => by
    show (splitL ss rest.sss (happendT ss rest.sss xs.1 (rest.flat i bools bits xs.2)),
      rest.unflat i bools bits (splitR ss rest.sss
        (happendT ss rest.sss xs.1 (rest.flat i bools bits xs.2)))) = xs
    rw [splitL_happendT, splitR_happendT, TeleT.unflat_flat rest xs.2]
    rfl
  | _, .loop ss _ _ _ _ _ _ _ _ _ _ rest, xs => by
    show (splitL ss rest.sss (happendT ss rest.sss xs.1 (rest.flat i bools bits xs.2)),
      rest.unflat i bools bits (splitR ss rest.sss
        (happendT ss rest.sss xs.1 (rest.flat i bools bits xs.2)))) = xs
    rw [splitL_happendT, splitR_happendT, TeleT.unflat_flat rest xs.2]
    rfl

theorem TeleT.flat_unflat : ∀ {pre : ι → List Type} (l : TeleT ι dom ss₂ pre)
    (x : HList (tys l.sss)), l.flat i bools bits (l.unflat i bools bits x) = x
  | _, .nil, _ => rfl
  | _, .cons ss _ _ _ _ rest, x => by
    show happendT ss rest.sss (splitL ss rest.sss x)
      (rest.flat i bools bits (rest.unflat i bools bits (splitR ss rest.sss x))) = x
    rw [TeleT.flat_unflat rest, happendT_split]
  | _, .loop ss _ _ _ _ _ _ _ _ _ _ rest, x => by
    show happendT ss rest.sss (splitL ss rest.sss x)
      (rest.flat i bools bits (rest.unflat i bools bits (splitR ss rest.sss x))) = x
    rw [TeleT.flat_unflat rest, happendT_split]

theorem TeleT.flat_initsOf : ∀ {pre : ι → List Type} (l : TeleT ι dom ss₂ pre),
    l.flat i bools bits (Tele.initsOf (l.at i bools bits)) = l.initsT
  | _, .nil => rfl
  | _, .cons ss _ _ inits _ rest => by
    show happendT ss rest.sss inits (rest.flat i bools bits (Tele.initsOf (rest.at i bools bits))) = _
    rw [TeleT.flat_initsOf rest]
    rfl
  | _, .loop ss _ _ _ _ _ _ _ inits _ _ rest => by
    show happendT ss rest.sss inits (rest.flat i bools bits (Tele.initsOf (rest.at i bools bits))) = _
    rw [TeleT.flat_initsOf rest]
    rfl

/-- The flattened state: the enclosing state, then the chain's. -/
def TeleT.fstate {pre : ι → List Type} (l : TeleT ι dom ss₂ pre) (a : HList (tys ss₂))
    (xs : HList (Tele.σs (l.at i bools bits))) : HList (tys (ss₂ ++ l.sss)) :=
  happendT ss₂ l.sss a (l.flat i bools bits xs)

end

set_option maxHeartbeats 2000000 in
/-- **Source to RTL for a `circuit do` with a chain of sub-machines** (each
reading the enclosing handles and the earlier ones' results), with the
`@[hardware_module]` calls' outputs given by `ext` (over the enclosing and
the chain's state signals; `hext`: pointwise). As
`machine_trace_of_nested_ext`, with the chain on its loops. -/
theorem machine_trace_of_tele_ext {declName : Name} (d : MachineData)
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
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)), Tele.InitOk (l.at i bools bits))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceWith declName d m dom src (fun i bools bits =>
      ext i bools bits
        (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))
        (Tele.loops (regsOf (tys ss₂)
          (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
          (l.at i bools bits) ())) := by
  obtain ⟨shape, nIn, domE, bposL, vposL, vwL, ss, ls, outs, nexts⟩ := d
  simp only at hss
  subst hss
  refine machine_trace_of_stream _ dom (happendT ss₂ l.sss inits l.initsT) src ok hbody
    hinit _ ?_ hr entry closes
  intro i bools bits
  let E : HList (tys ss₂) → HList (Tele.σs (l.at i bools bits)) → Nat → HList (tys (ss₂ ++ l.sss)) :=
    fun a xs t => evalTerms
      (fun j => (typedVal nIn (fun j => bposL.getD j 0) (fun j => vposL.getD j 0) (ss₂ ++ l.sss) ls
        bools (ext i bools bits ⟨fun _ => a⟩ (Tele.constOf (l.at i bools bits) xs)) t
        (l.fstate i bools bits a xs)).b (bposL.getD j 0))
      (fun j w => (typedVal nIn (fun j => bposL.getD j 0) (fun j => vposL.getD j 0) (ss₂ ++ l.sss) ls
        bools (ext i bools bits ⟨fun _ => a⟩ (Tele.constOf (l.at i bools bits) xs)) t
        (l.fstate i bools bits a xs)).v (vposL.getD j 0) w) nexts
  have hw : ∀ (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      l.fstate i bools bits
        (valsAt (tys ss₂) (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss) (mkHolds (tys ss₂) S)).snd t)
        (Tele.writesAt (regsOf (tys ss₂) S) (l.at i bools bits) () Ss t) =
      E (S.val t) (Tele.valsOf (l.at i bools bits) Ss t) t := by
    intro S Ss t
    have h := writes i bools bits S Ss t
    rw [typedVal_congr _ _ _ _ _ bools (ext i bools bits S Ss)
      (ext i bools bits ⟨fun _ => S.val t⟩
        (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits) Ss t))) t _
      (fun p w => hext i bools bits S Ss t p w)] at h
    exact h
  have hG : Tools.ShippingMachineTele.OuterPointwise (l.at i bools bits) (body i bools bits)
      (fun a xs t => splitL ss₂ l.sss (E a xs t)) := by
    intro S Ss t
    show _ = splitL ss₂ l.sss (E (S.val t) (Tele.valsOf (l.at i bools bits) Ss t) t)
    rw [← hw S Ss t]
    unfold TeleT.fstate
    rw [splitL_happendT]
  have hF : TelePointwise (l.at i bools bits)
      (fun a xs t => l.unflat i bools bits (splitR ss₂ l.sss (E a xs t))) := by
    intro S Ss t
    show _ = l.unflat i bools bits (splitR ss₂ l.sss
      (E (S.val t) (Tele.valsOf (l.at i bools bits) Ss t) t))
    rw [← hw S Ss t]
    unfold TeleT.fstate
    rw [splitR_happendT, TeleT.unflat_flat]
  obtain ⟨h0, x0, hstep⟩ :=
    Tools.ShippingMachineTele.fused_state inits (l.at i bools bits) (body i bools bits) _ hF
      (hI i bools bits) _ hG
  simp only at x0 hstep
  refine ⟨fun t => l.fstate i bools bits
    ((stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))).val t)
    (Tele.valsOf (l.at i bools bits) (Tele.loops (regsOf (tys ss₂)
      (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
      (l.at i bools bits) ()) t), ?_, ?_, ?_⟩
  · show TeleT.fstate i bools bits l _ _ = _
    rw [h0, x0]
    unfold TeleT.fstate
    rw [TeleT.flat_initsOf]
  · intro t
    show TeleT.fstate i bools bits l _ _ = _
    rw [(hstep t).1, (hstep t).2]
    unfold TeleT.fstate
    rw [TeleT.flat_unflat, happendT_split]
    show E _ _ t = _
    simp only [E]
    rw [typedVal_congr _ _ _ _ _ bools
      (ext i bools bits ⟨fun _ => (stateLoop inits
          (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))).val t⟩
        (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits)
          (Tele.loops (regsOf (tys ss₂) (stateLoop inits
            (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
            (l.at i bools bits) ()) t)))
      (ext i bools bits (stateLoop inits
          (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))
        (Tele.loops (regsOf (tys ss₂) (stateLoop inits
          (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
          (l.at i bools bits) ())) t _
      (fun p w => (hext i bools bits _ _ t p w).symm)]
    rfl
  · intro j
    rw [hsrc i bools bits, Tools.ShippingMachineTele.fusedBody_result]
    exact hres i bools bits _ _ j

def letObsT (d : MachineData) (dom : ι → DomainConfig) (ss₂ : List SType)
    [Inhabited (HList (tys ss₂))] (l : TeleT ι dom ss₂ (fun _ => [])) (hss : ss₂ ++ l.sss = d.ss)
    {ρ : ι → Type} (inits : HList (tys ss₂))
    (body : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys ss₂)) (Circuit.SigList (dom i) (tys ss₂)) (tys ss₂) →
      HList (Tele.ρs (l.at i bools bits)) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys ss₂)) (ρ i))
    (ext : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys ss₂)) → Tele.Sigs (l.at i bools bits) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat) :=
  fun i bools bits =>
    let S := stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))
    let Ss := Tele.loops (regsOf (tys ss₂) S) (l.at i bools bits) ()
    d.ls.map fun lt => fun j => enc lt.1 (eval
      (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) j
        (castSS hss (l.fstate i bools bits (S.val j) (Tele.valsOf (l.at i bools bits) Ss j)))).b
        (d.bpos k))
      (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) j
        (castSS hss (l.fstate i bools bits (S.val j) (Tele.valsOf (l.at i bools bits) Ss j)))).v
        (d.vpos k) w) lt.2)

/-- `machine_trace_of_tele_ext` with the wiring and the `let` wires. -/
theorem machine_traceL_of_tele_ext {declName : Name} (d : MachineData)
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
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss) (mkHolds (tys ss₂) S)).snd t)
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
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss) (mkHolds (tys ss₂) S)).fst).map
          (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S Ss) t
            (castSS hss (l.fstate i bools bits (S.val t) (Tele.valsOf (l.at i bools bits) Ss t)))).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (resOn (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))
        (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))))
    (hext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t p w : Nat),
      (ext i bools bits S Ss p w).val t =
        (ext i bools bits ⟨fun _ => S.val t⟩
          (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits) Ss t)) p w).val t)
    (hI : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)), Tele.InitOk (l.at i bools bits))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTraceL declName d m design dom src (fun i bools bits =>
      ext i bools bits (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))
        (Tele.loops (regsOf (tys ss₂)
          (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
          (l.at i bools bits) ()))
      (letObsT d dom ss₂ l hss inits body ext) := by
  obtain ⟨shape, nIn, domE, bposL, vposL, vwL, ss, ls, outs, nexts⟩ := d
  simp only at hss
  subst hss
  refine machine_trace_lets_of_stream _ dom (happendT ss₂ l.sss inits l.initsT) src _ ok hbody
    hinit _ ?_ hr entry closes
  intro i bools bits
  -- the recurrence functions, read off the terms, with the extension at the
  -- constant state signals: functions of the states' values
  let E : HList (tys ss₂) → HList (Tele.σs (l.at i bools bits)) → Nat → HList (tys (ss₂ ++ l.sss)) :=
    fun a xs t => evalTerms
      (fun j => (typedVal nIn (fun j => bposL.getD j 0) (fun j => vposL.getD j 0) (ss₂ ++ l.sss) ls
        bools (ext i bools bits ⟨fun _ => a⟩ (Tele.constOf (l.at i bools bits) xs)) t
        (l.fstate i bools bits a xs)).b (bposL.getD j 0))
      (fun j w => (typedVal nIn (fun j => bposL.getD j 0) (fun j => vposL.getD j 0) (ss₂ ++ l.sss) ls
        bools (ext i bools bits ⟨fun _ => a⟩ (Tele.constOf (l.at i bools bits) xs)) t
        (l.fstate i bools bits a xs)).v (vposL.getD j 0) w) nexts
  have hw : ∀ (S : Signal (dom i) (HList (tys ss₂))) (Ss : Tele.Sigs (l.at i bools bits)) (t : Nat),
      l.fstate i bools bits
        (valsAt (tys ss₂) (body i bools bits (regsOf (tys ss₂) S)
          (Tele.resultsOn (regsOf (tys ss₂) S) (l.at i bools bits) () Ss) (mkHolds (tys ss₂) S)).snd t)
        (Tele.writesAt (regsOf (tys ss₂) S) (l.at i bools bits) () Ss t) =
      E (S.val t) (Tele.valsOf (l.at i bools bits) Ss t) t := by
    intro S Ss t
    have h := writes i bools bits S Ss t
    rw [typedVal_congr _ _ _ _ _ bools (ext i bools bits S Ss)
      (ext i bools bits ⟨fun _ => S.val t⟩
        (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits) Ss t))) t _
      (fun p w => hext i bools bits S Ss t p w)] at h
    exact h
  have hG : Tools.ShippingMachineTele.OuterPointwise (l.at i bools bits) (body i bools bits)
      (fun a xs t => splitL ss₂ l.sss (E a xs t)) := by
    intro S Ss t
    show _ = splitL ss₂ l.sss (E (S.val t) (Tele.valsOf (l.at i bools bits) Ss t) t)
    rw [← hw S Ss t]
    unfold TeleT.fstate
    rw [splitL_happendT]
  have hF : TelePointwise (l.at i bools bits)
      (fun a xs t => l.unflat i bools bits (splitR ss₂ l.sss (E a xs t))) := by
    intro S Ss t
    show _ = l.unflat i bools bits (splitR ss₂ l.sss (E (S.val t) (Tele.valsOf (l.at i bools bits) Ss t) t))
    rw [← hw S Ss t]
    unfold TeleT.fstate
    rw [splitR_happendT, TeleT.unflat_flat]
  obtain ⟨h0, x0, hstep⟩ := Tools.ShippingMachineTele.fused_state inits (l.at i bools bits) (body i bools bits) _ hF
      (hI i bools bits) _ hG
  simp only at x0 hstep
  refine ⟨fun t => l.fstate i bools bits
    ((stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))).val t)
    (Tele.valsOf (l.at i bools bits) (Tele.loops (regsOf (tys ss₂)
      (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
      (l.at i bools bits) ()) t), ?_, ?_, ?_, ?_⟩
  · show TeleT.fstate i bools bits l _ _ = _
    rw [h0, x0]
    unfold TeleT.fstate
    rw [TeleT.flat_initsOf]
  · intro t
    show TeleT.fstate i bools bits l _ _ = _
    rw [(hstep t).1, (hstep t).2]
    unfold TeleT.fstate
    rw [TeleT.flat_unflat, happendT_split]
    show E _ _ t = _
    simp only [E]
    rw [typedVal_congr _ _ _ _ _ bools
      (ext i bools bits ⟨fun _ => (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))).val t⟩
        (Tele.constOf (l.at i bools bits) (Tele.valsOf (l.at i bools bits)
          (Tele.loops (regsOf (tys ss₂) (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
            (l.at i bools bits) ()) t)))
      (ext i bools bits (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits)))
        (Tele.loops (regsOf (tys ss₂) (stateLoop inits (Tools.ShippingMachineTele.fusedBody (l.at i bools bits) (body i bools bits))))
          (l.at i bools bits) ())) t _
      (fun p w => (hext i bools bits _ _ t p w).symm)]
    rfl
  · intro j
    rw [hsrc i bools bits, Tools.ShippingMachineTele.fusedBody_result]
    exact hres i bools bits _ _ j
  · intro j q g l' hg hl
    simp only [letObsT, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
    subst hg
    rfl


end Tools.ShippingMachineTeleNest
