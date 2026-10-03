import Tools.ShippingMachineFuse
import Tools.ShippingMachineAuto

/-! # The trace theorem of a `circuit do` with sub-machines

`machine_trace_of_stream` (ShippingMachineAuto) gives the trace theorem of
a machine module for any stream of states with the recurrence of the
next-value terms. For a declaration whose body contains further `circuit
do`s, the compiler flattens all of them into one machine (the enclosing
slots first, then each sub-machine's slots, in order); the stream is the
tuple of the enclosing loop and the sub-machines' loops, and its recurrence
is `fused_state` (ShippingMachineFuse) read through the flattening.

Per declaration the generator supplies: the sub-machines (`InnerT`: slot
sorts, result type, reset values, body reading the enclosing handles), the
enclosing body as a function of its handles and of the tuple of the
sub-machines' results, and four `rfl`s — the writes of all the machines on
constant states are the next-value terms (`writes`), the result on constant
states is the output terms (`hres`), the declaration is the enclosing body
on the loops (`hsrc`), and the flattened reset values are the layout's
(`hinit`). -/
namespace Tools.ShippingMachineNest
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMachineEntry Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingMachineAuto Tools.ShippingMachineFuse
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness

/-! ## Flattening typed state tuples -/

/-- The state tuple of `a ++ b` from those of `a` and `b`. -/
def happendT : (a b : List SType) → HList (tys a) → HList (tys b) → HList (tys (a ++ b))
  | [], _, _, y => y
  | _ :: a, b, x, y => (x.1, happendT a b x.2 y)

/-- The `a` part of a state tuple of `a ++ b`. -/
def splitL : (a b : List SType) → HList (tys (a ++ b)) → HList (tys a)
  | [], _, _ => ()
  | _ :: a, b, x => (x.1, splitL a b x.2)

/-- The `b` part of a state tuple of `a ++ b`. -/
def splitR : (a b : List SType) → HList (tys (a ++ b)) → HList (tys b)
  | [], _, x => x
  | _ :: a, b, x => splitR a b x.2

theorem splitL_happendT : ∀ (a b : List SType) (x : HList (tys a)) (y : HList (tys b)),
    splitL a b (happendT a b x y) = x
  | [], _, _, _ => rfl
  | _ :: a, b, x, y => by
    show (x.1, splitL a b (happendT a b x.2 y)) = x
    rw [splitL_happendT a b x.2 y]
    rfl

theorem splitR_happendT : ∀ (a b : List SType) (x : HList (tys a)) (y : HList (tys b)),
    splitR a b (happendT a b x y) = y
  | [], _, _, _ => rfl
  | _ :: a, b, x, y => splitR_happendT a b x.2 y

theorem happendT_split : ∀ (a b : List SType) (x : HList (tys (a ++ b))),
    happendT a b (splitL a b x) (splitR a b x) = x
  | [], _, _ => rfl
  | _ :: a, b, x => by
    show (x.1, happendT a b (splitL a b x.2) (splitR a b x.2)) = x
    rw [happendT_split a b x.2]
    rfl

/-! ## Sub-machines, for every domain and inputs -/

/-- A sub-machine of a declaration: its slot sorts and result type, and for
every domain and inputs its body, which reads the enclosing handles (`ss₂`
the enclosing slot sorts). -/
structure InnerT (ι : Type) (dom : ι → DomainConfig) (ss₂ : List SType) where
  ss : List SType
  ρ : ι → Type
  inh : Inhabited (HList (tys ss))
  inits : HList (tys ss)
  body : (i : ι) → (Nat → Signal (dom i) Bool) →
    ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
    RegList (dom i) (HList (tys ss₂)) (Circuit.SigList (dom i) (tys ss₂)) (tys ss₂) →
    RegList (dom i) (HList (tys ss)) (Circuit.SigList (dom i) (tys ss)) (tys ss) →
    Circuit (dom i) (Circuit.SigList (dom i) (tys ss)) (ρ i)

variable {ι : Type} {dom : ι → DomainConfig} {ss₂ : List SType}

/-- The sub-machine in one domain, for given inputs. -/
def InnerT.at (m : InnerT ι dom ss₂) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) : Inner (dom i) (tys ss₂) :=
  { βs := tys m.ss, inh := m.inh, ρ := m.ρ i, inits := m.inits, body := m.body i bools bits }

/-- The sub-machines in one domain, for given inputs. -/
def ats (l : List (InnerT ι dom ss₂)) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) : List (Inner (dom i) (tys ss₂)) :=
  l.map (·.at i bools bits)

/-- The slot sorts of the sub-machines, in order. -/
def sss (l : List (InnerT ι dom ss₂)) : List SType := (l.map (·.ss)).flatten

/-- The reset values of the sub-machines, flattened. -/
def initsT : (l : List (InnerT ι dom ss₂)) → HList (tys (sss l))
  | [] => ()
  | m :: l => happendT m.ss (sss l) m.inits (initsT l)

section
variable (i : ι) (bools : Nat → Signal (dom i) Bool)
  (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))

/-- The sub-machines' states, flattened. -/
def flat : (l : List (InnerT ι dom ss₂)) → HList (σs (ats l i bools bits)) → HList (tys (sss l))
  | [], _ => ()
  | m :: l, xs => happendT m.ss (sss l) xs.1 (flat l xs.2)

/-- The sub-machines' states from the flattened tuple. -/
def unflat : (l : List (InnerT ι dom ss₂)) → HList (tys (sss l)) → HList (σs (ats l i bools bits))
  | [], _ => ()
  | m :: l, x => (splitL m.ss (sss l) x, unflat l (splitR m.ss (sss l) x))

theorem unflat_flat : ∀ (l : List (InnerT ι dom ss₂)) (xs : HList (σs (ats l i bools bits))),
    unflat i bools bits l (flat i bools bits l xs) = xs
  | [], _ => rfl
  | m :: l, xs => by
    show (splitL m.ss (sss l) (happendT m.ss (sss l) xs.1 (flat i bools bits l xs.2)),
      unflat i bools bits l (splitR m.ss (sss l) (happendT m.ss (sss l) xs.1 (flat i bools bits l xs.2)))) = xs
    rw [splitL_happendT, splitR_happendT, unflat_flat l xs.2]
    rfl

theorem flat_unflat : ∀ (l : List (InnerT ι dom ss₂)) (x : HList (tys (sss l))),
    flat i bools bits l (unflat i bools bits l x) = x
  | [], _ => rfl
  | m :: l, x => by
    show happendT m.ss (sss l) (splitL m.ss (sss l) x)
      (flat i bools bits l (unflat i bools bits l (splitR m.ss (sss l) x))) = x
    rw [flat_unflat l, happendT_split]

theorem flat_initsOf : ∀ (l : List (InnerT ι dom ss₂)),
    flat i bools bits l (initsOf (ats l i bools bits)) = initsT l
  | [] => rfl
  | m :: l => by
    show happendT m.ss (sss l) m.inits (flat i bools bits l (initsOf (ats l i bools bits))) = _
    rw [flat_initsOf l]
    rfl

/-- The flattened state: the enclosing state, then the sub-machines'. -/
def fstate (l : List (InnerT ι dom ss₂)) (a : HList (tys ss₂))
    (xs : HList (σs (ats l i bools bits))) : HList (tys (ss₂ ++ sss l)) :=
  happendT ss₂ (sss l) a (flat i bools bits l xs)

end

/-- A state tuple along an equation of slot sorts (`rfl` for a
declaration, where both sides are one literal list). -/
def castSS {a b : List SType} (h : a = b) (x : HList (tys a)) : HList (tys b) :=
  match h with
  | rfl => x

set_option maxHeartbeats 2000000 in
/-- **Source to RTL for a `circuit do` with sub-machines, from data.** The
enclosing machine has slots `ss₂` and body `body`, which reads the tuple of
the sub-machines' results; the sub-machines are `l`; the compiler's slots
are `ss₂ ++ sss l`. With the check `ok`, the body equation, the reset check
and the three `rfl`s, the module a run of the real synthesis entry returns
shows the declaration — the enclosing body on its loop with every
sub-machine on its own loop. -/
theorem machine_trace_of_nested {declName : Name} (d : MachineData)
    (dom : ι → DomainConfig) (ss₂ : List SType) [Inhabited (HList (tys ss₂))]
    (l : List (InnerT ι dom ss₂)) (hss : ss₂ ++ sss l = d.ss) {ρ : ι → Type}
    (inits : HList (tys ss₂))
    (body : (i : ι) → (bools : Nat → Signal (dom i) Bool) →
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys ss₂)) (Circuit.SigList (dom i) (tys ss₂)) (tys ss₂) →
      HList (ρs (ats l i bools bits)) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys ss₂)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk (castSS hss (happendT ss₂ (sss l) inits (initsT l))) = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Sigs (ats l i bools bits)) (t : Nat),
      castSS hss (fstate i bools bits l
        (valsAt (tys ss₂) (body i bools bits (regsOf (tys ss₂) S)
          (resultsOn (regsOf (tys ss₂) S) (ats l i bools bits) Ss) (mkHolds (tys ss₂) S)).snd t)
        (innerValsAt (ats l i bools bits)
          (innerWrites (regsOf (tys ss₂) S) (ats l i bools bits) Ss) t)) =
      evalTerms
        (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t
          (castSS hss (fstate i bools bits l (S.val t) (valsOf (ats l i bools bits) Ss t)))).b
          (d.bpos j))
        (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t
          (castSS hss (fstate i bools bits l (S.val t) (valsOf (ats l i bools bits) Ss t)))).v
          (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys ss₂))) (Ss : Sigs (ats l i bools bits)) (t : Nat),
      (obsR i (body i bools bits (regsOf (tys ss₂) S)
          (resultsOn (regsOf (tys ss₂) S) (ats l i bools bits) Ss) (mkHolds (tys ss₂) S)).fst).map
          (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t
            (castSS hss (fstate i bools bits l (S.val t) (valsOf (ats l i bools bits) Ss t)))).b
            (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t
            (castSS hss (fstate i bools bits l (S.val t) (valsOf (ats l i bools bits) Ss t)))).v
            (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i (resOn (fusedBody (ats l i bools bits) (body i bools bits))
        (stateLoop inits (fusedBody (ats l i bools bits) (body i bools bits)))))
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape) :
    MachineTrace declName d m dom src := by
  obtain ⟨shape, nIn, domE, bposL, vposL, vwL, ss, ls, outs, nexts⟩ := d
  simp only at hss
  subst hss
  refine machine_trace_of_stream _ dom (happendT ss₂ (sss l) inits (initsT l)) src ok hbody
    hinit ?_ hr entry closes
  intro i bools bits
  -- the recurrence functions, read off the terms
  let E : HList (tys ss₂) → HList (σs (ats l i bools bits)) → Nat → HList (tys (ss₂ ++ sss l)) :=
    fun a xs t => evalTerms
      (fun j => (typedVal nIn (fun j => bposL.getD j 0) (fun j => vposL.getD j 0) (ss₂ ++ sss l) ls
        bools bits t (fstate i bools bits l a xs)).b (bposL.getD j 0))
      (fun j w => (typedVal nIn (fun j => bposL.getD j 0) (fun j => vposL.getD j 0) (ss₂ ++ sss l) ls
        bools bits t (fstate i bools bits l a xs)).v (vposL.getD j 0) w) nexts
  have hw : ∀ (S : Signal (dom i) (HList (tys ss₂))) (Ss : Sigs (ats l i bools bits)) (t : Nat),
      fstate i bools bits l
        (valsAt (tys ss₂) (body i bools bits (regsOf (tys ss₂) S)
          (resultsOn (regsOf (tys ss₂) S) (ats l i bools bits) Ss) (mkHolds (tys ss₂) S)).snd t)
        (innerValsAt (ats l i bools bits)
          (innerWrites (regsOf (tys ss₂) S) (ats l i bools bits) Ss) t) =
      E (S.val t) (valsOf (ats l i bools bits) Ss t) t :=
    fun S Ss t => writes i bools bits S Ss t
  have hG : OuterPointwise (ats l i bools bits) (body i bools bits)
      (fun a xs t => splitL ss₂ (sss l) (E a xs t)) := by
    intro S Ss t
    show _ = splitL ss₂ (sss l) (E (S.val t) (valsOf (ats l i bools bits) Ss t) t)
    rw [← hw S Ss t]
    unfold fstate
    rw [splitL_happendT]
  have hF : InnerPointwise (ats l i bools bits)
      (fun a xs t => unflat i bools bits l (splitR ss₂ (sss l) (E a xs t))) := by
    intro S Ss t
    show _ = unflat i bools bits l (splitR ss₂ (sss l) (E (S.val t) (valsOf (ats l i bools bits) Ss t) t))
    rw [← hw S Ss t]
    unfold fstate
    rw [splitR_happendT, unflat_flat]
  obtain ⟨h0, x0, hstep⟩ := fused_state inits (ats l i bools bits) (body i bools bits) _ hF _ hG
  simp only at x0 hstep
  refine ⟨fun t => fstate i bools bits l
    ((stateLoop inits (fusedBody (ats l i bools bits) (body i bools bits))).val t)
    (valsOf (ats l i bools bits) (innerLoops (regsOf (tys ss₂)
      (stateLoop inits (fusedBody (ats l i bools bits) (body i bools bits))))
      (ats l i bools bits)) t), ?_, ?_, ?_⟩
  · show fstate i bools bits l _ _ = _
    rw [h0, x0]
    unfold fstate
    rw [flat_initsOf]
  · intro t
    show fstate i bools bits l _ _ = _
    rw [(hstep t).1, (hstep t).2]
    unfold fstate
    rw [flat_unflat, happendT_split]
    rfl
  · intro j
    rw [hsrc i bools bits, fusedBody_result]
    exact hres i bools bits _ _ j

end Tools.ShippingMachineNest
