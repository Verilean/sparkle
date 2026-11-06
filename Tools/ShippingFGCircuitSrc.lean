import Tools.ShippingFGCircuitApply
import Tools.ShippingFGCircuitCover
set_option autoImplicit false
-- FG circuit pilot S1e, unit 1: `hsrc` for counterLoop (D.D-3 for this root). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `hsrc` for `counterLoop`: the generated state loop and the declaration's `Signal.loop` agree

`p.src` of the package `genGP` returns is, for a register leaf with no instances, `(genSemGenE X g eb ev).src`: the result term applied to `stateLoop g.inits (refBodyE …)`, with `eb`/`ev` the identity extensions (`insts = []`).
The declaration's observation is `counterLoop.machineSource`, which the endpoint command proves (`counterLoop.machine_source`, `machine_result`, `machine_writes`, kernel `Eq.refl`) to be the result term applied to `Signal.loop counterLoop.machineBody`.
Both are the SAME terms (`machineData.nexts`, `.outs`) evaluated on the state of a loop; we show by induction on the cycle that the two loops' states correspond under `machineSigma` (`x ↦ (x, ())`), from the cycle-0 values (`initsOf machineData = machineInits`, `rfl`)
and the one-step recurrences (`loop_state`, `machine_writes`). Then the two result lists agree at every cycle, hence are equal. -/
namespace Tools.ShippingFGCircuitSrc
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5Sem Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Sparkle.Tests.SignalLoopTest
open Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG

theorem list_ext_of_map_eval : ∀ {L L' : List (Nat → Nat)},
    (∀ t, L.map (fun f => f t) = L'.map (fun f => f t)) → L = L'
  | [], [], _ => rfl
  | [], b :: l', h => by have := h 0; simp at this
  | a :: l, [], h => by have := h 0; simp at this
  | a :: l, b :: l', h => by
    have h0 : ∀ t, a t = b t ∧ l.map (fun f => f t) = l'.map (fun f => f t) := fun t => by
      have := h t
      simpa only [List.map_cons, List.cons.injEq] using this
    have hab : a = b := funext fun t => (h0 t).1
    have hl : l = l' := list_ext_of_map_eval fun t => (h0 t).2
    rw [hab, hl]

/-- the loop of `counterLoop` (BitVec 8 signal) at cycle 0 and its recurrence -/
theorem counterLoop_loop_zero (bools : Nat → Signal defaultDomain Bool)
    (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) :
    (Signal.loop (counterLoop.machineBody () bools bits)).val 0 = 0#8 := by
  show Signal.loopGo _ 0 = _
  rw [Signal.loopGo_eq]
  rfl

theorem counterLoop_loop_succ (bools : Nat → Signal defaultDomain Bool)
    (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) (t : Nat) :
    (Signal.loop (counterLoop.machineBody () bools bits)).val (t + 1) =
      (Signal.loop (counterLoop.machineBody () bools bits)).val t + 1#8 := by
  show Signal.loopGo _ (t + 1) = Signal.loopGo _ t + 1#8
  rw [Signal.loopGo_eq]
  show (if t < t + 1 then Signal.loopGo _ t else default) + 1#8 = _
  rw [if_pos (by omega)]

theorem counterLoop_src_eq {ι : Type} (Q : Name → Option (SemPkg ι (fun _ => defaultDomain))) (X : Name) (gi : GenIn)
    (hd : gi.d = counterLoop.machineData) (hin : HEq gi.inits counterLoop.machineInits) (i : ι)
    (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) :
    (genSemGen (dom := fun _ => defaultDomain) Q X gi).src i bools bits = counterLoop.machineSource () bools bits := by
  obtain ⟨d, wf, inits, ok, bodyEq, init⟩ := gi
  simp only at hd hin
  subst hd
  have hin' : inits = counterLoop.machineInits := eq_of_heq hin
  subst hin'
  have hI : counterLoop.machineData.shape.insts = [] := Tools.ShippingFGCircuitApply.counterLoop_leafFacts.2.2.2.2.1
  have hlen : counterLoop.machineData.shape.insts.length = 0 := by rw [hI]; rfl
  let gi : GenIn := ⟨counterLoop.machineData, wf, counterLoop.machineInits, ok, bodyEq, init⟩
  have heb : ∀ S, extBOf (dom := fun _ => defaultDomain) Q gi i bools bits S = bools := fun S => by
    show (ExtStage (dom := fun _ => defaultDomain) Q gi i bools bits S gi.d.shape.insts.length).1 = bools
    rw [show gi.d.shape.insts.length = 0 from hlen]; rfl
  have hev : ∀ S, extOf (dom := fun _ => defaultDomain) Q gi i bools bits S = bits := fun S => by
    show (ExtStage (dom := fun _ => defaultDomain) Q gi i bools bits S gi.d.shape.insts.length).2 = bits
    rw [show gi.d.shape.insts.length = 0 from hlen]; rfl
  let eb := extBOf (dom := fun _ => defaultDomain) Q gi
  let ev := extOf (dom := fun _ => defaultDomain) Q gi
  let R := Signal.loop (counterLoop.machineBody () bools bits)
  let Sl : Signal defaultDomain (HList (tys counterLoop.machineData.ss)) :=
    @stateLoop defaultDomain _ _ ⟨counterLoop.machineInits⟩ counterLoop.machineInits (refBodyE gi eb ev i bools bits)
  have hW : ∀ (l l' : Signal defaultDomain (HList (tys counterLoop.machineData.ss))) (t : Nat), l.val t = l'.val t →
      valsAt (tys counterLoop.machineData.ss)
        (refBodyE gi eb ev i bools bits (mkRegList l (tys counterLoop.machineData.ss) (fun s => s) (fun f => f))
          (mkHolds (tys counterLoop.machineData.ss) l)).snd t =
      valsAt (tys counterLoop.machineData.ss)
        (refBodyE gi eb ev i bools bits (mkRegList l' (tys counterLoop.machineData.ss) (fun s => s) (fun f => f))
          (mkHolds (tys counterLoop.machineData.ss) l')).snd t := by
    intro l l' t h
    rw [genSemGenE_writes X gi eb ev i bools bits l t, genSemGenE_writes X gi eb ev i bools bits l' t]
    simp only [eb, ev, heb, hev, h]
  letI : Inhabited (HList (tys counterLoop.machineData.ss)) := ⟨counterLoop.machineInits⟩
  obtain ⟨hS0, hSs⟩ := loop_state (dom := defaultDomain) (tys counterLoop.machineData.ss)
    counterLoop.machineInits
    (fun live => (refBodyE gi eb ev i bools bits (mkRegList live (tys counterLoop.machineData.ss) (fun s => s) (fun f => f))
          (mkHolds (tys counterLoop.machineData.ss) live)).snd) hW
  have key : ∀ t, Sl.val t = counterLoop.machineSigma () (R.val t) := by
    intro t
    induction t with
    | zero => rw [counterLoop_loop_zero]; exact hS0
    | succ t ih =>
      have e1 : Sl.val (t + 1) = valsAt (tys counterLoop.machineData.ss)
          (refBodyE gi eb ev i bools bits (mkRegList Sl (tys counterLoop.machineData.ss) (fun s => s) (fun f => f))
            (mkHolds (tys counterLoop.machineData.ss) Sl)).snd t := hSs t
      rw [e1, genSemGenE_writes X gi eb ev i bools bits Sl t]
      simp only [eb, ev, heb, hev]
      show _ = counterLoop.machineSigma () (R.val (t + 1))
      rw [counterLoop_loop_succ]
      have hw := counterLoop.machine_writes () bools bits R t
      rw [ih]
      exact hw.symm
  apply list_ext_of_map_eval
  intro t
  show (refBodyE gi eb ev i bools bits (mkRegList Sl (tys counterLoop.machineData.ss) (fun s => s) (fun f => f))
      (mkHolds (tys counterLoop.machineData.ss) Sl)).fst.map (fun f => f t) = _
  rw [genSemGenE_result X gi eb ev i bools bits Sl t, counterLoop.machine_source () bools bits]
  have hr := counterLoop.machine_result () bools bits R t
  rw [hr, key t]
  simp only [eb, ev, heb, hev]
  rfl


/-! ## from the package `genGP` returns to the generated source semantics

The package's `src` is the `src` of the semantics the kit assigns to the table row (`genP_some_inv`, `src_toSem`), which is `genSemI (genS K) X (g.toIn hs)` (`GenData.genSem`, definitional). -/
section
open Tools.ShippingGen5Acc Tools.ShippingGen5DataOf Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1 Sparkle.Compiler.Elab
open Tools.ShippingMachineAuto (MachineData)

theorem genGP_root_src {ι : Type} {dom : ι → DomainConfig} (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (dataOfAt lvl) initsOf)
    (genData₀ : (env : Environment) → (E : ConstantInfo) → Option (GenData (dataOfAt lvl) E (structEnv env)))
    (env : Environment) {X : Name} {E : ConstantInfo} {g : GenData (dataOfAt lvl) E (structEnv env)}
    (hE : entry₀ env X = some E) (hg : genData₀ env E = some g) (hleaf : g.d.shape.insts = []) :
    ∃ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl hs genData₀ env X = some p ∧ p.d = g.d ∧
      ∃ Q, p.src = (genSemI Q X (g.toIn hs)).src := by
  let K := genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env)
  have hgK : K.genData₀ E = some g := hg
  have hd0 : dataOf₀ K X = some g.d := dataOf₀_of_genData₀ K hE hgK
  have hacc : Acc (CallRel K) X := by
    refine Acc.intro X fun y hy => ?_
    obtain ⟨d, hd, k, hk, -, -⟩ := hy
    rw [hd0] at hd
    have hd' : d = g.d := (Option.some.inj hd).symm
    subst hd'
    rw [hleaf] at hk
    exact absurd hk (by simp)
  have hunf := genS_unfold K hacc hE hgK
  have hall : ∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome := by
    intro k _
    have hlen : (K.dOf g).shape.insts.length = 0 := by
      show g.d.shape.insts.length = 0
      rw [hleaf]; rfl
    have := k.2
    omega
  rw [if_pos hall] at hunf
  have hF := factsOf_genS_assembled'' (ι := ι) (dom := dom) hs (genData₀ env)
  have hP := genP_eq_some K hF hunf
  have hpp : genGP (ι := ι) (dom := dom) lvl hs genData₀ env X = some _ := hP
  refine ⟨_, hpp, ?_, genS K, ?_⟩
  · obtain ⟨d', hd', hpd⟩ := genP_d_edges K hF hP
    rw [hd0] at hd'
    rw [hpd, ← Option.some.inj hd']
  · obtain ⟨s, hs', hps⟩ := genP_some_inv K hF hP
    rw [hunf] at hs'
    have hs'' : s = K.genSem (genS K) X g := (Option.some.inj hs').symm
    rw [← src_toSem, hps, hs'']
    rfl

theorem genGP_root_canon_src {ι : Type} {dom : ι → DomainConfig} (lvl : Lean.Expr → Nat) (env : Environment) {X : Name}
    {d : MachineData} (hR : Tools.ShippingFGCircuitCover.RootReader lvl env X d) (hwf : GenWF d = true) (hleaf : d.shape.insts = []) :
    ∃ (p : Pkg ι dom) (g : GenIn), genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) (Tools.ShippingFGCircuitCover.canonGD lvl) env X = some p ∧
      p.d = d ∧ g.d = d ∧ g.inits = Tools.ShippingGen5DataOfPure.initsOf g.d ∧ ∃ Q, p.src = (genSemI Q X g).src := by
  obtain ⟨E, hE, hsh, hdat⟩ := hR
  obtain ⟨g, hg, hgd⟩ := Tools.ShippingFGCircuitCover.canon_row (lvl := lvl) (env := env) hwf hsh hdat
  have hleaf' : g.d.shape.insts = [] := by rw [hgd]; exact hleaf
  obtain ⟨p, hp, hpd, Q, hsrc⟩ := genGP_root_src (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) (Tools.ShippingFGCircuitCover.canonGD lvl) env hE hg hleaf'
  exact ⟨p, g.toIn (dataOfSound_initsOf lvl), hp, hpd.trans hgd, hgd, rfl, Q, hsrc⟩

end

/-- **`hsrc` for `counterLoop`**: any package `genGP` returns for it (the table's row being the reader's data) observes the declaration itself. -/
theorem counterLoop_hsrc {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment)
    (hRead : Tools.ShippingFGCircuitCover.RootReader lvl env ``counterLoop counterLoop.machineData) :
    ∃ p : Pkg ι (fun _ => defaultDomain),
      Tools.ShippingGenFGLedgerPremises.genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl)
        (Tools.ShippingFGCircuitCover.canonGD lvl) env ``counterLoop = some p ∧
      ∀ (i : ι) bools bits, p.src i bools bits = Tools.ShippingFGCircuit.monoObs Tools.ShippingFGCircuitRoots.shCounter counterLoop bools bits := by
  obtain ⟨p, gi, hp, hpd, hgd, hgi, Q, hsrc⟩ := genGP_root_canon_src (ι := ι) (dom := fun _ => defaultDomain) lvl env hRead
    Tools.ShippingFGCircuitApply.counterLoop_wf Tools.ShippingFGCircuitApply.counterLoop_leafFacts.2.2.2.2.1
  refine ⟨p, hp, fun i bools bits => ?_⟩
  have hns : (gi.d.ss.isEmpty && gi.d.shape.insts.isEmpty) = false := by rw [hgd]; decide
  have hin : HEq gi.inits counterLoop.machineInits := by
    rw [hgi]
    have : ∀ d : Tools.ShippingMachineAuto.MachineData, d = counterLoop.machineData →
        HEq (Tools.ShippingGen5DataOfPure.initsOf d) counterLoop.machineInits := by
      rintro d rfl; exact heq_of_eq rfl
    exact this _ hgd
  have e : (genSemI Q ``counterLoop gi).src i bools bits = (genSemGen (dom := fun _ => defaultDomain) Q ``counterLoop gi).src i bools bits := by
    unfold genSemI; rw [hns]; rfl
  rw [hsrc, e, counterLoop_src_eq Q _ gi hgd hin i bools bits]
  rfl

end Tools.ShippingFGCircuitSrc

#print axioms Tools.ShippingFGCircuitSrc.counterLoop_src_eq
#print axioms Tools.ShippingFGCircuitSrc.counterLoop_hsrc
