import Tools.ShippingFGCircuitS1kPkg
import Tools.ShippingGen5SemExtPkg
import Tools.ShippingGen5SemSrcCausal
import Tools.ShippingFGCircuitRoots4
import Tools.ShippingMachineFuse
import Tools.ShippingFGCircuitS1tFinal
set_option autoImplicit false
-- FG circuit pilot S1u: `hsrc` for the non-leaf root `synth_hftPcieOutByte`. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §25.

/-! # S1u (part A): the generic `ExtStage` induction for a finite list of callees

`ExtStage Q g i bools bits S k` runs the first `k` calls of `g.d` over the callee table `Q`. `calleeOut` reads a callee package only through `q.d`, `q.kD` and `q.src`. So two tables that agree on those three
fields at every callee name give the same `ExtStage` at every stage (`ExtStage_agree_tables`, an induction on the stage). The package that `genGP` returns for the callee can therefore be replaced by the
callee's declaration-level observation, once the callee's own `src` is known. -/
namespace Tools.ShippingFGCircuitS1uSrc
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineSource
open Tools.ShippingGen5Sem Tools.ShippingGen2
open Tools.ShippingUnifiedSource (eval)

section Generic
variable {ι : Type} {dom : ι → DomainConfig}

/-- two callee packages agree on everything `calleeOut` reads -/
def CalleeAgree (q q' : SemPkg ι dom) : Prop := q.d = q'.d ∧ q.kD = q'.kD ∧ q.src = q'.src

/-- two callee tables agree at the name `c`, up to `CalleeAgree` -/
def AgreeAt (Q Q' : Name → Option (SemPkg ι dom)) (c : Name) : Prop :=
  (Q c = none ∧ Q' c = none) ∨ ∃ q q', Q c = some q ∧ Q' c = some q' ∧ CalleeAgree q q'

/-- two callee tables agree at every callee name of the machine `d` (the only names `ExtStage` reads) -/
def TablesAgree (Q Q' : Name → Option (SemPkg ι dom)) (d : MachineData) : Prop :=
  ∀ (k : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder), d.shape.insts[k]? = some (c, a, κ) → AgreeAt Q Q' c

theorem calleeOut_agree_tables (Q Q' : Name → Option (SemPkg ι dom)) (g : GenIn) (hQ : TablesAgree Q Q' g.d) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat) :
    calleeOut Q g i S bs vs k = calleeOut Q' g i S bs vs k := by
  unfold calleeOut
  cases hk : g.d.shape.insts[k]? with
  | none => rfl
  | some e =>
    obtain ⟨c, a, κ⟩ := e
    dsimp only
    rcases hQ k c a κ hk with ⟨h1, h2⟩ | ⟨q, q', h1, h2, hd, hkd, hs⟩
    · rw [h1, h2]
    · rw [h1, h2]
      dsimp only
      have hsel : selIdx g.d q k = selIdx g.d q' k := by
        unfold selIdx; rw [hd]
      rw [hsel, hd, hkd, hs]

theorem callOut_agree_tables (Q Q' : Name → Option (SemPkg ι dom)) (g : GenIn) (hQ : TablesAgree Q Q' g.d) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n))) :
    callOut Q g i S k st = callOut Q' g i S k st := by
  unfold callOut
  simp only [calleeOut_agree_tables Q Q' g hQ i S]

/-- **the `ExtStage` induction** (generic in the callee list): the stages over two agreeing tables are equal -/
theorem ExtStage_agree_tables (Q Q' : Name → Option (SemPkg ι dom)) (g : GenIn) (hQ : TablesAgree Q Q' g.d) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (n : Nat) :
    ExtStage Q g i bools bits S n = ExtStage Q' g i bools bits S n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ExtStage_succ, ExtStage_succ, ih, callOut_agree_tables Q Q' g hQ]

theorem genSemGen_agree_tables (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hQ : TablesAgree Q Q' g.d) :
    genSemGen Q X g = genSemGen Q' X g := by
  have hb : extBOf Q g = extBOf Q' g := by
    funext i bools bits S; unfold extBOf; rw [ExtStage_agree_tables Q Q' g hQ]
  have hv : extOf Q g = extOf Q' g := by
    funext i bools bits S; unfold extOf; rw [ExtStage_agree_tables Q Q' g hQ]
  unfold genSemGen; rw [hb, hv]

end Generic

/-! # S1u (part B): the generated source of a package with calls, from a link to the declaration

`src_eq_of_states` (the leaf case) has `ExtStage … 0 = id`, so the loop body does not read the state through the call streams. With calls the body's writes at `t` read the callee streams at `t`, which read the state at the cycles `≤ t`: the loop
recurrence is `loop_state_causal`, and the causality of the call streams is `extCausal_of_genSem` (from `CalleesCausal`). The link `hlink` is what the declaration side must supply: every state signal that starts at `inits` and follows the generated
recurrence over the generated call streams has the declaration's observation at the outputs. -/
section Rec
variable {ι : Type} {dom : ι → DomainConfig}
open Tools.ShippingFGCircuitSrc (list_ext_of_map_eval)

theorem genSemGen_src_eq_of_link (Q : Name → Option (SemPkg ι dom)) (X : Name) (g : GenIn) (hQ : CalleesCausal Q g.d) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n)) (obs : List (Nat → Nat))
    (hlink : ∀ S : Signal (dom i) (HList (tys g.d.ss)), S.val 0 = g.inits →
      (∀ t, S.val (t + 1) = evalTerms
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (extBOf Q g i bools bits S) (extOf Q g i bools bits S) t (S.val t)).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (extBOf Q g i bools bits S) (extOf Q g i bools bits S) t (S.val t)).v (g.d.vpos j) w) g.d.nexts) →
      ∀ t, obs.map (fun f => f t) = g.d.outs.map fun o => enc o.1 (eval
        (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (extBOf Q g i bools bits S) (extOf Q g i bools bits S) t (S.val t)).b (g.d.bpos j))
        (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (extBOf Q g i bools bits S) (extOf Q g i bools bits S) t (S.val t)).v (g.d.vpos j) w) o.2)) :
    (genSemGen Q X g).src i bools bits = obs := by
  letI : Inhabited (HList (tys g.d.ss)) := ⟨g.inits⟩
  let eb := extBOf Q g
  let ev := extOf Q g
  let Sl : Signal (dom i) (HList (tys g.d.ss)) :=
    @stateLoop (dom i) _ _ ⟨g.inits⟩ g.inits (refBodyE g eb ev i bools bits)
  have hW : ∀ (l l' : Signal (dom i) (HList (tys g.d.ss))) (t : Nat), (∀ c, c ≤ t → l.val c = l'.val c) →
      valsAt (tys g.d.ss)
        (refBodyE g eb ev i bools bits (mkRegList l (tys g.d.ss) (fun s => s) (fun f => f)) (mkHolds (tys g.d.ss) l)).snd t =
      valsAt (tys g.d.ss)
        (refBodyE g eb ev i bools bits (mkRegList l' (tys g.d.ss) (fun s => s) (fun f => f)) (mkHolds (tys g.d.ss) l')).snd t := by
    intro l l' t h
    rw [genSemGenE_writes X g eb ev i bools bits l t, genSemGenE_writes X g eb ev i bools bits l' t]
    obtain ⟨hv, hb⟩ := extCausal_of_genSem Q g hQ i bools bits l l' t h
    have key := Tools.ShippingMachineCausal.typedVal_congrB g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits l) (eb i bools bits l')
      (ev i bools bits l) (ev i bools bits l') t (l.val t) hb hv
    rw [key, h t (Nat.le_refl t)]
  obtain ⟨hS0, hSs⟩ := Tools.ShippingMachineFuse.loop_state_causal (dom := dom i) (tys g.d.ss) g.inits
    (fun live => (refBodyE g eb ev i bools bits (mkRegList live (tys g.d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys g.d.ss) live)).snd) hW
  have hrec : ∀ t, Sl.val (t + 1) = evalTerms
      (fun j => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits Sl) (ev i bools bits Sl) t (Sl.val t)).b (g.d.bpos j))
      (fun j w => (typedVal g.d.nIn g.d.bpos g.d.vpos g.d.ss g.d.ls (eb i bools bits Sl) (ev i bools bits Sl) t (Sl.val t)).v (g.d.vpos j) w) g.d.nexts := by
    intro t
    exact (hSs t).trans (genSemGenE_writes X g eb ev i bools bits Sl t)
  apply list_ext_of_map_eval
  intro t
  show (refBodyE g eb ev i bools bits (mkRegList Sl (tys g.d.ss) (fun s => s) (fun f => f))
      (mkHolds (tys g.d.ss) Sl)).fst.map (fun f => f t) = _
  rw [genSemGenE_result X g eb ev i bools bits Sl t]
  exact (hlink Sl hS0 hrec t).symm

end Rec

/-! # S1u (part C): the table side — the package `genGP` returns for a root whose callees are leaf rows, as `genSemI` over the table, and a combinational leaf's source -/
section Table
open Tools.ShippingGen5Acc Tools.ShippingGen5DataOf Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1 Tools.ShippingFGCircuitCover
open Tools.ShippingFGCircuitSrc (list_ext_of_map_eval)
variable {ι : Type} {dom : ι → DomainConfig}

/-- **a combinational leaf's `src`** (`ss = []`, `insts = []`): the generated source is the declaration's observation, from the endpoint's `machine_result` at the (unique) empty state -/
theorem genSemI_comb_src (Q : Name → Option (SemPkg ι dom)) (X : Name) (gi : GenIn) {d : MachineData} (hgd : gi.d = d)
    (hss : d.ss = []) (hin : d.shape.insts = [])
    (obs : (i : ι) → (Nat → Signal (dom i) Bool) → ((j n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n)) (t : Nat) (x : HList (tys d.ss)),
      (obs i bools bits).map (fun f => f t) = d.outs.map fun o => enc o.1 (eval
        (fun k => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).b (d.bpos k))
        (fun k w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools bits t x).v (d.vpos k) w) o.2)) :
    (genSemI Q X gi).src = obs := by
  subst hgd
  have hc : (gi.d.ss.isEmpty && gi.d.shape.insts.isEmpty) = true := by simp [hss, hin]
  unfold genSemI
  rw [if_pos hc]
  funext i bools bits
  apply list_ext_of_map_eval
  intro t
  show (gi.d.outs.map fun o t => enc o.1 (eval _ _ o.2)).map (fun f => f t) = _
  rw [hres i bools bits t gi.inits]
  simp only [List.map_map, Function.comp_def]

/-- a leaf row of the table: `genS` returns the kit's `genSem` over the table itself (the equation behind `genS_leaf_isSome`) -/
theorem genS_leaf_eq (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (dataOfAt lvl) initsOf)
    (genData₀ : (env : Environment) → (E : ConstantInfo) → Option (GenData (dataOfAt lvl) E (structEnv env)))
    (env : Environment) {c : Name} {E : ConstantInfo} {g : GenData (dataOfAt lvl) E (structEnv env)}
    (hE : entry₀ env c = some E) (hg : genData₀ env E = some g) (hleaf : g.d.shape.insts = []) :
    genS (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env)) c =
      some (genSemI (genS (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env))) c (g.toIn hs)) := by
  let K := genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env)
  have hgK : K.genData₀ E = some g := hg
  have hd0 : dataOf₀ K c = some g.d := dataOf₀_of_genData₀ K hE hgK
  have hacc : Acc (CallRel K) c := by
    refine Acc.intro c fun y hy => ?_
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
  exact hunf

/-- `genGP_root_kids` with the package's `src` as `genSemI` over the table and the callees' rows as `genSemI` over the same table -/
theorem genGP_root_kids_src (lvl : Lean.Expr → Nat) {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound (dataOfAt lvl) initsOf)
    (genData₀ : (env : Environment) → (E : ConstantInfo) → Option (GenData (dataOfAt lvl) E (structEnv env)))
    (env : Environment) {X : Name} {E : ConstantInfo} {g : GenData (dataOfAt lvl) E (structEnv env)}
    (hE : entry₀ env X = some E) (hg : genData₀ env E = some g)
    (hkids : ∀ c ∈ g.d.shape.insts.map (·.1), ∃ (Ec : ConstantInfo) (gc : GenData (dataOfAt lvl) Ec (structEnv env)),
      entry₀ env c = some Ec ∧ genData₀ env Ec = some gc ∧ gc.d.shape.insts = []) :
    ∃ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl hs genData₀ env X = some p ∧ p.decl = X ∧ p.d = g.d ∧ p.kD = kDOf g.d ∧
      p.src = (genSemI (genS (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env))) X (g.toIn hs)).src ∧
      ∀ c ∈ g.d.shape.insts.map (·.1), ∃ (Ec : ConstantInfo) (gc : GenData (dataOfAt lvl) Ec (structEnv env)),
        entry₀ env c = some Ec ∧ genData₀ env Ec = some gc ∧ gc.d.shape.insts = [] ∧
        genS (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env)) c =
          some (genSemI (genS (genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env))) c (gc.toIn hs)) := by
  obtain ⟨p, hP, hdecl, hpd, hkp⟩ := Tools.ShippingFGCircuitS1kPkg.genGP_root_kids (ι := ι) (dom := dom) lvl hs genData₀ env hE hg hkids
  refine ⟨p, hP, hdecl, hpd, hkp, ?_, ?_⟩
  · let K := genKit (ι := ι) (dom := dom) lvl hs env (genData₀ env)
    have hgK : K.genData₀ E = some g := hg
    have hd0 : dataOf₀ K X = some g.d := dataOf₀_of_genData₀ K hE hgK
    have hleafK : ∀ k : Fin g.d.shape.insts.length,
        Acc (CallRel K) (g.d.shape.insts[k]).1 ∧ (genS K (g.d.shape.insts[k]).1).isSome := by
      intro k
      obtain ⟨Ec, gc, hEc, hgc, hl⟩ := hkids _ (List.mem_map.2 ⟨g.d.shape.insts[k], List.getElem_mem k.2, rfl⟩)
      exact Tools.ShippingFGCircuitS1kPkg.genS_leaf_isSome (ι := ι) (dom := dom) lvl hs genData₀ env hEc hgc hl
    have hacc : Acc (CallRel K) X := by
      refine Acc.intro X fun y hy => ?_
      obtain ⟨d, hd, k, hk, -, hy⟩ := hy
      rw [hd0] at hd
      have hd' : d = g.d := (Option.some.inj hd).symm
      subst hd'
      subst hy
      exact (hleafK ⟨k, hk⟩).1
    have hunf := genS_unfold K hacc hE hgK
    have hall : ∀ k ∈ K.ordCallees (K.dOf g), (genS K ((K.dOf g).shape.insts[k]).1).isSome := by
      intro k _
      exact (hleafK k).2
    rw [if_pos hall] at hunf
    have hF := factsOf_genS_assembled'' (ι := ι) (dom := dom) hs (genData₀ env)
    have hP' := genP_eq_some K hF hunf
    have hpp : genGP (ι := ι) (dom := dom) lvl hs genData₀ env X = some _ := hP'
    have hpe : p = _ := Option.some.inj (hP.symm.trans hpp)
    subst hpe
    obtain ⟨s, hs', hps⟩ := genP_some_inv K hF hP'
    rw [hunf] at hs'
    have hs'' : s = K.genSem (genS K) X g := (Option.some.inj hs').symm
    rw [← src_toSem, hps, hs'']
    rfl
  · intro c hc
    obtain ⟨Ec, gc, hEc, hgc, hl⟩ := hkids c hc
    exact ⟨Ec, gc, hEc, hgc, hl, genS_leaf_eq (ι := ι) (dom := dom) lvl hs genData₀ env hEc hgc hl⟩

end Table


/-! # S1u (part D): the non-leaf root `synth_hftPcieOutByte`

**The statement** (docs §25.1). `HftObSrc` is unchanged (S1k). It is split into
* the children's `src` (PROVED here, no hypothesis): `genSemI_comb_src` at the two combinational leaf rows, from the endpoints' `machine_result` (`hftKids` is the table of the children's declaration-level observations `machineSource`),
* the `ExtStage` induction (PROVED: `ExtStage_agree_tables`): the generated call streams over the table `genS K` are those over `hftKids`,
* the root's own run-independent fact `HftRootLink` (NAMED HYPOTHESIS, FG D.D-3 / DG-SEM): a state sequence that starts at the data's inits and follows the data's recurrence over the call streams of `hftKids` has the root declaration's observation at its outputs. -/
section Hft
open Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuit (monoObs)
open Tools.ShippingFGCircuitCover Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1 Tools.ShippingGen5Acc Tools.ShippingGen5DataOf
open Tools.ShippingGen5Sem (kDOf GenWF)

/-- a combinational callee's package, at the declaration level: its data and its observation -/
noncomputable def kidSem {ι : Type} (decl : Name) (d : MachineData)
    (src : (i : ι) → (Nat → Signal defaultDomain Bool) → ((j n : Nat) → Signal defaultDomain (BitVec n)) → List (Nat → Nat)) :
    SemPkg ι (fun _ => defaultDomain) :=
  .comb ⟨decl, d, kDOf d, Tools.ShippingGen5DataOfPure.initsOf d, src⟩

/-- the callee table of the root's two children `httpGetByte`, `tlpCplByte`: each child is its declaration's observation (`machineSource` at the default domain). Static, two entries. -/
noncomputable def hftKids {ι : Type} : Name → Option (SemPkg ι (fun _ => defaultDomain)) := fun c =>
  if c = hftHttp then some (kidSem hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData
      (fun _ bools bits => Sparkle.IP.Net.HTTP.httpGetByte.machineSource defaultDomain bools bits))
  else if c = hftTlp then some (kidSem hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData
      (fun _ bools bits => Sparkle.IP.Bus.PCIe.tlpCplByte.machineSource defaultDomain bools bits))
  else none

/-- **`HftRootLink`** (NAMED HYPOTHESIS; FG D.D-3 / DG-SEM, the non-leaf root's own `hsrc` fact, run-independent): for every `GenIn` over the root's data, every inputs and every state sequence that starts at the generated inits and follows the
generated recurrence over the call streams `ExtStage hftKids` of the children's declaration-level observations, the root declaration's observation `monoObs shHft synth_hftPcieOutByte` is the data's outputs evaluated on that sequence. -/
def HftRootLink : Prop :=
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

theorem hftTlp_ne_http : hftTlp ≠ hftHttp := by decide
theorem root_insts_nonempty : synth_hftPcieOutByte.machineData.shape.insts.isEmpty = false := by decide +kernel
theorem http_ss : Sparkle.IP.Net.HTTP.httpGetByte.machineData.ss = [] := by decide +kernel
theorem tlp_ss : Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.ss = [] := by decide +kernel

/-- **`hsrc` of the non-leaf root, from the root link**: with the readers of the root and of the two children at the table's environment, every package `genGP` returns for the root observes the declaration, given `HftRootLink`.
The children's `src` and the `ExtStage` induction are proved (not hypotheses). -/
theorem hftObSrc_of_rootLink (hlink : HftRootLink) {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment)
    (hRd : RootReader lvl env hftRoot synth_hftPcieOutByte.machineData)
    (hRdH : RootReader lvl env hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hRdT : RootReader lvl env hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData) :
    HftObSrc (ι := ι) lvl env := by
  intro p hp i bools bits
  obtain ⟨E, hEnt, hsh, hdat⟩ := hRd
  obtain ⟨g, hg, hgd⟩ := canon_row (lvl := lvl) (env := env) root_wf hsh hdat
  obtain ⟨Eh, hEh, hshh, hdath⟩ := hRdH
  obtain ⟨gh, hgh, hghd⟩ := canon_row (lvl := lvl) (env := env) http_wf hshh hdath
  obtain ⟨Et, hEt, hsht, hdatt⟩ := hRdT
  obtain ⟨gt, hgt, hgtd⟩ := canon_row (lvl := lvl) (env := env) tlp_wf hsht hdatt
  have hkids : ∀ c ∈ g.d.shape.insts.map (·.1), ∃ (Ec : ConstantInfo) (gc : GenData (dataOfAt lvl) Ec (structEnv env)),
      entry₀ env c = some Ec ∧ canonGD lvl env Ec = some gc ∧ gc.d.shape.insts = [] := by
    intro c hc
    rw [hgd, root_insts] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨Eh, gh, hEh, hgh, by rw [hghd]; exact http_leaf⟩
    · exact ⟨Et, gt, hEt, hgt, by rw [hgtd]; exact tlp_leaf⟩
  obtain ⟨p0, hP, -, -, -, hsrc0, hrows⟩ := genGP_root_kids_src (ι := ι) (dom := fun _ => defaultDomain) lvl
    (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env hEnt hg hkids
  have hpe : p = p0 := Option.some.inj (hp.symm.trans hP)
  subst hpe
  rw [congrFun (congrFun (congrFun hsrc0 i) bools) bits]
  generalize genS (genKit (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) env (canonGD lvl env)) = Q at hrows ⊢
  let gi := g.toIn (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl)
  have hgi : gi.d = synth_hftPcieOutByte.machineData := hgd
  have hn : (gi.d.ss.isEmpty && gi.d.shape.insts.isEmpty) = false := by
    have h1 : gi.d.shape.insts.isEmpty = false := by rw [hgi]; exact root_insts_nonempty
    simp [h1]
  have harm : (genSemI Q hftRoot gi).src = (genSemGen Q hftRoot gi).src := by
    unfold genSemI; rw [hn]; rfl
  have hag : TablesAgree Q hftKids gi.d := by
    intro k c a κ hk
    have hc : c ∈ gi.d.shape.insts.map (·.1) := List.mem_map.2 ⟨(c, a, κ), List.mem_of_getElem? hk, rfl⟩
    obtain ⟨Ec, gc, hEc, hgc, hl, hQc⟩ := hrows c hc
    have hc2 : c = hftHttp ∨ c = hftTlp := by
      have hc' := hc
      rw [show gi.d = g.d from rfl, hgd, root_insts] at hc'
      simpa using hc'
    rcases hc2 with rfl | rfl
    · have e1 : Ec = Eh := Option.some.inj (hEc.symm.trans hEh)
      subst e1
      have e2 : gc = gh := Option.some.inj (hgc.symm.trans hgh)
      subst e2
      right
      refine ⟨_, kidSem hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData
        (fun _ bools bits => Sparkle.IP.Net.HTTP.httpGetByte.machineSource defaultDomain bools bits), hQc, by simp [hftKids], ?_, ?_, ?_⟩
      · show (genSemI Q hftHttp (gc.toIn _)).d = _
        rw [genSemI_d]; exact hghd
      · show (genSemI Q hftHttp (gc.toIn _)).kD = kDOf _
        rw [genSemI_kD, show (gc.toIn (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl)).d = _ from hghd]
      · exact genSemI_comb_src Q hftHttp (gc.toIn _) (d := Sparkle.IP.Net.HTTP.httpGetByte.machineData) hghd http_ss http_leaf
          (fun _ bools bits => Sparkle.IP.Net.HTTP.httpGetByte.machineSource defaultDomain bools bits)
          (fun _ bools bits t x => by
            have h := Sparkle.IP.Net.HTTP.httpGetByte.machine_result defaultDomain bools bits t
            rw [hlist_nil_subsingleton _ http_ss x Sparkle.IP.Net.HTTP.httpGetByte.machineInits]
            exact h)
    · have e1 : Ec = Et := Option.some.inj (hEc.symm.trans hEt)
      subst e1
      have e2 : gc = gt := Option.some.inj (hgc.symm.trans hgt)
      subst e2
      right
      refine ⟨_, kidSem hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData
        (fun _ bools bits => Sparkle.IP.Bus.PCIe.tlpCplByte.machineSource defaultDomain bools bits), hQc, by simp [hftKids, hftTlp_ne_http], ?_, ?_, ?_⟩
      · show (genSemI Q hftTlp (gc.toIn _)).d = _
        rw [genSemI_d]; exact hgtd
      · show (genSemI Q hftTlp (gc.toIn _)).kD = kDOf _
        rw [genSemI_kD, show (gc.toIn (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl)).d = _ from hgtd]
      · exact genSemI_comb_src Q hftTlp (gc.toIn _) (d := Sparkle.IP.Bus.PCIe.tlpCplByte.machineData) hgtd tlp_ss tlp_leaf
          (fun _ bools bits => Sparkle.IP.Bus.PCIe.tlpCplByte.machineSource defaultDomain bools bits)
          (fun _ bools bits t x => by
            have h := Sparkle.IP.Bus.PCIe.tlpCplByte.machine_result defaultDomain bools bits t
            rw [hlist_nil_subsingleton _ tlp_ss x Sparkle.IP.Bus.PCIe.tlpCplByte.machineInits]
            exact h)
  have hcaus : CalleesCausal Q gi.d := by
    intro k _ s hs
    have hc : (gi.d.shape.insts[k]).1 ∈ gi.d.shape.insts.map (·.1) := List.mem_map.2 ⟨_, List.getElem_mem k.2, rfl⟩
    obtain ⟨Ec, gc, hEc, hgc, hl, hQc⟩ := hrows _ hc
    rw [hQc] at hs
    cases hs
    refine genSemI_srcCausal Q _ (gc.toIn _) ?_
    intro k' _ s' _
    have h0 : (gc.toIn (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl)).d.shape.insts.length = 0 := congrArg List.length hl
    have h1 := k'.2
    omega
  rw [harm]
  have hb : extBOf Q gi = extBOf hftKids gi := by
    funext i bools bits S; unfold extBOf; rw [ExtStage_agree_tables Q hftKids gi hag]
  have hv : extOf Q gi = extOf hftKids gi := by
    funext i bools bits S; unfold extOf; rw [ExtStage_agree_tables Q hftKids gi hag]
  refine genSemGen_src_eq_of_link Q hftRoot gi hcaus i bools bits _ ?_
  intro S h0 hrec t
  rw [hb, hv] at hrec ⊢
  exact hlink gi hgi i bools bits S h0 hrec t

end Hft

/-! # S1u (part E): `synth_hftPcieOutByte_finalOff` with `hsrc` discharged

`HftFinalStmtOffL Ob CV` is `HftFinalStmtOff Ob CV` with the premise `hsrc : HftObSrc lvl (envAt cref w)` removed (derived inside, from `hchk` and the two child readers by `hftObSrc_of_rootLink`) and the run-independent premise `HftRootLink` put in front.
All the other premises are as in S1t: `L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hnoraw`. -/
section Final
open Tools.ShippingFGCircuitS1tFinal
open Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1iHead Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1qHead Tools.ShippingFGCircuitS1qLinked
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)
open Tools.ShippingFGCircuitCover Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitArtifact Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitBridge Tools.ShippingGen5DeclConnect
open Tools.ShippingFGCircuitS1qEndpoint Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingStRefCorrespondence (ReadWorld)

def HftFinalStmtOffL (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  HftRootLink →
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hcd : Ob (envAt cref w))
    (htop : ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hnoraw : HftObNoRawOff mctx mref cctx cref w b D'),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

/-- **`synth_hftPcieOutByte_finalOffL`**: S1t's assembly with `hsrc` supplied by `hftObSrc_of_rootLink` -/
theorem synth_hftPcieOutByte_finalOffL (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) :
    HftFinalStmtOffL Ob CV := by
  intro hlink ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hCD hTop hNoRaw
  have hhead : HeadAtOff hftRoot mctx mref cctx cref w := headAtOff_of_cellPrem _ hcell
  obtain ⟨raw, D₀, w1, hc, hpe⟩ := postEntryOff hr
  obtain ⟨hgates, ⟨d, hE⟩, hRead⟩ := startFacts_of_checked hchk (root_find_of_headAtOff hhead hc)
  exact synth_hftPcieOutByte_finalOff CV Ob hOb L lvl env₀ hstart hr hcell hchk hRdH hRdT hCD
    (hftObSrc_of_rootLink hlink lvl (envAt cref w) hRead hRdH hRdT) hTop hNoRaw

theorem synth_hftPcieOutByte_finalOffL_Z : HftFinalStmtOffL HftObCDZ cdvZ := synth_hftPcieOutByte_finalOffL cdvZ _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffL_Y : HftFinalStmtOffL HftObCDY cdvY := synth_hftPcieOutByte_finalOffL cdvY _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffL_X : HftFinalStmtOffL HftObCDX cdvX := synth_hftPcieOutByte_finalOffL cdvX _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffL_of (CV : CDRel) : HftFinalStmtOffL (HftObOf CV) CV := synth_hftPcieOutByte_finalOffL CV _ (fun _ h => h)

end Final

end Tools.ShippingFGCircuitS1uSrc

#print axioms Tools.ShippingFGCircuitS1uSrc.ExtStage_agree_tables
#print axioms Tools.ShippingFGCircuitS1uSrc.genSemGen_src_eq_of_link
#print axioms Tools.ShippingFGCircuitS1uSrc.genGP_root_kids_src
#print axioms Tools.ShippingFGCircuitS1uSrc.hftObSrc_of_rootLink
#print axioms Tools.ShippingFGCircuitS1uSrc.synth_hftPcieOutByte_finalOffL
#print axioms Tools.ShippingFGCircuitS1uSrc.synth_hftPcieOutByte_finalOffL_Z
