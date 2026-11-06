import Tools.ShippingFGCircuitS1kPkg
import Tools.ShippingGen5SemExtPkg
import Tools.ShippingGen5SemSrcCausal
import Tools.ShippingFGCircuitRoots4
import Tools.ShippingMachineFuse
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
open Tools.ShippingFGCircuitCover Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1
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

end Hft

end Tools.ShippingFGCircuitS1uSrc
