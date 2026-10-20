import Tools.ShippingShipsDesignSV
import Tools.ShippingChildMapCongr
import Tools.ShippingFirstGateKid
import Tools.ShippingMachineShipsComb

/-! # Gate-route parents: from the cone observation to the design level (worker N, round 10)

WRITTEN, NOT BUILT. PURE: no run, no compiler function.

The seven gate-route parents with a cone theorem conclude, per declaration,
`…ObservesC (ownChild y) M`: ONE cycle of the LINKED evaluation of the core
module `M` (`evalAssignsH (moduleWidths M) (ownChild y) …`), the linked
context being the run's own cached child `y`. The census counts a
declaration by `DesignSV (childMap design.modules) n (checkedOptimize b) …`
(the closed run of the emitted texts of the RETURNED design). The machine
route reaches it by

    core linked run (runModuleH, raw module, childMap D.modules)
      → shipped linked run (runModuleH, checkedOptimize b)   [machine_ships_hierHC: shipsHierHCheck]
      → DesignSV 0                                           [ships_design_svH: design_sv_runN,
                                                              runModuleTG_flat_of_H, svBounds_of_checks]

This file is that chain for a gate-route parent, with the three facts the
gate side does NOT have stated as named propositions (the OBSTACLES):

* (A) `DesignHasChild ms y`: the returned design resolves the cached child's
  name to the cached child's module. The cone contract says nothing about the
  translator state's `design` (`instRegisterChild` adds the child only when
  no module of that name is present yet; a design invariant over
  `translateExprToWire` is not proved anywhere).
* (B) `PostKeeps b M`: the full entry's post passes keep the cone body and
  its widths (`b.body = M.body`, `declWidth b = moduleWidths M`), and the
  body is assignments and instances only. Proved only for parentUse's
  two-statement body (`Tools.ShippingGateParentPost.post_instBody`), not for
  a cone body (the cone contract carries no typedness of `M`).
* (C) `OptKeepsOut ms b "out"`: `checkedOptimize` keeps the linked run's
  `out`. The machine route's lemma `hierRefineCheck_linkedH` and its
  checker `shipsHierHCheck` ask `"rst" ∈ b.inputs`
  (`HierFacts.rst`, through `refineCheck_run_sound`); a combinational
  gate-route parent has NO `rst` port (`addClockResetIfSequential` adds
  clk/rst only with a register or memory), so `shipsHierHCheck` is FALSE on
  it and the machine bridge would be VACUOUS here. A combinational variant of
  `refineCheck_transfer` / `hierRefineCheck_linkedH` without `rst` is not
  written. (C) holds trivially when the optimizer falls back
  (`optKeepsOut_of_eq`).

What IS proved here (generic over the parent):
* `evalAssignsH_congr`: the linked evaluation reads the child map only at the
  body's instance names (`AgreeOn`);
* `agreeOn_ownChild`: under (A), the design's child map agrees with
  `ownChild y` on every instance of a module whose instances are linked in
  `ownChild y` (`InstsLinked`);
* `regNexts_comb`, `memNexts_comb`, `runModuleH_comb_total`: a body of
  assignments and instances runs `T` cycles of `runModuleH` when every cycle's
  linked evaluation succeeds;
* `designSV0_of_runH`: `ships_design_svH`'s last step, alone: a combinational
  linked run of a module whose shipped design passes `designCheck … 0` and
  `kidsComb` is a closed run of the emitted texts (`DesignSV … 0`);
* `gate_designSV_of_steps`: (A), (B), (C), the decidable design checks and the
  width bounds (`DesignSide`), and the per-cycle observation give
  `DesignSV (childMap ms) 0 (checkedOptimize b) (seedIn b ins) T …` showing
  `G j` on `out` at every list index `j`.

NOT concluded: that EVERY closed run shows the source (the uniqueness half of
the machine closed forms); (A), (B), (C) and the checks are antecedents. -/
namespace Tools.ShippingGateDesignLift
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.RegDedup (declWidth)
open Sparkle.IR.OptCheck (checkedOptimize)
open Tools.ShippingHierarchySoundness (evalAssignsH)
open Tools.ShippingMachineLinked (childMap runModuleH stepModuleH)
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingDesignSV (DesignSV designCheck weS textCheckI_sound design_sv_runN)
open Tools.ShippingDesignSVBounds (InvN svBounds_of_checks)
open Tools.ShippingHierState (KidState)
open Tools.ShippingChildMapCongr (AgreeOn)
open Tools.ShippingHierTermSoundness (InstsLinked)
open Tools.ShippingFirstGateKid (ownChild ownChild_self)
open Tools.ShippingChildInv (Res)

/-! ## The obstacles, as propositions -/

/-- (A) The returned design resolves the cached child's name to the cached
child's module. -/
def DesignHasChild (ms : List Sparkle.IR.AST.Module) (y : Res) : Prop :=
  Sparkle.IR.Machine.moduleByName ms y.1.name = some y.1

/-- (B) The post passes keep the core body and its widths; the body is
assignments and instances only. -/
def PostKeeps (b M : Sparkle.IR.AST.Module) : Prop :=
  M.body.all Tools.ShippingHierSVSoundness.combStmtI = true ∧ b.body = M.body ∧
    declWidth b = Tools.ShippingMixedEntrySoundness.moduleWidths M

/-- (C) The shipped optimization keeps the linked run's output `outName`,
for fitting inputs and a start state bounded off the outputs (the
premises of the machine route's `hierRefineCheck_linkedH` without `rst`). -/
def OptKeepsOut (ms : List Sparkle.IR.AST.Module) (b : Sparkle.IR.AST.Module)
    (outName : String) : Prop :=
  ∀ (ins : Nat → String → Nat) (T : Nat) (st0 : String → Nat) (mems : MEnv) (envs : List Env),
    (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
    Tools.ShippingHierTyped.BoundOff (declWidth b) (b.outputs.map (·.name)) st0 →
    runModuleH (declWidth b) (childMap ms) b.body (seedIn b ins) T st0 mems = some envs →
    ∃ envsO, runModuleH (declWidth (checkedOptimize b)) (childMap ms)
        (checkedOptimize b).body (seedIn b ins) T st0 mems = some envsO ∧
      envsO.length = envs.length ∧
      ∀ (j : Nat) (hj : j < envsO.length) (hj' : j < envs.length),
        (envsO[j]'hj) outName = (envs[j]'hj') outName

/-- (C) in the optimizer's fallback branch. -/
theorem optKeepsOut_of_eq {ms : List Sparkle.IR.AST.Module} {b : Sparkle.IR.AST.Module}
    {outName : String} (h : checkedOptimize b = b) : OptKeepsOut ms b outName := by
  intro ins T st0 mems envs _ _ hrun
  rw [h]
  exact ⟨envs, hrun, rfl, fun _ _ _ => rfl⟩

/-- The decidable checks of the shipped design and the width premises of
`ships_design_svH` (inputs, start state, instance states), bundled. -/
def DesignSide (ms : List Sparkle.IR.AST.Module) (b : Sparkle.IR.AST.Module)
    (ins : Nat → String → Nat) (st0 : String → Nat) (kids : String → KidState) : Prop :=
  (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) ∧
  Tools.ShippingHierTyped.BoundOff (declWidth b) (b.outputs.map (·.name)) st0 ∧
  Tools.ShippingMachineDepthH.kidsComb ms (checkedOptimize b).body = true ∧
  designCheck (childMap ms) 0 (checkedOptimize b) = true ∧
  (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ weS (checkedOptimize b) x) ∧
  Bounded (weS (checkedOptimize b)) st0 ∧
  (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
    childMap ms mn = some (gc, gcwe) → InvN (childMap ms) 0 gc (kids iname))

/-! ## The linked evaluation reads the child map only at the instances -/

theorem evalAssignsH_congr {we : WEnv} {C C' : String → Option (Sparkle.IR.AST.Module × WEnv)}
    {mems : MEnv} (body : List Stmt) : AgreeOn C C' body → ∀ env : Env,
      evalAssignsH we C mems body env = evalAssignsH we C' mems body env := by
  induction body with
  | nil => intro _ env; rfl
  | cons st rest ih =>
    intro h env
    have ih' := ih (Tools.ShippingChildMapCongr.AgreeOn.tail h)
    cases st with
    | assign l r => simp only [evalAssignsH, ih']
    | inst mn iname conns =>
      have e : C mn = C' mn := Tools.ShippingChildMapCongr.AgreeOn.head h mn iname conns rfl
      simp only [evalAssignsH, ih', e]
    | _ => simp only [evalAssignsH, ih']

/-- Under (A), the design's child map agrees with the run's own child on
every instance linked in it. -/
theorem agreeOn_ownChild {ms : List Sparkle.IR.AST.Module} {y : Res}
    {M : Sparkle.IR.AST.Module}
    (hA : DesignHasChild ms y) (hlink : InstsLinked (ownChild y) M) :
    AgreeOn (childMap ms) (ownChild y) M.body := by
  intro mn iname conns hm
  obtain ⟨child, cwe, hc, -⟩ := hlink mn iname conns hm
  have hmn : mn = y.1.name := by
    by_cases h : mn = y.1.name
    · exact h
    · exfalso
      have hn : ownChild y mn = none := by
        unfold ownChild
        rw [if_neg h]
      rw [hn] at hc
      cases hc
  subst hmn
  rw [ownChild_self]
  have hA' : Sparkle.IR.Machine.moduleByName ms y.1.name = some y.1 := hA
  show (Sparkle.IR.Machine.moduleByName ms y.1.name).map
      (fun c => (c, Sparkle.IR.RegDedup.declWidth c)) = _
  rw [hA']
  rfl

/-! ## A body of assignments and instances runs its cycles -/

theorem regNexts_comb {we : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt}, body.all Tools.ShippingHierSVSoundness.combStmtI = true →
      ∀ env, regNexts we mems body env = some []
  | [], _, _ => rfl
  | st :: rest, h, env => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases st with
    | assign l e => simp only [regNexts]; exact regNexts_comb h.2 env
    | inst mn i c => simp only [regNexts]; exact regNexts_comb h.2 env
    | _ => simp [Tools.ShippingHierSVSoundness.combStmtI] at h

theorem memNexts_comb {we : WEnv} :
    ∀ {body : List Stmt}, body.all Tools.ShippingHierSVSoundness.combStmtI = true →
      ∀ mems env, memNexts we body mems env = some mems
  | [], _, _, _ => rfl
  | st :: rest, h, mems, env => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    cases st with
    | assign l e => simp only [memNexts]; exact memNexts_comb h.2 mems env
    | inst mn i c => simp only [memNexts]; exact memNexts_comb h.2 mems env
    | _ => simp [Tools.ShippingHierSVSoundness.combStmtI] at h

/-- **A linked run of assignments and instances follows its cycles**
(`Tools.ShippingGateDesign.runModule_assigns_total` for `runModuleH`). -/
theorem runModuleH_comb_total {we : WEnv}
    {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {body : List Stmt}
    (hall : body.all Tools.ShippingHierSVSoundness.combStmtI = true)
    {seed : Nat → (String → Nat) → Env} {R : Nat → Env → Prop} {N : Nat}
    (hstep : ∀ (k : Nat) (st : String → Nat) (mems : MEnv), k < N →
      ∃ e, evalAssignsH we C mems body (seed k st) = some e ∧ R k e) :
    ∀ (T : Nat) (st : String → Nat) (mems : MEnv), T ≤ N →
      ∃ envs, runModuleH we C body seed T st mems = some envs ∧ envs.length = T ∧
        ∀ (j : Nat) (hj : j < envs.length) (t : Nat), t + j + 1 = T → R t (envs[j]'hj) := by
  intro T
  induction T with
  | zero =>
    intro st mems _
    exact ⟨[], by simp [runModuleH], rfl, fun j hj => absurd hj (by simp)⟩
  | succ k ih =>
    intro st mems hT
    obtain ⟨e, he, hR⟩ := hstep k st mems (by omega)
    obtain ⟨rest, hr, hl, hc⟩ := ih st mems (by omega)
    refine ⟨e :: rest, ?_, by simp [hl], ?_⟩
    · simp only [runModuleH, stepModuleH]
      simp only [he, regNexts_comb hall, memNexts_comb hall, Option.bind_eq_bind,
        Option.bind_some, Tools.ShippingMachineShipsComb.applyNexts_nil]
      simp [hr]
    · intro j hj t ht
      cases j with
      | zero =>
        have e1 : t = k := by omega
        subst e1
        exact hR
      | succ j => exact hc j (by simpa using hj) t (by omega)

/-! ## The closed run of the emitted texts -/

/-- **`ships_design_svH`'s last step, alone**: a combinational linked run of
`o` over the design's child map, with the design's checks, is a closed run of
the emitted texts at depth 0. -/
theorem designSV0_of_runH {ms : List Sparkle.IR.AST.Module} {o : Sparkle.IR.AST.Module}
    {seed : Nat → (String → Nat) → Env} {T : Nat} {st0 : String → Nat} {mems : MEnv}
    {kids : String → KidState} {envs : List Env}
    (hcomb : Tools.ShippingMachineDepthH.kidsComb ms o.body = true)
    (hdc : designCheck (childMap ms) 0 o = true)
    (hrun : runModuleH (declWidth o) (childMap ms) o.body seed T st0 mems = some envs)
    (hseedB : ∀ k st, Bounded (weS o) st → Bounded (weS o) (seed k st))
    (hstW : Bounded (weS o) st0)
    (hkidsW : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
      childMap ms mn = some (gc, gcwe) → InvN (childMap ms) 0 gc (kids iname)) :
    DesignSV (childMap ms) 0 o seed T ⟨st0, mems, kids⟩ envs := by
  have hdc' := hdc
  simp only [designCheck, Bool.and_eq_true] at hdc'
  obtain ⟨-, -, -, hwf, -, -, -, -⟩ := textCheckI_sound hdc'.1
  have hrunT := Tools.ShippingMachineDepthH.runModuleTG_flat_of_H _ ms o.body seed
    (Tools.ShippingHierOptRun.memFree_of_linkedWF _ hwf) hcomb T st0 mems kids envs hrun
  exact design_sv_runN ms 0 o seed T ⟨st0, mems, kids⟩ envs hdc hrunT
    (svBounds_of_checks ms 0 o seed T ⟨st0, mems, kids⟩ envs hdc hseedB hstW hkidsW hrunT)

/-! ## The lift -/

/-- **A gate-route parent at the design level, from its per-cycle linked
observation over the run's own child.** `hstep`: at seeding index `k` the
core module's linked evaluation over `ownChild y` succeeds, shows
`G (T - 1 - k)` on `out`, and its instances are linked in `ownChild y` (the
shape of every `…ObservesC (ownChild y) M`). With (A), (B), (C) and the
design's checks and bounds (`DesignSide`): a closed run of the returned
design's emitted texts from `seedIn b ins` exists and shows `G j` on `out` at
list index `j`. -/
theorem gate_designSV_of_steps {ms : List Sparkle.IR.AST.Module}
    {M b : Sparkle.IR.AST.Module} {y : Res}
    (hA : DesignHasChild ms y) (hB : PostKeeps b M) (hC : OptKeepsOut ms b "out")
    {T : Nat} {ins : Nat → String → Nat} {st0 : String → Nat} {mems : MEnv}
    {kids : String → KidState} {G : Nat → Nat}
    (hstep : ∀ (k : Nat) (st : String → Nat) (mems' : MEnv), k < T →
      ∃ result, evalAssignsH (Tools.ShippingMixedEntrySoundness.moduleWidths M) (ownChild y)
          mems' M.body (seedIn b ins k st) = some result ∧
        result "out" = G (T - 1 - k) ∧ InstsLinked (ownChild y) M)
    (hside : DesignSide ms b ins st0 kids) :
    ∃ envsO, DesignSV (childMap ms) 0 (checkedOptimize b) (seedIn b ins) T
        ⟨st0, mems, kids⟩ envsO ∧
      envsO.length = T ∧ ∀ (j : Nat) (hj : j < envsO.length), (envsO[j]'hj) "out" = G j := by
  obtain ⟨hcomb, hbody, hw⟩ := hB
  obtain ⟨hinsFit, hbo, hkc, hdc, hinsW, hstW, hkidsW⟩ := hside
  have hall : b.body.all Tools.ShippingHierSVSoundness.combStmtI = true := by
    rw [hbody]
    exact hcomb
  obtain ⟨envs, hrun, hlen, hR⟩ := runModuleH_comb_total (we := declWidth b) (C := childMap ms)
    hall (seed := seedIn b ins) (N := T)
    (R := fun k e => ∀ s, s + k + 1 = T → e "out" = G s)
    (fun k st mems' hk => by
      obtain ⟨result, hev, hout, hlink⟩ := hstep k st mems' hk
      refine ⟨result, ?_, ?_⟩
      · rw [hbody, hw]
        exact (evalAssignsH_congr M.body (agreeOn_ownChild hA hlink) _).trans hev
      · intro s hs
        have e1 : T - 1 - k = s := by omega
        subst e1
        exact hout)
    T st0 mems (Nat.le_refl T)
  obtain ⟨envsO, hrunO, hlenO, hcorr⟩ := hC ins T st0 mems envs hinsFit hbo hrun
  refine ⟨envsO, designSV0_of_runH hkc hdc hrunO
    (Tools.ShippingShipsDesignSV.seedIn_bound hinsW) hstW hkidsW, by omega, ?_⟩
  intro j hj
  rw [hcorr j hj (by omega)]
  exact hR j (by omega) (T - 1 - j) (by omega) j (by omega)

end Tools.ShippingGateDesignLift

#print axioms Tools.ShippingGateDesignLift.evalAssignsH_congr
#print axioms Tools.ShippingGateDesignLift.runModuleH_comb_total
#print axioms Tools.ShippingGateDesignLift.designSV0_of_runH
#print axioms Tools.ShippingGateDesignLift.gate_designSV_of_steps
