import Tools.ShippingRefineSoundness

/-! # `refineCheck` without a reset port, on register-free modules (worker Q)

WRITTEN, NOT BUILT.

`Tools.ShippingRefineSoundness.refineCheck_run_sound` / `refineCheck_transfer`
ask `"rst" ∈ m.inputs.map (·.name)` and `∀ t, ins t "rst" = 0`. Those two
premises are used in exactly ONE place: `refineCheck_step_sound`'s
`hrst` / `hrstO` (`init "rst" = 0`, `initO "rst" = 0`), which become
`hrstM` / `hrstOF` (`envM "rst" = 0`, `envO "rst" = 0`, through
`evalAssigns_keeps "rst"`), and those are read ONLY by the register parts of
the conclusion:

* the pairing `∀ pr ∈ nextsO, pr ∈ nextsM` (`rw [hkM, hkO, hrstM, hrstOF, …]`:
  both registers take their next value, not their reset value), and
* the bound of `m`'s register updates (`rw [hallM' r hr, hrstM, …]`).

(`refineCheck_run_sound` itself only feeds `seedIn … "rst" = 0` through.)
The outputs' correspondence (`houtCorr`) and the evaluation of both assign
segments never read `rst`. On a module WITHOUT registers (`seqRegs m = []`,
and then `seqRegs o = []` by the check's pairing clause) the register parts are
empty, so the reset premises are vacuous; this file restates the three
theorems for that case without them:

* `refineCheck_seqRegs_o_nil`: the check gives `seqRegs o = []`;
* `refineCheck_step_noReg`: one cycle, both modules step with no register
  update and the memories unchanged, outputs equal;
* `refineCheck_run_noReg` / `refineCheck_transfer_noReg`: any number of
  cycles, from ANY pair of start states (no register to couple). -/

namespace Tools.ShippingRefineNoRst

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Sparkle.IR.Reorder (refsOf)
open Tools.ShippingOptSoundness Tools.ShippingSeqOptSoundness
open Tools.ShippingRefineSoundness

/-- A register-free `m` accepted by the check has a register-free `o`
(every register of `o` must have a namesake in `m`). -/
theorem refineCheck_seqRegs_o_nil {m o : Sparkle.IR.AST.Module}
    (hchk : refineCheck m o = true) (hnoR : seqRegs m = []) : seqRegs o = [] := by
  simp only [refineCheck] at hchk
  rw [Bool.and_eq_true] at hchk
  obtain ⟨h1, -⟩ := hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨-, hpairs⟩, -⟩ := h1
  cases hro : seqRegs o with
  | nil => rfl
  | cons ro rest =>
    exfalso
    have hmem : ro ∈ seqRegs o := by rw [hro]; simp
    have hf := List.all_eq_true.mp hpairs ro hmem
    rw [hnoR] at hf
    simp [regOf] at hf

open Sparkle.IR.RegDedup (declWidth) in
set_option maxHeartbeats 4000000 in
/-- **`refineCheck` is sound for one cycle on a register-free module, with no
reset premise.** With fitting inputs, both modules step with no register
update and the memories unchanged, and the outputs agree. -/
theorem refineCheck_step_noReg {m o : Sparkle.IR.AST.Module}
    (hchk : refineCheck m o = true) (hnoR : seqRegs m = []) {mems : MEnv} {init : Env}
    (hins : ∀ x ∈ m.inputs.map (·.name), init x < 2 ^ declWidth m x) {initO : Env}
    (hagree : ∀ x ∈ (m.inputs.map (·.name)).filter
        (fun x => declWidth m x == declWidth o x), initO x = init x) :
    ∃ envM envO,
      stepModule (declWidth m) m.body init mems = some (envM, [], mems) ∧
      stepModule (declWidth o) o.body initO mems = some (envO, [], mems) ∧
      (∀ p ∈ m.outputs, envO p.name = envM p.name) := by
  have hnoO : seqRegs o = [] := refineCheck_seqRegs_o_nil hchk hnoR
  simp only [refineCheck] at hchk
  rw [Bool.and_eq_true] at hchk
  obtain ⟨h1, h2⟩ := hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_hinEq, _houtEq⟩, hokM⟩, hokO⟩, _hndM⟩, _hndO⟩, _hdisjM⟩, _hdisjO⟩, _hzM⟩,
    _hzO⟩, _hpairs⟩, _hallM⟩ := h1
  -- fitting environments over both reference domains
  have hinsMfit : ∀ x ∈ (m.inputs.map (·.name) ++ (seqRegs m).map (·.1)),
      init x < 2 ^ (declWidth m) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hins x hx
    · rw [hnoR] at hx
      simp at hx
  have hwEq : ∀ x ∈ ((m.inputs.map (·.name)).filter
      (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)),
      declWidth m x = declWidth o x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨-, hwx⟩ := List.mem_filter.mp hx
      simpa using hwx
    · rw [hnoO] at hx
      simp at hx
  have hagree' : ∀ x ∈ ((m.inputs.map (·.name)).filter
      (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)),
      initO x = init x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hagree x hx
    · rw [hnoO] at hx
      simp at hx
  have hinsOfit : ∀ x ∈ ((m.inputs.map (·.name)).filter
      (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)),
      initO x < 2 ^ (declWidth o) x := by
    intro x hx
    rw [hagree' x hx, ← hwEq x hx]
    rcases List.mem_append.mp hx with hx | hx
    · exact hins x (List.mem_filter.mp hx).1
    · rw [hnoO] at hx
      simp at hx
  -- the normal-form half of the check
  split at h2
  case h_2 => cases h2
  rename_i dm dO hnm hno
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨houts, -⟩, -⟩ := h2
  have hd0M : RDefsOk (declWidth m) init init [] :=
    ⟨fun x d hx => by simp [List.lookup] at hx, fun _ _ => rfl⟩
  have hd0O : RDefsOk (declWidth o) initO initO [] :=
    ⟨fun x d hx => by simp [List.lookup] at hx, fun _ _ => rfl⟩
  obtain ⟨envM, hevM, hdM⟩ :=
    rNormBody_sound (mems := mems) hinsMfit (seqAssigns m) [] dm init hd0M hnm
  obtain ⟨envO, hevO, hdO⟩ :=
    rNormBody_sound (mems := mems) hinsOfit (seqAssigns o) [] dO initO hd0O hno
  have hevMfull : evalAssigns (declWidth m) mems m.body init = some envM := by
    rw [evalAssigns_seq_skip hokM]
    exact hevM
  have hevOfull : evalAssigns (declWidth o) mems o.body initO = some envO := by
    rw [evalAssigns_seq_skip hokO]
    exact hevO
  -- a normal form of `o` has the same value in both initial environments
  have hcongr : ∀ {e : Expr}, RShape (declWidth o) e →
      (refsOf e).all (fun x => ((m.inputs.map (·.name)).filter
        (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)).contains x) = true →
      evalExpr (declWidth m) init e = evalExpr (declWidth o) initO e := by
    intro e hs hrefs
    refine (rShape_congr hs (fun x hx => ?_)).2.2
    have hx' : x ∈ ((m.inputs.map (·.name)).filter
        (fun x => declWidth m x == declWidth o x) ++ (seqRegs o).map (·.1)) := by
      have := List.all_eq_true.mp hrefs x hx
      simpa [List.contains_eq_mem] using this
    exact ⟨hwEq x hx', (hagree' x hx').symm⟩
  -- output correspondence
  have houtCorr : ∀ p ∈ m.outputs, envO p.name = envM p.name := by
    intro p hp
    have h := List.all_eq_true.mp houts p hp
    split at h
    case h_2 => cases h
    rename_i em eo hem heo
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨heq, hrefsO⟩ := h
    obtain ⟨-, hvM⟩ := hdM.1 p.name em hem
    obtain ⟨hsO, hvO⟩ := hdO.1 p.name eo heo
    rw [heq, hcongr hsO hrefsO, hvO] at hvM
    exact Option.some.inj hvM
  -- no register: no update
  have hnoRL : seqRegsL m.body = [] := hnoR
  have hnoOL : seqRegsL o.body = [] := hnoO
  have hnM := regNexts_seq_map (we := (declWidth m)) (mems := mems) (envF := envM)
    (f := fun _ => 0) hokM (fun r hr => by rw [hnoRL] at hr; cases hr)
  have hnO := regNexts_seq_map (we := (declWidth o)) (mems := mems) (envF := envO)
    (f := fun _ => 0) hokO (fun r hr => by rw [hnoOL] at hr; cases hr)
  rw [hnoRL, List.map_nil] at hnM
  rw [hnoOL, List.map_nil] at hnO
  have hmemM := memNexts_seqStmtOk (we := (declWidth m)) (mems := mems) (envF := envM) hokM
  have hmemO := memNexts_seqStmtOk (we := (declWidth o)) (mems := mems) (envF := envO) hokO
  refine ⟨envM, envO, ?_, ?_, houtCorr⟩
  · simp only [stepModule, hevMfull, hnM, hmemM, Option.bind_eq_bind, Option.bind_some]
  · simp only [stepModule, hevOfull, hnO, hmemO, Option.bind_eq_bind, Option.bind_some]

open Sparkle.IR.RegDedup (declWidth) in
set_option maxHeartbeats 2000000 in
/-- **Accepted register-free pairs are trace-equivalent, with no reset
premise.** From any fitting input stream and ANY pair of start states, both
modules run for `k` cycles and their output streams coincide. -/
theorem refineCheck_run_noReg {m o : Sparkle.IR.AST.Module}
    (hchk : refineCheck m o = true) (hnoR : seqRegs m = []) (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x) :
    ∀ (k : Nat) (stM stO : String → Nat) (mems : MEnv),
      ∃ trM trO,
        runModule (declWidth m) m.body (seedIn m ins) k stM mems = some trM ∧
        runModule (declWidth o) o.body (seedIn m ins) k stO mems = some trO ∧
        trM.length = k ∧ trO.length = k ∧
        ∀ p ∈ m.outputs, trO.map (fun e => e p.name) = trM.map (fun e => e p.name) := by
  intro k
  induction k with
  | zero =>
    intro stM stO mems
    exact ⟨[], [], rfl, rfl, rfl, rfl, fun p _ => rfl⟩
  | succ k ih =>
    intro stM stO mems
    have hcontains : ∀ x ∈ m.inputs.map (·.name),
        ((m.inputs.map (·.name)).contains x) = true := by
      intro x hx
      simpa [List.contains_eq_mem] using hx
    have hinsE : ∀ x ∈ m.inputs.map (·.name),
        seedIn m ins k stM x < 2 ^ declWidth m x := by
      intro x hx
      simp only [seedIn]
      rw [if_pos (hcontains x hx)]
      exact hinsFit k x hx
    have hagreeE : ∀ x ∈ (m.inputs.map (·.name)).filter
        (fun x => declWidth m x == declWidth o x),
        seedIn m ins k stO x = seedIn m ins k stM x := by
      intro x hx
      obtain ⟨hxin, -⟩ := List.mem_filter.mp hx
      simp only [seedIn]
      rw [if_pos (hcontains x hxin), if_pos (hcontains x hxin)]
    obtain ⟨envM, envO, hstepM, hstepO, hout⟩ :=
      refineCheck_step_noReg hchk hnoR (mems := mems) hinsE hagreeE
    obtain ⟨trM', trO', hrunM', hrunO', hlenM', hlenO', houts'⟩ :=
      ih (applyNexts stM []) (applyNexts stO []) mems
    refine ⟨envM :: trM', envO :: trO', ?_, ?_, by simp [hlenM'], by simp [hlenO'], ?_⟩
    · simp only [runModule, hstepM, Option.bind_eq_bind, Option.bind_some, hrunM']
    · simp only [runModule, hstepO, Option.bind_eq_bind, Option.bind_some, hrunO']
    · intro p hp
      simp only [List.map_cons]
      rw [hout p hp, houts' p hp]

open Sparkle.IR.RegDedup (declWidth) in
/-- `refineCheck_transfer` for a register-free `m`, with no reset premise:
an `m`-side canonical-seed run transfers to `o` from ANY start state. -/
theorem refineCheck_transfer_noReg {m o : Sparkle.IR.AST.Module}
    (hchk : refineCheck m o = true) (hnoR : seqRegs m = []) (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    {k : Nat} {stM stO : String → Nat} {mems : MEnv} {envs : List Env}
    (hrun : runModule (declWidth m) m.body (seedIn m ins) k stM mems = some envs) :
    ∃ envsO,
      runModule (declWidth o) o.body (seedIn m ins) k stO mems = some envsO ∧
      envsO.length = envs.length ∧
      ∀ p ∈ m.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envs.length),
        (envsO[j]'hj) p.name = (envs[j]'hj') p.name := by
  obtain ⟨trM, trO, hrunM, hrunO, hlenM, hlenO, houts⟩ :=
    refineCheck_run_noReg hchk hnoR ins hinsFit k stM stO mems
  rw [hrun] at hrunM
  have htrM : trM = envs := (Option.some.inj hrunM.symm)
  subst htrM
  refine ⟨trO, hrunO, by omega, ?_⟩
  intro p hp j hj hj'
  have h1 := List.getElem_of_eq (houts p hp)
    (by simp only [List.length_map]; omega : j < (trO.map (fun e => e p.name)).length)
  simpa using h1

end Tools.ShippingRefineNoRst
