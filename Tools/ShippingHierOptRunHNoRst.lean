import Tools.ShippingHierOptRunH
import Tools.ShippingRefineNoRst

/-! # The optimizer check over the combinational linked run, without a reset port (worker Q)

WRITTEN, NOT BUILT.

`Tools.ShippingHierOptRunH.hierRefineCheck_linkedH` asks
`"rst" ∈ m.inputs.map (·.name)` and `∀ t, ins t "rst" = 0` (and a width bound
on the extracted module's registers' start values). It uses them in ONE
step: they become `hrstIn'` / `hrstZ'` on the extracted module
`openFlat m (openIns m) (openOuts m)` and are passed to
`Tools.ShippingRefineSoundness.refineCheck_transfer` (whose only use of them
is the register update of `refineCheck_step_sound`, see
`Tools.ShippingRefineNoRst`). A combinational gate-route parent has no `rst`
port (`addClockResetIfSequential` adds clk/rst only with a register or a
memory), so that theorem is vacuous on it.

`hierRefineCheck_linkedH_noRst` is the same theorem for a module with NO
register statement (`seqRegs m = []`; instances are dropped by `openFlat`
and assignments are not registers, so the extracted module has none either,
`seqRegs_openFlat`): no reset premise, no register start-value bound; the
proof is `hierRefineCheck_linkedH`'s with `refineCheck_transfer_noReg` in
place of `refineCheck_transfer`. -/
namespace Tools.ShippingHierOptRunHNoRst
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.HierCheck
open Sparkle.IR.Reorder (writesOf stmtWrites stmtReads refsOf evalExpr_congr)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen
open Tools.ShippingHierOptRun Tools.ShippingMachineLinked Tools.ShippingHierState
open Tools.ShippingHierOptRunH
open Tools.ShippingSeqOptSoundness (seedIn seqRegsL)

/-- Dropping the instance statements keeps the register list. -/
theorem seqRegsL_openBody :
    ∀ body : List Stmt, seqRegsL (openBody body) = seqRegsL body
  | [] => rfl
  | st :: rest => by
    have ih := seqRegsL_openBody rest
    unfold openBody at ih ⊢
    unfold seqRegsL at ih ⊢
    cases st <;> simp [List.filter_cons, List.filterMap_cons, ih]

/-- The extracted module has the module's registers. -/
theorem seqRegs_openFlat (m : Module) (insX outsX : List Port) :
    Sparkle.IR.OptCheck.seqRegs (openFlat m insX outsX) = Sparkle.IR.OptCheck.seqRegs m :=
  seqRegsL_openBody m.body

/-- **`hierRefineCheck_linkedH` for a register-free module, with no reset
port.** If `hierRefineCheck m o` accepts the optimizer's output `o` of a
module `m` without register statements, every combinational linked run of
`m` has a run of `o` from the same state, of the same length, with the same
values on every output port of `m`. The premises are
`hierRefineCheck_linkedH`'s without `hrstIn`, `hrstZ` and `hfitR`. -/
theorem hierRefineCheck_linkedH_noRst (ms : List Module) {m o : Module}
    (hchk : Sparkle.IR.RefineCheck.hierRefineCheck m o = true)
    (hwfM : linkedWF (childMap ms) m.body = true) (hwfO : linkedWF (childMap ms) o.body = true)
    (hndM : (instNames m.body).Nodup) (hndO : (instNames o.body).Nodup)
    (hloc : kidsLocal ms o.body = true)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ child cwe,
      (childMap ms) mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hOutM : ∀ w ∈ bodyInstOuts (childMap ms) m.body, w ∈ (openIns m).map (·.name))
    (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    {T : Nat} {st : String → Nat} {mems : MEnv} {envs : List Env}
    (hrun : runModuleH (declWidth m) (childMap ms) m.body (seedIn m ins) T st mems = some envs)
    (hfitX : ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name),
      (envs[j]'hj) x < 2 ^ declWidth m x)
    (hnoR : Sparkle.IR.OptCheck.seqRegs m = []) :
    o.inputs = m.inputs ∧ o.outputs = m.outputs ∧
    ∃ envsO, runModuleH (declWidth o) (childMap ms) o.body (seedIn m ins) T st mems = some envsO ∧
      envsO.length = envs.length ∧
      ∀ p ∈ m.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envs.length),
        (envsO[j]'hj) p.name = (envs[j]'hj') p.name := by
  -- the check, taken apart
  simp only [Sparkle.IR.RefineCheck.hierRefineCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨hk1, hk2⟩, hconnB⟩, hXdOB⟩, hrc⟩ := hchk
  have hOM := Tools.ShippingHierOptSoundness.instsKept_mem hk1
  have hMO := Tools.ShippingHierOptSoundness.instsKept_mem hk2
  have hXin : ∀ n ∈ (openIns m).map (·.name), n ∉ m.inputs.map (·.name) := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    have := (List.mem_filter.mp hp).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    simpa [List.contains_eq_mem] using this.2
  have hXdM : ∀ n ∈ (openIns m).map (·.name), n ∉ drivesOf m.body := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    have := (List.mem_filter.mp hp).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    simpa [List.contains_eq_mem] using this.1.2
  have hXdO : ∀ n ∈ (openIns m).map (·.name), n ∉ drivesOf o.body := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
    have := List.all_eq_true.mp hXdOB p hp
    simpa [List.contains_eq_mem] using this
  have hconn : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ c ∈ conns, ∀ w,
      c.2 = .ref w → w ∈ (m.outputs ++ (openOuts m)).map (·.name) ∨
        (w ∉ drivesOf m.body ∧ w ∉ drivesOf o.body) := by
    intro mn iname conns hmem c hc w hw
    have h1 := List.all_eq_true.mp hconnB _ hmem
    have h2 := List.all_eq_true.mp h1 c hc
    rw [hw] at h2
    have h3 : (((m.outputs ++ (openOuts m)).map (·.name)).contains w ||
        (!(drivesOf m.body).contains w && !(drivesOf o.body).contains w)) = true := h2
    rcases Bool.or_eq_true_iff.mp h3 with h | h
    · exact Or.inl (by simpa [List.contains_eq_mem] using h)
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      exact Or.inr ⟨by simpa [List.contains_eq_mem] using h.1, by simpa [List.contains_eq_mem] using h.2⟩
  have hOutO : ∀ w ∈ bodyInstOuts (childMap ms) o.body, w ∈ (openIns m).map (·.name) := by
    intro w hw
    obtain ⟨mn, iname, conns, child, cwe, hmem, hc, hwo⟩ := bodyInstOuts_mem hw
    exact hOutM w (instOut_body hc hwo (hOM _ _ _ hmem))
  -- the ports
  obtain ⟨hinP, houtP⟩ := Tools.ShippingRefineSoundness.refineCheck_ports hrc
  have hin : o.inputs = m.inputs := by
    simpa [openFlat] using hinP
  have hout : o.outputs = m.outputs := by
    simpa [openFlat] using houtP
  refine ⟨hin, hout, ?_⟩
  -- 1. the linked run of `m` as an open run of the extracted module
  have hlen := runModuleH_length _ (childMap ms) m.body _ T st mems envs hrun
  let E : Nat → Env := fun k => (envs[T - 1 - k]?).getD (fun _ => 0)
  have hE : ∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j) := by
    intro j hj
    simp only [E]
    rw [show T - 1 - (T - 1 - j) = j by omega]
    simp [hj]
  have hopen := linked_open_runH (declWidth m) (childMap ms) m (openIns m) (openOuts m) ins E hwfM hOutM hXin hXdM
    T st mems envs hrun hE
  -- 2. the extracted pair's check
  have hinsFit' : ∀ t x, x ∈ (openFlat m (openIns m) (openOuts m)).inputs.map (·.name) →
      insOf ((openIns m).map (·.name)) E ins t x < 2 ^ declWidth (openFlat m (openIns m) (openOuts m)) x := by
    intro t x hx
    show insOf ((openIns m).map (·.name)) E ins t x < 2 ^ declWidth m x
    simp only [insOf]
    split
    · rename_i hX
      have hX' : x ∈ (openIns m).map (·.name) := by simpa [List.contains_eq_mem] using hX
      simp only [E]
      cases hj : envs[T - 1 - t]? with
      | none => simp only [Option.getD_none]; exact Nat.two_pow_pos _
      | some e =>
        obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
        simpa using hfitX _ hlt x hX'
    · rename_i hX
      have hX' : x ∉ (openIns m).map (·.name) := by simpa [List.contains_eq_mem] using hX
      simp only [openFlat, List.map_append, List.mem_append] at hx
      rcases hx with hx | hx
      · exact hinsFit t x hx
      · exact absurd hx hX'
  have hopen' : runModule (declWidth (openFlat m (openIns m) (openOuts m)))
      (openFlat m (openIns m) (openOuts m)).body
      (seedIn (openFlat m (openIns m) (openOuts m))
        (insOf ((openIns m).map (·.name)) E ins)) T st mems = some envs := hopen
  have hnoR' : Sparkle.IR.OptCheck.seqRegs (openFlat m (openIns m) (openOuts m)) = [] := by
    rw [seqRegs_openFlat]; exact hnoR
  obtain ⟨envsO, hrunO, hlenO, houtsO⟩ := Tools.ShippingRefineNoRst.refineCheck_transfer_noReg hrc
    hnoR' (insOf ((openIns m).map (·.name)) E ins) hinsFit' (stM := st) (stO := st)
    (mems := mems) hopen'
  -- 3. the open run of the extracted optimized module as a linked run of `o`
  have hlinked := open_linked_runH (declWidth m) (declWidth o) ms m o (openIns m) (openOuts m) ins E
    hwfM hwfO hOM hMO hnofb hloc hOutM hOutO hXin hXdM hXdO hconn T st st mems envs envsO hrun hE
    hrunO
    (fun j hj hj' w hw => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
      exact houtsO p hp j hj hj')
    (fun _ _ _ => rfl)
  refine ⟨envsO, hlinked, hlenO, fun p hp j hj hj' => houtsO p (List.mem_append_left _ hp) j hj hj'⟩

end Tools.ShippingHierOptRunHNoRst
