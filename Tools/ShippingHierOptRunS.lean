import Tools.ShippingHierOptRun
-- BUILT by the integrator: bs1 exit 0 for this file (round par/init, base 87874a82).
-- Writing-time guesses: (g1) `seqRegs_openFlat_drives`: `simp only [seqRegs] at hr`, then
-- `List.mem_filterMap`, `simp only [openFlat, openBody] at hst`, the register case closes by `rfl`
-- (drivesOf's second part is `filterMap (register r .. => some r)`); (g2) the copied proof of
-- `hierRefineCheck_linked` elaborates unchanged with `stO` for `s.st` at the two places
-- (`refineCheck_transfer` already takes `stM`/`stO`; `open_linked_run` already takes `stO` and
-- concludes from `⟨stO, sM.mems, sM.kids⟩`).

/-! # The interface check with TWO start states (round par/init, L1)

`hierRefineCheck_linked` (Tools/ShippingHierOptRun.lean) runs the optimizer's output `o` from the
SAME state `s` as the input module `m`. Its two ingredients already take separate states:
`refineCheck_transfer` needs the target state to agree with the source state only on the
registers of the extracted `o`, and `open_linked_run` only on the names neither body drives.
`hierRefineCheck_linkedS` exposes that: the target start state `stO` is free at the names `m`
drives and `o` no longer drives (registers or assignments the optimizer removed).
`stO := s.st` gives back `hierRefineCheck_linked`. No new fact about the compiler. -/
namespace Tools.ShippingHierOptRunS
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.HierCheck
open Sparkle.IR.Reorder (writesOf)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierStateG
open Tools.ShippingHierState Tools.ShippingHierOptLinked
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingHierOptRun

/-- A register of the extracted module is driven by the module's body. -/
theorem seqRegs_openFlat_drives {o : Module} {X Y : List Port} :
    ∀ r ∈ Sparkle.IR.OptCheck.seqRegs (openFlat o X Y), r.1 ∈ drivesOf o.body := by
  intro r hr
  simp only [Sparkle.IR.OptCheck.seqRegs] at hr
  obtain ⟨st, hst, he⟩ := List.mem_filterMap.mp hr
  have hst' : st ∈ o.body := by
    simp only [openFlat, openBody] at hst
    exact (List.mem_filter.mp hst).1
  unfold drivesOf
  refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨st, hst', ?_⟩)
  cases st with
  | register out c rk i iv =>
    have he' : (out, c, rk, i, iv) = r := by simpa using he
    subst he'
    rfl
  | _ => simp at he

set_option maxHeartbeats 2000000 in
/-- **`hierRefineCheck_linked` with the target's own start state** (see the header): `stO` agrees
with the source state `s.st` at every name `m` does not drive or `o` drives. -/
theorem hierRefineCheck_linkedS {σ : Type} (KS : KStep σ) (hloc : KSLocal KS)
    (children : String → Option (Module × WEnv)) {m o : Module}
    (hchk : Sparkle.IR.RefineCheck.hierRefineCheck m o = true)
    (hwfM : linkedWF children m.body = true) (hwfO : linkedWF children o.body = true)
    (hndM : (instNames m.body).Nodup) (hndO : (instNames o.body).Nodup)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ child cwe,
      children mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hOutM : ∀ w ∈ bodyInstOuts children m.body, w ∈ (openIns m).map (·.name))
    (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    (hrstIn : "rst" ∈ m.inputs.map (·.name)) (hrstZ : ∀ t, ins t "rst" = 0)
    {T : Nat} {s : KState σ} {envs : List Env}
    (hrun : runModuleTG KS (declWidth m) children m.body (seedIn m ins) T s = some envs)
    (hfitX : ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name),
      (envs[j]'hj) x < 2 ^ declWidth m x)
    (hfitR : ∀ r ∈ Sparkle.IR.OptCheck.seqRegs (openFlat m (openIns m) (openOuts m)),
      s.st r.1 < 2 ^ declWidth m r.1)
    -- (par/init) the target's start state: the source's, except at names `m` drives and `o` does not
    (stO : String → Nat)
    (hag : ∀ n, (n ∉ drivesOf m.body ∨ n ∈ drivesOf o.body) → stO n = s.st n) :
    o.inputs = m.inputs ∧ o.outputs = m.outputs ∧
    ∃ envsO, runModuleTG KS (declWidth o) children o.body (seedIn m ins) T ⟨stO, s.mems, s.kids⟩ =
        some envsO ∧
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
  have hOutO : ∀ w ∈ bodyInstOuts children o.body, w ∈ (openIns m).map (·.name) := by
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
  have hlen := runModuleTG_length KS _ children m.body _ T s envs hrun
  let E : Nat → Env := fun k => (envs[T - 1 - k]?).getD (fun _ => 0)
  have hE : ∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j) := by
    intro j hj
    simp only [E]
    rw [show T - 1 - (T - 1 - j) = j by omega]
    simp [hj]
  have hopen := linked_open_run KS (declWidth m) children m (openIns m) (openOuts m) ins E hwfM hOutM hXin hXdM
    T s envs hrun hE
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
  have hrstIn' : "rst" ∈ (openFlat m (openIns m) (openOuts m)).inputs.map (·.name) := by
    simp only [openFlat, List.map_append, List.mem_append]; exact Or.inl hrstIn
  have hrstZ' : ∀ t, insOf ((openIns m).map (·.name)) E ins t "rst" = 0 := by
    intro t
    have : "rst" ∉ (openIns m).map (·.name) := fun h => hXin _ h hrstIn
    simp [insOf, List.contains_eq_mem, this, hrstZ t]
  have hopen' : runModule (declWidth (openFlat m (openIns m) (openOuts m)))
      (openFlat m (openIns m) (openOuts m)).body
      (seedIn (openFlat m (openIns m) (openOuts m))
        (insOf ((openIns m).map (·.name)) E ins)) T s.st s.mems = some envs := hopen
  obtain ⟨envsO, hrunO, hlenO, houtsO⟩ := Tools.ShippingRefineSoundness.refineCheck_transfer hrc
    (insOf ((openIns m).map (·.name)) E ins) hinsFit' hrstIn' hrstZ' (stM := s.st) (stO := stO)
    (mems := s.mems) (fun r hr => hag r.1 (Or.inr (seqRegs_openFlat_drives r hr))) hfitR hopen'
  -- 3. the open run of the extracted optimized module as a linked run of `o`
  have hlinked := open_linked_run KS hloc (declWidth m) (declWidth o) children m o (openIns m) (openOuts m) ins E
    hwfM hwfO hndM hndO hOM hMO hnofb hOutM hOutO hXin hXdM hXdO hconn T s stO envs envsO hrun hE
    hrunO
    (fun j hj hj' w hw => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hw
      exact houtsO p hp j hj hj')
    (fun n h1 _ => (hag n (Or.inl h1)).symm)
  refine ⟨envsO, hlinked, hlenO, fun p hp j hj hj' => houtsO p (List.mem_append_left _ hp) j hj hj'⟩

end Tools.ShippingHierOptRunS
