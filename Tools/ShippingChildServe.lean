import Tools.ShippingMachineInstG
import Tools.ShippingMachineLinkedT
import Tools.ShippingHierMono

/-! # The instance serving a call, on the general closing

`closeInstsG` ties call `k` to the instance statement of its group, whose
output wires are the calls' ports `portNames[nIn + k]`; it CHECKS that the
port names are distinct and that every child resolves by its name in the
merged design to itself. Hence an instance statement of the closed module one
of whose output connections is call `k`'s port is the instance of `k`'s group,
and its module (resolved by name) IS `children[k].1` — the call-to-instance
correspondence, read off the closing alone (`closeInstsG_serves`). -/
namespace Tools.ShippingChildServe
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineInstG (CallStmtG closeInstsG_insts closeInstsG_names)
open Tools.ShippingMachineLinkedT (connsG)

theorem nodup_getElem?_inj {α : Type} {l : List α} (h : l.Nodup) {i j : Nat} {a : α}
    (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  have hi' := (List.getElem?_eq_some_iff.mp hi).1
  exact (List.getElem?_inj hi' h).mp (by rw [hi, hj])

/-- The `idx`-th output connection of `connsG`. -/
theorem mem_connsG_out {mc : Module} {argWs : List String} {outs : List (Nat × String)}
    {outWs : List String} {idx : Nat} {e : Nat × String} {w : String}
    (he : outs[idx]? = some e) (hw : outWs[idx]? = some w) :
    (e.2, Expr.ref w) ∈ connsG mc argWs outs outWs := by
  unfold connsG
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨(e.2, w), ?_, rfl⟩
  have hz : ((outs.map (·.2)).zip outWs)[idx]? = some (e.2, w) := by
    rw [List.getElem?_zip_eq_some]
    exact ⟨by simp [he], hw⟩
  exact List.mem_of_getElem? hz

/-- **The instance serving call `k`.** On a closing by `closeInstsG` of a
module without instances, an instance statement one of whose output
connections is call `k`'s port has, as its module resolved by name,
`children[k].1`. -/
theorem closeInstsG_serves {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {fields : List String} {children : List (Module × Design)} {m₀ : Module} {d₀ : Design}
    {m : Module} {d : Design}
    (h : closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d))
    (h0 : ∀ st ∈ m₀.body, isInst st = false)
    (hcr : "clk" ∉ portNames ∧ "rst" ∉ portNames)
    {k : Nat} (hk : k < kI) {mc : Module} {iname : String} {argWs : List String}
    {outs : List (Nat × String)} {outWs : List String}
    (hst : Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ m.body)
    (hout : outs.mapM (fun (k, _) => portNames[nIn + k]?) = some outWs)
    (hke : ∃ e ∈ outs, e.1 = k)
    (hmod : moduleByName d.modules mc.name = some mc) :
    ∃ y, children[k]? = some y ∧ mc = y.1 := by
  obtain ⟨nodupNames, _, _, hcons⟩ := closeInstsG_names h
  have hpn : portNames.Nodup := by
    unfold closeInstsG at h
    simp only [Option.bind_eq_bind] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    · cases h
  rcases closeInstsG_insts h _ hst rfl with h0' | ⟨args', outs', child, mc', hcs, hmc', _, hall'⟩
  · exact absurd (h0 _ h0') (by simp [isInst])
  obtain ⟨outWs', argWs', iname', hout', hargs', _, _, _, _, _, _, _, _, _, hstEq⟩ := hcs
  simp only [Stmt.inst.injEq] at hstEq
  obtain ⟨hname, _, hconns⟩ := hstEq
  -- the module: both resolve the same name
  have hmc'n : mc'.name = child.1.name := Tools.ShippingMachineInst.moduleByName_name hmc'
  have hmm : mc = mc' := by
    rw [hname, hmc'n, hmc'] at hmod; exact (Option.some.inj hmod).symm
  subst hmm
  -- call `k`'s port wire is one of the instance's output connections
  obtain ⟨e, he, rfl⟩ := hke
  obtain ⟨idx, heIdx⟩ := List.mem_iff_getElem?.mp he
  obtain ⟨hlenO, hgetO⟩ := Tools.ShippingMachineInst.mapM_some _ outs outWs hout
  have hidxl : idx < outs.length := (List.getElem?_eq_some_iff.mp heIdx).1
  obtain ⟨w, hw, hwi⟩ := hgetO idx hidxl
  have hoe : outs[idx] = e := (List.getElem?_eq_some_iff.mp heIdx).2
  rw [hoe] at hw
  have hmemC := mem_connsG_out (mc := mc) (argWs := argWs) heIdx hwi
  rw [hconns] at hmemC
  -- in the closing's connections: an argument, the clock/reset, or an output
  rcases List.mem_append.mp hmemC with hin | hout2
  · rcases List.mem_append.mp hin with harg | hclk
    · obtain ⟨⟨p, aw⟩, hpz, hpe⟩ := List.mem_map.mp harg
      simp only [Prod.mk.injEq, Expr.ref.injEq] at hpe
      obtain ⟨q, hqz⟩ := List.mem_iff_getElem?.mp hpz
      have hqa : argWs'[q]? = some aw := (List.getElem?_zip_eq_some.mp hqz).2
      obtain ⟨_, hgetA⟩ := Tools.ShippingMachineInst.mapM_some _ args' argWs' hargs'
      have hqlen : q < args'.length := by
        have h1 := (List.getElem?_eq_some_iff.mp hqa).1
        obtain ⟨hl, _⟩ := Tools.ShippingMachineInst.mapM_some _ args' argWs' hargs'
        omega
      obtain ⟨aw2, haw2, hqa2⟩ := hgetA q hqlen
      rw [hqa] at hqa2; cases hqa2
      rw [hpe.2] at haw2
      have := nodup_getElem?_inj hpn hw haw2
      omega
    · split at hclk
      · simp only [List.mem_cons, Prod.mk.injEq, Expr.ref.injEq, List.not_mem_nil, or_false] at hclk
        rcases hclk with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact absurd (List.mem_of_getElem? hw) hcr.1
        · exact absurd (List.mem_of_getElem? hw) hcr.2
      · cases hclk
  · obtain ⟨⟨f, ow⟩, hfz, hfe⟩ := List.mem_map.mp hout2
    simp only [Prod.mk.injEq, Expr.ref.injEq] at hfe
    obtain ⟨i, hiz⟩ := List.mem_iff_getElem?.mp hfz
    obtain ⟨hfi, hoi⟩ := List.getElem?_zip_eq_some.mp hiz
    obtain ⟨_, hgetO'⟩ := Tools.ShippingMachineInst.mapM_some _ outs' outWs' hout'
    have hilen : i < outs'.length := by
      have := (List.getElem?_eq_some_iff.mp hfi).1; simpa using this
    obtain ⟨ow2, how2, hoi2⟩ := hgetO' i hilen
    rw [hoi] at hoi2; cases hoi2
    rw [hfe.2] at how2
    have hkk := nodup_getElem?_inj hpn hw how2
    have hk' : e.1 = outs'[i].1 := by simp only [List.get_eq_getElem] at hkk; omega
    have hmem' : outs'[i] ∈ outs' := List.getElem_mem hilen
    obtain ⟨_, hnm, _⟩ := hall' _ hmem'
    rw [← hk'] at hnm
    cases hy : children[e.1]? with
    | none => rw [hy] at hnm; cases hnm
    | some y =>
      rw [hy, Option.map_some, Option.some.injEq] at hnm
      refine ⟨y, rfl, ?_⟩
      have hyc : y ∈ children := List.mem_of_getElem? hy
      have := (hcons y hyc).1
      rw [hnm, hmc'] at this
      exact Option.some.inj this

/-- `closeInsts`'s checks: the port names are distinct and every child is
found by its name in the merged design as itself. -/
theorem closeInsts_names {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)) :
    portNames.Nodup ∧ ∀ c ∈ children, moduleByName d.modules c.1.name = some c.1 := by
  unfold closeInsts at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    cases h
    refine ⟨hc.1.1.1.1.1.1.1.1.1.1.1.2, fun c hcm => ?_⟩
    have := List.all_eq_true.mp hc.1.1.1.2 c hcm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · cases h

/-- **The instance serving call `k`, on the one-output closing.** An instance
statement of the closing that is call `k`'s statement (`CallStmt`: its last
connection is call `k`'s port) has, as its module resolved by name,
`children[k].1`. -/
theorem closeInsts_serves {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d))
    (h0 : ∀ st ∈ m₀.body, isInst st = false)
    {k : Nat} {args : List Nat} {mc : Module} {st : Stmt}
    (hst : st ∈ m.body) (hcs : Tools.ShippingMachineInst.CallStmt nIn kI n portNames k args mc st)
    (hmod : moduleByName d.modules mc.name = some mc) :
    ∃ y, children[k]? = some y ∧ mc = y.1 := by
  obtain ⟨hpn, hcons⟩ := closeInsts_names h
  obtain ⟨outW, argWs, outP, iname, hW, _, _, _, _, _, _, _, _, hstE⟩ := hcs
  have hi : isInst st = true := by subst hstE; rfl
  rcases Tools.ShippingMachineInst.closeInsts_insts h st hst hi with h0' | ⟨k', args', child, mc', _, hchild, hmc', hcs'⟩
  · exact absurd (h0 _ h0') (by simp [hi])
  obtain ⟨outW', argWs', outP', iname', hW', _, _, _, _, _, _, _, _, hstE'⟩ := hcs'
  rw [hstE] at hstE'
  simp only [Stmt.inst.injEq] at hstE'
  obtain ⟨hname, _, hconns⟩ := hstE'
  have hlast := congrArg List.getLast? hconns
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq, Prod.mk.injEq, Expr.ref.injEq] at hlast
  have hkk := nodup_getElem?_inj hpn hW (hlast.2 ▸ hW')
  have hk : k = k' := by omega
  subst hk
  have hmc'n : mc'.name = child.1.name := Tools.ShippingMachineInst.moduleByName_name hmc'
  have hmm : mc = mc' := by
    rw [hname, hmc'n, hmc'] at hmod; exact (Option.some.inj hmod).symm
  subst hmm
  refine ⟨child, hchild, ?_⟩
  have := hcons child (List.mem_of_getElem? hchild)
  rw [hmc'] at this
  exact Option.some.inj this

theorem noInstOf_of_B {t : String} {body : List Stmt} (h : noInstOfB t body = true) :
    Tools.ShippingHierMono.NoInstOf t body := by
  intro mn iname conns hm
  have := List.all_eq_true.mp h _ hm
  simpa using this

/-- **The one-output closing is acyclic at its module, and its children's
designs are consistent with it.** -/
theorem closeInsts_acyclic {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)) :
    m.name = m₀.name ∧ Tools.ShippingHierMono.NoInstOf m.name m.body ∧
      (∀ g ∈ d.modules, Tools.ShippingHierMono.NoInstOf m.name g.body) ∧
      ∀ c ∈ children, ∀ g ∈ c.2.modules, moduleByName d.modules g.name = some g := by
  unfold closeInsts at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    cases h
    refine ⟨rfl, noInstOf_of_B hc.1.1.2, fun g hg => noInstOf_of_B (List.all_eq_true.mp hc.1.2 g hg),
      fun c hcm g hg => ?_⟩
    have := List.all_eq_true.mp hc.1.1.1.2 c hcm
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    exact this.2 g hg
  · cases h

/-- **The general closing is acyclic at its module.** -/
theorem closeInstsG_acyclic {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {fields : List String}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d)) :
    m.name = m₀.name ∧ Tools.ShippingHierMono.NoInstOf m.name m.body ∧
      ∀ g ∈ d.modules, Tools.ShippingHierMono.NoInstOf m.name g.body := by
  unfold closeInstsG at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    cases h
    have hn : (withClockFor children m₀).name = m₀.name := (withClockFor_same children m₀).1
    refine ⟨hn, ?_, fun g hg => ?_⟩
    · show Tools.ShippingHierMono.NoInstOf (withClockFor children m₀).name _
      rw [hn]; exact noInstOf_of_B hc.1.2
    · show Tools.ShippingHierMono.NoInstOf (withClockFor children m₀).name _
      rw [hn]; exact noInstOf_of_B (List.all_eq_true.mp hc.2 g hg)
  · cases h

/-- The one-output closing's children are combinational, local and wired
(`kidsCombB`, checked by the closing). -/
theorem closeInsts_kidsComb {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)) :
    kidsCombB d.modules m.body = true := by
  unfold closeInsts at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    cases h
    exact hc.2
  · cases h

end Tools.ShippingChildServe
