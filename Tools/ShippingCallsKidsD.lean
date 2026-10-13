import Tools.ShippingCallsSeqKids
import Tools.ShippingDesignWithG

/-! # `MachineClosesAt` over children that have designs of their own

`ChildIfaceD`: what the general closing asks of a child whose module may hold
instances and whose design may hold modules (a child with calls) — the port
facts of `ChildIfaceG`, no memory-shaped body, and its design described by a
list `names` of printed names: the design's modules have distinct names, all
in `names`, and every instance of the child or of a design module names one
of `names` (the design is closed). A child without calls has it with
`names = []` (`ChildIfaceG.toD`).

`machineClosesAt_of_kidsD`: `MachineClosesAt` of a parent over such
children. Two entries of one declaration are one child (module AND design)
by the cache pin; the joined design's name consistency then needs name
separation over the descendants, stated as premises (N1, obligations — the
kernel does not evaluate `Name.toString`): the parent and each child print
differently from that child's descendants, and two DIFFERENT children share
no printed name. So two different children with a common descendant are NOT
covered here. -/
namespace Tools.ShippingCallsKidsD
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingCallsGate Tools.ShippingCallsRunG Tools.ShippingSeqChildIface
open Tools.ShippingInstStmtG Tools.ShippingCallsStmtsG Tools.ShippingDesignWith
open Tools.ShippingDesignWithG Tools.ShippingCallsSeqKids
open Sparkle.IR.OptCheck (seqStmtOk)

/-- **What the general closing asks of a child with a design of its own.** -/
structure ChildIfaceD (c : Name) (nArgs : Nat) (outs names : List String)
    (b : Sparkle.IR.AST.Module) (design : Design) : Prop where
  name : b.name = (Sparkle.IR.ModuleName.ofDecl c)
  nIn : (inPortsOf b).length = nArgs
  inNd : ((inPortsOf b).map (·.name)).Nodup
  outs : b.outputs.map (·.name) = outs
  outsIn : ∀ p ∈ b.outputs, (∀ q ∈ inPortsOf b, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
    p.name ≠ "rst"
  outsNd : (b.outputs.map (·.name)).Nodup
  noMem : Sparkle.Compiler.MachMemory.memParams? b = none
  desNd : (design.modules.map (·.name)).Nodup
  desNames : ∀ g ∈ design.modules, g.name ∈ names
  closed : ∀ g ∈ b :: design.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → mn ∈ names
  resolves : ∀ mn i conns, Stmt.inst mn i conns ∈ b.body →
    ∃ mc, moduleByName design.modules mn = some mc

/-- A child without calls: no descendant. -/
theorem ChildIfaceG.toD {c : Name} {nArgs : Nat} {outs : List String}
    {b : Sparkle.IR.AST.Module} {design : Design} (h : ChildIfaceG c nArgs outs b design) :
    ChildIfaceD c nArgs outs [] b design := by
  refine ⟨h.name, h.nIn, h.inNd, h.outs, h.outsIn, h.outsNd, memParams_none_of_seqOk h.seqOk,
    (by rw [h.design]; exact List.nodup_nil), (by rw [h.design]; intro g hg; cases hg), ?_, ?_⟩
  · rw [h.design]
    intro g hg mn i conns hm
    have hgb : g = b := by simpa using hg
    subst hgb
    have := List.all_eq_true.mp h.seqOk _ hm
    simp [seqStmtOk] at this
  · intro mn i conns hm
    have := List.all_eq_true.mp h.seqOk _ hm
    simp [seqStmtOk] at this

theorem module_of_name : ∀ (l : List Sparkle.IR.AST.Module), (l.map (·.name)).Nodup →
    ∀ a ∈ l, ∀ b ∈ l, a.name = b.name → a = b
  | [], _, a, ha, _, _, _ => by simp at ha
  | p :: l, hnd, a, ha, b, hb, he => by
    rw [List.map_cons] at hnd
    obtain ⟨h1, h2⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp ha with hpa | ha
    · rcases List.mem_cons.mp hb with hpb | hb
      · rw [hpa, hpb]
      · exact absurd (by rw [← hpa, he]; exact List.mem_map_of_mem hb) h1
    · rcases List.mem_cons.mp hb with hpb | hb
      · exact absurd (by rw [← hpb, ← he]; exact List.mem_map_of_mem ha) h1
      · exact module_of_name l h2 a ha b hb he

theorem noInstOfB_of_names {body : List Stmt} {nm : String}
    (h : ∀ mn i conns, Stmt.inst mn i conns ∈ body → mn ≠ nm) : noInstOfB nm body = true := by
  unfold noInstOfB
  rw [List.all_eq_true]
  intro st hs
  cases st with
  | inst mn i conns => simpa using h mn i conns hs
  | _ => rfl

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000 in
/-- **`MachineClosesAt` for the general closing over children with designs
of their own** (`ChildIfaceD`). -/
theorem machineClosesAt_of_kidsD {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (nk : Nat → Nat) (outsK : Nat → List String) (namesK : Nat → List String)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ChildIfaceD (d.shape.insts[k]).1 (nk k) (outsK k) (namesK k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ outsK k)
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (hsep : ∀ c ∈ d.shape.insts.map (·.1), ∀ c' ∈ d.shape.insts.map (·.1),
      (Sparkle.IR.ModuleName.ofDecl c) = (Sparkle.IR.ModuleName.ofDecl c') → c = c')
    (hparent : ∀ c ∈ d.shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (gi : Nat), ∀ c ∈ d.shape.insts, ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{(Sparkle.IR.ModuleName.ofDecl c.1)}")
    -- name separation over the descendants (N1): the parent and each child
    -- print differently from that child's descendants; two different
    -- children share no printed name
    (hparentD : ∀ (k : Nat), k < d.shape.insts.length → (Sparkle.IR.ModuleName.ofDecl declName) ∉ namesK k)
    (hselfD : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1) ∉ namesK k)
    (hdisjD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 ≠ (d.shape.insts[k']).1 →
      (Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1) ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k') :
    MachineClosesAt mctx mref cctx cref declName d.shape := by
  have hl : Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape :=
    letsClose_of_data d ok hbody halias mctx mref cctx cref
  intro tenv b w r w' hw' hdp hr
  obtain ⟨L, hw⟩ := invV_of_invW mctx cctx hw'
  have hB := fun L' : RefLaws mref cref => bodyRel L'
  unfold synthesizeMachineCertified at hr
  obtain ⟨⟨t, d₀⟩, w1, run, hr⟩ := RunsTo.bind hr
  have hw1 := harness_inv L hB (fun L' => harnessRel_of L' (translateRel L')) hw run
  have hd1 : L.dval w1 ≠ 0 := by
    rw [Tools.ShippingCallsSame.harness_depth L hB (fun L' => harnessRel_of L' (translateRel L'))
      hw run]
    exact dval_ne_of_depthPos mctx cctx L hdp
  dsimp only at hr
  obtain ⟨t', hcl⟩ := Option.isSome_iff_exists.mp (hl (profLogIO b) w t d₀ w1 run)
  rw [hcl] at hr
  dsimp only at hr
  split at hr
  · have := RunsTo.pure_eq hr
    rw [this]
    exact Option.some_ne_none _
  split at hr
  · rename_i he
    exact absurd (List.isEmpty_iff.mp he) hfne
  obtain ⟨children, rfl, hreal, hpair, -⟩ := closeInstsGM_run_all L hB hw1 hd1 hnomem hr
  have key : (closeInstsG (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) d.shape.instFields children
      (closeMachine d.shape.layout t', d₀)).isSome = true := by
    obtain ⟨hlenC, hall⟩ := hreal
    have hfull : ∀ (k : Nat) (c : Res), children[k]? = some c → ∃ hk : k < d.shape.insts.length,
        ChildIfaceD (d.shape.insts[k]).1 (nk k) (outsK k) (namesK k) c.1 c.2 := by
      intro k c hc
      have hk : k < d.shape.insts.length := by
        rw [← hlenC]
        exact (List.getElem?_eq_some_iff.mp hc).1
      obtain ⟨y, hy, hre⟩ := hall k hk
      rw [hc] at hy
      cases hy
      exact ⟨hk, hkid k hk c hre⟩
    -- two entries of one declaration are one child (module and design)
    have hsameDecl : ∀ (i j : Nat) (hi : i < d.shape.insts.length)
        (hj : j < d.shape.insts.length), (d.shape.insts[i]).1 = (d.shape.insts[j]).1 →
        children[i]? = children[j]? := by
      intro i j hki hkj hcc
      have hni : (d.shape.insts.map (·.1))[i]? = some (d.shape.insts[i]).1 := by simp [hki]
      have hnj : (d.shape.insts.map (·.1))[j]? = some (d.shape.insts[j]).1 := by simp [hkj]
      rw [← hcc] at hnj
      rcases Nat.lt_trichotomy i j with h | h | h
      · exact hpair i j _ h hni hnj
      · rw [h]
      · exact (hpair j i _ h hnj hni).symm
    have hcons : ∀ a ∈ children, ∀ c ∈ children, a.1.name = c.1.name → a.1 = c.1 := by
      intro a ha c hc' hn
      obtain ⟨i, hi, hai⟩ := List.getElem_of_mem ha
      obtain ⟨j, hj, hcj⟩ := List.getElem_of_mem hc'
      obtain ⟨hki, fi⟩ := hfull i a (by rw [List.getElem?_eq_getElem hi, hai])
      obtain ⟨hkj, fj⟩ := hfull j c (by rw [List.getElem?_eq_getElem hj, hcj])
      rw [fi.name, fj.name] at hn
      have hni : (d.shape.insts[i]).1 ∈ d.shape.insts.map (·.1) :=
        List.mem_map_of_mem (List.getElem_mem hki)
      have hnj : (d.shape.insts[j]).1 ∈ d.shape.insts.map (·.1) :=
        List.mem_map_of_mem (List.getElem_mem hkj)
      have hsame := hsameDecl i j hki hkj (hsep _ hni _ hnj hn)
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, hai, hcj] at hsame
      exact congrArg Prod.fst (Option.some.inj hsame)
    -- a visited module: its entry, and where it sits
    have hvis : ∀ g ∈ visited children, ∃ (k : Nat) (c : Res) (hk : k < d.shape.insts.length),
        children[k]? = some c ∧
        ChildIfaceD (d.shape.insts[k]).1 (nk k) (outsK k) (namesK k) c.1 c.2 ∧
        (g = c.1 ∨ g ∈ c.2.modules) := by
      intro g hg
      obtain ⟨c, hc, hor⟩ := mem_visited.mp hg
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
      obtain ⟨hk', full⟩ := hfull k c hk
      exact ⟨k, c, hk', hk, full, hor⟩
    have hconsV : ∀ a ∈ visited children, ∀ b ∈ visited children, a.name = b.name → a = b := by
      intro a ha b hb hn
      obtain ⟨i, ci, hki, hci, fi, hai⟩ := hvis a ha
      obtain ⟨j, cj, hkj, hcj, fj, hbj⟩ := hvis b hb
      by_cases hdecl : (d.shape.insts[i]).1 = (d.shape.insts[j]).1
      · have hsame := hsameDecl i j hki hkj hdecl
        rw [hci, hcj] at hsame
        have hcc : ci = cj := Option.some.inj hsame
        subst hcc
        rcases hai with hae | hai
        · rcases hbj with hbe | hbj
          · rw [hae, hbe]
          · exfalso
            have := fi.desNames b hbj
            rw [← hn, hae, fi.name] at this
            exact hselfD i hki this
        · rcases hbj with hbe | hbj
          · exfalso
            have := fi.desNames a hai
            rw [hn, hbe, fi.name] at this
            exact hselfD i hki this
          · exact module_of_name _ fi.desNd a hai b hbj hn
      · exfalso
        obtain ⟨hd1, hd2⟩ := hdisjD i hki j hkj hdecl
        obtain ⟨hd3, hd4⟩ := hdisjD j hkj i hki (fun e => hdecl e.symm)
        have hni : (d.shape.insts[i]).1 ∈ d.shape.insts.map (·.1) :=
          List.mem_map_of_mem (List.getElem_mem hki)
        have hnj : (d.shape.insts[j]).1 ∈ d.shape.insts.map (·.1) :=
          List.mem_map_of_mem (List.getElem_mem hkj)
        have han : a.name = (Sparkle.IR.ModuleName.ofDecl (d.shape.insts[i]).1) ∨ a.name ∈ namesK i := by
          rcases hai with hae | hai
          · exact Or.inl (by rw [hae]; exact fi.name)
          · exact Or.inr (fi.desNames a hai)
        have hbn : b.name = (Sparkle.IR.ModuleName.ofDecl (d.shape.insts[j]).1) ∨ b.name ∈ namesK j := by
          rcases hbj with hbe | hbj
          · exact Or.inl (by rw [hbe]; exact fj.name)
          · exact Or.inr (fj.desNames b hbj)
        rcases han with han | han
        · rcases hbn with hbn | hbn
          · exact hdecl (hsep _ hni _ hnj (by rw [← han, ← hbn, hn]))
          · exact hd1 (by rw [← han, hn]; exact hbn)
        · rcases hbn with hbn | hbn
          · exact hd3 (by rw [← hbn, ← hn]; exact han)
          · exact hd2 _ han (by rw [hn]; exact hbn)
    have hlenM : children.length = (d.shape.insts.map (·.2.1)).length := by simp [hlenC]
    refine closeInstsG_of_run d ok hbody hC hslots hdomB run.mreturns hcl hlenC ?_ hcons ?_ ?_ ?_
    · intro k c hc
      obtain ⟨hk, full⟩ := hfull k c hc
      refine ⟨?_, full.inNd, ?_, full.outsIn, full.outsNd, ?_⟩
      · intro args hargs
        obtain ⟨x, hx, rfl⟩ := inst_get hargs
        have hx' : d.shape.insts[k] = x := by
          have := List.getElem?_eq_getElem hk
          rw [hx] at this
          exact (Option.some.inj this).symm
        rw [full.nIn, hargsN k hk, hx']
      · have := hfieldOut k hk
        rw [← full.outs] at this
        obtain ⟨p, hp, he⟩ := List.mem_map.mp this
        exact ⟨p, hp, he⟩
      · rw [full.name]
        exact hparent _ (List.getElem_mem hk)
    · intro k k' key hkk hkk' hf
      obtain ⟨args, c, ha, hc, rfl⟩ := keys_get hlenM hkk
      obtain ⟨args', c', ha', hc', he⟩ := keys_get hlenM hkk'
      simp only [Prod.mk.injEq] at he
      obtain ⟨hk, full⟩ := hfull k c hc
      obtain ⟨hk', full'⟩ := hfull k' c' hc'
      obtain ⟨x, hx, hxa⟩ := inst_get ha
      obtain ⟨x', hx', hxa'⟩ := inst_get ha'
      have e1 : d.shape.insts[k] = x := by
        have := List.getElem?_eq_getElem hk
        rw [hx] at this
        exact (Option.some.inj this).symm
      have e2 : d.shape.insts[k'] = x' := by
        have := List.getElem?_eq_getElem hk'
        rw [hx'] at this
        exact (Option.some.inj this).symm
      have hn : (Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1) = (Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k']).1) := by
        rw [← full.name, ← full'.name]
        exact he.1
      have hni : (d.shape.insts[k]).1 ∈ d.shape.insts.map (·.1) :=
        List.mem_map_of_mem (List.getElem_mem hk)
      have hnj : (d.shape.insts[k']).1 ∈ d.shape.insts.map (·.1) :=
        List.mem_map_of_mem (List.getElem_mem hk')
      exact hfieldsNd k hk k' hk' (hsep _ hni _ hnj hn)
        (by rw [e1, e2, hxa, hxa']; exact he.2) hf
    · intro gi c hc o ho
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
      obtain ⟨hk', full⟩ := hfull k c hk
      rw [full.name]
      exact hfresh gi _ (List.getElem_mem hk') o ho
    · intro hd0
      refine design_checks hd0 hconsV ?_ ?_
      · intro c hc
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨_, full⟩ := hfull k c hk
        exact full.noMem
      · intro g hg
        obtain ⟨k, c, hk, _, full, hor⟩ := hvis g hg
        refine noInstOfB_of_names (fun mn i conns hm e => ?_)
        have hin : g ∈ c.1 :: c.2.modules := by
          rcases hor with rfl | h
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ h
        exact hparentD k hk (e ▸ full.closed g hin mn i conns hm)
  intro h0
  rw [h0] at key
  cases key

end Tools.ShippingCallsKidsD
