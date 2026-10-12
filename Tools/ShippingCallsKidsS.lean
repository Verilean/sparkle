import Tools.ShippingCallsKidsD
import Tools.ShippingCallsRunFinal

/-! # The general closing over callees that may SHARE a descendant: what is proved, and what it rests on

`machineClosesAt_of_kidsD` (`Tools/ShippingCallsKidsD.lean` 98–134) asks, for
two entries of DIFFERENT declarations, that no printed name occur under both
(`hdisjD`, 131–133). It is used in ONE place (231–252): to refute that two
visited modules of one name come from different callees. For a parent whose
callees share a descendant (`mixDeep`: `midH` is a callee and a descendant of
the callee `mid2`) the hypothesis is false.

What the closing needs there is not a fact about names. The pure closing
`closeInstsG` returns `none` unless every visited module is found, by its
name, AS ITSELF in the joined design (`Sparkle/IR/MachineInstG.lean`
140–141), so two visited modules of one name must be EQUAL — and for modules
that come from two different callees the only thing that can make them equal
is the child cache: nothing in `RealChild` relates one child's design to
another child's module, and two real compiles of one declaration are not
known to be equal (`Tools/ShippingCallsSame.lean` 5–7).

So this file does NOT derive `MachineClosesAt` for such a parent. It proves
the closing RELATIVE to a statement about the cache the closing ends in:

* `Agree decls m`: in the map `m`, the entries of two different declarations
  of `decls` agree on every module name they both have (the child's module
  or a module of its design).
* `CacheAgrees mref cref decls w`: `Agree` of what a read of the child cache
  returns in `w`.
* `MachineClosesAtS … decls`: `MachineClosesAt` with one more antecedent —
  the world the run ENDS in satisfies `CacheAgrees decls`. It is WEAKER than
  `MachineClosesAt` and is not accepted by anything that asks
  `MachineClosesAt`.
* `closes_of_agree` (the core): the proof of `machineClosesAt_of_kidsD` with
  `hdisjD` replaced by "IF the end world satisfies the invariant THEN it
  satisfies `CacheAgrees`".
* `machineClosesAtS_of_kids`: `MachineClosesAtS` from the hypotheses of
  `machineClosesAt_of_kidsD` WITHOUT `hdisjD`.
* `machineClosesAt_of_kidsD_again`: the old statement, from the core — with
  `hdisjD` the cache's entries of different callees have no name in common,
  so `CacheAgrees` holds vacuously. (The old file is unchanged; this shows
  the core generalises it.)

NOT proved, and not assumed under another name: that the end world of a real
run satisfies `CacheAgrees` when callees share a descendant. See
`docs/parallel/A-shared-descendant.md` for why it does not follow from the
invariant `InvW` and for the exact missing statements.

WRITTEN, NOT BUILT (par/a-17). -/
namespace Tools.ShippingCallsKidsS
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
open Tools.ShippingCallsKidsD
open Sparkle.IR.OptCheck (seqStmtOk)

/-- In the map `m`, the entries of two DIFFERENT declarations of `decls` agree
on every module name they both have: the child's module, or a module of its
design. (Nothing is said of two entries of one declaration: a map has one.) -/
def Agree (decls : List Name) (m : Std.HashMap Name Res) : Prop :=
  ∀ c ∈ decls, ∀ c' ∈ decls, c ≠ c' → ∀ (y y' : Res), m.get? c = some y → m.get? c' = some y' →
    ∀ a ∈ y.1 :: y.2.modules, ∀ b ∈ y'.1 :: y'.2.modules, a.name = b.name → a = b

section Defs
variable (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
  (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)

/-- What a read of the child cache returns in `w` satisfies `Agree decls`. -/
def CacheAgrees (decls : List Name) (w : Void IO.RealWorld) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) m w1,
    RunsTo (sparkleChildCache.get : MetaM _) mctx mref cctx cref w m w1 → Agree decls m

/-- **`MachineClosesAt` with one more antecedent**: the world the machine
synthesis ENDS in satisfies `CacheAgrees decls`. WEAKER than
`MachineClosesAt`. -/
def MachineClosesAtS (declName : Name) (shape : MachineShape) (decls : List Name) : Prop :=
  ∀ (b : Bool) w r w', InvW mref cref w → DepthPos mref cref w →
    RunsTo (synthesizeMachineCertified
      (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName shape)
      mctx mref cctx cref w r w' → CacheAgrees mref cref decls w' → r ≠ none

end Defs

/-- `MachineClosesAt` is the stronger statement. -/
theorem MachineClosesAtS.of_closes {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {declName : Name}
    {shape : MachineShape} (decls : List Name)
    (h : MachineClosesAt mctx mref cctx cref declName shape) :
    MachineClosesAtS mctx mref cctx cref declName shape decls :=
  fun b w r w' hw hd hr _ => h b w r w' hw hd hr

theorem mem_cons_of_or {g : Sparkle.IR.AST.Module} {c : Res}
    (h : g = c.1 ∨ g ∈ c.2.modules) : g ∈ c.1 :: c.2.modules := by
  rcases h with h | h
  · rw [h]
    exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ h

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

set_option maxHeartbeats 1000000 in
/-- **The core**: the general closing over children with designs of their
own (`ChildIfaceD`) returns a module on a run whose END world, if it
satisfies the invariant, satisfies `CacheAgrees` over the callees. The
hypotheses are those of `machineClosesAt_of_kidsD` without `hdisjD`. -/
theorem closes_of_agree {declName : Name} (d : MachineData) (ok : d.ok = true)
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
      c.toString = c'.toString → c = c')
    (hparent : ∀ c ∈ d.shape.insts, c.1.toString ≠ declName.toString)
    (hfresh : ∀ (gi : Nat), ∀ c ∈ d.shape.insts, ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{c.1.toString}")
    (hparentD : ∀ (k : Nat), k < d.shape.insts.length → declName.toString ∉ namesK k)
    (hselfD : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (d.shape.insts[k]).1.toString ∉ namesK k) :
    ∀ (b : Bool) w r w', InvW mref cref w → DepthPos mref cref w →
      RunsTo (synthesizeMachineCertified
        (fun e hint top named => translateExprToWire e hint top named) (profLogIO b) declName
        d.shape) mctx mref cctx cref w r w' →
      (InvW mref cref w' → CacheAgrees mref cref (d.shape.insts.map (·.1)) w') → r ≠ none := by
  have hl : Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape :=
    letsClose_of_data d ok hbody halias mctx mref cctx cref
  intro b w r w' hw' hdp hr hag
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
  obtain ⟨children, rfl, hreal, hpair, hfin, hwE⟩ :=
    Tools.ShippingCallsRunFinal.closeInstsGM_run_allF L hB hw1 hd1 hnomem hr
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
    -- the end world's cache: its entries of different callees agree
    have hAg : Agree (d.shape.insts.map (·.1)) (L.val w') := by
      obtain ⟨mE, wE, hgE⟩ := refGet_runs (mctx := mctx) (mref := mref) (cctx := cctx)
        (cref := cref) sparkleChildCache w'
      have hmE : mE = L.val w' := L.cacheGet _ _ _ hgE
      have hA := hag (invW_of_invV L hwE) mctx cctx mE wE hgE
      rw [hmE] at hA
      exact hA
    -- two entries of DIFFERENT declarations: their children agree on common names
    have hcross : ∀ (i j : Nat) (hi : i < d.shape.insts.length) (hj : j < d.shape.insts.length)
        (ci cj : Res), children[i]? = some ci → children[j]? = some cj →
        (d.shape.insts[i]).1 ≠ (d.shape.insts[j]).1 →
        ∀ a ∈ ci.1 :: ci.2.modules, ∀ b ∈ cj.1 :: cj.2.modules, a.name = b.name → a = b := by
      intro i j hi hj ci cj hci hcj hne a ha b hb hn
      obtain ⟨yi, hyi, hvi⟩ := hfin i hi
      obtain ⟨yj, hyj, hvj⟩ := hfin j hj
      have ei : yi = ci := Option.some.inj (hyi.symm.trans hci)
      have ej : yj = cj := Option.some.inj (hyj.symm.trans hcj)
      rw [ei] at hvi
      rw [ej] at hvj
      have hni : (d.shape.insts[i]).1 ∈ d.shape.insts.map (·.1) :=
        List.mem_map_of_mem (List.getElem_mem hi)
      have hnj : (d.shape.insts[j]).1 ∈ d.shape.insts.map (·.1) :=
        List.mem_map_of_mem (List.getElem_mem hj)
      exact hAg _ hni _ hnj hne ci cj hvi hvj a ha b hb hn
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
      · -- different declarations: by the cache the run ends in (the ONLY use of `hag`)
        exact hcross i j hki hkj ci cj hci hcj hdecl a (mem_cons_of_or hai) b
          (mem_cons_of_or hbj) hn
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
      have hn : (d.shape.insts[k]).1.toString = (d.shape.insts[k']).1.toString := by
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
        have hin : g ∈ c.1 :: c.2.modules := mem_cons_of_or hor
        exact hparentD k hk (e ▸ full.closed g hin mn i conns hm)
  intro h0
  rw [h0] at key
  cases key

set_option maxHeartbeats 1000000 in
/-- **`MachineClosesAtS` for the general closing over children with designs
of their own, callees that share a descendant included**: the hypotheses of
`machineClosesAt_of_kidsD` without the disjointness `hdisjD`. The conclusion
asks the run's end world to satisfy `CacheAgrees` over the callees — that is
NOT derived here. -/
theorem machineClosesAtS_of_kids {declName : Name} (d : MachineData) (ok : d.ok = true)
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
      c.toString = c'.toString → c = c')
    (hparent : ∀ c ∈ d.shape.insts, c.1.toString ≠ declName.toString)
    (hfresh : ∀ (gi : Nat), ∀ c ∈ d.shape.insts, ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{c.1.toString}")
    (hparentD : ∀ (k : Nat), k < d.shape.insts.length → declName.toString ∉ namesK k)
    (hselfD : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (d.shape.insts[k]).1.toString ∉ namesK k) :
    MachineClosesAtS mctx mref cctx cref declName d.shape (d.shape.insts.map (·.1)) :=
  fun b w r w' hw hdp hr hag =>
    closes_of_agree d ok hbody halias hC hslots hdomB hfne nk outsK namesK hnomem hkid hargsN
      hfieldOut hfieldsNd hsep hparent hfresh hparentD hselfD b w r w' hw hdp hr (fun _ => hag)

set_option maxHeartbeats 1000000 in
/-- **The statement of `machineClosesAt_of_kidsD`, from the core.** With the
disjointness `hdisjD`, the cache's entries of two different callees have no
module name in common (each is a `RealChild`, read by `hkid`), so the end
world satisfies `CacheAgrees` vacuously. Not a replacement of the theorem in
`Tools/ShippingCallsKidsD.lean` (unchanged, and still what the generators
use): the check that the core generalises it. -/
theorem machineClosesAt_of_kidsD_again {declName : Name} (d : MachineData) (ok : d.ok = true)
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
      c.toString = c'.toString → c = c')
    (hparent : ∀ c ∈ d.shape.insts, c.1.toString ≠ declName.toString)
    (hfresh : ∀ (gi : Nat), ∀ c ∈ d.shape.insts, ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{c.1.toString}")
    (hparentD : ∀ (k : Nat), k < d.shape.insts.length → declName.toString ∉ namesK k)
    (hselfD : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (d.shape.insts[k]).1.toString ∉ namesK k)
    (hdisjD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 ≠ (d.shape.insts[k']).1 →
      (d.shape.insts[k]).1.toString ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k') :
    MachineClosesAt mctx mref cctx cref declName d.shape := by
  intro b w r w' hw hdp hr
  refine closes_of_agree d ok hbody halias hC hslots hdomB hfne nk outsK namesK hnomem hkid
    hargsN hfieldOut hfieldsNd hsep hparent hfresh hparentD hselfD b w r w' hw hdp hr ?_
  intro hinv mctx' cctx' m w1 hg c hc c' hc' hne y y' hy hy' a ha b' hb hn
  exfalso
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
  obtain ⟨j, hj, hcj⟩ := List.getElem_of_mem hc'
  have hki : i < d.shape.insts.length := by simpa using hi
  have hkj : j < d.shape.insts.length := by simpa using hj
  have ei : (d.shape.insts[i]).1 = c := by
    rw [← hci]
    simp
  have ej : (d.shape.insts[j]).1 = c' := by
    rw [← hcj]
    simp
  have hry : RealChild mref cref (d.shape.insts[i]).1 y := by
    rw [ei]
    exact hinv.1 mctx' cctx' m w1 hg c y hy
  have hry' : RealChild mref cref (d.shape.insts[j]).1 y' := by
    rw [ej]
    exact hinv.1 mctx' cctx' m w1 hg c' y' hy'
  have fi := hkid i hki y hry
  have fj := hkid j hkj y' hry'
  have hdecl : (d.shape.insts[i]).1 ≠ (d.shape.insts[j]).1 := by
    rw [ei, ej]
    exact hne
  obtain ⟨hd1, hd2⟩ := hdisjD i hki j hkj hdecl
  obtain ⟨hd3, hd4⟩ := hdisjD j hkj i hki (fun e => hdecl e.symm)
  have han : a.name = (d.shape.insts[i]).1.toString ∨ a.name ∈ namesK i := by
    rcases List.mem_cons.mp ha with hae | hai
    · exact Or.inl (by rw [hae]; exact fi.name)
    · exact Or.inr (fi.desNames a hai)
  have hbn : b'.name = (d.shape.insts[j]).1.toString ∨ b'.name ∈ namesK j := by
    rcases List.mem_cons.mp hb with hbe | hbj
    · exact Or.inl (by rw [hbe]; exact fj.name)
    · exact Or.inr (fj.desNames b' hbj)
  have hni : (d.shape.insts[i]).1 ∈ d.shape.insts.map (·.1) :=
    List.mem_map_of_mem (List.getElem_mem hki)
  have hnj : (d.shape.insts[j]).1 ∈ d.shape.insts.map (·.1) :=
    List.mem_map_of_mem (List.getElem_mem hkj)
  rcases han with han | han
  · rcases hbn with hbn | hbn
    · exact hdecl (hsep _ hni _ hnj (by rw [← han, ← hbn, hn]))
    · exact hd1 (by rw [← han, hn]; exact hbn)
  · rcases hbn with hbn | hbn
    · exact hd3 (by rw [← hbn, ← hn]; exact han)
    · exact hd2 _ han (by rw [hn]; exact hbn)

end Tools.ShippingCallsKidsS
