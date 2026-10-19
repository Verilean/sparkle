import Tools.ShippingCallsGate
import Tools.ShippingCallsAssemblyG
import Tools.ShippingInstTagged

variable {tenv : Lean.Environment}

/-! # The general closing on a real run

* `closeInstsGM_run_all`: a run of `closeInstsGM` from an invariant world of
  positive depth, on a shape WITHOUT memory children, is the pure closing
  `closeInstsG` of real children, and two entries naming one declaration get
  the same child (the entries of one call each ask the memoised entry: the
  later is a hit of what the earlier left).
* `closeInstsG_of_run`: for a run of the harness on the machine's data and
  the `let` closing of its transition, `closeInstsG` returns a module on
  children with the child-side facts of `closeInstsG_of_facts`.

Data conditions, decided per declaration and NOT derived from the shape
reader: S3 (`callsOk`), the slots are the layout's, the binders after the
declaration's have ports. Shapes with memory children: not here.

ORIGIN DISPATCH (patched compiler, `MachineShape.instTagged`): "no memory
child" is now stated on the entries' ORIGINS (`hnotag`, a memory origin is the
only origin with a built child), not on their names: a declaration carrying a
memory placeholder name is compiled, so it is a real child here.
WRITTEN, NOT BUILT against patched compiler (par/o-close). -/
namespace Tools.ShippingCallsRunG
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingCallsShape Tools.ShippingCallsRun Tools.ShippingCallsAssembly
open Tools.ShippingGateChildComb Tools.ShippingChildInv Tools.ShippingRankRun
open Tools.ShippingInlineSoundness (EntryDefines)
open Tools.ShippingCallsGate Tools.ShippingCallsAssemblyG Tools.ShippingCallsStmtsG
open Tools.ShippingInstStmtG Tools.ShippingChildInv Tools.ShippingCallsSame
open Tools.ShippingInstTagged

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

theorem mapM_loop_congr {α β : Type} {f g : α → MetaM β} :
    ∀ (l : List α) (acc : List β), (∀ x ∈ l, f x = g x) →
      List.mapM.loop f l acc = List.mapM.loop g l acc
  | [], _, _ => rfl
  | x :: xs, acc, h => by
    simp only [List.mapM.loop]
    rw [h x (List.mem_cons_self ..)]
    congr 1
    funext y
    exact mapM_loop_congr xs (y :: acc) (fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem runs_mapM_congr {α β : Type} {f g : α → MetaM β} {l : List α}
    {w w' : Void IO.RealWorld} {r : List β}
    (h : RunsTo (List.mapM.loop f l []) mctx mref cctx cref w r w')
    (hfg : ∀ x ∈ l, f x = g x) :
    RunsTo (List.mapM.loop g l []) mctx mref cctx cref w r w' := by
  rw [← mapM_loop_congr l [] hfg]
  exact h

/-- **A run of the general closing, from an invariant world of positive
depth, no memory ORIGIN** (`hnotag`): the pure closing of real children, two
entries of one declaration getting the same child. -/
theorem closeInstsGM_run_all (L : RefLaws mref cref) (hB : ∀ L' : RefLaws mref cref, BodyRel L')
    {shape t m₀ d₀ r} {w w'} (hw : InvV L w) (hd : L.dval w ≠ 0)
    (hnotag : ∀ o ∈ shape.instTagged, o.2.child?.isNone = true)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ children, r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields children (m₀, d₀) ∧
      (children.length = shape.insts.length ∧
        ∀ k (hk : k < shape.insts.length), ∃ y, children[k]? = some y ∧
          RealChild mref cref (shape.insts[k]).1 y) ∧
      (∀ (i j : Nat) (c : Name), i < j → (shape.insts.map (·.1))[i]? = some c →
        (shape.insts.map (·.1))[j]? = some c → children[i]? = children[j]?) ∧ InvV L w' := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, w1, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨rfl, hw1⟩ := synthRead L hw hget
  have hd1 : L.dval w1 ≠ 0 := by rw [(L.same .synthGet hget).2.2]; exact hd
  dsimp only at hr
  obtain ⟨children, w2, hch, hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  -- the patched closing maps the tagged entries and dispatches on the origin
  have hch' := runs_mapM_congr
    (g := fun (x : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) => synthesizeChild x.1) hch
    (fun x hx => by
      obtain ⟨c, o⟩ := x
      have e : o.child? = none := Option.isNone_iff_eq_none.mp (hnotag (c, o) hx)
      dsimp only
      rw [e])
  obtain ⟨ys, hys, hlen, hk, -, hpair, hw2⟩ := mapM_loop_all _
    (fun (x : Name × Sparkle.Compiler.MachInstOrigin.InstOrigin) => x.1) L
    (fun x w y w' hp hdw hy => by
      obtain ⟨h1, h2, h3, h4⟩ := synthesizeChild_post L hB hp hy
      exact ⟨h1, h2, synthesizeChild_depth L hB hp hy, h3, h4,
        fun c0 y0 h0 => (synthesizeChild_pin L hB hp hdw h0 hy).1⟩)
    shape.instTagged [] children w1 _ hw1 hd1 hch'
  simp only [List.reverse_nil, List.nil_append] at hys
  subst hys
  refine ⟨children, heq, ⟨by rw [hlen, instTagged_length], fun k hkl => ?_⟩,
    fun i j c hij hi hj => ?_, hw2⟩
  · have hkT : k < shape.instTagged.length := by rw [instTagged_length]; exact hkl
    obtain ⟨y, hy, hre⟩ := hk k hkT
    refine ⟨y, hy, ?_⟩
    rw [← instTagged_getElem_fst shape hkT]
    exact hre
  · rw [← instTagged_map_fst] at hi hj
    exact hpair i j c hij hi hj

set_option maxHeartbeats 2000000 in
/-- **The general pure closing returns a module, for a real run of the
harness.** The design checks are asked on the joined design, given that the
harness's own design has no module. -/
theorem closeInstsG_of_run {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    {logProf : String → IO Unit} {t t' : Sparkle.IR.AST.Module} {d₀ : Design}
    {children : List (Sparkle.IR.AST.Module × Design)}
    (run : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
      d.shape.binders d.shape.body) (t, d₀))
    (hcl : closeLets d.shape.layout.lets t = some t')
    (hchL : children.length = d.shape.insts.length)
    (hchild : ∀ (k : Nat) (c : Sparkle.IR.AST.Module × Design), children[k]? = some c →
      (∀ args : List Nat, (d.shape.insts.map (·.2.1))[k]? = some args →
        (inPortsOf c.1).length = args.length) ∧
      ((inPortsOf c.1).map (·.name)).Nodup ∧
      (∃ p ∈ c.1.outputs, p.name = d.shape.instFields.getD k "") ∧
      (∀ p ∈ c.1.outputs, (∀ q ∈ inPortsOf c.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst") ∧
      (c.1.outputs.map (·.name)).Nodup ∧
      c.1.name ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hcons : ∀ a ∈ children, ∀ b ∈ children, a.1.name = b.1.name → a.1 = b.1)
    (hfieldsNd : ∀ (k k' : Nat) (key : String × List Nat),
      (keysOf (d.shape.insts.map (·.2.1)) children)[k]? = some key →
      (keysOf (d.shape.insts.map (·.2.1)) children)[k']? = some key →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (hfreshOuts : ∀ (gi : Nat) (c : Sparkle.IR.AST.Module × Design), c ∈ children →
      ∀ o ∈ d.shape.layout.outs, o.name ≠ s!"inst{gi}_{c.1.name}")
    (hdesign : d₀.modules = [] →
      children.all (fun c => Sparkle.Compiler.MachMemory.memSelf
        (moduleByName (designWith children d₀).modules) c.1) = true ∧
      children.all (fun c =>
        decide (moduleByName (designWith children d₀).modules c.1.name = some c.1) &&
        c.2.modules.all (fun g =>
          decide (moduleByName (designWith children d₀).modules g.name = some g))) = true ∧
      (designWith children d₀).modules.all (fun g => noInstOfB (Sparkle.IR.ModuleName.ofDecl declName) g.body) = true) :
    (closeInstsG (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) d.shape.instFields children
      (closeMachine d.shape.layout t', d₀)).isSome = true := by
  simp only [MachineData.callsOk, Bool.and_eq_true, decide_eq_true_eq] at hC
  obtain ⟨⟨⟨hnIn, hargs⟩, hfields⟩, hcoreR⟩ := hC
  simp only [MachineData.ok, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ok
  obtain ⟨hlen, hlets, positive, _, _, _, outsOk, outsNodup, hwf, hb, hv,
    _, _, hscoped, _, _, _, _, _, _, _, _⟩ := ok
  obtain ⟨hfitL, -⟩ := scoped_fit d.letBs d.letFields _ hscoped
  have hlsLen : d.letFields.length = d.ls.length := by simp [MachineData.letFields]
  have hletBs : d.letBs.length = d.shape.binders.length - (d.nIn + d.ss.length) := by
    simp [MachineData.letBs]
  have hposv : PositiveBinders d.shape.binders := by
    intro name n hmem
    have := List.all_eq_true.mp positive _ hmem
    simpa using this
  have hb' : ∀ j, j < d.kb → ∃ name, d.shape.binders[d.bpos j]? = some (name, .bool) := by
    intro j hj
    have := hb j hj
    cases h : d.shape.binders[d.bpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  have hv' : ∀ j, j < d.kv → ∃ name, d.shape.binders[d.vpos j]? = some (name, .bits (d.vw j)) := by
    intro j hj
    have := hv j hj
    cases h : d.shape.binders[d.vpos j]? with
    | none => rw [h] at this; cases this
    | some b =>
      obtain ⟨name, k⟩ := b
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨name, by rw [← this]⟩
  obtain ⟨ids, cache, returned, st, nd, len, hrun, hm, hD, nameLegal⟩ :=
    synthesizeMixedCertified_returns run
  have hA : (d.shape.binders.take nDecl).length = nDecl := by
    rw [List.length_take]
    omega
  have hsplit : d.shape.binders = d.shape.binders.take nDecl ++ d.shape.binders.drop nDecl :=
    (List.take_append_drop ..).symm
  have hBlen : (d.shape.binders.drop nDecl).length =
      d.shape.insts.length + d.ss.length + d.letBs.length := by
    rw [List.length_drop]
    omega
  have hcoreWF := core_wf d.core.2 d.letFields hwf
  obtain ⟨PI, ls, bodyB, w, P, bnd, hin, hPI, hlsL, hndI, hinW, hwAlloc, hbodyT, hacy, hnamed, hnw,
      hP, hF, hdes, hname⟩ :=
    transition_calls_facts (cs := d.callBounds) nd len hrun hm nameLegal hposv d.letFields d.core.2
      hwf hb' hv' hbody hsplit hdomB hBlen hfitL
      (by rw [hA]; exact fieldsOK_of_B d.letFields 0 d.core.2 hfields hwf)
      (by
        rw [hA, hlsLen]
        exact uses_of_reads (fun j hj hr => ⟨hj, posOk_rule hr⟩)
          (fun j hj hr => ⟨hj, posOk_rule hr⟩) d.core.2 hcoreWF hcoreR)
  have hmn : machNIn d.shape = PI.length := by
    rw [hPI]
    unfold machNIn
    rw [show d.shape.binders.length - d.shape.insts.length - d.shape.layout.slots.length -
      d.shape.layout.lets = nDecl by omega]
  rw [hmn, ← hslots]
  rw [hlets] at hcl
  have hargs' : ∀ (k : Nat) (args : List Nat), (d.shape.insts.map (·.2.1))[k]? = some args →
      ∀ a ∈ args, a < d.letBs.length := by
    intro k args hk a ha
    obtain ⟨c, hc, rfl⟩ := inst_get hk
    have := List.all_eq_true.mp (List.all_eq_true.mp hargs c (List.mem_of_getElem? hc)) a ha
    have : a < d.ls.length := by simpa using this
    omega
  obtain ⟨hm1, hm2, hm3⟩ := hdesign (by rw [hD, hdes]; rfl)
  refine closeInstsG_of_facts (cs := d.callBounds) hcl hin hlsL hndI hinW hwAlloc hbodyT hacy
    hnamed hnw hP hF outsOk outsNodup (by simp) hchL hargs' ?_ ?_ ?_ hcons hfieldsNd hfreshOuts
    hm1 hm2 (by rw [hname]; exact hm3)
  · intro j hj
    refine ⟨argBound (d.shape.insts[j]).2.1, by simp [MachineData.callBounds, hj], ?_⟩
    refine argBound_le _ 0 (Nat.zero_le _) (fun a ha => ?_)
    exact hargs' j _ (by simp [hj]) a ha
  · intro k args c hk hc a ha
    obtain ⟨x, hx, rfl⟩ := inst_get hk
    simp only [MachineData.callBounds, List.getElem?_map, hx, Option.map_some,
      Option.some.injEq] at hc
    rw [← hc]
    exact argBound_spec _ 0 a ha
  · intro k c hk
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hchild k c hk
    exact ⟨h1, h2, h3, h4, h5, by rw [hname]; exact h6⟩

end Tools.ShippingCallsRunG
