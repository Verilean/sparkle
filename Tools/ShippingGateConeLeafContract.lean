import Tools.ShippingInstanceLeaf
import Tools.ShippingInstArmGrow

variable {tenv : Lean.Environment}

/-! # The instance leaf's contract over `armCont` — the second half of `inst_leaf_contract` (worker N, round 2)

WRITTEN, NOT BUILT.

`Tools.ShippingInstanceLeaf.inst_leaf_contract` proves the unified contract
of an instance leaf with the child PINNED (`hsub`, `htag`): both enter only
in its `prefixRun`, which turns a run of the step into a run of the validated
cache wrapper around the uncached lowering on `(mc, dc)`. Everything after
reads only that run. Here that part is stated as the contract of the ARM'S
CONTINUATION `armCont rec mn y` for ANY child pair `y` — the pair a run's own
child synthesis returned (`inst_leaf_runs`) — with the child's facts about
`y`: no pinned-child premise, no tag premise.

The proof is the text of `inst_leaf_contract` after `prefixRun`, `mc := y.1`,
`dc := y.2`; `prefixRun` is `unfold armCont; rw [houts]`. -/
namespace Tools.ShippingGateParentRun
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingCompareLoweringSoundness (ScalarWidthsAgree)
open Tools.ShippingMixedLiteralSoundness (DeclGrows)
open Tools.ShippingBoolSourceSoundness (translateControlCachedWith_returns)
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires)
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion
open Tools.ShippingHierarchySoundness Tools.ShippingLinkCtx
open Tools.ShippingInstanceEntrySoundness
open Tools.ShippingInstanceLeaf
open Tools.ShippingChildInv (armCont)

set_option linter.unusedSectionVars false

variable [HierCtx] [ChildSem]

set_option maxHeartbeats 1000000 in
/-- **The contract of the arm's continuation on a child pair `y`.** -/
theorem armCont_leaf_contract {rec : TranslateFn} {ctx : CompilerState}
    {inputs : FVarId → Option Value} {we : WEnv} {mems : MEnv} {initial : Env}
    {mn : Name} {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    {vs : List Value} {v : Value} {y : Sparkle.IR.AST.Module × Design} {cwe : WEnv}
    {outName : String} {wOut : Nat}
    (hdc : y.2.modules = [])
    (hnoclk : ∀ p ∈ y.1.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false)
    (hnodup : (y.1.inputs.map (·.name)).Nodup)
    (houts : y.1.outputs = [⟨outName, .bitVector wOut⟩])
    (houtFresh : ∀ p ∈ y.1.inputs, (outName == p.name) = false)
    (hlen : y.1.inputs.length = argsE.length) (hlenV : argsE.length = vs.length)
    (hargs : ∀ k (hk : k < argsE.length) (hk' : k < vs.length),
      Contract rec ctx inputs we mems initial (argsE[k]'hk) (vs[k]'hk'))
    (meaning : Meaning inputs (instEN mn lvls dom argsE) v)
    (hsem : ChildSem.childSem mn vs = some v)
    (hwidth : v.kind.width = wOut)
    (hchild : HierCtx.children y.1.name = some (y.1, cwe))
    (hcorrect : ChildCorrect mn y.1 cwe outName) :
    Contract (armCont rec mn y) ctx inputs we mems initial (instEN mn lvls dom argsE) v := by
  -- the continuation at a one-output child is the validated wrapper
  have prefixRun : ∀ hint top named s t w,
      Returns (armCont rec mn y (instEN mn lvls dom argsE) hint top named) ctx s w t →
      Returns (translateControlCachedWith
        (translateInstanceUncachedWith rec mn y.1 y.2 ⟨outName, .bitVector wOut⟩)
        (instEN mn lvls dom argsE) hint top named) ctx s w t := by
    intro hint top named s t w tr
    unfold armCont at tr
    rw [houts] at tr
    exact tr
  have pairsLen : (y.1.inputs.zip argsE).length = vs.length := by
    simp [hlen, hlenV]
  have pairContracts : ∀ k (hk : k < (y.1.inputs.zip argsE).length) (hk' : k < vs.length),
      Contract rec ctx inputs we mems initial ((y.1.inputs.zip argsE)[k]'hk).2 (vs[k]'hk') := by
    intro k hk hk'
    have hkA : k < argsE.length := by rw [hlenV]; exact hk'
    have : ((y.1.inputs.zip argsE)[k]'hk).2 = argsE[k]'hkA := by simp
    rw [this]
    exact hargs k hkA hk'
  -- the structural frame of one uncached lowering
  have lowerFrame : ∀ hint top named s sm w, Lookup ctx inputs s →
      Returns (translateInstanceUncachedWith rec mn y.1 y.2 ⟨outName, .bitVector wOut⟩
        (instEN mn lvls dom argsE) hint top named) ctx s w sm →
      Frame s sm ∧ (s.usedNames.contains w = false ∨
        s.translateRecord.get? w = some (instEN mn lvls dom argsE)) := by
    intro hint top named s sm w lookup run
    obtain ⟨d', conns, sA, hArgs, hcase⟩ := instUncached_shape hdc hnoclk hlen run
    have fD : Frame s { s with design := d' } := frame_design s d'
    have fA := instArgs_frame _ vs _ 0 conns _ sA pairsLen pairContracts
      (lookup.transfer fD) hArgs
    rcases hcase with ⟨hvalid, ht⟩ | ⟨iname, hw, ht, -⟩
    · rw [ht]
      exact ⟨fD.trans fA, Or.inr (instHitValid_record hvalid)⟩
    · have fW := Tools.ShippingMixedBinarySoundness.Frame.makeWire sA hint wOut named
      have fN := frame_freshName (CircuitM.makeWire hint (.bitVector wOut) named sA).2
        s!"inst_{y.1.name}" false
      have fI := frame_emitInst (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2
        (.inst y.1.name iname (conns.reverse ++ [(outName, .ref w)]))
      refine ⟨?_, Or.inl ?_⟩
      · rw [ht]
        exact (((fD.trans fA).trans fW).trans fN).trans fI
      · have freshA := (CircuitM.makeWire_spec hint (.bitVector wOut) named sA).1
        rw [← hw] at freshA
        cases hu : s.usedNames.contains w with
        | false => rfl
        | true =>
          have := (fD.trans fA).used w hu
          rw [freshA] at this
          cases this
  constructor
  · intro hint top named s t w lookup hr
    rcases translateControlCachedWith_returns (prefixRun hint top named s t w hr) with
      hit | ⟨sm, miss, record⟩
    · have ht := (cacheLookupValidated_returns hit).1
      rw [ht]
      exact Frame.refl s
    · obtain ⟨fl, ok⟩ := lowerFrame hint top named s sm w lookup miss
      exact frame_record_valid fl ok record
  · intro hint top named s t w prior h widths hr
    refine cached_widths_outcome h meaning widths ?_ (prefixRun hint top named s t w hr)
    intro sm r wm run
    obtain ⟨d', conns, sA, hArgs, hcase⟩ := instUncached_shape hdc hnoclk hlen run
    -- only the design changed before the operand walk
    have invD : Inv ctx inputs we mems initial { s with design := d' } prior :=
      h.transfer (LinkCtx.runs_body (s := s) rfl h.runs)
        (LinkCtx.typed_body (s := s) rfl (fun _ hq => hq) (fun _ hq => hq) h.typed) rfl rfl
        (fun _ hu => hu) (fun _ _ => rfl)
    have lookupD : Lookup ctx inputs { s with design := d' } := Lookup.ofInputs invD.inputs
    have fA := instArgs_frame _ vs _ 0 conns _ sA pairsLen pairContracts lookupD hArgs
    rcases hcase with ⟨hvalid, ht⟩ | ⟨iname, hw, ht, hlk⟩
    · -- a validated single-out cache hit: the wire is recorded for this expression
      have wA : ScalarWidthsAgree we sA := by rw [← ht]; exact wm
      obtain ⟨ws, resA, hlenW, hconns, invA, frA, grA, vals⟩ :=
        instArgs_sem _ vs _ 0 conns _ sA prior pairsLen pairContracts invD wA hArgs
      obtain ⟨used, value, width⟩ :=
        h.records r _ (instHitValid_record hvalid) v meaning
      rw [ht]
      exact ⟨grA r used, width, grA, resA, invA, (frA r used).trans value, frA⟩
    · -- a fresh wire and one instance statement
      have hdeclT : ({ name := r, ty := .bitVector wOut } : Port) ∈ sm.module.wires := by
        rw [ht]
        show _ ∈ (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.module.wires
        rw [(CircuitM.freshName_spec _ _ _).2.2,
          (CircuitM.makeWire_spec hint (.bitVector wOut) named sA).2.2.2, hw]
        exact List.mem_cons_self
      have wA : ScalarWidthsAgree we sA := by
        intro p hp
        apply wm p
        rw [ht]
        show p ∈ (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.module.wires
        rw [(CircuitM.freshName_spec _ _ _).2.2,
          (CircuitM.makeWire_spec hint (.bitVector wOut) named sA).2.2.2]
        exact List.mem_cons_of_mem _ hp
      obtain ⟨ws, resA, hlenW, hconns, invA, frA, grA, vals⟩ :=
        instArgs_sem _ vs _ 0 conns _ sA prior pairsLen pairContracts invD wA hArgs
      have specW := CircuitM.makeWire_spec hint (.bitVector wOut) named sA
      have freshA : sA.usedNames.contains r = false := by rw [hw]; exact specW.1
      -- the state just before the instance statement
      have invW : Inv ctx inputs we mems initial
          (CircuitM.makeWire hint (.bitVector wOut) named sA).2 resA :=
        invA.allocate hint (.bitVector wOut) named
      have specN := CircuitM.freshName_spec s!"inst_{y.1.name}" false
        (CircuitM.makeWire hint (.bitVector wOut) named sA).2
      have invN : Inv ctx inputs we mems initial
          (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2 resA :=
        invW.transfer (LinkCtx.runs_body (by rw [specN.2.2]) invW.runs)
          (LinkCtx.typed_body (by rw [specN.2.2])
            (fun q hq => by rw [specN.2.2]; exact hq)
            (fun q hq => by rw [specN.2.2]; exact hq) invW.typed)
          (CircuitM.freshName_sourceBindings _ _ _) (CircuitM.freshName_translateRecord _ _ _)
          (fun z hz => by rw [specN.2.1]; simp [Std.HashSet.contains_insert, hz])
          (fun _ _ => rfl)
      -- the connection list and the child's evaluation
      have hconnsRev : conns.reverse = (y.1.inputs.zip ws).map
          (fun pw => (pw.1.name, Sparkle.IR.AST.Expr.ref pw.2)) := by
        rw [hconns, List.append_nil, List.reverse_reverse]
        exact zip3_map (fun (p : Port) (w : String) => (p.name, Sparkle.IR.AST.Expr.ref w))
          y.1.inputs argsE ws hlen
      have hwsLen : ws.length = y.1.inputs.length := by
        rw [hlenW]
        simp [hlen]
      have hports : ∀ k (hk : k < y.1.inputs.length) (hk' : k < vs.length),
          connEnv (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)]) resA
            (y.1.inputs[k]'hk).name = (vs[k]'hk').toNat := by
        intro k hk hk'
        have hkW : k < ws.length := by rw [hwsLen]; exact hk
        have hl : (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)]).lookup
            (y.1.inputs[k]'hk).name = some (.ref (ws[k]'hkW)) := by
          apply lookup_append_left
          rw [hconnsRev]
          exact lookup_zip_ports y.1.inputs ws k hk hkW hnodup
        rw [connEnv_at hl]
        exact (vals k hkW hk').1
      obtain ⟨cres, hrunC, houtV⟩ := hcorrect mems
        (connEnv (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)]) resA) vs v hsem hports
      have hlookOut : (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)]).lookup outName =
          some (.ref r) := by
        have hne : ∀ p ∈ conns.reverse, (outName == p.1) = false := by
          intro p hp
          rw [hconnsRev] at hp
          obtain ⟨pw, hpw, rfl⟩ := List.mem_map.mp hp
          exact houtFresh pw.1 (List.of_mem_zip hpw).1
        rw [lookup_append_right hne]
        simp [List.lookup]
      have hbind : bindOuts y.1.outputs
          (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)]) cres resA =
          write resA r v.toNat := by
        rw [houts]
        show (match (conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)]).lookup outName with
          | some (.ref w) => fun n => if n = w then cres outName else resA n
          | _ => resA) = _
        rw [hlookOut, houtV]
        rfl
      have runsI := runs_inst (iname := iname)
        (conns := conns.reverse ++ [(outName, Sparkle.IR.AST.Expr.ref r)])
        invN.runs hchild hrunC
      rw [hbind] at runsI
      have inputSafe : ∀ id u, inputs id = some u →
          visible ctx (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.sourceBindings id ≠
            some r := by
        intro id u hi bound
        rw [CircuitM.freshName_sourceBindings, CircuitM.makeWire_sourceBindings] at bound
        obtain ⟨z, hz, hu, _, _⟩ := invA.inputs.lookup id u hi
        have eq : z = r := Option.some.inj (hz.symm.trans bound)
        rw [eq, freshA] at hu
        cases hu
      have recordSafe : ∀ e u, (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.translateRecord.get? r =
            some e → ¬ Meaning inputs e u := by
        intro e u record
        rw [CircuitM.freshName_translateRecord, CircuitM.makeWire_translateRecord] at record
        exact fun meaning => fresh_not_recorded invA.records freshA meaning record
      have invT : Inv ctx inputs we mems initial sm (write resA r v.toNat) := by
        rw [ht]
        exact inv_write_reserved invN inputSafe recordSafe rfl rfl (fun _ hz => hz) runsI
          (HierCtx.typed_inst hchild (instLinked_sound hlk) invN.typed)
      have usedN : ∀ z, sA.usedNames.contains z = true → sm.usedNames.contains z = true := by
        intro z hz
        rw [ht]
        show (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.usedNames.contains z = true
        rw [specN.2.1, specW.2.1]
        simp [Std.HashSet.contains_insert, hz]
      refine ⟨?_, ?_, fun z hz => usedN z (grA z hz), write resA r v.toNat, invT,
        by simp [write], ?_⟩
      · rw [ht]
        show (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (.bitVector wOut) named sA).2).2.usedNames.contains r = true
        rw [specN.2.1, specW.2.1, ← hw]
        simp [Std.HashSet.contains_insert]
      · rw [wm _ hdeclT, ← hwidth]
        rfl
      · intro z hz
        have hzA := grA z hz
        have ne : z ≠ r := by
          intro eq
          rw [eq, freshA] at hzA
          cases hzA
        simp only [write, ne, if_false]
        exact frA z hz

end Tools.ShippingGateParentRun
