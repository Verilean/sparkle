import Tools.ShippingSeqParentGenD2
-- UNIT SR3x: only the REFUSAL text for callees sharing a leaf changed (step that fails stated); builds x3 (see report). BUILT (unit SR3w): m1 exit 0 (module), m2/m3(exit 1: my asserted call lists and the audit traversal order)/m4/m5 exit 0 (Tests.Compiler.SeqDeepGenDiffTest, SeqDeepGenDiffConclTest), r1 exit 1 (universe error in `oldInstGroups`) /r2/r3/f1 exit 0 (group numbering read from the old term; Tests.Compiler.SeqDeepGenGroupTest).
/-! # `#machine_seq_parent_endpoint P`, DEPTH-2 path with SEVERAL DIFFERENT callees at the parent (unit SR3w, ledger L8af)

A THIRD elaborator for the same command syntax (the depth-1 elaborator of `Tools/ShippingSeqParentGen.lean` and the one-callee depth-2
elaborator of `Tools/ShippingSeqParentGenD2.lean` are UNCHANGED; this module is imported only by files that want it).  It takes over exactly
when the parent `P` calls at least TWO different callees and at least one of them has call instances of its own; for every other
declaration it throws `unsupportedSyntax` (the earlier elaborators run as before).

## The TARGET CLASS (each condition is checked; a declaration outside it is REFUSED with a reason, never silently narrowed)
`P -> C_i -> G_i` for `i < r` (`r >= 2` DIFFERENT callees `C_i`), where
* `P` is a top-level machine (`machineSource` indexed by `Unit`), no memory, `instFields <> []`; its call instances call the `C_i` in any
  order / number, with any number of argument lists (the group numbering is recomputed from a call-argument approximation of the old key `(callee, argument lets, call arguments)` and compared with the partition read from the old term);
* every `C_i` is a `{dom : DomainConfig}` hardware module with ONE leaf callee `G_i` (any number of instances), no memory, `instFields <> []`;
* every `G_i` is a generated sequential leaf, no memory; the `G_i` are PAIRWISE DIFFERENT and different from every `C_j` and from `P`;
* the old chain exists: `#machine_design_svNR P 2`.
Each `(C_i, G_i)` block is the one-callee machinery of `Tools/ShippingSeqParentGenD2.lean` (its per-callee declarations are textual copies with the
names `P.epD2M{i}_*`); the parent level uses callee-dispatch families (`epD2M_outsOf`, ...) indexed by the name of the callee at call `k`.

## REFUSED, with the reason (message prefix `REFUSED`)
* a callee of `P` that is a LEAF next to a callee with calls (mixed sequential-leaf and depth-2 callees): the predicate `PC` of the old chain would
  mix `MachineRun` and `MachineRunNCA`, and the parent's `ChildIfaceP` / `KidFactsA` for a leaf next to a deep callee is not instantiated here; OPEN;
* two callees that call the SAME leaf `G` (OR a leaf that is also a callee): the library closing `Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids'`
  has the premise `hdisjD` (the sets of module names of two different call classes must be disjoint), which is FALSE when both contain `G`; the old
  piece that is MISSING is a closing lemma for different callees that share a module. Unit SR3x examined it: the step that fails is the equality of
  the two same-named modules of the callees' results (`KidTA`/`RealChildA` are histories of past runs; no law relates two runs of one declaration);
  a premise `hagree` for it would restate that obligation, so none was added;
* memory in `P` / a callee / a leaf; several leaves of ONE callee; depth 3 (a leaf with calls of its own); a non-polymorphic callee; no instField;
  a missing generated piece; a group numbering that cannot be aligned with the old generated `hcalls`.

## What is still STRUCTURAL (not claimed removed)
`findHeadApp?` ("first application of the head constant"), the beta-redex / zip pairing in `oldGroupFact%`, reading the call arguments by
`sigAtPos` / `findCall` (for every instance with ITS callee), reading the old partition from the chain `forall_getElem?_cons … (entry proof)` by the names `gfB/gfL/gfR/gfHb/gfHv`, and the assumption that the old generator's group order is the one
recomputed here (checked by the group COUNT and by the partition READ from the old generated term, up front; and by the typed extraction; a wrong numbering is a safe failure).  Concrete examples are not whole-class
coverage.  The boundary `P.epD2M_Bnd` (an existential over `O`, `T`, `AdmCtx`, `MachineDefines` of every `C_i` and `G_i`, a start world in `JQ`, the
cache invariant) stays in the CONCLUSION; `RealChildA` is a history of past synthesis results; `T` is an ADDED boundary. -/
namespace Tools.ShippingSeqParentGenD2M
open Lean Elab Command Meta Term
open Tools.ShippingSeqParentGen (runCmds elabText readNames readName reduceNat openBlock)
open Tools.ShippingSeqParentGenD2 (openBlock2 readNats readNatLists sourceIndex isMemName memWhy oldGroupCount groupFactsTmpl)

/-- The per-callee block (`@I@` = index, `@C@`/`@G@` = callee / leaf, `@KC@` = own inputs of `@C@`, `@GW@` = widths of `@G@`'s arguments):
the textual copy of the one-callee declarations of `Tools/ShippingSeqParentGenD2.lean` that do not mention the parent's other callees. -/
def tcTmpl : String := r#"
/-- An origin without a memory key builds no child (so a call-field origin, whatever its field index, is `KidTA`'s second disjunct). -/
theorem _root_.@P@.epD2M@I@_origin_child_none (o : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (h : Tools.ShippingMemCloses.memKey o = none) : o.child? = none := by
  cases o with
  | ord => rfl
  | field _ => rfl
  | mem c a d => exact absurd h (by simp [Tools.ShippingMemCloses.memKey])

theorem _root_.@P@.epD2M@I@_G_outs_clean :
    ∀ o ∈ @G@.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

noncomputable def _root_.@P@.epD2M@I@_G_nk : Nat :=
  ((@G@.machineData.shape.binders.take (@G@.machineData.shape.binders.length -
    @G@.machineData.shape.layout.slots.length - @G@.machineData.shape.layout.lets)).filter
      fun x => x.2 != .domain).length

theorem _root_.@P@.epD2M@I@_C_insts_G : ∀ (k : Nat) (hk : k < @C@.machineData.shape.insts.length),
    (@C@.machineData.shape.insts[k]).1 = ``@G@ := by
  first | decide | decide +kernel

theorem _root_.@P@.epD2M@I@_C_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk @C@.machineData @KC@ (fun _ => @GW@) = true := by
  first | decide | decide +kernel


theorem _root_.@P@.epD2M@I@_C_closesA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``@C@ @C@.machineData.shape := by
  have hent : ∀ (k : Nat) (hk : k < @C@.machineData.shape.insts.length),
      (@C@.machineData.shape.insts[k]).1 = ``@G@ ∧ Tools.ShippingMemCloses.memKey (originAt @C@.machineData.shape k) = none := by
    first | decide | decide +kernel
  have hkid : ∀ (k : Nat) (hk : k < @C@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (originAt @C@.machineData.shape k)
        (@C@.machineData.shape.insts[k]).1 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``@G@) @P@.epD2M@I@_G_nk
        (@G@.machineData.shape.layout.outs.map (·.name)) [] y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, ho⟩ := hent k hk
    unfold Tools.ShippingCallsMemA.KidTA at hy
    rw [@P@.epD2M@I@_origin_child_none _ ho] at hy
    rcases hy with hy | ⟨-, hre⟩
    · exact absurd hy (by show (none : Option _) ≠ some y; exact fun h => nomatch h)
    · rw [hn] at hre
      have hG := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O @G@.machineData @G@.machine_ok
        @G@.machine_body (by decide) (by decide) hR0 (fun mc cc => @G@.machine_closes mc _ cc _) hre
      exact Tools.ShippingCallsKidsD.ChildIfaceD.toP (Tools.ShippingCallsKidsD.ChildIfaceG.toD hG)
        (fun hx => nomatch hx)
  intro tenv
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := @KC@) O T hA @C@.machineData
    @C@.machine_ok @C@.machine_body (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun _ => Sparkle.IR.ModuleName.ofDecl ``@G@) (fun _ => @P@.epD2M@I@_G_nk)
    (fun _ => @G@.machineData.shape.layout.outs.map (·.name)) (fun _ => [])
    hkid (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun k hk k' hk' _ => by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)
    (fun k hk => Tools.ShippingModuleName.ofDecl_ne (by decide : ``@G@ ≠ ``@C@))
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by first | decide | decide +kernel :
        ∀ o ∈ @C@.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi _)
    (fun k hk hx => nomatch hx)
    (fun k hk k' hk' hne => (hne (by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)).elim)

theorem _root_.@P@.epD2M@I@_C_hsep {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape) :
    ∀ (k : Nat) (hk : k < @C@.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      RealChildA O (@C@.machineData.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl ``@C@) := by
  have hn : ∀ (k : Nat) (hk : k < @C@.machineData.shape.insts.length),
      (@C@.machineData.shape.insts[k]).1 = ``@G@ := by
    first | decide | decide +kernel
  refine Tools.ShippingSeqChildDeepConsumerA.hsep_of_leaf_kids (mctx := mctx) (cctx := cctx) O @C@.machineData ?_
    (fun k hk => by rw [hn k hk]; decide)
  intro k hk
  rw [hn k hk]
  exact ⟨@G@.machineData, @G@.machine_ok, @G@.machine_body, by decide, by decide, hR0,
    fun mc cc => @G@.machine_closes mc _ cc _⟩


set_option maxRecDepth 100000 in
theorem _root_.@P@.epD2M@I@_C_outChars : ∀ o ∈ @C@.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem _root_.@P@.epD2M@I@_C_outScalar : ∀ o ∈ @C@.machineData.shape.layout.outs,
    Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel


theorem _root_.@P@.epD2M@I@_G_kidFactsA (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape) (n : Nat) :
    KidFactsA O ``@G@ @G@.machineData.shape.layout.outs @GW@ n := by
  have hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``@G@ @G@.machineData.shape :=
    fun mc cc => @G@.machine_closes mc _ cc _
  have hon : ∀ o ∈ @G@.machineData.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
    fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (@P@.epD2M@I@_G_outs_clean o ho)
  have hdw : Tools.ShippingPortWidthsPure.declWidths @G@.machineData = @GW@ := by first | decide | decide +kernel
  exact
  { outsIn := fun y hy =>
      (Tools.ShippingSeqChildIfaceA.seqChild_of_realA O @G@.machineData @G@.machine_ok @G@.machine_body
        (by decide) (by decide) hR0 hcl hy).outsIn
    outTys := fun y hy =>
      Tools.ShippingCallWidthsChildRealA.leaf_real_outTysA (O := O) @G@.machineData @G@.machine_ok @G@.machine_body
        (by decide) (by decide) (by decide) (by decide) hR0
        (fun mctx' cctx' {tenv} b _ w r w' _ _ hr => @G@.machine_closes mctx' _ cctx' _ (Tools.ShippingChildInv.profLogIO b) w r w' hr) hy
    kidA := fun y hy =>
      Tools.ShippingParentRunFactsA.leaf_real_kidAA O @G@.machineData @G@.machine_ok @G@.machine_body
        (by decide) (by decide) (by decide) (by decide) hR0 hcl hy
    kidR := fun y hy =>
      Tools.ShippingParentRunFactsA.leaf_real_kidRA O @G@.machineData @G@.machine_ok @G@.machine_body
        (by decide) (by decide) hR0 hcl hy
    masked := fun y hy =>
      Tools.ShippingChecksMaskedLeafA.leaf_real_kidMA (nDecl := @G@.machineData.nIn) O @G@.machineData
        @G@.machine_ok @G@.machine_body (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        hR0 hcl hy
    portsIn := fun y hy =>
      Tools.ShippingParentDesignFA.leaf_real_portsInA O @G@.machineData @G@.machine_ok @G@.machine_body
        (nDecl := @G@.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hon (by decide) hy
    inW := fun y hy j q hq => by
      obtain ⟨wd, h1, h2⟩ := Tools.ShippingParentDesignFA.leaf_real_inWidthsA O @G@.machineData @G@.machine_ok
        @G@.machine_body (nDecl := @G@.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy j q hq
      rw [hdw] at h1
      exact ⟨wd, h1, h2⟩
    clk := fun y hy =>
      Tools.ShippingParentDesignFA.leaf_real_clkA O @G@.machineData @G@.machine_ok @G@.machine_body
        (nDecl := @G@.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) hR0 hcl hy
    check := fun y hy ms _ _ => by
      have hK := Tools.ShippingParentDesignFA.leaf_real_kidK_regA O @G@.machineData @G@.machine_ok @G@.machine_body
        (nDecl := @G@.machineData.nIn) (by decide) (by decide) rfl (by decide) (by decide) (by decide) hR0 hcl hon (by decide) hy
      exact ⟨hK.1 _ n, fun g hg => hK.2 g hg _ n⟩ }

theorem _root_.@P@.epD2M@I@_C_kidFactsA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape) :
    KidFactsA O ``@C@ @C@.machineData.shape.layout.outs
      (Tools.ShippingCallsChildPorts.argWidths @C@.machineData @KC@) (n + 1) := by
  have hn := @P@.epD2M@I@_C_insts_G
  exact Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidFactsA O T @C@.machineData @C@.machine_ok
    @C@.machine_body (nDecl := @KC@) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    @KC@ (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun _ => @G@.machineData.shape.layout.outs) (fun _ => @GW@) n
    (fun k hk => by rw [hn k hk]; exact @P@.epD2M@I@_G_kidFactsA O hR0 n)
    (fun k hk => by rw [hn k hk]; exact @P@.epD2M@I@_G_kidFactsA O hR0 (n + 1))
    (by first | decide | decide +kernel) @P@.epD2M@I@_C_callArgs
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (@P@.epD2M@I@_C_outChars o ho)) @P@.epD2M@I@_C_outScalar
    (@P@.epD2M@I@_C_hsep O hR0) entry
    (fun _ _ hA' => @P@.epD2M@I@_C_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0))
theorem _root_.@P@.epD2M@I@_C_hgk (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape) :
    ∀ (k : Nat) (hk : k < @C@.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      RealChildA O (@C@.machineData.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ∈ [Sparkle.IR.ModuleName.ofDecl ``@G@] ∧
        ∀ mn i conns, Sparkle.IR.AST.Stmt.inst mn i conns ∈ g.body → mn ∈ [Sparkle.IR.ModuleName.ofDecl ``@G@] := by
  intro k hk y' hy g hg
  rw [@P@.epD2M@I@_C_insts_G k hk] at hy
  have hI := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O @G@.machineData @G@.machine_ok @G@.machine_body
    (by decide) (by decide) hR0 (fun mc cc => @G@.machine_closes mc _ cc _) hy
  rcases List.mem_cons.mp hg with e | hin
  · subst e
    refine ⟨by rw [hI.name]; exact List.mem_singleton_self _, fun mn i conns hm => ?_⟩
    have := List.all_eq_true.mp hI.seqOk _ hm
    simp [Sparkle.IR.OptCheck.seqStmtOk] at this
  · rw [hI.design] at hin
    cases hin

theorem _root_.@P@.epD2M@I@_C_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)
    {y : Tools.ShippingChildInv.Res} (h : RealChildA O ``@C@ y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``@C@) (Tools.ShippingMachineEntry.machNIn @C@.machineData.shape)
      (@C@.machineData.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl ``@G@] y.1 y.2 :=
  Tools.ShippingSeqChildDeepIfacePA.deepChild_ifaceP O T @C@.machineData @C@.machine_ok @C@.machine_body (nDecl := @KC@)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun h0 => absurd (congrArg List.length h0) (by decide)) @KC@
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    _ (@P@.epD2M@I@_C_hgk O hR0) (@P@.epD2M@I@_C_hsep O hR0) entry
    (fun _ _ hA' => @P@.epD2M@I@_C_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0)) h

def _root_.@P@.epD2M@I@_C_Bnd (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State) :
    Lean.Meta.Context → Lean.Core.Context → Void IO.RealWorld → Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Prop :=
  fun mctx cctx _ _ _ =>
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape

instance _root_.@P@.epD2M@I@_C_inhab : Inhabited (HList (Tools.ShippingMachineDenote.tys @C@.machineData.ss)) :=
  oldInst% (Inhabited (HList (Tools.ShippingMachineDenote.tys @C@.machineData.ss))) @C@.machine_composedNR1
    Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA


theorem _root_.@P@.epD2M@I@_C_hcausal : HCausalOf @C@.machineData (fun i => i) @C@.machineExt @C@.machineExtB :=
  fun i bools bits S S' t h =>
  @C@.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
    (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)

theorem _root_.@P@.epD2M@I@_C_traceXA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``@C@ [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O ``@C@ @C@.machineData.shape m design)
      ``@C@ @C@.machineData m design (fun i => i) @C@.machineSource
      (fun i bools bits => @C@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @C@.machineInits (@C@.machineBody i bools bits)))
      (fun i bools bits => @C@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @C@.machineInits (@C@.machineBody i bools bits)))
      (letObsB @C@.machineData (fun i => i) @C@.machineInits
        @C@.machineBody @C@.machineExt @C@.machineExtB) :=
  Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA @C@.machineData
    (fun i => i) @C@.machineInits @C@.machineBody @C@.machineResult
    @C@.machineExt @C@.machineExtB @C@.machineSource @C@.machine_ok @C@.machine_body @C@.machine_inits
    @C@.machine_writes @C@.machine_result @C@.machine_source @P@.epD2M@I@_C_hcausal
    O (bodyStepC_of_tele O T) hA (n := D₀ + 1) (htr_of_tele O hA T D₀) (m := m) (design := design)
    (machineRunJQC_of_closesA O hA hcore entry (@P@.epD2M@I@_C_closesA O T hA hR0) hw hc)

theorem _root_.@P@.epD2M@I@_C_hcalls (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
    HCallsOf 1 @C@.machineData design m (dom := fun i => i)
      (letObsB @C@.machineData (fun i => i) @C@.machineInits @C@.machineBody @C@.machineExt @C@.machineExtB)
      (fun i bools bits => @C@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @C@.machineInits (@C@.machineBody i bools bits)))
      (fun i bools bits => @C@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @C@.machineInits (@C@.machineBody i bools bits)))
      @KC@
      (fun n => if n = ``@G@ then @G@.machineData.bsIn else [])
      (fun n => if n = ``@G@ then @G@.machineData.shape.layout.outs else [])
      (fun i n => if n = ``@G@ then fun vals => @G@.machineSource i
        (Tools.ShippingMachineChild.boolsOf @G@.machineData.bsIn vals)
        (Tools.ShippingMachineChild.bitsOf @G@.machineData.bsIn vals) else fun vals => [])
      (fun n => if n = ``@G@ then (fun mc => Tools.ShippingGateChild.MachineRun ``@G@ @G@.machineData.shape mc)
        else (fun mc => Tools.ShippingGateChild.MachineRun ``@G@ @G@.machineData.shape mc)) :=
  (old_seqparent% hcalls @C@) m design

theorem _root_.@P@.epD2M@I@_C_composedA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``@C@ [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape) :
    Tools.ShippingMachineDepthRun.ComposedNW 1 ``@C@ @C@.machineData @KC@ m design
      (fun i => i) @C@.machineSource
      (fun i bools bits => @C@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @C@.machineInits (@C@.machineBody i bools bits)))
      (fun i bools bits => @C@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @C@.machineInits (@C@.machineBody i bools bits))) := by
  have h := @P@.epD2M@I@_C_traceXA O T hA hR0 hw hc hcore entry
  exact machine_linkedT_callsRNA 1 O h (by first | decide | decide +kernel) @KC@ (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun n => if n = ``@G@ then @G@.machineData.bsIn else [])
    (fun n => if n = ``@G@ then @G@.machineData.shape.layout.outs else [])
    (fun i n => if n = ``@G@ then fun vals => @G@.machineSource i
        (Tools.ShippingMachineChild.boolsOf @G@.machineData.bsIn vals)
        (Tools.ShippingMachineChild.bitsOf @G@.machineData.bsIn vals) else fun vals => [])
    (fun n => if n = ``@G@ then (fun mc => Tools.ShippingGateChild.MachineRun ``@G@ @G@.machineData.shape mc)
        else (fun mc => Tools.ShippingGateChild.MachineRun ``@G@ @G@.machineData.shape mc))
    (@P@.epD2M@I@_C_hcalls m design)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < @C@.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = ``@G@ := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        rw [← Option.some.inj hc']
        exact @P@.epD2M@I@_C_insts_G k hk
      subst hck
      have hmr : Tools.ShippingGateChild.MachineRun ``@G@ @G@.machineData.shape mc :=
        ⟨mctx', mref, cctx', cref, w1, w2, Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx hR0,
          @G@.machine_closes mctx' _ cctx' _⟩
      split <;> exact hmr)

theorem _root_.@P@.epD2M@I@_C_seqChildRunN2 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {mc : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (h : Tools.ShippingMachineDepthRunRA.MachineRunNCA O ``@C@ @C@.machineData.shape (@P@.epD2M@I@_C_Bnd mref cref) mc design) :
    Tools.ShippingMachineDepth.SeqChildRunN (childMap design.modules) design 2 mc (List.take @KC@ @C@.machineData.bsIn)
      @C@.machineData.shape.layout.outs
      (fun vals => @C@.machineSource Sparkle.Core.Domain.defaultDomain
        (Tools.ShippingMachineChild.boolsOf (List.take @KC@ @C@.machineData.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take @KC@ @C@.machineData.bsIn) vals)) :=
  Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA O 1 (@P@.epD2M@I@_C_Bnd mref cref)
    (fun hcore hadm hjqc entry _ hB => @P@.epD2M@I@_C_composedA O T hadm hB hjqc.1 (Or.inr hjqc.2) hcore entry)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (oldNamed% (∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
        (bits : Nat → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j : Nat), j < @KC@ →
        @C@.machineExtB i bools bits (Tools.ShippingMachineSource.stateLoop @C@.machineInits (@C@.machineBody i bools bits)) j = bools j)
      @C@.seq_child_runN_ofR1 Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC hextB)
    (oldNamed% (∀ (i : Sparkle.Core.Domain.DomainConfig) (bools : Nat → Sparkle.Core.Signal.Signal i Bool)
        (bits : Nat → (n : Nat) → Sparkle.Core.Signal.Signal i (BitVec n)) (j n' : Nat), j < @KC@ →
        @C@.machineExt i bools bits (Tools.ShippingMachineSource.stateLoop @C@.machineInits (@C@.machineBody i bools bits)) j n' = bits j n')
      @C@.seq_child_runN_ofR1 Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC hext)
    Sparkle.Core.Domain.defaultDomain h
"#

/-- Parent level, part 1: the callee-dispatch families and the data facts about the parent's call instances. -/
def pHead : String := r#"
noncomputable def _root_.@P@.epD2M_calleeAt (k : Nat) : Name :=
  ((@P@.machineData.shape.insts[k]?).map (·.1)).getD Name.anonymous

theorem _root_.@P@.epD2M_calleeAt_eq (k : Nat) (hk : k < @P@.machineData.shape.insts.length) :
    @P@.epD2M_calleeAt k = (@P@.machineData.shape.insts[k]).1 := by
  simp [@P@.epD2M_calleeAt, List.getElem?_eq_getElem hk]

@DISPDEFS@

theorem _root_.@P@.epD2M_callees : @P@.machineData.shape.insts.map (·.1) = @CALLEES@ := by
  first | decide | decide +kernel

theorem _root_.@P@.epD2M_mem : ∀ c ∈ @P@.machineData.shape.insts.map (·.1), @ORC@ := by
  first | decide | decide +kernel

/-- An origin without a memory key builds no child (so a call-field origin, whatever its field index, is `KidTA`'s second disjunct). -/
theorem _root_.@P@.epD2M_origin_child_none (o : Sparkle.Compiler.MachInstOrigin.InstOrigin)
    (h : Tools.ShippingMemCloses.memKey o = none) : o.child? = none := by
  cases o with
  | ord => rfl
  | field _ => rfl
  | mem c a d => exact absurd h (by simp [Tools.ShippingMemCloses.memKey])

theorem _root_.@P@.epD2M_insts_C : ∀ (k : Nat) (hk : k < @P@.machineData.shape.insts.length),
    (@ORK@) ∧ Tools.ShippingMemCloses.memKey (originAt @P@.machineData.shape k) = none := by
  first | decide | decide +kernel

theorem _root_.@P@.epD2M_ne : ∀ k : Nat, k < @P@.machineData.shape.insts.length →
    @P@.epD2M_calleeAt k ≠ ``@P@ ∧ @P@.epD2M_leafOf (@P@.epD2M_calleeAt k) ≠ ``@P@ := by
  first | decide | decide +kernel

theorem _root_.@P@.epD2M_disj : ∀ k : Nat, k < @P@.machineData.shape.insts.length →
    ∀ k' : Nat, k' < @P@.machineData.shape.insts.length →
    @P@.epD2M_calleeAt k ≠ @P@.epD2M_calleeAt k' →
    (@P@.epD2M_calleeAt k ≠ @P@.epD2M_leafOf (@P@.epD2M_calleeAt k') ∧
     @P@.epD2M_leafOf (@P@.epD2M_calleeAt k) ≠ @P@.epD2M_leafOf (@P@.epD2M_calleeAt k')) := by
  first | decide | decide +kernel

theorem _root_.@P@.epD2M_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk @P@.machineData @KP@ @KI@ = true := by
  first | decide | decide +kernel

theorem _root_.@P@.epD2M_callWidths :
    Tools.ShippingCallWidths.callWidthsOk @P@.machineData @KP@ @KO@ = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem _root_.@P@.epD2M_outChars : ∀ o ∈ @P@.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem _root_.@P@.epD2M_outScalar : ∀ o ∈ @P@.machineData.shape.layout.outs,
    Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel

theorem _root_.@P@.epD2M_closesA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    @HB@
    :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``@P@ @P@.machineData.shape := by
  have hent := @P@.epD2M_insts_C
  have hkid : ∀ (k : Nat) (hk : k < @P@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (originAt @P@.machineData.shape k)
        (@P@.machineData.shape.insts[k]).1 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl (@P@.epD2M_calleeAt k)) (@P@.epD2M_nInOf (@P@.epD2M_calleeAt k))
        ((@P@.epD2M_outsOf (@P@.epD2M_calleeAt k)).map (·.name))
        [Sparkle.IR.ModuleName.ofDecl (@P@.epD2M_leafOf (@P@.epD2M_calleeAt k))] y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, ho⟩ := hent k hk
    unfold Tools.ShippingCallsMemA.KidTA at hy
    rw [@P@.epD2M_origin_child_none _ ho] at hy
    rcases hy with hy | ⟨-, hre⟩
    · exact absurd hy (by show (none : Option _) ≠ some y; exact fun h => nomatch h)
    · rw [@P@.epD2M_calleeAt_eq k hk]
      rcases hn with @HNPAT@
@KIDBRANCHES@
  intro tenv
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := @KP@) O T hA @P@.machineData
    @P@.machine_ok @P@.machine_body (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun k => Sparkle.IR.ModuleName.ofDecl (@P@.epD2M_calleeAt k)) (fun k => @P@.epD2M_nInOf (@P@.epD2M_calleeAt k))
    (fun k => (@P@.epD2M_outsOf (@P@.epD2M_calleeAt k)).map (·.name))
    (fun k => [Sparkle.IR.ModuleName.ofDecl (@P@.epD2M_leafOf (@P@.epD2M_calleeAt k))])
    hkid (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun k hk k' hk' h => by
      have e := Tools.ShippingModuleName.ofDecl_injective h
      rw [@P@.epD2M_calleeAt_eq k hk, @P@.epD2M_calleeAt_eq k' hk'] at e
      exact ⟨e, by rw [(hent k hk).2, (hent k' hk').2]⟩)
    (fun k hk => Tools.ShippingModuleName.ofDecl_ne (@P@.epD2M_ne k hk).1)
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by first | decide | decide +kernel :
        ∀ o ∈ @P@.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi _)
    (fun k hk hx => Tools.ShippingModuleName.ofDecl_ne (@P@.epD2M_ne k hk).2 (List.mem_singleton.mp hx).symm)
    (fun k hk k' hk' hn => by
      have hne : @P@.epD2M_calleeAt k ≠ @P@.epD2M_calleeAt k' := fun e =>
        hn ⟨(@P@.epD2M_calleeAt_eq k hk).symm.trans (e.trans (@P@.epD2M_calleeAt_eq k' hk')),
          by rw [(hent k hk).2, (hent k' hk').2]⟩
      obtain ⟨h1, h2⟩ := @P@.epD2M_disj k hk k' hk' hne
      refine ⟨fun hmem => Tools.ShippingModuleName.ofDecl_ne h1 (List.mem_singleton.mp hmem), fun x hx hx' => ?_⟩
      simp only [List.mem_singleton] at hx hx'
      subst hx
      exact Tools.ShippingModuleName.ofDecl_ne h2 hx')

theorem _root_.@P@.epD2M_hkid (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    @HB@
    :
    ∀ (k : Nat) (hk : k < @P@.machineData.shape.insts.length),
      Tools.ShippingSeqChildDeepKidFactsA.KidFactsA O (@P@.machineData.shape.insts[k]).1
        (@P@.epD2M_outsOf (@P@.epD2M_calleeAt k)) (@P@.epD2M_widthsOf (@P@.epD2M_calleeAt k)) (n + 1) := by
  intro k hk
  rw [@P@.epD2M_calleeAt_eq k hk]
  rcases (@P@.epD2M_insts_C k hk).1 with @HNPAT@
@HKIDBRANCHES@

"#

/-- Parent level, part 2: the endpoint pieces whose text only differs from the one-callee path by the hypotheses and families. -/
def pMid : String := r#"
theorem _root_.@P@.epD2M_ranA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    @HB@
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``@P@ [] false)
      mctx mref cctx cref w (raw, D) w1)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@P@ @P@.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx ``@P@ @P@.machineData.shape raw D :=
  Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (@P@.epD2M_closesA O T hA @HA@) hw hc

theorem _root_.@P@.epD2M_runFacts (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    @HB@
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``@P@ [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@P@ @P@.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  Tools.ShippingSeqParentKidFactsA.kidsA_runFacts O @P@.machineData @P@.machine_ok @P@.machine_body
    (nDecl := @KP@) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    @KO@ @KI@ (n + 1)
    (@P@.epD2M_hkid O T n @HA@) @P@.epD2M_callWidths hpost (@P@.epD2M_ranA O T hA @HA@ hcore entry hw hc)

theorem _root_.@P@.epD2M_outsCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    @HB@
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``@P@ [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@P@ @P@.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) (n + 1) (checkedOptimize b) = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_outsCheck O @P@.machineData @P@.machine_ok @P@.machine_body
    (nDecl := @KP@) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    @KO@ @KI@ (n + 1)
    (@P@.epD2M_hkid O T n @HA@) hpost (@P@.epD2M_ranA O T hA @HA@ hcore entry hw hc)
    (@P@.epD2M_runFacts O T n hA @HA@ hcore hpost entry hw hc).gate

theorem _root_.@P@.epD2M_kidsMasked (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    @HB@
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``@P@ [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@P@ @P@.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    Tools.ShippingMachineShipsDepth.kidsMaskedN D.modules b.body = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_maskedN O @P@.machineData @P@.machine_ok @P@.machine_body
    (nDecl := @KP@) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    @KO@ @KI@ (n + 1)
    (@P@.epD2M_hkid O T n @HA@) hpost (@P@.epD2M_ranA O T hA @HA@ hcore entry hw hc)

theorem _root_.@P@.epD2M_designCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    @HB@
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``@P@ [] false)
      mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@P@ @P@.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) (n + 1) (checkedOptimize b) = true :=
  Tools.ShippingSeqParentKidFactsA.kidsA_designCheck O @P@.machineData @P@.machine_ok @P@.machine_body
    (nDecl := @KP@) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    @KO@ @KI@ (n + 1)
    (@P@.epD2M_hkid O T n @HA@) @P@.epD2M_callWidths @P@.epD2M_callArgs hpost (@P@.epD2M_ranA O T hA @HA@ hcore entry hw hc)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (@P@.epD2M_outChars o ho)) @P@.epD2M_outScalar
"#

/-- Parent level, part 3: the instance / causality data, the trace, soundness, composition and the boundary. -/
def pTail : String := r#"
instance _root_.@P@.epD2M_inhab : Inhabited (HList (Tools.ShippingMachineDenote.tys @P@.machineData.ss)) :=
  oldInst% (Inhabited (HList (Tools.ShippingMachineDenote.tys @P@.machineData.ss))) @P@.machine_composedNR2
    Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA

theorem _root_.@P@.epD2M_hcausal : HCausalOf @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
    @P@.machineExt @P@.machineExtB := fun i bools bits S S' t h =>
  @P@.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
    (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)

theorem _root_.@P@.epD2M_traceXA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    @HB@
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``@P@ [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``@P@ @P@.machineData.shape) :
    Tools.ShippingMachineTraceX.MachineTraceLBX
      (ServedRealA O ``@P@ @P@.machineData.shape m design)
      ``@P@ @P@.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineSource
      (fun i bools bits => @P@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
      (fun i bools bits => @P@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
      (letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits
        @P@.machineBody @P@.machineExt @P@.machineExtB) :=
  Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA @P@.machineData
    (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits @P@.machineBody @P@.machineResult
    @P@.machineExt @P@.machineExtB @P@.machineSource @P@.machine_ok @P@.machine_body @P@.machine_inits
    @P@.machine_writes @P@.machine_result @P@.machine_source @P@.epD2M_hcausal
    O (bodyStepC_of_tele O T) hA (n := D₀ + 1) (htr_of_tele O hA T D₀) (m := m) (design := design)
    (machineRunJQC_of_closesA O hA hcore entry (@P@.epD2M_closesA O T hA @HA@) hw hc)

theorem _root_.@P@.epD2M_soundLA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    @HB@
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``@P@ [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``@P@ @P@.machineData.shape) :
    Tools.ShippingMachineAuto.MachineTraceLB ``@P@ @P@.machineData m design (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
      @P@.machineSource
      (fun i bools bits => @P@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
      (fun i bools bits => @P@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
      (letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits
        @P@.machineBody @P@.machineExt @P@.machineExtB) := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, -, tr⟩ :=
    @P@.epD2M_traceXA O T hA @HA@ hw hc hcore entry
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, tr⟩

theorem _root_.@P@.epD2M_houtTy : ∀ o ∈ @P@.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

theorem _root_.@P@.epD2M_composedA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    @HB@
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``@P@ [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``@P@ @P@.machineData.shape) :
    ComposedG (fun D => KSn (childMap D.modules) 2) (ResetNk 2) ``@P@ @P@.machineData @KP@ m design
      (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineSource
      (fun i bools bits => @P@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
      (fun i bools bits => @P@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits))) := by
  have h := @P@.epD2M_traceXA O T hA @HA@ hw hc hcore entry
  refine Tools.ShippingMachineShipsDepth.composedG_of_NW ?_
  exact machine_linkedT_callsRNA 2 O h (by first | decide | decide +kernel) @KP@ (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    @P@.epD2M_bsF @P@.epD2M_outsOf @P@.epD2M_srcF (@P@.epD2M_PC O design)
    (fun i bools bits k c hk => by
      have hk2 : @CALLEES@[k]? = some c := by
        rw [← @P@.epD2M_callees]; exact hk
      have hlt : k < @MP@ := by
        have := (List.getElem?_eq_some_iff.mp hk2).1; simpa using this
      -- the group facts of the generated proof that do not mention the child predicate: one bundle per distinct (callee, argument list)
@GROUPFACTS@
      right
      unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
      rcases k with @MPAT@
@CASES@
      · omega)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      rcases @P@.epD2M_mem c (List.mem_of_getElem? hc') with @CPAT@
@RUNBRANCHES@)

def _root_.@P@.epD2M_Bnd : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
@BNDDEFS@
    ∃ D₀, JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA O (cv w))
"#

/-- The term of the endpoint: `machine_design_noShips_noBd_dc` at `n := 2`, `C := True`, applied to the generated pieces. -/
def endpointTermM : String := r#"(@Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc 2 @P@.epD2M_Bnd (fun _ _ _ _ => True)
    ``@P@ @P@.machineData @KP@ Unit (fun _ => Sparkle.Core.Domain.defaultDomain) _ _ _ _ _ _ _
    (fun hcore entry _ hB => by
      obtain @OBT@ := hB
      exact @P@.epD2M_soundLA O T hA @HA@ hw hc hcore entry)
    (fun hcore entry _ hB _ => by
      obtain @OBT@ := hB
      exact @P@.epD2M_composedA O T hA @HA@ hw hc hcore entry)
    @P@.epD2M_houtTy
    (fun hcore hpost entry hB => by
      obtain @OBT@ := hB
      exact @P@.epD2M_runFacts O T 1 hA @HA@ hcore hpost entry hw hc)
    (fun hcore hpost entry _ hB => by
      obtain @OBT@ := hB
      exact @P@.epD2M_outsCheck O T 1 hA @HA@ hcore hpost entry hw hc)
    (fun hcore hpost entry hB => by
      obtain @OBT@ := hB
      exact @P@.epD2M_kidsMasked O T 1 hA @HA@ hcore hpost entry hw hc)
    (fun hcore hpost entry hB => by
      obtain @OBT@ := hB
      exact @P@.epD2M_designCheck O T 1 hA @HA@ hcore hpost entry hw hc))"#


/-! ## class analysis: every refusal has a stated reason -/

/-- The data the several-callee template is instantiated with: callee `i` is `Cs[i]` with leaf `Gs[i]`. -/
structure D2MParams where
  P : Name
  Cs : List Name
  Gs : List Name
  /-- own input ports of each callee -/
  kCs : List Nat
  /-- declared widths of each leaf's arguments -/
  gws : List (List Nat)
  /-- number of output fields of each callee -/
  nOutsCs : List Nat
  kP : Nat
  mP : Nat
  /-- the DISTINCT (callee index, argument list) keys of the parent's calls, in order of first occurrence (= the group index of the old generated `hcalls`) -/
  groups : List (Nat × List Nat)
  /-- per call instance of `P`, the index of its group -/
  instGroup : List Nat
  /-- per call instance of `P`, the index of its callee -/
  instCallee : List Nat
  /-- diagnostic: how the partition read from the old term compares with the recomputed approximation -/
  partitionNote : String
deriving Repr

def refuseM {α : Type} (fn : Name) (why : String) : CommandElabM α :=
  throwError "#machine_seq_parent_endpoint (unit SR3w, depth 2, several callees): REFUSED `{fn}`: {why}"

/-- The keys of the calls of `fn`, one per instance, as READ from `fn.machineExt` / `fn.machineExtB` (a CALL-ARGUMENT APPROXIMATION of the old
generator's key): `(callee of THIS instance, argument lets, the call's arguments)`; see `Tools.ShippingSeqParentGenD2.oldGroupKeyList`. -/
def oldGroupKeyListM (fn : Name) (cs : List Name) (kP : Nat) (al : List (List Nat)) :
    MetaM (Except String (List (Name × List Nat × List Expr))) := do
  let env ← getEnv
  let some _ := env.find? (fn ++ `machineExt) | return .error s!"{fn ++ `machineExt} not found"
  let ext ← mkConstWithFreshMVarLevels (fn ++ `machineExt)
  let extB? ← if env.contains (fn ++ `machineExtB) then some <$> mkConstWithFreshMVarLevels (fn ++ `machineExtB) else pure none
  forallBoundedTelescope (← inferType ext) (some 4) fun ibb _ => do
    unless ibb.size == 4 do return .error s!"{fn ++ `machineExt} does not start with the four binders (i, bools, bits, state)"
    let unfoldExt (c : Expr) : MetaM Expr := do
      let e ← whnfCore (mkAppN c ibb).headBeta
      if let .const n _ := e.getAppFn then
        if let some v := env.find? n >>= (·.value?) then
          return (v.beta e.getAppArgs).headBeta
      pure e
    let extBody ← unfoldExt ext
    let extBBody ← match extB? with | some x => unfoldExt x | none => pure extBody
    let mut keys : Array (Name × List Nat × List Expr) := #[]
    for ((a, k), C) in al.zipIdx.zip cs do
      let pos := kP + k
      let some sig := (Tools.ShippingMachineSeqCommand.sigAtPos pos extBody).orElse fun _ => Tools.ShippingMachineSeqCommand.sigAtPos pos extBBody
        | return .error s!"call instance {k}: no argument Signal at port {pos} of {fn ++ `machineExt}"
      let some call := Tools.ShippingMachineSeqCommand.findCall C sig
        | return .error s!"call instance {k}: no call of {C} in the Signal at port {pos}"
      keys := keys.push (C, a, (← instantiateMVars call).getAppArgs.toList)
    return .ok keys.toList

/-- Per instance its group index, per group its (callee, argument list): the first-occurrence partition (`Tools.ShippingSeqParentGenD2.groupPartition`)
of the keys. -/
def oldGroupKeysM (fn : Name) (cs : List Name) (kP : Nat) (al : List (List Nat)) :
    MetaM (Except String (List Nat × List (Name × List Nat))) := do
  match ← oldGroupKeyListM fn cs kP al with
  | .error why => return .error why
  | .ok keys =>
    let (inst, ks) := Tools.ShippingSeqParentGenD2.groupPartition keys
    return .ok (inst, ks.map fun (c, a, _) => (c, a))

def analyseM (fn : Name) : CommandElabM D2MParams := do
  let env ← getEnv
  let nat := fun (s : String) (n : Name) => liftTermElabM do reduceNat (← elabText (s.replace "@F@" n.toString))
  let calleesOf := fun (n : Name) => liftTermElabM do readNames (← elabText (s!"({n}.machineData.shape.insts.map (·.1))"))
  let pc ← calleesOf fn
  if pc.isEmpty then refuseM fn "no call instance"
  if pc.any isMemName then refuseM fn (memWhy "P" fn)
  let Cs := pc.eraseDups
  let mut Gs : Array Name := #[]
  for C in Cs do
    unless env.contains (C ++ `machineData) do refuseM fn s!"the callee {C} is not a generated machine (no {C ++ `machineData})"
    let cc ← calleesOf C
    if cc.isEmpty then
      refuseM fn s!"the callee {C} is a LEAF (no call instance of its own) next to callees with calls: a MIXED parent (sequential leaf next to a depth-2 callee) is OPEN on this path (the child predicate of the old chain would mix `MachineRun` and `MachineRunNCA`, and no parent-side interface / KidFactsA is instantiated for a leaf next to a deep callee)"
    if cc.any isMemName then refuseM fn (memWhy "C" C)
    let ccs := cc.eraseDups
    unless ccs.length == 1 do
      refuseM fn s!"the callee {C} calls {ccs.length} DIFFERENT grandchildren {ccs}; this path takes ONE leaf grandchild per callee (OPEN: several)"
    let G := ccs.head!
    unless env.contains (G ++ `machineData) do refuseM fn s!"the grandchild {G} is not a generated machine"
    let gc ← calleesOf G
    if gc.any isMemName then refuseM fn (memWhy "G" G)
    let gi ← nat "@F@.machineData.shape.insts.length" G
    unless gi == 0 do
      refuseM fn s!"the grandchild {G} of {C} has {gi} call instance(s) of its own: depth 3, OPEN (no depth-3 interface/closing lemma on the new boundary)"
    Gs := Gs.push G
  -- the leaves must be pairwise different, and different from every callee and from the parent
  for G in Gs.toList do
    if Gs.toList.count G > 1 then
      let who := (Cs.zip Gs.toList).filter (·.2 == G) |>.map (·.1)
      refuseM fn s!"the callees {who} call the SAME leaf {G}: the closing lemma `Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids'` has the premise `hdisjD` (the module-name sets of two DIFFERENT call classes must be disjoint), which is FALSE when both contain {G}; the step that FAILS (unit SR3x): the last obligation of that closing is that a module of callee i's result and a module of callee j's result with one name are EQUAL; the children are `KidTA`/`RealChildA` values, i.e. results of PAST runs of `synthesizeCombinational`, and no law of `RefLawsAOps` or invariant relates two such runs (two compiles of {G} are not known equal); a premise stating it would be that obligation itself (a restated premise, not a lemma) and could not be discharged for {G} (OPEN)"
    if Cs.contains G then refuseM fn s!"the leaf {G} is also a callee of the parent: `hdisjD` of `machineClosesAtA_of_memKids'` cannot hold (OPEN)"
    if G == fn then refuseM fn s!"the leaf {G} is the parent itself"
  let al ← liftTermElabM do readNatLists (← elabText s!"({fn}.machineData.shape.insts.map (·.2.1))")
  let kP ← nat "(@F@.machineData.bsIn.length - @F@.machineData.shape.insts.length)" fn
  let oldThm := fn ++ `machine_composedNR2
  unless env.contains oldThm do
    refuseM fn s!"{oldThm} not found (the class needs the old generated chain: `#machine_design_svNR {fn} 2`, which also generates the child pieces)"
  -- (unit SR3w, per review) the numbering is READ from the old generated `hcalls`; the recomputed call-argument approximation is a diagnostic only
  let instGroup ← match ← liftTermElabM <| Tools.ShippingSeqParentGenD2.oldInstGroups oldThm with
    | .ok og => pure og
    | .error why => refuseM fn s!"the partition of the instances into groups cannot be read from the old generated {oldThm}: {why}"
  unless instGroup.length == al.length do
    refuseM fn s!"the old generated {oldThm} has {instGroup.length} call entries but {fn} has {al.length} call instances"
  let some groupKeys := Tools.ShippingSeqParentGenD2.groupKeysOf instGroup (pc.map Cs.idxOf |>.zip al)
    | refuseM fn s!"the old generated {oldThm} groups the instances as {instGroup}, but the instances of one group do not have one (callee, argument list) (callees {pc}, argument lists {al})"
  let groups := groupKeys
  let partitionNote : String ← match ← liftTermElabM <| oldGroupKeysM fn pc kP al with
    | .ok (inst, _) => pure (if inst == instGroup then "the recomputed call-argument approximation of the old key gives the same partition" else s!"the recomputed call-argument approximation of the old key gives a DIFFERENT partition {inst} (the old term's numbering is used)")
    | .error why => pure s!"the call-argument approximation of the old key was not computed ({why})"
  for (n, ss) in [(fn, [`machine_composedNR2, `machine_ok, `machine_body, `machine_inits, `machine_writes, `machine_result, `machine_source,
        `machine_ext_causal, `machineSource, `machineInits, `machineBody, `machineResult, `machineExt, `machineExtB, `machineData])] ++
      Cs.map (fun C => (C, [`machine_composedNR1, `machine_ok, `machine_body, `machine_inits, `machine_writes, `machine_result, `machine_source,
        `machine_ext_causal, `machineSource, `machineInits, `machineBody, `machineResult, `machineExt, `machineExtB, `machineData,
        `seq_child_runN_ofR1])) ++
      Gs.toList.map (fun G => (G, [`machine_ok, `machine_body, `machine_closes, `machineSource, `machineData])) do
    for s in ss do
      unless env.contains (n ++ s) do
        refuseM fn s!"{n ++ s} not found (the class needs the old generated chain: `#machine_design_svNR {fn} 2`, which also generates the child pieces)"
  let nOld ← liftTermElabM <| Tools.ShippingSeqParentGenD2.oldGroupCount oldThm
  unless nOld == groups.length do
    refuseM fn s!"the old generated {oldThm} has {nOld} group(s) of facts but its entries use {groups.length} group(s)"
  let ip ← liftTermElabM <| sourceIndex fn
  unless ip == ``Unit || ip == ``PUnit do refuseM fn s!"the parent's machineSource is indexed by {ip}, expected Unit (a top-level, non-polymorphic machine)"
  let mut kCs : Array Nat := #[]
  let mut gws : Array (List Nat) := #[]
  let mut nOuts : Array Nat := #[]
  for (C, G) in Cs.zip Gs.toList do
    let ic ← liftTermElabM <| sourceIndex C
    unless ic == `Sparkle.Core.Domain.DomainConfig do
      refuseM fn s!"the callee {C}'s machineSource is indexed by {ic}, expected DomainConfig (a hardware module with a `dom : DomainConfig` binder); a callee that is not domain polymorphic is OPEN on this path"
    for n in [fn, C] do
      let nf ← nat "@F@.machineData.shape.instFields.length" n
      if nf == 0 then
        refuseM fn s!"{n} has no instField: its calls are one-output COMBINATIONAL children, not the sequential calls of this path"
    kCs := kCs.push (← nat "(@F@.machineData.bsIn.length - @F@.machineData.shape.insts.length)" C)
    nOuts := nOuts.push (← nat "@F@.machineData.shape.layout.outs.length" C)
    gws := gws.push (← liftTermElabM do readNats (← elabText s!"(Tools.ShippingPortWidthsPure.declWidths {G}.machineData)"))
  let mP ← nat "@F@.machineData.shape.insts.length" fn
  return { P := fn, Cs := Cs, Gs := Gs.toList, kCs := kCs.toList, gws := gws.toList, nOutsCs := nOuts.toList, kP := kP, mP := mP,
           groups := groups, instGroup := instGroup, instCallee := pc.map Cs.idxOf, partitionNote := partitionNote }

/-! ## text assembly -/

/-- Substitute the data of callee `i` for `@I@ @C@ @G@ @KC@ @GW@`. -/
def sub1 (p : D2MParams) (i : Nat) (s : String) : String :=
  ((((s.replace "@I@" (toString i)).replace "@C@" (p.Cs.getD i .anonymous).toString).replace "@G@"
    (p.Gs.getD i .anonymous).toString).replace "@KC@" (toString (p.kCs.getD i 0))).replace "@GW@" (toString (p.gws.getD i []))

def rangeR (p : D2MParams) : List Nat := List.range p.Cs.length

def indentLines (n : Nat) (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").map fun l => "".pushn ' ' n ++ l)

/-- `if n = ``C0 then v0 else if n = ``C1 then v1 else d` (the values written with `@C@` etc.). -/
def chainS (p : D2MParams) (v : String) (d : String) : String :=
  (rangeR p).foldr (fun i acc => "if n = ``" ++ (p.Cs.getD i .anonymous).toString ++ " then " ++ sub1 p i v ++ " else " ++ acc) d

def dispDefs (p : D2MParams) : String :=
  let eqDefs : List (String × String × String × String) :=
    [("outsOf", "List Sparkle.IR.Machine.OutField", "@C@.machineData.shape.layout.outs", "[]"),
     ("widthsOf", "List Nat", "Tools.ShippingCallsChildPorts.argWidths @C@.machineData @KC@", "[]"),
     ("nInOf", "Nat", "Tools.ShippingMachineEntry.machNIn @C@.machineData.shape", "0"),
     ("leafOf", "Name", "``@G@", "Name.anonymous")]
  let one := fun (f, ty, v, d) =>
    let negs := fun (i : Nat) => "".intercalate (((List.range i).map fun j =>
      "if_neg (show ¬ ((``" ++ (p.Cs.getD i .anonymous).toString ++ " : Name) = ``" ++ (p.Cs.getD j .anonymous).toString ++ ") by decide), "))
    "noncomputable def _root_.@P@.epD2M_" ++ f ++ " (n : Name) : " ++ ty ++ " :=\n  " ++ chainS p v d ++ "\n\n" ++
    "\n".intercalate ((rangeR p).map fun i =>
      "theorem _root_.@P@.epD2M_" ++ f ++ "_" ++ toString i ++ " : @P@.epD2M_" ++ f ++ " ``" ++ (p.Cs.getD i .anonymous).toString ++ " = " ++ sub1 p i v ++ " := by\n  unfold @P@.epD2M_" ++ f ++ "\n  rw [" ++ negs i ++ "if_pos rfl]\n")
  let others :=
    "noncomputable def _root_.@P@.epD2M_bsF (n : Name) :=\n  " ++ chainS p "List.take @KC@ @C@.machineData.bsIn" "[]" ++ "\n\n" ++
    "noncomputable def _root_.@P@.epD2M_srcF (_i : Unit) (n : Name) : (Nat → List Nat) → List (Nat → Nat) :=\n  " ++
      chainS p "fun vals => @C@.machineSource Sparkle.Core.Domain.defaultDomain (Tools.ShippingMachineChild.boolsOf (List.take @KC@ @C@.machineData.bsIn) vals) (Tools.ShippingMachineChild.bitsOf (List.take @KC@ @C@.machineData.bsIn) vals)" "fun _ => []" ++ "\n\n" ++
    "noncomputable def _root_.@P@.epD2M_PC (O : RefLawsAOps MkRefd mref cref) (design : Sparkle.IR.AST.Design) (n : Name) (mc : Sparkle.IR.AST.Module) : Prop :=\n  " ++
      chainS p "Tools.ShippingMachineDepthRunRA.MachineRunNCA O ``@C@ @C@.machineData.shape (@P@.epD2M@I@_C_Bnd mref cref) mc design" "True" ++ "\n"
  "\n".intercalate (eqDefs.map one) ++ "\n" ++ others

def hypBinders (p : D2MParams) : String :=
  "\n    ".intercalate ((rangeR p).map fun i => sub1 p i
    "(hM@I@ : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)\n    (hR@I@ : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)")

def hypArgs (p : D2MParams) : String := " ".intercalate ((rangeR p).map fun i => s!"hM{i} hR{i}")

def obtainPat (p : D2MParams) : String :=
  "⟨O, T, hA, " ++ ", ".intercalate ((rangeR p).map fun i => s!"hM{i}, hR{i}") ++ ", D₀, hw, hc⟩"

def bndDefs (p : D2MParams) : String :=
  "\n".intercalate ((rangeR p).map fun i => sub1 p i
    "    MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape ∧\n    MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape ∧")

def orOf (p : D2MParams) (lhs : String) : String :=
  " ∨ ".intercalate ((rangeR p).map fun i => lhs ++ " = ``" ++ (p.Cs.getD i .anonymous).toString)

def patOf (p : D2MParams) (a : String) : String := " | ".intercalate ((rangeR p).map fun _ => a)

def calleesLit (p : D2MParams) : String :=
  "[" ++ ", ".intercalate (p.instCallee.map fun i => "``" ++ (p.Cs.getD i .anonymous).toString) ++ "]"

def kidBranches (p : D2MParams) : String :=
  "\n".intercalate ((rangeR p).map fun i => sub1 p i
    ("      · rw [hn] at hre ⊢\n        rw [@P@.epD2M_outsOf_@I@, @P@.epD2M_nInOf_@I@, @P@.epD2M_leafOf_@I@]\n        exact @P@.epD2M@I@_C_ifaceP O T hM@I@ hR@I@ hre"))

def hkidBranches (p : D2MParams) : String :=
  "\n".intercalate ((rangeR p).map fun i => sub1 p i
    ("  · rw [hn, @P@.epD2M_outsOf_@I@, @P@.epD2M_widthsOf_@I@]\n    exact @P@.epD2M@I@_C_kidFactsA O T n hM@I@ hR@I@"))

def runBranches (p : D2MParams) : String :=
  "\n".intercalate ((rangeR p).map fun i => sub1 p i
    ("      · exact Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main O T\n          (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons hM@I@\n          (fun mctx cctx _ w raw D _ => Tools.ShippingReflectCtx.MachineDefines.ctx hR@I@)\n          (fun mctx cctx w raw D hin _ => by\n            obtain ⟨_, _, _, hadm', _⟩ := hin\n            exact @P@.epD2M@I@_C_closesA O T hadm' (Tools.ShippingReflectCtx.MachineDefines.ctx hR@I@))\n          (by first | decide | decide +kernel)"))

/-- The cases of `epD2M_composedA`: instance `k` of the parent, from ITS callee's pieces and ITS group's facts. -/
def composedCases (p : D2MParams) : String :=
  let one (k : Nat) : String :=
    let ci := p.instCallee.getD k 0
    let g := p.instGroup.getD k 0
    let args := (p.groups.getD g (0, [])).2
    let alts := (List.range (p.nOutsCs.getD ci 0)).map fun K =>
      sub1 p ci (((("(refine ⟨rfl, @ARGS@, rfl, (fun mc hmc => ⟨@P@.epD2M@I@_C_seqChildRunN2 O T hmc, by rw [(@P@.epD2M@I@_C_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L@J@, R@J@, @K@, _, _, rfl, rfl, ?_, fun τ => rfl⟩; exact (congrArg (fun l => l[@K@]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (@C@.machineSource Sparkle.Core.Domain.defaultDomain) Hb@J@ Hv@J@)).trans rfl)"
        ).replace "@ARGS@" (toString args)).replace "@J@" (toString g)).replace "@K@" (toString K))
    "· have hck : c = ``" ++ (p.Cs.getD ci .anonymous).toString ++ " := by simpa using hk2.symm\n  subst hck\n  first\n" ++
      "\n".intercalate (alts.map fun a => "    | " ++ a)
  "\n".intercalate ((List.range p.mP).map fun k => indentLines 6 (one k))

/-- The group facts of every distinct (callee, argument list): group `j` = `gfL{j}` … of the old generated `hcalls`. -/
def groupFacts (p : D2MParams) : String :=
  "\n".intercalate ((p.groups.zipIdx.map fun ((ci, args), j) =>
    sub1 p ci ((groupFactsTmpl.replace "@J@" (toString j)).replace "@ARGS@" (toString args))))

def assembleM (p : D2MParams) : String :=
  let tcs := "\n".intercalate ((rangeR p).map fun i => sub1 p i tcTmpl)
  let pat := "".intercalate ((List.range p.mP).map fun _ => "_ | ") ++ "k"
  let ptxt := pHead ++ pMid ++ pTail
  let ptxt := ptxt.replace "@DISPDEFS@" (dispDefs p)
  let ptxt := ptxt.replace "@KIDBRANCHES@" (kidBranches p)
  let ptxt := ptxt.replace "@HKIDBRANCHES@" (hkidBranches p)
  let ptxt := ptxt.replace "@RUNBRANCHES@" (runBranches p)
  let ptxt := ptxt.replace "@GROUPFACTS@" (groupFacts p)
  let ptxt := ptxt.replace "@CASES@" (composedCases p)
  let ptxt := ptxt.replace "@BNDDEFS@" (bndDefs p)
  let ptxt := ptxt.replace "@HB@" (hypBinders p)
  let ptxt := ptxt.replace "@HA@" (hypArgs p)
  let ptxt := ptxt.replace "@HNPAT@" (patOf p "hn")
  let ptxt := ptxt.replace "@CPAT@" (patOf p "rfl")
  let ptxt := ptxt.replace "@ORC@" (orOf p "c")
  let ptxt := ptxt.replace "@ORK@" (orOf p "(@P@.machineData.shape.insts[k]).1")
  let ptxt := ptxt.replace "@CALLEES@" (calleesLit p)
  let ptxt := ptxt.replace "@KO@" "(fun k => @P@.epD2M_outsOf (@P@.epD2M_calleeAt k))"
  let ptxt := ptxt.replace "@KI@" "(fun k => @P@.epD2M_widthsOf (@P@.epD2M_calleeAt k))"
  let ptxt := ptxt.replace "@MPAT@" pat
  let ptxt := ptxt.replace "@MP@" (toString p.mP)
  let src := Tools.ShippingSeqParentGenD2.openBlock2 ++ tcs ++ ptxt
  (src.replace "@P@" p.P.toString).replace "@KP@" (toString p.kP)

def endpointSrc (p : D2MParams) : String :=
  (((endpointTermM.replace "@OBT@" (obtainPat p)).replace "@HA@" (hypArgs p)).replace "@P@" p.P.toString).replace "@KP@" (toString p.kP)

/-! ## audit of the generated endpoint -/

open Tests.Compiler.ChildVertAuditTest in
def auditM (p : D2MParams) (ep : Name) : MetaM Unit := do
  stdAxioms ep
  let ty := (← getConstInfo ep).type
  let premises ← forallTelescope ty fun xs _ => do
    let mut ps : Array String := #[]
    for x in xs do
      let t ← inferType x
      if (← isProp t) then ps := ps.push s!"{(← x.fvarId!.getUserName)} : {t.getAppFn.constName?.getD Name.anonymous}"
    return ps
  let expected := ["hr : Tools.ShippingEntrySoundness.RunsTo", "entry : Tools.ShippingMachineEntry.MachineDefines", "closes : True"]
  unless premises.toList == expected do throwError "SR3w AUDIT FAILED: outer Prop premises are {premises}, expected {expected}"
  let cl ← depClosure ep
  let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
    `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
    `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SR3w AUDIT FAILED: the forbidden name {f} does not exist (the audit would check nothing)"
  let bad := hits cl ++ cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "SR3w AUDIT FAILED: {ep}: old boundary / old child predicate in closure: {bad}"
  let pe := fun (s : String) => p.P ++ Name.mkSimple s
  let perCallee := (rangeR p).foldr (fun i acc => acc ++ [pe s!"epD2M{i}_C_composedA", pe s!"epD2M{i}_C_seqChildRunN2", pe s!"epD2M{i}_C_ifaceP",
      pe s!"epD2M{i}_C_kidFactsA", pe s!"epD2M{i}_C_closesA"]) []
  for must in [pe "epD2M_soundLA", pe "epD2M_composedA", pe "epD2M_traceXA", pe "epD2M_designCheck", pe "epD2M_runFacts", pe "epD2M_outsCheck",
      pe "epD2M_kidsMasked", pe "epD2M_closesA", pe "epD2M_hkid",
      ``Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA, ``Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA,
      ``Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main, ``Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA,
      ``Tools.ShippingParentRanA.machineRanA_main, ``Tools.ShippingMachineShipsDepth.composedG_of_NW,
      ``Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc] ++ perCallee do
    unless cl.contains must do throwError "SR3w AUDIT FAILED: {must} not in the closure of {ep}"
  for old in [p.P ++ `machine_composedNR2] ++ p.Cs.map (· ++ `machine_composedNR1) ++ p.Cs.map (· ++ `seq_child_runN_ofR1) do
    if cl.contains old then throwError "SR3w AUDIT FAILED: the old generated theorem {old} is in the closure of {ep}"
  let (_, concl) ← forallTelescope ty fun _ c => pure ((), c)
  let bnd := pe "epD2M_Bnd"
  unless (concl.find? (·.isConstOf bnd)).isSome do throwError "SR3w AUDIT FAILED: {bnd} not in the conclusion"
  let some bv := (← getConstInfo bnd).value? | throwError "SR3w AUDIT FAILED: {bnd} has no value"
  let mut defs : Array Name := #[]
  let mut todo : Array Expr := #[bv]
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if e.getAppFn.isConstOf ``Tools.ShippingMachineEntry.MachineDefines && e.getAppNumArgs == 6 then
      if let some a := e.getAppArgs[4]? then
        defs := defs.push (← Tools.ShippingSeqParentGen.readName a)
    match e with
    | .app f a => todo := todo.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | .mdata _ b => todo := todo.push b
    | _ => pure ()
  let want := (p.Cs ++ p.Gs).toArray
  unless defs.qsort (·.toString < ·.toString) == want.qsort (·.toString < ·.toString) do
    throwError "SR3w AUDIT FAILED: {bnd} asks MachineDefines for {defs}, expected exactly {want}"
  logInfo m!"SR3w AUDIT OK: {ep}: standard axioms; outer Prop premises ASSERTED {premises}; closure {cl.size} constants, none of ChildBnd/StartV/GenKid/old KidFacts/MachineRunNC/machineRunNC_of_real/seqChildRunN_of_composedC; the old generated theorems are not in the closure; {bnd} (an EXISTENTIAL over O/T/AdmCtx/MachineDefines of {p.Cs} and {p.Gs}/start world, not a proof that it holds) stays in the conclusion; chains {p.Cs.zip p.Gs}"

/-! ## the command (third elaborator) -/

open Tools.ShippingSeqParentGen in
@[command_elab Tools.ShippingSeqParentGen.«command#machine_seq_parent_endpoint_»]
def elabEndpointD2M : CommandElab := fun stx => do
  let f : Ident := ⟨stx[1]⟩
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  unless (← getEnv).contains (fn ++ `machineData) do throwUnsupportedSyntax
  let pc ← liftTermElabM do readNames (← elabText (s!"({fn}.machineData.shape.insts.map (·.1))"))
  -- dispatch: at least TWO different callees, at least one of which has call instances of its own
  unless pc.eraseDups.length ≥ 2 do throwUnsupportedSyntax
  let mut deep := false
  for c in pc.eraseDups do
    if (← getEnv).contains (c ++ `machineData) then
      let n ← liftTermElabM do reduceNat (← elabText s!"{c}.machineData.shape.insts.length")
      if n > 0 then deep := true
  unless deep do throwUnsupportedSyntax
  let p ← analyseM fn
  logInfo m!"SR3w: depth-2 class instance with {p.Cs.length} callees of {p.P}: {p.Cs.zip p.Gs} (kP {p.kP}, kC {p.kCs}); {p.mP} call instance(s) with (callee index, argument list) groups {p.groups} (instance -> group {p.instGroup}, instance -> callee {p.instCallee}; numbering READ from the old term: {p.partitionNote}); leaf argument widths {p.gws}"
  let src := assembleM p
  try
    Tools.ShippingSeqParentGen.runCmds src
  catch e =>
    try Tools.ShippingSeqParentGen.runCmds "end" catch _ => pure ()
    throw e
  let ep := fn ++ `epD2M_endpoint
  try
    liftTermElabM do
      let some stx := (Parser.runParserCategory (← getEnv) `term (endpointSrc p)).toOption
        | throwError "endpoint term: parse error"
      let e ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let ty ← instantiateMVars (← inferType e)
      if e.hasMVar || ty.hasMVar then throwError "#machine_seq_parent_endpoint (depth 2, several callees): unassigned mvars in the endpoint term"
      addAndCompile <| .thmDecl { name := ep, levelParams := [], type := ty, value := e }
    liftTermElabM <| auditM p ep
  finally
    Tools.ShippingSeqParentGen.runCmds "end"

end Tools.ShippingSeqParentGenD2M
