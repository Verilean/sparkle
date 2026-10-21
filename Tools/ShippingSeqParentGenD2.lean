import Tools.ShippingSeqParentGen
import Tools.ShippingSeqOldPieces
import Tools.ShippingSeqChildDeepRunA
import Tools.ShippingSeqChildDeepKidFactsA
import Tools.ShippingSeqChildDeepIfacePA
import Tools.ShippingSeqChildDeepConsumerA
import Tools.ShippingSeqParentKidFactsA
-- BUILT (unit SR3t): t2 exit 0 (the module itself; the templates are exercised by Tests.Compiler.SeqDeepGenTest / SeqDeepGenInstTest). t1 exit 1 (an `s!` string with braces).
/-! # `#machine_seq_parent_endpoint P`, DEPTH-2 path (unit SR3t, ledger L8ac)

The depth-1 elaborator of `Tools/ShippingSeqParentGen.lean` is UNCHANGED (it still refuses a child that has calls of its own).  This
module registers a SECOND elaborator for the same command syntax: for a declaration whose callee itself has call instances it takes
over (generate, or REFUSE with a stated reason); for every other declaration it throws `unsupportedSyntax` and the depth-1 elaborator
runs as before.

## The TARGET CLASS (exact; each condition is checked, a declaration outside it is REFUSED, never silently narrowed)

`P -> C -> G`, with `P` the parent (root), `C` its callee that has calls of its own, `G` the callee of `C`:
* `P` is a top-level machine (its `machineSource` is indexed by `Unit`), with at least one call instance, `instFields <> []`, no memory;
  EVERY call instance of `P` calls the SAME child `C` (any number of instances, any output fields), with the SAME argument list
  (the old generated `hcalls` has one group-facts bundle per distinct argument list; this path extracts ONE group);
* `C` is a `{dom : DomainConfig}` hardware module (its `machineSource` is indexed by `DomainConfig`), with `instFields <> []`, no memory;
  EVERY call instance of `C` calls the SAME leaf `G` (any number of instances / fields / arguments);
* `G` is a generated sequential LEAF (no call instance), with the pieces `G.machine_ok/machine_body/machine_closes/machineSource`;
* the old chain exists: `#machine_design_svNR P 2` (gives `P.machine_composedNR2` and `C.machine_composedNR1`, `C.seq_child_runN_ofR1`);
* `kP` = own input ports of `P` (`bsIn.length - insts.length`), `kC` likewise for `C` (it counts the `dom` binder); depth is 2 (`n = 2`).
The facts about the shapes that the proofs need (closing, name separation, widths, argument counts, ...) are `decide`d INSIDE the
generated declarations: a declaration inside the class whose data fail one of them makes the generated command fail loudly.

## REFUSALS (each with its reason; message prefix `REFUSED`)
several different callees of `P` / of `C`; a callee of `G` (depth 3); different argument lists among `P`'s calls (several groups);
a parent that is not a top-level machine or a child that is not a domain-polymorphic hardware module; no instField (combinational
calls); a missing generated piece (the message names it and the old command to run).

## WHAT IS GENERATED (names `P.epD2_*`; template text = the hand lemmas of units SR3n-SR3s, with the declaration names and the numbers
computed from the data) and WHAT STAYS A PREMISE: the endpoint `P.epD2_endpoint` has the premises `hr`, `entry`, `closes : True`; the
boundary `P.epD2_Bnd` (an existential over `O : RefLawsAOps`, `T : RefLawsATele`, `AdmCtx`, `MachineDefines C`, `MachineDefines G`,
a start world in `JQ`, the cache invariant) stays in the CONCLUSION.  NOT a general theorem; RealChildA is a history of past synthesis
results; `T` is an ADDED boundary.

## What is still POSITIONAL (see `Tools/ShippingSeqOldPieces.lean`)
The old generated terms are read through helpers that select by BINDER NAME of the consumer head (`hcalls`, `hextB`, `hext`), by the
lambda-binder name of the group-fact redex (`gfL0 gfR0 gfHb0 gfHv0`) and by BINDER KIND (the one instance-implicit argument).  Still
structural (not chosen by index): "the first application of the head constant in the value", "the argument `hcalls` is a lambda whose
body is a beta-redex", and the group index `0`.  Each extracted term is checked `isDefEq` against an EXPLICIT type written in the
template (the group-fact types of `Hb`/`Hv` leave their right-hand side as `_`: the family the generator absorbed into; the final
`.trans rfl` of the entry proof checks it against the entry's value). -/
namespace Tools.ShippingSeqParentGenD2
open Lean Elab Command Meta Term
open Tools.ShippingSeqParentGen (runCmds elabText readNames readName reduceNat openBlock)

def openBlock2 : String := openBlock ++ r#"
open Tools.ShippingInstTagged (originAt)
open Tools.ShippingMemCloses (ChildIfaceP)
open Tools.ShippingSeqChildDeepKidFactsA (KidFactsA)
open Tools.ShippingMachineCausal Tools.ShippingMachineDepthRunRA Tools.ShippingServedRealA Tools.ShippingChildDepthC
open Tools.ShippingChildTranslateA Tools.ShippingParentRanA Tools.ShippingChildComposeC Tools.ShippingChildRunAMain
open Tools.ShippingParentSeqComposedA
variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
"#

def d2Head : String := r#"
theorem _root_.@P@.epD2_G_outs_clean :
    ∀ o ∈ @G@.machineData.shape.layout.outs, ∀ c ∈ o.name.toList, Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

noncomputable def _root_.@P@.epD2_G_nk : Nat :=
  ((@G@.machineData.shape.binders.take (@G@.machineData.shape.binders.length -
    @G@.machineData.shape.layout.slots.length - @G@.machineData.shape.layout.lets)).filter
      fun x => x.2 != .domain).length

theorem _root_.@P@.epD2_C_insts_G : ∀ (k : Nat) (hk : k < @C@.machineData.shape.insts.length),
    (@C@.machineData.shape.insts[k]).1 = ``@G@ := by
  first | decide | decide +kernel

theorem _root_.@P@.epD2_C_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk @C@.machineData @KC@ (fun _ => @GW@) = true := by
  first | decide | decide +kernel


theorem _root_.@P@.epD2_C_closesA {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``@C@ @C@.machineData.shape := by
  have hent : ∀ (k : Nat) (hk : k < @C@.machineData.shape.insts.length),
      (@C@.machineData.shape.insts[k]).1 = ``@G@ ∧ originAt @C@.machineData.shape k = .field k := by
    first | decide | decide +kernel
  have hkid : ∀ (k : Nat) (hk : k < @C@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (originAt @C@.machineData.shape k)
        (@C@.machineData.shape.insts[k]).1 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``@G@) @P@.epD2_G_nk
        (@G@.machineData.shape.layout.outs.map (·.name)) [] y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, ho⟩ := hent k hk
    rw [ho] at hy
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
    (fun _ => Sparkle.IR.ModuleName.ofDecl ``@G@) (fun _ => @P@.epD2_G_nk)
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

theorem _root_.@P@.epD2_C_hsep {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
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
theorem _root_.@P@.epD2_C_outChars : ∀ o ∈ @C@.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem _root_.@P@.epD2_C_outScalar : ∀ o ∈ @C@.machineData.shape.layout.outs,
    Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel


theorem _root_.@P@.epD2_G_kidFactsA (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape) (n : Nat) :
    KidFactsA O ``@G@ @G@.machineData.shape.layout.outs @GW@ n := by
  have hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context),
      Tools.ShippingMachineEntry.MachineCloses mc mref cc cref ``@G@ @G@.machineData.shape :=
    fun mc cc => @G@.machine_closes mc _ cc _
  have hon : ∀ o ∈ @G@.machineData.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name :=
    fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (@P@.epD2_G_outs_clean o ho)
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

theorem _root_.@P@.epD2_C_kidFactsA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape) :
    KidFactsA O ``@C@ @C@.machineData.shape.layout.outs
      (Tools.ShippingCallsChildPorts.argWidths @C@.machineData @KC@) (n + 1) := by
  have hn := @P@.epD2_C_insts_G
  exact Tools.ShippingSeqChildDeepKidFactsA.deepChild_kidFactsA O T @C@.machineData @C@.machine_ok
    @C@.machine_body (nDecl := @KC@) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun h0 => absurd (congrArg List.length h0) (by decide))
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    @KC@ (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun _ => @G@.machineData.shape.layout.outs) (fun _ => @GW@) n
    (fun k hk => by rw [hn k hk]; exact @P@.epD2_G_kidFactsA O hR0 n)
    (fun k hk => by rw [hn k hk]; exact @P@.epD2_G_kidFactsA O hR0 (n + 1))
    (by first | decide | decide +kernel) @P@.epD2_C_callArgs
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (@P@.epD2_C_outChars o ho)) @P@.epD2_C_outScalar
    (@P@.epD2_C_hsep O hR0) entry
    (fun _ _ hA' => @P@.epD2_C_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0))


theorem _root_.@P@.epD2_insts_C : ∀ (k : Nat) (hk : k < @P@.machineData.shape.insts.length),
    (@P@.machineData.shape.insts[k]).1 = ``@C@ ∧ originAt @P@.machineData.shape k = .field k := by
  first | decide | decide +kernel

theorem _root_.@P@.epD2_callArgs :
    Tools.ShippingPortsMatchRaw.callArgsOk @P@.machineData @KP@
      (fun _ => Tools.ShippingCallsChildPorts.argWidths @C@.machineData @KC@) = true := by
  first | decide | decide +kernel

theorem _root_.@P@.epD2_callWidths :
    Tools.ShippingCallWidths.callWidthsOk @P@.machineData @KP@ (fun _ => @C@.machineData.shape.layout.outs) = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem _root_.@P@.epD2_outChars : ∀ o ∈ @P@.machineData.shape.layout.outs, ∀ c ∈ o.name.toList,
    Sparkle.IR.NameHints.charOk c = true := by
  first | decide | decide +kernel

set_option maxRecDepth 100000 in
theorem _root_.@P@.epD2_outScalar : ∀ o ∈ @P@.machineData.shape.layout.outs,
    Tools.ShippingTextTyped.scalarTy o.ty = true := by
  first | decide | decide +kernel


theorem _root_.@P@.epD2_C_hgk (O : RefLawsAOps MkRefd mref cref)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape) :
    ∀ (k : Nat) (hk : k < @C@.machineData.shape.insts.length) (y' : Tools.ShippingChildInv.Res),
      RealChildA O (@C@.machineData.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ∈ [Sparkle.IR.ModuleName.ofDecl ``@G@] ∧
        ∀ mn i conns, Sparkle.IR.AST.Stmt.inst mn i conns ∈ g.body → mn ∈ [Sparkle.IR.ModuleName.ofDecl ``@G@] := by
  intro k hk y' hy g hg
  rw [@P@.epD2_C_insts_G k hk] at hy
  have hI := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O @G@.machineData @G@.machine_ok @G@.machine_body
    (by decide) (by decide) hR0 (fun mc cc => @G@.machine_closes mc _ cc _) hy
  rcases List.mem_cons.mp hg with e | hin
  · subst e
    refine ⟨by rw [hI.name]; exact List.mem_singleton_self _, fun mn i conns hm => ?_⟩
    have := List.all_eq_true.mp hI.seqOk _ hm
    simp [Sparkle.IR.OptCheck.seqStmtOk] at this
  · rw [hI.design] at hin
    cases hin

theorem _root_.@P@.epD2_C_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
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
    _ (@P@.epD2_C_hgk O hR0) (@P@.epD2_C_hsep O hR0) entry
    (fun _ _ hA' => @P@.epD2_C_closesA O T hA' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0)) h

theorem _root_.@P@.epD2_closesA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape) :
    Tools.ShippingChildRunAKids.MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx
      ``@P@ @P@.machineData.shape := by
  have hent := @P@.epD2_insts_C
  have hkid : ∀ (k : Nat) (hk : k < @P@.machineData.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingCallsMemA.KidTA O (originAt @P@.machineData.shape k)
        (@P@.machineData.shape.insts[k]).1 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl ``@C@) (Tools.ShippingMachineEntry.machNIn @C@.machineData.shape)
        (@C@.machineData.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl ``@G@] y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, ho⟩ := hent k hk
    rw [ho] at hy
    rcases hy with hy | ⟨-, hre⟩
    · exact absurd hy (by show (none : Option _) ≠ some y; exact fun h => nomatch h)
    · rw [hn] at hre
      exact @P@.epD2_C_ifaceP O T hM hR0 hre
  intro tenv
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := @KP@) O T hA @P@.machineData
    @P@.machine_ok @P@.machine_body (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel) (fun h0 => absurd (congrArg List.length h0) (by decide))
    (fun _ => Sparkle.IR.ModuleName.ofDecl ``@C@) (fun _ => Tools.ShippingMachineEntry.machNIn @C@.machineData.shape)
    (fun _ => @C@.machineData.shape.layout.outs.map (·.name)) (fun _ => [Sparkle.IR.ModuleName.ofDecl ``@G@])
    hkid (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (by first | decide | decide +kernel)
    (fun k hk k' hk' _ => by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)
    (fun k hk => Tools.ShippingModuleName.ofDecl_ne (by decide : ``@C@ ≠ ``@P@))
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head
      ((by first | decide | decide +kernel :
        ∀ o ∈ @P@.machineData.shape.layout.outs, o.name.toList.head? ≠ some 'i') o ho) gi _)
    (fun k hk hx => Tools.ShippingModuleName.ofDecl_ne (by decide : ``@G@ ≠ ``@P@) (List.mem_singleton.mp hx).symm)
    (fun k hk k' hk' hne => (hne (by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)).elim)


theorem _root_.@P@.epD2_ranA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)
    {D₀ : Nat} {w w1 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : Tools.ShippingEntrySoundness.RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore ``@P@ [] false)
      mctx mref cctx cref w (raw, D) w1)
    (entry : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@P@ @P@.machineData.shape)
    (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w)) :
    Tools.ShippingParentRanA.MachineRanA O mctx cctx ``@P@ @P@.machineData.shape raw D :=
  Tools.ShippingParentRanA.machineRanA_main O hA T hcore entry (@P@.epD2_closesA O T hA hM hR0) hw hc

theorem _root_.@P@.epD2_hkid (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape) :
    ∀ (k : Nat) (hk : k < @P@.machineData.shape.insts.length),
      Tools.ShippingSeqChildDeepKidFactsA.KidFactsA O (@P@.machineData.shape.insts[k]).1
        ((fun _ => @C@.machineData.shape.layout.outs) k)
        ((fun _ => Tools.ShippingCallsChildPorts.argWidths @C@.machineData @KC@) k) (n + 1) := by
  intro k hk
  rw [(@P@.epD2_insts_C k hk).1]
  exact @P@.epD2_C_kidFactsA O T n hM hR0

theorem _root_.@P@.epD2_runFacts (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)
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
    (fun _ => @C@.machineData.shape.layout.outs) (fun _ => Tools.ShippingCallsChildPorts.argWidths @C@.machineData @KC@) (n + 1)
    (@P@.epD2_hkid O T n hM hR0) @P@.epD2_callWidths hpost (@P@.epD2_ranA O T hA hM hR0 hcore entry hw hc)

theorem _root_.@P@.epD2_outsCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)
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
    (fun _ => @C@.machineData.shape.layout.outs) (fun _ => Tools.ShippingCallsChildPorts.argWidths @C@.machineData @KC@) (n + 1)
    (@P@.epD2_hkid O T n hM hR0) hpost (@P@.epD2_ranA O T hA hM hR0 hcore entry hw hc)
    (@P@.epD2_runFacts O T n hA hM hR0 hcore hpost entry hw hc).gate

theorem _root_.@P@.epD2_kidsMasked (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)
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
    (fun _ => @C@.machineData.shape.layout.outs) (fun _ => Tools.ShippingCallsChildPorts.argWidths @C@.machineData @KC@) (n + 1)
    (@P@.epD2_hkid O T n hM hR0) hpost (@P@.epD2_ranA O T hA hM hR0 hcore entry hw hc)

theorem _root_.@P@.epD2_designCheck (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (n : Nat)
    (hA : AdmCtx O.quiet mctx cctx)
    (hM : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)
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
    (fun _ => @C@.machineData.shape.layout.outs) (fun _ => Tools.ShippingCallsChildPorts.argWidths @C@.machineData @KC@) (n + 1)
    (@P@.epD2_hkid O T n hM hR0) @P@.epD2_callWidths @P@.epD2_callArgs hpost (@P@.epD2_ranA O T hA hM hR0 hcore entry hw hc)
    (fun o ho => Tools.ShippingSVBridge.sanitizeName_of_clean (@P@.epD2_outChars o ho)) @P@.epD2_outScalar


"#

def d2Tail : String := r#"
def _root_.@P@.epD2_C_Bnd (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cref : ST.Ref IO.RealWorld Lean.Core.State) :
    Lean.Meta.Context → Lean.Core.Context → Void IO.RealWorld → Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → Prop :=
  fun mctx cctx _ _ _ =>
    Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape

instance _root_.@P@.epD2_C_inhab : Inhabited (HList (Tools.ShippingMachineDenote.tys @C@.machineData.ss)) :=
  oldInst% (Inhabited (HList (Tools.ShippingMachineDenote.tys @C@.machineData.ss))) @C@.machine_composedNR1
    Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA

instance _root_.@P@.epD2_inhab : Inhabited (HList (Tools.ShippingMachineDenote.tys @P@.machineData.ss)) :=
  oldInst% (Inhabited (HList (Tools.ShippingMachineDenote.tys @P@.machineData.ss))) @P@.machine_composedNR2
    Tools.ShippingMachineCausal.machine_traceL_of_data_causalRA

theorem _root_.@P@.epD2_C_hcausal : HCausalOf @C@.machineData (fun i => i) @C@.machineExt @C@.machineExtB :=
  fun i bools bits S S' t h =>
  @C@.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
    (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)

theorem _root_.@P@.epD2_hcausal : HCausalOf @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain)
    @P@.machineExt @P@.machineExtB := fun i bools bits S S' t h =>
  @P@.machine_ext_causal i { B := bools, V := bits, S := S } { B := bools, V := bits, S := S' } t
    (Tools.ShippingMachineCausal.CtxAgree.of_state bools bits S S' t h)

theorem _root_.@P@.epD2_C_traceXA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
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
    @C@.machine_writes @C@.machine_result @C@.machine_source @P@.epD2_C_hcausal
    mctx mref cctx cref O (bodyStepC_of_tele O T) hA (D₀ + 1) (htr_of_tele O hA T D₀) m design
    (machineRunJQC_of_closesA O hA hcore entry (@P@.epD2_C_closesA O T hA hR0) hw hc)

theorem _root_.@P@.epD2_C_hcalls (m : Sparkle.IR.AST.Module) (design : Sparkle.IR.AST.Design) :
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

theorem _root_.@P@.epD2_C_composedA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
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
  have h := @P@.epD2_C_traceXA O T hA hR0 hw hc hcore entry
  exact machine_linkedT_callsRNA 1 O h (by first | decide | decide +kernel) @KC@ (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun n => if n = ``@G@ then @G@.machineData.bsIn else [])
    (fun n => if n = ``@G@ then @G@.machineData.shape.layout.outs else [])
    (fun i n => if n = ``@G@ then fun vals => @G@.machineSource i
        (Tools.ShippingMachineChild.boolsOf @G@.machineData.bsIn vals)
        (Tools.ShippingMachineChild.bitsOf @G@.machineData.bsIn vals) else fun vals => [])
    (fun n => if n = ``@G@ then (fun mc => Tools.ShippingGateChild.MachineRun ``@G@ @G@.machineData.shape mc)
        else (fun mc => Tools.ShippingGateChild.MachineRun ``@G@ @G@.machineData.shape mc))
    (@P@.epD2_C_hcalls m design)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < @C@.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = ``@G@ := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        rw [← Option.some.inj hc']
        exact @P@.epD2_C_insts_G k hk
      subst hck
      have hmr : Tools.ShippingGateChild.MachineRun ``@G@ @G@.machineData.shape mc :=
        ⟨mctx', mref, cctx', cref, w1, w2, Dc, hrun, Tools.ShippingReflectCtx.MachineDefines.ctx hR0,
          @G@.machine_closes mctx' _ cctx' _⟩
      split <;> exact hmr)

theorem _root_.@P@.epD2_C_seqChildRunN2 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    {mc : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (h : Tools.ShippingMachineDepthRun.MachineRunNCA O ``@C@ @C@.machineData.shape (@P@.epD2_C_Bnd mref cref) mc design) :
    Tools.ShippingMachineDepth.SeqChildRunN (childMap design.modules) design 2 mc (List.take @KC@ @C@.machineData.bsIn)
      @C@.machineData.shape.layout.outs
      (fun vals => @C@.machineSource Sparkle.Core.Domain.defaultDomain
        (Tools.ShippingMachineChild.boolsOf (List.take @KC@ @C@.machineData.bsIn) vals)
        (Tools.ShippingMachineChild.bitsOf (List.take @KC@ @C@.machineData.bsIn) vals)) :=
  Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA O 1 (@P@.epD2_C_Bnd mref cref)
    (fun hcore hadm hjqc entry _ hB => @P@.epD2_C_composedA O T hadm hB hjqc.1 (Or.inr hjqc.2) hcore entry)
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

theorem _root_.@P@.epD2_traceXA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hM : MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)
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
    @P@.machine_writes @P@.machine_result @P@.machine_source @P@.epD2_hcausal
    mctx mref cctx cref O (bodyStepC_of_tele O T) hA (D₀ + 1) (htr_of_tele O hA T D₀) m design
    (machineRunJQC_of_closesA O hA hcore entry (@P@.epD2_closesA O T hA hM hR0) hw hc)

theorem _root_.@P@.epD2_soundLA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hM : MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)
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
    @P@.epD2_traceXA O T hA hM hR0 hw hc hcore entry
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, tr⟩

theorem _root_.@P@.epD2_houtTy : ∀ o ∈ @P@.machineData.shape.layout.outs, o.ty.bitWidth = o.width := by
  first | decide | decide +kernel

theorem _root_.@P@.epD2_composedA {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hM : MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape)
    (hR0 : MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape)
    {D₀ : Nat} (hw : JQ O.quiet D₀ w) (hc : D₀ = 0 ∨ CacheInvA O (cv w))
    (hcore : RunsTo (synthesizeCombinationalCore ``@P@ [] false) mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``@P@ @P@.machineData.shape) :
    ComposedG (fun D => KSn (childMap D.modules) 2) (ResetNk 2) ``@P@ @P@.machineData @KP@ m design
      (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineSource
      (fun i bools bits => @P@.machineExt i bools bits
        (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits)))
      (fun i bools bits => @P@.machineExtB i bools bits
        (Tools.ShippingMachineSource.stateLoop @P@.machineInits (@P@.machineBody i bools bits))) := by
  have h := @P@.epD2_traceXA O T hA hM hR0 hw hc hcore entry
  refine Tools.ShippingMachineShipsDepth.composedG_of_NW ?_
  exact machine_linkedT_callsRNA 2 O h (by first | decide | decide +kernel) @KP@ (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel) (by first | decide | decide +kernel)
    (fun n => if n = ``@C@ then List.take @KC@ @C@.machineData.bsIn else [])
    (fun n => if n = ``@C@ then @C@.machineData.shape.layout.outs else [])
    (fun i n => if n = ``@C@ then fun vals => @C@.machineSource Sparkle.Core.Domain.defaultDomain
      (Tools.ShippingMachineChild.boolsOf (List.take @KC@ @C@.machineData.bsIn) vals)
      (Tools.ShippingMachineChild.bitsOf (List.take @KC@ @C@.machineData.bsIn) vals) else fun vals => [])
    (fun _ mc => Tools.ShippingMachineDepthRunRA.MachineRunNCA O ``@C@ @C@.machineData.shape (@P@.epD2_C_Bnd mref cref) mc design)
    (fun i bools bits k c hk => by
      have hk' : k < @P@.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hk).1; simpa using this
      have hck : c = ``@C@ := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk'] at hk
        rw [← Option.some.inj hk]
        exact (@P@.epD2_insts_C k hk').1
      subst hck
      -- the group facts of the generated proof that do not mention the child predicate
      have L : ∀ (q : Nat) (hq : q < (@ARGS@ : List Nat).length), (@ARGS@ : List Nat)[q] < @P@.machineData.ls.length ∧
          ∃ g, (letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits @P@.machineBody @P@.machineExt @P@.machineExtB i bools bits)[(@ARGS@ : List Nat)[q]]? = some g :=
        oldGroupFact% (∀ (q : Nat) (hq : q < (@ARGS@ : List Nat).length), (@ARGS@ : List Nat)[q] < @P@.machineData.ls.length ∧
          ∃ g, (letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits @P@.machineBody @P@.machineExt @P@.machineExtB i bools bits)[(@ARGS@ : List Nat)[q]]? = some g) @P@.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfL0
      have R : ∀ τ : Nat, Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits @P@.machineBody @P@.machineExt @P@.machineExtB i bools bits) (@ARGS@ : List Nat) τ)
          ((List.take @KC@ @C@.machineData.bsIn).filter fun b => b.2 != .domain) :=
        oldGroupFact% (∀ τ : Nat, Tools.ShippingMachineChild.InRange (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits @P@.machineBody @P@.machineExt @P@.machineExtB i bools bits) (@ARGS@ : List Nat) τ)
          ((List.take @KC@ @C@.machineData.bsIn).filter fun b => b.2 != .domain)) @P@.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfR0
      have Hb : Tools.ShippingMachineChild.boolsOf (List.take @KC@ @C@.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits @P@.machineBody @P@.machineExt @P@.machineExtB i bools bits) (@ARGS@ : List Nat)) = _ :=
        oldGroupFact% (Tools.ShippingMachineChild.boolsOf (List.take @KC@ @C@.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits @P@.machineBody @P@.machineExt @P@.machineExtB i bools bits) (@ARGS@ : List Nat)) = _) @P@.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHb0
      have Hv : Tools.ShippingMachineChild.bitsOf (List.take @KC@ @C@.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits @P@.machineBody @P@.machineExt @P@.machineExtB i bools bits) (@ARGS@ : List Nat)) = _ :=
        oldGroupFact% (Tools.ShippingMachineChild.bitsOf (List.take @KC@ @C@.machineData.bsIn)
          (Tools.ShippingMachineCallsLinkedT.valsOf (letObsB @P@.machineData (fun _ : Unit => Sparkle.Core.Domain.defaultDomain) @P@.machineInits @P@.machineBody @P@.machineExt @P@.machineExtB i bools bits) (@ARGS@ : List Nat)) = _) @P@.machine_composedNR2 Tools.ShippingMachineCallsLinkedTNR.machine_linkedT_callsRN hcalls gfHv0
      have hlt : k < @MP@ := by
        have : @P@.machineData.shape.insts.length = @MP@ := by first | decide | decide +kernel
        omega
      right
      unfold Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN
      rcases k with @MPAT@
@CASES@
      · omega)
    (fun k c hc' hnone mctx' cctx' mc Dc w1 w2 hadm hcache hsv hq hrun hcons hmod => by
      have hk : k < @P@.machineData.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hc').1; simpa using this
      have hck : c = ``@C@ := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc'
        rw [← Option.some.inj hc']
        exact (@P@.epD2_insts_C k hk).1
      subst hck
      exact Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main O T
        (RealChildA.run mctx' cctx' w1 w2 hadm hcache hsv hq hrun) hcons hM
        (fun mctx cctx _ w raw D _ => Tools.ShippingReflectCtx.MachineDefines.ctx hR0)
        (fun mctx cctx w raw D hin _ => by
          obtain ⟨_, _, _, hadm', _⟩ := hin
          exact @P@.epD2_C_closesA O T hadm' (Tools.ShippingReflectCtx.MachineDefines.ctx hR0))
        (by first | decide | decide +kernel))

def _root_.@P@.epD2_Bnd : Tools.ShippingMachineShipsHier.CtxBnd := fun mctx mref cctx cref w _ _ =>
  ∃ (O : RefLawsAOps MkRefd mref cref) (_ : RefLawsATele O.quiet mref cref),
    AdmCtx O.quiet mctx cctx ∧
    MachineDefines mctx mref cctx cref ``@C@ @C@.machineData.shape ∧
    MachineDefines mctx mref cctx cref ``@G@ @G@.machineData.shape ∧
    ∃ D₀, JQ O.quiet D₀ w ∧ (D₀ = 0 ∨ CacheInvA O (cv w))
"#

/-- The term of the endpoint: `machine_design_noShips_noBd_dc` at `n := 2`, `C := True`, applied to the generated pieces. -/
def endpointTermD2 : String := r#"(@Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc 2 @P@.epD2_Bnd (fun _ _ _ _ => True)
    ``@P@ @P@.machineData @KP@ Unit (fun _ => Sparkle.Core.Domain.defaultDomain) _ _ _ _ _ _ _
    (fun hcore entry _ hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact @P@.epD2_soundLA O T hA hM hR0 hw hc hcore entry)
    (fun hcore entry _ hB _ => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact @P@.epD2_composedA O T hA hM hR0 hw hc hcore entry)
    @P@.epD2_houtTy
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact @P@.epD2_runFacts O T 1 hA hM hR0 hcore hpost entry hw hc)
    (fun hcore hpost entry _ hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact @P@.epD2_outsCheck O T 1 hA hM hR0 hcore hpost entry hw hc)
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact @P@.epD2_kidsMasked O T 1 hA hM hR0 hcore hpost entry hw hc)
    (fun hcore hpost entry hB => by
      obtain ⟨O, T, hA, hM, hR0, D₀, hw, hc⟩ := hB
      exact @P@.epD2_designCheck O T 1 hA hM hR0 hcore hpost entry hw hc))"#


/-! ## class analysis: every refusal has a stated reason -/

/-- Read a `List Nat` back by head reduction. -/
partial def readNats (e : Expr) : MetaM (List Nat) := do
  let e ← withDefault (whnf e)
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``List.nil, _ => return []
  | some ``List.cons, #[_, h, t] => return (← reduceNat h) :: (← readNats t)
  | _, _ => throwError "readNats: cannot read a list of numerals from {e}"

/-- Read a `List (List Nat)` back by head reduction. -/
partial def readNatLists (e : Expr) : MetaM (List (List Nat)) := do
  let e ← withDefault (whnf e)
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``List.nil, _ => return []
  | some ``List.cons, #[_, h, t] => return (← readNats h) :: (← readNatLists t)
  | _, _ => throwError "readNatLists: cannot read a list of lists from {e}"

/-- The data the depth-2 template is instantiated with.  `P` = the parent, `C` = its ONE callee (the non-leaf child), `G` = the ONE
callee of `C` (a leaf).  `kP`/`kC` = the numbers of own input ports of `P`/`C`, `mP`/`mC` = the numbers of call instances,
`gw` = the declared widths of `G`'s arguments, `args` = the (single) argument list of the calls of `P`, `kf` = per instance of `P`
the index of the called output field among the outputs of `C`. -/
structure D2Params where
  P : Name
  C : Name
  G : Name
  kP : Nat
  kC : Nat
  mP : Nat
  mC : Nat
  gw : List Nat
  args : List Nat
  nOutsC : Nat
deriving Repr

def refuse {α : Type} (fn : Name) (why : String) : CommandElabM α :=
  throwError "#machine_seq_parent_endpoint (unit SR3t, depth 2): REFUSED `{fn}`: {why}"

/-- Is the first explicit argument of `c.machineSource` of type `ty`? (`Unit` for a top-level machine, `DomainConfig` for a
`{dom : DomainConfig}` polymorphic hardware module.) -/
def sourceIndex (c : Name) : MetaM Name := do
  let ci ← getConstInfo (c ++ `machineSource)
  forallTelescope ci.type fun xs _ => do
    let some x := xs[0]? | return Name.anonymous
    let t ← whnf (← inferType x)
    return t.getAppFn.constName?.getD Name.anonymous

def analyse (fn : Name) : CommandElabM D2Params := do
  let env ← getEnv
  let nat := fun (s : String) (n : Name) => liftTermElabM do reduceNat (← elabText (s.replace "@F@" n.toString))
  -- the callees of the parent: ONE child
  let pc ← liftTermElabM do readNames (← elabText (s!"({fn}.machineData.shape.insts.map (·.1))"))
  if pc.isEmpty then refuse fn "no call instance"
  let pcs := pc.eraseDups
  unless pcs.length == 1 do
    refuse fn s!"the parent calls {pcs.length} DIFFERENT children {pcs}; the depth-2 closing / checks of this path are instantiated with ONE callee (`fun _ => C`), several different non-leaf children are OPEN (the depth-1 path handles several leaf children)"
  let C := pcs.head!
  let cc ← liftTermElabM do readNames (← elabText (s!"({C}.machineData.shape.insts.map (·.1))"))
  if cc.isEmpty then
    refuse fn s!"the child {C} has no call instance: `{fn}` is depth 1 (use the depth-1 path)"
  let ccs := cc.eraseDups
  unless ccs.length == 1 do
    refuse fn s!"the child {C} calls {ccs.length} DIFFERENT grandchildren {ccs}; this path takes ONE leaf grandchild (OPEN: several)"
  let G := ccs.head!
  let gi ← nat "@F@.machineData.shape.insts.length" G
  unless gi == 0 do
    refuse fn s!"the grandchild {G} has {gi} call instance(s) of its own: depth 3, OPEN (no depth-3 interface/closing lemma on the new boundary)"
  -- the argument lists of the parent's calls: ONE group (the old generated hcalls has one group-facts bundle per distinct list)
  let al ← liftTermElabM do readNatLists (← elabText s!"({fn}.machineData.shape.insts.map (·.2.1))")
  let some a0 := al.head? | refuse fn "no call instance"
  unless al.all (· == a0) do
    refuse fn s!"the calls of the parent have DIFFERENT argument lists {al}; the old generated `hcalls` has one group-facts bundle per distinct list and this path extracts ONE (OPEN: several groups)"
  for (n, ss) in [(fn, [`machine_composedNR2, `machine_ok, `machine_body, `machine_inits, `machine_writes, `machine_result, `machine_source,
        `machine_ext_causal, `machineSource, `machineInits, `machineBody, `machineResult, `machineExt, `machineExtB, `machineData]),
      (C, [`machine_composedNR1, `machine_ok, `machine_body, `machine_inits, `machine_writes, `machine_result, `machine_source,
        `machine_ext_causal, `machineSource, `machineInits, `machineBody, `machineResult, `machineExt, `machineExtB, `machineData,
        `seq_child_runN_ofR1]),
      (G, [`machine_ok, `machine_body, `machine_closes, `machineSource, `machineData])] do
    for s in ss do
      unless env.contains (n ++ s) do
        refuse fn s!"{n ++ s} not found (the class needs the old generated chain: `#machine_design_svNR {fn} 2`, which also generates the child pieces)"
  -- domain polymorphism: the parent is a top-level machine (index `Unit`), the child a `{dom : DomainConfig}` hardware module
  let ip ← liftTermElabM <| sourceIndex fn
  let ic ← liftTermElabM <| sourceIndex C
  unless ip == ``Unit do refuse fn s!"the parent's machineSource is indexed by {ip}, expected Unit (a top-level, non-polymorphic machine)"
  unless ic == `Sparkle.Core.Domain.DomainConfig do
    refuse fn s!"the child {C}'s machineSource is indexed by {ic}, expected DomainConfig (a hardware module with a `dom : DomainConfig` binder); a child that is not domain polymorphic is OPEN on this path"
  for n in [fn, C] do
    let nf ← nat "@F@.machineData.shape.instFields.length" n
    if nf == 0 then
      refuse fn s!"{n} has no instField: its calls are one-output COMBINATIONAL children, not the sequential calls of this path"
  let kP ← nat "(@F@.machineData.bsIn.length - @F@.machineData.shape.insts.length)" fn
  let kC ← nat "(@F@.machineData.bsIn.length - @F@.machineData.shape.insts.length)" C
  let mP ← nat "@F@.machineData.shape.insts.length" fn
  let mC ← nat "@F@.machineData.shape.insts.length" C
  let nOutsC ← nat "@F@.machineData.shape.layout.outs.length" C
  let gw ← liftTermElabM do readNats (← elabText s!"(Tools.ShippingPortWidthsPure.declWidths {G}.machineData)")
  return { P := fn, C := C, G := G, kP := kP, kC := kC, mP := mP, mC := mC, gw := gw, args := a0, nOutsC := nOutsC }

/-! ## text assembly -/

def subst2 (s : String) (p : D2Params) : String :=
  ((((((s.replace "@ARGS@" (toString p.args)).replace "@P@" p.P.toString).replace "@C@" p.C.toString).replace "@G@" p.G.toString).replace "@KP@" (toString p.kP)).replace
    "@KC@" (toString p.kC)).replace "@GW@" (toString p.gw)

/-- The cases of `epD2_composedA`: instance `k` of the parent.  The called output field index is found among the outputs of `C`
(`first` over the candidates; a wrong candidate fails at `rfl`). -/
def composedCases (p : D2Params) : String :=
  let alts := (List.range p.nOutsC).map fun K =>
    s!"(refine ⟨rfl, {p.args}, rfl, (fun mc hmc => ⟨@P@.epD2_C_seqChildRunN2 O T hmc, by rw [(@P@.epD2_C_seqChildRunN2 O T hmc).2.2.2.2.2.1]; decide⟩), L, R, {K}, _, _, rfl, rfl, ?_, fun τ => rfl⟩
         exact (congrArg (fun l => l[{K}]?) (Tools.ShippingMachineCallsLinkedT.decoded_eq (@C@.machineSource Sparkle.Core.Domain.defaultDomain) Hb Hv)).trans rfl)"
  let one := "· first\n" ++ "\n".intercalate (alts.map fun a => "    | " ++ a)
  "\n".intercalate ((List.range p.mP).map fun _ => one)

def assembleD2 (p : D2Params) : String :=
  let pat := "".intercalate ((List.range p.mP).map fun _ => "_ | ") ++ "k"
  let src := openBlock2 ++ d2Head ++ d2Tail
  let src := src.replace "@MPAT@" pat
  let src := src.replace "@MP@" (toString p.mP)
  let src := src.replace "@CASES@" ("\n".intercalate (((composedCases p).splitOn "\n").map fun l => "      " ++ l))
  subst2 src p

/-! ## audit of the generated endpoint -/

open Tests.Compiler.ChildVertAuditTest in
def auditD2 (p : D2Params) (ep : Name) : MetaM Unit := do
  stdAxioms ep
  let ty := (← getConstInfo ep).type
  let premises ← forallTelescope ty fun xs _ => do
    let mut ps : Array String := #[]
    for x in xs do
      let t ← inferType x
      if (← isProp t) then ps := ps.push s!"{(← x.fvarId!.getUserName)} : {t.getAppFn.constName?.getD Name.anonymous}"
    return ps
  let expected := ["hr : Tools.ShippingEntrySoundness.RunsTo", "entry : Tools.ShippingMachineEntry.MachineDefines", "closes : True"]
  unless premises.toList == expected do throwError "SR3t AUDIT FAILED: outer Prop premises are {premises}, expected {expected}"
  let cl ← depClosure ep
  let forbidden : List Name := [`Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
    `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC,
    `Tools.ShippingMachineDepthRun.machineRunNC_of_real, `Tools.ShippingMachineDepthRun.seqChildRunN_of_composedC]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SR3t AUDIT FAILED: the forbidden name {f} does not exist (the audit would check nothing)"
  let bad := hits cl ++ cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
  unless bad.isEmpty do throwError "SR3t AUDIT FAILED: {ep}: old boundary / old child predicate in closure: {bad}"
  let pe := fun (s : String) => p.P ++ Name.mkSimple s
  for must in [pe "epD2_soundLA", pe "epD2_composedA", pe "epD2_traceXA", pe "epD2_C_composedA", pe "epD2_C_seqChildRunN2",
      pe "epD2_designCheck", pe "epD2_runFacts", pe "epD2_outsCheck", pe "epD2_kidsMasked", pe "epD2_closesA", pe "epD2_C_ifaceP",
      pe "epD2_C_kidFactsA", pe "epD2_C_closesA",
      ``Tools.ShippingSeqChildDeepRunA.seqChildRunN_of_composedCA, ``Tools.ShippingMachineDepthRunRA.machine_linkedT_callsRNA,
      ``Tools.ShippingMachineDepthRunRA.machineRunNCA_of_real_main, ``Tools.ShippingParentSeqComposedA.machine_traceL_of_data_causalRA_ranA,
      ``Tools.ShippingParentRanA.machineRanA_main, ``Tools.ShippingMachineShipsDepth.composedG_of_NW,
      ``Tools.ShippingSeqParentLemmas.machine_design_noShips_noBd_dc] do
    unless cl.contains must do throwError "SR3t AUDIT FAILED: {must} not in the closure of {ep}"
  -- the old composed theorems supply only PC-free subterms: the theorems themselves are not in the closure
  for old in [p.P ++ `machine_composedNR2, p.C ++ `machine_composedNR1, p.C ++ `seq_child_runN_ofR1] do
    if cl.contains old then throwError "SR3t AUDIT FAILED: the old generated theorem {old} is in the closure of {ep}"
  let (_, concl) ← forallTelescope ty fun _ c => pure ((), c)
  let bnd := pe "epD2_Bnd"
  unless (concl.find? (·.isConstOf bnd)).isSome do throwError "SR3t AUDIT FAILED: {bnd} not in the conclusion"
  -- the boundary: MachineDefines for the CHILD and the GRANDCHILD (in this order), read back from its definition
  let some bv := (← getConstInfo bnd).value? | throwError "SR3t AUDIT FAILED: {bnd} has no value"
  let mut defs : Array Name := #[]
  let mut todo : Array Expr := #[bv]
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if e.getAppFn.isConstOf ``Tools.ShippingMachineEntry.MachineDefines then
      let args := e.getAppArgs
      -- the declaration name argument (a `Name` literal `Lean.Name.str …`), position 4
      if let some a := args[4]? then
        defs := defs.push (← Tools.ShippingSeqParentGen.readName a)
    match e with
    | .app f a => todo := todo.push f |>.push a
    | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
    | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
    | .mdata _ b => todo := todo.push b
    | _ => pure ()
  unless defs.qsort (·.toString < ·.toString) == #[p.C, p.G].qsort (·.toString < ·.toString) do
    throwError "SR3t AUDIT FAILED: {bnd} asks MachineDefines for {defs}, expected exactly {[p.C, p.G]}"
  logInfo m!"SR3t AUDIT OK: {ep}: standard axioms; outer Prop premises ASSERTED {premises}; closure {cl.size} constants, none of ChildBnd/StartV/GenKid/old KidFacts/MachineRunNC/machineRunNC_of_real/seqChildRunN_of_composedC (each forbidden name resolved first); the old generated theorems are not in the closure; {bnd} (an EXISTENTIAL over O/T/AdmCtx/MachineDefines {p.C}/MachineDefines {p.G}/start world, not a proof that it holds) stays in the conclusion; chain {p.P} -> {p.C} -> {p.G}"

/-! ## the command (second elaborator; depth-1 path unchanged) -/

open Tools.ShippingSeqParentGen in
@[command_elab Tools.ShippingSeqParentGen.«command#machine_seq_parent_endpoint_»]
def elabEndpointD2 : CommandElab := fun stx => do
  let f : Ident := ⟨stx[1]⟩
  let fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo f
  -- dispatch: only a parent that has a callee with call instances of its own is handled here
  unless (← getEnv).contains (fn ++ `machineData) do throwUnsupportedSyntax
  let pc ← liftTermElabM do readNames (← elabText (s!"({fn}.machineData.shape.insts.map (·.1))"))
  let mut deep := false
  for c in pc.eraseDups do
    if (← getEnv).contains (c ++ `machineData) then
      let n ← liftTermElabM do reduceNat (← elabText s!"{c}.machineData.shape.insts.length")
      if n > 0 then deep := true
  unless deep do throwUnsupportedSyntax
  let p ← analyse fn
  logInfo m!"SR3t: depth-2 class instance {p.P} -> {p.C} -> {p.G}: kP {p.kP}, kC {p.kC}, {p.mP} call instance(s) of {p.C} with arguments {p.args}, {p.mC} of {p.G} with widths {p.gw}"
  let src := assembleD2 p
  try
    runCmds src
  catch e =>
    try runCmds "end" catch _ => pure ()
    throw e
  let ep := fn ++ `epD2_endpoint
  try
    liftTermElabM do
      let some stx := (Parser.runParserCategory (← getEnv) `term (subst2 endpointTermD2 p)).toOption
        | throwError "endpoint term: parse error"
      let e ← elabTerm stx none
      synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let ty ← instantiateMVars (← inferType e)
      if e.hasMVar || ty.hasMVar then throwError "#machine_seq_parent_endpoint (depth 2): unassigned mvars in the endpoint term"
      addAndCompile <| .thmDecl { name := ep, levelParams := [], type := ty, value := e }
    liftTermElabM <| auditD2 p ep
  finally
    runCmds "end"

end Tools.ShippingSeqParentGenD2
