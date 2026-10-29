import Tools.ShippingGen5T2OutTy
set_option autoImplicit false
-- NOT BUILT: written without running Lean. No sorry / axiom / native_decide.

/-! # `T1HypND` and the dec-free T2-OUTTY roots (scripts/gen5/DGEN_FREEZE.md §7.10, rev2.6, par/gen5-t2 5f0b2a69)

`T1HypND` is `T1Hyp` (Tools/ShippingGen2Defs.lean, `structure T1Hyp`) with its fields copied VERBATIM except `dec`.
New file; `Tools/ShippingGen2Defs.lean` is NOT edited. `T1Hyp.toND` is the adapter (uses `pkg`/`defines`/`closes`/
`closed`, never `dec`). The ND roots restate §7.9 H1-H4 with `H : T1HypND`; their proofs use only `T1HypND.defines`
/ `T1HypND.closed` and do NOT go through `T1Hyp.toND` or the §7.9 roots (checked in Tests/Gen5/T1NDCheck.lean).
CONDITIONAL as §7.9: `hDG_CLOSINGRUN`, DG-SEM, `OneOutWidth` / `hkidW` stay inputs. Not M5 or FG completion. -/
namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain

variable {ι : Type} {dom : ι → DomainConfig}

/-- **`T1HypND`**: the hypotheses of T1 without `dec` (fields verbatim from `T1Hyp`). -/
structure T1HypND {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (DataOk : Pkg ι dom → Prop) : Prop where
  /-- G3-GEN: a package for every reached declaration. -/
  pkg : ∀ c, Reach c → ∃ q, P c = some q ∧ q.decl = c ∧ DataOk q
  /-- G3-SHAPE: its shape reflection, in every admissible context. -/
  defines : ∀ c, Reach c → ∀ q, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
    MachineDefines mctx mref cctx cref c q.d.shape
  /-- **T1 scope (route 3)**: the machine synthesis of every reached declaration returns (it does not fall back).
  Coverage obligation G-CLOSES: derive from the data (`memCallee_closesA`, Srm3Callee.lean:91, for memory callees;
  `closes_of_data`, Tools/ShippingMachineClosesData.lean, in general); declarations where it fails are route 4 (M4),
  not removed from FG. -/
  closes : ∀ c, Reach c → ∀ q, P c = some q → ∀ mctx cctx, AdmCtx L.O.quiet mctx cctx →
    MachineClosesAtA L.O mctx cctx c q.d.shape
  /-- Static call closure of `Reach` (its match with the translator's actual child calls is G-REACH). -/
  closed : ∀ c, Reach c → ∀ q, P c = some q → ∀ k (hk : k < q.d.shape.insts.length),
    (q.d.shape.instOrigins.getD k .ord).child? = none → Reach (q.d.shape.insts[k]).1

/-- The adapter: a `T1Hyp` gives a `T1HypND` (field projections; `dec` is not used). -/
theorem T1Hyp.toND {mref cref} {L : Laws mref cref} {P : Pkgs ι dom} {Reach : Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1Hyp L P Reach DataOk) : T1HypND L P Reach DataOk :=
  ⟨H.pkg, H.defines, H.closes, H.closed⟩

/-- **(H1, ND)** The `houtTy` row of a reached callee from ONE real-entry result. -/
theorem houtTy_of_realChildND {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1HypND L P Reach DataOk) {c : Lean.Name} {q : Pkg ι dom}
    {r : Tools.ShippingChildInv.Res} (hR : Reach c) (hq : P c = some q)
    (hy : Tools.ShippingChildCacheA.RealChildA L.O c r) :
    ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width :=
  match hy with
  | .run mctx cctx _ _ adm _ _ _ hr => by
    obtain ⟨_, _, _, core, -⟩ := Tools.ShippingPostSoundness.synthesizeCombinational_reads hr
    exact Tools.ShippingReaderOutsInv.outTy_of_core core (H.defines c hR q hq mctx cctx adm)

/-- **(H2, ND)** The callee of an ordinary call of a reached parent is reached. -/
theorem reach_callee_of_t1ND {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1HypND L P Reach DataOk) (p : Pkg ι dom) (hRp : Reach p.decl)
    (hPp : P p.decl = some p) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none) :
    Reach (p.d.shape.insts[k]'hk).1 :=
  H.closed p.decl hRp p hPp k hk hord

/-- **(H3, ND)** The `houtTy` row from the closing witness of `hDG_CLOSINGRUN`. -/
theorem houtTy_of_closingND {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) {Reach : Lean.Name → Prop}
    {DataOk : Pkg ι dom → Prop} (H : T1HypND L P Reach DataOk) (p q : Pkg ι dom) (k : Nat)
    (hk : k < p.d.shape.insts.length) (hRc : Reach (p.d.shape.insts[k]'hk).1)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1) :
    ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width := by
  obtain ⟨r, _, hS, -⟩ := hDG_CLOSINGRUN
  exact houtTy_of_realChildND L P H hRc hDG_GENP hS.1

/-- **(H4, ND) one-output parents**: §7.7 (c) without `houtTy`. -/
theorem callTie_of_served_oneOut_t1ND {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (h1 : p.d.shape.instFields = []) (hOW : OneOutWidth P p k) :
    CallTie p q k hk :=
  callTie_of_served_oneOut L P p q k hk hDG_GENP hDG_CLOSINGRUN hDG_SEM
    (houtTy_of_closingND L P H p q k hk (reach_callee_of_t1ND L P H p hRp hPp k hk hord) hDG_GENP hDG_CLOSINGRUN)
    h1 hOW

/-- **(H4, ND) group parents**: §7.8 without `houtTy`. -/
theorem callTie_of_served_kidW_closing_t1ND {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (p q : Pkg ι dom)
    (k : Nat) (hk : k < p.d.shape.insts.length) {Reach : Lean.Name → Prop} {DataOk : Pkg ι dom → Prop}
    (H : T1HypND L P Reach DataOk) (hRp : Reach p.decl) (hPp : P p.decl = some p)
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none)
    (hDG_GENP : P (p.d.shape.insts[k]'hk).1 = some q)
    (hDG_CLOSINGRUN : ∃ (r : Tools.ShippingChildInv.Res) (dsn : Sparkle.IR.AST.Design),
      ShipsRes L P (p.d.shape.insts[k]'hk).1 r ∧
      (∀ g ∈ r.2.modules, Sparkle.IR.Machine.moduleByName dsn.modules g.name = some g) ∧
      Sparkle.IR.Machine.moduleByName dsn.modules r.1.name = some r.1 ∧ FieldRowAt p k r.1)
    (hDG_SEM : GenExtAtCall p q k hk)
    (hG : p.d.shape.instFields ≠ [])
    (hkidW : ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
      Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
      ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
        (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth) =
          some pt.ty.bitWidth) :
    CallTie p q k hk :=
  callTie_of_served_kidW_closing L P p q k hk hDG_GENP hDG_CLOSINGRUN hDG_SEM
    (houtTy_of_closingND L P H p q k hk (reach_callee_of_t1ND L P H p hRp hPp k hk hord) hDG_GENP hDG_CLOSINGRUN)
    hG hkidW

end Tools.ShippingGen2
