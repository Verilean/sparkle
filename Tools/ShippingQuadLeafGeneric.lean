import Tools.ShippingTopShareNoParent
import Tools.ShippingSeqChildDeepIfacePA
import Tools.ShippingSeqChildDeepConsumerA
import Tools.ShippingCallsMemPinned
import Tools.ShippingServedRealA
-- BUILT (unit SR13): g2/g3 (module) exit 0, g8 (with Tests.Compiler.QuadLeafGenericTest) exit 0, g9 (Tests.Compiler.ChildVertAuditTest) exit 0 (dev runs); the final-SHA rebuild is in REPORT-SR13.md.
-- SCOPE (binding): DATA-GENERIC lemmas of the shared-leaf class "QUAD" — a parent `dP` whose four call entries are `[c₁, c₁, c₂, c₂]`
-- (all four origins without a memory child), two DIFFERENT callees `c₁`, `c₂` whose calls are ALL one NON-memory LEAF `G` (the SAME leaf for
-- both).  The statements are over `MachineData` / names / call lists; no declaration of `topshare`, `wrap`, `wrap3`, `acc` occurs here.
-- Existing statements are not changed: `Tools.ShippingTopShareRun`, `…Ret`, `…NoParent` and the `TopShare*Test` files are untouched; the
-- `topshare` instances may be re-derived from these lemmas (`Tests/Compiler/QuadLeafGenericTest.lean`).
-- WHAT IS PROVED here: the instance-level wiring that was written by hand for `topshare` (`MachineClosesAtA` / `CalleeOK` / `hsep` / `hgk` /
-- `ChildIfaceP` of a callee whose calls are one leaf, the parent's start-world no-fallback `MachineClosesAtStart0`, the parent's own run, the machine run).
-- WHAT STAYS A PREMISE (named, per field): the decidable data facts of `LeafData` / `LeafCalleeData` / `QuadParentData` (an instance proves them by
-- `decide` on the stored `machineData`), `MachineDefines` of the parent / callees / leaf (the entry's reads of the environment), `O`, `T`, `hA`,
-- `MachineCloses` of the leaf.  `RealChildA` is a history of past synthesis results, not semantic correctness in the current environment.
-- No `sorry`, no `axiom`, no `native_decide`, no new law / field.
namespace Tools.ShippingQuadLeafGeneric
open Tools.ShippingTopShareRun
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildBndInit Tools.ShippingChildBndCore Tools.ShippingChildInvA
open Tools.ShippingChildVCA Tools.ShippingChildFresh Tools.ShippingChildCacheA Tools.ShippingChildPinC
open Tools.ShippingChildDepthC Tools.ShippingChildRunA
open Tools.ShippingSharedLeafCoh Tools.ShippingLeafMissCoh Tools.ShippingSharedLeafHit
open Tools.ShippingSharedLeafExt Tools.ShippingLeafKeepCache Tools.ShippingLeafBodyCi Tools.ShippingLeafTermKeeps
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineCloses Tools.ShippingSeqChildIface Tools.ShippingSeqChildIfaceA
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMixedEntrySoundness
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingChildRunAKids Tools.ShippingMachineOutcomeA3 Tools.ShippingChildCoreC Tools.ShippingChildVertA
open Tools.ShippingClosedKinds Tools.ShippingSharedLeafNL
open Tools.ShippingMemCloses Tools.ShippingMachineClosesData
open Tools.ShippingInstTagged (originAt)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- An origin without a memory key builds no child. -/
theorem origin_child_none (o : InstOrigin) (h : memKey o = none) : o.child? = none := by
  cases o with
  | ord => rfl
  | field _ => rfl
  | mem c a d => exact absurd h (by simp [memKey])

/-! ## The leaf -/

/-- The data half of `LeafOK` (no environment reads): generated sequential leaf, no instances, output types match their widths. -/
structure LeafData (d : MachineData) : Prop where
  ok : d.ok = true
  body : d.shape.body = quote d.dom
    (fun j => inputExpr d.shape.binders.length (d.bpos j))
    (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed
  insts : d.shape.insts = []
  outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width

/-- The number of the leaf's own (non-domain) inputs — the `nk` of the callers' `ChildIfaceP` (the generator's `epD2M{i}_G_nk`, read off the data). -/
noncomputable def leafNk (d : MachineData) : Nat :=
  ((d.shape.binders.take (d.shape.binders.length - d.shape.layout.slots.length - d.shape.layout.lets)).filter
    fun x => x.2 != .domain).length

theorem leafOK_of_data {G : Name} {dG : MachineData} (hG : LeafData dG)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) :
    LeafOK mctx mref cctx cref G :=
  ⟨dG, hG.ok, hG.body, hG.insts, hG.outTy, hR0, hcl⟩

/-! ## A callee whose calls are all ONE non-memory leaf -/

/-- The data facts of a callee `dC` (named `C`, `n` declared inputs) all of whose call instances call the leaf `G` (`dG`) without a memory origin. -/
structure LeafCalleeData (dC dG : MachineData) (C G : Name) (n : Nat) : Prop where
  ok : dC.ok = true
  body : dC.shape.body = quote dC.dom
    (fun j => inputExpr dC.shape.binders.length (dC.bpos j))
    (fun j => inputExpr dC.shape.binders.length (dC.vpos j)) dC.packed
  alias : dC.letsAliasOk = true
  callsOk : dC.callsOk n = true
  slots : dC.ss.length = dC.shape.layout.slots.length
  domB : ∀ b ∈ dC.shape.binders.drop n, b.2 ≠ .domain
  insts_ne : dC.shape.insts ≠ []
  fne : dC.shape.instFields ≠ []
  kids : ∀ (k : Nat) (hk : k < dC.shape.insts.length),
    (dC.shape.insts[k]).1 = G ∧ memKey (originAt dC.shape k) = none
  tagged : ∀ x ∈ dC.shape.instTagged, x.1 = G ∧ x.2.child? = none
  argsN : ∀ (k : Nat) (hk : k < dC.shape.insts.length), leafNk dG = (dC.shape.insts[k]).2.1.length
  fieldOut : ∀ (k : Nat), k < dC.shape.insts.length →
    dC.shape.instFields.getD k "" ∈ dG.shape.layout.outs.map (·.name)
  fieldsNd : ∀ (k : Nat) (hk : k < dC.shape.insts.length) (k' : Nat) (hk' : k' < dC.shape.insts.length),
    (dC.shape.insts[k]).1 = (dC.shape.insts[k']).1 →
    memKey (originAt dC.shape k) = memKey (originAt dC.shape k') →
    (dC.shape.insts[k]).2.1 = (dC.shape.insts[k']).2.1 →
    dC.shape.instFields.getD k "" = dC.shape.instFields.getD k' "" → k = k'
  outHead : ∀ o ∈ dC.shape.layout.outs, o.name.toList.head? ≠ some 'i'
  outTy : ∀ o ∈ dC.shape.layout.outs, o.ty.bitWidth = o.width
  nomem : ∀ x ∈ dC.shape.instTagged, x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true
  slotsNe : dC.shape.layout.slots ≠ []
  hkD : n ≤ dC.bsIn.length
  hIlen : (dC.bsIn.drop n).length = dC.shape.insts.length
  hSL : ∀ b ∈ dC.slotBs ++ dC.letBs, b.2 ≠ .domain
  hSlen : dC.slotBs.length = dC.shape.layout.slots.length
  hLlen : dC.letBs.length = dC.shape.layout.lets
  hNIn : machNIn dC.shape = ((dC.bsIn.take n).filter (fun b => b.2 != .domain)).length
  GneC : G ≠ C

/-- `MachineClosesAtA` of a callee whose calls are one leaf. -/
theorem leafCallee_closesA (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {dC dG : MachineData} {C G : Name} {n : Nat}
    (hG : LeafData dG) (hC : LeafCalleeData dC dG C G n)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) :
    MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx C dC.shape := by
  have hent := hC.kids
  have hkid : ∀ (k : Nat) (hk : k < dC.shape.insts.length) (y : Res),
      Tools.ShippingCallsMemA.KidTA O (originAt dC.shape k) (dC.shape.insts[k]).1 y →
      ChildIfaceP (Sparkle.IR.ModuleName.ofDecl G) (leafNk dG)
        (dG.shape.layout.outs.map (·.name)) [] y.1 y.2 := by
    intro k hk y hy
    obtain ⟨hn, ho⟩ := hent k hk
    unfold Tools.ShippingCallsMemA.KidTA at hy
    rw [origin_child_none _ ho] at hy
    rcases hy with hy | ⟨-, hre⟩
    · exact absurd hy (by show (none : Option _) ≠ some y; exact fun h => nomatch h)
    · rw [hn] at hre
      have hG' := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O dG hG.ok hG.body hG.insts hG.outTy hR0 hcl hre
      exact Tools.ShippingCallsKidsD.ChildIfaceD.toP (Tools.ShippingCallsKidsD.ChildIfaceG.toD hG')
        (fun hx => nomatch hx)
  intro tenv
  exact Tools.ShippingCallsMemPinned.machineClosesAtA_of_memKids' (tenv := tenv) (nDecl := n) O T hA dC
    hC.ok hC.body hC.alias hC.callsOk hC.slots hC.domB (fun h0 => hC.fne h0)
    (fun _ => Sparkle.IR.ModuleName.ofDecl G) (fun _ => leafNk dG)
    (fun _ => dG.shape.layout.outs.map (·.name)) (fun _ => [])
    hkid hC.argsN hC.fieldOut hC.fieldsNd
    (fun k hk k' hk' _ => by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)
    (fun k hk => Tools.ShippingModuleName.ofDecl_ne hC.GneC)
    (fun gi k hk o ho => Tools.ShippingCallsGate.instName_ne_of_head (hC.outHead o ho) gi _)
    (fun k hk hx => nomatch hx)
    (fun k hk k' hk' hne => (hne (by
      obtain ⟨h1, h2⟩ := hent k hk
      obtain ⟨h1', h2'⟩ := hent k' hk'
      exact ⟨h1.trans h1'.symm, by rw [h2, h2'] <;> rfl⟩)).elim)

/-- The callee's results are separated from its own name (`hsep` of `deepChild_ifaceP`). -/
theorem leafCallee_hsep (O : RefLawsAOps MkRefd mref cref) {dC dG : MachineData} {C G : Name} {n : Nat}
    (hG : LeafData dG) (hC : LeafCalleeData dC dG C G n)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) :
    ∀ (k : Nat) (hk : k < dC.shape.insts.length) (y' : Res),
      RealChildA O (dC.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ≠ (Sparkle.IR.ModuleName.ofDecl C) := by
  refine Tools.ShippingSeqChildDeepConsumerA.hsep_of_leaf_kids (mctx := mctx) (cctx := cctx) O dC ?_
    (fun k hk => by rw [(hC.kids k hk).1]; exact hC.GneC)
  intro k hk
  rw [(hC.kids k hk).1]
  exact ⟨dG, hG.ok, hG.body, hG.insts, hG.outTy, hR0, hcl⟩

/-- The callee's results contain only modules named like the leaf and instantiate only the leaf (`hgk`). -/
theorem leafCallee_hgk (O : RefLawsAOps MkRefd mref cref) {dC dG : MachineData} {C G : Name} {n : Nat}
    (hG : LeafData dG) (hC : LeafCalleeData dC dG C G n)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) :
    ∀ (k : Nat) (hk : k < dC.shape.insts.length) (y' : Res),
      RealChildA O (dC.shape.insts[k]).1 y' →
      ∀ g ∈ y'.1 :: y'.2.modules, g.name ∈ [Sparkle.IR.ModuleName.ofDecl G] ∧
        ∀ mn i conns, Sparkle.IR.AST.Stmt.inst mn i conns ∈ g.body → mn ∈ [Sparkle.IR.ModuleName.ofDecl G] := by
  intro k hk y' hy g hg
  rw [(hC.kids k hk).1] at hy
  have hI := Tools.ShippingSeqChildIfaceA.seqChild_of_realA O dG hG.ok hG.body hG.insts hG.outTy hR0 hcl hy
  rcases List.mem_cons.mp hg with e | hin
  · subst e
    refine ⟨by rw [hI.name]; exact List.mem_singleton_self _, fun mn i conns hm => ?_⟩
    have := List.all_eq_true.mp hI.seqOk _ hm
    simp [Sparkle.IR.OptCheck.seqStmtOk] at this
  · rw [hI.design] at hin
    cases hin

/-- `ChildIfaceP` of the callee's result (interface of a callee whose calls are one leaf). -/
theorem leafCallee_ifaceP (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {dC dG : MachineData} {C G : Name} {n : Nat}
    (hG : LeafData dG) (hC : LeafCalleeData dC dG C G n)
    (entry : MachineDefines mctx mref cctx cref C dC.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {y : Res} (h : RealChildA O C y) :
    ChildIfaceP (Sparkle.IR.ModuleName.ofDecl C) (machNIn dC.shape)
      (dC.shape.layout.outs.map (·.name)) [Sparkle.IR.ModuleName.ofDecl G] y.1 y.2 :=
  Tools.ShippingSeqChildDeepIfacePA.deepChild_ifaceP O T dC hC.ok hC.body (nDecl := n)
    hC.callsOk hC.slots hC.domB hC.insts_ne hC.fne hC.outTy hC.nomem hC.slotsNe n hC.hkD hC.hIlen hC.hSL hC.hSlen hC.hLlen hC.hNIn
    _ (leafCallee_hgk O hG hC hR0 hcl) (leafCallee_hsep O hG hC hR0 hcl) entry
    (fun _ _ hA' => leafCallee_closesA O T hA' hG hC (Tools.ShippingReflectCtx.MachineDefines.ctx hR0) hcl) h

/-- `CalleeOK` of a callee whose calls are one leaf (the bundle consumed by `topshare_closing4` & co). -/
theorem leafCallee_calleeOK (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {dC dG : MachineData} {C G : Name} {n : Nat}
    (hG : LeafData dG) (hC : LeafCalleeData dC dG C G n)
    (entry : MachineDefines mctx mref cctx cref C dC.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) :
    CalleeOK O mctx cctx C dC :=
  ⟨hC.ok, hC.body, ⟨n, hC.callsOk, hC.domB⟩, hC.slots, hC.insts_ne, hC.fne,
    fun x hx => by
      obtain ⟨h1, h2⟩ := hC.tagged x hx
      rw [h1]; exact ⟨h2, leafOK_of_data hG hR0 hcl⟩,
    fun k hk => by rw [(hC.kids k hk).1]; exact hC.GneC,
    entry, leafCallee_closesA O T hA hG hC hR0 hcl⟩

/-! ## The parent with the call list `[c₁, c₁, c₂, c₂]` -/

/-- the callee name at call `k` (`k < 2` : first callee) -/
def quadName (c₁ c₂ : Name) (k : Nat) : String :=
  if k < 2 then Sparkle.IR.ModuleName.ofDecl c₁ else Sparkle.IR.ModuleName.ofDecl c₂
/-- the callee's own-input count at call `k` -/
noncomputable def quadNk (d₁ d₂ : MachineData) (k : Nat) : Nat :=
  if k < 2 then machNIn d₁.shape else machNIn d₂.shape
/-- the callee's output names at call `k` -/
noncomputable def quadOuts (d₁ d₂ : MachineData) (k : Nat) : List String :=
  if k < 2 then d₁.shape.layout.outs.map (·.name) else d₂.shape.layout.outs.map (·.name)
/-- the names of the callee's grandchildren (the shared leaf) -/
def quadNames (G : Name) (_ : Nat) : List String := [Sparkle.IR.ModuleName.ofDecl G]

/-- The decidable data facts of the PARENT `dP` (named `c`, `n` declared inputs) with the call list `[c₁, c₁, c₂, c₂]`. -/
structure QuadParentData (dP d₁ d₂ : MachineData) (c c₁ c₂ G : Name) (n : Nat) : Prop where
  ok : dP.ok = true
  body : dP.shape.body = quote dP.dom
    (fun j => inputExpr dP.shape.binders.length (dP.bpos j))
    (fun j => inputExpr dP.shape.binders.length (dP.vpos j)) dP.packed
  alias : dP.letsAliasOk = true
  callsOk : dP.callsOk n = true
  slots : dP.ss.length = dP.shape.layout.slots.length
  domB : ∀ b ∈ dP.shape.binders.drop n, b.2 ≠ .domain
  insts_ne : dP.shape.insts ≠ []
  fne : dP.shape.instFields ≠ []
  names : dP.shape.instTagged.map (·.1) = [c₁, c₁, c₂, c₂]
  child : ∀ x ∈ dP.shape.instTagged, x.2.child? = none
  len4 : dP.shape.insts.length = 4
  nomemKey : ∀ (k : Nat) (hk : k < dP.shape.insts.length), memKey (originAt dP.shape k) = none
  argsN : ∀ (k : Nat) (hk : k < dP.shape.insts.length), quadNk d₁ d₂ k = (dP.shape.insts[k]).2.1.length
  fieldOut : ∀ (k : Nat), k < dP.shape.insts.length → dP.shape.instFields.getD k "" ∈ quadOuts d₁ d₂ k
  fieldsNd : ∀ (k : Nat) (hk : k < dP.shape.insts.length) (k' : Nat) (hk' : k' < dP.shape.insts.length),
    (dP.shape.insts[k]).1 = (dP.shape.insts[k']).1 →
    memKey (originAt dP.shape k) = memKey (originAt dP.shape k') →
    (dP.shape.insts[k]).2.1 = (dP.shape.insts[k']).2.1 →
    dP.shape.instFields.getD k "" = dP.shape.instFields.getD k' "" → k = k'
  sep : ∀ (k : Nat) (hk : k < dP.shape.insts.length) (k' : Nat) (hk' : k' < dP.shape.insts.length),
    quadName c₁ c₂ k = quadName c₁ c₂ k' →
    (dP.shape.insts[k]).1 = (dP.shape.insts[k']).1 ∧ memKey (originAt dP.shape k) = memKey (originAt dP.shape k')
  outHead : ∀ o ∈ dP.shape.layout.outs, o.name.toList.head? ≠ some 'i'
  c12 : c₁ ≠ c₂
  cne1 : c ≠ c₁
  cne2 : c ≠ c₂
  cneG : c ≠ G

/-- The call list of a parent: four origins without a child, in the shape `[c₁, c₁, c₂, c₂]` (generic form of `topshare_instTagged_shape`). -/
theorem quad_shape {dP : MachineData} {c₁ c₂ : Name}
    (hnames : dP.shape.instTagged.map (·.1) = [c₁, c₁, c₂, c₂])
    (hchild : ∀ x ∈ dP.shape.instTagged, x.2.child? = none) :
    ∃ o₁ o₁' o₂ o₂' : InstOrigin, o₁.child? = none ∧ o₁'.child? = none ∧ o₂.child? = none ∧ o₂'.child? = none ∧
      dP.shape.instTagged = [(c₁, o₁), (c₁, o₁'), (c₂, o₂), (c₂, o₂')] := by
  revert hnames hchild
  generalize dP.shape.instTagged = L
  intro h1 h2
  rcases L with _ | ⟨⟨n1, o1⟩, _ | ⟨⟨n2, o2⟩, _ | ⟨⟨n3, o3⟩, _ | ⟨⟨n4, o4⟩, _ | ⟨e, L⟩⟩⟩⟩⟩
  · simp at h1
  · simp at h1
  · simp at h1
  · simp at h1
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h1
    obtain ⟨e1, e2, e3, e4⟩ := h1
    subst e1 e2 e3 e4
    simp at h2
    obtain ⟨a1, a2, a3, a4⟩ := h2
    exact ⟨o1, o2, o3, o4, a1, a2, a3, a4, rfl⟩
  · simp at h1

/-- **`MachineClosesAtStart0` of the parent DERIVED** (generic form of `topshare_closes0`): the machine synthesis of a parent with the call list
`[c₁, c₁, c₂, c₂]` (two callees whose calls are one shared non-memory leaf `G`) does not fall back at the entry's start world. -/
theorem quad_closes0 (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {dP d₁ d₂ dG : MachineData} {c c₁ c₂ G : Name} {nP n₁ n₂ : Nat}
    (hP : QuadParentData dP d₁ d₂ c c₁ c₂ G nP)
    (hG : LeafData dG) (h₁ : LeafCalleeData d₁ dG c₁ G n₁) (h₂ : LeafCalleeData d₂ dG c₂ G n₂)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape) :
    MachineClosesAtStart0 (mref := mref) (cref := cref) O mctx cctx c dP.shape := by
  obtain ⟨o₁, o₁', o₂, o₂', ho₁, ho₁', ho₂, ho₂', hPt⟩ := quad_shape hP.names hP.child
  have hc2not : ∀ k (hk : k < d₁.shape.insts.length), (d₁.shape.insts[k]).1 ≠ c₂ := by
    intro k hk e
    rw [(h₁.kids k hk).1] at e
    exact h₂.GneC e
  intro tenv b w9 r w10 hj hcv hr
  exact machineSynth_ne_none4 O hA hP.c12 ho₁ ho₁' ho₂ ho₂' dP hP.ok hP.body hP.alias hP.callsOk hP.slots hP.domB
    hP.insts_ne hP.fne hPt hP.len4 hP.nomemKey _ _
    (leafCallee_calleeOK O T hA hG h₁ entry₁ hR0 hcl) (leafCallee_calleeOK O T hA hG h₂ entry₂ hR0 hcl) hc2not
    (quadName c₁ c₂) (quadNk d₁ d₂) (quadOuts d₁ d₂) (quadNames G)
    (fun y hy k hk => by
      have := leafCallee_ifaceP O T hA hG h₁ entry₁ hR0 hcl hy
      simpa [quadName, quadNk, quadOuts, quadNames, if_pos hk] using this)
    (fun y hy k hk2 hk4 => by
      have := leafCallee_ifaceP O T hA hG h₂ entry₂ hR0 hcl hy
      simpa [quadName, quadNk, quadOuts, quadNames, if_neg (Nat.not_lt.mpr hk2)] using this)
    hP.argsN hP.fieldOut hP.fieldsNd hP.sep
    (fun k hk => by
      unfold quadName
      split
      · exact Tools.ShippingModuleName.ofDecl_ne (Ne.symm hP.cne1)
      · exact Tools.ShippingModuleName.ofDecl_ne (Ne.symm hP.cne2))
    (fun gi k _ o ho => Tools.ShippingCallsGate.instName_ne_of_head (hP.outHead o ho) gi _)
    (fun k hk hx => Tools.ShippingModuleName.ofDecl_ne hP.cneG (List.mem_singleton.mp hx))
    hj hcv hr

/-- `MachineRunJQC` of the parent at depth `1` from ONE core run at depth `0` (generic form of `topshare_machineRun`). -/
theorem quad_machineRun (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {dP d₁ d₂ dG : MachineData} {c c₁ c₂ G : Name} {nP n₁ n₂ : Nat}
    (hP : QuadParentData dP d₁ d₂ c c₁ c₂ G nP)
    (hG : LeafData dG) (h₁ : LeafCalleeData d₁ dG c₁ G n₁) (h₂ : LeafCalleeData d₂ dG c₂ G n₂)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hw : JQC O 0 w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (m, design) w') :
    Tools.ShippingServedRealA.MachineRunJQC O mctx cctx 1 c dP.shape m design := by
  obtain ⟨tenv, b, w9, w10, hmach, hw9, -, -⟩ :=
    core_run_tracked0' O hA entryP (quad_closes0 O T hA hP hG h₁ h₂ entry₁ entry₂ hR0 hcl) hw hcore
  exact ⟨tenv, b, w9, w10, hmach, hw9⟩

/-- **The parent's own run with the returned value linked and no parent module in `Dg`** (generic form of the premises-wiring of
`topshare_returned`; the conclusion is that of `Tools.ShippingTopShareNoParent.topshare_entry_run4_ret_np`). -/
theorem quad_entry_run_ret_np (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref)
    (hA : AdmCtx O.quiet mctx cctx) {dP d₁ d₂ dG : MachineData} {c c₁ c₂ G : Name} {nP n₁ n₂ : Nat}
    (hP : QuadParentData dP d₁ d₂ c c₁ c₂ G nP)
    (hG : LeafData dG) (h₁ : LeafCalleeData d₁ dG c₁ G n₁) (h₂ : LeafCalleeData d₂ dG c₂ G n₂)
    (entryP : MachineDefines mctx mref cctx cref c dP.shape)
    (entry₁ : MachineDefines mctx mref cctx cref c₁ d₁.shape)
    (entry₂ : MachineDefines mctx mref cctx cref c₂ d₂.shape)
    (hR0 : MachineDefines mctx mref cctx cref G dG.shape)
    (hcl : ∀ (mc : Meta.Context) (cc : Core.Context), MachineCloses mc mref cc cref G dG.shape)
    {w w' : Void IO.RealWorld} {y : Res} (hw : JQC O 0 w)
    (h : RunsTo (synthesizeCombinational c) mctx mref cctx cref w y w') :
    ∃ (y₁ y₂ : Res) (t t' : Sparkle.IR.AST.Module) (d₀ : Sparkle.IR.AST.Design)
      (M : Sparkle.IR.AST.Module) (Dg : Sparkle.IR.AST.Design) (w10 wc : Void IO.RealWorld),
      closeLets dP.shape.layout.lets t = some t' ∧
      some (M, Dg) = Sparkle.IR.Machine.closeInstsG (machNIn dP.shape) dP.shape.insts.length
        dP.shape.layout.slots.length (t.inputs.map (·.name)) (dP.shape.insts.map (·.2.1))
        dP.shape.instFields [y₁, y₁, y₂, y₂] (closeMachine dP.shape.layout t', d₀) ∧
      JQC O 0 w' ∧ cv w' = cv w10 ∧
      CacheClosed (cv w10) ∧ KeyTop (cv w10) ∧ CacheCoh (cv w10) ∧
      (cv w10).get? c₁ = some y₁ ∧ (cv w10).get? c₂ = some y₂ ∧
      (∀ a ∈ ModsOf y₁, ∀ b ∈ ModsOf y₂, a.name = b.name → a = b) ∧
      (∀ k₁ (hk₁ : k₁ < d₁.shape.insts.length) k₂ (hk₂ : k₂ < d₂.shape.insts.length),
        (d₁.shape.insts[k₁]).1 = (d₂.shape.insts[k₂]).1 →
        ∃ e, (cv w10).get? (d₁.shape.insts[k₁]).1 = some e ∧ e.1 ∈ y₁.2.modules ∧ e.1 ∈ y₂.2.modules) ∧
      RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, Dg) wc ∧ cv wc = cv w10 ∧
      ((y.1 = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∧
          y.2 = topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg) ∨
       (y.1 = Sparkle.IR.RefineCheck.mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M) ∧
          y.2 = topMap M.name Sparkle.IR.RefineCheck.mergeChecked
            (topMap M.name Sparkle.IR.ZeroWidth.dropZeroWidthModule Dg))) ∧
      (∀ x ∈ Dg.modules, x.name ≠ M.name) := by
  obtain ⟨o₁, o₁', o₂, o₂', ho₁, ho₁', ho₂, ho₂', hPt⟩ := quad_shape hP.names hP.child
  have hc2not : ∀ k (hk : k < d₁.shape.insts.length), (d₁.shape.insts[k]).1 ≠ c₂ := by
    intro k hk e
    rw [(h₁.kids k hk).1] at e
    exact h₂.GneC e
  exact Tools.ShippingTopShareNoParent.topshare_entry_run4_ret_np O hA hP.c12 ho₁ ho₁' ho₂ ho₂' dP hP.ok hP.body
    hP.insts_ne hP.fne hP.callsOk hP.slots hP.domB hPt entryP
    (quad_closes0 O T hA hP hG h₁ h₂ entry₁ entry₂ hR0 hcl) d₁ d₂
    (leafCallee_calleeOK O T hA hG h₁ entry₁ hR0 hcl) (leafCallee_calleeOK O T hA hG h₂ entry₂ hR0 hcl) hc2not
    hP.cne1 hP.cne2
    (fun k hk e => hP.cneG (by rw [← e, (h₁.kids k hk).1]))
    (fun k hk e => hP.cneG (by rw [← e, (h₂.kids k hk).1])) hw h

end Tools.ShippingQuadLeafGeneric

#print axioms Tools.ShippingQuadLeafGeneric.leafCallee_closesA
#print axioms Tools.ShippingQuadLeafGeneric.leafCallee_hsep
#print axioms Tools.ShippingQuadLeafGeneric.leafCallee_hgk
#print axioms Tools.ShippingQuadLeafGeneric.leafCallee_ifaceP
#print axioms Tools.ShippingQuadLeafGeneric.leafCallee_calleeOK
#print axioms Tools.ShippingQuadLeafGeneric.quad_shape
#print axioms Tools.ShippingQuadLeafGeneric.quad_closes0
#print axioms Tools.ShippingQuadLeafGeneric.quad_machineRun
#print axioms Tools.ShippingQuadLeafGeneric.quad_entry_run_ret_np
