import Tools.ShippingSrm7Rank
import Tools.ShippingSrm5Deep
import Tools.ShippingSrm5Ident
import Tools.ShippingSrm4Core2
import Tools.ShippingSrm4Kid
-- BUILT (unit SRM12): dev runs a5 (Corr + CorrTest) exit 0, a8 (audit) exit 0; the final-SHA rebuild is in REPORT-SRM12.md.
-- SCOPE (binding): the CORRESPONDENCE between the SRM7 call-graph edges (`Kid = (callee name, origin)`, read from `X.machineData.shape.instTagged`) and the INSTANCE STATEMENTS
-- `Stmt.inst mn iname conns` of the modules of the compiled design `D.modules`.
-- DEFINED (Props): `InstFwd ks body` (every instance statement targets `kidModName k` for an edge `k ∈ ks`, and `k` is a memory-origin edge iff the target name decodes as a memory module),
-- `InstBwd ks body` (every edge has an instance statement of `kidModName k`), `ModCorr g m`, `DesignCorr g ms`, `ChildCorr g O c`.  Memory-origin and ordinary edges are NOT merged:
-- `kidModName` sends an origin `.mem cb aw dw` to `ofMem cb aw dw` and every other origin to `ofDecl callee`, and `kidModName_mem_iff` records that the two kinds never share a name.
-- PROVED here, GENERIC over the machine closing (`MachineRanA`, i.e. `closeInstsG` + `ChildrenRealA`; no particular design): `ran_designCorr` (the module of a machine run, its optimised form, and
-- every module of the run's design `D`, from the per-kid facts `hname`/`hkids`), `memCallee_childCorr` (a `RealChildA` of a callee over `MemCalleeData`), `childCorr_noInst` (a plain leaf).
-- PREMISES of those theorems (named in the statements): `hname` (an ordinary kid's result is named `ofDecl callee`: obtained from the kid's `ChildIfaceP.name`), `hkids` (the callee's own
-- `ChildCorr`), `hgraph` (the graph entry of the declaration is `shape.instTagged`: by `decide`/`rfl` for a graph read from the machine data).  Not claimed: an arbitrary graph, or that the graph was read from the right declarations.
-- `RealChildA` is a history of past synthesis results, not semantic correctness in the current environment.  No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.
set_option autoImplicit false
namespace Tools.ShippingSrm12Corr
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Sparkle.Compiler.Elab
open Tools.ShippingChildInv Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildCacheA
open Tools.ShippingChildVCA Tools.ShippingChildRunA Tools.ShippingChildBndCore Tools.ShippingChildRunAKids
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineClosesData Tools.ShippingMachineCloses Tools.ShippingMachineAuto
open Tools.ShippingMemCloses Tools.ShippingCallsMemA
open Tools.ShippingSrm3Iface Tools.ShippingSrm3Callee
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (originAt)
open Sparkle.Compiler.MachMemory (memModule)
open Sparkle.IR.ModuleName (decode ofDecl ofMem Key)
open Tools.ShippingSrm7Rank (Kid CallGraph callees kidModName)
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The correspondence Props -/

/-- (forward) every instance statement of `body` targets `kidModName k` for an edge `k ∈ ks`, and the edge is a memory-origin edge exactly when the target name decodes as a built memory module -/
def InstFwd (ks : List Kid) (body : List Stmt) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
    ∃ k ∈ ks, kidModName k = mn ∧ ∀ cb aw dw, k.2 = InstOrigin.mem cb aw dw ↔ decode mn = some (Key.mem cb aw dw)

/-- (backward) every edge `k ∈ ks` has an instance statement of the module `kidModName k` in `body` (one statement may serve several edges) -/
def InstBwd (ks : List Kid) (body : List Stmt) : Prop :=
  ∀ k ∈ ks, ∃ iname conns, Stmt.inst (kidModName k) iname conns ∈ body

/-- the name of `m` is a compiler name: a declaration's module or a built memory module -/
def Named (m : Sparkle.IR.AST.Module) : Prop :=
  (∃ c, decode m.name = some (Key.decl c)) ∨ ∃ cb aw dw, decode m.name = some (Key.mem cb aw dw)

/-- **The module-level correspondence** against the graph `g`: the name is a compiler name; a memory-named module has no instance statement; a declaration-named module has a graph entry whose edges and
instance statements correspond in both directions (`InstFwd`, `InstBwd`) -/
def ModCorr (g : CallGraph) (m : Sparkle.IR.AST.Module) : Prop :=
  Named m ∧
  (∀ cb aw dw, decode m.name = some (Key.mem cb aw dw) → ∀ mn iname conns, Stmt.inst mn iname conns ∉ m.body) ∧
  (∀ c, decode m.name = some (Key.decl c) → ∃ ks, callees g c = some ks ∧ InstFwd ks m.body ∧ InstBwd ks m.body)

/-- every module of the list satisfies `ModCorr` -/
def DesignCorr (g : CallGraph) (ms : List Sparkle.IR.AST.Module) : Prop := ∀ m ∈ ms, ModCorr g m

/-- the correspondence for the result `y` (module and served design) of every `RealChildA` of the declaration `c` -/
def ChildCorr (g : CallGraph) (O : RefLawsAOps MkRefd mref cref) (c : Name) : Prop :=
  ∀ y : Res, RealChildA O c y → DesignCorr g (y.1 :: y.2.modules)

/-! ## Names of edges -/

theorem decode_ofMem (cb : Bool) (aw dw : Nat) : decode (ofMem cb aw dw) = some (Key.mem cb aw dw) := by
  rw [ofMem, Tools.ShippingModuleName.decode_encode]

theorem decode_ofDecl (c : Name) : decode (ofDecl c) = some (Key.decl c) := by
  rw [ofDecl, Tools.ShippingModuleName.decode_encode]

/-- an edge is a memory-origin edge exactly when its module name decodes as a built memory module (memory and ordinary edges never share a name) -/
theorem kidModName_mem_iff (k : Kid) (cb : Bool) (aw dw : Nat) :
    k.2 = InstOrigin.mem cb aw dw ↔ decode (kidModName k) = some (Key.mem cb aw dw) := by
  obtain ⟨n, o⟩ := k
  cases o with
  | ord => simp [kidModName, decode_ofDecl]
  | field i => simp [kidModName, decode_ofDecl]
  | mem cb' aw' dw' =>
    simp only [kidModName, decode_ofMem, Option.some.injEq, Key.mem.injEq, InstOrigin.mem.injEq]

/-- the module name of an edge decodes as a compiler name -/
theorem decode_kidModName (k : Kid) :
    (∃ c, decode (kidModName k) = some (Key.decl c)) ∨ ∃ cb aw dw, decode (kidModName k) = some (Key.mem cb aw dw) := by
  obtain ⟨n, o⟩ := k
  cases o with
  | ord => exact Or.inl ⟨n, decode_ofDecl n⟩
  | field i => exact Or.inl ⟨n, decode_ofDecl n⟩
  | mem cb aw dw => exact Or.inr ⟨cb, aw, dw, decode_ofMem cb aw dw⟩

/-- **The name of a call's result is the module name of its edge**: a memory origin builds `memModule` (named `ofMem`), any other origin's result is a `RealChildA`, named `ofDecl callee` by the premise `hn` -/
theorem kidTA_name {O : RefLawsAOps MkRefd mref cref} {o : InstOrigin} {c : Name} {y : Res}
    (h : KidTA O o c y) (hn : o.child? = none → RealChildA O c y → y.1.name = ofDecl c) :
    y.1.name = kidModName (c, o) := by
  cases o with
  | ord =>
    rcases h with h | ⟨_, h⟩
    · exact absurd h (by simp [InstOrigin.child?])
    · exact hn rfl h
  | field i =>
    rcases h with h | ⟨_, h⟩
    · exact absurd h (by simp [InstOrigin.child?])
    · exact hn rfl h
  | mem cb aw dw =>
    rcases h with h | ⟨h, _⟩
    · have : y = memModule cb aw dw := (Option.some.inj h).symm
      subst this
      exact Tools.ShippingMemOnlyNames.memModule_name cb aw dw
    · exact absurd h (by simp [InstOrigin.child?])

theorem instTagged_mem_idx (shape : MachineShape) {k : Nat} (hk : k < shape.insts.length) :
    ((shape.insts[k]).1, originAt shape k) ∈ shape.instTagged := by
  have hkT : k < shape.instTagged.length := by rw [Tools.ShippingInstTagged.instTagged_length]; exact hk
  have := List.getElem_mem hkT
  rwa [Tools.ShippingInstTagged.instTagged_getElem] at this

theorem instTagged_exists_idx (shape : MachineShape) {x : Kid} (hx : x ∈ shape.instTagged) :
    ∃ (k : Nat) (hk : k < shape.insts.length), x = ((shape.insts[k]).1, originAt shape k) := by
  obtain ⟨k, hkT, rfl⟩ := List.getElem_of_mem hx
  have hk : k < shape.insts.length := by rw [← Tools.ShippingInstTagged.instTagged_length]; exact hkT
  exact ⟨k, hk, Tools.ShippingInstTagged.instTagged_getElem shape hkT⟩

/-! ## Memory modules -/

theorem memModule_modCorr (g : CallGraph) (cb : Bool) (aw dw : Nat) : ModCorr g (memModule cb aw dw).1 := by
  have hn : (memModule cb aw dw).1.name = ofMem cb aw dw := Tools.ShippingMemOnlyNames.memModule_name cb aw dw
  refine ⟨Or.inr ⟨cb, aw, dw, by rw [hn, decode_ofMem]⟩, ?_, ?_⟩
  · intro _ _ _ _ mn iname conns h
    simp [memModule] at h
  · intro c hc
    rw [hn, decode_ofMem] at hc
    cases hc

/-- the served design of a built memory module is that module alone -/
theorem memModule_design_modules (cb : Bool) (aw dw : Nat) : (memModule cb aw dw).2.modules = [(memModule cb aw dw).1] := rfl

/-! ## One machine run: instance statements ↔ edges (GENERIC) -/

/-- **Forward half**: every instance statement of the module a machine run produced targets the module of an edge of `shape.instTagged` (memory origin ↔ memory name). Premise `hname`: an ordinary kid's result is named `ofDecl callee`. -/
theorem ran_instFwd (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    {M : Sparkle.IR.AST.Module} {D : Design}
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hname : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y → y.1.name = ofDecl (d.shape.insts[k]).1) :
    InstFwd d.shape.instTagged M.body := by
  intro mn iname conns hm
  obtain ⟨k, hk, y, -, hmn, -, -, hKT⟩ := Tools.ShippingSrm5Ident.inst_target_ranA O d ok hbody hC hslots hdomB ran mn iname conns hm
  have hy : y.1.name = kidModName ((d.shape.insts[k]).1, originAt d.shape k) := kidTA_name (hKT hfne) (hname k hk y)
  have hmn' : kidModName ((d.shape.insts[k]).1, originAt d.shape k) = mn := hy.symm.trans hmn.symm
  refine ⟨_, instTagged_mem_idx d.shape hk, hmn', fun cb aw dw => ?_⟩
  rw [← hmn']
  exact kidModName_mem_iff _ cb aw dw

/-- **Backward half**: every edge of `shape.instTagged` has an instance statement of its module in the module a machine run produced (`closeInstsG_calls`, one statement per call group). -/
theorem ran_instBwd (O : RefLawsAOps MkRefd mref cref) {c : Name} (d : MachineData)
    (hfne : d.shape.instFields ≠ [])
    {M : Sparkle.IR.AST.Module} {D : Design}
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hname : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y → y.1.name = ofDecl (d.shape.insts[k]).1) :
    InstBwd d.shape.instTagged M.body := by
  intro kk hkk
  obtain ⟨k, hk, rfl⟩ := instTagged_exists_idx d.shape hkk
  obtain ⟨_, bb, w9, w10, hrun9, t, t', d₀, run, hcl, hmt⟩ := ran
  rcases hmt with ⟨hno, -, -⟩ | ⟨-, children, hcc, hreal⟩
  · exact absurd (List.length_pos_iff.mp (by have := hk; omega) : d.shape.insts ≠ []) (by simp [hno])
  rcases hcc with ⟨hfe, -⟩ | ⟨hfe, hG, hMC⟩
  · exact absurd hfe hfne
  obtain ⟨st, hst, args, outs, child, mc, hcs, hmc, -, -, hchild⟩ :=
    Tools.ShippingMachineInstG.closeInstsG_calls hG k (by simpa using hk)
  obtain ⟨hlenC, hall⟩ := hreal
  obtain ⟨y, hy, hor⟩ := hall k hk
  have hKT := Tools.ShippingSrm4Core1.kidTA_ofO hk hMC hy hor
  have hyn : y.1.name = kidModName ((d.shape.insts[k]).1, originAt d.shape k) := kidTA_name hKT (hname k hk y)
  obtain ⟨_, _, iname, -, -, -, -, -, -, -, -, -, -, -, hstE⟩ := hcs
  have hmcn : mc.name = child.1.name := Tools.ShippingMachineInst.moduleByName_name hmc
  rw [hy, Option.map_some, Option.some.injEq] at hchild
  obtain ⟨conns, hstE'⟩ : ∃ conns, st = Stmt.inst mc.name iname conns := ⟨_, hstE⟩
  refine ⟨iname, conns, ?_⟩
  rw [← hyn, hchild, ← hmcn, ← hstE']
  exact hst

/-! ## The module of a run and every module of its design -/

theorem modCorr_of_run {g : CallGraph} {m : Sparkle.IR.AST.Module} {c : Name} (hn : m.name = ofDecl c) {ks : List Kid}
    (hgraph : callees g c = some ks) (hf : InstFwd ks m.body) (hb : InstBwd ks m.body) : ModCorr g m := by
  have hd : decode m.name = some (Key.decl c) := by rw [hn, decode_ofDecl]
  refine ⟨Or.inl ⟨c, hd⟩, ?_, ?_⟩
  · intro cb aw dw h
    rw [hd] at h
    cases h
  · intro c' hc'
    rw [hd, Option.some.injEq, Key.decl.injEq] at hc'
    subst hc'
    exact ⟨ks, hgraph, hf, hb⟩

/-- **GENERIC step.** For a machine run `ran` of declaration `c` (memory and/or ordinary calls, general closing), whose graph entry is `shape.instTagged`:
(i) its module `b` (the post-processed `M`), (ii) its optimised form, (iii) every module of its design `D` satisfy `ModCorr`.  Premises: `hname` (ordinary kids' result names), `hkids` (the callees' own `ChildCorr`). -/
theorem ran_designCorr (O : RefLawsAOps MkRefd mref cref) (g : CallGraph) {c : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    {M b : Sparkle.IR.AST.Module} {D : Design}
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (ran : Tools.ShippingParentRanA.MachineRanA O mctx cctx c d.shape M D)
    (hgraph : callees g c = some d.shape.instTagged)
    (hname : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y → y.1.name = ofDecl (d.shape.insts[k]).1)
    (hkids : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none →
      ChildCorr g O (d.shape.insts[k]).1) :
    ModCorr g b ∧ ModCorr g (checkedOptimize b) ∧ DesignCorr g D.modules := by
  obtain ⟨hMn, hbb, -, -, hmods, -⟩ := core_kids_facts_ranAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran
  have hfwd := ran_instFwd O d ok hbody hC hslots hdomB hfne ran hname
  have hbwd := ran_instBwd O d hfne ran hname
  have hbn : b.name = ofDecl c := (Tools.ShippingSrm5Deep.post_name hpost).trans hMn
  have hmb : ModCorr g b := modCorr_of_run hbn hgraph (hbb ▸ hfwd) (hbb ▸ hbwd)
  refine ⟨hmb, ?_, ?_⟩
  · have hgate : Sparkle.IR.RefineCheck.hierGate b = true :=
      Tools.ShippingSrm4Core2.core_hierGate_anyAM O d ok hbody hC hslots hdomB hins hfne outTy hpost ran
    refine modCorr_of_run ((Tools.ShippingModuleNames.checkedOptimize_name b).trans hbn) hgraph ?_ ?_
    · intro mn iname conns h
      exact (hbb ▸ hfwd) mn iname conns ((Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hgate mn iname conns).mp h)
    · intro kk hkk
      obtain ⟨iname, conns, h⟩ := (hbb ▸ hbwd) kk hkk
      exact ⟨iname, conns, (Tools.ShippingChecksDepthGate.checkedOptimize_inst_iff_gate hgate _ iname conns).mpr h⟩
  · intro g' hg'
    obtain ⟨k, hk, y, hKT, hor, -⟩ := hmods g' hg'
    rcases hKT with hmem | ⟨hnone, hre⟩
    · obtain ⟨cb, aw, dw, rfl⟩ := Tools.ShippingInstTagged.child?_eq_memModule hmem
      rcases hor with h | h
      · rw [h]; exact memModule_modCorr g cb aw dw
      · have : g' = (memModule cb aw dw).1 := by
          simpa [memModule_design_modules] using h
        rw [this]; exact memModule_modCorr g cb aw dw
    · have := hkids k hk hnone y hre
      rcases hor with h | h
      · exact this g' (by rw [h]; exact List.mem_cons_self)
      · exact this g' (List.mem_cons_of_mem _ h)

/-! ## Callees -/

/-- **`ChildCorr` of a callee over `MemCalleeData`** (memory and/or ordinary calls): every `RealChildA` of `C` and its served design satisfy `DesignCorr`.  Premises: `hord` (the ordinary kids' `ChildIfaceP`, as for `memCallee_kidHeight`),
`hnameK` (the interface name of kid `k` is `ofDecl` of its callee), `hgraph`, `hkids` (the ordinary kids' `ChildCorr`), the machine entry. -/
theorem memCallee_childCorr (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (g : CallGraph)
    {d : MachineData} {C : Name} {n : Nat} {nameK : Nat → String} {nk : Nat → Nat}
    {outsK namesK : Nat → List String} {names : List String}
    (hC : MemCalleeData d C n nameK nk outsK namesK names)
    (hord : ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx O.quiet mctx' cctx' →
      ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y → ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2)
    (hnameK : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none →
      nameK k = ofDecl (d.shape.insts[k]).1)
    (entry : MachineDefines mctx mref cctx cref C d.shape)
    (hgraph : callees g C = some d.shape.instTagged)
    (hkids : ∀ (k : Nat) (hk : k < d.shape.insts.length), (originAt d.shape k).child? = none →
      ChildCorr g O (d.shape.insts[k]).1) :
    ChildCorr g O C := by
  intro y hy
  obtain ⟨mctx', cctx', M, D, hpost, hdes, ran⟩ :=
    Tools.ShippingSrm4Core5.deepChild_ranAM O T d hC.ok hC.body (nDecl := n) hC.callsOk hC.slots hC.domB hC.insts_ne hC.fne hC.outTy
      (Tools.ShippingSrm4Kid.memCallee_hsep O hC hord) entry (fun m c hA => memCallee_closesA O T hA hC (hord m c hA)) hy
  have hname : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y' : Res), (originAt d.shape k).child? = none →
      RealChildA O (d.shape.insts[k]).1 y' → y'.1.name = ofDecl (d.shape.insts[k]).1 := by
    intro k hk y' hn hre
    obtain ⟨m', c', hA'⟩ := adm_of_realChildA hre
    rw [(hord m' c' hA' k hk y' hn hre).name]
    exact hnameK k hk hn
  obtain ⟨hb, -, hD⟩ := ran_designCorr O g d hC.ok hC.body (nDecl := n) hC.callsOk hC.slots hC.domB hC.insts_ne hC.fne hC.outTy hpost ran
    hgraph hname hkids
  intro m hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact hb
  · exact hD m (by rw [← hdes]; exact hm)

/-- **`ChildCorr` of a plain leaf** (no call entries, graph entry `[]`): a `ChildIfaceP` with NO instance targets (`names = []`) leaves nothing to correspond, and the served design is empty. -/
theorem childCorr_noInst (O : RefLawsAOps MkRefd mref cref) (g : CallGraph) {c : Name}
    (hgraph : callees g c = some [])
    (hiface : ∀ y : Res, RealChildA O c y → ∃ (nArgs : Nat) (outs : List String), ChildIfaceP (ofDecl c) nArgs outs [] y.1 y.2) :
    ChildCorr g O c := by
  intro y hy
  obtain ⟨nArgs, outs, hI⟩ := hiface y hy
  have hmods : y.2.modules = [] := by
    cases hm : y.2.modules with
    | nil => rfl
    | cons g0 gs =>
      have := hI.desNames g0 (by rw [hm]; exact List.mem_cons_self)
      simp at this
  intro m hm
  rw [hmods] at hm
  have hm' : m = y.1 := by simpa using hm
  subst hm'
  refine modCorr_of_run hI.name hgraph ?_ ?_
  · intro mn iname conns h
    have := hI.closed _ (List.mem_cons_self) mn iname conns h
    simp at this
  · intro k hk
    cases hk

/-! ## Consequence: the rank facts SRM5/SRM8 need, per instance statement -/

open Tools.ShippingSrm7Rank (rkOf declRank rkOf_edge)

theorem callees_mem_names (g : CallGraph) {c : Name} {ks : List Kid} (h : callees g c = some ks) : c ∈ g.map Prod.fst := by
  induction g with
  | nil => simp [callees] at h
  | cons e t ih =>
    obtain ⟨d, ks'⟩ := e
    unfold callees at h
    by_cases hd : (d == c) = true
    · have hdc : d = c := by simpa using hd
      simp [hdc]
    · rw [if_neg hd] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- **Per instance statement**: if the caller `m` (satisfying `ModCorr`) has the computed rank `r`, then the target `mn` of every instance statement of `m` has a computed rank `r' < r` (`rkOf_edge` through `InstFwd`) -/
theorem inst_rank (g : CallGraph) (F : Nat) {m : Sparkle.IR.AST.Module} (hm : ModCorr g m) {r : Nat}
    (hr : rkOf g F m.name = some r) {mn iname : String} {conns : List (String × Sparkle.IR.AST.Expr)}
    (hin : Stmt.inst mn iname conns ∈ m.body) : ∃ r', rkOf g F mn = some r' ∧ r' < r := by
  obtain ⟨hN, hmem, hdecl⟩ := hm
  rcases hN with ⟨c, hc⟩ | ⟨cb, aw, dw, hc⟩
  · obtain ⟨ks, hks, hfwd, -⟩ := hdecl c hc
    obtain ⟨k, hk, hkn, -⟩ := hfwd mn iname conns hin
    have hr' : declRank g F c = some r := by
      simp only [rkOf, hc] at hr
      exact hr
    obtain ⟨r', h1, h2⟩ := rkOf_edge hr' hks hk
    exact ⟨r', hkn ▸ h1, h2⟩
  · exact absurd hin (hmem cb aw dw hc mn iname conns)

end Tools.ShippingSrm12Corr

#print axioms Tools.ShippingSrm12Corr.kidModName_mem_iff
#print axioms Tools.ShippingSrm12Corr.ran_instFwd
#print axioms Tools.ShippingSrm12Corr.ran_instBwd
#print axioms Tools.ShippingSrm12Corr.ran_designCorr
#print axioms Tools.ShippingSrm12Corr.memCallee_childCorr
#print axioms Tools.ShippingSrm12Corr.childCorr_noInst
#print axioms Tools.ShippingSrm12Corr.callees_mem_names
#print axioms Tools.ShippingSrm12Corr.inst_rank
#print axioms Tools.ShippingSrm12Corr.modCorr_of_run
#print axioms Tools.ShippingSrm12Corr.kidTA_name
#print axioms Tools.ShippingSrm12Corr.memModule_modCorr
