import Lean
import Tools.ShippingGen5PTShard
set_option autoImplicit false
-- D.D-4 final, Q-B connection per root (Issue sparkle-ledger-dd4-shard). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Ordinary definitions and theorems checked by the kernel.

/-! # `FGLedgerPremisesStmt` per root: `PT := PTcore ⊕ (the shards the root needs)`

* `compAll A Ss` composes the tables of the shards `Ss` onto `A` (in order); `rootPT Ss := compAll PTcore Ss`.
* `FGLedgerPremisesStmtRootAt PT` is the statement of `FGLedgerPremisesStmtPTC` with the table `PTcorpus` replaced by an arbitrary `PT` (nothing else changes);
  `FGLedgerPremisesStmtRoot Ss := FGLedgerPremisesStmtRootAt (rootPT Ss)`.
* Bridges: `FGLedgerPremisesStmtCV → ∀ Ss, FGLedgerPremisesStmtRoot Ss`; `FGLedgerPremisesStmtRoot [] ↔ FGLedgerPremisesStmtPTC` (`Iff.rfl`); an empty shard changes nothing.
* The named premises on the composed table split into core rows and, per shard, shard rows (`RootNamed`, `rootNamed_iff`). Nothing is assumed: they are `Prop` definitions.
* Nothing here adopts `PTcorpus`, G-PRIM or TRUSTED, and nothing here proves a shard row sound (`RowTypedAtV` / `RowTeleEvAt` of shard rows stay named premises). -/

namespace Tools.ShippingGen5PTRootShard
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5PTCorpus Tools.ShippingGen5PTShard

/-! ## Composition of a list of shards -/

/-- `A ⊕ S₁ ⊕ … ⊕ Sₙ` (left to right). -/
noncomputable def compAll (A : PrimTableK) : List PTShard → PrimTableK
  | [] => A
  | S :: Ss => compAll (A ⊕ₚ S.toPT) Ss

/-- The table of a root that needs the shards `Ss`. -/
noncomputable def rootPT (Ss : List PTShard) : PrimTableK := compAll PTcore Ss

theorem rootPT_nil : rootPT [] = PTcore := rfl

/-- Each shard is fresh against the composition of the core with the shards before it (decidable, `⟨rfl, rfl⟩` per root). -/
def FreshChain : PrimTableK → List PTShard → Prop
  | _, [] => True
  | A, S :: Ss => FreshAgainst A S ∧ FreshChain (A ⊕ₚ S.toPT) Ss

theorem compAll_keeps_tys {c : Name} {ls : List Level} {r : TyRow} :
    ∀ (Ss : List PTShard) (A : PrimTableK), A.tys c ls = some r → (compAll A Ss).tys c ls = some r
  | [], _, h => h
  | _ :: Ss, A, h => compAll_keeps_tys Ss _ (comp_tys_left h)

theorem compAll_keeps_tms {c : Name} {ls : List Level} {r : TmRow} :
    ∀ (Ss : List PTShard) (A : PrimTableK), A.tms c ls = some r → (compAll A Ss).tms c ls = some r
  | [], _, h => h
  | _ :: Ss, A, h => compAll_keeps_tms Ss _ (comp_tms_left h)

/-- The core keeps its rows in every root table. -/
theorem rootPT_keeps_core_tys {Ss : List PTShard} {c : Name} {ls : List Level} {r : TyRow} (h : PTcore.tys c ls = some r) : (rootPT Ss).tys c ls = some r :=
  compAll_keeps_tys Ss _ h
theorem rootPT_keeps_core_tms {Ss : List PTShard} {c : Name} {ls : List Level} {r : TmRow} (h : PTcore.tms c ls = some r) : (rootPT Ss).tms c ls = some r :=
  compAll_keeps_tms Ss _ h

/-- Under the chain of freshness, a row of a shard of the list stays in the composition (the shards are composed in order, the later ones cannot hide it). -/
theorem compAll_keeps_shard_tys {c : Name} {ls : List Level} {r : TyRow} :
    ∀ (Ss : List PTShard) (A : PrimTableK), FreshChain A Ss → ∀ S ∈ Ss, S.toPT.tys c ls = some r → (compAll A Ss).tys c ls = some r
  | [], _, _, S, hS, _ => by cases hS
  | T :: Ts, A, ⟨hf, hc⟩, S, hS, h => by
      rcases List.mem_cons.1 hS with rfl | hS'
      · exact compAll_keeps_tys Ts _ (comp_tys_right_excl hf.excl h)
      · exact compAll_keeps_shard_tys Ts _ hc S hS' h

theorem compAll_keeps_shard_tms {c : Name} {ls : List Level} {r : TmRow} :
    ∀ (Ss : List PTShard) (A : PrimTableK), FreshChain A Ss → ∀ S ∈ Ss, S.toPT.tms c ls = some r → (compAll A Ss).tms c ls = some r
  | [], _, _, S, hS, _ => by cases hS
  | T :: Ts, A, ⟨hf, hc⟩, S, hS, h => by
      rcases List.mem_cons.1 hS with rfl | hS'
      · exact compAll_keeps_tms Ts _ (comp_tms_right_excl hf.excl h)
      · exact compAll_keeps_shard_tms Ts _ hc S hS' h

theorem rootPT_keeps_shard_tys {Ss : List PTShard} (hf : FreshChain PTcore Ss) {S : PTShard} (hS : S ∈ Ss) {c : Name} {ls : List Level} {r : TyRow}
    (h : S.toPT.tys c ls = some r) : (rootPT Ss).tys c ls = some r := compAll_keeps_shard_tys Ss _ hf S hS h
theorem rootPT_keeps_shard_tms {Ss : List PTShard} (hf : FreshChain PTcore Ss) {S : PTShard} (hS : S ∈ Ss) {c : Name} {ls : List Level} {r : TmRow}
    (h : S.toPT.tms c ls = some r) : (rootPT Ss).tms c ls = some r := compAll_keeps_shard_tms Ss _ hf S hS h

/-- Origin of a row of the composition: a row of `A` or a row of one of the shards. -/
theorem compAll_origin_tms {c : Name} {ls : List Level} {r : TmRow} :
    ∀ (Ss : List PTShard) (A : PrimTableK), (compAll A Ss).tms c ls = some r →
      (∃ r', A.tms c ls = some r') ∨ ∃ S ∈ Ss, ∃ r', S.toPT.tms c ls = some r'
  | [], _, h => Or.inl ⟨r, h⟩
  | T :: Ts, A, h => by
      rcases compAll_origin_tms Ts (A ⊕ₚ T.toPT) h with ⟨r', h'⟩ | ⟨S, hS, r', h'⟩
      · simp only [comp, Option.or_eq_some_iff] at h'
        rcases h' with h' | ⟨_, h'⟩
        · exact Or.inl ⟨r', h'⟩
        · exact Or.inr ⟨T, List.mem_cons_self .., r', h'⟩
      · exact Or.inr ⟨S, List.mem_cons_of_mem _ hS, r', h'⟩

/-- Composition with an empty shard changes nothing. -/
theorem comp_empty (A : PrimTableK) : (A ⊕ₚ PTShard.empty.toPT) = A := by
  cases A with
  | mk t m =>
    simp only [comp, PrimTableK.mk.injEq]
    constructor
    · funext c ls
      simp only [PTShard.toPT, PTShard.empty]
      cases lvNats ls <;> simp
    · funext c ls
      simp only [PTShard.toPT, PTShard.empty]
      cases lvNats ls <;> simp

theorem rootPT_empty : rootPT [PTShard.empty] = PTcore := comp_empty PTcore

/-- The root table keeps the functional carrier. -/
theorem cvFinal_rootPT_functional (Ss : List PTShard) :
    Tools.ShippingGen5FG.ConstValueFunctional (Tools.ShippingGen5CVFinal.CVFinal (rootPT Ss)) :=
  Tools.ShippingGen5CVFinal.cvFinal_functional (rootPT Ss)

/-! ## Decidable coverage of a shard's keys by a table -/

/-- Every key of the shard (at its numeral levels) has a row in `PT`. -/
def Covers (PT : PrimTableK) (S : PTShard) : Bool :=
  S.tyKeys.all (fun k => (PT.tys k.1 (k.2.map natLv)).isSome) && S.tmKeys.all (fun k => (PT.tms k.1 (k.2.map natLv)).isSome)

/-! ## The statement per root -/

section stmt
open Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingGen5Acc Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Sparkle.IR.Semantics Sparkle.IR.Machine Sparkle.Core Sparkle.Core.Signal
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1
open Tools.ShippingGen5ConstValueESoundK (OblLbrZero)
open Tools.ShippingGen5EnvDeclClosed (KernelClosedInvariant)
open Tools.ShippingGen5CVFinal Tools.ShippingGen5RowTypedV Tools.ShippingGen5ConstValueEVL

/-- `FGLedgerPremisesStmtPTC` with `PTcorpus` replaced by the table `PT` (the same text; only the table differs). -/
def FGLedgerPremisesStmtRootAt (PT : PrimTableK) : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    -- carriers (binders, NOT hypotheses; their characterizing rows are in the registry)
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)        -- D.D-1
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)             -- A.P-05
    -- D.D-3 fixed (GP := genGP lvl (dataOfSound_initsOf lvl) genData₀); D.D-4 fixed (CV := CVFinal PT, PT := the root's table)
    (lvl : Lean.Expr → Nat)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    (L : Laws mref cref)                                                      -- A.P-01  (= T1L-01)
    -- outer hypotheses (closed Props)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)   -- C.EN-4
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)                                        -- C.RK-6
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),                      -- C.CV-4 (= T1L-43)
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp))
    (h_D_LBR : OblLbrZero),                                                                      -- named premise: lbr bridge (unresolved)
    ConstValueFunctional (CVFinal PT) ∧
    ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
      (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
      EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →     -- A.P-02 Start, A.P-04 run, D.D-1 ReflectsAll
      -- named premises on the entry environment (unresolved obligations of the carrier; ordinary hypotheses)
      KernelClosedInvariant (envAt cref w) →                                    -- EnvDeclClosed via OblLbrZero (audit: 0 counterexamples)
      LitRows PT (envAt cref w) →                                               -- Nat / String rows of PT
      OblRowTypedV PT (envAt cref w) →                                          -- RowTypedAtV rows (incl. the dependent ones)
      (∀ (c : Name) (ls : List Level), RowTeleEvAt PT (envAt cref w) c ls) →    -- RowTeleEvAt rows
      -- inner hypotheses; P := genGP lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w), Reach := TgtRun P declName  (Q-F2)
      (∀ c, TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName c → ∀ q : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) c = some q →      -- h_A_P06
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ c, TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName c → ∀ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) c = some p →      -- h_D_T4
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth) →
      -- conclusion: the tail of the FG_CONNECT body (FG.lean), unchanged except CV := CVFinal PT
      (∃ raw, Post b raw) ∧
      (∃ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) declName = some p) ∧
      (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat),
          genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
      DeclConnect (CVFinal PT) (envAt cref w) (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) (TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName)

/-- The statement of a root that needs the shards `Ss`: `PT := PTcore ⊕ₚ S₁ ⊕ₚ … ⊕ₚ Sₙ`. -/
noncomputable def FGLedgerPremisesStmtRoot (Ss : List PTShard) : Prop := FGLedgerPremisesStmtRootAt (rootPT Ss)

/-- The `PT`-parametric statement specialises to every table, so to every root table (nothing else changes). -/
theorem fgLedgerPremisesStmtRootAt_of_CV : FGLedgerPremisesStmtCV → ∀ PT, FGLedgerPremisesStmtRootAt PT := by
  unfold FGLedgerPremisesStmtCV FGLedgerPremisesStmtRootAt
  intro h PT ι dom mref cref ReflectsAll Post lvl genData₀ L h_C_EN4 h_C_RK6 h_C_CV4 h_D_LBR
  exact h ReflectsAll Post lvl genData₀ PT L h_C_EN4 h_C_RK6 h_C_CV4 h_D_LBR

theorem fgLedgerPremisesStmtRoot_of_CV : FGLedgerPremisesStmtCV → ∀ Ss, FGLedgerPremisesStmtRoot Ss :=
  fun h Ss => fgLedgerPremisesStmtRootAt_of_CV h _

theorem fgLedgerPremisesStmtRoot_of_H : FGLedgerPremisesStmtH → ∀ Ss, FGLedgerPremisesStmtRoot Ss :=
  fun h => fgLedgerPremisesStmtRoot_of_CV (fgLedgerPremisesStmtCV_of_H h)

/-- Bridge from `FGLedgerPremisesStmtPTC`: it is the statement of the root that needs no shard. -/
theorem fgLedgerPremisesStmtRoot_nil_iff : FGLedgerPremisesStmtRoot [] ↔ FGLedgerPremisesStmtPTC := Iff.rfl

theorem fgLedgerPremisesStmtRootAt_core_iff : FGLedgerPremisesStmtRootAt PTcorpus ↔ FGLedgerPremisesStmtPTC := Iff.rfl

/-- A root whose only shard is empty (e.g. `Tests.SignalLoopTest`) has exactly the statement `FGLedgerPremisesStmtPTC`. -/
theorem fgLedgerPremisesStmtRoot_empty_iff : FGLedgerPremisesStmtRoot [PTShard.empty] ↔ FGLedgerPremisesStmtPTC := by
  unfold FGLedgerPremisesStmtRoot
  rw [rootPT_empty]; exact Iff.rfl

end stmt

/-! ## How the named premises split on a composed table

The five named premises of the statement: `OblLbrZero`, `KernelClosedInvariant` (do not mention the table), `LitRows PT`, `OblRowTypedV PT`, `∀ c ls, RowTeleEvAt PT`.
On `PT = rootPT Ss`: `LitRows` comes from the core (`litRows_rootPT`), and the two row premises split into the rows of the core and, per shard, the rows at the shard's keys. -/

section split
open Tools.ShippingGen5CVFinal Tools.ShippingGen5RowTypedV Tools.ShippingGen5ConstValueEVL

/-- A statement about all keys splits into the keys with a core row and the keys of each shard (keys with no row at all are given by `hnone`). -/
theorem forall_split (Ss : List PTShard) (P : Name → List Level → Prop) (hnone : ∀ c ls, (rootPT Ss).tms c ls = none → P c ls) :
    (∀ c ls, P c ls) ↔ (∀ c ls, (PTcore.tms c ls).isSome → P c ls) ∧ ∀ S ∈ Ss, ∀ k ∈ S.tmKeys, P k.1 (k.2.map natLv) := by
  constructor
  · intro h
    exact ⟨fun c ls _ => h c ls, fun S _ k _ => h _ _⟩
  · rintro ⟨hc, hs⟩ c ls
    cases hr : (rootPT Ss).tms c ls with
    | none => exact hnone c ls hr
    | some r =>
      rcases compAll_origin_tms Ss PTcore hr with ⟨r', h'⟩ | ⟨S, hS, r', h'⟩
      · exact hc c ls (by simp [h'])
      · obtain ⟨ns, rfl, hk⟩ := PTShard.toPT_tms_some h'
        exact hs S hS (c, ns) hk

/-- Core part of `OblRowTypedV` / `RowTeleEvAt`: the keys that have a row in `PTcore`, stated on the table `PT`. -/
def CoreRowTypedV (PT : PrimTableK) (env : Environment) : Prop := ∀ c ls, (PTcore.tms c ls).isSome → RowTypedAtV PT env c ls
def CoreRowTeleEv (PT : PrimTableK) (env : Environment) : Prop := ∀ c ls, (PTcore.tms c ls).isSome → RowTeleEvAt PT env c ls
/-- Shard part: the rows at the keys of the shard `S` (a named premise PER SHARD). -/
def ShardRowTypedV (S : PTShard) (PT : PrimTableK) (env : Environment) : Prop := ∀ k ∈ S.tmKeys, RowTypedAtV PT env k.1 (k.2.map natLv)
def ShardRowTeleEv (S : PTShard) (PT : PrimTableK) (env : Environment) : Prop := ∀ k ∈ S.tmKeys, RowTeleEvAt PT env k.1 (k.2.map natLv)

/-- The two row premises of a shard (named; nothing here proves or assumes them). -/
def ShardPremises (S : PTShard) (PT : PrimTableK) (env : Environment) : Prop := ShardRowTypedV S PT env ∧ ShardRowTeleEv S PT env

theorem oblRowTypedV_split (Ss : List PTShard) (env : Environment) :
    OblRowTypedV (rootPT Ss) env ↔ CoreRowTypedV (rootPT Ss) env ∧ ∀ S ∈ Ss, ShardRowTypedV S (rootPT Ss) env :=
  forall_split Ss (fun c ls => RowTypedAtV (rootPT Ss) env c ls) (fun c ls h => rowTypedAtV_of_none _ env c ls h)

theorem rowTeleEv_split (Ss : List PTShard) (env : Environment) :
    (∀ c ls, RowTeleEvAt (rootPT Ss) env c ls) ↔ CoreRowTeleEv (rootPT Ss) env ∧ ∀ S ∈ Ss, ShardRowTeleEv S (rootPT Ss) env :=
  forall_split Ss (fun c ls => RowTeleEvAt (rootPT Ss) env c ls) (fun c ls h => rowTeleEvAt_of_none _ env c ls h)

/-- `LitRows` of the core is `LitRows` of every root table (the `Nat` / `String` rows are core rows). -/
theorem litRows_rootPT {Ss : List PTShard} {env : Environment} (h : LitRows PTcore env) : LitRows (rootPT Ss) env := by
  obtain ⟨rn, rs, hn, hnd, hnk, hnT, hs, hsd, hsk, hsT⟩ := h
  exact ⟨rn, rs, rootPT_keeps_core_tys hn, hnd, hnk, hnT, rootPT_keeps_core_tys hs, hsd, hsk, hsT⟩

theorem litRows_rootPT_of_env {Ss : List PTShard} {env : Environment} (hN : ¬ IsDefn env `Nat) (hS : ¬ IsDefn env `String) : LitRows (rootPT Ss) env :=
  litRows_rootPT (ptcorpus_litRows hN hS)

/-- The three table-dependent named premises of a root, split: literal rows, core rows, and one pair of row premises per shard. -/
structure RootNamed (Ss : List PTShard) (env : Environment) : Prop where
  lit : LitRows (rootPT Ss) env
  coreTyped : CoreRowTypedV (rootPT Ss) env
  coreTele : CoreRowTeleEv (rootPT Ss) env
  shards : ∀ S ∈ Ss, ShardPremises S (rootPT Ss) env

theorem rootNamed_iff (Ss : List PTShard) (env : Environment) :
    (LitRows (rootPT Ss) env ∧ OblRowTypedV (rootPT Ss) env ∧ ∀ c ls, RowTeleEvAt (rootPT Ss) env c ls) ↔ RootNamed Ss env := by
  rw [oblRowTypedV_split, rowTeleEv_split]
  constructor
  · rintro ⟨hl, ⟨hc1, hs1⟩, ⟨hc2, hs2⟩⟩
    exact ⟨hl, hc1, hc2, fun S hS => ⟨hs1 S hS, hs2 S hS⟩⟩
  · rintro ⟨hl, hc1, hc2, hs⟩
    exact ⟨hl, ⟨hc1, fun S hS => (hs S hS).1⟩, ⟨hc2, fun S hS => (hs S hS).2⟩⟩

/-- A root with no shard has no shard premise: the premises are those of the core. -/
theorem rootNamed_nil_iff (env : Environment) :
    RootNamed [] env ↔ LitRows PTcore env ∧ CoreRowTypedV PTcore env ∧ CoreRowTeleEv PTcore env :=
  ⟨fun h => ⟨h.lit, h.coreTyped, h.coreTele⟩, fun ⟨a, b, c⟩ => ⟨a, b, c, fun _ h => by cases h⟩⟩

end split

end Tools.ShippingGen5PTRootShard

#print axioms Tools.ShippingGen5PTRootShard.fgLedgerPremisesStmtRoot_of_CV
#print axioms Tools.ShippingGen5PTRootShard.fgLedgerPremisesStmtRoot_empty_iff
#print axioms Tools.ShippingGen5PTRootShard.rootNamed_iff
#print axioms Tools.ShippingGen5PTRootShard.litRows_rootPT_of_env
#print axioms Tools.ShippingGen5PTRootShard.rootPT_keeps_shard_tms
