import Tools.ShippingMemLeafRun
import Tools.ShippingKaryRun
-- UNBUILT (unit SRM2): the run names and exits are recorded in REPORT-SRM2.md.
-- No `sorry`, no `axiom`, no `native_decide`, no new RefLawsAOps/RefLawsATele field, no existing statement changed.

/-! # Memory-aware miss-then-hit tracking and the parent's closing over K callees (unit SRM2, ledger L8bd2)

The NM analogue of `Tools.ShippingKaryRun` (`kary_group`, `kary_loop`, `kary_closing`), over the cache clauses `CacheClosedNM` + `KeyTop` + `MemDet` of `Tools/ShippingMemLeafCache.lean` and the
one-step contract `StepNM` of `Tools/ShippingMemLeafRun.lean`.  A callee (`NCal`) is a machine whose calls are each a MEMORY entry (the origin's child is a built memory module) or a `StepNM`
callee; its first call by the parent is a cache MISS (`synthesizeChild_miss_nm`, which records the design facts), the second a HIT (`synthesizeChild_hit`).

PROVED here: `nm_group` (one callee, called twice: the same entry, the cache clauses, and for every call of the callee a kid fact: a built memory module or a cache entry, whose top is named like
a module of the callee's design), `nm_loop` (by induction on the callee list), `nm_closing` (the parent's `closeInstsGM` is the pure `closeInstsG` of `Y.flatMap (fun y => [y, y])`; `CacheCoh`
from `cacheCoh_of_nm`; the per-call kid fact UPGRADED to membership of the module itself; the SHARED-LEAF DESIGN CLAUSE for every pair of calls with the same name, memory kids and cached kids alike).
PREMISES (named): `CalleeNM` of every callee (data facts, `StepNM` of each non-memory call, `MachineDefines`, `MachineClosesAtA` of the callee), the pairwise distinct callee names, the call / growth
name separation `hnc`.  `RealChildA` / `JQC` are histories of past synthesis results, not semantic correctness in the current environment.
CLASS BOUNDARY: a parent whose call list is `cs.flatMap (fun e => [e.c, e.c])` (every callee called twice, origins without a memory child); a callee's calls are memory entries or `StepNM` callees.
An example does not make the class complete. -/

namespace Tools.ShippingNmGroup
open Tools.ShippingKaryRun
open Tools.ShippingTopShareRun Tools.ShippingTopShareNoParent
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
open Tools.ShippingMemLeafCache Tools.ShippingMemLeafRun
open Sparkle.Compiler.MachMemory (memModule memChild?)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- One callee of a parent: its declaration name, its machine data, the names its own call steps may add to the cache (`Gs`: the growth set of its calls' `StepNM`) and the module names that
occur inside its result's design (`names`, for the interface `ChildIfaceP`; used by the entry layer only). -/
structure NCal where
  c : Name
  d : MachineData
  Gs : List Name
  names : List String

/-- **The data and contracts of ONE callee** (the premises of `synthesizeChild_miss_nm` about the callee, bundled): data facts, every call a memory entry or a `StepNM` callee at every depth `≠ 0`
(with growth set `Gs`), origins agree with the placeholder names, no call is the callee itself, `c ∉ Gs`, `MachineDefines`, `MachineClosesAtA` of the callee. -/
structure CalleeNM (O : RefLawsAOps MkRefd mref cref) (mctx : Meta.Context) (cctx : Core.Context) (e : NCal) : Prop where
  ok : e.d.ok = true
  body : e.d.shape.body = quote e.d.dom
    (fun j => inputExpr e.d.shape.binders.length (e.d.bpos j))
    (fun j => inputExpr e.d.shape.binders.length (e.d.vpos j)) e.d.packed
  calls : ∃ nDecl : Nat, e.d.callsOk nDecl = true ∧ ∀ b ∈ e.d.shape.binders.drop nDecl, b.2 ≠ .domain
  slots : e.d.ss.length = e.d.shape.layout.slots.length
  ins : e.d.shape.insts ≠ []
  fne : e.d.shape.instFields ≠ []
  step : ∀ D', D' ≠ 0 → ∀ x ∈ e.d.shape.instTagged, (∃ md, x.2.child? = some md ∧ MemKid md) ∨
    (x.2.child? = none ∧ StepNM (mref := mref) (cref := cref) O mctx cctx D' x.1 e.Gs)
  agree : ∀ (k : Nat) (hk : k < e.d.shape.insts.length),
    memChild? (e.d.shape.insts[k]).1 = (e.d.shape.instOrigins.getD k .ord).child?
  cne : ∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e.c
  cG : e.c ∉ e.Gs
  entry : MachineDefines mctx mref cctx cref e.c e.d.shape
  closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx e.c e.d.shape

/-- a built memory module, found by its name among the memory-named modules of a cached design, IS the built one -/
theorem memMod_eq_kid {a : Sparkle.IR.AST.Module} {k : Res} (ha : MemMod a) (hk : MemKid k) (h : a.name = k.1.name) : a = k.1 := by
  obtain ⟨cb, aw, dw, rfl⟩ := ha
  obtain ⟨cb', aw', dw', rfl⟩ := hk
  have hn := h
  rw [Tools.ShippingMemOnlyNames.memModule_name, Tools.ShippingMemOnlyNames.memModule_name] at hn
  obtain ⟨e1, e2, e3⟩ := Tools.ShippingModuleName.ofMem_injective hn
  subst e1 e2 e3
  rfl

/-- **ONE callee, called twice: a cache MISS then a cache HIT** (`kary_group` over the NM clauses).  Kid fact for every call `k` of the callee: a built memory module of the origin, or the cache entry of the
call, with a module of the callee's design named like it. -/
theorem nm_group (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {e : NCal} (K : CalleeNM O mctx cctx e)
    {w w₁ w₂ : Void IO.RealWorld} {y y' : Res} (hw : JQC O D w)
    (hcl : CacheClosedNM (cv w)) (hk : KeyTop (cv w)) (hmd : MemDet (cv w)) (hm : (cv w).get? e.c = none)
    (h₁ : RunsTo (synthesizeChild e.c) mctx mref cctx cref w y w₁)
    (h₂ : RunsTo (synthesizeChild e.c) mctx mref cctx cref w₁ y' w₂) :
    y' = y ∧ JQC O D w₂ ∧ CacheClosedNM (cv w₂) ∧ KeyTop (cv w₂) ∧ MemDet (cv w₂) ∧ CacheExtends (cv w) (cv w₂) ∧
      (cv w₂).get? e.c = some y ∧
      (∀ k (hk : k < e.d.shape.insts.length),
        (∃ md, (e.d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧ ∃ a ∈ y.2.modules, a.name = md.1.name) ∨
        ((e.d.shape.instOrigins.getD k .ord).child? = none ∧ ∃ z, (cv w₂).get? (e.d.shape.insts[k]).1 = some z ∧
          ∃ a ∈ y.2.modules, a.name = z.1.name)) ∧
      (∀ c' r', (cv w₂).get? c' = some r' → (cv w).get? c' = some r' ∨ c' = e.c ∨
        c' ∈ e.d.shape.insts.map (·.1) ∨ c' ∈ e.Gs) := by
  obtain ⟨nDecl, hC, hdomB⟩ := K.calls
  obtain ⟨hj1, hcl1, hk1, hmd1, hext1, hget1, ⟨kids, d₀, hy, hd0, hlen, hkids⟩, hgrow1⟩ :=
    synthesizeChild_miss_nm O hA hD e.Gs K.cG e.d K.ok K.body hC K.slots hdomB K.ins K.fne
      (K.step (D + 1) (Nat.succ_ne_zero D)) K.cne K.entry K.closes hw hcl hk hmd hm h₁
  obtain ⟨hyy, hj2, hcv2⟩ := synthesizeChild_hit O hA hj1 hget1 h₂
  rw [hcv2]
  refine ⟨hyy, hj2, hcl1, hk1, hmd1, hext1, hget1, fun kk hkk => ?_, hgrow1⟩
  have hni : ∀ q ∈ kids, ∃ a ∈ y.2.modules, a.name = q.1.name := by
    intro q hq
    rw [hy]
    exact designWith_hasName q hq
  have hkl : kk < kids.length := by rw [hlen]; exact hkk
  have hgi : kids[kk]? = some kids[kk] := List.getElem?_eq_getElem hkl
  rcases hkids kk hkk with ⟨md, h1, h2, h3⟩ | ⟨h1, z, hz, hcz⟩
  · refine Or.inl ⟨md, h1, h3, hni md ?_⟩
    rw [hgi] at h2
    cases h2
    exact List.getElem_mem hkl
  · refine Or.inr ⟨h1, z, hcz, hni z ?_⟩
    rw [hgi] at hz
    cases hz
    exact List.getElem_mem hkl

/-- **The K groups, by induction on the callee list** (`kary_loop` over the NM clauses). -/
theorem nm_loop (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) {f : Name × InstOrigin → MetaM Res} :
    ∀ (cs : List NCal) (L : List (Name × InstOrigin)) (acc r : List Res) (w w' : Void IO.RealWorld),
      (∀ e ∈ cs, CalleeNM O mctx cctx e) → (cs.map (·.c)).Nodup →
      (∀ e ∈ cs, ∀ e' ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c) ∧ e'.c ∉ e.Gs) →
      L.map (·.1) = cs.flatMap (fun e => [e.c, e.c]) → (∀ x ∈ L, x.2.child? = none) →
      JQC O D w → CacheClosedNM (cv w) → KeyTop (cv w) → MemDet (cv w) → (∀ e ∈ cs, (cv w).get? e.c = none) →
      RunsTo (List.mapM.loop f L acc) mctx mref cctx cref w r w' →
      (∀ x : Name × InstOrigin, x.2.child? = none → f x = synthesizeChild x.1) →
      ∃ Y : List Res, Y.length = cs.length ∧ r = acc.reverse ++ Y.flatMap (fun y => [y, y]) ∧
        JQC O D w' ∧ CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheExtends (cv w) (cv w') ∧
        (∀ j (hj : j < cs.length), ∃ y, Y[j]? = some y ∧ (cv w').get? (cs[j]).c = some y) ∧
        (∀ j (hj : j < cs.length) (y : Res), Y[j]? = some y →
          ∀ k (hk : k < (cs[j]).d.shape.insts.length),
            (∃ md, ((cs[j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧ ∃ a ∈ y.2.modules, a.name = md.1.name) ∨
            (((cs[j]).d.shape.instOrigins.getD k .ord).child? = none ∧ ∃ z, (cv w').get? ((cs[j]).d.shape.insts[k]).1 = some z ∧
              ∃ a ∈ y.2.modules, a.name = z.1.name)) ∧
        (∀ c' r', (cv w').get? c' = some r' → (cv w).get? c' = some r' ∨ c' ∈ cs.map (·.c) ∨
          c' ∈ cs.flatMap (fun e => e.d.shape.insts.map (·.1) ++ e.Gs)) := by
  intro cs
  induction cs with
  | nil =>
    intro L acc r w w' hK hnd hnc hL hch hw hcl hk hmd habs h hf
    have hL0 : L = [] := by simpa using hL
    subst hL0
    obtain ⟨rfl, rfl⟩ := RunsTo.pure_world h
    refine ⟨[], rfl, by simp, hw, hcl, hk, hmd, fun _ _ h => h, ?_, ?_, ?_⟩
    · intro j hj; exact absurd hj (Nat.not_lt_zero _)
    · intro j hj; exact absurd hj (Nat.not_lt_zero _)
    · intro c' r' h; exact Or.inl h
  | cons e cs ih =>
    intro L acc r w w' hK hnd hnc hL hch hw hcl hk hmd habs h hf
    rcases L with _ | ⟨x1, _ | ⟨x2, L'⟩⟩
    · simp at hL
    · simp at hL
    · simp only [List.map_cons, List.flatMap_cons, List.cons_append, List.cons.injEq] at hL
      obtain ⟨e1, e2, hL'⟩ := hL
      have hx1 : x1.2.child? = none := hch x1 (List.mem_cons_self ..)
      have hx2 : x2.2.child? = none := hch x2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      obtain ⟨y, w1, hy, h⟩ := RunsTo.bind h
      obtain ⟨y', w2, hy', h⟩ := RunsTo.bind h
      rw [hf x1 hx1, e1] at hy
      rw [hf x2 hx2, e2] at hy'
      have hKe : CalleeNM O mctx cctx e := hK e (List.mem_cons_self ..)
      have hme : (cv w).get? e.c = none := habs e (List.mem_cons_self ..)
      obtain ⟨hyy, hj2, hcl2, hk2, hmd2, hext2, hget2, hkids2, hgrow2⟩ :=
        nm_group O hA hD hKe hw hcl hk hmd hme hy hy'
      have hyy' : y = y' := hyy.symm
      subst hyy'
      have hnd' : e.c ∉ cs.map (·.c) ∧ (cs.map (·.c)).Nodup := by
        simpa [List.nodup_cons] using hnd
      have habs' : ∀ e' ∈ cs, (cv w2).get? e'.c = none := by
        intro e' he'
        cases hq : (cv w2).get? e'.c with
        | none => rfl
        | some q =>
          rcases hgrow2 e'.c q hq with h0 | h0 | h0 | h0
          · rw [habs e' (List.mem_cons_of_mem _ he')] at h0; cases h0
          · exact absurd (h0 ▸ List.mem_map_of_mem (f := (·.c)) he') hnd'.1
          · obtain ⟨x, hx, hxc⟩ := List.mem_map.mp h0
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
            exact absurd hxc ((hnc e (List.mem_cons_self ..) e' (List.mem_cons_of_mem _ he')).1 i hi)
          · exact absurd h0 (hnc e (List.mem_cons_self ..) e' (List.mem_cons_of_mem _ he')).2
      obtain ⟨Y', hlen, hr, hj, hcl', hk', hmd', hext', hget', hkids', hgrow'⟩ :=
        ih L' (y :: y :: acc) r w2 w'
          (fun e' he' => hK e' (List.mem_cons_of_mem _ he')) hnd'.2
          (fun a ha b hb => hnc a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
          hL' (fun x hx => hch x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)))
          hj2 hcl2 hk2 hmd2 habs' h hf
      refine ⟨y :: Y', by simp [hlen], ?_, hj, hcl', hk', hmd', fun c r' h0 => hext' c r' (hext2 c r' h0), ?_, ?_, ?_⟩
      · rw [hr]; simp
      · intro j hj0
        rcases j with _ | j
        · exact ⟨y, rfl, hext' _ _ hget2⟩
        · exact hget' j (Nat.lt_of_succ_lt_succ hj0)
      · intro j hj0 y0 hy0
        rcases j with _ | j
        · have : y0 = y := (Option.some.inj hy0).symm
          subst this
          intro k hk0
          rcases hkids2 k hk0 with hm0 | ⟨hc0, z, hz, hm0⟩
          · exact Or.inl hm0
          · exact Or.inr ⟨hc0, z, hext' _ _ hz, hm0⟩
        · exact hkids' j (Nat.lt_of_succ_lt_succ hj0) y0 hy0
      · intro c' r' h0
        rcases hgrow' c' r' h0 with h1 | h1 | h1
        · rcases hgrow2 c' r' h1 with h2 | h2 | h2 | h2
          · exact Or.inl h2
          · exact Or.inr (Or.inl (by simp [h2]))
          · exact Or.inr (Or.inr (by simp [List.mem_append, h2]))
          · exact Or.inr (Or.inr (by simp [List.mem_append, h2]))
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h1))
        · exact Or.inr (Or.inr (by simp only [List.flatMap_cons, List.mem_append]; exact Or.inr h1))

/-- `insts` names of a K-grouped call list: call `k` is a call of the callee `k / 2`. -/
theorem nm_insts_names {shape : MachineShape} {cs : List NCal}
    (hP : shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c])) :
    ∀ k (hk : k < shape.insts.length), (cs[k / 2]?).map (·.c) = some (shape.insts[k]).1 := by
  intro k hk
  have h1 := dup_getElem? (fun e : NCal => e.c) cs k
  rw [← h1, ← hP, Tools.ShippingInstTagged.instTagged_map_fst]
  simp [List.getElem?_eq_getElem hk]

theorem nm_insts_length {shape : MachineShape} {cs : List NCal}
    (hP : shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c])) :
    shape.insts.length = 2 * cs.length := by
  have h := congrArg List.length hP
  simp only [List.length_map, Tools.ShippingInstTagged.instTagged_length] at h
  rw [h]
  exact dup_length' (fun e : NCal => e.c) cs

/-- **The parent's `closeInstsGM` over K groups of memory-aware callees** (`kary_closing` over the NM clauses).  The end cache is `CacheClosedNM`/`KeyTop`/`MemDet`, hence `CacheCoh`.  For every
call of a callee the kid fact UPGRADED: a built memory module of the origin that IS a module of the callee's design, or the cache entry of the call whose top IS a module of the callee's design.  The
SHARED-LEAF DESIGN CLAUSE: any two calls (of any two callees) with the same name have a common module (the entry's top, or the memory module) inside BOTH designs. -/
theorem nm_closing (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    {D : Nat} (hD : D ≠ 0) (cs : List NCal) {shape : MachineShape}
    (hK : ∀ e ∈ cs, CalleeNM O mctx cctx e) (hnd : (cs.map (·.c)).Nodup)
    (hnc : ∀ e ∈ cs, ∀ e' ∈ cs, (∀ k (hk : k < e.d.shape.insts.length), (e.d.shape.insts[k]).1 ≠ e'.c) ∧ e'.c ∉ e.Gs)
    (hP : shape.instTagged.map (·.1) = cs.flatMap (fun e => [e.c, e.c]))
    (hch : ∀ x ∈ shape.instTagged, x.2.child? = none)
    {t m₀ : Sparkle.IR.AST.Module} {d₀ : Sparkle.IR.AST.Design}
    {r : Option (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)} {w w' : Void IO.RealWorld}
    (hw : JQC O D w) (hcl : CacheClosedNM (cv w)) (hk : KeyTop (cv w)) (hmd : MemDet (cv w))
    (habs : ∀ e ∈ cs, (cv w).get? e.c = none)
    (hr : RunsTo (closeInstsGM shape t m₀ d₀) mctx mref cctx cref w r w') :
    ∃ Y : List Res, Y.length = cs.length ∧
      r = Sparkle.IR.Machine.closeInstsG (machNIn shape) shape.insts.length
        shape.layout.slots.length (t.inputs.map (·.name)) (shape.insts.map (·.2.1))
        shape.instFields (Y.flatMap fun y => [y, y]) (m₀, d₀) ∧
      JQC O D w' ∧ CacheClosedNM (cv w') ∧ KeyTop (cv w') ∧ MemDet (cv w') ∧ CacheCoh (cv w') ∧
      (∀ j (hj : j < cs.length), ∃ y, Y[j]? = some y ∧ (cv w').get? (cs[j]).c = some y) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ a ∈ ModsOf y, ∀ b ∈ ModsOf y', a.name = b.name → a = b) ∧
      (∀ j (hj : j < cs.length) (y : Res), Y[j]? = some y →
        ∀ k (hk : k < (cs[j]).d.shape.insts.length),
          (∃ md, ((cs[j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
            memChild? ((cs[j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
          (((cs[j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? ((cs[j]).d.shape.insts[k]).1 = none ∧
            ∃ z, (cv w').get? ((cs[j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules)) ∧
      (∀ i (hi : i < cs.length) j (hj : j < cs.length) (y y' : Res), Y[i]? = some y → Y[j]? = some y' →
        ∀ k₁ (hk₁ : k₁ < (cs[i]).d.shape.insts.length) k₂ (hk₂ : k₂ < (cs[j]).d.shape.insts.length),
          ((cs[i]).d.shape.insts[k₁]).1 = ((cs[j]).d.shape.insts[k₂]).1 →
          ∃ z, z ∈ y.2.modules ∧ z ∈ y'.2.modules ∧
            ((∃ e, (cv w').get? (((cs[i]).d.shape.insts[k₁]).1) = some e ∧ z = e.1) ∨
             (∃ md, MemKid md ∧ memChild? (((cs[i]).d.shape.insts[k₁]).1) = some md ∧ z = md.1))) ∧
      (∀ c' r', (cv w').get? c' = some r' → (cv w).get? c' = some r' ∨ c' ∈ cs.map (·.c) ∨
        c' ∈ cs.flatMap (fun e => e.d.shape.insts.map (·.1) ++ e.Gs)) := by
  unfold closeInstsGM at hr
  obtain ⟨synth?, wa, hget, hr⟩ := RunsTo.bind hr
  obtain ⟨hwa, rfl⟩ := triple_runs (tripleC_synthRead O hA D) hw hget
  have hcva : cv wa = cv w := by
    have hk0 := O.frame hA _ FramedA.synthGet w hw.1.1
    rw [endW_of_runs hget] at hk0
    exact hk0.1
  dsimp only at hr
  obtain ⟨children, wb, hch', hr⟩ := RunsTo.bind hr
  obtain ⟨heq, rfl⟩ := RunsTo.pure_world hr
  have hcl' : CacheClosedNM (cv wa) := by rw [hcva]; exact hcl
  have hk' : KeyTop (cv wa) := by rw [hcva]; exact hk
  have hmd' : MemDet (cv wa) := by rw [hcva]; exact hmd
  have habs' : ∀ e ∈ cs, (cv wa).get? e.c = none := by
    intro e he; rw [hcva]; exact habs e he
  obtain ⟨Y, hlen, hrr, hj, hcl2, hk2, hmd2, hext, hget', hkids, hgrow⟩ :=
    nm_loop O hA hD cs shape.instTagged [] children wa w' hK hnd hnc hP hch hwa hcl' hk' hmd' habs' hch'
      (fun ⟨c, o⟩ hx => by
        simp only [] at hx ⊢
        simp [hx])
  have hcoh : CacheCoh (cv w') := cacheCoh_of_nm hcl2 hk2 hmd2
  have hchildren : children = Y.flatMap (fun y => [y, y]) := by rw [hrr]; simp
  -- the upgraded per-call kid fact
  have hup : ∀ j (hj : j < cs.length) (y : Res), Y[j]? = some y →
      ∀ k (hk : k < (cs[j]).d.shape.insts.length),
        (∃ md, ((cs[j]).d.shape.instOrigins.getD k .ord).child? = some md ∧ MemKid md ∧
          memChild? ((cs[j]).d.shape.insts[k]).1 = some md ∧ md.1 ∈ y.2.modules) ∨
        (((cs[j]).d.shape.instOrigins.getD k .ord).child? = none ∧ memChild? ((cs[j]).d.shape.insts[k]).1 = none ∧
          ∃ z, (cv w').get? ((cs[j]).d.shape.insts[k]).1 = some z ∧ z.1 ∈ y.2.modules) := by
    intro j hj0 y hy k hkk
    obtain ⟨y1, hy1, hg1⟩ := hget' j hj0
    rw [hy] at hy1
    cases hy1
    have hag := (hK _ (List.getElem_mem hj0)).agree k hkk
    rcases hkids j hj0 y hy k hkk with ⟨md, h1, h2, a, ha, han⟩ | ⟨h1, z, hz, a, ha, han⟩
    · have hamem : a ∈ ModsOf y := List.mem_cons_of_mem _ ha
      have hma : MemNamed a.name := by
        rw [han]
        obtain ⟨cb, aw, dw, rfl⟩ := h2
        exact memModule_memNamed cb aw dw
      have hmm : MemMod a := hmd2 _ _ hg1 a hamem hma
      have := memMod_eq_kid hmm h2 han
      refine Or.inl ⟨md, h1, h2, by rw [h1] at hag; exact hag, ?_⟩
      rw [← this]; exact ha
    · refine Or.inr ⟨h1, by rw [h1] at hag; exact hag, z, hz, ?_⟩
      have hamem : a ∈ ModsOf y := List.mem_cons_of_mem _ ha
      have := hcoh _ _ _ z hg1 hz a hamem z.1 (List.mem_cons_self ..) han
      rw [← this]; exact ha
  refine ⟨Y, hlen, by rw [hchildren] at heq; first | exact heq | exact heq.symm, hj, hcl2, hk2, hmd2, hcoh, hget', ?_, hup, ?_, ?_⟩
  · intro i hi j hj0 y y' hy hy' a ha b hb hab
    obtain ⟨y1, hy1, hg1⟩ := hget' i hi
    obtain ⟨y2, hy2, hg2⟩ := hget' j hj0
    rw [hy] at hy1; rw [hy'] at hy2
    cases hy1; cases hy2
    exact hcoh _ _ _ _ hg1 hg2 a ha b hb hab
  · intro i hi j hj0 y y' hy hy' k₁ hk₁ k₂ hk₂ hn
    rcases hup i hi y hy k₁ hk₁ with ⟨md₁, hc₁, hm₁, hmn₁, hmem₁⟩ | ⟨hc₁, hmn₁, e₁, he₁, hmem₁⟩
    · rcases hup j hj0 y' hy' k₂ hk₂ with ⟨md₂, hc₂, hm₂, hmn₂, hmem₂⟩ | ⟨hc₂, hmn₂, e₂, he₂, hmem₂⟩
      · rw [hn] at hmn₁
        have hmd12 : md₁ = md₂ := Option.some.inj (hmn₁.symm.trans hmn₂)
        subst hmd12
        exact ⟨md₁.1, hmem₁, hmem₂, Or.inr ⟨md₁, hm₁, by rw [hn]; exact hmn₂, rfl⟩⟩
      · rw [hn] at hmn₁
        rw [hmn₁] at hmn₂
        cases hmn₂
    · rcases hup j hj0 y' hy' k₂ hk₂ with ⟨md₂, hc₂, hm₂, hmn₂, hmem₂⟩ | ⟨hc₂, hmn₂, e₂, he₂, hmem₂⟩
      · rw [hn] at hmn₁
        rw [hmn₁] at hmn₂
        cases hmn₂
      · rw [← hn] at he₂
        have hee : e₂ = e₁ := Option.some.inj (he₂.symm.trans he₁)
        subst hee
        exact ⟨e₂.1, hmem₁, hmem₂, Or.inl ⟨e₂, he₁, rfl⟩⟩
  · intro c' r' h0
    rcases hgrow c' r' h0 with h1 | h1
    · left; rw [← hcva]; exact h1
    · exact Or.inr h1

end Tools.ShippingNmGroup

#print axioms Tools.ShippingNmGroup.nm_group
#print axioms Tools.ShippingNmGroup.nm_loop
#print axioms Tools.ShippingNmGroup.nm_closing
