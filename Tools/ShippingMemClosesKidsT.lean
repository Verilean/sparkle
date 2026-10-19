import Tools.ShippingMemClosesKids

variable {tenv : Lean.Environment}

/-! # The memory-parent closing over the ORIGIN-based kid (`KidT`): no `TagsAgree` (round par/o-kidt)

`Tools.ShippingMemCloses.machineClosesAt_of_kidsDM` (M2) proves
`MachineClosesAt` of a parent tied by the general closing whose call entries
are memory placeholders and/or real children. Since the origin-tag compiler
change it asks `hagree : TagsAgree d.shape` (every entry's NAME decodes to
what its ORIGIN builds) because its children are name-based `Kid`s and its
name separation (`hsep`, `hfieldsNd`, `hdisjD`) identifies two entries by
their callee NAME. Both are false for a collision shape: a memory entry next
to a call of a declaration that carries the memory's placeholder name
(`Tests/Compiler/MemNameCollisionTest.lean`). The patched compiler compiles
such a parent correctly (two entries, two instances: the memory module and the
declaration's own module); M2 does not cover it.

This file is M2 with

* the children taken as the closing takes them, by the entry's ORIGIN
  (`Tools.ShippingInstTagged.KidT mref cref (originAt d.shape k) (insts[k]).1`:
  the built memory module for a memory origin, a real child of the entry's
  declaration otherwise — whatever its name), straight from the BUILT
  tag-based M1 `closeInstsGM_run_allM`;
* two entries identified as ONE CALL when their callee names AND their memory
  keys agree (`memKey`: the memory parameters of a memory origin, `none`
  otherwise — decidable, and equal exactly when the origins build the same
  child: `child?_eq_of_memKey`, `memKey_of_child?`). That is the pairing M1
  states (`… → (originAt shape i).child? = (originAt shape j).child? → children[i]? = children[j]?`).

Contents:

* `memKey`, `child?_eq_of_memKey`, `memKey_of_child?`;
* `memKidT_iface` — the kid of a memory origin is the built memory module and
  has the interface (`memIface`, BUILT);
* `closeInstsG_of_kidsPT` — `closeInstsG_of_kidsP` (BUILT) with `hpair`,
  `hcross`, `hfieldsNd`, `hsep` over "same name AND same memory key" in place
  of "same name" (the proof is the built one; the four places that used the
  name equality use the pair);
* `machineClosesAt_of_kidsDMT` — M2 over `KidT`, NO `hagree`, no memory
  premise, from the BUILT `closeInstsGM_run_allM`;
* `machineClosesAt_of_kidsDM_fromT` — the statement of the old M2 (name-based
  `Kid`, name separation, `hagree`) re-derived from the new one: under
  `TagsAgree` two entries of one name have one memory key
  (`Tools.ShippingInstTagged.agree_at`, `memKey_of_child?`) and a `KidT` is a
  `Kid` (`kid_of_kidT`). The old theorem and its file are UNCHANGED (still what
  `#machine_no_ports_memseq` uses); this shows the new statement generalises it.

Since round par/o-kidt2: the run-fact chain (`kidsM_*`, `core_*M`) has `…T` forms over `KidT` (no
`hagree`), and `#machine_no_ports_memseq` has a TAG MODE (tables keyed by `keyAt` below) that generates
collision parents. Still name-based: `GenKidM`, `MemOnly*`, `#machine_no_ports_mem`,
`#machine_no_ports_memkid`. `child?_none_of_memKey`, `child?_of_memKey`, `keyAt`, `keyAt_eq`: BUILT (gt5).

BUILT (par/o-kidt; run kt1 failed: `MachineClosesAt`'s implicit `tenv` binder needed `intro tenv` before `refine` (integrator fix); kt2 exit 0; axioms [propext, Classical.choice, Quot.sound]). -/
namespace Tools.ShippingMemCloses
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
open Tools.ShippingMemKid (Kid calleeAt calleeAt_eq mem_inPorts mem_outsIn mem_design mem_noInst)
open Sparkle.Compiler.MachMemory (memModule memChild? memParams? isMemModule memSelf portKey)
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingInstTagged (KidT originAt)

/-! ## The memory key of an origin -/

/-- The memory parameters of a memory origin, `none` for any other origin
(decidable, unlike the equality of the built children). -/
def memKey : InstOrigin → Option (Bool × Nat × Nat)
  | .mem cb aw dw => some (cb, aw, dw)
  | .ord => none
  | .field _ => none

/-- Origins of one memory key build the same child. -/
theorem child?_eq_of_memKey {o o' : InstOrigin} (h : memKey o = memKey o') :
    o.child? = o'.child? := by
  cases o with
  | ord =>
    cases o' with
    | ord => rfl
    | field _ => rfl
    | mem cb aw dw => exact absurd h (by simp [memKey])
  | field i =>
    cases o' with
    | ord => rfl
    | field _ => rfl
    | mem cb aw dw => exact absurd h (by simp [memKey])
  | mem cb aw dw =>
    cases o' with
    | ord => exact absurd h (by simp [memKey])
    | field _ => exact absurd h (by simp [memKey])
    | mem cb' aw' dw' =>
      have h' : some (cb, aw, dw) = some (cb', aw', dw') := h
      have e : (cb, aw, dw) = (cb', aw', dw') := Option.some.inj h'
      cases e
      rfl

/-- Origins that build the same child have one memory key (the built memory
module records its parameters: `memParams_memModule'`). -/
theorem memKey_of_child? {o o' : InstOrigin} (h : o.child? = o'.child?) :
    memKey o = memKey o' := by
  cases o with
  | ord =>
    cases o' with
    | ord => rfl
    | field _ => rfl
    | mem cb aw dw =>
      exact absurd h (by simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?])
  | field i =>
    cases o' with
    | ord => rfl
    | field _ => rfl
    | mem cb aw dw =>
      exact absurd h (by simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?])
  | mem cb aw dw =>
    cases o' with
    | ord => exact absurd h (by simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?])
    | field _ => exact absurd h (by simp [Sparkle.Compiler.MachInstOrigin.InstOrigin.child?])
    | mem cb' aw' dw' =>
      have h' : some (memModule cb aw dw) = some (memModule cb' aw' dw') := h
      have e : memModule cb aw dw = memModule cb' aw' dw' := Option.some.inj h'
      have e2 : memParams? (memModule cb aw dw).1 = memParams? (memModule cb' aw' dw').1 := by
        rw [e]
      rw [Tools.ShippingMachineShipsHier.memParams_memModule',
        Tools.ShippingMachineShipsHier.memParams_memModule'] at e2
      exact e2

/-- An origin without a memory key builds no child. -/
theorem child?_none_of_memKey {o : InstOrigin} (h : memKey o = none) : o.child? = none := by
  cases o with
  | ord => rfl
  | field _ => rfl
  | mem cb aw dw => exact absurd h (by simp [memKey])

/-- An origin of memory key `(cb, aw, dw)` builds that memory module. -/
theorem child?_of_memKey {o : InstOrigin} {cb : Bool} {aw dw : Nat}
    (h : memKey o = some (cb, aw, dw)) : o.child? = some (memModule cb aw dw) := by
  cases o with
  | ord => exact absurd h (by simp [memKey])
  | field _ => exact absurd h (by simp [memKey])
  | mem cb' aw' dw' =>
    have h' : some (cb', aw', dw') = some (cb, aw, dw) := h
    have e : (cb', aw', dw') = (cb, aw, dw) := Option.some.inj h'
    cases e
    first | rfl | exact Tools.ShippingInstTagged.child?_mem _ _ _

/-- **The table key of call entry `k`** (the generators' tag mode): its callee and the memory key
of its ORIGIN — two entries of one name are told apart by it (a collision). -/
def keyAt (d : MachineData) (k : Nat) : Name × Option (Bool × Nat × Nat) :=
  (calleeAt d k, memKey (originAt d.shape k))

theorem keyAt_eq (d : MachineData) {k : Nat} (hk : k < d.shape.insts.length) :
    keyAt d k = ((d.shape.insts[k]).1, memKey (originAt d.shape k)) := by
  unfold keyAt
  rw [calleeAt_eq d hk]

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A kid of a memory ORIGIN has the interface** (whatever the entry's name). -/
theorem memKidT_iface {o : InstOrigin} {c : Name} {cb : Bool} {aw dw : Nat}
    (ho : o.child? = some (memModule cb aw dw)) {y : Res} (hy : KidT mref cref o c y) :
    ChildIfaceP (memModule cb aw dw).1.name 4 ["out"] [(memModule cb aw dw).1.name] y.1 y.2 := by
  have e := Tools.ShippingInstTagged.KidT.mem hy ho
  subst e
  exact memIface cb aw dw

/-! ## The pure closing, entries identified by name AND memory key -/

set_option maxHeartbeats 1000000 in
/-- **`closeInstsG_of_kidsP` with entries identified by (name, memory key)**:
two entries of one name and one memory key have one child (`hpair`); the
children of two entries that differ in name OR memory key agree on every
module name they both have (`hcross`); `hsep` / `hfieldsNd` over the pair. -/
theorem closeInstsG_of_kidsPT {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    {logProf : String → IO Unit} {t t' : Sparkle.IR.AST.Module} {d₀ : Design}
    {children : List Res}
    (run : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire tenv e hint top named) logProf declName
      d.shape.binders d.shape.body) (t, d₀))
    (hcl : closeLets d.shape.layout.lets t = some t')
    (hlenC : children.length = d.shape.insts.length)
    (nameK : Nat → String) (nk : Nat → Nat) (outsK : Nat → List String)
    (namesK : Nat → List String)
    (hfull : ∀ (k : Nat) (c : Res), children[k]? = some c →
      ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) c.1 c.2)
    (hpair : ∀ (i j : Nat) (hi : i < d.shape.insts.length) (hj : j < d.shape.insts.length),
      (d.shape.insts[i]).1 = (d.shape.insts[j]).1 →
      memKey (originAt d.shape i) = memKey (originAt d.shape j) → children[i]? = children[j]?)
    (hcross : ∀ (i j : Nat) (hi : i < d.shape.insts.length) (hj : j < d.shape.insts.length)
      (ci cj : Res), children[i]? = some ci → children[j]? = some cj →
      ¬ ((d.shape.insts[i]).1 = (d.shape.insts[j]).1 ∧
        memKey (originAt d.shape i) = memKey (originAt d.shape j)) →
      ∀ a ∈ ci.1 :: ci.2.modules, ∀ b ∈ cj.1 :: cj.2.modules, a.name = b.name → a = b)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ outsK k)
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      memKey (originAt d.shape k) = memKey (originAt d.shape k') →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), nameK k = nameK k' →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        memKey (originAt d.shape k) = memKey (originAt d.shape k'))
    (hparent : ∀ (k : Nat), k < d.shape.insts.length → nameK k ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (gi : Nat) (k : Nat), k < d.shape.insts.length → ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{nameK k}")
    (hparentD : ∀ (k : Nat), k < d.shape.insts.length → (Sparkle.IR.ModuleName.ofDecl declName) ∉ namesK k) :
    (closeInstsG (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) d.shape.instFields children
      (closeMachine d.shape.layout t', d₀)).isSome = true := by
  have hlt : ∀ (k : Nat) (c : Res), children[k]? = some c → k < d.shape.insts.length := by
    intro k c hc
    rw [← hlenC]
    exact (List.getElem?_eq_some_iff.mp hc).1
  have hcons : ∀ a ∈ children, ∀ c ∈ children, a.1.name = c.1.name → a.1 = c.1 := by
    intro a ha c hc' hn
    obtain ⟨i, hi, hai⟩ := List.getElem_of_mem ha
    obtain ⟨j, hj, hcj⟩ := List.getElem_of_mem hc'
    have hia : children[i]? = some a := by rw [List.getElem?_eq_getElem hi, hai]
    have hjc : children[j]? = some c := by rw [List.getElem?_eq_getElem hj, hcj]
    have fi := hfull i a hia
    have fj := hfull j c hjc
    have hki := hlt i a hia
    have hkj := hlt j c hjc
    rw [fi.name, fj.name] at hn
    obtain ⟨hs1, hs2⟩ := hsep i hki j hkj hn
    have hsame := hpair i j hki hkj hs1 hs2
    rw [hia, hjc] at hsame
    exact congrArg Prod.fst (Option.some.inj hsame)
  -- a visited module: its entry, and where it sits
  have hvis : ∀ g ∈ visited children, ∃ (k : Nat) (c : Res), k < d.shape.insts.length ∧
      children[k]? = some c ∧
      ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) c.1 c.2 ∧
      (g = c.1 ∨ g ∈ c.2.modules) := by
    intro g hg
    obtain ⟨c, hc, hor⟩ := mem_visited.mp hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
    exact ⟨k, c, hlt k c hk, hk, hfull k c hk, hor⟩
  have hconsV : ∀ a ∈ visited children, ∀ b ∈ visited children, a.name = b.name → a = b := by
    intro a ha b hb hn
    obtain ⟨i, ci, hki, hci, fi, hai⟩ := hvis a ha
    obtain ⟨j, cj, hkj, hcj, fj, hbj⟩ := hvis b hb
    by_cases hdecl : (d.shape.insts[i]).1 = (d.shape.insts[j]).1 ∧
        memKey (originAt d.shape i) = memKey (originAt d.shape j)
    · -- one call: one child (module and design)
      have hsame := hpair i j hki hkj hdecl.1 hdecl.2
      rw [hci, hcj] at hsame
      have hcc : ci = cj := Option.some.inj hsame
      have hbi : b = ci.1 ∨ b ∈ ci.2.modules := by
        rw [hcc]
        exact hbj
      rcases hai with hae | hai
      · rcases hbi with hbe | hbi
        · rw [hae, hbe]
        · rw [hae]
          exact (fi.self b hbi (by rw [← hn, hae])).symm
      · rcases hbi with hbe | hbi
        · rw [hbe]
          exact fi.self a hai (by rw [hn, hbe])
        · exact module_of_name _ fi.desNd a hai b hbi hn
    · -- different calls
      exact hcross i j hki hkj ci cj hci hcj hdecl a (mem_cons_of_or hai) b
        (mem_cons_of_or hbj) hn
  have hlenM : children.length = (d.shape.insts.map (·.2.1)).length := by simp [hlenC]
  refine closeInstsG_of_run d ok hbody hC hslots hdomB run hcl hlenC ?_ hcons ?_ ?_ ?_
  · intro k c hc
    have hk := hlt k c hc
    have full := hfull k c hc
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
      exact hparent k hk
  · intro k k' key hkk hkk' hf
    obtain ⟨args, c, ha, hc, rfl⟩ := keys_get hlenM hkk
    obtain ⟨args', c', ha', hc', he⟩ := keys_get hlenM hkk'
    simp only [Prod.mk.injEq] at he
    have hk := hlt k c hc
    have hk' := hlt k' c' hc'
    have full := hfull k c hc
    have full' := hfull k' c' hc'
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
    have hn : nameK k = nameK k' := (full.name.symm.trans he.1).trans full'.name
    obtain ⟨hs1, hs2⟩ := hsep k hk k' hk' hn
    exact hfieldsNd k hk k' hk' hs1 hs2
      (by rw [e1, e2, hxa, hxa']; exact he.2) hf
  · intro gi c hc o ho
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
    rw [(hfull k c hk).name]
    exact hfresh gi k (hlt k c hk) o ho
  · intro hd0
    refine design_checksM hd0 hconsV ?_ ?_
    · intro c hc
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hc
      exact (hfull k c hk).memOk
    · intro g hg
      obtain ⟨k, c, hk, _, full, hor⟩ := hvis g hg
      refine noInstOfB_of_names (fun mn i conns hm e => ?_)
      exact hparentD k hk (e ▸ full.closed g (mem_cons_of_or hor) mn i conns hm)

/-! ## The closing over `KidT` -/

set_option maxHeartbeats 1000000 in
/-- **(M2, origin-based) `MachineClosesAt` for the general closing over the
kids of the entries' ORIGINS** — a memory origin's built module, a real child
of the entry's declaration otherwise, whatever the declaration's name. Two
entries are one call when their names AND memory keys agree (the pairing of
the BUILT M1 `closeInstsGM_run_allM`). NO `TagsAgree`, no memory premise: a
collision shape (a memory entry beside a call of a declaration named as its
placeholder) is covered. -/
theorem machineClosesAt_of_kidsDMT {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (nameK : Nat → String) (nk : Nat → Nat) (outsK : Nat → List String)
    (namesK : Nat → List String)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      KidT mref cref (originAt d.shape k) (d.shape.insts[k]).1 y →
      ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ outsK k)
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      memKey (originAt d.shape k) = memKey (originAt d.shape k') →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), nameK k = nameK k' →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        memKey (originAt d.shape k) = memKey (originAt d.shape k'))
    (hparent : ∀ (k : Nat), k < d.shape.insts.length → nameK k ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (gi : Nat) (k : Nat), k < d.shape.insts.length → ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{nameK k}")
    (hparentD : ∀ (k : Nat), k < d.shape.insts.length → (Sparkle.IR.ModuleName.ofDecl declName) ∉ namesK k)
    (hdisjD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length),
      ¬ ((d.shape.insts[k]).1 = (d.shape.insts[k']).1 ∧
        memKey (originAt d.shape k) = memKey (originAt d.shape k')) →
      nameK k ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k') :
    MachineClosesAt mctx mref cctx cref declName d.shape := by
  have hl : Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape :=
    letsClose_of_data d ok hbody halias mctx mref cctx cref
  intro tenv b w r w' hw' hdp hr
  obtain ⟨L, hw⟩ := invV_of_invW mctx cctx hw'
  have hB : ∀ L' : RefLaws mref cref, Tools.ShippingChildInv.BodyRel L' := fun L' => bodyRel L'
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
  obtain ⟨children, rfl, hreal, hpair, -⟩ := closeInstsGM_run_allM L hB hw1 hd1 hr
  have key : (closeInstsG (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      (t.inputs.map (·.name)) (d.shape.insts.map (·.2.1)) d.shape.instFields children
      (closeMachine d.shape.layout t', d₀)).isSome = true := by
    obtain ⟨hlenC, hall⟩ := hreal
    have hfull : ∀ (k : Nat) (c : Res), children[k]? = some c →
        ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) c.1 c.2 := by
      intro k c hc
      have hk : k < d.shape.insts.length := by
        rw [← hlenC]
        exact (List.getElem?_eq_some_iff.mp hc).1
      obtain ⟨y, hy, hre⟩ := hall k hk
      rw [hc] at hy
      cases hy
      exact hkid k hk c hre
    -- two entries of one name and one memory key are one child (module and design)
    have hsameCall : ∀ (i j : Nat) (hi : i < d.shape.insts.length)
        (hj : j < d.shape.insts.length), (d.shape.insts[i]).1 = (d.shape.insts[j]).1 →
        memKey (originAt d.shape i) = memKey (originAt d.shape j) →
        children[i]? = children[j]? := by
      intro i j hki hkj hcc hkey
      have ho : (originAt d.shape i).child? = (originAt d.shape j).child? :=
        child?_eq_of_memKey hkey
      have hni : (d.shape.insts.map (·.1))[i]? = some (d.shape.insts[i]).1 := by simp [hki]
      have hnj : (d.shape.insts.map (·.1))[j]? = some (d.shape.insts[j]).1 := by simp [hkj]
      rw [← hcc] at hnj
      rcases Nat.lt_trichotomy i j with h | h | h
      · exact hpair i j _ h hni hnj ho
      · rw [h]
      · exact (hpair j i _ h hnj hni ho.symm).symm
    refine closeInstsG_of_kidsPT d ok hbody hC hslots hdomB run.mreturns hcl hlenC nameK nk outsK
      namesK hfull hsameCall ?_ hargsN hfieldOut hfieldsNd hsep hparent hfresh hparentD
    -- two entries of DIFFERENT calls: no module name in common
    intro i j hki hkj ci cj hci hcj hdecl a ha b' hb hn
    exfalso
    have fi := hfull i ci hci
    have fj := hfull j cj hcj
    obtain ⟨hx1, hx2⟩ := hdisjD i hki j hkj hdecl
    obtain ⟨hx3, -⟩ := hdisjD j hkj i hki (fun e => hdecl ⟨e.1.symm, e.2.symm⟩)
    have han : a.name = nameK i ∨ a.name ∈ namesK i := by
      rcases List.mem_cons.mp ha with hae | hai
      · exact Or.inl (by rw [hae]; exact fi.name)
      · exact Or.inr (fi.desNames a hai)
    have hbn : b'.name = nameK j ∨ b'.name ∈ namesK j := by
      rcases List.mem_cons.mp hb with hbe | hbj
      · exact Or.inl (by rw [hbe]; exact fj.name)
      · exact Or.inr (fj.desNames b' hbj)
    rcases han with han | han
    · rcases hbn with hbn | hbn
      · exact hdecl (hsep i hki j hkj (by rw [← han, ← hbn, hn]))
      · exact hx1 (by rw [← han, hn]; exact hbn)
    · rcases hbn with hbn | hbn
      · exact hx3 (by rw [← hbn, ← hn]; exact han)
      · exact hx2 _ han (by rw [hn]; exact hbn)
  intro h0
  rw [h0] at key
  cases key

set_option maxHeartbeats 1000000 in
/-- **The statement of the old M2 (`machineClosesAt_of_kidsDM`: name-based
`Kid`, name separation, `hagree`), from the origin-based one**: under
`TagsAgree` two entries of one name build the same child, hence have one
memory key, and a `KidT` of an entry is a `Kid` of its name. The old theorem
is unchanged; this shows the new statement generalises it. -/
theorem machineClosesAt_of_kidsDM_fromT {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (nameK : Nat → String) (nk : Nat → Nat) (outsK : Nat → List String)
    (namesK : Nat → List String)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y →
      ChildIfaceP (nameK k) (nk k) (outsK k) (namesK k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ outsK k)
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (hsep : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), nameK k = nameK k' →
      (d.shape.insts[k]).1 = (d.shape.insts[k']).1)
    (hparent : ∀ (k : Nat), k < d.shape.insts.length → nameK k ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (gi : Nat) (k : Nat), k < d.shape.insts.length → ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{nameK k}")
    (hparentD : ∀ (k : Nat), k < d.shape.insts.length → (Sparkle.IR.ModuleName.ofDecl declName) ∉ namesK k)
    (hdisjD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 ≠ (d.shape.insts[k']).1 →
      nameK k ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k')
    (hagree : Tools.ShippingInstTagged.TagsAgree d.shape) :
    MachineClosesAt mctx mref cctx cref declName d.shape := by
  -- under `TagsAgree`, one name gives one memory key
  have hkeyOf : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      memKey (originAt d.shape k) = memKey (originAt d.shape k') := by
    intro k hk k' hk' he
    apply memKey_of_child?
    show (d.shape.instOrigins.getD k .ord).child? = (d.shape.instOrigins.getD k' .ord).child?
    rw [← Tools.ShippingInstTagged.agree_at hagree hk, ← Tools.ShippingInstTagged.agree_at hagree hk',
      he]
  intro tenv
  refine machineClosesAt_of_kidsDMT d ok hbody halias hC hslots hdomB hfne nameK nk outsK namesK
    ?_ hargsN hfieldOut ?_ ?_ hparent hfresh hparentD ?_
  · intro k hk y hy
    exact hkid k hk y
      (Tools.ShippingInstTagged.kid_of_kidT hy (Tools.ShippingInstTagged.agree_at hagree hk))
  · intro k hk k' hk' hn _ ha hf
    exact hfieldsNd k hk k' hk' hn ha hf
  · intro k hk k' hk' hn
    have he := hsep k hk k' hk' hn
    exact ⟨he, hkeyOf k hk k' hk' he⟩
  · intro k hk k' hk' hne
    exact hdisjD k hk k' hk' (fun he => hne ⟨he, hkeyOf k hk k' hk' he⟩)

end Tools.ShippingMemCloses
