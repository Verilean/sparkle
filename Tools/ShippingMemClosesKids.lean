import Tools.ShippingCallsKidsD
import Tools.ShippingMemClosesRun
import Tools.ShippingMemKidFacts

variable {tenv : Lean.Environment}

/-! # `MachineClosesAt` over children that are memory placeholders OR real children (M2, round par/a-18)

`machineClosesAt_of_kidsD` (`Tools/ShippingCallsKidsD.lean` 98–317) cannot be
used for a parent with a memory: besides `hnomem` (108, used at 158 through
`closeInstsGM_run_all`), two fields of its child interface `ChildIfaceD` are
FALSE of the built memory module `memModule cb aw dw`
(`Sparkle/Compiler/MachMemory.lean` 46–58), and one premise is false of a
memory entry:

* `name : b.name = (Sparkle.IR.ModuleName.ofDecl c)` (39) — the module is named
  `SparkleMem_combo_4_8`, the placeholder prints `SparkleMem.combo.4.8`;
* `noMem : memParams? b = none` (46) — the module's body IS the memory
  statement;
* `hselfD : (Sparkle.IR.ModuleName.ofDecl c) ∉ namesK k` (129–130) — the memory module's design is
  `[itself]` (line 58), so its own name is a name of its design.

What the closing's check asks instead (`closeInstsG_of_run`,
`Tools/ShippingCallsRunG.lean` 127–134): `memSelf` — a child with a
memory-shaped body is found, by its name, as a module `isMemModule` accepts;
every child and every module of a child's design is found by its name AS
ITSELF; no visited module has an instance of the parent. None of these asks
"no memory" or "the child is not in its own design".

So the interface here, `ChildIfaceP`, has

* `name : b.name = nm` for a printed name `nm` given per entry (a real
  child: `(Sparkle.IR.ModuleName.ofDecl c)`; a memory: the module's name);
* `memOk : ∀ cb aw dw, memParams? b = some (cb, aw, dw) → isMemModule cb aw dw b = true`
  in place of `noMem` (vacuous when `memParams? b = none`; TRUE of the memory
  module: `isMemModule_memModule`);
* `self : ∀ g ∈ design.modules, g.name = b.name → g = b` in place of the
  premise `hselfD` (vacuous when the child's name is not in its design; TRUE
  of the memory module, whose design is `[itself]`);
* `resolves` dropped (the proof of `machineClosesAt_of_kidsD` never uses it).

Contents:

* `memSelf_of`, `design_checksM` — `design_checks`
  (`Tools/ShippingDesignWithG.lean` 83–110) with "no memory child" replaced
  by `memOk`; `design_checks_again` re-derives the old statement.
* `isMemModule_memModule`, `memIface`, `memKid_iface` — the built memory
  module has the interface, for every read kind and widths.
* `ChildIfaceD.toP` — a `ChildIfaceD` child whose name is not in its design.
* `closeInstsG_of_kidsP` — PURE (no world): the general pure closing returns
  a module on children with `ChildIfaceP`, given that two entries of one
  declaration have one child (`hpair`) and that the children of two entries
  of DIFFERENT declarations agree on every module name they both have
  (`hcross`).
* `machineClosesAt_of_kidsDM` (M2) — `MachineClosesAt` of a parent whose
  children are `Kid`s; `hpair` from M1 (`closeInstsGM_run_allM`), `hcross`
  from name disjointness (`hdisjD`, as in the old theorem). No `hnomem`.
* `machineClosesAt_of_kidsD_fromM` — the statement of
  `machineClosesAt_of_kidsD`, from M2. The old theorem is unchanged and is
  still what the generators use; this shows M2 generalises it.

NOT here: callees that share a descendant (`hdisjD` is asked; the relative
closing of `Tools/ShippingCallsKidsS.lean` is not generalised to memory
entries — its `hcross` would come from `closeInstsG_of_kidsP`'s hypothesis of
the same name).

WRITTEN, NOT BUILT (par/a-18).

ORIGIN DISPATCH (patched compiler): `machineClosesAt_of_kidsDM` now also asks
`hagree : TagsAgree d.shape` (every entry's name decodes to what its ORIGIN
builds; decided per declaration, false exactly for a collision shape) and uses
`closeInstsGM_run_allM_named`; `machineClosesAt_of_kidsD_fromM` derives it
from `hnomem` and the tag condition `hnotag` (`tagsAgree_of_nomem_notag`).
OPEN: a collision shape (a memory entry beside a call of a declaration named
as its placeholder) needs `closeInstsG_of_kidsP` keyed on (name, origin
class) instead of the name. WRITTEN, NOT BUILT against patched compiler
(par/o-close). -/
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

/-! ## The design checks, with memory children -/

/-- `memSelf` of a module that resolves to itself and, if its body is
memory-shaped, is the built memory module of its parameters. -/
theorem memSelf_of {find : String → Option Sparkle.IR.AST.Module} {c : Sparkle.IR.AST.Module}
    (hf : find c.name = some c)
    (hm : ∀ (cb : Bool) (aw dw : Nat), memParams? c = some (cb, aw, dw) →
      isMemModule cb aw dw c = true) :
    memSelf find c = true := by
  unfold Sparkle.Compiler.MachMemory.memSelf
  cases h : memParams? c with
  | none => rfl
  | some p =>
    obtain ⟨cb, aw, dw⟩ := p
    show (find c.name).any (isMemModule cb aw dw) = true
    rw [hf]
    exact hm cb aw dw h

/-- **The design checks of the general closing, memory children allowed**:
`design_checks` with "no child has a memory-shaped body" replaced by "a child
with a memory-shaped body is the built memory module of its parameters". -/
theorem design_checksM {children : List (Sparkle.IR.AST.Module × Design)} {d : Design}
    {parent : String} (hd : d.modules = [])
    (hcons : ∀ a ∈ visited children, ∀ b ∈ visited children, a.name = b.name → a = b)
    (hmem : ∀ c ∈ children, ∀ (cb : Bool) (aw dw : Nat),
      memParams? c.1 = some (cb, aw, dw) → isMemModule cb aw dw c.1 = true)
    (hno : ∀ g ∈ visited children, noInstOfB parent g.body = true) :
    children.all (fun c => Sparkle.Compiler.MachMemory.memSelf
      (moduleByName (designWith children d).modules) c.1) = true ∧
    children.all (fun c =>
      decide (moduleByName (designWith children d).modules c.1.name = some c.1) &&
      c.2.modules.all (fun g =>
        decide (moduleByName (designWith children d).modules g.name = some g))) = true ∧
    (designWith children d).modules.all (fun g => noInstOfB parent g.body) = true := by
  obtain ⟨hres, hmods⟩ := designWith_resolvesG hd hcons
  refine ⟨?_, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro c hc
    exact memSelf_of (find := moduleByName (designWith children d).modules) (c := c.1)
      (hres c.1 (mem_visited.mpr ⟨c, hc, Or.inl rfl⟩)) (hmem c hc)
  · rw [List.all_eq_true]
    intro c hc
    rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨hres c.1 (mem_visited.mpr ⟨c, hc, Or.inl rfl⟩), fun g hg => ?_⟩
    rw [decide_eq_true_eq]
    exact hres g (mem_visited.mpr ⟨c, hc, Or.inr hg⟩)
  · rw [List.all_eq_true]
    intro g hg
    exact hno g (hmods g hg)

/-- The statement of `design_checks`, from `design_checksM`. -/
theorem design_checks_again {children : List (Sparkle.IR.AST.Module × Design)} {d : Design}
    {parent : String} (hd : d.modules = [])
    (hcons : ∀ a ∈ visited children, ∀ b ∈ visited children, a.name = b.name → a = b)
    (hmem : ∀ c ∈ children, memParams? c.1 = none)
    (hno : ∀ g ∈ visited children, noInstOfB parent g.body = true) :
    children.all (fun c => Sparkle.Compiler.MachMemory.memSelf
      (moduleByName (designWith children d).modules) c.1) = true ∧
    children.all (fun c =>
      decide (moduleByName (designWith children d).modules c.1.name = some c.1) &&
      c.2.modules.all (fun g =>
        decide (moduleByName (designWith children d).modules g.name = some g))) = true ∧
    (designWith children d).modules.all (fun g => noInstOfB parent g.body) = true :=
  design_checksM hd hcons
    (fun c hc cb aw dw h => by
      rw [hmem c hc] at h
      cases h)
    hno

/-! ## The interface -/

/-- **What the general closing asks of a child** — a real child with a design
of its own, or a built memory module. `nm` is the child module's name. -/
structure ChildIfaceP (nm : String) (nArgs : Nat) (outs names : List String)
    (b : Sparkle.IR.AST.Module) (design : Design) : Prop where
  name : b.name = nm
  nIn : (inPortsOf b).length = nArgs
  inNd : ((inPortsOf b).map (·.name)).Nodup
  outs : b.outputs.map (·.name) = outs
  outsIn : ∀ p ∈ b.outputs, (∀ q ∈ inPortsOf b, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
    p.name ≠ "rst"
  outsNd : (b.outputs.map (·.name)).Nodup
  memOk : ∀ (cb : Bool) (aw dw : Nat), memParams? b = some (cb, aw, dw) →
    isMemModule cb aw dw b = true
  desNd : (design.modules.map (·.name)).Nodup
  desNames : ∀ g ∈ design.modules, g.name ∈ names
  self : ∀ g ∈ design.modules, g.name = b.name → g = b
  closed : ∀ g ∈ b :: design.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body → mn ∈ names

/-- A child with a design of its own (`ChildIfaceD`) whose printed name is
not a name of its design. -/
theorem _root_.Tools.ShippingCallsKidsD.ChildIfaceD.toP {c : Name} {nArgs : Nat} {outs names : List String}
    {b : Sparkle.IR.AST.Module} {design : Design} (h : ChildIfaceD c nArgs outs names b design)
    (hself : (Sparkle.IR.ModuleName.ofDecl c) ∉ names) : ChildIfaceP (Sparkle.IR.ModuleName.ofDecl c) nArgs outs names b design := by
  refine ⟨h.name, h.nIn, h.inNd, h.outs, h.outsIn, h.outsNd, ?_, h.desNd, h.desNames, ?_,
    h.closed⟩
  · intro cb aw dw hm
    rw [h.noMem] at hm
    cases hm
  · intro g hg he
    exfalso
    apply hself
    rw [← h.name, ← he]
    exact h.desNames g hg

/-- The recognizer accepts the module it is the recognizer of, for every read
kind and widths. -/
theorem isMemModule_memModule (cb : Bool) (aw dw : Nat) :
    isMemModule cb aw dw (memModule cb aw dw).1 = true := by
  first
    | simp [Sparkle.Compiler.MachMemory.isMemModule, Sparkle.Compiler.MachMemory.memModule,
        Sparkle.Compiler.MachMemory.portKey]
    | (cases cb <;>
        simp (config := { decide := true }) [Sparkle.Compiler.MachMemory.isMemModule,
          Sparkle.Compiler.MachMemory.memModule, Sparkle.Compiler.MachMemory.portKey])

/-- **The built memory module has the interface**: four argument ports, the
output `out`, and a design that is the module itself. -/
theorem memIface (cb : Bool) (aw dw : Nat) :
    ChildIfaceP (memModule cb aw dw).1.name 4 ["out"] [(memModule cb aw dw).1.name]
      (memModule cb aw dw).1 (memModule cb aw dw).2 := by
  refine ⟨rfl, ?_, ?_, rfl, mem_outsIn cb aw dw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mem_inPorts]
  · rw [mem_inPorts]
    show (["wa", "wd", "we", "ra"] : List String).Nodup
    first
      | decide
      | simp
  · show (["out"] : List String).Nodup
    exact List.nodup_cons.mpr ⟨(fun hx => nomatch hx), List.nodup_nil⟩
  · intro cb' aw' dw' hm
    have hm' : some (cb, aw, dw) = some (cb', aw', dw') := hm
    have e := Option.some.inj hm'
    have e1 : cb = cb' := congrArg (fun (p : Bool × Nat × Nat) => p.1) e
    have e2 : aw = aw' := congrArg (fun (p : Bool × Nat × Nat) => p.2.1) e
    have e3 : dw = dw' := congrArg (fun (p : Bool × Nat × Nat) => p.2.2) e
    rw [← e1, ← e2, ← e3]
    exact isMemModule_memModule cb aw dw
  · show ([(memModule cb aw dw).1.name] : List String).Nodup
    exact List.nodup_cons.mpr ⟨(fun hx => nomatch hx), List.nodup_nil⟩
  · intro g hg
    rw [mem_design hg]
    exact List.mem_cons_self ..
  · intro g hg _
    exact mem_design hg
  · intro g hg mn i conns hm
    have hgm : g = (memModule cb aw dw).1 := by
      rcases List.mem_cons.mp hg with h | h
      · exact h
      · exact mem_design h
    rw [hgm] at hm
    exact absurd hm (mem_noInst cb aw dw mn i conns)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- **A kid of a memory placeholder has the interface.** -/
theorem memKid_iface {c : Name} {cb : Bool} {aw dw : Nat}
    (hc : memChild? c = some (memModule cb aw dw)) {y : Res} (hy : Kid mref cref c y) :
    ChildIfaceP (memModule cb aw dw).1.name 4 ["out"] [(memModule cb aw dw).1.name] y.1 y.2 := by
  have e := hy.mem hc
  subst e
  exact memIface cb aw dw

theorem mem_cons_of_or {g : Sparkle.IR.AST.Module} {c : Res}
    (h : g = c.1 ∨ g ∈ c.2.modules) : g ∈ c.1 :: c.2.modules := by
  rcases h with h | h
  · rw [h]
    exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ h

/-! ## The pure closing -/

set_option maxHeartbeats 1000000 in
/-- **The general pure closing returns a module** on children with
`ChildIfaceP`, for a real run of the harness — given that two entries of one
declaration have one child (`hpair`) and that the children of two entries of
different declarations agree on every module name they both have (`hcross`).
No world, no memory hypothesis. -/
theorem closeInstsG_of_kidsP {declName : Name} (d : MachineData) (ok : d.ok = true)
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
      (d.shape.insts[i]).1 = (d.shape.insts[j]).1 → children[i]? = children[j]?)
    (hcross : ∀ (i j : Nat) (hi : i < d.shape.insts.length) (hj : j < d.shape.insts.length)
      (ci cj : Res), children[i]? = some ci → children[j]? = some cj →
      (d.shape.insts[i]).1 ≠ (d.shape.insts[j]).1 →
      ∀ a ∈ ci.1 :: ci.2.modules, ∀ b ∈ cj.1 :: cj.2.modules, a.name = b.name → a = b)
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
    have hsame := hpair i j hki hkj (hsep i hki j hkj hn)
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
    by_cases hdecl : (d.shape.insts[i]).1 = (d.shape.insts[j]).1
    · -- one declaration: one child (module and design)
      have hsame := hpair i j hki hkj hdecl
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
    · -- different declarations
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
    exact hfieldsNd k hk k' hk' (hsep k hk k' hk' hn)
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

/-! ## The closing -/

set_option maxHeartbeats 1000000 in
/-- **(M2) `MachineClosesAt` for the general closing over kids** — memory
placeholders or real children with designs of their own. `nameK k` is the
module name of entry `k`'s child. Name separation as in
`machineClosesAt_of_kidsD`, over the module names: different declarations
have different module names (`hsep`), no child is named as the parent
(`hparent`, `hparentD`), and two different declarations share no name
(`hdisjD`). No memory hypothesis; `hselfD` is the field `self` of the
interface. -/
theorem machineClosesAt_of_kidsDM {declName : Name} (d : MachineData) (ok : d.ok = true)
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
  obtain ⟨children, rfl, hreal, hpair, -⟩ := closeInstsGM_run_allM_named L hB hw1 hd1 hagree hr
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
    -- two entries of one declaration are one child (module and design)
    have hsameDecl : ∀ (i j : Nat) (hi : i < d.shape.insts.length)
        (hj : j < d.shape.insts.length), (d.shape.insts[i]).1 = (d.shape.insts[j]).1 →
        children[i]? = children[j]? := by
      intro i j hki hkj hcc
      have hni : (d.shape.insts.map (·.1))[i]? = some (d.shape.insts[i]).1 := by simp [hki]
      have hnj : (d.shape.insts.map (·.1))[j]? = some (d.shape.insts[j]).1 := by simp [hkj]
      rw [← hcc] at hnj
      rcases Nat.lt_trichotomy i j with h | h | h
      · exact hpair i j _ h hni hnj
      · rw [h]
      · exact (hpair j i _ h hnj hni).symm
    refine closeInstsG_of_kidsP d ok hbody hC hslots hdomB run.mreturns hcl hlenC nameK nk outsK
      namesK hfull hsameDecl ?_ hargsN hfieldOut hfieldsNd hsep hparent hfresh hparentD
    -- two entries of DIFFERENT declarations: no module name in common
    intro i j hki hkj ci cj hci hcj hdecl a ha b' hb hn
    exfalso
    have fi := hfull i ci hci
    have fj := hfull j cj hcj
    obtain ⟨hx1, hx2⟩ := hdisjD i hki j hkj hdecl
    obtain ⟨hx3, -⟩ := hdisjD j hkj i hki (fun e => hdecl e.symm)
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
/-- **The statement of `machineClosesAt_of_kidsD`, from M2**: without a
memory entry every kid is a real child, its module is named as the
declaration prints, and `hselfD` gives the interface's `self`. Not a
replacement of the theorem in `Tools/ShippingCallsKidsD.lean` (unchanged, and
still what the generators use): the check that M2 generalises it. -/
theorem machineClosesAt_of_kidsD_fromM {declName : Name} (d : MachineData) (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (halias : d.letsAliasOk = true)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hfne : d.shape.instFields ≠ [])
    (nk : Nat → Nat) (outsK : Nat → List String) (namesK : Nat → List String)
    (hnomem : ∀ c ∈ d.shape.insts, Sparkle.Compiler.MachMemory.memChild? c.1 = none)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      ChildIfaceD (d.shape.insts[k]).1 (nk k) (outsK k) (namesK k) y.1 y.2)
    (hargsN : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      nk k = (d.shape.insts[k]).2.1.length)
    (hfieldOut : ∀ (k : Nat), k < d.shape.insts.length →
      d.shape.instFields.getD k "" ∈ outsK k)
    (hfieldsNd : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 = (d.shape.insts[k']).1 →
      (d.shape.insts[k]).2.1 = (d.shape.insts[k']).2.1 →
      d.shape.instFields.getD k "" = d.shape.instFields.getD k' "" → k = k')
    (hsep : ∀ c ∈ d.shape.insts.map (·.1), ∀ c' ∈ d.shape.insts.map (·.1),
      (Sparkle.IR.ModuleName.ofDecl c) = (Sparkle.IR.ModuleName.ofDecl c') → c = c')
    (hparent : ∀ c ∈ d.shape.insts, (Sparkle.IR.ModuleName.ofDecl c.1) ≠ (Sparkle.IR.ModuleName.ofDecl declName))
    (hfresh : ∀ (gi : Nat), ∀ c ∈ d.shape.insts, ∀ o ∈ d.shape.layout.outs,
      o.name ≠ s!"inst{gi}_{(Sparkle.IR.ModuleName.ofDecl c.1)}")
    (hparentD : ∀ (k : Nat), k < d.shape.insts.length → (Sparkle.IR.ModuleName.ofDecl declName) ∉ namesK k)
    (hselfD : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      (Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1) ∉ namesK k)
    (hdisjD : ∀ (k : Nat) (hk : k < d.shape.insts.length) (k' : Nat)
      (hk' : k' < d.shape.insts.length), (d.shape.insts[k]).1 ≠ (d.shape.insts[k']).1 →
      (Sparkle.IR.ModuleName.ofDecl (d.shape.insts[k]).1) ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k')
    (hnotag : ∀ o ∈ d.shape.instTagged, o.2.child?.isNone = true) :
    MachineClosesAt mctx mref cctx cref declName d.shape := by
  refine machineClosesAt_of_kidsDM d ok hbody halias hC hslots hdomB hfne
    (fun k => (Sparkle.IR.ModuleName.ofDecl (calleeAt d k))) nk outsK namesK ?_ hargsN hfieldOut hfieldsNd ?_ ?_ ?_
    hparentD ?_ (Tools.ShippingInstTagged.tagsAgree_of_nomem_notag hnomem hnotag)
  · intro k hk y hy
    show ChildIfaceP (Sparkle.IR.ModuleName.ofDecl (calleeAt d k)) (nk k) (outsK k) (namesK k) y.1 y.2
    rw [calleeAt_eq d hk]
    exact Tools.ShippingCallsKidsD.ChildIfaceD.toP
      (hkid k hk y (hy.real (hnomem _ (List.getElem_mem hk)))) (hselfD k hk)
  · intro k hk k' hk' he
    have he' : (Sparkle.IR.ModuleName.ofDecl (calleeAt d k)) = (Sparkle.IR.ModuleName.ofDecl (calleeAt d k')) := he
    rw [calleeAt_eq d hk, calleeAt_eq d hk'] at he'
    exact hsep _ (List.mem_map_of_mem (List.getElem_mem hk)) _
      (List.mem_map_of_mem (List.getElem_mem hk')) he'
  · intro k hk
    show (Sparkle.IR.ModuleName.ofDecl (calleeAt d k)) ≠ (Sparkle.IR.ModuleName.ofDecl declName)
    rw [calleeAt_eq d hk]
    exact hparent _ (List.getElem_mem hk)
  · intro gi k hk o ho
    show o.name ≠ s!"inst{gi}_{(Sparkle.IR.ModuleName.ofDecl (calleeAt d k))}"
    rw [calleeAt_eq d hk]
    exact hfresh gi _ (List.getElem_mem hk) o ho
  · intro k hk k' hk' hne
    show (Sparkle.IR.ModuleName.ofDecl (calleeAt d k)) ∉ namesK k' ∧ ∀ x ∈ namesK k, x ∉ namesK k'
    rw [calleeAt_eq d hk]
    exact hdisjD k hk k' hk' hne

end Tools.ShippingMemCloses
