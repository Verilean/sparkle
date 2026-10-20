import Tools.ShippingDesignSV
import Tools.ShippingHierPremisesBase
import Tools.ShippingMachineShipsDepth
import Tools.ShippingChecksDepth
import Tools.ShippingChecksDerived

/-! # The design's checks read the child map only at the instances' names (G1, unit U2, round par/a-13)

A child WITH calls of its own is checked, under a parent, against the
PARENT's child map (`designCheck C k y.1` with `C = childMap D.modules`,
`D` the parent's design); what its own run gives is about ITS child map
(`childMap D'.modules`, `D'` the child's design). The two maps differ (the
parent's design has more modules) but agree on the names the child's
instance statements use — and that is all the body-level checks read:

* `AgreeOn C C' body`: `C mn = C' mn` for every instance statement
  `.inst mn _ _` of `body`;
* `linkedWF_congr`, `noSelfRead_congr`, `portsMatchB_congr`,
  `kidsPass_congr`: each check has the same value under two maps that agree
  on the body's instances (`linkedWF` through `bodyInstOuts_congr`,
  `linkedWrites_congr`).

And two pure facts about a module that is a closed machine's body plus
instance statements, permuted (what either closing returns,
`CloseCalls.some`):

* `outMaskedB_perm_insts`: an output port masked in the closed machine's
  body is masked in the permuted body with the instance statements (an
  instance statement writes nothing in the combinational fold:
  `stmtWrites (.inst ..) = []`);
* `outsMaskedN_of_typed`: `outsMaskedN` of a module of assignments,
  registers and instances whose outputs are masked and whose instance
  connections name no output port (`Tools.ShippingChecksMasked.outsMaskedN_of_seqOk`
  asks a body WITHOUT instances).

Pure: no run, no compiler function.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingChildMapCongr
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierOpen (stmtInstOuts bodyInstOuts linkedWrites linkedWF)

/-- Two child maps agree on the modules the instance statements of `body`
name. -/
def AgreeOn (C C' : String → Option (Module × WEnv)) (body : List Stmt) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → C mn = C' mn

variable {C C' : String → Option (Module × WEnv)}

theorem AgreeOn.tail {st : Stmt} {rest : List Stmt} (h : AgreeOn C C' (st :: rest)) :
    AgreeOn C C' rest :=
  fun mn iname conns hm => h mn iname conns (List.mem_cons_of_mem _ hm)

theorem AgreeOn.head {st : Stmt} {rest : List Stmt} (h : AgreeOn C C' (st :: rest)) :
    ∀ mn iname conns, st = Stmt.inst mn iname conns → C mn = C' mn := by
  intro mn iname conns e
  subst e
  exact h mn iname conns (List.mem_cons_self ..)

/-- The wires one statement's instance drives, under two maps that agree at
its name. -/
theorem stmtInstOuts_congr (st : Stmt)
    (h : ∀ mn iname conns, st = Stmt.inst mn iname conns → C mn = C' mn) :
    stmtInstOuts C st = stmtInstOuts C' st := by
  cases st with
  | inst mn iname conns =>
    have e := h mn iname conns rfl
    simp only [Tools.ShippingHierOpen.stmtInstOuts, e]
  | _ => rfl

theorem bodyInstOuts_congr : ∀ (body : List Stmt), AgreeOn C C' body →
    bodyInstOuts C body = bodyInstOuts C' body
  | [], _ => rfl
  | st :: rest, h => by
    have ih := bodyInstOuts_congr rest (AgreeOn.tail h)
    have hs := stmtInstOuts_congr st (AgreeOn.head h)
    simp only [Tools.ShippingHierOpen.bodyInstOuts, ih, hs]

theorem linkedWrites_congr : ∀ (body : List Stmt), AgreeOn C C' body →
    linkedWrites C body = linkedWrites C' body
  | [], _ => rfl
  | st :: rest, h => by
    have ih := linkedWrites_congr rest (AgreeOn.tail h)
    have hs := stmtInstOuts_congr st (AgreeOn.head h)
    cases st with
    | assign l r => simp only [Tools.ShippingHierOpen.linkedWrites, ih]
    | _ => simp only [Tools.ShippingHierOpen.linkedWrites, ih, hs]

/-- **`linkedWF` reads the child map at the instances' names only.** -/
theorem linkedWF_congr : ∀ (body : List Stmt), AgreeOn C C' body →
    linkedWF C body = linkedWF C' body
  | [], _ => rfl
  | st :: rest, h => by
    have ih := linkedWF_congr rest (AgreeOn.tail h)
    have hb := bodyInstOuts_congr rest (AgreeOn.tail h)
    have hw := linkedWrites_congr rest (AgreeOn.tail h)
    cases st with
    | assign l r => simp only [Tools.ShippingHierOpen.linkedWF, ih, hb]
    | inst mn iname conns =>
      have e := h mn iname conns (List.mem_cons_self ..)
      simp only [Tools.ShippingHierOpen.linkedWF, ih, hw, e]
    | _ => simp only [Tools.ShippingHierOpen.linkedWF, ih]

/-- Two per-statement tests that agree on the statements of a body have the
same `all`. -/
theorem all_congr_mem {body : List Stmt} (f g : Stmt → Bool)
    (h : ∀ st ∈ body, f st = g st) : body.all f = body.all g := by
  induction body with
  | nil => rfl
  | cons st rest ih =>
    simp only [List.all_cons]
    rw [h st (List.mem_cons_self ..), ih (fun s hs => h s (List.mem_cons_of_mem _ hs))]

/-- **`noSelfRead` reads the child map at the instances' names only.** -/
theorem noSelfRead_congr {body : List Stmt} (h : AgreeOn C C' body) :
    Tools.ShippingHierPremisesBase.noSelfRead C body =
      Tools.ShippingHierPremisesBase.noSelfRead C' body := by
  unfold Tools.ShippingHierPremisesBase.noSelfRead
  refine all_congr_mem _ _ (fun st hst => ?_)
  cases st with
  | inst mn iname conns =>
    have e := h mn iname conns hst
    simp only [e]
  | _ => rfl

/-- **`portsMatchB` reads the child map at the instances' names only.** -/
theorem portsMatchB_congr {o : Module} (h : AgreeOn C C' o.body) :
    Tools.ShippingDesignSV.portsMatchB C o = Tools.ShippingDesignSV.portsMatchB C' o := by
  unfold Tools.ShippingDesignSV.portsMatchB
  refine all_congr_mem _ _ (fun st hst => ?_)
  cases st with
  | inst mn iname conns =>
    have e := h mn iname conns hst
    simp only [e]
  | _ => rfl

/-- **`kidsPass` reads the child map at the instances' names only.** -/
theorem kidsPass_congr {body : List Stmt} (f : Module → Bool) (h : AgreeOn C C' body) :
    Tools.ShippingDesignSV.kidsPass C f body = Tools.ShippingDesignSV.kidsPass C' f body := by
  unfold Tools.ShippingDesignSV.kidsPass
  refine all_congr_mem _ _ (fun st hst => ?_)
  cases st with
  | inst mn iname conns =>
    have e := h mn iname conns hst
    simp only [e]
  | _ => rfl

/-! ## A closed machine's body plus instance statements -/

/-- Instance statements write nothing in the combinational fold. -/
theorem writesOf_insts : ∀ (L : List Stmt), L.all Sparkle.IR.Machine.isInst = true →
    Sparkle.IR.Reorder.writesOf L = []
  | [], _ => rfl
  | st :: rest, h => by
    have h' : Sparkle.IR.Machine.isInst st = true ∧
        rest.all Sparkle.IR.Machine.isInst = true := by
      simpa only [List.all_cons, Bool.and_eq_true] using h
    have ih := writesOf_insts rest h'.2
    cases st with
    | inst mn iname conns =>
      have e : Sparkle.IR.Reorder.writesOf (Stmt.inst mn iname conns :: rest) =
          Sparkle.IR.Reorder.writesOf [Stmt.inst mn iname conns] ++
            Sparkle.IR.Reorder.writesOf rest :=
        Sparkle.IR.Reorder.writesOf_append [Stmt.inst mn iname conns] rest
      rw [e, ih]
      rfl
    | _ => exact Tools.ShippingChecksDerived.ff_absurd h'.1

/-- **An output port masked in a body is masked in the body with instance
statements added and permuted** (what either closing does to the closed
machine's body). -/
theorem outMaskedB_perm_insts {we : WEnv} {b0 L body : List Stmt} {p : Port}
    (hL : L.all Sparkle.IR.Machine.isInst = true) (hperm : (b0 ++ L).Perm body)
    (h : Sparkle.IR.RefineCheck.outMaskedB we b0 p = true) :
    Sparkle.IR.RefineCheck.outMaskedB we body p = true := by
  unfold Sparkle.IR.RefineCheck.outMaskedB at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  obtain ⟨hc, ha⟩ := h
  refine ⟨?_, ?_⟩
  · have hW : Sparkle.IR.Reorder.writesOf (b0 ++ L) = Sparkle.IR.Reorder.writesOf b0 := by
      rw [Sparkle.IR.Reorder.writesOf_append, writesOf_insts L hL, List.append_nil]
    have hP : (Sparkle.IR.Reorder.writesOf (b0 ++ L)).Perm (Sparkle.IR.Reorder.writesOf body) :=
      hperm.flatMap_right _
    rw [← hP.count_eq, hW]
    exact hc
  · obtain ⟨st, hst, hm⟩ := List.any_eq_true.mp ha
    exact List.any_eq_true.mpr ⟨st, hperm.subset (List.mem_append_left _ hst), hm⟩

/-- **`outsMaskedN` of a module of assignments, registers and instances**:
no memory, the outputs masked, and no instance connection naming an output
port. -/
theorem outsMaskedN_of_typed {c : Module}
    (hk : ∀ st ∈ c.body, Tools.ShippingHierSVSoundness.seqStmtOkI st = true)
    (hm : ∀ p ∈ c.outputs,
      Tools.ShippingMachineShipsHier.outMasked (Sparkle.IR.RegDedup.declWidth c) c.body p = true)
    (hconn : ∀ p ∈ c.outputs, ∀ mn iname conns, Stmt.inst mn iname conns ∈ c.body →
      ∀ cn ∈ conns, cn.2 ≠ Sparkle.IR.AST.Expr.ref p.name) :
    Tools.ShippingMachineShipsDepth.outsMaskedN c = true := by
  unfold Tools.ShippingMachineShipsDepth.outsMaskedN Tools.ShippingMachineShipsHier.noMem
  refine Tools.ShippingChecksDepth.and_true_intro
    (List.all_eq_true.mpr fun st hst => ?_)
    (List.all_eq_true.mpr fun p hp => Tools.ShippingChecksDepth.and_true_intro (hm p hp)
      (List.all_eq_true.mpr fun st hst => ?_))
  · have hst' := hk st hst
    cases st <;> first | rfl | exact Tools.ShippingChecksDerived.ff_absurd hst'
  · cases st with
    | inst mn iname conns =>
      exact List.all_eq_true.mpr fun cn hcn =>
        decide_eq_true (hconn p hp mn iname conns hst cn hcn)
    | _ => rfl

end Tools.ShippingChildMapCongr
