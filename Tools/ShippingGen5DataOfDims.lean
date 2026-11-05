import Tools.ShippingGen5DataOf
set_option autoImplicit false
-- NOT BUILT by an issue-linked clean build (agent build: Tools.ShippingGen5DataOfDims 365 jobs, Tests.Gen5.DataOfCheck4 762 jobs, exit 0; the clean build is the coder's). No sorry / axiom / native_decide.

/-! # DG-DATAOF row 6b: the `d`-side facts of DG-COVER's `ShapeAgree`

Statements are those of `scripts/gen5/DG_DATAOF_FREEZE.md` rev3 §10. All of them are about one `d` obtained from one
`dataOfFrom` / `dataOfAt` success. Not supplied: that `dataOfAt` is `some`, that `s` is the run's `sp`, entrywise agreement, row 6a. -/
namespace Tools.ShippingGen5DataOf
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineAuto Tools.ShippingMachineCommand
open Tools.ShippingMachineEntry Tools.ShippingReaderInputs Tools.ShippingReaderApp
open Tools.ShippingReaderTerm Tools.ShippingGen5DataOfPure Tools.ShippingGen5DataOfPure2
open Tools.ShippingMixedSourceBridge (inputExpr)
open Sparkle.Core Sparkle.IR.Machine Sparkle.Compiler.Elab

theorem mapM_unField_length : ∀ (l : List (MixedGateBinder × Σ w : Nat, Term (.bits w)))
    (r : List (Σ s : SType, Term s)), l.mapM (fun p => unField p.1 p.2) = some r → r.length = l.length
  | [], r, h => by
    rw [List.mapM_nil] at h
    have := Option.some.inj h
    subst this; rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases hf : unField a.1 a.2 with
    | none => simp [hf] at h
    | some x =>
      cases hm : l.mapM (fun p => unField p.1 p.2) with
      | none => simp [hf, hm] at h
      | some r' =>
        simp [hf, hm, pure, bind] at h
        subst h
        simp [mapM_unField_length l r' hm]

theorem typedFields_length {ks : List MixedGateBinder} {fs : List (Σ w : Nat, Term (.bits w))}
    {r : List (Σ s : SType, Term s)} (h : typedFields ks fs = some r) :
    r.length = min ks.length fs.length := by
  unfold typedFields at h
  rw [mapM_unField_length _ r h, List.length_zip]

theorem dataOfFront_some {E : Lean.ConstantInfo} {senv : StructEnv} {shape : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {nIn : Nat} {dom : Lean.Expr}
    (h : dataOfFront E senv shape tin fl = some (nIn, dom)) :
    (∃ p, mixedGatePeel tin = some p ∧ nIn = p.1.length + shape.insts.length) ∧
    shape.binders.length = nIn + shape.layout.slots.length + shape.layout.lets := by
  unfold dataOfFront at h
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
  dsimp only at h
  by_cases hg : (shape.binders.length == p.1.length + shape.insts.length + shape.layout.slots.length
      + shape.layout.lets) = true
  · rw [if_pos hg] at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h
    have h' := Option.some.inj h
    have hn : p.1.length + shape.insts.length = nIn := (Prod.mk.inj h').1
    refine ⟨⟨p, hp, hn.symm⟩, ?_⟩
    have := beq_iff_eq.1 hg
    omega
  · rw [if_neg hg] at h
    cases h

theorem dataOfTail_dims {shape : MachineShape} {nIn : Nat} {dom : Lean.Expr} {W : Nat} {whole : Term (.bits W)}
    {d : MachineData}
    (hb : shape.binders.length = nIn + shape.layout.slots.length + shape.layout.lets)
    (h : dataOfTail shape nIn dom W whole = some d) :
    d.nIn = nIn ∧ d.ss.length = shape.layout.slots.length ∧ d.ls.length = shape.layout.lets := by
  unfold dataOfTail at h
  obtain ⟨⟨l1, core⟩, hlc, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨fs, hfs, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨ls, hls, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨outs, hout, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨nl, hnl, hc⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨rfl, _, _⟩ := checked_sound hc
  obtain ⟨hl1, _⟩ := splitLets_some hlc
  obtain ⟨_, hfl, _⟩ := splitFields_some hfs
  have e1 := typedFields_length hls
  have e2 := typedFields_length hnl
  simp only [List.length_drop, List.length_take, List.length_map] at e1 e2
  refine ⟨rfl, ?_, ?_⟩
  · show (nl.map (·.1)).length = _
    rw [List.length_map]; omega
  · show ls.length = _
    omega

theorem dataOfCore_dims (lvl : Lean.Expr → Nat) {shape : MachineShape} {nIn : Nat} {dom : Lean.Expr}
    {d : MachineData}
    (hb : shape.binders.length = nIn + shape.layout.slots.length + shape.layout.lets)
    (h : dataOfCore lvl shape nIn dom = some d) :
    d.shape = shape ∧ d.nIn = nIn ∧ d.ss.length = shape.layout.slots.length ∧ d.ls.length = shape.layout.lets := by
  unfold dataOfCore at h
  split at h
  · rename_i W whole hr
    obtain ⟨hs, _⟩ := dataOfCore_sound lvl (by unfold dataOfCore; rw [hr]; exact h)
    exact ⟨hs, dataOfTail_dims hb h⟩
  · cases h

theorem dataOfFrom_nIn (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (h : dataOfFrom lvl E senv s tin fl = some d) :
    ∃ p, mixedGatePeel tin = some p ∧ d.nIn = p.1.length + s.insts.length := by
  unfold dataOfFrom at h
  obtain ⟨⟨nIn, dom⟩, hf, hc⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨p, hp, hn⟩, hb⟩ := dataOfFront_some hf
  obtain ⟨_, hd, _⟩ := dataOfCore_dims lvl hb hc
  exact ⟨p, hp, hd.trans hn⟩

theorem dataOfFrom_dims (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (h : dataOfFrom lvl E senv s tin fl = some d) :
    d.shape = s ∧ d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length ≤ d.nIn := by
  obtain ⟨p, _, hn⟩ := dataOfFrom_nIn lvl h
  unfold dataOfFrom at h
  obtain ⟨⟨nIn, dom⟩, hf, hc⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨_, hb⟩ := dataOfFront_some hf
  obtain ⟨h1, _, h3, h4⟩ := dataOfCore_dims lvl hb hc
  exact ⟨h1, h3, h4, by omega⟩

theorem dataOfFrom_sound_dims (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv}
    {s : MachineShape} {tin : Lean.Expr} {fl : Lean.Expr → Lean.Expr} {d : MachineData}
    (h : dataOfFrom lvl E senv s tin fl = some d) :
    (d.shape = s ∧ d.ok = true ∧
      d.shape.body = quote d.dom
        (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
      d.initOk (initsOf d) = true) ∧
    (d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length ≤ d.nIn) :=
  ⟨dataOfFrom_sound lvl h, (dataOfFrom_dims lvl h).2⟩

theorem dataOfAt_dims (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv} {s : MachineShape}
    {d : MachineData} (h : dataOfAt lvl E senv s = some d) :
    d.shape = s ∧ d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length ≤ d.nIn := by
  unfold dataOfAt at h
  split at h
  · cases h
  · exact dataOfFrom_dims lvl h

theorem dataOfAt_sound_dims (lvl : Lean.Expr → Nat) {E : Lean.ConstantInfo} {senv : StructEnv}
    {s : MachineShape} {d : MachineData} (h : dataOfAt lvl E senv s = some d) :
    (d.shape = s ∧ d.ok = true ∧
      d.shape.body = quote d.dom
        (fun j => inputExpr d.shape.binders.length (d.bpos j))
        (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧
      d.initOk (initsOf d) = true) ∧
    (d.ss.length = s.layout.slots.length ∧ d.ls.length = s.layout.lets ∧ s.insts.length ≤ d.nIn) :=
  ⟨dataOfAt_sound lvl h, (dataOfAt_dims lvl h).2⟩

end Tools.ShippingGen5DataOf
