import Tools.ShippingFGCircuitS3vChild
set_option autoImplicit false
-- FG circuit pilot S3y, steps 1-2: the first GENERAL connection.  `checkData_sound`: for ANY `MachineData d` of the combinational sub-language (`circOk`) and ANY module `m`, a successful `checkData d m` (the ports `portsOk`, the source terms `ofData d`, the validator `checkComb`) gives `DataShows d m`: `ChildFn m (childRange d) (dataValue d x)`, where `dataValue` is defined from `d` ALONE (`letTV` / `Term.eval` on `d.outs`, at the `decB`/`decV` decoding of the argument values), never from a module.  The per-declaration side facts of `k0_childFn` (port count, widths, `portIdx`, output count, fragment) are Bool checks inside `circOk`/`portsOk`; `k0_childFn'` re-derives `k0_childFn` from it.  No run premise, no Laws/CellPrem/hr.  No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §73.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3yGen
open Tools.ShippingFGCircuitS3tComb Tools.ShippingFGCircuitS3tCombRun Tools.ShippingFGCircuitS3vBridge
open Tools.ShippingUnifiedSource Tools.ShippingMachineAuto Tools.ShippingMachineDenote
open Tools.ShippingMachineCompose (ChildFn argPorts)
open Tools.ShippingMachineChild (childValue childRange decB decV portIdx InRange inRange_get)
open Sparkle.Core (HList)
open Sparkle.IR.AST (Module Port)
open Sparkle.Compiler.Elab (MixedGateBinder)

/-- the bit width of a port binder (a domain binder has no port: 0) -/
def binderW : MixedGateBinder → Nat
  | .bool => 1
  | .bits n => n
  | .domain => 0

/-- **the data's own meaning** of its first output on the argument values `vals`: the value `Term.eval` gives the output term under the typed valuation `letTV` (the `let`s evaluated in order) at the decoding `decB`/`decV` of `vals`, encoded.  Defined from `d` (and the state `x`, unique for a stateless `d`) ALONE: no module, no `ofData`, no `CTerm`. -/
def dataValue (d : MachineData) (x : HList (tys d.ss)) (vals : List Nat) : Nat :=
  match d.outs[0]? with
  | none => 0
  | some o =>
    enc o.1 (eval (fun j => (letTV d x (decB d.bsIn vals) (decV d.bsIn vals)).b (d.bpos j))
      (fun j w => (letTV d x (decB d.bsIn vals) (decV d.bsIn vals)).v (d.vpos j) w) o.2)

/-- **the data-level claim**: for every state value, on the argument values in the data's input range, the module's IR output is the data's own value -/
def DataShows (d : MachineData) (m : Module) : Prop :=
  ∀ x : HList (tys d.ss), ChildFn m (childRange d) (dataValue d x)

/-- the combinational sub-language: no state, one output, every `let` and the output in `Frag` -/
def circOk (d : MachineData) : Bool :=
  d.ss.isEmpty && (d.outs.length == 1) && d.ls.all (fun l => Frag d l.2) && d.outs.all (fun o => Frag d o.2)

/-- the module's ports against the data's input binders: as many ports as hardware binders, none of them `clk`/`rst`, each at its binder's width, the source position of port `i` has port index `i`, one output -/
def portsOk (d : MachineData) (m : Module) : Bool :=
  let bs := d.bsIn.filter (fun b => b.2 != .domain)
  (m.inputs.length == bs.length) &&
  m.inputs.all (fun p => p.name != "clk" && p.name != "rst") &&
  (m.inputs.zip bs).all (fun (p, b) => portW p == binderW b.2) &&
  ((inputPositions d).length == bs.length) &&
  (List.range (inputPositions d).length).all (fun i => portIdx d.bsIn ((inputPositions d).getD i 0) == i) &&
  (m.outputs.length == 1)

/-- **the general checker on (data, module)**: no root-specific constant -/
def checkData (d : MachineData) (m : Module) : Bool :=
  circOk d && portsOk d m && (match ofData d with | some s => checkComb s m | none => false)

/-- what `portsOk` says, as propositions -/
theorem portsOk_spec (d : MachineData) (m : Module) (h : portsOk d m = true) :
    m.inputs.length = (d.bsIn.filter (fun b => b.2 != .domain)).length ∧
    (∀ p ∈ m.inputs, p.name ≠ "clk" ∧ p.name ≠ "rst") ∧
    (∀ (i : Nat) (p : Port) (b : Lean.Name × MixedGateBinder),
      m.inputs[i]? = some p → (d.bsIn.filter (fun b => b.2 != .domain))[i]? = some b → portW p = binderW b.2) ∧
    (inputPositions d).length = (d.bsIn.filter (fun b => b.2 != .domain)).length ∧
    (∀ (i q : Nat), (inputPositions d)[i]? = some q → portIdx d.bsIn q = i) ∧
    m.outputs.length = 1 := by
  unfold portsOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, ?_, ?_, h4, ?_, h6⟩
  · intro p hp
    have := List.all_eq_true.mp h2 p hp
    simpa using this
  · intro i p b hp hb
    have hz : (m.inputs.zip (d.bsIn.filter (fun b => b.2 != .domain)))[i]? = some (p, b) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hp, hb⟩
    have := List.all_eq_true.mp h3 (p, b) (List.mem_of_getElem? hz)
    simpa using this
  · intro i q hq
    have hi : i < (inputPositions d).length := (List.getElem?_eq_some_iff.mp hq).1
    have := List.all_eq_true.mp h5 i (List.mem_range.mpr hi)
    have hg : (inputPositions d).getD i 0 = q := by
      simp [List.getD_eq_getElem?_getD, hq]
    rw [hg] at this
    simpa using this

/-- **G1, the general validator soundness**: for every data `d` and module `m`, `checkData d m = true` gives `DataShows d m`.  General in `d` and `m`; no run, no law. -/
theorem checkData_sound (d : MachineData) (m : Module) (h : checkData d m = true) : DataShows d m := by
  intro x
  unfold checkData at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hc, hp⟩, h3⟩ := h
  obtain ⟨s, hs, hck⟩ : ∃ s, ofData d = some s ∧ checkComb s m = true := by
    split at h3
    · rename_i s hs; exact ⟨s, hs, h3⟩
    · cases h3
  unfold circOk at hc
  simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hc
  obtain ⟨⟨⟨hss0, hout1⟩, hfl⟩, hfo⟩ := hc
  have hss : d.ss.length = 0 := by rw [hss0]; rfl
  obtain ⟨hnin, hnoclk, hw, hipl, hidx, hnout⟩ := portsOk_spec d m hp
  obtain ⟨outP, hout⟩ := List.length_eq_one_iff.mp hnout
  refine ⟨outP, hout, ?_⟩
  intro mems env hrst hP
  have hargs : argPorts m = m.inputs := by
    unfold argPorts
    apply List.filter_eq_self.mpr
    intro p hp'
    have := hnoclk p hp'
    simp [this.1, this.2]
  obtain ⟨vals, hvals⟩ : ∃ vals : List Nat, vals = (argPorts m).map (fun p => env p.name) := ⟨_, rfl⟩
  rw [← hvals] at hP ⊢
  have hvlen : vals.length = m.inputs.length := by rw [hvals, hargs]; simp
  have hvget : ∀ (i : Nat) (p : Port), m.inputs[i]? = some p → vals.getD i 0 = env p.name := by
    intro i p hi
    rw [hvals, hargs, List.getD_eq_getElem?_getD]
    simp [List.getElem?_map, hi]
  let V : Nat → Nat := fun q => vals.getD (portIdx d.bsIn q) 0
  have hW : ∀ p w, p < d.nIn → ((decV d.bsIn vals p w).toNat) = V p % 2 ^ w := by
    intro p w _
    simp [decV, V]
  have hsound := ofData_sound d hss V x (decB d.bsIn vals) (decV d.bsIn vals) hW
    (by simpa using hfl) (by simpa using hfo) s hs
  obtain ⟨hinPos, hlen, hrel⟩ := hsound
  obtain ⟨env', he, hov⟩ := checkComb_sound s m hck V mems env (by
    intro i p q hi hq
    rw [hinPos] at hq
    have hidxq := hidx i q hq
    have hbs : (d.bsIn.filter (fun b => b.2 != .domain))[i]? ≠ none := by
      intro hn
      have := (List.getElem?_eq_none_iff.mp hn)
      have := (List.getElem?_eq_some_iff.mp hi).1
      omega
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hbs
    have hpw := hw i p b hi hb
    have hbmem := List.mem_of_getElem? hb
    have hbnd : b.2 != .domain := (List.mem_filter.mp hbmem).2
    have hrng := inRange_get hP i b (by rw [childRange] at hP; exact hb)
    have hvi : vals.getD i 0 = env p.name := hvget i p hi
    have hvi' : vals[i]?.getD 0 = env p.name := by rw [← List.getD_eq_getElem?_getD]; exact hvi
    show env p.name = vals.getD (portIdx d.bsIn q) 0 % 2 ^ portW p
    rw [hidxq, hvi]
    symm
    apply Nat.mod_eq_of_lt
    rw [hpw]
    rcases b with ⟨nm, k⟩
    simp only [] at hrng
    cases k with
    | bool => simpa [binderW, hvi'] using hrng
    | bits n => simpa [binderW, hvi'] using hrng
    | domain => simp at hbnd)
  refine ⟨env', he, ?_⟩
  have hslen : s.outs.length = 1 := by rw [hlen]; simpa using hout1
  obtain ⟨c0, hc0⟩ := List.length_eq_one_iff.mp hslen
  obtain ⟨o0, ho0⟩ := List.length_eq_one_iff.mp (by simpa using hout1 : d.outs.length = 1)
  have h1 := hov 0 outP c0 (by simp [hout]) (by simp [hc0])
  have h2 := hrel 0 o0 c0 (by simp [ho0]) (by simp [hc0])
  rw [h1, h2.1]
  simp [dataValue, ho0]

end Tools.ShippingFGCircuitS3yGen
