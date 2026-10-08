import Tools.ShippingMachineDepth
import Tools.ShippingMachineCleanup

/-! # A machine with calls, as a child: its ports

A child that has children of its own is closed by `closeInstsG`: its inputs
are the transition's ports before the slots and `let`s, the clock and the
reset, without the call ports (`MachineWired`'s last clause). This file
reads off what `SeqChildRunN` needs of such a module's ports: distinct input
names, the clock and the reset among them, no output an input, and as many
argument ports as the declaration has non-domain arguments. -/
namespace Tools.ShippingMachineDepthChild
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineCompose (argPorts machPorts_length)
open Sparkle.IR.Machine (OutField outNameOk)

/-- A filter whose predicate holds exactly on the first `N` elements. -/
theorem filter_eq_take {α : Type} (p : α → Bool) :
    ∀ (l : List α) (N : Nat), N ≤ l.length →
      (∀ i (hi : i < l.length), i < N → p l[i] = true) →
      (∀ i (hi : i < l.length), N ≤ i → p l[i] = false) →
      l.filter p = l.take N
  | [], N, _, _, _ => by simp
  | a :: rest, 0, _, _, hfalse => by
    simp only [List.take_zero]
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp [hfalse i hi (Nat.zero_le _)]
  | a :: rest, N + 1, hN, htrue, hfalse => by
    have ha : p a = true := htrue 0 (by simp) (by omega)
    rw [List.filter_cons, if_pos ha, List.take_succ_cons]
    congr 1
    exact filter_eq_take p rest N (by simp at hN; omega)
      (fun i hi hiN => htrue (i + 1) (by simp; omega) (by omega))
      (fun i hi hiN => hfalse (i + 1) (by simp; omega) (by omega))

/-- **The ports of a machine with calls and slots.** -/
theorem calls_ports {declName : Name} {d : MachineData} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName d.shape ids cache m dsn regs lets)
    (len : ids.length = d.shape.binders.length)
    (hfe : d.shape.instFields ≠ []) (hsl : d.shape.layout.slots ≠ [])
    (houtOk : ∀ o ∈ d.shape.layout.outs, outNameOk o.name = true)
    (kD : Nat) (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length) :
    (m.inputs.map (·.name)).Nodup ∧ "clk" ∈ m.inputs.map (·.name) ∧
    "rst" ∈ m.inputs.map (·.name) ∧
    (∀ x ∈ m.outputs.map (·.name), x ∉ m.inputs.map (·.name)) ∧
    (argPorts m).length = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length := by
  obtain ⟨hnd, halloc, -, -, -, -, -, houts, -, -, -, -, -, -, -, -, hcl⟩ := wired
  generalize hNm : (machPorts declName ids cache d.shape.binders).map (·.name) = names
    at hnd halloc hcl
  obtain ⟨outWs, extra, hsub, hsup, hex, hin⟩ := hcl hfe
  have hext : extra = [] := by
    rcases hex with h | ⟨_, h⟩
    · exact h
    · exact absurd h hsl
  subst hext
  have hslE : d.shape.layout.slots.isEmpty = false := by
    cases h : d.shape.layout.slots with
    | nil => exact absurd h hsl
    | cons _ _ => rfl
  rw [hslE] at hin
  simp only [Bool.false_eq_true, if_false, List.append_nil] at hin
  -- the names
  have hnClk : ∀ x ∈ names, x ≠ "clk" := fun x hx h =>
    Tools.ShippingMachineCleanup.not_allocated_clk (h ▸ halloc x hx)
  have hnRst : ∀ x ∈ names, x ≠ "rst" := fun x hx h =>
    Tools.ShippingRegisterSoundness.not_allocated_rst (h ▸ halloc x hx)
  have hOW : ∀ w ∈ outWs, w ∈ names := by
    intro w hw
    obtain ⟨k, _, hk⟩ := hsub w hw
    exact List.mem_of_getElem? hk
  have clkOut : "clk" ∉ outWs := fun h => hnClk _ (hOW _ h) rfl
  have rstOut : "rst" ∉ outWs := fun h => hnRst _ (hOW _ h) rfl
  generalize hK : names.length - d.shape.layout.lets - d.shape.layout.slots.length = K at hin
  have hTnd : (names.take K).Nodup := hnd.sublist (List.take_sublist _ _)
  have hTmem : ∀ x ∈ names.take K, x ∈ names := fun x hx => List.mem_of_mem_take hx
  have hLnd : (names.take K ++ ["clk", "rst"]).Nodup := by
    refine List.nodup_append.mpr ⟨hTnd, by simp, ?_⟩
    intro a ha b hb hab
    subst hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hnClk _ (hTmem _ ha) rfl
    · exact hnRst _ (hTmem _ ha) rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hin]; exact hLnd.filter _
  · rw [hin, List.mem_filter]; exact ⟨by simp, by simpa [List.contains_eq_mem] using clkOut⟩
  · rw [hin, List.mem_filter]; exact ⟨by simp, by simpa [List.contains_eq_mem] using rstOut⟩
  · intro x hx hxi
    rw [houts] at hx
    simp only [List.map_map, List.mem_map, Function.comp] at hx
    obtain ⟨o, ho, rfl⟩ := hx
    have hok := houtOk o ho
    obtain ⟨hna, hnr, _⟩ := Tools.ShippingMachineClose.outNameOk_facts hok
    have hnc : o.name ≠ "clk" := by
      simp only [outNameOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok
      exact hok.2
    rw [hin, List.mem_filter] at hxi
    rcases List.mem_append.mp hxi.1 with h | h
    · exact hna (halloc _ (hTmem _ h))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · exact hnc h
      · exact hnr h
  · -- the argument ports: the declaration's
    have hmapA : (argPorts m).map (·.name) = (m.inputs.map (·.name)).filter
        (fun x => x != "clk" && x != "rst") := by
      unfold argPorts; rw [List.filter_map]; rfl
    have hA : (argPorts m).map (·.name) = (names.take K).filter fun x => !outWs.contains x := by
      rw [hmapA, hin, List.filter_append, List.filter_append]
      have e1 : ((["clk", "rst"].filter fun x => !outWs.contains x).filter
          fun x => x != "clk" && x != "rst") = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        have := (List.mem_filter.mp hx).1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl <;> simp
      rw [e1, List.append_nil]
      apply List.filter_eq_self.mpr
      intro x hx
      have hx' := hTmem x (List.mem_filter.mp hx).1
      simp [hnClk x hx', hnRst x hx']
    -- the lengths
    have hlenB : d.shape.binders.length ≤ ids.length := by omega
    have hNL : names.length = (d.shape.binders.filter fun b => b.2 != .domain).length := by
      rw [← hNm, List.length_map, machPorts_length _ hlenB]
    have hsplit := d.binders_split
    have hSLf : ((d.slotBs ++ d.letBs).filter fun b => b.2 != .domain).length =
        d.slotBs.length + d.letBs.length := by
      rw [List.filter_eq_self.mpr (fun b hb => bne_iff_ne.mpr (hSL b hb)), List.length_append]
    have hKv : K = ((d.bsIn.filter fun b => b.2 != .domain)).length := by
      rw [← hK, hNL, hsplit, List.append_assoc, List.filter_append, List.length_append, hSLf,
        hSlen, hLlen]
      omega
    have hBsplit : (d.bsIn.filter fun b => b.2 != .domain).length =
        ((d.bsIn.take kD).filter fun b => b.2 != .domain).length +
          ((d.bsIn.drop kD).filter fun b => b.2 != .domain).length := by
      conv => lhs; rw [← List.take_append_drop kD d.bsIn]
      rw [List.filter_append, List.length_append]
    have hDrop : ((d.bsIn.drop kD).filter fun b => b.2 != .domain).length ≤ d.shape.insts.length := by
      rw [← hIlen]; exact List.length_filter_le _ _
    generalize hNv : machNIn d.shape = N at hsub hsup
    have hNK : N ≤ K := by rw [hKv, hBsplit, ← hNIn, hNv]; omega
    have hKN : K ≤ N + d.shape.insts.length := by rw [hKv, hBsplit, ← hNIn, hNv]; omega
    have hKlen : K ≤ names.length := by rw [← hK]; omega
    have htk : (names.take K).length = K := by simp; omega
    have hfeq : (names.take K).filter (fun x => !outWs.contains x) = (names.take K).take N := by
      apply filter_eq_take _ _ N (by rw [htk]; exact hNK)
      · intro i hi hiN
        simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
        intro hmem
        obtain ⟨k, _, hk⟩ := hsub _ hmem
        have hi' : i < names.length := by rw [htk] at hi; omega
        have hkl : N + k < names.length := (List.getElem?_eq_some_iff.mp hk).1
        have hik : names[N + k]? = names[i]? := by
          rw [hk, List.getElem?_eq_getElem hi', List.getElem_take]
        have := (List.getElem?_inj hkl hnd).mp hik
        omega
      · intro i hi hiN
        simp only [Bool.not_eq_false', List.contains_eq_mem, decide_eq_true_eq]
        have hik : i - N < d.shape.insts.length := by rw [htk] at hi; omega
        obtain ⟨w, hw, hwo⟩ := hsup (i - N) hik
        rw [show N + (i - N) = i by omega] at hw
        rw [List.getElem_take]
        have : names[i]'(by rw [htk] at hi; omega) = w := by
          have := List.getElem?_eq_some_iff.mp hw
          exact this.2
        rw [this]; exact hwo
    have := congrArg List.length hA
    rw [List.length_map, hfeq, List.length_take, htk] at this
    rw [this, ← hNIn, hNv]
    omega

end Tools.ShippingMachineDepthChild
