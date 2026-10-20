import Tools.ShippingSVBridge
import Tools.ShippingDesignSVLeaf

/-! # The two width tables agree on declared wires (G1, `designCheck` conjunct 3)

`Sparkle.IR.RegDedup.declWidth m x` reads `m.wires` by RAW name (0 for a
name that is not a wire, ports included). The emitter's
`Tools.SVParser.RoundtripProof.moduleWof m x` reads
`m.wires ++ m.inputs ++ m.outputs` by SANITIZED name, and
`weOf (moduleWof m) x` is its `getD 0`. Pure facts, no run:

* `declWidth_eq_weS`: on a WIRE `x` of a module whose wire names are
  sanitize-stable the two agree (the first match of the emitter's lookup is
  the wire itself; the type cases coincide: `bitVector k ↦ k`, `bit ↦ 1`,
  anything else `0`). No duplicate-freeness is needed: both lookups take the
  FIRST wire of that name.
* `moduleWof_wire`: such a wire of scalar type is DECLARED in the emitter's
  map (`moduleWof m x = some _`).
* `seqNames_widths`: conjunct 3 of `textCheckI` — the tables agree on
  `seqNames m.body` — when every name of `seqNames m.body` is a wire.

A name that is NOT a wire (a port that is not also declared as a wire) has
`declWidth = 0` and the port's width in the emitter's map: there the two
tables differ, so "read names are wires" is a real hypothesis.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingWidthTables
open Sparkle.IR.AST

theorem wire_find {m : Sparkle.IR.AST.Module} {x : String}
    (hx : x ∈ m.wires.map (·.name)) :
    ∃ p, m.wires.find? (fun p => p.name == x) = some p := by
  cases hf : m.wires.find? (fun p => p.name == x) with
  | some p => exact ⟨p, rfl⟩
  | none =>
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hx
    have hqn' : q.name = x := hqn
    have hb : (q.name == x) = true := beq_iff_eq.mpr hqn'
    exact absurd hb (List.find?_eq_none.mp hf q hq)

/-- **The width tables agree on a wire** of a module with sanitize-stable
wire names. -/
theorem declWidth_eq_weS {m : Sparkle.IR.AST.Module} {x : String}
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hx : x ∈ m.wires.map (·.name)) :
    Sparkle.IR.RegDedup.declWidth m x =
      Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof m) x := by
  obtain ⟨p, hf⟩ := wire_find hx
  simp only [Sparkle.IR.RegDedup.declWidth, Tools.SVParser.EmitSem.weOf,
    Tools.SVParser.RoundtripProof.moduleWof]
  rw [List.find?_append, List.find?_append, Tools.ShippingSVBridge.find_sanitized m.wires x hs, hf]
  obtain ⟨pn, pty⟩ := p
  cases pty <;> simp_all

/-- **A scalar wire is declared in the emitter's width map.** -/
theorem moduleWof_wire {m : Sparkle.IR.AST.Module} {x : String}
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hty : ∀ p ∈ m.wires, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n)
    (hx : x ∈ m.wires.map (·.name)) :
    ∃ k, Tools.SVParser.RoundtripProof.moduleWof m x = some k := by
  obtain ⟨p, hf⟩ := wire_find hx
  have hp := List.mem_of_find?_eq_some hf
  simp only [Tools.SVParser.RoundtripProof.moduleWof]
  rw [List.find?_append, List.find?_append, Tools.ShippingSVBridge.find_sanitized m.wires x hs, hf]
  rcases hty p hp with h | ⟨n, h⟩
  · exact ⟨1, by simp [h]⟩
  · exact ⟨n, by simp [h]⟩

/-- **Conjunct 3 of `textCheckI`**: the tables agree on the names the body
uses, when those are wires with sanitize-stable names. -/
theorem seqNames_widths {m : Sparkle.IR.AST.Module}
    (hs : ∀ p ∈ m.wires, Sparkle.Backend.Verilog.sanitizeName p.name = p.name)
    (hsub : ∀ x ∈ Tools.ShippingSeqSVSoundness.seqNames m.body, x ∈ m.wires.map (·.name)) :
    (Tools.ShippingSeqSVSoundness.seqNames m.body).all
      (fun x => Sparkle.IR.RegDedup.declWidth m x == Tools.ShippingDesignSV.weS m x) = true := by
  rw [List.all_eq_true]
  intro x hx
  exact beq_iff_eq.mpr (declWidth_eq_weS hs (hsub x hx))

end Tools.ShippingWidthTables
