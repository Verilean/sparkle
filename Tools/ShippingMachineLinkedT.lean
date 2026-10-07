import Tools.ShippingMachineComposedT
import Tools.ShippingMachineCompose
import Tools.ShippingMachineInstG

/-! # A machine with structure / sequential / memory calls, composed

`machine_linked` (ShippingMachineCompose) composes a machine with
combinational one-output children (`closeInsts`). Here the calls are tied by
`closeInstsG` (several outputs per instance, sequential children, memories)
and the composition is the STATEFUL linked run (`runModuleT`): seeded with
the declaration's own inputs only, it shows the source, provided every
instance's child, run on any environments whose argument wires carry the
source's argument values and whose output wires carry the source's call
values, shows those output values. -/
namespace Tools.ShippingMachineLinkedT
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingMachineLinked
open Tools.ShippingHierState Tools.ShippingMachineCompose
open Tools.ShippingEntrySoundness (weOf)

/-- The connections of a call group's instance statement (`CallStmtG`). -/
def connsG (mc : Module) (argWs : List String) (outs : List (Nat × String))
    (outWs : List String) : List (String × Expr) :=
  ((mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").zip argWs).map
      (fun (p, w) => (p.name, Expr.ref w)) ++
    (if mc.inputs.any (fun p => p.name == "clk" || p.name == "rst") then
      [("clk", Expr.ref "clk"), ("rst", Expr.ref "rst")] else []) ++
    ((outs.map (·.2)).zip outWs).map (fun (f, w) => (f, Expr.ref w))

theorem lookup_append_skip {L M : List (String × Expr)} {k : String}
    (h : ∀ c ∈ L, c.1 ≠ k) : (L ++ M).lookup k = M.lookup k := by
  induction L with
  | nil => rfl
  | cons c rest ih =>
    have hc : (k == c.1) = false := by
      rw [beq_eq_false_iff_ne]; exact fun he => h c List.mem_cons_self he.symm
    simp only [List.cons_append, List.lookup, hc]
    exact ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

theorem lookup_zipmap : ∀ (fs ws : List String) (k w : String), fs.Nodup → (k, w) ∈ fs.zip ws →
    ((fs.zip ws).map (fun (f, w) => (f, Expr.ref w))).lookup k = some (.ref w)
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | f :: fs, x :: ws, k, w, hnd, h => by
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    simp only [List.zip_cons_cons, List.map_cons, List.lookup]
    rcases h with ⟨rfl, rfl⟩ | h
    · simp
    · have hk : k ≠ f := by
        intro he; subst he
        exact (List.nodup_cons.mp hnd).1 (List.of_mem_zip h).1
      have hb : (k == f) = false := beq_eq_false_iff_ne.mpr hk
      simp only [hb]
      exact lookup_zipmap fs ws k w (List.nodup_cons.mp hnd).2 h

/-- An output field's wire is one of the instance's output wires. -/
theorem connsG_out {mc : Module} {argWs : List String} {outs : List (Nat × String)}
    {outWs : List String} {f w : String}
    (hf : mc.outputs.any (·.name == f) = true) (hfnd : (outs.map (·.2)).Nodup)
    (hdisj : (mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").any (·.name == f) = false)
    (hclk : f ≠ "clk") (hrst : f ≠ "rst")
    (hmem : (f, w) ∈ (outs.map (·.2)).zip outWs) :
    w ∈ Tools.ShippingHierOpen.instOutWires mc.outputs (connsG mc argWs outs outWs) := by
  have hlk : (connsG mc argWs outs outWs).lookup f = some (.ref w) := by
    unfold connsG
    rw [lookup_append_skip, lookup_zipmap _ _ _ _ hfnd hmem]
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨⟨p, w'⟩, hpw, rfl⟩ := List.mem_map.mp hc
      have hp := (List.of_mem_zip hpw).1
      intro he
      have : (mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").any (·.name == f) =
          true := List.any_eq_true.mpr ⟨p, hp, by simpa using he⟩
      rw [hdisj] at this; cases this
    · split at hc
      · simp at hc; rcases hc with rfl | rfl
        · exact Ne.symm hclk
        · exact Ne.symm hrst
      · cases hc
  obtain ⟨p, hp, hpf⟩ := List.any_eq_true.mp hf
  have hpf' : p.name = f := by simpa using hpf
  unfold Tools.ShippingHierOpen.instOutWires
  apply List.mem_filterMap.mpr
  exact ⟨p, hp, by rw [hpf', hlk]⟩

end Tools.ShippingMachineLinkedT
