import Tools.ShippingInstStmt
import Sparkle.IR.MachineInstG

/-! # The instance statement of a call group (several outputs, sequential children)

`instStmtG` returns ONE instance for a call group — the entries reading the
fields of one call: the child's non-clock input ports connected to the
argument wires in order, `clk` / `rst` for a sequential child, and each read
field's output port to that entry's wire. Here: that statement, explicitly,
from the fitting facts (`instStmtG_some`). Pure; the facts are to be derived
from the parent's and the child's runs. -/
namespace Tools.ShippingInstStmtG
open Sparkle.IR.AST Sparkle.IR.Machine

/-- The child's input ports the arguments are connected to. -/
def inPortsOf (mc : Module) : List Port :=
  mc.inputs.filter fun p => p.name != "clk" && p.name != "rst"

/-- A child with a clock or a reset input. -/
def isSeqChild (mc : Module) : Bool :=
  mc.inputs.any fun p => p.name == "clk" || p.name == "rst"

/-- The connections of a call group's instance. -/
def callConnsG (ins : List Port) (argWs : List String) (seq : Bool) (fields outWs : List String) :
    List (String × Expr) :=
  (ins.zip argWs).map (fun (x : Port × String) => (x.1.name, Expr.ref x.2)) ++
    (if seq then [("clk", Expr.ref "clk"), ("rst", Expr.ref "rst")] else []) ++
    (fields.zip outWs).map (fun (x : String × String) => (x.1, Expr.ref x.2))

/-- **`instStmtG` on a fitting child.** -/
theorem instStmtG_some {nIn kI n gi : Nat} {portNames : List String} {args : List Nat}
    {outs : List (Nat × String)} {mc m : Module} {outWs argWs : List String}
    (hout : outs.mapM (fun (k, _) => portNames[nIn + k]?) = some outWs)
    (hargs : args.mapM (fun j => portNames[nIn + kI + n + j]?) = some argWs)
    (hlen : (inPortsOf mc).length = argWs.length)
    (hnd : ((inPortsOf mc).map (·.name)).Nodup)
    (hfo : ∀ f ∈ outs.map (·.2), ∃ p ∈ mc.outputs, p.name = f)
    (hfnd : (outs.map (·.2)).Nodup)
    (hfin : ∀ f ∈ outs.map (·.2), (∀ p ∈ inPortsOf mc, p.name ≠ f) ∧ f ≠ "clk" ∧ f ≠ "rst")
    (hne : ∀ w ∈ outWs, w ∉ argWs) (hond : outWs.Nodup)
    (hwire : ∀ w ∈ outWs, ∃ p ∈ m.wires, p.name = w)
    (hclk : isSeqChild mc = true →
      (∃ p ∈ m.inputs, p.name = "clk") ∧ ∃ p ∈ m.inputs, p.name = "rst")
    (hfresh : s!"inst{gi}_{mc.name}" ∉
      m.inputs.map (·.name) ++ m.outputs.map (·.name) ++ m.wires.map (·.name)) :
    instStmtG nIn kI n portNames gi args outs mc m =
      some (.inst mc.name s!"inst{gi}_{mc.name}"
        (callConnsG (inPortsOf mc) argWs (isSeqChild mc) (outs.map (·.2)) outWs)) := by
  have h1 : (outs.map (·.2)).all (fun f => mc.outputs.any (·.name == f)) = true := by
    rw [List.all_eq_true]
    intro f hf
    obtain ⟨p, hp, he⟩ := hfo f hf
    exact List.any_eq_true.mpr ⟨p, hp, by simpa using he⟩
  have h2 : (outs.map (·.2)).any (fun f => (inPortsOf mc).any (·.name == f)) = false := by
    rw [List.any_eq_false]
    intro f hf
    rw [Bool.not_eq_true, List.any_eq_false]
    intro p hp
    simpa using (hfin f hf).1 p hp
  have h3 : (outs.map (·.2)).contains "clk" = false := by
    have : "clk" ∉ outs.map (·.2) := fun hc => (hfin _ hc).2.1 rfl
    simpa using this
  have h4 : (outs.map (·.2)).contains "rst" = false := by
    have : "rst" ∉ outs.map (·.2) := fun hc => (hfin _ hc).2.2 rfl
    simpa using this
  have h5 : outWs.any (fun w => argWs.contains w) = false := by
    rw [List.any_eq_false]
    intro w hw
    simpa using hne w hw
  have h6 : outWs.all (fun w => m.wires.any (·.name == w)) = true := by
    rw [List.all_eq_true]
    intro w hw
    obtain ⟨p, hp, he⟩ := hwire w hw
    exact List.any_eq_true.mpr ⟨p, hp, by simpa using he⟩
  have h7 : (isSeqChild mc && !(m.inputs.any (·.name == "clk") && m.inputs.any (·.name == "rst"))) =
      false := by
    cases hs : isSeqChild mc with
    | false => rfl
    | true =>
      obtain ⟨⟨p, hp, he⟩, ⟨q, hq, hqe⟩⟩ := hclk hs
      have a1 : m.inputs.any (·.name == "clk") = true :=
        List.any_eq_true.mpr ⟨p, hp, by simpa using he⟩
      have a2 : m.inputs.any (·.name == "rst") = true :=
        List.any_eq_true.mpr ⟨q, hq, by simpa using hqe⟩
      simp [a1, a2]
  have h8 : (m.inputs.map (·.name) ++ m.outputs.map (·.name) ++ m.wires.map (·.name)).contains
      s!"inst{gi}_{mc.name}" = false := by
    simpa using hfresh
  unfold instStmtG
  simp only [Option.bind_eq_bind, hout, hargs, Option.bind_some]
  change (if ((inPortsOf mc).length != argWs.length) = true then none else _) = _
  simp only [hlen, bne_self_eq_false, Bool.false_eq_true, if_false]
  change (if (!decide ((inPortsOf mc).map (·.name)).Nodup) = true then none else _) = _
  simp only [hnd, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
  change (if (!(outs.map (·.2)).all (fun f => mc.outputs.any (·.name == f)) ||
      !decide (outs.map (·.2)).Nodup) = true then none else _) = _
  simp only [h1, hfnd, decide_true, Bool.not_true, Bool.or_self, Bool.false_eq_true, if_false]
  change (if ((outs.map (·.2)).any (fun f => (inPortsOf mc).any (·.name == f)) ||
      (outs.map (·.2)).contains "clk" || (outs.map (·.2)).contains "rst") = true then none else _) = _
  simp only [h2, h3, h4, Bool.or_self, Bool.false_eq_true, if_false]
  change (if (outWs.any (fun w => argWs.contains w) || !decide outWs.Nodup) = true then none
    else _) = _
  simp only [h5, hond, decide_true, Bool.not_true, Bool.or_self, Bool.false_eq_true, if_false]
  change (if (!outWs.all (fun w => m.wires.any (·.name == w))) = true then none else _) = _
  simp only [h6, Bool.not_true, Bool.false_eq_true, if_false]
  change (if (isSeqChild mc &&
      !(m.inputs.any (·.name == "clk") && m.inputs.any (·.name == "rst"))) = true then none
    else _) = _
  simp only [h7, Bool.false_eq_true, if_false]
  change (if (m.inputs.map (·.name) ++ m.outputs.map (·.name) ++ m.wires.map (·.name)).contains
      s!"inst{gi}_{mc.name}" = true then none else _) = _
  simp only [h8, Bool.false_eq_true, if_false]
  rfl

end Tools.ShippingInstStmtG
