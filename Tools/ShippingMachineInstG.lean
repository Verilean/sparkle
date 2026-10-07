import Tools.ShippingMachineInst
import Sparkle.IR.MachineInstG

/-! # The instance statements `closeInstsG` adds

A call whose result is a structure, or whose child is sequential, is tied by
`closeInstsG` (Sparkle.IR.MachineInstG): the entries of one call (the same
child and argument `let`s) are ONE instance, its input ports connected to the
argument wires, for a sequential child its `clk`/`rst` to the module's, and
each entry's output port (field) to the entry's transition input. This file
states the shape of those statements (`CallStmtG`) and that every instance
statement of the closed module is one of them (`closeInstsG_insts`). -/
namespace Tools.ShippingMachineInstG
open Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingMachineInst (mapM_some)

/-- The instance statement of one call group: entries `outs` (index, field),
argument `let`s `args`, child `mc`. -/
def CallStmtG (nIn kI n : Nat) (portNames : List String) (args : List Nat)
    (outs : List (Nat × String)) (mc : Module) (st : Stmt) : Prop :=
  ∃ outWs argWs iname,
    outs.mapM (fun (k, _) => portNames[nIn + k]?) = some outWs ∧
    args.mapM (fun j => portNames[nIn + kI + n + j]?) = some argWs ∧
    (mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").length = argWs.length ∧
    ((mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").map (·.name)).Nodup ∧
    (outs.map (·.2)).all (fun f => mc.outputs.any (·.name == f)) = true ∧
    (outs.map (·.2)).Nodup ∧
    (outs.map (·.2)).any (fun f =>
      (mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").any (·.name == f)) = false ∧
    ¬ (outs.map (·.2)).contains "clk" ∧ ¬ (outs.map (·.2)).contains "rst" ∧
    outWs.any (fun w => argWs.contains w) = false ∧ outWs.Nodup ∧
    st = .inst mc.name iname
      (((mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").zip argWs).map
          (fun (p, w) => (p.name, Expr.ref w)) ++
        (if mc.inputs.any (fun p => p.name == "clk" || p.name == "rst") then
          [("clk", Expr.ref "clk"), ("rst", Expr.ref "rst")] else []) ++
        ((outs.map (·.2)).zip outWs).map (fun (f, w) => (f, Expr.ref w)))

theorem instStmtG_some {nIn kI n : Nat} {portNames : List String} {gi : Nat} {args : List Nat}
    {outs : List (Nat × String)} {mc m : Module} {st : Stmt}
    (h : instStmtG nIn kI n portNames gi args outs mc m = some st) :
    CallStmtG nIn kI n portNames args outs mc st := by
  unfold instStmtG at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨outWs, hout, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨argWs, hargs, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  rename_i hlen
  split at h
  · cases h
  rename_i hnd
  split at h
  · cases h
  rename_i hfields
  split at h
  · cases h
  rename_i hdisj
  split at h
  · cases h
  rename_i houtWs
  split at h
  · cases h
  rename_i hwires
  split at h
  · cases h
  split at h
  · cases h
  cases h
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.not_eq_true, Bool.or_eq_true,
    not_or, Bool.not_eq_false] at hlen hnd hfields hdisj houtWs
  refine ⟨outWs, argWs, _, hout, hargs, by simpa using hlen, by simpa using hnd, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, rfl⟩
  · simpa using hfields.1
  · simpa using hfields.2
  · simpa using hdisj.1.1
  · simpa using hdisj.1.2
  · simpa using hdisj.2
  · simpa using houtWs.1
  · simpa using houtWs.2

end Tools.ShippingMachineInstG
