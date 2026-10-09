import Tools.ShippingDesignSVLeaf
import Sparkle.Compiler.MachMemory
import Tools.ShippingDesignSVBack

/-! # The built memory module is a checked leaf, for every parameter

`memModule cb aw dw` — the module every memory call of a machine-route body
instantiates (`MachineWired` / `find_memModule`) — passes `leafCheck` and
`outsLeaf` for EVERY read kind and widths: its text runs as `LeafRun`
(combinational reads a `.reads` step, synchronous reads with the read latch),
its IR run is that run both ways (`leaf_forward` / `leaf_backward`), its steps
stay within the emitted widths (`leaf_stepBound`), and its output — assigned
from the read data — is within its width in any run of the text
(`leaf_outs`), whatever the memory holds. -/
namespace Tools.ShippingDesignSV
open Sparkle.IR.AST Sparkle.IR.Semantics Tools.ShippingMemSVSoundness

private theorem san_ra : Sparkle.Backend.Verilog.sanitizeName "ra" = "ra" := by
  simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
private theorem san_wa : Sparkle.Backend.Verilog.sanitizeName "wa" = "wa" := by
  simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
private theorem san_wd : Sparkle.Backend.Verilog.sanitizeName "wd" = "wd" := by
  simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
private theorem san_we : Sparkle.Backend.Verilog.sanitizeName "we" = "we" := by
  simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
private theorem san_out : Sparkle.Backend.Verilog.sanitizeName "out" = "out" := by
  simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
private theorem san_out_rdata : Sparkle.Backend.Verilog.sanitizeName "out_rdata" = "out_rdata" := by
  simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
private theorem san_clk : Sparkle.Backend.Verilog.sanitizeName "clk" = "clk" := by
  simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]
private theorem san_rst : Sparkle.Backend.Verilog.sanitizeName "rst" = "rst" := by
  simp [Sparkle.Backend.Verilog.sanitizeName, String.all_bool_eq]

set_option maxHeartbeats 2000000 in
/-- **The memory module is a checked leaf**, for every read kind and widths. -/
theorem leafCheck_memModule (cb : Bool) (aw dw : Nat) :
    leafCheck (Sparkle.Compiler.MachMemory.memModule cb aw dw).1 = true := by
  cases cb <;>
  simp (config := {decide := true}) [leafCheck, Sparkle.Compiler.MachMemory.memModule, seqStmtOkA,
    memOpsRefs, leafNames, wRefs, hasSyncMem, seqCheckM, Tools.SVParser.EmitSem.seqCheck,
    Tools.SVParser.RoundtripProof.moduleWof, Tools.SVParser.EmitSem.weOf,
    Sparkle.IR.RegDedup.declWidth, wofOf, weS, Tools.SVParser.EmitSem.sf4Check,
    Sparkle.IR.Semantics.widthOf, Tools.SVParser.EmitSem.payloadCheckC,
    Tools.SVParser.EmitSem.payloadCheck, Sparkle.IR.Semantics.extractReads, isRefE,
    Tools.SVParser.EmitAst.emitAstExpr, Tools.SVParser.EmitSem.extractReadsSV,
    Tools.SVParser.EmitSem.eqSV, Tools.SVParser.EmitSem.readPortsCheck,
    Tools.SVParser.EmitSem.portCheck, Sparkle.IR.Semantics.weWithReads,
    Tools.SVParser.EmitSem.wofWithReads, san_ra, san_wa, san_wd, san_we, san_out,
    san_out_rdata, san_clk, san_rst]

/-- **The memory module's output is written** (assigned from the read data),
for every read kind and widths. -/
theorem outsLeaf_memModule (cb : Bool) (aw dw : Nat) :
    outsLeaf (Sparkle.Compiler.MachMemory.memModule cb aw dw).1 = true := by
  simp [outsLeaf, Sparkle.Compiler.MachMemory.memModule]

/-- Every instance of the body resolves to a built memory module. -/
def MemKids (C : String → Option (Module × WEnv)) (body : List Stmt) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
    ∃ cb aw dw cwe, C mn = some ((Sparkle.Compiler.MachMemory.memModule cb aw dw).1, cwe)

theorem kidsPass_memKids {C : String → Option (Module × WEnv)} {f : Module → Bool}
    (hf : ∀ cb aw dw, f (Sparkle.Compiler.MachMemory.memModule cb aw dw).1 = true) :
    ∀ {body : List Stmt}, MemKids C body → kidsPass C f body = true := by
  intro body hk
  simp only [kidsPass, List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    obtain ⟨cb, aw, dw, cwe, hc⟩ := hk mn iname conns hst
    show (match C mn with | some (child, _) => f child | none => false) = true
    rw [hc]; exact hf cb aw dw
  | _ => rfl

/-- **A memory parent's design checks**: when every instance is a built
memory module, `designCheck 0` is the parent's own text check, and
`outsCheck 0` holds — for every read kind and widths of the memories. -/
theorem designCheck_memKids {C : String → Option (Module × WEnv)} {o : Module}
    (ht : textCheckI C o = true) (hk : MemKids C o.body) :
    designCheck C 0 o = true ∧ Tools.ShippingDesignSVBack.outsCheck C 0 o = true := by
  refine ⟨?_, kidsPass_memKids outsLeaf_memModule hk⟩
  simp only [designCheck, Bool.and_eq_true]
  exact ⟨ht, kidsPass_memKids leafCheck_memModule hk⟩

end Tools.ShippingDesignSV
