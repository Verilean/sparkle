import Tools.ShippingSeqSVSoundness
import Tools.ShippingMemSVSoundness

/-! # S7-2: the sequential post-pipeline, composed

For a sequential module `m` the shipping pipeline runs
`optimizeModule` (checked by `seqOptCheck`), prints the result, and the
corpus validation parses the bytes back. The three transfer theorems —
checker (`seqOptCheck_transfer`), emitted-SV semantics
(`seq_run_to_sv`) and parsed-back text (`seq_run_to_parsed`) — are
each family-agnostic; this file composes them into ONE statement: from
one canonical-seed run of `m`, under the pipeline's decidable premises,
the optimized module, its emitted Verilog and the module parsed back
from the printed bytes all run to the SAME trace. -/

namespace Tools.ShippingPipelineSoundness

open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck
open Tools.ShippingSeqOptSoundness Tools.ShippingSeqSVSoundness

open Sparkle.IR.RegDedup (declWidth) in
/-- **The composed sequential pipeline transfer.** One canonical-seed
run of the checked module carries, in one step, to the optimized
module, to its emitted SV semantics, and to the module the shipping
parser reads back from the printed bytes — all with the SAME trace. -/
theorem shipping_pipeline_transfer {m o : Module}
    {body' bimg : List Stmt} {wof : String → Option Nat}
    -- checker premises
    (hchk : seqOptCheck m o = true) (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    (hrstIn : "rst" ∈ m.inputs.map (·.name))
    (hrstZ : ∀ t, ins t "rst" = 0)
    -- emitted-SV premises
    (hsv : Tools.SVParser.EmitSem.seqCheck wof
      (Tools.SVParser.EmitSem.weOf wof) o.body = true)
    (hwagE : ∀ n ∈ seqNames o.body,
      declWidth o n = Tools.SVParser.EmitSem.weOf wof n)
    -- parsed-bytes premises
    (hok' : body'.all seqStmtOk = true)
    (hcert : Tools.SVParser.RoundtripProof.semFragCheck o = true)
    (hI : Tools.SVParser.RoundtripProof.bodyImage
      (Tools.SVParser.RoundtripProof.moduleWof o) o.wires o.body = some bimg)
    (hchkR : Tools.SVParser.RoundtripProof.bodyReorderCheck body' bimg = true)
    (hwagP : ∀ n ∈ seqNames o.body,
      declWidth o n = ((Tools.SVParser.RoundtripProof.moduleWof o) n).getD 0)
    -- the run and its states
    {k : Nat} {stM stO : String → Nat} {mems : MEnv} {envs : List Env}
    (hcpl : ∀ pr ∈ (seqRegs m).zip (seqRegs o), stO pr.2.1 = stM pr.1.1)
    (hfit : ∀ r ∈ seqRegs m, stM r.1 < 2 ^ declWidth m r.1)
    (hinsW : ∀ t x, x ∈ m.inputs.map (·.name) →
      ins t x < 2 ^ Tools.SVParser.EmitSem.weOf wof x)
    (hinsP : ∀ t x, x ∈ m.inputs.map (·.name) →
      ins t x < 2 ^ ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0)
    (hstBE : Bounded (Tools.SVParser.EmitSem.weOf wof) stO)
    (hstBP : Bounded
      (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0) stO)
    (hrun : runModule (declWidth m) m.body (seedIn m ins) k stM mems = some envs) :
    ∃ envsO,
      -- the optimized module's trace, output-matched to `m`'s
      runModule (declWidth o) o.body (seedIn m ins) k stO mems = some envsO ∧
      envsO.length = envs.length ∧
      (∀ p ∈ m.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envs.length),
        (envsO[j]'hj) p.name = (envs[j]'hj') p.name) ∧
      -- its emitted Verilog's trace
      (∃ pairs regs mprog,
        Tools.SVParser.EmitSem.emitAssigns wof o.body = some pairs ∧
        Tools.SVParser.EmitSem.emitRegs wof o.body = some regs ∧
        Tools.SVParser.EmitSem.emitMemWrites wof o.body = some mprog ∧
        Tools.SVParser.EmitSem.runModuleSV wof pairs regs mprog
          (seedIn m ins) k stO mems = some envsO) ∧
      -- the parsed-back module's trace
      runModule (fun x => ((Tools.SVParser.RoundtripProof.moduleWof o) x).getD 0)
        body' (seedIn m ins) k stO mems = some envsO := by
  have hok : o.body.all seqStmtOk = true := seqOptCheck_stmtOk_o hchk
  obtain ⟨envsO, hrunO, hlen, hcorr⟩ :=
    seqOptCheck_transfer hchk ins hinsFit hrstIn hrstZ hcpl hfit hrun
  refine ⟨envsO, hrunO, hlen, hcorr, ?_, ?_⟩
  · exact seq_run_to_sv hok hsv hwagE (seedIn m ins)
      (seedIn_bounded hinsW) hstBE hrunO
  · exact seq_run_to_parsed hok hok' hcert hI hchkR hwagP
      (ins := ins) hinsP hstBP hrunO

open Sparkle.IR.RegDedup (declWidth) in
open Tools.ShippingMemSVSoundness in
/-- **The composed memory post-pipeline transfer.** Sync-read memory
bodies pass the post-processing passes unchanged (the identity gates),
so the fold starts from the checked module's own canonical-seed run: its
emitted Verilog (the `runModuleSVM` layer, read latch and write program
included) and the module the shipping parser reads back from the printed
bytes both run to the SAME trace. -/
theorem shipping_pipeline_transfer_mem {m o : Module}
    {body' bimg : List Stmt} {we0 : WEnv}
    -- emitted-SV premises
    (hchkM : seqCheckM (Tools.SVParser.RoundtripProof.moduleWof o)
      (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof o))
      o.body = true)
    (hrefs : o.body.all memOpsRefs = true)
    (hwag : ∀ n ∈ seqNamesM o.body,
      we0 n = Tools.SVParser.EmitSem.weOf
        (Tools.SVParser.RoundtripProof.moduleWof o) n)
    -- parsed-bytes premises
    (hchkM' : seqCheckM (Tools.SVParser.RoundtripProof.moduleWof o)
      (Tools.SVParser.EmitSem.weOf (Tools.SVParser.RoundtripProof.moduleWof o))
      body' = true)
    (hcert : Tools.SVParser.RoundtripProof.semFragCheck o = true)
    (hI : Tools.SVParser.RoundtripProof.bodyImage
      (Tools.SVParser.RoundtripProof.moduleWof o) o.wires o.body = some bimg)
    (hchkR : Tools.SVParser.RoundtripProof.bodyReorderCheck body' bimg = true)
    -- the run and its state
    {ins : Nat → String → Nat}
    (hinsW : ∀ t x, x ∈ m.inputs.map (·.name) →
      ins t x < 2 ^ Tools.SVParser.EmitSem.weOf
        (Tools.SVParser.RoundtripProof.moduleWof o) x)
    {k : Nat} {stO : String → Nat} {mems : MEnv} {envs : List Env}
    (hstB : Bounded (Tools.SVParser.EmitSem.weOf
      (Tools.SVParser.RoundtripProof.moduleWof o)) stO)
    (hrun : runModule we0 o.body (seedIn m ins) k stO mems = some envs) :
    -- the emitted Verilog's trace
    (∃ pairs seqs mprog,
      Tools.SVParser.EmitSem.emitAssigns
        (Tools.SVParser.RoundtripProof.moduleWof o) o.body = some pairs ∧
      emitSeqNexts (Tools.SVParser.RoundtripProof.moduleWof o) o.body = some seqs ∧
      Tools.SVParser.EmitSem.emitMemWrites
        (Tools.SVParser.RoundtripProof.moduleWof o) o.body = some mprog ∧
      runModuleSVM (Tools.SVParser.RoundtripProof.moduleWof o) pairs seqs mprog
        (seedIn m ins) k stO mems = some envs) ∧
    -- the parsed-back module's trace
    runModule (Tools.SVParser.EmitSem.weOf
        (Tools.SVParser.RoundtripProof.moduleWof o))
      body' (seedIn m ins) k stO mems = some envs := by
  refine ⟨?_, ?_⟩
  · exact mem_run_to_sv hchkM hrefs hwag (seedIn m ins)
      (seedIn_bounded hinsW) hstB hrun
  · exact mem_run_to_parsed hchkM hchkM' hrefs hcert hI hchkR hwag
      (ins := ins) hinsW hstB hrun

end Tools.ShippingPipelineSoundness
