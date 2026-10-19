import Tools.ShippingMemKidPorts
import Tools.ShippingKidFacts
import Tools.ShippingDesignSVMem
import Tools.ShippingMachineShipsHier
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # What the check-free chain takes of ONE callee that may be a MEMORY, and the built memory module's side of it (G1, unit U4, round par/b-13)

`Tools.ShippingKidFacts.KidFacts mref cref c outs ins n` cannot be the
interface of a memory child, for three reasons READ off the definitions
(`docs/parallel/B-memkids.md` §2):

1. it quantifies over `RealChild mref cref c y`; a memory's child is not
   compiled from a declaration (`closeInstsGM`: `memChild? c = some md ⇒ pure
   md`), so NO `RealChild` witness is produced for it — for a memory
   placeholder `c` the nine fields would be about nothing the run uses;
2. the field `masked : outsMaskedN y.1 = true` is FALSE of the built module:
   `outsMaskedN` asks `noMem y.1.body` and an output assigned by a constant or
   a slice, and the module's body is one memory statement and
   `out := out_rdata`. The child bound of a memory is another one
   (`kidsMem` / `memInv`: the read latch within the output's width), and the
   endpoints of memory parents state `kidsMixed`, not `kidsMaskedN`;
3. the field `check` at `n ≥ 1` is FALSE of the built module:
   `kidCheck C (k+1) = designCheck C k` asks `textCheckI`, whose first
   conjunct `seqStmtOkI` rejects a memory statement. It holds at `n = 0`
   only (`kidCheck C 0 = leafCheck`, `leafCheck_memModule`).

So this file states the weakest replacement that the consumers need:

* `KidFactsM mref cref c outs ins n`: the fields of `KidFacts` over
  `Tools.ShippingMemKid.Kid` (the built module for a memory placeholder, a
  real child otherwise), with `masked` replaced by `flat : FlatOk y.1` —
  masked outputs and no memory, OR the built memory module;
* `kidFacts_toM`: a callee that is NOT a memory placeholder has it from its
  `KidFacts` (every `n`);
* `memKid_facts`: a memory placeholder has it at `n = 0`, for every read
  kind and widths — outputs `[out : BitVec dw]`, argument widths
  `[aw, dw, 1, aw]`;
* `kidsM_runFacts`, `kidsM_outsCheck`, `kidsM_mixed`, `kidsM_designCheck`:
  the four run hypotheses of `Tools.ShippingNoPorts.machine_design_noPorts`
  at a parent WITH a register tied by the general closing, from `KidFactsM`
  of every call entry's callee — `kidsM_mixed` proves `kidsMixed` (the `Bd`
  of the depth-0 route), not `kidsMaskedN`.

SCOPE: depth 0 for a parent with a memory child (reason 3); a parent with a
register (`hsl`: `core_clkM`). The closing `MachineClosesAt` of such a
parent stays a hypothesis: `closesAtCoreG` refuses a memory child.

UNVERIFIED at the time of writing: this file was not built. -/
namespace Tools.ShippingMemKid
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingUnifiedSource Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMachineCloses
open Tools.ShippingMixedEntrySoundness
open Tools.ShippingGateChildComb Tools.ShippingChildInv
open Tools.ShippingInstStmtG Tools.ShippingCallsAssemblyG Tools.ShippingTransitionClosed
open Tools.ShippingSeqChildIface Tools.ShippingCallsKidsD Tools.ShippingDesignWithG
open Tools.ShippingClosedKinds Tools.ShippingKidsChildIface
open Sparkle.IR.RefineCheck (mergeChecked hierBinds)
open Sparkle.IR.OptCheck (seqStmtOk checkedOptimize)
open Tools.ShippingMachineLinked (childMap)
open Sparkle.Compiler.MachMemory (memModule memChild?)

/-! ## Pure: the statement of a call group, the flat child bound -/

/-- **The port a connection of a call group's instance names**: an argument
port of the child, `clk`, `rst`, or an output port of the child — EVERY
connection (`Tools.ShippingPortsMatchRaw.callStmtG_conn` speaks of the
reference connections and of what they read). -/
theorem callStmtG_portNames {nIn kI n : Nat} {names : List String} {args : List Nat}
    {outs : List (Nat × String)} {mc : Sparkle.IR.AST.Module} {mn iname : String}
    {conns : List (String × Sparkle.IR.AST.Expr)}
    (h : Tools.ShippingMachineInstG.CallStmtG nIn kI n names args outs mc
      (Stmt.inst mn iname conns))
    {cn : String × Sparkle.IR.AST.Expr} (hm : cn ∈ conns) :
    (∃ q ∈ inPortsOf mc, q.name = cn.1) ∨ cn.1 = "clk" ∨ cn.1 = "rst" ∨
      ∃ p ∈ mc.outputs, p.name = cn.1 := by
  obtain ⟨outWs, argWs, iname', hout, hargs, -, -, hfo, -, -, -, -, -, -, he⟩ := h
  injection he with h1 h2 h3
  rw [h3] at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · -- an argument connection
      left
      obtain ⟨⟨q, aw⟩, hq, heq⟩ := List.mem_map.mp hm
      exact ⟨q, (List.of_mem_zip hq).1, congrArg Prod.fst heq⟩
    · -- the clock and the reset
      right
      by_cases hs : (mc.inputs.any fun p => p.name == "clk" || p.name == "rst") = true
      · rw [if_pos hs] at hm
        rcases List.mem_cons.mp hm with h0 | h0
        · exact Or.inl (congrArg Prod.fst h0)
        · rcases List.mem_cons.mp h0 with h0 | h0
          · exact Or.inr (Or.inl (congrArg Prod.fst h0))
          · cases h0
      · rw [if_neg hs] at hm
        cases hm
  · -- an output connection
    right
    right
    right
    obtain ⟨⟨f, w'⟩, hfw, heq⟩ := List.mem_map.mp hm
    have hf : f ∈ outs.map (·.2) := (List.of_mem_zip hfw).1
    obtain ⟨p, hp, hpe⟩ := List.any_eq_true.mp (List.all_eq_true.mp hfo f hf)
    exact ⟨p, hp, (beq_iff_eq.mp hpe).trans (congrArg Prod.fst heq)⟩

/-- **What the flat (depth-0) child bound asks of a kid's own module**:
masked outputs and no memory (`kidsMasked`), or the built memory module
(`kidsMem`). -/
def FlatOk (m : Sparkle.IR.AST.Module) : Prop :=
  (Tools.ShippingMachineShipsHier.noMem m.body = true ∧
    m.outputs.all (Tools.ShippingMachineShipsHier.outMasked (Sparkle.IR.RegDedup.declWidth m)
      m.body) = true) ∨
  ∃ cb aw dw, m = (memModule cb aw dw).1

/-- `outsMaskedN` (the depth form) gives the flat form. -/
theorem flatOk_of_masked {m : Sparkle.IR.AST.Module}
    (h : Tools.ShippingMachineShipsDepth.outsMaskedN m = true) : FlatOk m := by
  unfold Tools.ShippingMachineShipsDepth.outsMaskedN at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine Or.inl ⟨h1, List.all_eq_true.mpr fun p hp => ?_⟩
  have h3 := List.all_eq_true.mp h2 p hp
  rw [Bool.and_eq_true] at h3
  exact h3.1

/-- One instance whose child is masked and memory-free. -/
theorem kidsMasked_one {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {mn iname : String} {conns : List (String × Sparkle.IR.AST.Expr)}
    {child : Sparkle.IR.AST.Module} {cwe : Sparkle.IR.Semantics.WEnv}
    (hc : C mn = some (child, cwe))
    (h1 : Tools.ShippingMachineShipsHier.noMem child.body = true)
    (h2 : child.outputs.all (Tools.ShippingMachineShipsHier.outMasked cwe child.body) = true) :
    Tools.ShippingMachineShipsHier.kidsMasked C [Stmt.inst mn iname conns] = true := by
  simp [Tools.ShippingMachineShipsHier.kidsMasked, hc, h1, h2]

/-- One instance whose child is the built memory module, no connection naming
its read latch. -/
theorem kidsMem_one {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {mn iname : String} {conns : List (String × Sparkle.IR.AST.Expr)}
    {cb : Bool} {aw dw : Nat} {cwe : Sparkle.IR.Semantics.WEnv}
    (hc : C mn = some ((memModule cb aw dw).1, cwe))
    (hn : (conns.any fun c => c.1 == "out_rdata") = false) :
    Tools.ShippingMachineShipsHier.kidsMem C [Stmt.inst mn iname conns] = true := by
  simp [Tools.ShippingMachineShipsHier.kidsMem, hc, hn,
    Tools.ShippingMachineShipsHier.memParams_memModule']

/-- **`kidsMixed` from one fact per instance statement.** -/
theorem kidsMixed_of {C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)}
    {body : List Stmt}
    (h : ∀ mn iname conns, Stmt.inst mn iname conns ∈ body →
      Tools.ShippingMachineShipsHier.kidsMasked C [Stmt.inst mn iname conns] = true ∨
      Tools.ShippingMachineShipsHier.kidsMem C [Stmt.inst mn iname conns] = true) :
    Tools.ShippingMachineShipsHier.kidsMixed C body = true := by
  unfold Tools.ShippingMachineShipsHier.kidsMixed
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    rw [Bool.or_eq_true]
    exact h mn iname conns hst
  | _ => rfl

/-! ## The built memory module -/

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

/-- The layout-style description of the memory module's one output. -/
def memOuts (dw : Nat) : List OutField :=
  [{ name := "out", lo := 0, width := dw, ty := .bitVector dw }]

/-- The memory module's argument widths, in the call's argument order
`wa wd we ra`. -/
def memIns (aw dw : Nat) : List Nat := [aw, dw, 1, aw]

theorem mem_output {cb : Bool} {aw dw : Nat} {p : Port}
    (hp : p ∈ (memModule cb aw dw).1.outputs) : p = { name := "out", ty := .bitVector dw } := by
  have hp' : p ∈ [({ name := "out", ty := .bitVector dw } : Port)] := hp
  exact List.mem_singleton.mp hp'

theorem mem_wire {cb : Bool} {aw dw : Nat} {p : Port}
    (hp : p ∈ (memModule cb aw dw).1.wires) :
    p = { name := "out_rdata", ty := .bitVector dw } := by
  have hp' : p ∈ [({ name := "out_rdata", ty := .bitVector dw } : Port)] := hp
  exact List.mem_singleton.mp hp'

theorem mem_input_names {cb : Bool} {aw dw : Nat} {p : Port}
    (hp : p ∈ (memModule cb aw dw).1.inputs) :
    p.name = "wa" ∨ p.name = "wd" ∨ p.name = "we" ∨ p.name = "ra" ∨ p.name = "clk" ∨
      p.name = "rst" := by
  have hp' : p ∈ [({ name := "wa", ty := .bitVector aw } : Port),
      { name := "wd", ty := .bitVector dw }, { name := "we", ty := .bit },
      { name := "ra", ty := .bitVector aw }, { name := "clk", ty := .bit },
      { name := "rst", ty := .bit }] := hp
  rcases List.mem_cons.mp hp' with h | hp'
  · exact Or.inl (congrArg Port.name h)
  rcases List.mem_cons.mp hp' with h | hp'
  · exact Or.inr (Or.inl (congrArg Port.name h))
  rcases List.mem_cons.mp hp' with h | hp'
  · exact Or.inr (Or.inr (Or.inl (congrArg Port.name h)))
  rcases List.mem_cons.mp hp' with h | hp'
  · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg Port.name h))))
  rcases List.mem_cons.mp hp' with h | hp'
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (congrArg Port.name h)))))
  rcases List.mem_cons.mp hp' with h | hp'
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (congrArg Port.name h)))))
  · cases hp'

/-- The argument ports: the inputs but `clk` and `rst`. -/
theorem mem_inPort_names {cb : Bool} {aw dw : Nat} {q : Port}
    (hq : q ∈ inPortsOf (memModule cb aw dw).1) :
    q.name = "wa" ∨ q.name = "wd" ∨ q.name = "we" ∨ q.name = "ra" := by
  have hq' : q ∈ (memModule cb aw dw).1.inputs.filter
      (fun p => p.name != "clk" && p.name != "rst") := hq
  obtain ⟨h1, h0⟩ := List.mem_filter.mp hq'
  have h2 : (q.name != "clk" && q.name != "rst") = true := h0
  rcases mem_input_names h1 with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · rw [h] at h2
    exact absurd h2 (by decide)
  · rw [h] at h2
    exact absurd h2 (by decide)

/-- The argument ports as a list (the call's argument order). -/
theorem mem_inPorts (cb : Bool) (aw dw : Nat) :
    inPortsOf (memModule cb aw dw).1 =
      [({ name := "wa", ty := .bitVector aw } : Port), { name := "wd", ty := .bitVector dw },
        { name := "we", ty := .bit }, { name := "ra", ty := .bitVector aw }] := by
  first
    | rfl
    | simp (config := { decide := true }) [inPortsOf, memModule]

theorem mem_outsIn (cb : Bool) (aw dw : Nat) :
    ∀ p ∈ (memModule cb aw dw).1.outputs,
      (∀ q ∈ inPortsOf (memModule cb aw dw).1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
        p.name ≠ "rst" := by
  intro p hp
  have e := mem_output hp
  subst e
  refine ⟨fun q hq => ?_, ?_, ?_⟩
  · show q.name ≠ "out"
    rcases mem_inPort_names hq with h | h | h | h
    · rw [h]
      decide
    · rw [h]
      decide
    · rw [h]
      decide
    · rw [h]
      decide
  · show "out" ≠ "clk"
    decide
  · show "out" ≠ "rst"
    decide

theorem mem_outTys (cb : Bool) (aw dw : Nat) :
    Tools.ShippingChildIfaceTy.ChildOutTys (memOuts dw) (memModule cb aw dw).1 :=
  ⟨rfl⟩

theorem mem_outsAssigned (cb : Bool) (aw dw : Nat) :
    Tools.ShippingDesignSVBack.outsAssigned (memModule cb aw dw).1 = true := by
  first
    | rfl
    | simp (config := { decide := true }) [Tools.ShippingDesignSVBack.outsAssigned, memModule]

/-- The memory module's design is the module itself. -/
theorem mem_design {cb : Bool} {aw dw : Nat} {g : Sparkle.IR.AST.Module}
    (hg : g ∈ (memModule cb aw dw).2.modules) : g = (memModule cb aw dw).1 := by
  have hg' : g ∈ [(memModule cb aw dw).1] := hg
  exact List.mem_singleton.mp hg'

theorem mem_noInst (cb : Bool) (aw dw : Nat) (mn iname : String)
    (conns : List (String × Sparkle.IR.AST.Expr)) :
    Stmt.inst mn iname conns ∉ (memModule cb aw dw).1.body := by
  intro h
  simp [memModule] at h

theorem mem_kidR (cb : Bool) (aw dw : Nat) :
    ∀ g ∈ (memModule cb aw dw).1 :: (memModule cb aw dw).2.modules, ∀ mn i conns,
      Stmt.inst mn i conns ∈ g.body → ∃ g2 ∈ (memModule cb aw dw).2.modules, g2.name = mn := by
  intro g hg mn i conns hm
  have e : g = (memModule cb aw dw).1 := by
    rcases List.mem_cons.mp hg with h | h
    · exact h
    · exact mem_design h
  rw [e] at hm
  exact absurd hm (mem_noInst cb aw dw mn i conns)

theorem mem_portsIn (cb : Bool) (aw dw : Nat) :
    Tools.ShippingLeafTyped.PortsIn (memModule cb aw dw).1 := by
  refine { wn := ?_, ow := ?_, oi := ?_, ostable := ?_, ond := ?_, oty := ?_ }
  · intro p hp
    have e := mem_wire hp
    subst e
    exact san_out_rdata
  · intro q hq p hp
    have e := mem_output hq
    subst e
    have e2 := mem_wire hp
    subst e2
    show "out_rdata" ≠ "out"
    decide
  · intro q hq p hp
    have e := mem_output hq
    subst e
    show Sparkle.Backend.Verilog.sanitizeName p.name ≠ "out"
    rcases mem_input_names hp with h | h | h | h | h | h
    · rw [h, san_wa]
      decide
    · rw [h, san_wd]
      decide
    · rw [h, san_we]
      decide
    · rw [h, san_ra]
      decide
    · rw [h, san_clk]
      decide
    · rw [h, san_rst]
      decide
  · intro q hq
    have e := mem_output hq
    subst e
    exact san_out
  · show (["out"] : List String).Nodup
    exact List.nodup_cons.mpr ⟨(fun h => nomatch h), List.nodup_nil⟩
  · intro q hq
    have e := mem_output hq
    subst e
    exact Or.inr ⟨dw, rfl⟩

/-- The emitter's widths of the memory module's input ports. -/
theorem mem_weS (cb : Bool) (aw dw : Nat) :
    Tools.ShippingDesignSV.weS (memModule cb aw dw).1 "wa" = aw ∧
    Tools.ShippingDesignSV.weS (memModule cb aw dw).1 "wd" = dw ∧
    Tools.ShippingDesignSV.weS (memModule cb aw dw).1 "we" = 1 ∧
    Tools.ShippingDesignSV.weS (memModule cb aw dw).1 "ra" = aw ∧
    Tools.ShippingDesignSV.weS (memModule cb aw dw).1 "clk" = 1 ∧
    Tools.ShippingDesignSV.weS (memModule cb aw dw).1 "rst" = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp (config := { decide := true }) [Tools.ShippingDesignSV.weS, Tools.ShippingDesignSV.wofOf,
    Tools.SVParser.EmitSem.weOf, Tools.SVParser.RoundtripProof.moduleWof, memModule,
    san_ra, san_wa, san_wd, san_we, san_out_rdata, san_clk, san_rst]

theorem mem_inW (cb : Bool) (aw dw : Nat) :
    ∀ (j : Nat) (q : Port), (inPortsOf (memModule cb aw dw).1)[j]? = some q →
      ∃ wd, (memIns aw dw)[j]? = some wd ∧
        Tools.ShippingDesignSV.weS (memModule cb aw dw).1 q.name = wd := by
  intro j q hq
  rw [mem_inPorts] at hq
  obtain ⟨hwa, hwd, hwe, hra, -, -⟩ := mem_weS cb aw dw
  match j, hq with
  | 0, h =>
    have e : ({ name := "wa", ty := .bitVector aw } : Port) = q := Option.some.inj h
    rw [← e]
    exact ⟨aw, rfl, hwa⟩
  | 1, h =>
    have e : ({ name := "wd", ty := .bitVector dw } : Port) = q := Option.some.inj h
    rw [← e]
    exact ⟨dw, rfl, hwd⟩
  | 2, h =>
    have e : ({ name := "we", ty := .bit } : Port) = q := Option.some.inj h
    rw [← e]
    exact ⟨1, rfl, hwe⟩
  | 3, h =>
    have e : ({ name := "ra", ty := .bitVector aw } : Port) = q := Option.some.inj h
    rw [← e]
    exact ⟨aw, rfl, hra⟩
  | j + 4, h => exact absurd h (by simp)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-- A connection of a memory instance never names the read latch. -/
theorem mem_conns_noRdata {nIn kI n : Nat} {names : List String} {args : List Nat}
    {outs : List (Nat × String)} {cb : Bool} {aw dw : Nat} {mn iname : String}
    {conns : List (String × Sparkle.IR.AST.Expr)}
    (h : Tools.ShippingMachineInstG.CallStmtG nIn kI n names args outs (memModule cb aw dw).1
      (Stmt.inst mn iname conns)) :
    (conns.any fun c => c.1 == "out_rdata") = false := by
  rw [List.any_eq_false]
  intro cn hcn hb
  have e : cn.1 = "out_rdata" := beq_iff_eq.mp hb
  rcases callStmtG_portNames h hcn with ⟨q, hq, hqn⟩ | h1 | h1 | ⟨p, hp, hpn⟩
  · rw [e] at hqn
    rcases mem_inPort_names hq with h2 | h2 | h2 | h2
    · exact absurd (h2.symm.trans hqn) (by decide)
    · exact absurd (h2.symm.trans hqn) (by decide)
    · exact absurd (h2.symm.trans hqn) (by decide)
    · exact absurd (h2.symm.trans hqn) (by decide)
  · exact absurd (e.symm.trans h1) (by decide)
  · exact absurd (e.symm.trans h1) (by decide)
  · have e2 := mem_output hp
    subst e2
    have e3 : "out" = "out_rdata" := hpn.trans e
    exact absurd e3 (by decide)

/-! ## The interface -/

/-- **What a parent's check-free chain takes of one callee `c` that may be a
memory**: facts of every kid of `c`. `outs`: the callee's output fields;
`ins`: the widths of its argument ports; `n`: the parent's depth. The fields
are `Tools.ShippingKidFacts.KidFacts`' over `Kid`, with `masked` replaced by
`flat`. -/
structure KidFactsM (mref : ST.Ref IO.RealWorld Meta.State)
    (cref : ST.Ref IO.RealWorld Core.State) (c : Name) (outs : List OutField)
    (ins : List Nat) (n : Nat) : Prop where
  outsIn : ∀ (y : Res), Kid mref cref c y →
    ∀ p ∈ y.1.outputs, (∀ q ∈ inPortsOf y.1, q.name ≠ p.name) ∧ p.name ≠ "clk" ∧
      p.name ≠ "rst"
  outTys : ∀ (y : Res), Kid mref cref c y →
    Tools.ShippingChildIfaceTy.ChildOutTys outs y.1
  kidA : ∀ (y : Res), Kid mref cref c y →
    Tools.ShippingDesignSVBack.outsAssigned y.1 = true ∧
      ∀ g ∈ y.2.modules, Tools.ShippingDesignSVBack.outsAssigned g = true
  kidR : ∀ (y : Res), Kid mref cref c y →
    ∀ g ∈ y.1 :: y.2.modules, ∀ mn i conns, Stmt.inst mn i conns ∈ g.body →
      ∃ g2 ∈ y.2.modules, g2.name = mn
  flat : ∀ (y : Res), Kid mref cref c y → FlatOk y.1
  portsIn : ∀ (y : Res), Kid mref cref c y → Tools.ShippingLeafTyped.PortsIn y.1
  inW : ∀ (y : Res), Kid mref cref c y →
    ∀ (j : Nat) (q : Port), (inPortsOf y.1)[j]? = some q →
      ∃ wd, ins[j]? = some wd ∧ Tools.ShippingDesignSV.weS y.1 q.name = wd
  clk : ∀ (y : Res), Kid mref cref c y → isSeqChild y.1 = true →
    Tools.ShippingDesignSV.weS y.1 "clk" = 1 ∧ Tools.ShippingDesignSV.weS y.1 "rst" = 1
  check : ∀ (y : Res), Kid mref cref c y →
    ∀ ms : List Sparkle.IR.AST.Module,
      moduleByName ms y.1.name = some y.1 →
      (∀ g ∈ y.2.modules, moduleByName ms g.name = some g) →
      Tools.ShippingChecksDesign.kidCheck (childMap ms) n y.1 = true ∧
        ∀ g ∈ y.2.modules, Tools.ShippingChecksDesign.kidCheck (childMap ms) n g = true

/-- **A callee that is not a memory placeholder**: its `KidFacts`, every
depth. -/
theorem kidFacts_toM {c : Name} {outs : List OutField} {ins : List Nat} {n : Nat}
    (h : Tools.ShippingKidFacts.KidFacts mref cref c outs ins n)
    (hc : memChild? c = none) : KidFactsM mref cref c outs ins n :=
  { outsIn := fun y hy => h.outsIn y (hy.real hc)
    outTys := fun y hy => h.outTys y (hy.real hc)
    kidA := fun y hy => h.kidA y (hy.real hc)
    kidR := fun y hy => h.kidR y (hy.real hc)
    flat := fun y hy => flatOk_of_masked (h.masked y (hy.real hc))
    portsIn := fun y hy => h.portsIn y (hy.real hc)
    inW := fun y hy => h.inW y (hy.real hc)
    clk := fun y hy => h.clk y (hy.real hc)
    check := fun y hy => h.check y (hy.real hc) }

/-- **A memory placeholder**, at depth 0: the built memory module's side of
the interface, for every read kind and widths. -/
theorem memKid_facts {c : Name} {cb : Bool} {aw dw : Nat}
    (hc : memChild? c = some (memModule cb aw dw)) :
    KidFactsM mref cref c (memOuts dw) (memIns aw dw) 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have e := hy.mem hc
    subst e
    exact mem_outsIn cb aw dw
  · intro y hy
    have e := hy.mem hc
    subst e
    exact mem_outTys cb aw dw
  · intro y hy
    have e := hy.mem hc
    subst e
    refine ⟨mem_outsAssigned cb aw dw, fun g hg => ?_⟩
    rw [mem_design hg]
    exact mem_outsAssigned cb aw dw
  · intro y hy
    have e := hy.mem hc
    subst e
    exact mem_kidR cb aw dw
  · intro y hy
    have e := hy.mem hc
    subst e
    exact Or.inr ⟨cb, aw, dw, rfl⟩
  · intro y hy
    have e := hy.mem hc
    subst e
    exact mem_portsIn cb aw dw
  · intro y hy
    have e := hy.mem hc
    subst e
    exact mem_inW cb aw dw
  · intro y hy _
    have e := hy.mem hc
    subst e
    exact ⟨(mem_weS cb aw dw).2.2.2.2.1, (mem_weS cb aw dw).2.2.2.2.2⟩
  · intro y hy ms _ _
    have e := hy.mem hc
    subst e
    have hl : Tools.ShippingChecksDesign.kidCheck (childMap ms) 0 (memModule cb aw dw).1 = true :=
      Tools.ShippingDesignSV.leafCheck_memModule cb aw dw
    refine ⟨hl, fun g hg => ?_⟩
    rw [mem_design hg]
    exact hl

/-- The callee of entry `k` (anonymous outside the list): tables of a parent
with DIFFERENT callees are keyed by it, so no entry order is assumed. -/
def calleeAt (d : MachineData) (k : Nat) : Name :=
  ((d.shape.insts[k]?).map (·.1)).getD .anonymous

theorem calleeAt_eq (d : MachineData) {k : Nat} (hk : k < d.shape.insts.length) :
    calleeAt d k = (d.shape.insts[k]).1 := by
  unfold calleeAt
  rw [List.getElem?_eq_getElem hk]
  rfl

/-! ## The four run hypotheses of the head, from `KidFactsM` -/

/-- **`hkidW` from the data** (`Tools.ShippingCallWidths.hkidW_of_data`, its
proof verbatim, over `Kid`). -/
theorem hkidW_of_dataM {d : MachineData} {nDecl : Nat} {kidOuts : Nat → List OutField}
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys (kidOuts k) y.1) :
    ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y →
      ∀ p ∈ y.1.outputs, p.name = d.shape.instFields.getD k "" →
        (d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth := by
  intro k hk y hy p hp hpn
  unfold Tools.ShippingCallWidths.callWidthsOk at hcw
  have h1 : ((kidOuts k).all fun o =>
      o.name != d.shape.instFields.getD k "" ||
        decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some o.ty.bitWidth)) = true :=
    List.all_eq_true.mp hcw k (List.mem_range.mpr hk)
  rw [(hkidT k hk y hy).outputs] at hp
  obtain ⟨o, ho, e⟩ := List.mem_map.mp hp
  have h2 : (o.name != d.shape.instFields.getD k "" ||
      decide ((d.shape.binders[nDecl + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
        some o.ty.bitWidth)) = true :=
    List.all_eq_true.mp h1 o ho
  have hpn' : o.name = d.shape.instFields.getD k "" := by
    rw [← e] at hpn
    exact hpn
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact absurd hpn' (bne_iff_ne.mp h2)
  · have h3 := of_decide_eq_true h2
    rw [← e]
    exact h3

/-- **The run's facts of the full entry's module** (`core_runFactsM`). -/
theorem kidsM_runFacts {c : Name} (d : MachineData) (ok : d.ok = true)
    (hagree : Tools.ShippingInstTagged.TagsAgree d.shape)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsM mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b :=
  core_runFactsM (hagree := hagree) d ok hbody hC hslots hdomB hins hsl hfne outTy
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    (hkidW_of_dataM hcw (fun k hk y hy => (hkid k hk).outTys y hy))
    hB hcore hpost entry closes

/-- **The output check at depth `n`, under the statement-kind gate**
(`core_outsCheck_all_gateM`). -/
theorem kidsM_outsCheck {c : Name} (d : MachineData) (ok : d.ok = true)
    (hagree : Tools.ShippingInstTagged.TagsAgree d.shape)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsM mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hg : Sparkle.IR.RefineCheck.hierGate b = true) :
    Tools.ShippingDesignSVBack.outsCheck (childMap D.modules) n (checkedOptimize b) = true :=
  core_outsCheck_all_gateM (hagree := hagree) d ok hbody hC hslots hdomB hins outTy hfne
    (fun k hk y hy => (hkid k hk).kidA y hy)
    (fun k hk y hy => (hkid k hk).kidR y hy)
    hB hcore hpost entry closes hg n

set_option maxHeartbeats 4000000 in
/-- **`kidsMixed` of a machine tied by the general closing, on the core run's
design**: every instance of the full entry's module resolves to a kid's own
module, which is masked and memory-free or the built memory module; a memory
instance's connections name its ports only (`core_callStmtM`,
`mem_conns_noRdata`). -/
theorem core_kidsMixedM {c : Name} (d : MachineData) (ok : d.ok = true)
    (hagree : Tools.ShippingInstTagged.TagsAgree d.shape)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hkidF : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      Kid mref cref (d.shape.insts[k]).1 y → FlatOk y.1)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingMachineShipsHier.kidsMixed (childMap D.modules) b.body = true := by
  have hst := core_callStmtM (hagree := hagree) d ok hbody hC hslots hdomB hins hfne outTy hB hcore hpost entry
    closes
  refine kidsMixed_of fun mn iname conns hm => ?_
  obtain ⟨mc, hmc, ⟨k, hk, y, hre, hmcy⟩, nIn, kI, n, names, args, outs, hcs⟩ :=
    hst mn iname conns hm
  have hCm : childMap D.modules mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) :=
    congrArg (fun o : Option Sparkle.IR.AST.Module =>
      o.map fun g => (g, Sparkle.IR.RegDedup.declWidth g)) hmc
  rcases hkidF k hk y hre with ⟨h1, h2⟩ | ⟨cb, aw, dw, hmem⟩
  · left
    rw [← hmcy] at h1 h2
    exact kidsMasked_one hCm h1 h2
  · right
    rw [← hmcy] at hmem
    rw [hmem] at hcs hCm
    exact kidsMem_one hCm (mem_conns_noRdata hcs)

/-- **The children's flat bound** (`core_kidsMixedM`). -/
theorem kidsM_mixed {c : Name} (d : MachineData) (ok : d.ok = true)
    (hagree : Tools.ShippingInstTagged.TagsAgree d.shape)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsM mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape) :
    Tools.ShippingMachineShipsHier.kidsMixed (childMap D.modules) b.body = true :=
  core_kidsMixedM (hagree := hagree) d ok hbody hC hslots hdomB hins hfne outTy
    (fun k hk y hy => (hkid k hk).flat y hy)
    hB hcore hpost entry closes

set_option maxHeartbeats 4000000 in
/-- **`designCheck` of the shipped module at depth `n` with NO check
premise**, from `KidFactsM` (`Tools.ShippingKidFacts.kids_designCheck`, its
proof over the copies). -/
theorem kidsM_designCheck {c : Name} (d : MachineData) (ok : d.ok = true)
    (hagree : Tools.ShippingInstTagged.TagsAgree d.shape)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    {nDecl : Nat} (hC : d.callsOk nDecl = true)
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hdomB : ∀ b ∈ d.shape.binders.drop nDecl, b.2 ≠ .domain)
    (hins : d.shape.insts ≠ [])
    (hsl : d.shape.layout.slots ≠ [])
    (hfne : d.shape.instFields ≠ [])
    (outTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (kidOuts : Nat → List OutField) (kidIns : Nat → List Nat) (n : Nat)
    (hkid : ∀ (k : Nat) (hk : k < d.shape.insts.length),
      KidFactsM mref cref (d.shape.insts[k]).1 (kidOuts k) (kidIns k) n)
    (hcw : Tools.ShippingCallWidths.callWidthsOk d nDecl kidOuts = true)
    (hargs : Tools.ShippingPortsMatchRaw.callArgsOk d nDecl kidIns = true)
    {w w1 : Void IO.RealWorld} {M b : Sparkle.IR.AST.Module} {D : Design}
    (hB : ChildBnd mref cref w)
    (hcore : RunsTo (synthesizeCombinationalCore c [] false) mctx mref cctx cref w (M, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule M ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule M))
    (entry : MachineDefines mctx mref cctx cref c d.shape)
    (closes : MachineClosesAt mctx mref cctx cref c d.shape)
    (hon : ∀ o ∈ d.shape.layout.outs, Sparkle.Backend.Verilog.sanitizeName o.name = o.name)
    (hoty : ∀ o ∈ d.shape.layout.outs, Tools.ShippingTextTyped.scalarTy o.ty = true) :
    Tools.ShippingDesignSV.designCheck (childMap D.modules) n (checkedOptimize b) = true := by
  have hkidW := hkidW_of_dataM hcw (fun k hk y hy => (hkid k hk).outTys y hy)
  have hraw : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) b = true :=
    core_portsMatch_rawM (hagree := hagree) d ok hbody hC hslots hdomB hins hfne outTy hkidW
      (fun k hk y hy => (hkid k hk).portsIn y hy)
      (kidIns := kidIns) hargs
      (fun k hk y hy j q hq => (hkid k hk).inW y hy j q hq)
      (fun k hk y hy hs => (hkid k hk).clk y hy hs)
      hB hcore hpost entry closes hon hoty
      (core_clkM d ok hbody hC hslots hdomB hins outTy hfne hsl hB hcore hpost entry closes)
  have hports : Tools.ShippingDesignSV.portsMatchB (childMap D.modules) (checkedOptimize b) =
      true :=
    Tools.ShippingPortsMatchShipped.portsMatchB_shipped
      (core_hierGateM (hagree := hagree) d ok hbody hC hslots hdomB hins hfne outTy hB hcore hpost entry closes)
      hraw
  have hkids := core_kidsPass_deepM (hagree := hagree) d ok hbody hC hslots hdomB hins hfne outTy n
    (fun k hk y hy ms h1 h2 => (hkid k hk).check y hy ms h1 h2)
    hB hcore hpost entry closes
  exact core_designCheck_runM (hagree := hagree) d ok hbody hC hslots hdomB hins hsl hfne outTy
    (fun k hk y hy => (hkid k hk).outsIn y hy)
    hkidW hB hcore hpost entry closes hon hoty n hports hkids

end Tools.ShippingMemKid
