import Tools.ShippingMachineInst
import Tools.ShippingInstNames
import Tools.ShippingChecksRaw
import Tools.ShippingChecksDerived
import Tools.ShippingHierOptRun
import Tools.ShippingOutsExtractedParts
import Tools.ShippingMachineDepthH

/-! # The ONE-OUTPUT closing (`closeInsts`): what its result says of its instance statements (G1, round par/a-6)

`Sparkle.IR.Machine.closeInsts` ties a machine's one-output calls to
instances. `MachineWired`'s clause about distinct instance names and the
self-feed test is conditional on `instFields ≠ []` (the GROUP closing,
which checks both); for the one-output closing those two facts are not
checked by the compiler. They follow from what `instStmt` builds:

* `instStmt_name`: the statement of call `k` is named `inst{k}_{child}`;
* `closeInsts_stmts`: the closed body is a permutation of the machine's body
  and one such statement per call, in order;
* `closeInsts_instNames`: so the instance names of the closed body are
  distinct, when the machine's body has no instance
  (`Tools.ShippingInstNames.instName_inj`: the call index is read off the
  name, whatever the children's names);
* `callStmt_parts`: a call's statement connects argument wires to input
  ports and the call's wire to THE output port, the call's wire not being an
  argument wire;
* `noSelfRead_of_calls`: so no instance reads its own output;
* `kidsLocal_of_comb`: the combinational children's check (`kidsComb`, what
  `closeInsts` runs as `kidsCombB`) contains the local children's check.

Pure: nothing here is about a run. -/
namespace Tools.ShippingOneOutClose
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Tools.ShippingMachineInst (CallStmt mapM_some)
open Tools.ShippingHierState (instNames inConns)
open Tools.ShippingHierOpen (instOutWires)
open Tools.ShippingMachineLinked (childMap)

/-- **The instance statement of call `k` is named `inst{k}_{child}`.** -/
theorem instStmt_name {nIn kI n : Nat} {portNames : List String} {k : Nat} {args : List Nat}
    {mc m : Module} {st : Stmt} (h : instStmt nIn kI n portNames k args mc m = some st) :
    ∃ conns : List (String × Sparkle.IR.AST.Expr),
      st = Stmt.inst mc.name s!"inst{k}_{mc.name}" conns := by
  unfold instStmt at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨outW, hout, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨argWs, hargs, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    cases h
    exact ⟨_, rfl⟩
  · cases h

/-- **The closed body: the machine's body and one named instance statement
per call, in order, permuted.** -/
theorem closeInsts_stmts {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d)) :
    ∃ stmts : List Stmt, (m₀.body ++ stmts).Perm m.body ∧
      ∀ (i : Nat) (hi : i < stmts.length),
        ∃ (mc : Module) (conns : List (String × Sparkle.IR.AST.Expr)),
          stmts[i] = Stmt.inst mc.name s!"inst{i}_{mc.name}" conns := by
  unfold closeInsts at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨stmts, hstmts, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨outWs, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨body, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hperm⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
    cases h
    obtain ⟨hlen, hget⟩ := mapM_some _ _ stmts hstmts
    refine ⟨stmts, Sparkle.IR.Reorder.isPermOf_sound hperm, fun i hi => ?_⟩
    obtain ⟨st', hst', hstk⟩ := hget i (by rw [← hlen]; exact hi)
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hstk
    subst hstk
    simp only [List.getElem_range, Option.bind_eq_bind] at hst'
    obtain ⟨args, hargs, hst'⟩ := Option.bind_eq_some_iff.mp hst'
    obtain ⟨child, hchild, hst'⟩ := Option.bind_eq_some_iff.mp hst'
    obtain ⟨mc, hmc, hst'⟩ := Option.bind_eq_some_iff.mp hst'
    obtain ⟨conns, he⟩ := instStmt_name hst'
    exact ⟨mc, conns, he⟩
  · cases h

/-! ## Instance names -/

theorem instNames_append : ∀ (a b : List Stmt),
    instNames (a ++ b) = instNames a ++ instNames b
  | [], _ => rfl
  | st :: rest, b => by
    have ih := instNames_append rest b
    rw [List.cons_append]
    cases st with
    | inst mn i conns =>
      have e1 : instNames (Stmt.inst mn i conns :: (rest ++ b)) = i :: instNames (rest ++ b) := rfl
      have e2 : instNames (Stmt.inst mn i conns :: rest) = i :: instNames rest := rfl
      rw [e1, e2, ih, List.cons_append]
    | assign l r => exact ih
    | register o c rk inp iv => exact ih
    | memory => exact ih

/-- A body of assignments and registers has no instance name. -/
theorem instNames_nil_of_seqOk {body : List Stmt}
    (h : body.all Sparkle.IR.OptCheck.seqStmtOk = true) : instNames body = [] := by
  cases hn : instNames body with
  | nil => rfl
  | cons a l =>
    obtain ⟨mn, conns, hm⟩ := Tools.ShippingHierOptRun.mem_instNames (n := a) (body := body)
      (by rw [hn]; exact List.mem_cons_self ..)
    exact Tools.ShippingChecksDerived.ff_absurd (List.all_eq_true.mp h _ hm)

/-- Statements named `inst{off+i}_…` at position `i` have distinct names,
each of that form at an index `≥ off`. -/
theorem stmts_names : ∀ (stmts : List Stmt) (off : Nat),
    (∀ (i : Nat) (hi : i < stmts.length),
      ∃ (mc : Module) (conns : List (String × Sparkle.IR.AST.Expr)),
        stmts[i] = Stmt.inst mc.name s!"inst{off + i}_{mc.name}" conns) →
    (instNames stmts).Nodup ∧
      ∀ x ∈ instNames stmts, ∃ (j : Nat) (nm : String), off ≤ j ∧ x = s!"inst{j}_{nm}"
  | [], _, _ => ⟨List.nodup_nil, fun x hx => by cases hx⟩
  | st :: rest, off, h => by
    obtain ⟨mc, conns, hst⟩ := h 0 (by rw [List.length_cons]; omega)
    have hst' : st = Stmt.inst mc.name s!"inst{off + 0}_{mc.name}" conns := hst
    have hrest : ∀ (i : Nat) (hi : i < rest.length),
        ∃ (mc : Module) (conns : List (String × Sparkle.IR.AST.Expr)),
          rest[i] = Stmt.inst mc.name s!"inst{off + 1 + i}_{mc.name}" conns := by
      intro i hi
      obtain ⟨mc', conns', h'⟩ := h (i + 1) (by rw [List.length_cons]; omega)
      have h'' : rest[i] = Stmt.inst mc'.name s!"inst{off + (i + 1)}_{mc'.name}" conns' := h'
      have e : off + (i + 1) = off + 1 + i := by omega
      rw [e] at h''
      exact ⟨mc', conns', h''⟩
    obtain ⟨hnd, hall⟩ := stmts_names rest (off + 1) hrest
    have hin : instNames (st :: rest) = s!"inst{off + 0}_{mc.name}" :: instNames rest :=
      congrArg (fun s : Stmt => instNames (s :: rest)) hst'
    rw [hin]
    refine ⟨List.nodup_cons.mpr ⟨fun hm => ?_, hnd⟩, fun x hx => ?_⟩
    · obtain ⟨j, nm, hj, he⟩ := hall _ hm
      have hinj : off + 0 = j := Tools.ShippingInstNames.instName_inj he
      omega
    · rcases List.mem_cons.mp hx with e | hx'
      · exact ⟨off + 0, mc.name, by omega, e⟩
      · obtain ⟨j, nm, hj, he⟩ := hall x hx'
        exact ⟨j, nm, by omega, he⟩

/-- **The instance names of the one-output closing's result are distinct**,
when the machine's body has no instance. (`closeInsts` does not check this:
it follows from the names `instStmt` builds.) -/
theorem closeInsts_instNames {nIn kI n : Nat} {portNames : List String}
    {insts : List (List Nat)} {children : List (Module × Design)} {m₀ : Module} {d₀ : Design}
    {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d))
    (h0 : instNames m₀.body = []) : (instNames m.body).Nodup := by
  obtain ⟨stmts, hperm, hs⟩ := closeInsts_stmts h
  have hnd : (instNames stmts).Nodup :=
    (stmts_names stmts 0 (fun i hi => by
      obtain ⟨mc, conns, he⟩ := hs i hi
      refine ⟨mc, conns, ?_⟩
      rw [Nat.zero_add]
      exact he)).1
  have hp : ((m₀.body ++ stmts).filterMap Sparkle.IR.Machine.instNameOf).Perm
      (m.body.filterMap Sparkle.IR.Machine.instNameOf) := hperm.filterMap _
  rw [Tools.ShippingChecksRaw.instNameOf_eq, Tools.ShippingChecksRaw.instNameOf_eq,
    instNames_append, h0, List.nil_append] at hp
  exact hp.nodup_iff.mp hnd

/-! ## A call's statement -/

/-- **What a call's instance statement is**: an instance of the child's
module; the call's wire is the transition's port at the call's position; the
child has ONE output port and no clock or reset input; every connection is
the output port's (to the call's wire) or an input port's (to an argument
wire, the port not the output port's name); the call's wire is no argument
wire. -/
theorem callStmt_parts {nIn kI n k : Nat} {portNames : List String} {args : List Nat}
    {mc : Module} {mn iname : String} {conns : List (String × Sparkle.IR.AST.Expr)}
    (h : CallStmt nIn kI n portNames k args mc (Stmt.inst mn iname conns)) :
    ∃ (outW : String) (argWs : List String) (outP : Port),
      mn = mc.name ∧ portNames[nIn + k]? = some outW ∧ mc.outputs = [outP] ∧
      (mc.inputs.any (fun p => p.name == "clk" || p.name == "rst")) = false ∧
      outW ∉ argWs ∧ outP.name ≠ "rst" ∧
      (∀ c ∈ conns, c = (outP.name, Sparkle.IR.AST.Expr.ref outW) ∨
        ∃ q ∈ mc.inputs, ∃ aw ∈ argWs,
          c = (q.name, Sparkle.IR.AST.Expr.ref aw) ∧ q.name ≠ outP.name) ∧
      (outP.name, Sparkle.IR.AST.Expr.ref outW) ∈ conns := by
  obtain ⟨outW, argWs, outP, iname', hout, hargs, houts, hclk, hlen, hnd, hne, hon, hrst, he⟩ := h
  obtain ⟨h1, h2, h3⟩ := Stmt.inst.inj he
  refine ⟨outW, argWs, outP, h1, hout, houts, hclk, hne, hrst, ?_, ?_⟩
  · intro c hc
    rw [h3] at hc
    rcases List.mem_append.mp hc with hc | hc
    · right
      obtain ⟨⟨q, aw⟩, hq, heq⟩ := List.mem_map.mp hc
      have hqin : q ∈ mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst") :=
        (List.of_mem_zip hq).1
      refine ⟨q, (List.mem_filter.mp hqin).1, aw, (List.of_mem_zip hq).2, heq.symm, fun e => ?_⟩
      apply hon
      rw [← e]
      exact List.mem_map.mpr ⟨q, hqin, rfl⟩
    · left
      exact List.mem_singleton.mp hc
  · rw [h3]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- **No instance of a body of call statements reads its own output.** -/
theorem noSelfRead_of_calls {ms : List Module} {body : List Stmt}
    (h : ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Stmt.inst mn iname conns ∈ body →
      ∃ (nIn kI n : Nat) (portNames : List String) (k : Nat) (args : List Nat) (mc : Module),
        moduleByName ms mc.name = some mc ∧
        CallStmt nIn kI n portNames k args mc (Stmt.inst mn iname conns)) :
    Tools.ShippingHierPremisesBase.noSelfRead (childMap ms) body = true := by
  unfold Tools.ShippingHierPremisesBase.noSelfRead
  rw [List.all_eq_true]
  intro st hst
  cases st with
  | inst mn iname conns =>
    obtain ⟨nIn, kI, n, portNames, k, args, mc, hfind, hcs⟩ := h mn iname conns hst
    obtain ⟨outW, argWs, outP, hmn, -, houts, -, hne, -, hall, -⟩ := callStmt_parts hcs
    have hc : childMap ms mn = some (mc, Sparkle.IR.RegDedup.declWidth mc) := by
      rw [hmn]
      exact congrArg (Option.map fun c => (c, Sparkle.IR.RegDedup.declWidth c)) hfind
    simp only [hc]
    rw [List.all_eq_true]
    intro cn hcn
    obtain ⟨nm, e⟩ := cn
    cases e with
    | ref w =>
      show (!(Tools.ShippingHierOpen.instOutWires mc.outputs conns).contains w) = true
      have hnot : w ∉ Tools.ShippingHierOpen.instOutWires mc.outputs conns := by
        intro hw
        have hcn' : (nm, Sparkle.IR.AST.Expr.ref w) ∈
            conns.filter (fun c => !(mc.outputs.map (·.name)).contains c.1) := hcn
        obtain ⟨hmem, hflt⟩ := List.mem_filter.mp hcn'
        rcases hall _ hmem with e1 | ⟨q, -, aw, haw, e1, -⟩
        · -- the output connection is not an input connection
          have hnm : nm = outP.name := congrArg Prod.fst e1
          have hflt' : (!(mc.outputs.map (·.name)).contains nm) = true := hflt
          rw [houts, hnm] at hflt'
          simp at hflt'
        · have hw2 : Sparkle.IR.AST.Expr.ref w = Sparkle.IR.AST.Expr.ref aw :=
            congrArg Prod.snd e1
          have hwaw : w = aw := Sparkle.IR.AST.Expr.ref.inj hw2
          obtain ⟨p, hp, hpc⟩ := Tools.ShippingOutsExtractedParts.instOutWires_port hw
          rw [houts] at hp
          have hpe : p = outP := List.mem_singleton.mp hp
          rw [hpe] at hpc
          rcases hall _ hpc with e2 | ⟨q2, -, aw2, -, e2, hqo2⟩
          · have hw3 : Sparkle.IR.AST.Expr.ref w = Sparkle.IR.AST.Expr.ref outW :=
              congrArg Prod.snd e2
            have hwo : w = outW := Sparkle.IR.AST.Expr.ref.inj hw3
            apply hne
            rw [← hwo, hwaw]
            exact haw
          · exact hqo2 (congrArg Prod.fst e2).symm
      simpa [List.contains_eq_mem] using hnot
    | _ => rfl
  | _ => rfl

/-! ## The children's checks -/

/-- An assignment-only body has no memory statement. -/
theorem noMem_of_assigns {body : List Stmt}
    (h : body.all Sparkle.IR.RegDedup.isAssign = true) :
    Tools.ShippingMachineShipsHier.noMem body = true := by
  unfold Tools.ShippingMachineShipsHier.noMem
  rw [List.all_eq_true] at h ⊢
  intro st hst
  have h1 := h st hst
  cases st with
  | memory => exact Tools.ShippingChecksDerived.ff_absurd h1
  | _ => rfl

/-- **Combinational children are local children**: `kidsComb` (assignments
only, reads closed over the input ports, outputs written, no output an
input, inputs wired) contains `kidsLocal` (no memory and the middle three). -/
theorem kidsLocal_of_comb {ms : List Module} {body : List Stmt}
    (h : Tools.ShippingMachineDepthH.kidsComb ms body = true) :
    Tools.ShippingHierOptRunH.kidsLocal ms body = true := by
  unfold Tools.ShippingMachineDepthH.kidsComb at h
  unfold Tools.ShippingHierOptRunH.kidsLocal
  rw [List.all_eq_true] at h ⊢
  intro st hst
  have h1 := h st hst
  cases st with
  | inst mn iname conns =>
    cases hm : moduleByName ms mn with
    | none => simp [hm] at h1
    | some c =>
      simp only [hm, Bool.and_eq_true] at h1 ⊢
      obtain ⟨⟨⟨⟨hasg, hcl⟩, hw⟩, hio⟩, -⟩ := h1
      exact ⟨⟨⟨noMem_of_assigns hasg, hcl⟩, hw⟩, hio⟩
  | _ => rfl

end Tools.ShippingOneOutClose
