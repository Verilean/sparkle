import Tools.ShippingMachineLinkedT
import Tools.ShippingHierMem
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # A memory call's instance inside the composed machine

`machine_linkedT` asks of every instance its child's own run on any
environments whose argument wires carry the source's argument values and
whose output wires carry the call's values. For a memory call the child is
the built memory module (`MachMemory.memModule`, the `MachineWired` clause),
its four argument wires carry the operand Signals, its one output wire the
source read: `memChild_run` is that run. This file states it on the call
group's connections (`connsG`). -/
namespace Tools.ShippingMachineMemLinked
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierarchySoundness Tools.ShippingHierState
open Tools.ShippingMachineLinkedT Tools.ShippingHierMem
open Sparkle.IR.Machine (moduleByName)
open Tools.ShippingMachineLinked (childMap)

/-- The memory child's connections from a call group (`connsG`): the four
operands' wires, the clock and reset, the read on `out`. -/
theorem memConnsG (cb : Bool) (aw dw : Nat) (a0 a1 a2 a3 ow : String) (k : Nat) :
    connsG (Sparkle.Compiler.MachMemory.memModule cb aw dw).1 [a0, a1, a2, a3] [(k, "out")] [ow] =
      [("wa", .ref a0), ("wd", .ref a1), ("we", .ref a2), ("ra", .ref a3),
       ("clk", .ref "clk"), ("rst", .ref "rst"), ("out", .ref ow)] := rfl

/-- The source read of a memory call: combinational (`memoryComboRead`) or
synchronous (`memory`). -/
def memRead {D : DomainConfig} {aw dw : Nat} (cb : Bool) (A : Signal D (BitVec aw))
    (Dd : Signal D (BitVec dw)) (E : Signal D Bool) (R : Signal D (BitVec aw)) :
    Signal D (BitVec dw) :=
  match cb with
  | true => Signal.memoryComboRead A Dd E R
  | false => Signal.memory A Dd E R

/-- **A memory call's instance runs as the source read.** -/
theorem memInst_run {D : DomainConfig} {cb : Bool} {aw dw : Nat} (we : WEnv) (argWs : List String)
    (outs : List (Nat × String)) (outWs : List String) (Pw : Nat → Env) (T : Nat) (kid : KidState)
    (hargs : argWs.length = 4) (houts : outs.map (·.2) = ["out"]) (houtWs : outWs.length = 1)
    (hm0 : ∀ n i, kid.mems n i = 0) (hst0 : kid.st "out_rdata" = 0)
    (A : Signal D (BitVec aw)) (Dd : Signal D (BitVec dw)) (E : Signal D Bool)
    (R : Signal D (BitVec aw))
    (hA : ∀ t, t < T → ∀ w, argWs[0]? = some w → Pw t w = (A.val (T - 1 - t)).toNat)
    (hD : ∀ t, t < T → ∀ w, argWs[1]? = some w → Pw t w = (Dd.val (T - 1 - t)).toNat)
    (hE : ∀ t, t < T → ∀ w, argWs[2]? = some w → Pw t w = (if E.val (T - 1 - t) then 1 else 0))
    (hR : ∀ t, t < T → ∀ w, argWs[3]? = some w → Pw t w = (R.val (T - 1 - t)).toNat)
    (hO : ∀ t, t < T → ∀ w, outWs[0]? = some w →
      Pw t w = ((memRead cb A Dd E R).val (T - 1 - t)).toNat) :
    let mc := (Sparkle.Compiler.MachMemory.memModule cb aw dw).1
    ∃ cenvs, runModule we mc.body
        (fun t cst => connEnvS (inConns mc.outputs (connsG mc argWs outs outWs)) (Pw t) cst)
        T kid.st kid.mems = some cenvs ∧
      ∀ j, j < T → ∀ p ∈ mc.outputs, ∀ w, (connsG mc argWs outs outWs).lookup p.name = some (.ref w) →
        (cenvs[j]?).map (· p.name) = some (Pw (T - 1 - j) w) := by
  intro mc
  match argWs, outs, outWs, hargs, houts, houtWs with
  | [a0, a1, a2, a3], [(k, f)], [ow], _, houts, _ =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at houts
    subst houts
    obtain ⟨cenvs, hrun, hobs⟩ : ∃ cenvs, runModule we mc.body
        (fun t cst => connEnvS (inConns mc.outputs (connsG mc [a0, a1, a2, a3] [(k, "out")] [ow]))
          (Pw t) cst) T kid.st kid.mems = some cenvs ∧
        ∀ j, j < T → (cenvs[j]?).map (· "out") = some (Pw (T - 1 - j) ow) := by
      cases cb with
      | true =>
        exact memChild_run (D := D) (aw := aw) (dw := dw) we Pw T
          (connsG mc [a0, a1, a2, a3] [(k, "out")] [ow]) a0 a1 a2 a3 ow rfl rfl rfl rfl A Dd E R
          (fun t ht => hA t ht a0 rfl) (fun t ht => hD t ht a1 rfl) (fun t ht => hE t ht a2 rfl)
          (fun t ht => hR t ht a3 rfl) (fun t ht => hO t ht ow rfl) kid.st kid.mems hm0
      | false =>
        exact memSyncChild_run (D := D) (aw := aw) (dw := dw) we Pw T
          (connsG mc [a0, a1, a2, a3] [(k, "out")] [ow]) a0 a1 a2 a3 ow rfl rfl rfl rfl rfl
          A Dd E R
          (fun t ht => hA t ht a0 rfl) (fun t ht => hD t ht a1 rfl) (fun t ht => hE t ht a2 rfl)
          (fun t ht => hR t ht a3 rfl) (fun t ht => hO t ht ow rfl) kid.st hst0 kid.mems hm0
    refine ⟨cenvs, hrun, fun j hj p hp w hw => ?_⟩
    have hp' : p = { name := "out", ty := .bitVector dw } := by
      simpa [mc, Sparkle.Compiler.MachMemory.memModule] using hp
    subst hp'
    rw [memConnsG] at hw
    simp (config := { decide := true }) [List.lookup] at hw
    subst hw
    exact hobs j hj

theorem fields_out {fs : List String} (hne : fs ≠ []) (hnd : fs.Nodup)
    (hall : ∀ f ∈ fs, f = "out") : fs = ["out"] := by
  match fs, hne, hnd with
  | [f], _, _ => rw [hall f (by simp)]
  | f :: g :: rest, _, hnd =>
    have hf := hall f (by simp)
    have hg := hall g (by simp)
    exact absurd (by rw [hf, hg] : f = g) (fun he => (List.nodup_cons.mp hnd).1 (by simp [he]))

/-- **Memory children satisfy the composition's premise.** For a machine all
of whose calls are memory reads (each call: the built combinational-read
memory module, four argument `let`s observed as the operand Signals, the
call's value the source read), every instance's child runs as
`machine_linkedT` asks, from zeroed memories. -/
theorem mem_hchild {D : DomainConfig} (shape : Sparkle.Compiler.Elab.MachineShape)
    (dsn : Design) (body : List Stmt) (lsrc : List (Nat → Nat)) (nL : Nat)
    (bsI : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)) (kD : Nat)
    (extB : Nat → Signal D Bool) (ext : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (names : List String) (offA offO : Nat) (T : Nat) (kids : String → KidState)
    (hm0 : ∀ iname n a, (kids iname).mems n a = 0)
    (hst0 : ∀ iname, (kids iname).st "out_rdata" = 0) :
    ∀ (args : List Nat) (outs : List (Nat × String)) (mc : Module) (iname : String)
      (argWs outWs : List String),
      args.mapM (fun j => names[offA + j]?) = some argWs →
      outs.mapM (fun (k, _) => names[offO + k]?) = some outWs →
      moduleByName dsn.modules mc.name = some mc →
      Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ body →
      outs ≠ [] → (outs.map (·.2)).Nodup →
      (outs.map (·.2)).all (fun f => mc.outputs.any (·.name == f)) = true →
      (∀ e ∈ outs, (shape.insts.map (·.2.1))[e.1]? = some args ∧
        shape.instFields.getD e.1 "" = e.2 ∧
        ∀ c md, (shape.insts.map (·.1))[e.1]? = some c →
          (shape.instOrigins.getD e.1 .ord).child? = some md → mc = md.1) →
      -- the calls of this instance are memory reads
      (∀ e ∈ outs, ∀ c, (shape.insts.map (·.1))[e.1]? = some c →
      ∃ (cb : Bool) (aw dw : Nat) (A : Signal D (BitVec aw)) (Dd : Signal D (BitVec dw)) (E : Signal D Bool)
        (R : Signal D (BitVec aw)) (l0 l1 l2 l3 : Nat),
        (shape.instOrigins.getD e.1 .ord).child? =
          some (Sparkle.Compiler.MachMemory.memModule cb aw dw) ∧
        (shape.insts.map (·.2.1))[e.1]? = some [l0, l1, l2, l3] ∧
        lsrc[l0]? = some (fun j => (A.val j).toNat) ∧ l0 < nL ∧
        lsrc[l1]? = some (fun j => (Dd.val j).toNat) ∧ l1 < nL ∧
        lsrc[l2]? = some (fun j => if E.val j then 1 else 0) ∧ l2 < nL ∧
        lsrc[l3]? = some (fun j => (R.val j).toNat) ∧ l3 < nL ∧
        (bsI[e.1]?.map (·.2)) = some (.bits dw) ∧
        ∀ j, (ext (kD + e.1) dw).val j = (memRead cb A Dd E R).val j) →
      ∀ Pw : Nat → Env,
        (∀ t, Pw t "rst" = 0) → (∀ t, Pw t "clk" = 0) →
        (∀ t, t < T → ∀ (q : Nat) (hq : q < args.length) (w : String) (g : Nat → Nat),
          argWs[q]? = some w → lsrc[args[q]]? = some g → args[q] < nL →
          Pw t w = g (T - 1 - t)) →
        (∀ t, t < T → ∀ (idx : Nat) (e : Nat × String) (w : String), outs[idx]? = some e →
          outWs[idx]? = some w →
          Pw t w = Tools.ShippingMachineEntry.posEnc (fun p => (extB p).val (T - 1 - t))
            (fun p n => (ext p n).val (T - 1 - t)) (kD + e.1)
            ((bsI[e.1]?.map (·.2)).getD .domain)) →
        ∃ cenvs, runModule (Sparkle.IR.RegDedup.declWidth mc) mc.body
            (fun t cst => connEnvS (inConns mc.outputs (connsG mc argWs outs outWs)) (Pw t) cst)
            T (kids iname).st (kids iname).mems = some cenvs ∧
          ∀ j, j < T → ∀ p ∈ mc.outputs, ∀ w,
            (connsG mc argWs outs outWs).lookup p.name = some (.ref w) →
            (cenvs[j]?).map (· p.name) = some (Pw (T - 1 - j) w) := by
  intro args outs mc iname argWs outWs hargsW hout _ _ hne hfnd hfields hall hmemF Pw _ _ hPa hPo
  obtain ⟨e, he⟩ : ∃ e, e ∈ outs := by
    cases outs with
    | nil => exact absurd rfl hne
    | cons e _ => exact ⟨e, List.mem_cons_self⟩
  obtain ⟨hargs, _, hmd⟩ := hall e he
  have hk : e.1 < (shape.insts.map (·.1)).length := by
    have := (List.getElem?_eq_some_iff.mp hargs).1; simpa using this
  obtain ⟨cb, aw, dw, A, Dd, E, R, l0, l1, l2, l3, hmc, hla, h0, h0l, h1, h1l, h2, h2l, h3, h3l, hty,
    hext⟩ := hmemF e he _ (List.getElem?_eq_getElem hk)
  have hmc' := hmd _ _ (List.getElem?_eq_getElem hk) hmc
  subst hmc'
  rw [hla, Option.some.injEq] at hargs
  subst hargs
  -- one output field, `out`
  have hfo : outs.map (·.2) = ["out"] := by
    apply fields_out (by simpa using hne) hfnd
    intro f hf
    have := List.all_eq_true.mp hfields f hf
    simp only [Sparkle.Compiler.MachMemory.memModule, List.any_cons, List.any_nil, Bool.or_false,
      beq_iff_eq] at this
    exact this.symm
  obtain ⟨hlo, _⟩ := Tools.ShippingMachineInst.mapM_some _ outs outWs hout
  obtain ⟨hla', _⟩ := Tools.ShippingMachineInst.mapM_some _ _ argWs hargsW
  have hol : outs.length = 1 := by simpa using congrArg List.length hfo
  have he0 : outs[0]? = some e := by
    match outs, hol, he with
    | [e'], _, he => simp at he; subst he; rfl
  refine memInst_run (D := D) (cb := cb) (aw := aw) (dw := dw) _ argWs outs outWs Pw T (kids iname)
    (by rw [hla']; rfl) hfo (by omega) (hm0 iname) (hst0 iname) A Dd E R ?_ ?_ ?_ ?_ ?_
  · intro t ht w hw; exact hPa t ht 0 (by simp) w _ hw h0 h0l
  · intro t ht w hw; exact hPa t ht 1 (by simp) w _ hw h1 h1l
  · intro t ht w hw; exact hPa t ht 2 (by simp) w _ hw h2 h2l
  · intro t ht w hw; exact hPa t ht 3 (by simp) w _ hw h3 h3l
  · intro t ht w hw
    rw [hPo t ht 0 e w he0 hw, hty]
    show ((ext (kD + e.1) dw).val (T - 1 - t)).toNat = _
    rw [hext]

open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge in
open Sparkle.IR.Machine Sparkle.Compiler.Elab in
/-- **A machine whose calls are memory reads, composed with its memories.**
From the open endpoint (`MachineTraceLB`): the STATEFUL linked run of the
emitted module — each memory instance stepping its own memory, from zero —
seeded with the declaration's own inputs only, shows the source, given per
call the operand Signals the `let`s observe and the call's value as their
source read. -/
theorem machine_linkedT_mem {declName : Name} {d : MachineData} {m : Module} {dsn : Design}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (h : MachineTraceLB declName d m dsn dom src ext extB lsrc)
    (hfe : d.shape.instFields ≠ [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hI : ∀ b ∈ d.bsIn.drop kD, b.2 ≠ .domain)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (hcalls : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k c,
      (d.shape.insts.map (·.1))[k]? = some c →
      ∃ (cb : Bool) (aw dw : Nat) (A : Signal (dom i) (BitVec aw)) (Dd : Signal (dom i) (BitVec dw))
        (E : Signal (dom i) Bool) (R : Signal (dom i) (BitVec aw)) (l0 l1 l2 l3 : Nat),
        (d.shape.instOrigins.getD k .ord).child? =
          some (Sparkle.Compiler.MachMemory.memModule cb aw dw) ∧
        (d.shape.insts.map (·.2.1))[k]? = some [l0, l1, l2, l3] ∧
        (lsrc i bools bits)[l0]? = some (fun j => (A.val j).toNat) ∧ l0 < d.ls.length ∧
        (lsrc i bools bits)[l1]? = some (fun j => (Dd.val j).toNat) ∧ l1 < d.ls.length ∧
        (lsrc i bools bits)[l2]? = some (fun j => if E.val j then 1 else 0) ∧ l2 < d.ls.length ∧
        (lsrc i bools bits)[l3]? = some (fun j => (R.val j).toNat) ∧ l3 < d.ls.length ∧
        ((d.bsIn.drop kD)[k]?.map (·.2)) = some (.bits dw) ∧
        ∀ j, (ext i bools bits (kD + k) dw).val j = (memRead cb A Dd E R).val j) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = d.ss.length ∧
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
        (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
        (kids : String → KidState),
        (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
          (fun j => (extB i bools bits j).val (T - 1 - t))
          (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
        (∀ t st r, r ∈ regs → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        -- the memories (arrays and read latches) start zeroed
        (∀ iname n a, (kids iname).mems n a = 0) → (∀ iname, (kids iname).st "out_rdata" = 0) →
        ∃ envs, runModuleT (Tools.ShippingEntrySoundness.weOf m) (childMap dsn.modules) m.body
            seed T st0 mems kids = some envs ∧
          envs.length = T ∧
          ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
            (envs[j]'hj) o.name = f j := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ :=
    machine_linkedT h hfe kD hkD hI hIlen hSL hSlen hLlen hNIn
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit hm0 hst0
  exact H i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit
    (fun args outs mc iname argWs outWs h1 h2 h3 h4 h5 h6 h7 h8 =>
      mem_hchild d.shape dsn m.body (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD
        (extB i bools bits) (ext i bools bits) _ _ _ T kids hm0 hst0 args outs mc iname argWs
        outWs h1 h2 h3 h4 h5 h6 h7 h8 (fun e _ c hc => hcalls i bools bits e.1 c hc))

end Tools.ShippingMachineMemLinked
