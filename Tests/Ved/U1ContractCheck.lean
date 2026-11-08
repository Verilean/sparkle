import Tools.VedU1Contract
import Tools.VedStrictAudit
import Tests.Ved.PilotB0Fixture

/-!
# Checks for the U1 contract (Tools/VedU1Contract.lean), rev 3

Two kinds of records, kept apart:
* KERNEL FACTS: `example … := by decide` and `theorem`s.  The kernel checks
  them (no `native_decide`).
* EVALUATION OBSERVATIONS: `#guard` lines (the compiled evaluator runs the
  `Decidable` instance; the kernel does not check them).  Used only for the
  real artifact `pilotB0`, whose size makes kernel `decide` unattractive.

Contents:
1. the toy declaration `toyDelay`, its table READ FROM ITS TYPE
   (`ved_table%`), the kernel binding of the table to the declaration
   (`toyDelay : toyTable.Ty`), the module, the contract;
2. P1-A controls: another declaration's table, merged inputs, a missing
   output, a width mismatch (and the module mutations of rev 2), all
   rejected by `decide`;
3. the FULL statement `U1Stmt toyC toyMod toyDelay`, proved structurally for
   every input stream in range, every clock stream, every run length; strict
   audit of it;
4. `pilotB0` observations (`#guard`).
-/

namespace Tests.Ved.U1ContractCheck

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract

/-! ## 1. The toy -/

/-- The toy declaration: a one-cycle delay. -/
def toyDelay (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  Signal.register 0 x

/-- The table, read from `toyDelay`'s TYPE (not from any module). -/
def toyTable : DeclTable := ved_table% toyDelay

example : toyTable = { binders := ["x"], ins := [.bv 4], out := .leaf (.bv 4) } := by decide

/-- Kernel binding: the declaration has the table's type. -/
def toyBound : toyTable.Ty := toyDelay

/-- A module of the `synthesizeCombinational` shape (data inputs, then clk, rst; no
wire for clk/rst/out). -/
def toyMod : Module :=
  { name := "toyDelay",
    inputs := [⟨"_gen_x", .bitVector 4⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩],
    outputs := [⟨"out", .bitVector 4⟩],
    wires := [⟨"_gen_x", .bitVector 4⟩, ⟨"_gen_r", .bitVector 4⟩],
    body := [.register "_gen_r" "clk" ("rst", .synchronous) (.ref "_gen_x") 0,
             .assign "out" (.ref "_gen_r")] }

def toyC : Contract := contractOf toyTable ["out"] (some ("clk", "rst")) toyMod

example : toyC.dataInputs = [⟨"_gen_x", .bitVector 4⟩] ∧ toyC.outputs = [⟨"out", .bitVector 4⟩] ∧
    toyC.inits = [("_gen_r", 0)] := by decide

example : CorrStmt toyC := by decide
example : ShapeStmt toyC toyMod := by decide
example : WidthStmt toyC toyMod := by decide
-- the first draft's width clause rejects even the toy (clk/rst/out have no wire)
example : ¬ WidthStmtDraft1 toyMod := by decide

/-! ## 2. P1-A controls (kernel-checked rejections) -/

/-- Another declaration: two inputs. -/
def toyAdd (a b : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4) :=
  (· + ·) <$> a <*> b
/-- Another declaration: 8-bit delay (width mismatch with `toyMod`). -/
def toyDelay8 (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  Signal.register 0 x
/-- Another declaration: two output projections. -/
def toyPair (x : Signal defaultDomain (BitVec 4)) : Signal defaultDomain (BitVec 4 × Bool) :=
  (fun v => (v, v == 0)) <$> Signal.register 0 x

example : ved_table% toyAdd = { binders := ["a", "b"], ins := [.bv 4, .bv 4], out := .leaf (.bv 4) } := by decide
example : ved_table% toyPair =
    { binders := ["x"], ins := [.bv 4], out := .pair (.leaf (.bv 4)) (.leaf .bit) } := by decide

-- the tables of the other declarations differ from toyDelay's, so their
-- `U1Stmt _ _ f` does not even typecheck at `toyC` (f : toyC.table.Ty)
example : ved_table% toyDelay8 ≠ toyTable ∧ ved_table% toyAdd ≠ toyTable ∧
    ved_table% toyPair ≠ toyTable := by decide

-- (a) another declaration's table against toyMod: rejected (arity / width)
example : ¬ ShapeCore (contractOf (ved_table% toyAdd) ["out"] (some ("clk", "rst")) toyMod) toyMod := by decide
example : ¬ ShapeCore (contractOf (ved_table% toyDelay8) ["out"] (some ("clk", "rst")) toyMod) toyMod := by decide

-- (b) two inputs merged under one name: the module that feeds `toyAdd`'s
-- `a` and `b` from ONE stream `_gen_a`.  Naming both binders `_gen_a`
-- violates injectivity; the naming rule gives `_gen_b`, which the module
-- lacks (arity).
def mergedMod : Module :=
  { toyMod with
    name := "toyAdd",
    inputs := [⟨"_gen_a", .bitVector 4⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩],
    wires := [⟨"_gen_a", .bitVector 4⟩],
    body := [.assign "out" (.op .add [.ref "_gen_a", .ref "_gen_a"])] }
example : ¬ CorrStmt { contractOf (ved_table% toyAdd) ["out"] (some ("clk", "rst")) mergedMod with
    inNames := ["_gen_a", "_gen_a"] } := by decide
example : ¬ ShapeCore (contractOf (ved_table% toyAdd) ["out"] (some ("clk", "rst")) mergedMod) mergedMod := by decide
-- a duplicated port list does not help: the contract still fails injectivity
example : ¬ CorrStmt { contractOf (ved_table% toyAdd) ["out"] (some ("clk", "rst"))
    { mergedMod with inputs := [⟨"_gen_a", .bitVector 4⟩, ⟨"_gen_a", .bitVector 4⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩] } with
    inNames := ["_gen_a", "_gen_a"] } := by decide

-- (c) a missing output: `toyPair` has two projections; a module with one
-- output port fails coverage (one name) or the output shape (two names)
def pairMod1 : Module := { toyMod with name := "toyPair" }
example : ¬ CorrStmt (contractOf (ved_table% toyPair) ["out"] (some ("clk", "rst")) pairMod1) := by decide
example : ¬ ShapeCore (contractOf (ved_table% toyPair) ["out_0", "out_1"] (some ("clk", "rst")) pairMod1) pairMod1 := by decide
example : CorrStmt (contractOf (ved_table% toyPair) ["out_0", "out_1"] (some ("clk", "rst")) pairMod1) := by decide

-- (d) width mismatch: the right table, a module with a 5-bit input or 8-bit output
example : ¬ ShapeCore toyC { toyMod with
    inputs := [⟨"_gen_x", .bitVector 5⟩, ⟨"clk", .bit⟩, ⟨"rst", .bit⟩] } := by decide
example : ¬ ShapeCore toyC { toyMod with outputs := [⟨"out", .bitVector 8⟩] } := by decide
-- … or the input's wire declaration (what `declWidth` reads) at another width
example : ¬ WidthStmt toyC { toyMod with
    wires := [⟨"_gen_x", .bitVector 5⟩, ⟨"_gen_r", .bitVector 4⟩] } := by decide

-- (e) clk/rst separation: an output named like the clock
example : ¬ CorrStmt { toyC with outNames := ["clk"] } := by decide

-- rev 2 module mutations against the same contract (still rejected)
example : ¬ ShapeStmt toyC { toyMod with
    body := [.register "_gen_r" "clk" ("rst", .synchronous) (.ref "_gen_x") 1,
             .assign "out" (.ref "_gen_r")] } := by decide          -- init value
example : ¬ ShapeStmt toyC { toyMod with
    outputs := [⟨"out", .bitVector 4⟩, ⟨"out2", .bit⟩] } := by decide   -- extra output
example : ¬ ShapeStmt toyC { toyMod with
    body := [.register "_gen_r" "clk" ("_gen_x", .synchronous) (.ref "_gen_x") 0,
             .assign "out" (.ref "_gen_r")] } := by decide          -- reset not the rst input
example : ¬ ShapeStmt toyC { toyMod with
    inputs := [⟨"clk", .bit⟩, ⟨"rst", .bit⟩, ⟨"_gen_x", .bitVector 4⟩] } := by decide  -- input order

/-! ## 3. The full statement for `toyDelay` -/

/-- The declaration's output value at time `t`, as a number. -/
def toyR (ins : Nat → String → Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => ins t "_gen_x" % 16

theorem toy_src (ins : Nat → String → Nat) (t : Nat) :
    srcOf toyC toyDelay ins "out" t = toyR ins t := by
  cases t with
  | zero => rfl
  | succ t =>
    show (BitVec.ofNat 4 (ins t "_gen_x")).toNat = ins t "_gen_x" % 16
    simp [BitVec.toNat_ofNat]

/-- One cycle of `toyMod.body` from any environment. -/
theorem toy_step (env0 : Env) (mems : MEnv) :
    stepModule (declWidth toyMod) toyMod.body env0 mems =
      some ((fun n => if n = "out" then env0 "_gen_r" else env0 n),
            [("_gen_r", if env0 "rst" ≠ 0 then encodeInit 0 4 else mask 4 (env0 "_gen_x"))],
            mems) := by
  have hw : declWidth toyMod "_gen_r" = 4 := by decide
  have hb : toyMod.body = [.register "_gen_r" "clk" ("rst", .synchronous) (.ref "_gen_x") 0,
      .assign "out" (.ref "_gen_r")] := rfl
  rw [hb]
  simp only [stepModule, evalAssigns, regNexts, memNexts, evalExpr, hw]
  by_cases h : env0 "rst" = 0 <;> simp [h]

/-- The run, generalised: a `k`-cycle tail starting at stream time `s` of a
`K`-cycle run, from any state holding the declaration's value at `s`. -/
theorem toy_run (ins : Nat → String → Nat) (hrst : ∀ t, ins t "rst" = 0) (K : Nat) :
    ∀ k s (st : String → Nat) (mems : MEnv), s + k = K → st "_gen_r" = toyR ins s →
      ∃ envs, runModule (declWidth toyMod) toyMod.body (seedFwd toyMod K ins) k st mems = some envs ∧
        ∀ i, i < k → ∃ env, envs[i]? = some env ∧ env "out" = toyR ins (s + i) := by
  intro k
  induction k with
  | zero => intro s st mems _ _; exact ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro s st mems hK hst
    have hs : K - 1 - k = s := by omega
    have hseed : ∀ n, seedFwd toyMod K ins k st n =
        (if n = "_gen_x" ∨ n = "clk" ∨ n = "rst" then ins s n else st n) := by
      intro n; simp [seedFwd, toyMod, hs]
    let st' := applyNexts st [("_gen_r", mask 4 (ins s "_gen_x"))]
    have hst' : st' "_gen_r" = toyR ins (s + 1) := by
      simp [st', applyNexts, toyR, mask]
    obtain ⟨rest, hrun, hrest⟩ := ih (s + 1) st' mems (by omega) hst'
    have hstep := toy_step (seedFwd toyMod K ins k st) mems
    have hr : seedFwd toyMod K ins k st "rst" = 0 := by rw [hseed]; simp [hrst]
    have hx : seedFwd toyMod K ins k st "_gen_x" = ins s "_gen_x" := by rw [hseed]; simp
    have hg : seedFwd toyMod K ins k st "_gen_r" = st "_gen_r" := by rw [hseed]; simp
    refine ⟨(fun n => if n = "out" then seedFwd toyMod K ins k st "_gen_r"
        else seedFwd toyMod K ins k st n) :: rest, ?_, ?_⟩
    · rw [runModule_first, hstep]
      simp only [hr, hx, ne_eq, not_true_eq_false, if_false]
      show (runModule (declWidth toyMod) toyMod.body (seedFwd toyMod K ins) k st' mems).bind _ = _
      rw [hrun]; rfl
    · intro i hi
      cases i with
      | zero => exact ⟨_, rfl, by simp [hg, hst]⟩
      | succ i =>
        obtain ⟨env, he, hv⟩ := hrest i (by omega)
        exact ⟨env, by simpa using he, by rw [hv]; congr 1; omega⟩

theorem toyDelay_outputs : OutputsStmt toyC toyMod toyDelay := by
  intro ins hok K
  have hrst : ∀ t, ins t "rst" = 0 := fun t => hok.2 t ("clk", "rst") rfl
  have h0 : st0 toyC toyMod "_gen_r" = toyR ins 0 := by
    show st0 toyC toyMod "_gen_r" = 0; decide
  obtain ⟨envs, hrun, hall⟩ := toy_run ins hrst K K 0 (st0 toyC toyMod) (fun _ _ => 0) (by omega) h0
  refine ⟨envs, hrun, ?_⟩
  intro t ht o ho
  have ho' : o = ⟨"out", .bitVector 4⟩ := by
    have : toyC.outputs = [⟨"out", .bitVector 4⟩] := by decide
    rw [this] at ho; simpa using ho
  subst ho'
  obtain ⟨env, he, hv⟩ := hall t ht
  exact ⟨env, he, by rw [hv, toy_src]; simp⟩

/-- The fixed contract and the outputs, for `toyDelay`: no run premise, every
data stream in range, EVERY clock stream, reset held 0, every run length. -/
theorem toyDelay_u1 : U1Stmt toyC toyMod toyDelay :=
  ⟨by decide, by decide, by decide, toyDelay_outputs⟩

/-- info: VED STRICT OK Tests.Ved.U1ContractCheck.toyDelay_u1: [Classical.choice, Quot.sound, propext] -/
#guard_msgs in
#ved_strict_audit toyDelay_u1

/-- P1-B: the clock is free.  A toggling clock stream satisfies `InputsOk`,
so `toyDelay_outputs` applies to it (nothing fixes clk = 0). -/
theorem toy_inputsOk_toggling_clock :
    InputsOk toyC toyMod (fun t n => if n = "clk" then t % 2 else 0) := by
  refine ⟨fun t p hp => ?_, fun t kr hkr => ?_⟩
  · have h : toyC.dataInputs = [⟨"_gen_x", .bitVector 4⟩] := by decide
    rw [h] at hp
    simp only [List.mem_singleton] at hp
    subst hp
    show (if "_gen_x" = "clk" then t % 2 else 0) < 2 ^ declWidth toyMod "_gen_x"
    simp only [show ("_gen_x" = "clk") = False by decide, if_false]
    exact Nat.two_pow_pos _
  · have h : toyC.clkRst = some ("clk", "rst") := rfl
    rw [h] at hkr
    cases hkr
    rfl

/-! ## 4. The real artifact `pilotB0` (EVALUATION OBSERVATIONS, `#guard`) -/

set_option linter.unusedVariables false in
/-- Same TYPE as `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte`
(copied: that module's olean is not built here).  Only the type is read. -/
def pilotSig (rxByte : Signal defaultDomain (BitVec 8))
    (rxValid sopTlp : Signal defaultDomain Bool)
    (dataDword : Signal defaultDomain (BitVec 32))
    (cplId : Signal defaultDomain (BitVec 16)) : Signal defaultDomain (BitVec 8) :=
  rxByte

open Tests.Ved.PilotB0Fixture in
def pilotC : Contract := contractOf (ved_table% pilotSig) ["out"] (some ("clk", "rst")) pilotB0

open Tests.Ved.PilotB0Fixture in
#guard (pilotB0.wires.find? (·.name == "clk")).isNone &&
       (pilotB0.wires.find? (·.name == "rst")).isNone &&
       (pilotB0.wires.find? (·.name == "out")).isNone

#guard decide (CorrStmt pilotC)

open Tests.Ved.PilotB0Fixture in
#guard decide (ShapeCore pilotC pilotB0)

-- pilotB0 has two child instances: outside the v1 scope (not a width rejection)
open Tests.Ved.PilotB0Fixture in
#guard (pilotB0.body.filter (fun s => match s with | .inst .. => true | _ => false)).length == 2 &&
       !memInstFree pilotB0.body

open Tests.Ved.PilotB0Fixture in
#guard decide (WidthStmt pilotC pilotB0)

open Tests.Ved.PilotB0Fixture in
#guard !decide (WidthStmtDraft1 pilotB0)

end Tests.Ved.U1ContractCheck
