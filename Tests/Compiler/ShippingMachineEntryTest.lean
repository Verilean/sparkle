import Lean
import Sparkle.Core.CircuitDo
import Tools.ShippingMachineDenote
import Tools.ShippingMachineSource
import IP.Bus.LINHW

/-! A general `circuit do` on the certified route.

A `circuit do` with any number of register slots — Bool and BitVec slots of
any widths, a result that is one Signal, directly or as one field of a
structure — is compiled as its TRANSITION through the certified
combinational harness and closed into registers
(`Sparkle.Compiler.Elab.machineShape?`, `synthesizeMachineCertified`).

* The route is taken by declarations the two certified gates refuse, and
  only by those; the emitted module has one register per slot.
* For every declaration here the emitted module is simulated with the IR
  semantics against the source Signal (the library's own `Signal.loop`).
* `linHW_execution` certifies an IP declaration ITSELF, with its structure
  result (two output ports); `lin_execution` its field-projecting wrapper.
* `mThree_execution` is the end-to-end theorem for a three-slot machine with
  heterogeneous slots: a run of the real synthesis entry, the emitted module
  run for any number of cycles, and the value of the SOURCE declaration at
  every cycle.

The emitted text differs from the legacy lowering of `circuit do`; the
function is the same, which is what is checked and proved. -/
namespace Sparkle.Tests.Compiler.ShippingMachineEntryTest
open Lean Elab Command Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core.Circuit
open Tools.ShippingEntrySoundness Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineClose Tools.ShippingMachineEntry Tools.ShippingMachineSource

/-! ## Declarations -/

section
variable {dom : DomainConfig}

/-- Three slots of two kinds; one slot is never written (it holds). -/
def mThree (en : Signal dom Bool) (d : Signal dom (BitVec 4)) : Signal dom (BitVec 4) :=
  circuit do
    let a ← Signal.reg (0#4)
    let b ← Signal.reg (3#4)
    let g ← Signal.reg true
    a <~ Signal.mux en ((a : Signal dom (BitVec 4)) + d) (b : Signal dom (BitVec 4))
    g <~ Signal.beq (a : Signal dom (BitVec 4)) d
    return Signal.mux (g : Signal dom Bool) (a : Signal dom (BitVec 4)) (b : Signal dom (BitVec 4))

structure TwoOut (dom : DomainConfig) where
  cnt : Signal dom (BitVec 8)
  flag : Signal dom Bool
instance : Sparkle.Core.HasDomain (TwoOut dom) dom := ⟨⟩

/-- A structure result, hardware `let`s shared by the writes and the result. -/
def twoHW (en : Signal dom Bool) : TwoOut dom :=
  circuit do
    let c ← Signal.reg (0#8)
    let f ← Signal.reg false
    let cs := (c : Signal dom (BitVec 8))
    let nxt := cs + (Signal.pure 1#8 : Signal dom (BitVec 8))
    c <~ Signal.mux en nxt cs
    f <~ Signal.beq cs (Signal.pure 255#8 : Signal dom (BitVec 8))
    return ({ cnt := cs, flag := (f : Signal dom Bool) } : TwoOut dom)

/-- One field of the structure result, each its own module. -/
def twoFlag (en : Signal dom Bool) : Signal dom Bool := (twoHW en).flag
def twoCnt (en : Signal dom Bool) : Signal dom (BitVec 8) := (twoHW en).cnt

/-- The LIN checksum of the IP library (one slot, some twenty `let`s, a
structure result), in any domain … -/
def linChk (start : Signal dom Bool) (byteIn : Signal dom (BitVec 8)) (valid : Signal dom Bool) :
    Signal dom (BitVec 8) :=
  (Sparkle.IP.Bus.LINHW.checksumHW start byteIn valid).chk
end

/-- … and in the default domain, whose reset is synchronous. -/
def linChkDefault (start : Signal defaultDomain Bool) (byteIn : Signal defaultDomain (BitVec 8))
    (valid : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  (Sparkle.IP.Bus.LINHW.checksumHW start byteIn valid).chk

/-! ## The route, and the emitted module against the source -/

/-- Widths of every declared name of a module. -/
def weAll (M : Sparkle.IR.AST.Module) : WEnv := fun name =>
  match (M.wires ++ M.inputs ++ M.outputs).find? (·.name == name) with
  | some p => p.ty.bitWidth
  | none => 0

/-- Run `m` for `k` cycles from its registers' reset values with reset low:
`ins t` are the input values at cycle `t`. Returns `out` per cycle. -/
def simOut (m : Sparkle.IR.AST.Module) (k : Nat) (ins : Nat → String → Option Nat)
    (port : String := "out") : Option (List Nat) :=
  let init : String → Nat := fun n =>
    (m.body.findSome? fun st => match st with
      | .register o _ _ _ i => if o == n then some i.toNat else none
      | _ => none).getD 0
  (runModule (weAll m) m.body
    (fun j st => fun n => match ins (k - 1 - j) n with
      | some v => v
      | none => if n == "rst" then 0 else st n) k init (fun _ _ => 0)).map (·.map (· port))

def bStream {dom : DomainConfig} (seed : Nat) : Signal dom Bool :=
  ⟨fun t => (t * 7 + seed * 3 + t / 3) % 3 != 0⟩
def vStream {dom : DomainConfig} (w seed : Nat) : Signal dom (BitVec w) :=
  ⟨fun t => BitVec.ofNat w (t * 37 + seed * 11 + t * t)⟩

/-- The declaration takes the machine route; returns the shipped module. -/
def machineModule (name : Name) (slots : Nat) (rk : Sparkle.IR.Type.ResetKind)
    (outs : List String := ["out"]) : TermElabM Sparkle.IR.AST.Module := do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  let ci ← getConstInfo name
  let ec := entryConst true false [] ci pred inl (structEnv env)
  unless (certifiedShape? false [] ec).isNone && (mixedCertifiedShape? false [] ec pred).isNone do
    throwError "{name}: a combinational or register gate accepts the declaration"
  let some shape := machineShape? false [] ec (structEnv env)
    | throwError "{name}: not a machine shape"
  unless shape.layout.slots.length == slots && shape.layout.resetKind == rk do
    throwError "{name}: unexpected layout {repr shape.layout}"
  let (m, _) ← synthesizeCombinational name
  let regs := m.body.filter fun st => match st with
    | .register .. => true
    | _ => false
  unless regs.length == slots do
    throwError "{name}: {regs.length} registers for {slots} slots"
  unless regs.all (fun st => match st with
      | .register _ _ (_, k) _ _ => k == rk
      | _ => false) do
    throwError "{name}: a register with the wrong reset kind"
  unless m.inputs.any (·.name == "clk") && m.inputs.any (·.name == "rst") &&
      m.outputs.map (·.name) == outs do
    throwError "{name}: unexpected ports"
  return m

run_cmd liftTermElabM do
  let K := 40
  let en : Signal defaultDomain Bool := bStream 1
  let d : Signal defaultDomain (BitVec 4) := vStream 4 2
  let start : Signal defaultDomain Bool := ⟨fun t => t % 9 == 0⟩
  let valid : Signal defaultDomain Bool := bStream 2
  let byte : Signal defaultDomain (BitVec 8) := vStream 8 5
  let check (name : Name) (got : Option (List Nat)) (want : List Nat) : TermElabM Unit := do
    unless got == some want do
      throwError "{name}: the emitted module departs from the source\n{got}\n{want}"
  let m ← machineModule ``mThree 3 .asynchronous
  check ``mThree
    (simOut m K fun t n => if n == "_gen_en" then some (en.val t).toNat
      else if n == "_gen_d" then some (d.val t).toNat else none)
    ((List.range K).map fun t => ((mThree en d).val t).toNat)
  let m ← machineModule ``twoFlag 2 .asynchronous
  check ``twoFlag
    (simOut m K fun t n => if n == "_gen_en" then some (en.val t).toNat else none)
    ((List.range K).map fun t => ((twoFlag en).val t).toNat)
  let m ← machineModule ``twoCnt 2 .asynchronous
  check ``twoCnt
    (simOut m K fun t n => if n == "_gen_en" then some (en.val t).toNat else none)
    ((List.range K).map fun t => ((twoCnt en).val t).toNat)
  let lin (t : Nat) (n : String) : Option Nat :=
    if n == "_gen_start" then some (start.val t).toNat
    else if n == "_gen_valid" then some (valid.val t).toNat
    else if n == "_gen_byteIn" then some (byte.val t).toNat else none
  let m ← machineModule ``linChk 1 .asynchronous
  check ``linChk (simOut m K lin) ((List.range K).map fun t => ((linChk start byte valid).val t).toNat)
  let m ← machineModule ``linChkDefault 1 .synchronous
  check ``linChkDefault (simOut m K lin)
    ((List.range K).map fun t => ((linChkDefault start byte valid).val t).toNat)
  -- structure results: one module, one output port per field
  let m ← machineModule ``twoHW 2 .asynchronous ["cnt", "flag"]
  let enIn (t : Nat) (n : String) : Option Nat :=
    if n == "_gen_en" then some (en.val t).toNat else none
  check ``twoHW (simOut m K enIn "cnt") ((List.range K).map fun t => ((twoHW en).cnt.val t).toNat)
  check ``twoHW (simOut m K enIn "flag")
    ((List.range K).map fun t => ((twoHW en).flag.val t).toNat)
  let m ← machineModule ``Sparkle.IP.Bus.LINHW.checksumHW 1 .asynchronous ["acc", "chk"]
  check ``Sparkle.IP.Bus.LINHW.checksumHW (simOut m K lin "acc")
    ((List.range K).map fun t =>
      ((Sparkle.IP.Bus.LINHW.checksumHW start byte valid).acc.val t).toNat)
  check ``Sparkle.IP.Bus.LINHW.checksumHW (simOut m K lin "chk")
    ((List.range K).map fun t =>
      ((Sparkle.IP.Bus.LINHW.checksumHW start byte valid).chk.val t).toNat)
  logInfo m!"MACHINE ROUTE: 7 declarations (Signal and structure results), {K} cycles each, emitted module == source"

/-! ## The three-slot machine, end to end -/

#def_machine_body mThreeBody of mThree

def mThreeIn : List (Name × MixedGateBinder) := [(`dom, .domain), (`en, .bool), (`d, .bits 4)]
def mThreeSlots : List (Name × MixedGateBinder) := [(`a, .bits 4), (`b, .bits 4), (`g, .bool)]
def mThreeLayout : Layout :=
  { slots := [{ lo := 5, width := 4, init := 0 }, { lo := 1, width := 4, init := 3 },
      { lo := 0, width := 1, init := 1 }]
    outs := [{ name := "out", lo := 9, width := 4, ty := .bitVector 4 }]
    resetKind := .asynchronous }
noncomputable def mThreeShape : MachineShape :=
  { binders := mThreeIn ++ mThreeSlots, body := mThreeBody, layout := mThreeLayout }

/-- The packed transition: `result ++ nextA ++ nextB ++ nextG`. Bool inputs:
`en`, `g`; BitVec inputs: `d`, `a`, `b`. -/
def mThreeTerm : Term (.bits (4 + (4 + (4 + 1)))) :=
  .concat (.mux (.boolInput 1) (.bitsInput 4 1) (.bitsInput 4 2))
    (.concat (.mux (.boolInput 0) (.binary .add (.bitsInput 4 1) (.bitsInput 4 0)) (.bitsInput 4 2))
      (.concat (.bitsInput 4 2)
        (.mux (.compare .eq (.bitsInput 4 1) (.bitsInput 4 0)) (.bitsLit 1 1) (.bitsLit 1 0))))

def mThreeBpos : Nat → Nat := fun j => if j = 0 then 1 else 5
def mThreeVpos : Nat → Nat := fun j => j + 2

theorem mThree_body : mThreeShape.body =
    quote (.bvar 5) (fun j => inputExpr mThreeShape.binders.length (mThreeBpos j))
      (fun j => inputExpr mThreeShape.binders.length (mThreeVpos j))
      (packLets [] mThreeTerm).2 := rfl

theorem mThreeTerm_wf : mThreeTerm.WF 2 3 (fun _ => 4) := by
  simp [mThreeTerm, Term.WF]

run_cmd liftTermElabM do
  let env ← getEnv
  let ci ← getConstInfo ``mThree
  let some shape := machineShape? false []
      (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env))
      (structEnv env)
    | throwError "mThree: not a machine shape"
  let .ok r := reflExpr shape.body | throwError "mThree: body not reflectable"
  unless (← getConstInfo ``mThreeBody).value? == some r do
    throwError "mThreeBody is not the machine body of mThree"
  unless shape.binders == mThreeIn ++ mThreeSlots && shape.layout.slots == mThreeLayout.slots &&
      shape.layout.outs == mThreeLayout.outs &&
      shape.layout.resetKind == mThreeLayout.resetKind do
    throwError "mThreeShape is not the machine shape of mThree"

/-! ### The emitted module, cycle by cycle -/

/-- A run of the real entry on `mThree` returns a module that preserves every
cycle of the machine. -/
theorem mThree_machine {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``mThree [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``mThree mThreeShape) :
    MachinePreserves ``mThree mThreeShape mThreeIn mThreeSlots [] m := by
  apply synthesizeCombinationalCore_machine_sound hr entry (machineCloses_of_noLets rfl rfl) rfl rfl
  · intro name n hmem
    simp only [mThreeShape, mThreeIn, mThreeSlots, List.cons_append, List.nil_append,
      List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, reduceCtorEq, and_false,
      false_or, MixedGateBinder.bits.injEq] at hmem
    omega
  · intro b hb
    simp only [mThreeSlots, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp
  · intro b hb; cases hb
  · exact .cons rfl (.cons rfl (.cons rfl .nil))
  · intro o ho
    simp only [mThreeShape, mThreeLayout, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho
    exact ⟨by decide, by decide⟩
  · decide

/-! ### The source machine -/

abbrev Slots3 : List Type := [BitVec 4, BitVec 4, Bool]

/-- The body `circuit do` expands `mThree` to. -/
def mThreeCircuit {dom : DomainConfig} (en : Signal dom Bool) (d : Signal dom (BitVec 4)) :
    RegList dom (HList Slots3) (Circuit.SigList dom Slots3) Slots3 →
      Circuit dom (Circuit.SigList dom Slots3) (Signal dom (BitVec 4)) :=
  fun regs =>
    (Circuit.next regs.1 (Signal.mux en (regs.1.1 + d) regs.2.1.1)).bind fun _ =>
    (Circuit.next regs.2.2.1 (Signal.beq regs.1.1 d)).bind fun _ =>
    Circuit.pure' (Signal.mux regs.2.2.1.1 regs.1.1 regs.2.1.1)

def mThreeInits : HList Slots3 := (0#4, 3#4, true, ())

theorem mThree_circuit {dom : DomainConfig} (en : Signal dom Bool) (d : Signal dom (BitVec 4)) :
    mThree en d = runCircuitH mThreeInits (mThreeCircuit en d) := rfl

/-- **The source machine**: the state of `mThree` as a recurrence, and its
result as a function of the state. -/
theorem mThree_state {dom : DomainConfig} (en : Signal dom Bool) (d : Signal dom (BitVec 4)) :
    (stateLoop mThreeInits (mThreeCircuit en d)).val 0 = (0#4, 3#4, true, ()) ∧
    (∀ t, (stateLoop mThreeInits (mThreeCircuit en d)).val (t + 1) =
      ((if en.val t then ((stateLoop mThreeInits (mThreeCircuit en d)).val t).1 + d.val t
          else ((stateLoop mThreeInits (mThreeCircuit en d)).val t).2.1),
        ((stateLoop mThreeInits (mThreeCircuit en d)).val t).2.1,
        ((stateLoop mThreeInits (mThreeCircuit en d)).val t).1 == d.val t, ())) ∧
    ∀ t, (mThree en d).val t =
      if ((stateLoop mThreeInits (mThreeCircuit en d)).val t).2.2.1
        then ((stateLoop mThreeInits (mThreeCircuit en d)).val t).1
        else ((stateLoop mThreeInits (mThreeCircuit en d)).val t).2.1 := by
  obtain ⟨h0, hs⟩ := circuit_state mThreeInits (mThreeCircuit en d)
    (pointwise_of_const _ (fun _ _ => rfl))
  refine ⟨h0, fun t => ?_, fun t => rfl⟩
  rw [hs t]
  rfl

/-! ### Source to RTL -/

/-- The packed transition value of `mThree` on a state `(a, b, g)` and
inputs `en`, `d`. -/
theorem mThree_packed (B : Nat → Bool) (V : (j : Nat) → (n : Nat) → BitVec n) :
    packedAt mThreeTerm mThreeBpos mThreeVpos B V =
      ((if B 5 then V 3 4 else V 4 4) ++
        ((if B 1 then V 3 4 + V 2 4 else V 4 4) ++
          (V 4 4 ++ (if V 3 4 == V 2 4 then 1#1 else 0#1)))).toNat := rfl

set_option maxHeartbeats 1000000 in
/-- **Source-to-RTL execution of a three-slot `circuit do`.** One successful
run of the real synthesis entry on `mThree` returns a module with three
registers such that: run for any number `T` of cycles with reset low, the
registers starting at their reset values and every cycle's environment
carrying that cycle's inputs, cycle `j` drives `out` with the value of the
SOURCE declaration at time `j`. -/
theorem mThree_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``mThree [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``mThree mThreeShape) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = 6 ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (ra rb rg : String),
      [ra, rb, rg].Nodup ∧
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ t st, t < T → SourceInputs ``mThree mThreeIn ids cache
          (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
          (seed t st)) →
        (∀ t st r, r ∈ [ra, rb, rg] → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) →
        st0 ra = 0 → st0 rb = 3 → st0 rg = 1 →
        ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
          ∀ j (hj : j < envs.length),
            (envs[j]'hj) "out" = ((mThree (bools 1) (bits 2 4)).val j).toNat := by
  obtain ⟨ids, nd, len, cache, h⟩ := machine_trace (mThree_machine hr entry) rfl
  obtain ⟨regs, rnd, rlen, trace⟩ := h (.bvar 5) 2 3 (fun _ => 4) mThreeBpos mThreeVpos
    [] mThreeTerm mThreeTerm_wf
    (by
      intro j hj
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl
      · exact ⟨`en, rfl⟩
      · exact ⟨`g, rfl⟩)
    (by
      intro j hj
      have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl
      · exact ⟨`d, rfl⟩
      · exact ⟨`a, rfl⟩
      · exact ⟨`b, rfl⟩)
    mThree_body
    (by
      intro f hf
      simp only [mThreeShape, mThreeLayout, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl <;> decide)
    (by
      intro o ho
      simp only [mThreeShape, mThreeLayout, List.mem_cons, List.not_mem_nil, or_false] at ho
      subst ho; decide)
  match regs, rlen, rnd, trace with
  | [ra, rb, rg], _, rnd, trace =>
  refine ⟨ids, nd, len, cache, ra, rb, rg, rnd, ?_⟩
  intro D bools bits T seed st0 mems inputs pass rst ia ib ig
  obtain ⟨s0, step, out⟩ := mThree_state (bools 1) (bits 2 4)
  generalize stateLoop mThreeInits (mThreeCircuit (bools 1) (bits 2 4)) = S at s0 step out
  -- The binders' values over time: the inputs' Signals, and the state.
  let B : Nat → Nat → Bool := fun τ j => if j = 5 then (S.val τ).2.2.1 else (bools j).val τ
  let V : Nat → (j : Nat) → (n : Nat) → BitVec n := fun τ j n =>
    if j = 3 then BitVec.ofNat n (S.val τ).1.toNat
    else if j = 4 then BitVec.ofNat n (S.val τ).2.1.toNat
    else (bits j n).val τ
  have hB5 : ∀ τ, B τ 5 = (S.val τ).2.2.1 := fun τ => rfl
  have hB1 : ∀ τ, B τ 1 = (bools 1).val τ := fun τ => rfl
  have hV2 : ∀ τ, V τ 2 4 = (bits 2 4).val τ := fun τ => rfl
  have hV3 : ∀ τ, V τ 3 4 = (S.val τ).1 := fun τ => by simp [V]
  have hV4 : ∀ τ, V τ 4 4 = (S.val τ).2.1 := fun τ => by simp [V]
  obtain ⟨envs, hrun, hlen, hobs⟩ := trace T B V seed st0 mems
    (by
      intro t st ht
      refine sourceInputs_congr nd ?_ ?_ (inputs t st ht)
      · intro j hj
        have : j ≠ 5 := by simp [mThreeIn] at hj; omega
        simp [B, this]
      · intro j hj n
        have h3 : j ≠ 3 := by simp [mThreeIn] at hj; omega
        have h4 : j ≠ 4 := by simp [mThreeIn] at hj; omega
        simp [V, h3, h4])
    pass rst
    (by
      intro i r b hr hb
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        simp [mThreeSlots] at this; omega
      rcases hi with rfl | rfl | rfl <;>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
          mThreeSlots] at hr hb <;> subst hr <;> subst hb
      · show st0 _ = (V 0 3 4).toNat
        rw [hV3, s0, ia]; rfl
      · show st0 _ = (V 0 4 4).toNat
        rw [hV4, s0, ib]; rfl
      · show st0 _ = encodeBool (B 0 5)
        rw [hB5, s0, ig]; rfl)
    (by
      intro τ i f b hf hb
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        simp [mThreeSlots] at this; omega
      rw [mThree_packed, hB5, hB1, hV2, hV3, hV4]
      rcases hi with rfl | rfl | rfl <;>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
          mThreeSlots, mThreeShape, mThreeLayout] at hf hb <;> subst hf <;> subst hb
      · show (V (τ + 1) 3 4).toNat = _
        rw [hV3, step τ, field_lo _ _ (by decide), field_hi _ _ (by decide)]
        exact (field_all _).symm
      · show (V (τ + 1) 4 4).toNat = _
        rw [hV4, step τ, field_lo _ _ (by decide), field_lo _ _ (by decide),
          field_hi _ _ (by decide)]
        exact (field_all _).symm
      · show encodeBool (B (τ + 1) 5) = _
        rw [hB5, step τ, field_lo _ _ (by decide), field_lo _ _ (by decide),
          field_lo _ _ (by decide), field_all]
        cases ((S.val τ).1 == (bits 2 4).val τ) <;> rfl)
    (fun _ => trivial)
  refine ⟨envs, hrun, hlen, fun j hj => ?_⟩
  rw [hobs j hj { name := "out", lo := 9, width := 4, ty := .bitVector 4 }
    (by simp [mThreeShape, mThreeLayout]), mThree_packed, hB5, hB1, hV2, hV3, hV4, out j]
  show mask 4 (_ >>> 9) = _
  rw [field_hi _ _ (by decide)]
  exact field_all _

/-! ## The LIN checksum of the IP library, end to end

`IP/Bus/LINHW.checksumHW`: one accumulator register, the carry folded back
in, eighteen hardware `let`s, a structure result. `linChk` is its `chk`
field. The `let`s stay `let`s: each is one wire of the emitted module, named
after the source binder. -/

#def_machine_body linBody of linChk

def linIn : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`start, .bool), (`byteIn, .bits 8), (`valid, .bool)]
def linSlots : List (Name × MixedGateBinder) := [(`accR, .bits 8)]
def linLets : List (Name × MixedGateBinder) :=
  [(`p0, .bits 8), (`pFF, .bits 8), (`p1, .bits 8), (`zeroBit, .bits 1), (`accW, .bits 9),
   (`byteW, .bits 9), (`sumW, .bits 9), (`p1_9, .bits 9), (`p8_9, .bits 9),
   (`carryShift, .bits 9), (`carryMasked, .bits 9), (`p0_9, .bits 9), (`isCarryZero, .bool),
   (`carry, .bool), (`sumLo, .bits 8), (`sumLoP1, .bits 8), (`folded, .bits 8),
   (`chkSig, .bits 8)]
def linLayout : Layout :=
  { slots := [{ lo := 0, width := 8, init := 0 }]
    outs := [{ name := "out", lo := 8, width := 8, ty := .bitVector 8 }]
    resetKind := .asynchronous, lets := 18 }
noncomputable def linShape : MachineShape :=
  { binders := linIn ++ linSlots ++ linLets, body := linBody, layout := linLayout }

/-- The first `fun` binder name of an expression (the slice's binder is a
hygienic macro name of the IP source file). -/
def firstLamName : Lean.Expr → Option Name
  | .lam n _ _ _ => some n
  | .app f a => (firstLamName f).orElse fun _ => firstLamName a
  | _ => none

noncomputable def linSliceName : Name := (firstLamName linBody).getD .anonymous

/-- Bool inputs of the term: `start`, `valid`, `isCarryZero`, `carry`. -/
def linBpos : Nat → Nat := fun j => [1, 3, 17, 18].getD j 0
/-- BitVec inputs of the term: `byteIn`, `accR`, then the BitVec `let`s. -/
def linVpos : Nat → Nat := fun j =>
  [2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22].getD j 0
def linVw : Nat → Nat := fun j =>
  [8, 8, 8, 8, 8, 1, 9, 9, 9, 9, 9, 9, 9, 9, 8, 8, 8, 8].getD j 0

/-- The eighteen `let` fields, in source order. -/
noncomputable def linFields : List (Σ w : Nat, Term (.bits w)) :=
  [⟨8, .bitsLit 8 0⟩, ⟨8, .bitsLit 8 255⟩, ⟨8, .bitsLit 8 1⟩, ⟨1, .bitsLit 1 0⟩,
   ⟨1 + 8, .concat (.bitsInput 1 5) (.bitsInput 8 1)⟩,
   ⟨1 + 8, .concat (.bitsInput 1 5) (.bitsInput 8 0)⟩,
   ⟨9, .binary .add (.bitsInput 9 6) (.bitsInput 9 7)⟩,
   ⟨9, .bitsLit 9 1⟩, ⟨9, .bitsLit 9 8⟩,
   ⟨9, .binary .shr (.bitsInput 9 8) (.bitsInput 9 10)⟩,
   ⟨9, .binary .and (.bitsInput 9 11) (.bitsInput 9 9)⟩,
   ⟨9, .bitsLit 9 0⟩,
   ⟨1, .mux (.compare .eq (.bitsInput 9 12) (.bitsInput 9 13)) (.bitsLit 1 1) (.bitsLit 1 0)⟩,
   ⟨1, .mux (.boolNot (.boolInput 2)) (.bitsLit 1 1) (.bitsLit 1 0)⟩,
   ⟨8, .slice linSliceName 0 8 (.bitsInput 9 8)⟩,
   ⟨8, .binary .add (.bitsInput 8 14) (.bitsInput 8 4)⟩,
   ⟨8, .mux (.boolInput 3) (.bitsInput 8 15) (.bitsInput 8 14)⟩,
   ⟨8, .binary .xor (.bitsInput 8 1) (.bitsInput 8 3)⟩]

/-- What remains after the `let`s: `chk ++ nextAcc`. -/
def linCore : Term (.bits (8 + 8)) :=
  .concat (.bitsInput 8 17)
    (.mux (.boolInput 0) (.bitsInput 8 2) (.mux (.boolInput 1) (.bitsInput 8 16) (.bitsInput 8 1)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem lin_body : linShape.body =
    quote (.bvar 22) (fun j => inputExpr linShape.binders.length (linBpos j))
      (fun j => inputExpr linShape.binders.length (linVpos j))
      (packLets linFields linCore).2 := rfl

theorem lin_wf : (packLets linFields linCore).2.WF 4 18 linVw := by
  simp [packLets, linFields, linCore, Term.WF, linVw]


run_cmd liftTermElabM do
  let env ← getEnv
  let ci ← getConstInfo ``linChk
  let some shape := machineShape? false []
      (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env))
      (structEnv env)
    | throwError "linChk: not a machine shape"
  let .ok r := reflExpr shape.body | throwError "linChk: body not reflectable"
  unless (← getConstInfo ``linBody).value? == some r do
    throwError "linBody is not the machine body of linChk"
  unless shape.binders == linIn ++ linSlots ++ linLets && shape.layout.slots == linLayout.slots &&
      shape.layout.outs == linLayout.outs && shape.layout.lets == linLayout.lets &&
      shape.layout.resetKind == linLayout.resetKind do
    throwError "linShape is not the machine shape of linChk"
  -- the `let` boundary: the real machine synthesis ties every `let`
  let translate : TranslateFn := fun e h t n => translateExprToWire e h t n
  unless (← synthesizeMachineCertified translate (fun _ => pure ()) ``linChk shape).isSome do
    throwError "linChk: the machine synthesis did not tie the lets"

theorem lin_machine {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``linChk [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``linChk linShape)
    (closes : MachineCloses mctx mref cctx cref ``linChk linShape) :
    MachinePreserves ``linChk linShape linIn linSlots linLets m := by
  apply synthesizeCombinationalCore_machine_sound hr entry closes rfl rfl
  · intro name n hmem
    simp only [linShape, linIn, linSlots, linLets, List.cons_append, List.nil_append,
      List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, reduceCtorEq, and_false,
      false_or, MixedGateBinder.bits.injEq] at hmem
    omega
  · intro b hb
    simp only [linSlots, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb; simp
  · intro b hb
    simp only [linLets, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> simp
  · exact .cons rfl .nil
  · intro o ho
    simp only [linShape, linLayout, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho
    exact ⟨by decide, by decide⟩
  · decide

/-! ### The source machine -/

/-- The nine-bit sum of the accumulator and the byte. -/
def linSumW (acc byte : BitVec 8) : BitVec 9 := (0#1 ++ acc : BitVec 9) + (0#1 ++ byte : BitVec 9)
/-- No carry out of the eight-bit sum. -/
def linCarryZero (acc byte : BitVec 8) : Bool := (linSumW acc byte >>> 8#9 &&& 1#9) == 0#9
def linSumLo (acc byte : BitVec 8) : BitVec 8 := BitVec.extractLsb' 0 8 (linSumW acc byte)
/-- The accumulator's next value when a byte is taken: the eight-bit sum
with the carry folded back in. -/
def linFold (acc byte : BitVec 8) : BitVec 8 :=
  if !linCarryZero acc byte then linSumLo acc byte + 1#8 else linSumLo acc byte

abbrev Slots1 : List Type := [BitVec 8]

/-- The body `circuit do` expands `checksumHW` to. -/
def linCircuit {dom : DomainConfig} (start : Signal dom Bool) (byteIn : Signal dom (BitVec 8))
    (valid : Signal dom Bool) :
    RegList dom (HList Slots1) (Circuit.SigList dom Slots1) Slots1 →
      Circuit dom (Circuit.SigList dom Slots1) (Sparkle.IP.Bus.LINHW.ChkOut dom) :=
  fun regs =>
    let accSig : Signal dom (BitVec 8) := regs.1.1
    let p0 := (Signal.pure 0#8 : Signal dom (BitVec 8))
    let pFF := (Signal.pure 0xFF#8 : Signal dom (BitVec 8))
    let p1 := (Signal.pure 1#8 : Signal dom (BitVec 8))
    let zeroBit := (Signal.pure 0#1 : Signal dom (BitVec 1))
    let accW := (zeroBit ++ accSig : Signal dom (BitVec 9))
    let byteW := (zeroBit ++ byteIn : Signal dom (BitVec 9))
    let sumW := (accW + byteW : Signal dom (BitVec 9))
    let p1_9 := (Signal.pure 1#9 : Signal dom (BitVec 9))
    let p8_9 := (Signal.pure 8#9 : Signal dom (BitVec 9))
    let carryShift := (sumW >>> p8_9 : Signal dom (BitVec 9))
    let carryMasked := (carryShift &&& p1_9 : Signal dom (BitVec 9))
    let p0_9 := (Signal.pure 0#9 : Signal dom (BitVec 9))
    let isCarryZero := (Signal.beq carryMasked p0_9 : Signal dom Bool)
    let carry := (~~~isCarryZero : Signal dom Bool)
    let sumLo := sumW.map (BitVec.extractLsb' 0 8 ·)
    let sumLoP1 := (sumLo + p1 : Signal dom (BitVec 8))
    let folded := Signal.mux carry sumLoP1 sumLo
    (Circuit.next regs.1 (Signal.mux start p0 (Signal.mux valid folded accSig))).bind fun _ =>
    Circuit.pure' ({ acc := accSig, chk := (accSig ^^^ pFF : Signal dom (BitVec 8)) } :
      Sparkle.IP.Bus.LINHW.ChkOut dom)

def linInits : HList Slots1 := (0#8, ())

theorem lin_circuit {dom : DomainConfig} (start : Signal dom Bool)
    (byteIn : Signal dom (BitVec 8)) (valid : Signal dom Bool) :
    Sparkle.IP.Bus.LINHW.checksumHW start byteIn valid =
      runCircuitH linInits (linCircuit start byteIn valid) := rfl

/-- **The source machine of the LIN checksum**: the accumulator as a
recurrence, and the checksum as a function of the accumulator. -/
theorem lin_state {dom : DomainConfig} (start : Signal dom Bool) (byteIn : Signal dom (BitVec 8))
    (valid : Signal dom Bool) :
    (stateLoop linInits (linCircuit start byteIn valid)).val 0 = (0#8, ()) ∧
    (∀ t, (stateLoop linInits (linCircuit start byteIn valid)).val (t + 1) =
      ((if start.val t then 0#8
        else if valid.val t then
          linFold ((stateLoop linInits (linCircuit start byteIn valid)).val t).1 (byteIn.val t)
        else ((stateLoop linInits (linCircuit start byteIn valid)).val t).1), ())) ∧
    ∀ t, (linChk start byteIn valid).val t =
      ((stateLoop linInits (linCircuit start byteIn valid)).val t).1 ^^^ 255#8 := by
  obtain ⟨h0, hs⟩ := circuit_state linInits (linCircuit start byteIn valid)
    (pointwise_of_const _ (fun _ _ => rfl))
  refine ⟨h0, fun t => ?_, fun t => rfl⟩
  rw [hs t]
  rfl

/-! ### The `let`s of the source are the `let`s of the transition -/

/-- The value of every BitVec binder from the accumulator on, as a function
of the accumulator and the byte: the slot, then the `let`s. -/
def linV (acc byte : BitVec 8) (pos w : Nat) : BitVec w :=
  match pos with
  | 4 => acc.setWidth w
  | 5 => BitVec.ofNat w 0
  | 6 => BitVec.ofNat w 255
  | 7 => BitVec.ofNat w 1
  | 8 => BitVec.ofNat w 0
  | 9 => (0#1 ++ acc : BitVec 9).setWidth w
  | 10 => (0#1 ++ byte : BitVec 9).setWidth w
  | 11 => (linSumW acc byte).setWidth w
  | 12 => BitVec.ofNat w 1
  | 13 => BitVec.ofNat w 8
  | 14 => (linSumW acc byte >>> 8#9).setWidth w
  | 15 => (linSumW acc byte >>> 8#9 &&& 1#9).setWidth w
  | 16 => BitVec.ofNat w 0
  | 19 => (linSumLo acc byte).setWidth w
  | 20 => (linSumLo acc byte + 1#8).setWidth w
  | 21 => (linFold acc byte).setWidth w
  | 22 => (acc ^^^ 255#8).setWidth w
  | _ => 0#w

theorem bit_of_bool (c : Bool) : (if c then 1#1 else 0#1).toNat = encodeBool c := by
  cases c <;> rfl

/-- The valuation built from the source's own `let` values satisfies the
`let` equations of the transition. -/
theorem lin_lets (bools : Nat → Bool) (acc : BitVec 8)
    (bits : (j : Nat) → (n : Nat) → BitVec n) :
    LetsHold linBpos linVpos
      (fun j => if j = 17 then linCarryZero acc (bits 2 8)
        else if j = 18 then !linCarryZero acc (bits 2 8) else bools j)
      (fun j n => if 4 ≤ j then linV acc (bits 2 8) j n else bits j n)
      5 linLets linFields := by
  simp [LetsHold, linLets, linFields, posEnc, eval, linBpos, linVpos, linV, machWidth,
    Tools.ShippingScalarSoundness.Binary.apply, Tools.ShippingBoolSourceSoundness.compareValue,
    linCarryZero, linSumW, linSumLo, linFold]
  generalize ((0#1 ++ acc + (0#1 ++ bits 2 8)) >>> 8 &&& 1#9) = x
  by_cases h : x = 0#9 <;> simp [h, encodeBool]

/-- What remains after the `let`s, on the source's values. -/
theorem lin_core (B : Nat → Bool) (V : (j : Nat) → (n : Nat) → BitVec n) :
    packedAt linCore linBpos linVpos B V =
      (V 22 8 ++ (if B 1 then V 5 8 else if B 3 then V 21 8 else V 4 8)).toNat := rfl

set_option maxHeartbeats 1000000 in
/-- **Source-to-RTL execution of the LIN checksum.** One successful run of
the real synthesis entry on `linChk` returns a module with one register such
that: run for any number `T` of cycles with reset low, the register starting
at its reset value and every cycle's environment carrying that cycle's
inputs, cycle `j` drives `out` with the checksum the SOURCE declaration has
at time `j`. -/
theorem lin_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``linChk [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``linChk linShape)
    (closes : MachineCloses mctx mref cctx cref ``linChk linShape) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = 23 ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (racc : String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ t st, t < T → SourceInputs ``linChk linIn ids cache
          (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
          (seed t st)) →
        (∀ t st, seed t st racc = st racc) →
        (∀ t st, seed t st "rst" = 0) →
        st0 racc = 0 →
        ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
          ∀ j (hj : j < envs.length),
            (envs[j]'hj) "out" = ((linChk (bools 1) (bits 2 8) (bools 3)).val j).toNat := by
  obtain ⟨ids, nd, len, cache, h⟩ := machine_trace (lin_machine hr entry closes) rfl
  obtain ⟨regs, rnd, rlen, trace⟩ := h (.bvar 22) 4 18 linVw linBpos linVpos
    linFields linCore lin_wf
    (by
      intro j hj
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · exact ⟨`start, rfl⟩
      · exact ⟨`valid, rfl⟩
      · exact ⟨`isCarryZero, rfl⟩
      · exact ⟨`carry, rfl⟩)
    (by
      intro j hj
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
          j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
    lin_body
    (by
      intro f hf
      simp only [linShape, linLayout, List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; decide)
    (by
      intro o ho
      simp only [linShape, linLayout, List.mem_cons, List.not_mem_nil, or_false] at ho
      subst ho; decide)
  match regs, rlen, rnd, trace with
  | [racc], _, _, trace =>
  refine ⟨ids, nd, len, cache, racc, ?_⟩
  intro D bools bits T seed st0 mems inputs pass rst ia
  obtain ⟨s0, step, out⟩ := lin_state (bools 1) (bits 2 8) (bools 3)
  generalize stateLoop linInits (linCircuit (bools 1) (bits 2 8) (bools 3)) = S at s0 step out
  -- The binders' values over time: the inputs' Signals, the state, the source's lets.
  let B : Nat → Nat → Bool := fun τ j =>
    if j = 17 then linCarryZero (S.val τ).1 ((bits 2 8).val τ)
    else if j = 18 then !linCarryZero (S.val τ).1 ((bits 2 8).val τ)
    else (bools j).val τ
  let V : Nat → (j : Nat) → (n : Nat) → BitVec n := fun τ j n =>
    if 4 ≤ j then linV (S.val τ).1 ((bits 2 8).val τ) j n else (bits j n).val τ
  have hB1 : ∀ τ, B τ 1 = (bools 1).val τ := fun τ => rfl
  have hB3 : ∀ τ, B τ 3 = (bools 3).val τ := fun τ => rfl
  have hV4 : ∀ τ, V τ 4 8 = (S.val τ).1 := fun τ => by simp [V, linV]
  have hV5 : ∀ τ, V τ 5 8 = 0#8 := fun τ => rfl
  have hV21 : ∀ τ, V τ 21 8 = linFold (S.val τ).1 ((bits 2 8).val τ) := fun τ => by
    simp [V, linV]
  have hV22 : ∀ τ, V τ 22 8 = (S.val τ).1 ^^^ 255#8 := fun τ => by simp [V, linV]
  obtain ⟨envs, hrun, hlen, hobs⟩ := trace T B V seed st0 mems
    (by
      intro t st ht
      refine sourceInputs_congr nd ?_ ?_ (inputs t st ht)
      · intro j hj
        have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [linIn] at hj; omega
        rcases this with rfl | rfl | rfl | rfl <;> simp [B]
      · intro j hj n
        have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [linIn] at hj; omega
        rcases this with rfl | rfl | rfl | rfl <;> simp [V])
    (by
      intro t st r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact pass t st)
    rst
    (by
      intro i r b hr hb
      have hi : i = 0 := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        simp [linSlots] at this; omega
      subst hi
      simp only [List.getElem?_cons_zero, Option.some.injEq, linSlots] at hr hb
      subst hr; subst hb
      show st0 _ = (V 0 4 8).toNat
      rw [hV4, s0, ia]; rfl)
    (by
      intro τ i f b hf hb
      have hi : i = 0 := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        simp [linSlots] at this; omega
      subst hi
      rw [lin_core, hB1, hB3, hV4, hV5, hV21, hV22]
      simp only [List.getElem?_cons_zero, Option.some.injEq, linSlots, linShape, linLayout]
        at hf hb
      subst hf; subst hb
      show (V (τ + 1) 4 8).toNat = _
      rw [hV4, step τ, field_lo _ _ (by decide)]
      exact (field_all _).symm)
    (fun τ => lin_lets (fun j => (bools j).val τ) (S.val τ).1 (fun j n => (bits j n).val τ))
  refine ⟨envs, hrun, hlen, fun j hj => ?_⟩
  rw [hobs j hj { name := "out", lo := 8, width := 8, ty := .bitVector 8 }
    (by simp [linShape, linLayout]), lin_core, hV22, out j]
  show mask 8 (_ >>> 8) = _
  rw [field_hi _ _ (by decide)]
  exact field_all _


/-! ## A structure result: the IP declaration itself

`Sparkle.IP.Bus.LINHW.checksumHW` returns a structure of two Signals. On the
machine route it is one module with one output port per field, named after
the field — no wrapper. The transition's `let`s and binders are those of
`linChk`; what remains after the `let`s is `acc ++ chk ++ nextAcc`. -/

#def_machine_body linHWBody of Sparkle.IP.Bus.LINHW.checksumHW

def linHWLayout : Layout :=
  { slots := [{ lo := 0, width := 8, init := 0 }]
    outs := [{ name := "acc", lo := 16, width := 8, ty := .bitVector 8 },
      { name := "chk", lo := 8, width := 8, ty := .bitVector 8 }]
    resetKind := .asynchronous, lets := 18 }
noncomputable def linHWShape : MachineShape :=
  { binders := linIn ++ linSlots ++ linLets, body := linHWBody, layout := linHWLayout }

def linHWCore : Term (.bits (8 + (8 + 8))) :=
  .concat (.bitsInput 8 1) (.concat (.bitsInput 8 17)
    (.mux (.boolInput 0) (.bitsInput 8 2) (.mux (.boolInput 1) (.bitsInput 8 16) (.bitsInput 8 1))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem linHW_body : linHWShape.body =
    quote (.bvar 22) (fun j => inputExpr linHWShape.binders.length (linBpos j))
      (fun j => inputExpr linHWShape.binders.length (linVpos j))
      (packLets linFields linHWCore).2 := rfl

theorem linHW_wf : (packLets linFields linHWCore).2.WF 4 18 linVw := by
  simp [packLets, linFields, linHWCore, Term.WF, linVw]

run_cmd liftTermElabM do
  let env ← getEnv
  let ci ← getConstInfo ``Sparkle.IP.Bus.LINHW.checksumHW
  let some shape := machineShape? false []
      (entryConst true false [] ci (instancePredicate env) (userInliner env) (structEnv env))
      (structEnv env)
    | throwError "checksumHW: not a machine shape"
  let .ok r := reflExpr shape.body | throwError "checksumHW: body not reflectable"
  unless (← getConstInfo ``linHWBody).value? == some r do
    throwError "linHWBody is not the machine body of checksumHW"
  unless shape.binders == linIn ++ linSlots ++ linLets &&
      shape.layout.slots == linHWLayout.slots && shape.layout.outs == linHWLayout.outs &&
      shape.layout.lets == linHWLayout.lets &&
      shape.layout.resetKind == linHWLayout.resetKind do
    throwError "linHWShape is not the machine shape of checksumHW"
  let translate : TranslateFn := fun e h t n => translateExprToWire e h t n
  unless (← synthesizeMachineCertified translate (fun _ => pure ())
      ``Sparkle.IP.Bus.LINHW.checksumHW shape).isSome do
    throwError "checksumHW: the machine synthesis did not tie the lets"

theorem linHW_machine {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``Sparkle.IP.Bus.LINHW.checksumHW [] false)
      mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Sparkle.IP.Bus.LINHW.checksumHW linHWShape)
    (closes : MachineCloses mctx mref cctx cref ``Sparkle.IP.Bus.LINHW.checksumHW linHWShape) :
    MachinePreserves ``Sparkle.IP.Bus.LINHW.checksumHW linHWShape linIn linSlots linLets m := by
  apply synthesizeCombinationalCore_machine_sound hr entry closes rfl rfl
  · intro name n hmem
    simp only [linHWShape, linIn, linSlots, linLets, List.cons_append, List.nil_append,
      List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, reduceCtorEq, and_false,
      false_or, MixedGateBinder.bits.injEq] at hmem
    omega
  · intro b hb
    simp only [linSlots, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb; simp
  · intro b hb
    simp only [linLets, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl <;> simp
  · exact .cons rfl .nil
  · intro o ho
    simp only [linHWShape, linHWLayout, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> exact ⟨by decide, by decide⟩
  · decide

theorem linHW_core (B : Nat → Bool) (V : (j : Nat) → (n : Nat) → BitVec n) :
    packedAt linHWCore linBpos linVpos B V =
      (V 4 8 ++ (V 22 8 ++ (if B 1 then V 5 8 else if B 3 then V 21 8 else V 4 8))).toNat := rfl

/-- The accumulator field of the source is the state. -/
theorem linHW_acc {dom : DomainConfig} (start : Signal dom Bool) (byteIn : Signal dom (BitVec 8))
    (valid : Signal dom Bool) (t : Nat) :
    (Sparkle.IP.Bus.LINHW.checksumHW start byteIn valid).acc.val t =
      ((stateLoop linInits (linCircuit start byteIn valid)).val t).1 := rfl

set_option maxHeartbeats 1000000 in
/-- **Source-to-RTL execution of the LIN checksum module of the IP library,
both outputs.** One successful run of the real synthesis entry on
`IP.Bus.LINHW.checksumHW` — the IP declaration, not a wrapper — returns a
module with one register and two output ports such that, run for any number
of cycles from reset values with reset low, cycle `j` drives `acc` and `chk`
with the two fields the SOURCE declaration has at time `j`. -/
theorem linHW_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``Sparkle.IP.Bus.LINHW.checksumHW [] false)
      mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Sparkle.IP.Bus.LINHW.checksumHW linHWShape)
    (closes : MachineCloses mctx mref cctx cref ``Sparkle.IP.Bus.LINHW.checksumHW linHWShape) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = 23 ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (racc : String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ t st, t < T → SourceInputs ``Sparkle.IP.Bus.LINHW.checksumHW linIn ids cache
          (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
          (seed t st)) →
        (∀ t st, seed t st racc = st racc) →
        (∀ t st, seed t st "rst" = 0) →
        st0 racc = 0 →
        ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
          ∀ j (hj : j < envs.length),
            (envs[j]'hj) "acc" = ((Sparkle.IP.Bus.LINHW.checksumHW (bools 1) (bits 2 8)
              (bools 3)).acc.val j).toNat ∧
            (envs[j]'hj) "chk" = ((Sparkle.IP.Bus.LINHW.checksumHW (bools 1) (bits 2 8)
              (bools 3)).chk.val j).toNat := by
  obtain ⟨ids, nd, len, cache, h⟩ := machine_trace (linHW_machine hr entry closes) rfl
  obtain ⟨regs, rnd, rlen, trace⟩ := h (.bvar 22) 4 18 linVw linBpos linVpos
    linFields linHWCore linHW_wf
    (by
      intro j hj
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · exact ⟨`start, rfl⟩
      · exact ⟨`valid, rfl⟩
      · exact ⟨`isCarryZero, rfl⟩
      · exact ⟨`carry, rfl⟩)
    (by
      intro j hj
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
          j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
    linHW_body
    (by
      intro f hf
      simp only [linHWShape, linHWLayout, List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; decide)
    (by
      intro o ho
      simp only [linHWShape, linHWLayout, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> decide)
  match regs, rlen, rnd, trace with
  | [racc], _, _, trace =>
  refine ⟨ids, nd, len, cache, racc, ?_⟩
  intro D bools bits T seed st0 mems inputs pass rst ia
  obtain ⟨s0, step, out⟩ := lin_state (bools 1) (bits 2 8) (bools 3)
  have acc := linHW_acc (bools 1) (bits 2 8) (bools 3)
  generalize stateLoop linInits (linCircuit (bools 1) (bits 2 8) (bools 3)) = S
    at s0 step out acc
  let B : Nat → Nat → Bool := fun τ j =>
    if j = 17 then linCarryZero (S.val τ).1 ((bits 2 8).val τ)
    else if j = 18 then !linCarryZero (S.val τ).1 ((bits 2 8).val τ)
    else (bools j).val τ
  let V : Nat → (j : Nat) → (n : Nat) → BitVec n := fun τ j n =>
    if 4 ≤ j then linV (S.val τ).1 ((bits 2 8).val τ) j n else (bits j n).val τ
  have hB1 : ∀ τ, B τ 1 = (bools 1).val τ := fun τ => rfl
  have hB3 : ∀ τ, B τ 3 = (bools 3).val τ := fun τ => rfl
  have hV4 : ∀ τ, V τ 4 8 = (S.val τ).1 := fun τ => by simp [V, linV]
  have hV5 : ∀ τ, V τ 5 8 = 0#8 := fun τ => rfl
  have hV21 : ∀ τ, V τ 21 8 = linFold (S.val τ).1 ((bits 2 8).val τ) := fun τ => by
    simp [V, linV]
  have hV22 : ∀ τ, V τ 22 8 = (S.val τ).1 ^^^ 255#8 := fun τ => by simp [V, linV]
  obtain ⟨envs, hrun, hlen, hobs⟩ := trace T B V seed st0 mems
    (by
      intro t st ht
      refine sourceInputs_congr nd ?_ ?_ (inputs t st ht)
      · intro j hj
        have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [linIn] at hj; omega
        rcases this with rfl | rfl | rfl | rfl <;> simp [B]
      · intro j hj n
        have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by simp [linIn] at hj; omega
        rcases this with rfl | rfl | rfl | rfl <;> simp [V])
    (by
      intro t st r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact pass t st)
    rst
    (by
      intro i r b hr hb
      have hi : i = 0 := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        simp [linSlots] at this; omega
      subst hi
      simp only [List.getElem?_cons_zero, Option.some.injEq, linSlots] at hr hb
      subst hr; subst hb
      show st0 _ = (V 0 4 8).toNat
      rw [hV4, s0, ia]; rfl)
    (by
      intro τ i f b hf hb
      have hi : i = 0 := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        simp [linSlots] at this; omega
      subst hi
      rw [linHW_core, hB1, hB3, hV4, hV5, hV21, hV22]
      simp only [List.getElem?_cons_zero, Option.some.injEq, linSlots, linHWShape, linHWLayout]
        at hf hb
      subst hf; subst hb
      show (V (τ + 1) 4 8).toNat = _
      rw [hV4, step τ, field_lo _ _ (by decide), field_lo _ _ (by decide)]
      exact (field_all _).symm)
    (fun τ => lin_lets (fun j => (bools j).val τ) (S.val τ).1 (fun j n => (bits j n).val τ))
  refine ⟨envs, hrun, hlen, fun j hj => ⟨?_, ?_⟩⟩
  · rw [hobs j hj { name := "acc", lo := 16, width := 8, ty := .bitVector 8 }
      (by simp [linHWShape, linHWLayout]), linHW_core, hV4, hV22, acc j]
    show mask 8 (_ >>> 16) = _
    rw [field_hi _ _ (by decide)]
    exact field_all _
  · rw [hobs j hj { name := "chk", lo := 8, width := 8, ty := .bitVector 8 }
      (by simp [linHWShape, linHWLayout]), linHW_core, hV4, hV22]
    have hchk : (Sparkle.IP.Bus.LINHW.checksumHW (bools 1) (bits 2 8) (bools 3)).chk.val j =
        (S.val j).1 ^^^ 255#8 := out j
    rw [hchk]
    show mask 8 (_ >>> 8) = _
    rw [field_lo _ _ (by decide), field_hi _ _ (by decide)]
    exact field_all _


/-! ## The reference machine

`machine_ref_trace` needs no valuation: the emitted module of the IP
declaration shows, on both ports and at every cycle, the reference machine
computed from the terms. The side conditions are decided. -/

open Tools.ShippingMachineRef in
/-- The reference machine of the LIN checksum module. -/
noncomputable def linRef : RefMachine :=
  RefMachine.mk 4 1 linBpos linVpos linFields (8 + (8 + 8)) linHWCore linHWLayout.slots

open Tools.ShippingMachineRef in
theorem linHW_scoped : LetsScoped linBpos linVpos (linIn.length + linSlots.length) linLets
    linFields := by
  simp [LetsScoped, reads, linLets, linFields, linBpos, linVpos, machWidth, linIn, linSlots]

open Tools.ShippingMachineRef in
/-- **The emitted LIN checksum module implements its reference machine.** -/
theorem linHW_reference {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``Sparkle.IP.Bus.LINHW.checksumHW [] false)
      mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Sparkle.IP.Bus.LINHW.checksumHW linHWShape)
    (closes : MachineCloses mctx mref cctx cref ``Sparkle.IP.Bus.LINHW.checksumHW linHWShape) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = 23 ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (racc : String),
      ∀ (T : Nat) (inB : Nat → Nat → Bool) (inV : Nat → (j : Nat) → (n : Nat) → BitVec n)
        (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ t st, t < T → SourceInputs ``Sparkle.IP.Bus.LINHW.checksumHW linIn ids cache
          (inB (T - 1 - t)) (inV (T - 1 - t)) (seed t st)) →
        (∀ t st, seed t st racc = st racc) →
        (∀ t st, seed t st "rst" = 0) →
        st0 racc = 0 →
        ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
          ∀ j (hj : j < envs.length),
            (envs[j]'hj) "acc" = linRef.out inB inV j 16 8 ∧
            (envs[j]'hj) "chk" = linRef.out inB inV j 8 8 := by
  obtain ⟨ids, nd, len, cache, h⟩ := machine_ref_trace (linHW_machine hr entry closes)
    (.cons ⟨rfl, by simp, by decide⟩ .nil)
  obtain ⟨regs, rnd, rlen, trace⟩ := h (.bvar 22) 4 18 linVw linBpos linVpos
    linFields linHWCore linHW_wf
    (by
      intro j hj
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · exact ⟨`start, rfl⟩
      · exact ⟨`valid, rfl⟩
      · exact ⟨`isCarryZero, rfl⟩
      · exact ⟨`carry, rfl⟩)
    (by
      intro j hj
      have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
          j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)
    linHW_body
    (by
      intro f hf
      simp only [linHWShape, linHWLayout, List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf; decide)
    (by
      intro o ho
      simp only [linHWShape, linHWLayout, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl <;> decide)
    linHW_scoped
  match regs, rlen, rnd, trace with
  | [racc], _, _, trace =>
  refine ⟨ids, nd, len, cache, racc, ?_⟩
  intro T inB inV seed st0 mems inputs pass rst ia
  obtain ⟨envs, hrun, hlen, hobs⟩ := trace T inB inV seed st0 mems inputs
    (by
      intro t st r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; exact pass t st)
    rst
    (by
      intro i r f hr hf
      have hi : i = 0 := by
        have := (List.getElem?_eq_some_iff.mp hf).1
        simp [linHWShape, linHWLayout] at this; omega
      subst hi
      simp only [List.getElem?_cons_zero, Option.some.injEq, linHWShape, linHWLayout] at hr hf
      subst hr; subst hf
      exact ia)
  refine ⟨envs, hrun, hlen, fun j hj => ⟨?_, ?_⟩⟩
  · exact hobs j hj { name := "acc", lo := 16, width := 8, ty := .bitVector 8 }
      (by simp [linHWShape, linHWLayout])
  · exact hobs j hj { name := "chk", lo := 8, width := 8, ty := .bitVector 8 }
      (by simp [linHWShape, linHWLayout])


/-! ## Source = reference machine, by the generic theorem

`denote_state` / `denote_out` prove once that a `circuit do` whose writes
and result are the typed values of the terms is its reference machine. For
the LIN checksum module the declaration-specific facts are DATA and `rfl`:
the typed `let`s, the next-value terms, that the body's writes are their
typed values (`linHW_writes`, `rfl`), and decidable facts about positions. -/

section Denote
open Tools.ShippingMachineRef Tools.ShippingMachineDenote

/-- The state tuple's `Inhabited` instance, at the sorts' types. -/
local instance : Inhabited (HList (tys [.bits 8])) := inferInstanceAs (Inhabited (HList Slots1))

/-- The `let`s as typed terms (the Bool `let`s as Bool terms). -/
noncomputable def linTyped : List (Σ s : SType, Term s) :=
  [⟨.bits 8, .bitsLit 8 0⟩, ⟨.bits 8, .bitsLit 8 255⟩, ⟨.bits 8, .bitsLit 8 1⟩,
   ⟨.bits 1, .bitsLit 1 0⟩,
   ⟨.bits (1 + 8), .concat (.bitsInput 1 5) (.bitsInput 8 1)⟩,
   ⟨.bits (1 + 8), .concat (.bitsInput 1 5) (.bitsInput 8 0)⟩,
   ⟨.bits 9, .binary .add (.bitsInput 9 6) (.bitsInput 9 7)⟩,
   ⟨.bits 9, .bitsLit 9 1⟩, ⟨.bits 9, .bitsLit 9 8⟩,
   ⟨.bits 9, .binary .shr (.bitsInput 9 8) (.bitsInput 9 10)⟩,
   ⟨.bits 9, .binary .and (.bitsInput 9 11) (.bitsInput 9 9)⟩,
   ⟨.bits 9, .bitsLit 9 0⟩,
   ⟨.bool, .compare .eq (.bitsInput 9 12) (.bitsInput 9 13)⟩,
   ⟨.bool, .boolNot (.boolInput 2)⟩,
   ⟨.bits 8, .slice linSliceName 0 8 (.bitsInput 9 8)⟩,
   ⟨.bits 8, .binary .add (.bitsInput 8 14) (.bitsInput 8 4)⟩,
   ⟨.bits 8, .mux (.boolInput 3) (.bitsInput 8 15) (.bitsInput 8 14)⟩,
   ⟨.bits 8, .binary .xor (.bitsInput 8 1) (.bitsInput 8 3)⟩]

theorem linTyped_fields : (linTyped.map fun l => toField l.1 l.2) = linFields := rfl

/-- The accumulator's next value. -/
def linNextT : Term (.bits 8) :=
  .mux (.boolInput 0) (.bitsInput 8 2) (.mux (.boolInput 1) (.bitsInput 8 16) (.bitsInput 8 1))

def linNexts : Terms [.bits 8] := .cons linNextT .nil

/-- The sort of every binder position. -/
def linK : Nat → Option SType := fun p =>
  [none, some .bool, some (.bits 8), some .bool, some (.bits 8),
   some (.bits 8), some (.bits 8), some (.bits 8), some (.bits 1), some (.bits 9),
   some (.bits 9), some (.bits 9), some (.bits 9), some (.bits 9), some (.bits 9),
   some (.bits 9), some (.bits 9), some .bool, some .bool, some (.bits 8), some (.bits 8),
   some (.bits 8), some (.bits 8)].getD p none

theorem lin_facts : TermFacts 4 4 18 linVw linBpos linVpos linK [.bits 8] linTyped where
  bools := by
    intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> exact ⟨rfl, by decide⟩
  bits := by
    intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
        j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, by decide⟩
  slots := by
    intro i s h
    have hi : i = 0 := by
      have := (List.getElem?_eq_some_iff.mp h).1
      simp at this; omega
    subst hi
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; rfl
  lets := by
    simp [LetsTyped, linTyped, reads, Term.WF, linBpos, linVpos, linVw, linK]

/-- The body's pending write is the typed value of the next-value term —
for every state signal, at every cycle. -/
theorem linHW_writes {D : DomainConfig} (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (S : Signal D (HList Slots1)) (t : Nat) :
    valsAt Slots1 (linCircuit (bools 1) (bits 2 8) (bools 3)
      (mkRegList S Slots1 (fun s => s) (fun f => f)) (mkHolds Slots1 S)).snd t =
    evalTerms
      (fun j => (typedVal 4 linBpos linVpos [.bits 8] linTyped bools bits t (S.val t)).b
        (linBpos j))
      (fun j w => (typedVal 4 linBpos linVpos [.bits 8] linTyped bools bits t (S.val t)).v
        (linVpos j) w) linNexts := rfl

set_option maxHeartbeats 1000000 in
/-- **The state of the LIN checksum is its reference machine's.** The
stream is the `circuit do`'s state loop (`circuit_state`, from the writes
being the terms' values). -/
theorem linHW_state {D : DomainConfig} (bools : Nat → Signal D Bool)
    (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (τ : Nat) :
    encState [.bits 8] ((stateLoop linInits (linCircuit (bools 1) (bits 2 8) (bools 3))).val τ) =
      linRef.state (fun τ p => (bools p).val τ) (fun τ p w => (bits p w).val τ) τ := by
  have hW : ∀ (l l' : Signal D (HList Slots1)) (t : Nat), l.val t = l'.val t →
      valsAt Slots1 (linCircuit (bools 1) (bits 2 8) (bools 3)
          (mkRegList l Slots1 (fun s => s) (fun f => f)) (mkHolds Slots1 l)).snd t =
        valsAt Slots1 (linCircuit (bools 1) (bits 2 8) (bools 3)
          (mkRegList l' Slots1 (fun s => s) (fun f => f)) (mkHolds Slots1 l')).snd t := by
    intro l l' t h
    rw [linHW_writes bools bits l t, linHW_writes bools bits l' t, h]
  obtain ⟨h0, hs⟩ := circuit_state linInits (linCircuit (bools 1) (bits 2 8) (bools 3)) hW
  refine denote_state (ss := [.bits 8])
    (fun t => (stateLoop linInits (linCircuit (bools 1) (bits 2 8) (bools 3))).val t)
    bools bits linTyped linNexts ⟨8, .bitsInput 8 1⟩ [⟨8, .bitsInput 8 17⟩, ⟨8, linNextT⟩] linHWCore
    linHWLayout.slots 2 rfl rfl ?_ ?_ ?_ lin_facts ?_ ?_ τ
  · intro i f hf
    have hi : i = 0 := by
      have := (List.getElem?_eq_some_iff.mp hf).1
      simp [linHWLayout] at this; omega
    subst hi
    simp only [linHWLayout, List.getElem?_cons_zero, Option.some.injEq] at hf
    subst hf
    exact ⟨⟨8, linNextT⟩, rfl, rfl, rfl⟩
  · rfl
  · intro i
    show encState [.bits 8] ((stateLoop linInits (linCircuit (bools 1) (bits 2 8) (bools 3))).val 0) i = _
    rw [h0]
    rcases i with _ | i
    · rfl
    · rfl
  · intro g hg
    simp only [linNexts, Terms.fields, toField, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    simp [linNextT, Term.WF, linVw]
  · intro t
    show (stateLoop linInits (linCircuit (bools 1) (bits 2 8) (bools 3))).val (t + 1) = _
    rw [hs t, linHW_writes bools bits]

set_option maxHeartbeats 1000000 in
/-- **Source-to-RTL execution of the LIN checksum module, by the generic
theorems.** The same statement as `linHW_execution`; the proof is the
reference-machine theorem of the emitted module (`linHW_reference`), the
generic identification of the state stream with its reference machine
(`denote_state`, `denote_out`; the stream is the `circuit do`'s state loop,
`stateLoop_stream`), and `rfl`. -/
theorem linHW_execution_generic {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``Sparkle.IP.Bus.LINHW.checksumHW [] false)
      mctx mref cctx cref w (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``Sparkle.IP.Bus.LINHW.checksumHW linHWShape)
    (closes : MachineCloses mctx mref cctx cref ``Sparkle.IP.Bus.LINHW.checksumHW linHWShape) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = 23 ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (racc : String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
        (∀ t st, t < T → SourceInputs ``Sparkle.IP.Bus.LINHW.checksumHW linIn ids cache
          (fun j => (bools j).val (T - 1 - t)) (fun j n => (bits j n).val (T - 1 - t))
          (seed t st)) →
        (∀ t st, seed t st racc = st racc) →
        (∀ t st, seed t st "rst" = 0) →
        st0 racc = 0 →
        ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
          ∀ j (hj : j < envs.length),
            (envs[j]'hj) "acc" = ((Sparkle.IP.Bus.LINHW.checksumHW (bools 1) (bits 2 8)
              (bools 3)).acc.val j).toNat ∧
            (envs[j]'hj) "chk" = ((Sparkle.IP.Bus.LINHW.checksumHW (bools 1) (bits 2 8)
              (bools 3)).chk.val j).toNat := by
  obtain ⟨ids, nd, len, cache, racc, h⟩ := linHW_reference hr entry closes
  refine ⟨ids, nd, len, cache, racc, ?_⟩
  intro D bools bits T seed st0 mems inputs pass rst ia
  obtain ⟨envs, hrun, hlen, hobs⟩ := h T (fun τ p => (bools p).val τ)
    (fun τ p w => (bits p w).val τ) seed st0 mems inputs pass rst ia
  refine ⟨envs, hrun, hlen, fun j hj => ?_⟩
  obtain ⟨hacc, hchk⟩ := hobs j hj
  have out := fun {s : SType} (ot : Term s) (hwf : ot.WF 4 18 linVw) (k : Nat) hk =>
    denote_out (ss := [.bits 8]) (fun t => (stateLoop linInits (linCircuit (bools 1) (bits 2 8) (bools 3))).val t)
      bools bits linTyped ⟨8, .bitsInput 8 1⟩ [⟨8, .bitsInput 8 17⟩, ⟨8, linNextT⟩] linHWCore
      linHWLayout.slots rfl lin_facts (linHW_state bools bits) ot hwf k hk j
  refine ⟨?_, ?_⟩
  · rw [hacc]
    exact (out (.bitsInput 8 1) (by simp [Term.WF, linVw]) 0 rfl).symm
  · rw [hchk]
    exact (out (.bitsInput 8 17) (by simp [Term.WF, linVw]) 1 rfl).symm

end Denote


run_cmd do
  if (← get).messages.hasErrors then throwError "machine entry regression failed"
  for name in [``mThree_execution, ``mThree_machine, ``mThree_state,
      ``lin_execution, ``lin_machine, ``lin_state, ``lin_lets, ``linHW_execution,
      ``linHW_machine, ``linHW_reference, ``linHW_state, ``linHW_execution_generic,
      ``Tools.ShippingMachineDenote.denote_state, ``Tools.ShippingMachineDenote.denote_out,
      ``Tools.ShippingMachineRef.machine_ref_trace,
      ``Tools.ShippingMachineClose.closeLets_eval,
      ``Tools.ShippingMachineEntry.chain_values,

      ``Tools.ShippingMachineEntry.synthesizeCombinationalCore_machine_sound,
      ``Tools.ShippingMachineEntry.synthesizeMachineCertified_sound,
      ``Tools.ShippingMachineEntry.machine_trace,
      ``Tools.ShippingMachineEntry.transition_facts,
      ``Tools.ShippingMachineClose.closeMachine_step,
      ``Tools.ShippingUnifiedExecutionSoundness.synthesizeMixedCertified_term_sound_at] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  logInfo m!"MACHINE ENDPOINT: source circuit do → real entry → N registers → trace; standard axioms only"

end Sparkle.Tests.Compiler.ShippingMachineEntryTest
