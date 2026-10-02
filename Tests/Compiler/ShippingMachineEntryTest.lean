import Lean
import Sparkle.Core.CircuitDo
import Tools.ShippingMachineEntry
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
def simOut (m : Sparkle.IR.AST.Module) (k : Nat) (ins : Nat → String → Option Nat) :
    Option (List Nat) :=
  let init : String → Nat := fun n =>
    (m.body.findSome? fun st => match st with
      | .register o _ _ _ i => if o == n then some i.toNat else none
      | _ => none).getD 0
  (runModule (weAll m) m.body
    (fun j st => fun n => match ins (k - 1 - j) n with
      | some v => v
      | none => if n == "rst" then 0 else st n) k init (fun _ _ => 0)).map (·.map (· "out"))

def bStream {dom : DomainConfig} (seed : Nat) : Signal dom Bool :=
  ⟨fun t => (t * 7 + seed * 3 + t / 3) % 3 != 0⟩
def vStream {dom : DomainConfig} (w seed : Nat) : Signal dom (BitVec w) :=
  ⟨fun t => BitVec.ofNat w (t * 37 + seed * 11 + t * t)⟩

/-- The declaration takes the machine route; returns the shipped module. -/
def machineModule (name : Name) (slots : Nat) (rk : Sparkle.IR.Type.ResetKind) :
    TermElabM Sparkle.IR.AST.Module := do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  let ci ← getConstInfo name
  let ec := entryConst true false [] ci pred inl (userProjection? env)
  unless (certifiedShape? false [] ec).isNone && (mixedCertifiedShape? false [] ec pred).isNone do
    throwError "{name}: a combinational or register gate accepts the declaration"
  let some shape := machineShape? false [] ec (userProjection? env)
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
      m.outputs.map (·.name) == ["out"] do
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
  logInfo m!"MACHINE ROUTE: 5 declarations (3, 2, 2, 1, 1 slots), {K} cycles each, emitted module == source"

/-! ## The three-slot machine, end to end -/

#def_machine_body mThreeBody of mThree

def mThreeIn : List (Name × MixedGateBinder) := [(`dom, .domain), (`en, .bool), (`d, .bits 4)]
def mThreeSlots : List (Name × MixedGateBinder) := [(`a, .bits 4), (`b, .bits 4), (`g, .bool)]
def mThreeLayout : Layout :=
  { slots := [{ lo := 5, width := 4, init := 0 }, { lo := 1, width := 4, init := 3 },
      { lo := 0, width := 1, init := 1 }]
    outLo := 9, outWidth := 4, outTy := .bitVector 4, resetKind := .asynchronous }
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
      (fun j => inputExpr mThreeShape.binders.length (mThreeVpos j)) mThreeTerm := rfl

theorem mThreeTerm_wf : mThreeTerm.WF 2 3 (fun _ => 4) := by
  simp [mThreeTerm, Term.WF]

run_cmd liftTermElabM do
  let env ← getEnv
  let ci ← getConstInfo ``mThree
  let some shape := machineShape? false []
      (entryConst true false [] ci (instancePredicate env) (userInliner env) (userProjection? env))
      (userProjection? env)
    | throwError "mThree: not a machine shape"
  let .ok r := reflExpr shape.body | throwError "mThree: body not reflectable"
  unless (← getConstInfo ``mThreeBody).value? == some r do
    throwError "mThreeBody is not the machine body of mThree"
  unless shape.binders == mThreeIn ++ mThreeSlots && shape.layout.slots == mThreeLayout.slots &&
      shape.layout.outLo == mThreeLayout.outLo && shape.layout.outWidth == mThreeLayout.outWidth &&
      shape.layout.outTy == mThreeLayout.outTy &&
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
    MachinePreserves ``mThree mThreeShape mThreeIn mThreeSlots m := by
  apply synthesizeCombinationalCore_machine_sound hr entry rfl
  · intro name n hmem
    simp only [mThreeShape, mThreeIn, mThreeSlots, List.cons_append, List.nil_append,
      List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, reduceCtorEq, and_false,
      false_or, MixedGateBinder.bits.injEq] at hmem
    omega
  · intro b hb
    simp only [mThreeSlots, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl <;> simp
  · exact .cons rfl (.cons rfl (.cons rfl .nil))
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
    mThreeTerm mThreeTerm_wf
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
  refine ⟨envs, hrun, hlen, fun j hj => ?_⟩
  rw [hobs j hj, mThree_packed, hB5, hB1, hV2, hV3, hV4, out j]
  show mask 4 (_ >>> 9) = _
  rw [field_hi _ _ (by decide)]
  exact field_all _

/-! ## The LIN checksum of the IP library, end to end

`IP/Bus/LINHW.checksumHW`: one accumulator register, the carry folded back
in, some twenty hardware `let`s, a structure result. `linChk` is its `chk`
field. -/

#def_machine_body linBody of linChk

def linIn : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`start, .bool), (`byteIn, .bits 8), (`valid, .bool)]
def linSlots : List (Name × MixedGateBinder) := [(`accR, .bits 8)]
def linLayout : Layout :=
  { slots := [{ lo := 0, width := 8, init := 0 }]
    outLo := 8, outWidth := 8, outTy := .bitVector 8, resetKind := .asynchronous }
noncomputable def linShape : MachineShape :=
  { binders := linIn ++ linSlots, body := linBody, layout := linLayout }

/-- The first `fun` binder name of an expression (the slice's binder is a
hygienic macro name of the IP source file). -/
def firstLamName : Lean.Expr → Option Name
  | .lam n _ _ _ => some n
  | .app f a => (firstLamName f).orElse fun _ => firstLamName a
  | _ => none

noncomputable def linSliceName : Name := (firstLamName linBody).getD .anonymous

/-- The nine-bit sum of the accumulator and the byte. -/
def linSum : Term (.bits (1 + 8)) :=
  .binary .add (.concat (.bitsLit 1 0) (.bitsInput 8 1)) (.concat (.bitsLit 1 0) (.bitsInput 8 0))

/-- The packed transition: `chk ++ nextAcc`. Bool inputs: `start`, `valid`;
BitVec inputs: `byteIn`, `accR`. -/
noncomputable def linTerm : Term (.bits (8 + 8)) :=
  .concat (.binary .xor (.bitsInput 8 1) (.bitsLit 8 255))
    (.mux (.boolInput 0) (.bitsLit 8 0)
      (.mux (.boolInput 1)
        (.mux (.boolNot (.compare .eq
            (.binary .and (.binary .shr linSum (.bitsLit 9 8)) (.bitsLit 9 1)) (.bitsLit 9 0)))
          (.binary .add (.slice linSliceName 0 8 linSum) (.bitsLit 8 1))
          (.slice linSliceName 0 8 linSum))
        (.bitsInput 8 1)))

def linBpos : Nat → Nat := fun j => if j = 0 then 1 else 3
def linVpos : Nat → Nat := fun j => if j = 0 then 2 else 4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem lin_body : linShape.body =
    quote (.bvar 4) (fun j => inputExpr linShape.binders.length (linBpos j))
      (fun j => inputExpr linShape.binders.length (linVpos j)) linTerm := rfl

theorem linTerm_wf : linTerm.WF 2 2 (fun _ => 8) := by
  simp [linTerm, linSum, Term.WF]


run_cmd liftTermElabM do
  let env ← getEnv
  let ci ← getConstInfo ``linChk
  let some shape := machineShape? false []
      (entryConst true false [] ci (instancePredicate env) (userInliner env) (userProjection? env))
      (userProjection? env)
    | throwError "linChk: not a machine shape"
  let .ok r := reflExpr shape.body | throwError "linChk: body not reflectable"
  unless (← getConstInfo ``linBody).value? == some r do
    throwError "linBody is not the machine body of linChk"
  unless shape.binders == linIn ++ linSlots && shape.layout.slots == linLayout.slots &&
      shape.layout.outLo == linLayout.outLo && shape.layout.outWidth == linLayout.outWidth &&
      shape.layout.outTy == linLayout.outTy &&
      shape.layout.resetKind == linLayout.resetKind do
    throwError "linShape is not the machine shape of linChk"

theorem lin_machine {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``linChk [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref ``linChk linShape) :
    MachinePreserves ``linChk linShape linIn linSlots m := by
  apply synthesizeCombinationalCore_machine_sound hr entry rfl
  · intro name n hmem
    simp only [linShape, linIn, linSlots, List.cons_append, List.nil_append,
      List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, reduceCtorEq, and_false,
      false_or, MixedGateBinder.bits.injEq] at hmem
    omega
  · intro b hb
    simp only [linSlots, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb; simp
  · exact .cons rfl .nil
  · decide

/-- The accumulator's next value when a byte is taken: the eight-bit sum
with the carry folded back in. -/
def linFold (acc byte : BitVec 8) : BitVec 8 :=
  if !(((0#1 ++ acc : BitVec 9) + (0#1 ++ byte : BitVec 9)) >>> 8#9 &&& 1#9 == 0#9) then
    BitVec.extractLsb' 0 8 ((0#1 ++ acc : BitVec 9) + (0#1 ++ byte : BitVec 9)) + 1#8
  else BitVec.extractLsb' 0 8 ((0#1 ++ acc : BitVec 9) + (0#1 ++ byte : BitVec 9))

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

/-- The packed transition value of the LIN checksum on an accumulator and
inputs. -/
theorem lin_packed (B : Nat → Bool) (V : (j : Nat) → (n : Nat) → BitVec n) :
    packedAt linTerm linBpos linVpos B V =
      ((V 4 8 ^^^ 255#8) ++
        (if B 1 then 0#8 else if B 3 then linFold (V 4 8) (V 2 8) else V 4 8)).toNat := rfl

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
    (entry : MachineDefines mctx mref cctx cref ``linChk linShape) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = 5 ∧
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
  obtain ⟨ids, nd, len, cache, h⟩ := machine_trace (lin_machine hr entry) rfl
  obtain ⟨regs, rnd, rlen, trace⟩ := h (.bvar 4) 2 2 (fun _ => 8) linBpos linVpos
    linTerm linTerm_wf
    (by
      intro j hj
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl
      · exact ⟨`start, rfl⟩
      · exact ⟨`valid, rfl⟩)
    (by
      intro j hj
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl
      · exact ⟨`byteIn, rfl⟩
      · exact ⟨`accR, rfl⟩)
    lin_body
  match regs, rlen, rnd, trace with
  | [racc], _, _, trace =>
  refine ⟨ids, nd, len, cache, racc, ?_⟩
  intro D bools bits T seed st0 mems inputs pass rst ia
  obtain ⟨s0, step, out⟩ := lin_state (bools 1) (bits 2 8) (bools 3)
  generalize stateLoop linInits (linCircuit (bools 1) (bits 2 8) (bools 3)) = S at s0 step out
  let B : Nat → Nat → Bool := fun τ j => (bools j).val τ
  let V : Nat → (j : Nat) → (n : Nat) → BitVec n := fun τ j n =>
    if j = 4 then BitVec.ofNat n (S.val τ).1.toNat else (bits j n).val τ
  have hV2 : ∀ τ, V τ 2 8 = (bits 2 8).val τ := fun τ => rfl
  have hV4 : ∀ τ, V τ 4 8 = (S.val τ).1 := fun τ => by simp [V]
  obtain ⟨envs, hrun, hlen, hobs⟩ := trace T B V seed st0 mems
    (by
      intro t st ht
      refine sourceInputs_congr nd (fun _ _ => rfl) ?_ (inputs t st ht)
      intro j hj n
      have h4 : j ≠ 4 := by simp [linIn] at hj; omega
      simp [V, h4])
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
      rw [lin_packed, hV2, hV4]
      simp only [List.getElem?_cons_zero, Option.some.injEq, linSlots, linShape, linLayout]
        at hf hb
      subst hf; subst hb
      show (V (τ + 1) 4 8).toNat = _
      rw [hV4, step τ, field_lo _ _ (by decide)]
      exact (field_all _).symm)
  refine ⟨envs, hrun, hlen, fun j hj => ?_⟩
  rw [hobs j hj, lin_packed, hV2, hV4, out j]
  show mask 8 (_ >>> 8) = _
  rw [field_hi _ _ (by decide)]
  exact field_all _


run_cmd do
  if (← get).messages.hasErrors then throwError "machine entry regression failed"
  for name in [``mThree_execution, ``mThree_machine, ``mThree_state,
      ``lin_execution, ``lin_machine, ``lin_state,
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
