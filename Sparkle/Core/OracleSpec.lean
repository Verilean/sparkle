/-
  Oracle-Driven Reverse Synthesis Framework (Type-Class Based, Proof-Required)

  Users declare oracle reductions as type class instances with a mandatory
  equivalence proof. Without the proof, the instance cannot be constructed,
  preventing unsound FSM replacements.

  Example:

  ```lean
  structure MulState where
    rd : BitVec 64; rdx : BitVec 64; rs1 : BitVec 64; rs2 : BitVec 64

  instance : OracleReduction "pcpi_mul" MulState (BitVec 64 × BitVec 64) (BitVec 64) where
    step s := carrySaveStep s
    initState (rs1, rs2) := ⟨0, 0, rs1, rs2⟩
    extractResult s := s.rd ^^^ s.rdx
    compute (rs1, rs2) := rs1 * rs2
    numCycles := 32
    equiv := by ...  -- must prove step^32(init) = compute
    registers := [...]
    encodeInputs regs := (regs[0]!, regs[1]!)
    decodeResult result := [("rd", result), ("rdx", 0)]
    trigger regs := regs[5]! == 0
  ```
-/

import Sparkle.Core.JIT
import Sparkle.IR.AST

namespace Sparkle.Core.OracleSpec

open Sparkle.Core.JIT
open Sparkle.IR.AST

/-- A register role in an oracle specification. -/
structure RegRole where
  /-- Logical name (e.g., "rs1") -/
  role : String
  /-- Glob pattern to match IR register names. "*" = prefix wildcard. -/
  namePattern : String
  /-- True if this register is written by the oracle (output). -/
  isOutput : Bool := false
  deriving Repr, Inhabited

/-- Iterate a function n times. -/
def iterateN (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => iterateN f n (f x)

/-- Type class for oracle-driven FSM reductions with mandatory proof.

    Type parameters:
    - `tag`: string literal identifying this reduction (e.g., "pcpi_mul")
    - `State`: internal FSM state type (e.g., rd × rdx × rs1 × rs2)
    - `Input`: input type extracted from registers (e.g., rs1 × rs2)
    - `Output`: result type to inject back (e.g., product)

    The `equiv` field requires a proof that iterating `step` for `numCycles`
    from `initState input` and extracting the result equals `compute input`.
    Without this proof, the instance cannot be constructed. -/
class OracleReduction (tag : String) (State : Type) (Input : Type) (Output : Type) where
  /-- One cycle of the FSM (pure Lean function modeling the hardware) -/
  step : State → State
  /-- Map input register values to the FSM's initial state -/
  initState : Input → State
  /-- Extract the final result from the FSM state -/
  extractResult : State → Output
  /-- Direct computation (what the oracle actually executes) -/
  compute : Input → Output
  /-- Number of cycles the FSM takes -/
  numCycles : Nat
  /-- MANDATORY PROOF: iterating step = direct compute.
      This is the soundness guarantee. Without it, the instance
      cannot be constructed (unless sorry is used, which is explicit). -/
  equiv : ∀ (input : Input),
    extractResult (iterateN step numCycles (initState input)) = compute input

  -- Runtime interface (connects Lean types to JIT register indices) --

  /-- Register roles for pattern matching -/
  registers : List RegRole
  /-- Encode JIT register values → typed Input -/
  encodeInputs : Array UInt64 → Input
  /-- Decode typed Output → (role, value) pairs to write back -/
  decodeResult : Output → List (String × UInt64)
  /-- Trigger condition on raw register values -/
  trigger : Array UInt64 → Bool
  /-- Wire patterns to eliminate from IR (optional) -/
  deadWirePatterns : List String := []

/-- Resolved oracle: type class instance with register indices bound. -/
structure ResolvedOracle where
  tag : String
  regIndices : Array UInt32
  roleToIdx : List (String × Nat)

/-- Mutable state for a running oracle. -/
structure OracleState where
  totalSkipped : Nat := 0
  triggerCount : Nat := 0

/-- Find first occurrence of needle in haystack, returns character index. -/
private def findSubstr (haystack needle : String) : Option Nat :=
  let hLen := haystack.length
  let nLen := needle.length
  if nLen > hLen then none
  else Id.run do
    for i in [:hLen - nLen + 1] do
      if (haystack.drop i).toString.startsWith needle then return some i
    return none

/-- Match a name against a glob pattern.
    Splits pattern on `*` and checks that all segments appear in order.
    Examples: `*pcpi_mul*_seq*` matches `_gen_picorv32_pcpi_mul_next_rd_seq42`. -/
def matchPattern (pattern : String) (name : String) : Bool :=
  let segments := pattern.splitOn "*" |>.filter (· != "")
  if segments.isEmpty then true
  else Id.run do
    let mut pos : Nat := 0
    for seg in segments do
      let remaining := (name.drop pos).toString
      match findSubstr remaining seg with
      | some idx => pos := pos + idx + seg.length
      | none => return false
    return true

/-- Resolve an OracleReduction instance against a JITHandle. -/
def resolve (tag : String) {State Input Output : Type}
    [inst : OracleReduction tag State Input Output] (handle : JITHandle)
    : IO (Option ResolvedOracle) := do
  let numRegs ← JIT.numRegs handle
  let mut indices : Array UInt32 := #[]
  let mut roleMap : List (String × Nat) := []
  let mut idx : Nat := 0
  for role in inst.registers do
    let mut found := false
    for i in [:numRegs.toNat] do
      let name ← JIT.regName handle i.toUInt32
      if matchPattern role.namePattern name then
        indices := indices.push i.toUInt32
        roleMap := roleMap ++ [(role.role, idx)]
        found := true
        break
    if !found then return none
    idx := idx + 1
  return some { tag, regIndices := indices, roleToIdx := roleMap }

/-- Create a runtime oracle from a resolved OracleReduction. -/
def mkOracle (tag : String) {State Input Output : Type}
    [inst : OracleReduction tag State Input Output] (resolved : ResolvedOracle)
    : IO ((JITHandle → Nat → Array UInt64 → IO (Option Nat)) × IO.Ref OracleState) := do
  let stateRef ← IO.mkRef ({} : OracleState)

  let oracle : JITHandle → Nat → Array UInt64 → IO (Option Nat) := fun handle _cycle _vals => do
    let mut regVals : Array UInt64 := #[]
    for idx in resolved.regIndices do
      regVals := regVals.push (← JIT.getReg handle idx)

    if !inst.trigger regVals then return none

    -- Use the verified compute function
    let input := inst.encodeInputs regVals
    let result := inst.compute input
    let outputs := inst.decodeResult result

    for (role, value) in outputs do
      match resolved.roleToIdx.find? (·.1 == role) with
      | some (_, roleIdx) =>
        if h : roleIdx < resolved.regIndices.size then
          JIT.setReg handle resolved.regIndices[roleIdx] value
      | none => pure ()

    stateRef.modify fun s => {
      totalSkipped := s.totalSkipped + inst.numCycles
      triggerCount := s.triggerCount + 1
    }
    return some inst.numCycles

  return (oracle, stateRef)

/-- One-shot: resolve + create oracle. -/
def mkOracleAuto (tag : String) (State Input Output : Type)
    [OracleReduction tag State Input Output] (handle : JITHandle)
    : IO (Option ((JITHandle → Nat → Array UInt64 → IO (Option Nat)) × IO.Ref OracleState)) := do
  match ← resolve tag (State := State) (Input := Input) (Output := Output) handle with
  | some resolved => some <$> mkOracle tag (State := State) (Input := Input) (Output := Output) resolved
  | none => return none

/-- Compose multiple oracle callbacks: first match wins. -/
def composeOracles
    (oracles : List (JITHandle → Nat → Array UInt64 → IO (Option Nat)))
    : JITHandle → Nat → Array UInt64 → IO (Option Nat) :=
  fun handle cycle vals => do
    for oracle in oracles do
      match ← oracle handle cycle vals with
      | some n => return some n
      | none => pure ()
    return none

/-- IR reduction: remove dead wires and stub output registers. -/
def reduceIR (tag : String) (State Input Output : Type)
    [inst : OracleReduction tag State Input Output]
    (body : List Stmt) : List Stmt :=
  if inst.deadWirePatterns.isEmpty then body
  else
    let isDead (name : String) : Bool :=
      inst.deadWirePatterns.any fun pat => matchPattern pat name
    let outputRoles := inst.registers.filter (·.isOutput)
    let isOutputReg (name : String) : Bool :=
      outputRoles.any fun role => matchPattern role.namePattern name
    body.filterMap fun s =>
      match s with
      | .assign lhs _ =>
        if isDead lhs then none else some s
      | .register output clk rst _input iv =>
        if isOutputReg output then
          some (.register output clk rst (.ref output) iv)
        else some s
      | other => some other

end Sparkle.Core.OracleSpec
