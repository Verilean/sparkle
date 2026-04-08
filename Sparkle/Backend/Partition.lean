/-
  IR Graph Partitioning for Multi-Thread Simulation

  Splits a flattened Module into 2 partitions (CPU + Peripheral)
  based on wire name prefixes. Identifies boundary signals that
  must be exchanged between partitions each cycle.
-/

import Sparkle.IR.AST
import Sparkle.IR.Type

open Sparkle.IR.AST
open Sparkle.IR.Type

namespace Sparkle.Backend.Partition

/-- Classification of a wire/register into a partition -/
inductive PartitionId where
  | cpu
  | peripheral
  deriving BEq, Repr

/-- Classify a wire name into CPU or Peripheral partition.
    Names containing "picorv32" or bus-related prefixes go to CPU. -/
def classifyWire (name : String) : PartitionId :=
  if name.startsWith "picorv32" || name.startsWith "_gen_picorv32" ||
     name.startsWith "_gen_shared" || name.startsWith "_gen_trap" ||
     name.startsWith "_gen_mem_valid" || name.startsWith "_gen_mem_instr" ||
     name.startsWith "_gen_mem_addr" || name.startsWith "_gen_mem_wdata" ||
     name.startsWith "_gen_mem_wstrb" then
    .cpu
  else
    .peripheral

/-- Collect all Expr.ref names in an expression -/
partial def collectRefs : Expr → List String
  | .ref name => [name]
  | .op _ args => args.flatMap collectRefs
  | .concat args => args.flatMap collectRefs
  | .slice e _ _ => collectRefs e
  | .index arr idx => collectRefs arr ++ collectRefs idx
  | _ => []

/-- Result of partitioning a module -/
structure PartitionResult where
  cpuModule : Module
  periModule : Module
  /-- Signals that CPU writes and Peripheral reads -/
  cpuToPeri : List Port
  /-- Signals that Peripheral writes and CPU reads -/
  periToCpu : List Port

/-- Partition a flattened module into CPU and Peripheral sub-modules.
    Returns two modules + boundary signal lists. -/
def partitionModule (m : Module) : PartitionResult := Id.run do
  let mut cpuBody : List Stmt := []
  let mut periBody : List Stmt := []
  let mut cpuWires : List Port := []
  let mut periWires : List Port := []

  -- Track which partition each wire belongs to
  let mut wirePartition : List (String × PartitionId) := []

  -- Collect register names to avoid wire/register duplication
  let registerNames := m.body.filterMap fun s => match s with
    | .register name _ _ _ _ => some name | _ => none

  -- Classify wires (exclude register outputs to avoid duplicate declarations)
  for w in m.wires do
    if registerNames.contains w.name then pure ()  -- skip: declared by register
    else
      let pid := classifyWire w.name
      wirePartition := wirePartition ++ [(w.name, pid)]
      if pid == .cpu then cpuWires := cpuWires ++ [w]
      else periWires := periWires ++ [w]

  -- Classify statements
  for s in m.body do
    match s with
    | .assign name _ =>
      if classifyWire name == .cpu then cpuBody := cpuBody ++ [s]
      else periBody := periBody ++ [s]
    | .register name _ _ _ _ =>
      if classifyWire name == .cpu then cpuBody := cpuBody ++ [s]
      else periBody := periBody ++ [s]
    | .memory name _ _ _ _ _ _ _ _ _ =>
      if classifyWire name == .cpu then cpuBody := cpuBody ++ [s]
      else periBody := periBody ++ [s]
    | _ => cpuBody := cpuBody ++ [s]  -- default to CPU

  -- Find boundary signals: wires referenced across partitions
  let mut cpuToPeri : List Port := []
  let mut periToCpu : List Port := []
  let mut seenBoundary : List String := []

  for s in cpuBody ++ periBody do
    let (name, refs) := match s with
      | .assign n rhs => (n, collectRefs rhs)
      | .register n _ _ input _ => (n, collectRefs input)
      | .memory _ _ _ _ wa wd we _ _ _ =>
        ("", collectRefs wa ++ collectRefs wd ++ collectRefs we)
      | _ => ("", [])
    let stmtPart := classifyWire name
    for r in refs do
      if !seenBoundary.contains r then
        let refPart := classifyWire r
        if stmtPart == .cpu && refPart == .peripheral then
          -- CPU reads from peripheral
          let ty := match (m.wires ++ m.inputs ++ m.outputs).find? (·.name == r) with
            | some p => p.ty | none => .bitVector 32
          periToCpu := periToCpu ++ [{ name := r, ty }]
          seenBoundary := seenBoundary ++ [r]
        else if stmtPart == .peripheral && refPart == .cpu then
          -- Peripheral reads from CPU
          let ty := match (m.wires ++ m.inputs ++ m.outputs).find? (·.name == r) with
            | some p => p.ty | none => .bitVector 32
          cpuToPeri := cpuToPeri ++ [{ name := r, ty }]
          seenBoundary := seenBoundary ++ [r]

  -- Build sub-modules
  -- Boundary signals become both output of source and input of destination
  let cpuOutputs := m.outputs.filter (classifyWire ·.name == .cpu)
  let periOutputs := m.outputs.filter (classifyWire ·.name == .peripheral)

  let cpuMod : Module := {
    name := s!"{m.name}_cpu"
    inputs := m.inputs ++ periToCpu  -- CPU reads boundary from peripheral
    outputs := cpuOutputs ++ cpuToPeri  -- CPU sends boundary to peripheral
    wires := cpuWires
    body := cpuBody
  }

  let periMod : Module := {
    name := s!"{m.name}_peri"
    inputs := m.inputs ++ cpuToPeri  -- Peripheral reads boundary from CPU
    outputs := periOutputs ++ periToCpu  -- Peripheral sends boundary to CPU
    wires := periWires
    body := periBody
  }

  { cpuModule := cpuMod
    periModule := periMod
    cpuToPeri := cpuToPeri
    periToCpu := periToCpu }

end Sparkle.Backend.Partition
