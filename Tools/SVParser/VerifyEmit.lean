/-
  `#verify_emit f` — kernel-checked proof that the SystemVerilog Sparkle
  EMITS for `f` denotes the same circuit as the IR it was emitted from.

  The command closes the emission loop inside Lean:

      f (Signal DSL)
        --synthesizeHierarchical-->  IR design D
        --toVerilogDesign------->    SystemVerilog text
        --SVParser parse+lower-->    IR design D'
        --this command---------->    per-register / per-output theorems
                                     D.cone ≡ D'.cone, proved by bv_decide

  For every register the NEXT-STATE cone and for every output port the
  OUTPUT cone is fully inlined over (inputs ∪ registers) on both sides —
  so the proof is invariant under the re-structuring the parser's
  optimizer performs — then reflected into pure `BitVec` terms and proved
  equal with `bv_decide` (the Lean-kernel-checked SAT pipeline; no
  external tool in the trusted base).  Combined with the structural
  checks (same ports, same registers, same initial values, same reset),
  stepwise cone equality gives full sequential equivalence by induction.

  v1 scope: single-module designs (no sub-instances), no memories, all
  widths ≤ the sizes bv_decide can absorb (DSL-scale circuits — this is
  a proof about SPARKLE-AUTHORED designs, not the XiangShan-scale ingest
  path, which is checked by co-sim + yosys equiv in CI instead).

  ⚠ same caveat as `#verify_eq` (docs/KnownIssues.md Issue 2): call this
  from interactively-run files / `lake env lean` drivers, not from
  modules imported by the default build target.
-/

import Lean
import Sparkle.Compiler.Elab
import Sparkle.Backend.Verilog
import Sparkle.IR.Optimize
import Tools.SVParser

namespace Tools.SVParser.VerifyEmit

open Lean Elab Command
open Sparkle.IR.AST
open Sparkle.IR.Optimize (buildDefMap DefMap)

def isClockName (n : String) : Bool :=
  n == "clk" || n == "clock"

def varIdent (n : String) : Ident :=
  mkIdent (Name.mkSimple s!"v_{Sparkle.Backend.Verilog.sanitizeName n}")

/-- Widths of every named wire/port in a module. -/
def widthTable (m : Sparkle.IR.AST.Module) : Std.HashMap String Nat :=
  (m.inputs ++ m.outputs ++ m.wires).foldl
    (fun h p => h.insert p.name p.ty.bitWidth) {}

/-- Fully inline a cone over (inputs ∪ registers): substitute assign
    definitions until only input/register refs remain. -/
partial def inlineCone (dm : DefMap) (stopAt : Std.HashMap String Bool)
    (fuel : Nat) : Sparkle.IR.AST.Expr → Except String Sparkle.IR.AST.Expr
  | .ref n =>
    if stopAt.contains n then .ok (.ref n)
    else match fuel, dm.get? n with
      | 0, _ => .error s!"cone inlining fuel exhausted at `{n}` (combinational cycle?)"
      | _, none => .error s!"`{n}` is neither an input, a register, nor assigned"
      | fuel + 1, some rhs => inlineCone dm stopAt fuel rhs
  | .op o args => do .ok (.op o (← args.mapM (inlineCone dm stopAt fuel)))
  | .concat args => do .ok (.concat (← args.mapM (inlineCone dm stopAt fuel)))
  | .slice e hi lo => do .ok (.slice (← inlineCone dm stopAt fuel e) hi lo)
  | .index .. => .error "memories/dynamic indexing unsupported by #verify_emit (v1)"
  | .sliceDim .. => .error "symbolic-width slices unsupported by #verify_emit (v1)"
  | e => .ok e

/-- Width of an inlined expression (refs are inputs/registers only). -/
partial def widthOf (wt : Std.HashMap String Nat) : Sparkle.IR.AST.Expr → Except String Nat
  | .const _ w => .ok w
  | .ref n => match wt.get? n with
    | some w => .ok w
    | none => .error s!"unknown width for `{n}`"
  | .slice _ hi lo => .ok (hi - lo + 1)
  | .concat args => do
    let ws ← args.mapM (widthOf wt)
    .ok (ws.foldl (· + ·) 0)
  | .op op args =>
    match op, args with
    | .eq, _ | .lt_u, _ | .lt_s, _ | .le_u, _ | .le_s, _
    | .gt_u, _ | .gt_s, _ | .ge_u, _ | .ge_s, _ => .ok 1
    | .mux, [_, t, _] => widthOf wt t
    | .not, [a] => widthOf wt a
    | .neg, [a] => widthOf wt a
    | _, a :: _ => widthOf wt a
    | _, [] => .error "empty operator"
  | _ => .error "unsupported expression shape"

/-- Reflect an inlined IR expression into a `BitVec` term.  Semantics
    mirror the CSim/Verilog backends: ring/bitwise ops at operand width,
    comparisons produce `BitVec 1`, mux tests ≠ 0, shifts by dynamic
    `BitVec` amounts (≥ width ⇒ 0, the Verilog rule), slices via
    `extractLsb'`, MSB-first concat via `++`. -/
partial def denote (wt : Std.HashMap String Nat) :
    Sparkle.IR.AST.Expr → CommandElabM Term
  | .const v w =>
    if v < 0 then
      `((-(BitVec.ofNat $(quote w) $(quote v.natAbs)) : BitVec $(quote w)))
    else
      `((BitVec.ofNat $(quote w) $(quote v.toNat)))
  | .ref n => pure (varIdent n)
  | .slice e hi lo => do
    `((BitVec.extractLsb' $(quote lo) $(quote (hi - lo + 1)) $(← denote wt e)))
  | .concat args => do
    match args with
    | [] => throwError "#verify_emit: empty concat"
    | a :: rest =>
      let mut acc ← denote wt a
      for r in rest do
        acc ← `(($acc ++ $(← denote wt r)))
      pure acc
  | .op o args => do
    match o, args with
    | .and, [a, b] => `(($(← denote wt a) &&& $(← denote wt b)))
    | .or,  [a, b] => `(($(← denote wt a) ||| $(← denote wt b)))
    | .xor, [a, b] => `(($(← denote wt a) ^^^ $(← denote wt b)))
    | .add, [a, b] => `(($(← denote wt a) + $(← denote wt b)))
    | .sub, [a, b] => `(($(← denote wt a) - $(← denote wt b)))
    | .mul, [a, b] => `(($(← denote wt a) * $(← denote wt b)))
    | .not, [a]    => `((~~~ $(← denote wt a)))
    | .neg, [a]    => `((- $(← denote wt a)))
    | .eq,  [a, b] =>
      `((if $(← denote wt a) = $(← denote wt b) then (1 : BitVec 1) else 0))
    | .lt_u, [a, b] =>
      `((if BitVec.ult $(← denote wt a) $(← denote wt b) then (1 : BitVec 1) else 0))
    | .le_u, [a, b] =>
      `((if BitVec.ule $(← denote wt a) $(← denote wt b) then (1 : BitVec 1) else 0))
    | .gt_u, [a, b] =>
      `((if BitVec.ult $(← denote wt b) $(← denote wt a) then (1 : BitVec 1) else 0))
    | .ge_u, [a, b] =>
      `((if BitVec.ule $(← denote wt b) $(← denote wt a) then (1 : BitVec 1) else 0))
    | .lt_s, [a, b] =>
      `((if BitVec.slt $(← denote wt a) $(← denote wt b) then (1 : BitVec 1) else 0))
    | .le_s, [a, b] =>
      `((if BitVec.sle $(← denote wt a) $(← denote wt b) then (1 : BitVec 1) else 0))
    | .gt_s, [a, b] =>
      `((if BitVec.slt $(← denote wt b) $(← denote wt a) then (1 : BitVec 1) else 0))
    | .ge_s, [a, b] =>
      `((if BitVec.sle $(← denote wt b) $(← denote wt a) then (1 : BitVec 1) else 0))
    | .mux, [c, t, e] => do
      let wc ← match widthOf wt c with
        | .ok w => pure w
        | .error msg => throwError "#verify_emit: {msg}"
      let dc ← denote wt c
      let dt ← denote wt t
      let de ← denote wt e
      `((if $dc ≠ (0 : BitVec $(quote wc)) then $dt else $de))
    | .shl, [a, b] => `(($(← denote wt a) <<< $(← denote wt b)))
    | .shr, [a, b] => `(($(← denote wt a) >>> $(← denote wt b)))
    | .asr, [a, b] => `((BitVec.sshiftRight' $(← denote wt a) $(← denote wt b)))
    | _, _ => throwError "#verify_emit: unsupported operator {repr o} / arity {args.length}"
  | e => throwError "#verify_emit: unsupported expression {repr e}"

structure Obligation where
  label : String     -- register or output name
  lhs   : Sparkle.IR.AST.Expr -- inlined cone in the source design
  rhs   : Sparkle.IR.AST.Expr -- inlined cone in the reparsed design

/-- Collect the per-register next-state and per-output cones of a module,
    fully inlined over (inputs ∪ registers). -/
def conesOf (m : Sparkle.IR.AST.Module) : Except String (List (String × Sparkle.IR.AST.Expr) × List (String × Sparkle.IR.AST.Expr)) := do
  if m.body.any (fun s => match s with | .inst .. => true | _ => false) then
    .error "sub-instances unsupported by #verify_emit (v1) — flatten first"
  else if m.body.any (fun s => match s with | .memory .. => true | _ => false) then
    .error "memories unsupported by #verify_emit (v1)"
  else
  let dm := buildDefMap m.body
  let stopAt : Std.HashMap String Bool := Id.run do
    let mut h : Std.HashMap String Bool := {}
    for p in m.inputs do h := h.insert p.name true
    for s in m.body do
      match s with
      | .register out _ _ _ _ => h := h.insert out true
      | _ => pure ()
    return h
  let mut regCones : List (String × Sparkle.IR.AST.Expr) := []
  for s in m.body do
    match s with
    | .register out _ _ input _ =>
      regCones := regCones ++ [(out, ← inlineCone dm stopAt 10000 input)]
    | _ => pure ()
  let mut outCones : List (String × Sparkle.IR.AST.Expr) := []
  for p in m.outputs do
    outCones := outCones ++ [(p.name, ← inlineCone dm stopAt 10000 (.ref p.name))]
  .ok (regCones, outCones)

/-- Registers of a module as (name, width, init, rstName, kind). -/
def regSigs (m : Sparkle.IR.AST.Module) : List (String × Nat × Int × String) :=
  let wt := widthTable m
  m.body.filterMap fun s => match s with
    | .register out _ (rst, _) _ init => some (out, wt.getD out 0, init, rst)
    | _ => none

syntax (name := verifyEmitCmd) "#verify_emit " ident : command

@[command_elab verifyEmitCmd]
def elabVerifyEmit : CommandElab := fun stx => do
  match stx with
  | `(#verify_emit $f:ident) => do
    let declName ← liftCoreM (realizeGlobalConstNoOverloadWithInfo f)
    -- 1. Source design
    let design ← liftTermElabM (Sparkle.Compiler.Elab.synthesizeHierarchical declName)
    if design.modules.length != 1 then
      throwErrorAt f "#verify_emit: hierarchical designs unsupported (v1); got {design.modules.length} modules"
    let some m := design.modules.head? | throwErrorAt f "#verify_emit: empty design"
    -- 2. Emit → 3. reparse
    let sv := Sparkle.Backend.Verilog.toVerilogDesign design
    let design' ← match Tools.SVParser.Lower.parseAndLowerHierarchical sv with
      | .ok d => pure d
      | .error e => throwErrorAt f "#verify_emit: reparse of emitted Verilog failed: {e}"
    let some m' := design'.modules.find? (·.name == Sparkle.Backend.Verilog.sanitizeName m.name)
      | throwErrorAt f "#verify_emit: module `{m.name}` not found after reparse"
    -- 4. structural checks: ports, registers, inits
    let portSig := fun (mm : Sparkle.IR.AST.Module) =>
      ((mm.inputs.filter (fun p => !isClockName p.name)).map (fun p => (p.name, p.ty.bitWidth)),
       mm.outputs.map (fun p => (p.name, p.ty.bitWidth)))
    unless portSig m == portSig m' do
      throwErrorAt f "#verify_emit: port signature changed across the roundtrip{indentD m!"src: {repr (portSig m)}"}{indentD m!"rt:  {repr (portSig m')}"}"
    let sigL := (regSigs m).toArray.qsort (fun a b => a.1 < b.1)
    let sigR := (regSigs m').toArray.qsort (fun a b => a.1 < b.1)
    unless sigL == sigR do
      throwErrorAt f "#verify_emit: register set / init / reset changed across the roundtrip{indentD m!"src: {repr sigL}"}{indentD m!"rt:  {repr sigR}"}"
    -- 5. cones on both sides
    let (regL, outL) ← match conesOf m with
      | .ok c => pure c | .error e => throwErrorAt f "#verify_emit (source): {e}"
    let (regR, outR) ← match conesOf m' with
      | .ok c => pure c | .error e => throwErrorAt f "#verify_emit (reparsed): {e}"
    let lookup := fun (l : List (String × Sparkle.IR.AST.Expr)) (n : String) => l.find? (·.1 == n) |>.map (·.2)
    let mut obligations : List Obligation := []
    for (n, e) in regL do
      match lookup regR n with
      | some e' => obligations := obligations ++ [⟨s!"reg {n}", e, e'⟩]
      | none => throwErrorAt f "#verify_emit: register `{n}` missing after reparse"
    for (n, e) in outL do
      match lookup outR n with
      | some e' => obligations := obligations ++ [⟨s!"out {n}", e, e'⟩]
      | none => throwErrorAt f "#verify_emit: output `{n}` missing after reparse"
    -- 6. shared binders: inputs (minus clock/reset-as-port kept: reset IS
    --    a compared register component, but it also appears in cones only
    --    via ports — keep every non-clock input) ++ registers
    let wt := widthTable m
    let binderNames : List (String × Nat) :=
      ((m.inputs.filter (fun p => !isClockName p.name)).map (fun p => (p.name, p.ty.bitWidth)))
      ++ (regSigs m).map (fun (n, w, _, _) => (n, w))
    let binders ← binderNames.toArray.mapM fun (n, w) => do
      `(bracketedBinder| ($(varIdent n) : BitVec $(quote w)))
    -- Reset hypotheses: the reparsed register DATA cones legitimately
    -- carry a `rst ? init : …` arm (the parser folds the reset branch of
    -- the emitted always_ff into the mux chain), while the source design
    -- keeps reset in the register construct.  Under rst = 1 the register
    -- semantics override the data path on BOTH sides, so cone equality
    -- is only meaningful — and only holds — under rst = 0.
    let rstNames := ((regSigs m).map (fun (_, _, _, r) => r)).eraseDups
    let mut hypBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
    let mut hIdx : Nat := 0
    for r in rstNames do
      unless m.inputs.any (·.name == r) do
        throwErrorAt f "#verify_emit: register reset `{r}` is not an input port"
      let hName := mkIdent (Name.mkSimple s!"hrst_{hIdx}")
      hypBinders := hypBinders.push
        (← `(bracketedBinder| ($hName : $(varIdent r) = (0 : BitVec 1))))
      hIdx := hIdx + 1
    -- 7. one theorem per obligation
    let mut proven : Nat := 0
    for ob in obligations do
      let lhs ← denote wt ob.lhs
      let rhs ← denote (widthTable m') ob.rhs
      let thmName := Name.mkSimple
        s!"{declName.toString.replace "." "_"}_emit_{Sparkle.Backend.Verilog.sanitizeName (ob.label.replace " " "_")}"
      let thmIdent := mkIdent thmName
      let cmd ←
        `(command| theorem $thmIdent $binders* $hypBinders* : $lhs = $rhs := by
              bv_decide)
      elabCommand cmd
      proven := proven + 1
    logInfoAt stx m!"✅ #verify_emit `{declName}`: emitted SystemVerilog proven equivalent — {proven} cone obligations (registers + outputs), ports/registers/inits structurally matched"
  | _ => throwUnsupportedSyntax

end Tools.SVParser.VerifyEmit
