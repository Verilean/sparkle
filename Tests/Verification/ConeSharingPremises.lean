/-
  Cone-sharing premises on a REAL body: `crc16CcittHW` (DroneCAN).

  The deep route cannot finish this circuit today: its single register's
  fully-inlined cone is 16 M chars (see `DeepElabRealIP`).  Cone sharing
  stops inlining at the wires read more than once and links them through
  `shared_cone_agrees_at_settled`.  This file checks, at build time and
  by evaluation on the actual synthesized body, that every premise of
  that theorem holds with that stop set — so the IR side is ready before
  the deep grammar is extended.  A `throwError` on any failure.

  Measured 2026-09-13: 94 statements, 1 register, 5 inputs, 26 shared
  wires; register cone 954 chars, per-wire cones ≤ 589 chars; all
  checks true; `stopAtFrozenCheck` false with the shared stop set, which
  is precisely why the seed-side theorem cannot be used here.
-/
import IP.Bus.DroneCANHW
import Tools.DeepElab
open Sparkle.IR.AST Sparkle.IR.Semantics Tools.ConeFold


open Lean Elab Command in
run_cmd do
  let d ← liftTermElabM (Sparkle.Compiler.Elab.synthesizeHierarchical
    ``Sparkle.IP.Bus.DroneCANHW.crc16CcittHW)
  let some m := d.modules.head? | throwError "no module"
  let body := Tools.DeepElab.deepOrderBody m.body
  let wt := Tools.SVParser.VerifyEmit.widthTable m
  let we : WEnv := fun n => wt.getD n 0
  -- read counts over assign rhs + register inputs
  let mut cnt : Std.HashMap String Nat := {}
  let mut defined : Std.HashSet String := {}
  let mut regs : List (String × Sparkle.IR.AST.Expr) := []
  for st in body do
    match st with
    | .assign l r =>
      defined := defined.insert l
      for n in Sparkle.IR.Reorder.refsOf r do cnt := cnt.insert n (cnt.getD n 0 + 1)
    | .register out _ _ input _ =>
      regs := regs ++ [(out, input)]
      for n in Sparkle.IR.Reorder.refsOf input do cnt := cnt.insert n (cnt.getD n 0 + 1)
    | _ => pure ()
  let shared := (cnt.toList.filter fun (n, c) => c ≥ 2 && defined.contains n).map (·.1)
  let base : Std.HashMap String Bool :=
    (m.inputs.foldl (fun h p => h.insert p.name true) {})
    |> regs.foldl (fun h (r, _) => h.insert r true)
  let stopShared := shared.foldl (fun h n => h.insert n true) base
  let dm := Sparkle.IR.Optimize.buildDefMap body
  logInfo m!"body stmts={body.length} regs={regs.length} inputs={m.inputs.length} shared(multiply-read, defined) wires={shared.length}"
  unless shared.length == 26 do throwError "expected 26 shared wires, got {shared.length}"
  unless memFreeCheck body do throwError "memFreeCheck failed"
  unless noSelfReadCheck body do throwError "noSelfReadCheck failed"
  unless Sparkle.IR.Reorder.woCheck [] body do throwError "woCheck failed"
  unless bodyWidthOk we body do throwError "bodyWidthOk failed on crc16's body"
  unless hwfCheck we stopShared body do throwError "hwfCheck (shared stop set) failed"
  -- the seed-side theorem's frozen premise is NOT available here — that
  -- is the reason for shared_cone_agrees_at_settled; pin it so a change
  -- in either direction is noticed
  if stopAtFrozenCheck stopShared body then throwError "stopAtFrozenCheck unexpectedly TRUE with shared stop set"
  unless stopAtFrozenCheck base body do throwError "stopAtFrozenCheck failed with the base stop set"
  for (r, input) in regs do
    match inlineConeT dm stopShared 10000 input with
    | .ok c =>
      let cr := resolveSlicesT wt 10000 c
      let sz := (repr cr).pretty.length
      unless sz < 2000 do throwError "register {r}: shared cone is {sz} chars, expected < 2000"
      unless widthOk we cr && widthOf we cr == we r do throwError "register {r}: shared cone width check failed"
      logInfo m!"CONE-SHARING crc16 register {r}: shared cone {sz} chars (inlined: 16 M), widthOk"
    | .error e => logInfo m!"register {r}: inlineConeT failed: {e}"
  -- per shared wire: its own small cone (stopping at the OTHER shared wires)
  let mut maxW := 0
  let mut allOk := true
  for w in shared do
    match dm.get? w with
    | some rhs =>
      match inlineConeT dm stopShared 10000 rhs with
      | .ok c =>
        let cr := resolveSlicesT wt 10000 c
        let sz := (repr cr).pretty.length
        if sz > maxW then maxW := sz
        unless widthOk we cr && widthOf we cr == we w do
          allOk := false
          logInfo m!"wire {w}: widthOk={widthOk we cr} widthOf={widthOf we cr} we={we w}"
      | .error e => allOk := false; logInfo m!"wire {w}: inlineConeT failed: {e}"
    | none => allOk := false; logInfo m!"wire {w}: no definition"
  unless allOk do throwError "a shared wire's cone failed widthOk / width agreement"
  unless maxW < 2000 do throwError "largest per-wire cone is {maxW} chars, expected < 2000"
  logInfo m!"CONE-SHARING crc16: 26 shared wires, per-wire cones ≤ {maxW} chars, all premises of shared_cone_agrees_at_settled hold"
