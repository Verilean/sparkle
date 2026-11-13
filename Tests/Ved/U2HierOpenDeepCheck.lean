import Tools.VedU2HierRegEntry
import Tools.DeepFinArms
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# Checks for H2d: the open parent's `#verify_elab_deep` on real-IP-shaped circuits

Issue sparkle-ved-hier2-h2d.  Real IP rows (R211 `synth_arpRequesterByte`, R228, R210) stopped inside the
`#verify_elab_deep` of the OPEN parent.  What was found and fixed (see `docs/VED-HIER-H2D.md`):

* `Missing cases: (Fin.mk (succ^18 _) _)`: the generated `match` on a `Fin n` literal index (slot names, 13
  registers + 5 inputs) is closed by the match compiler's contradiction search, whose fixed fuel (16) the
  tail of the `Fin` exceeds.  `finTailArm` adds the explicit arm `⟨k + n, h⟩ => absurd h _`; the literal arms
  are unchanged and `nm ⟨i, _⟩` still reduces by `rfl`.
* a child call whose argument is a register of a NESTED circuit (a parser called inside the parent's
  `circuit do`): the nested loop's state is exported (`<port>_deep_state_n<j>`) and the hierarchical checker
  ties the argument to the register by it.  The top loop's registers need not be one contiguous block.
* a port that does not read the circuit's own loop cannot export its state; its failure no longer stops the
  later ports (`sparkle.deepContinue`).

* H2d2 (R211): a parent whose registers form a WIDE pack (57 bits), guarded by `~~~`, with a Bool flag over a
  conjunction and a child call on a derived argument.  Four things stood between such a parent and acceptance:
  `omega` does not read `^^^`/`&&&`/`(0#1).toNat` and the pack arithmetic made it explode (`ved_hier_close`,
  `Tools/VedU2HierClose.lean`); `simp` dropped `x <<< 0` as a `rfl` step, whose kernel check (`Nat.mod` on a literal
  modulus) needed minutes and gigabytes for a 56-bit pack (`shl_zero`); the trace closers used `bv_decide` (native axiom,
  refused by the strict audit): `sparkle.deepNoNative` and `ved_bv_close` (`Tools/DeepNoNative.lean`); an operator on an
  operand without a range fact stayed `evalOp` (`rawOpL`).
* POSITIVES: the `Fin` tail arm (25 arms); `topN` (parent registers, a nested stateful call, a child call
  reading the nested register and the parent's) through `#ved_u2_hier`'s entry: type `U2HRStmt c m d decl`
  compared with `==`, axioms within `propext`, `Classical.choice`, `Quot.sound`, and the nested state theorem
  exists.
* REFUSALS (the real module with ONE piece altered against the declaration's own deep facts; refused at
  `[proof]`, nothing left behind): an altered arm value, the next-state nets of two registers exchanged, the
  nested register's init changed, the nested register exchanged with a parent register, the child's port read
  from another register.
-/

namespace Tests.Ved.U2HierOpenDeepCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier Tools.VedU1HierEntry Tools.VedU2Hier
  Tools.VedU2HierEntry Tools.VedU2HierRegEntry

/-! ## The `Fin` tail arm -/

/-- A name table over 25 slots: without the tail arm the match compiler reports a missing case. -/
abbrev slots25 : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]

-- WITHOUT the tail arm the 25-arm match is refused ("Missing cases"); the refusal is asserted and its message
-- dropped.
run_cmd do
  let arms ← (List.range 25).toArray.mapM fun i =>
    `(Lean.Parser.Term.matchAltExpr| | ⟨$(quote i), _⟩ => $(quote s!"s{i}"))
  let saved := (← get).messages
  elabCommand (← `(def nmNoTail : Fin slots25.length → String := fun i => match i with $arms:matchAlt*))
  let msgs := (← get).messages.toList.drop saved.toList.length
  let ok ← msgs.anyM fun m => do pure (m.severity == .error && (← m.data.toString).startsWith "Missing cases")
  modify fun s => { s with messages := saved }
  unless ok do throwError "the 25-arm match without the tail arm was not refused with `Missing cases`"

run_cmd do
  let arms ← (List.range 25).toArray.mapM fun i =>
    `(Lean.Parser.Term.matchAltExpr| | ⟨$(quote i), _⟩ => $(quote s!"s{i}"))
  let arms ← Tools.DeepElab.finTailArm arms 25
  elabCommand (← `(def $(mkIdent `nm25) : Fin slots25.length → String := fun i => match i with $arms:matchAlt*))

example : nm25 ⟨3, by decide⟩ = "s3" := rfl
example : nm25 ⟨24, by decide⟩ = "s24" := rfl
-- 15 arms or fewer keep their exact generated shape.
run_cmd do
  let arms ← (List.range 15).toArray.mapM fun i =>
    `(Lean.Parser.Term.matchAltExpr| | ⟨$(quote i), _⟩ => $(quote s!"s{i}"))
  unless (← Tools.DeepElab.finTailArm arms 15 : Array _).size == 15 do throwError "arms added below the ceiling"
  unless (← Tools.DeepElab.finTailArm arms 16 : Array _).size == 16 do throwError "no tail arm above the ceiling"

/-! ## Declarations: parent registers, a nested stateful call, a child call over both -/

@[hardware_module]
def sum2 (x y : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := x + y

/-- A plain stateful function (inlined into its caller, not an instance). -/
def inner (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let r ← Signal.reg 0#8
    r <~ r + x
    return r

def topN (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    let p := inner x
    let d ← Signal.reg 0#8
    let cS := (c : Signal defaultDomain (BitVec 8))
    let dS := (d : Signal defaultDomain (BitVec 8))
    c <~ cS + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))
    d <~ dS + x
    return sum2 p (cS + dS)

/-- The declaration the CONTROLS alter (never accepted itself). -/
def topRef (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let c ← Signal.reg 0#8
    let p := inner x
    let d ← Signal.reg 0#8
    let cS := (c : Signal defaultDomain (BitVec 8))
    let dS := (d : Signal defaultDomain (BitVec 8))
    c <~ cS + (Signal.pure 1#8 : Signal defaultDomain (BitVec 8))
    d <~ dS + x
    return sum2 p (cS + dS)

/-! ## A wide register pack, `~~~`, a Bool flag over a conjunction, a derived child argument (H2d2) -/

@[hardware_module]
def sumw {dom : DomainConfig} (x y : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := x + y

structure OW (dom : DomainConfig) where
  out : Signal dom (BitVec 8)
  seen : Signal dom Bool

instance {dom : DomainConfig} : Sparkle.Core.HasDomain (OW dom) dom := ⟨⟩

/-- Parent registers of 24 + 8 + 24 + 1 bits (a 57-bit pack): a counter guarded by `~~~isIdle`, a latch, an accumulator
guarded by a comparison, a flag over a conjunction; the child reads the derived net `mux trig x b`. -/
def wideG {dom : DomainConfig} (trig : Signal dom Bool) (x : Signal dom (BitVec 8)) : OW dom :=
  circuit do
    let a ← Signal.reg (0#24)
    let b ← Signal.reg (0#8)
    let c ← Signal.reg (0#24)
    let d ← Signal.reg false
    let aS := (a : Signal dom (BitVec 24))
    let bS := (b : Signal dom (BitVec 8))
    let cS := (c : Signal dom (BitVec 24))
    let dS := (d : Signal dom Bool)
    let isIdle := aS === (Signal.pure 0#24 : Signal dom (BitVec 24))
    a <~ Signal.mux trig (Signal.pure 1#24) (Signal.mux (~~~isIdle) (aS + (Signal.pure 1#24 : Signal dom (BitVec 24))) aS)
    b <~ Signal.mux trig x bS
    c <~ Signal.mux (bS === (Signal.pure 3#8 : Signal dom (BitVec 8))) (cS + (Signal.pure 3#24 : Signal dom (BitVec 24))) cS
    d <~ Signal.mux trig (Signal.pure false) (Signal.mux (isIdle &&& (bS === (Signal.pure 3#8 : Signal dom (BitVec 8)))) (Signal.pure true) dS)
    let byteOut := sumw (Signal.mux trig x bS) (Signal.pure 1#8 : Signal dom (BitVec 8))
    return ({ out := byteOut, seen := dS } : OW dom)

def wideW (trig : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  (wideG trig x).out

/-- The declaration the CONTROLS alter (never accepted itself). -/
def wideRef (trig : Signal defaultDomain Bool) (x : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  (wideG trig x).out

/-! ## Helpers -/

def std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def std3Only (n : Name) : CoreM Unit := do
  let axs ← collectAxioms n
  unless axs.all (std3.contains ·) do throwError "{n}: axioms outside the standard three: {axs}"

def expectedOf (decl : Name) (nDom : Nat) : Lean.Expr :=
  let nm := HNames.ofBase decl
  let stmt := (List.range nDom).foldl (fun e _ => mkApp e (Lean.mkConst ``defaultDomain)) (Lean.mkConst decl)
  mkAppN (Lean.mkConst ``U2HRStmt)
    #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, Lean.mkConst nm.design, stmt]

def localConsts : CommandElabM NameSet := do
  return (← getEnv).constants.map₂.toList.foldl (fun s (n, _) => s.insert n) {}

def synthOf (decl : Name) : CommandElabM (Sparkle.IR.AST.Module × Design) := liftTermElabM do
  Sparkle.Compiler.Elab.synthesizeCombinational decl

/-! ## Positive -/

/-- The entry run, the exact type (`==`), the strict audit, the standard axioms, the nested state theorem. -/
def checkOk (decl : Name) : CommandElabM Unit := do
  let (m, d, thm, nDom, _) ← vedU2HierEntryR decl
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    discard <| Tools.VedStrictAudit.strictAudit thm
    std3Only thm
    let openSuf := "ved_open_" ++ "_".intercalate (decl.components.map toString)
    for suf in ["_deep_state", "_deep_state_n0"] do
      let n := decl ++ Name.mkSimple (openSuf ++ suf)
      let some (.thmInfo _) := (← getEnv).find? n | throwError "{n} is not a theorem"
      std3Only n
    logInfo m!"u2 hier open-deep OK {thm}: {(regsOf m.body).length} parent registers, children {d.modules.map (·.name)}"

/-- info: u2 hier open-deep OK Tests.Ved.U2HierOpenDeepCheck.topN.ved_u1: 3 parent registers, children [Tests.Ved.U2HierOpenDeepCheck.sum2] -/
#guard_msgs in
run_cmd checkOk ``topN

/-- The entry run for a parent without a nested circuit whose output is the projection `port` of a structure: exact type
(`==`), strict audit, standard axioms, the loop state exported by that port. -/
def checkOkFlat (decl : Name) (port : String) : CommandElabM Unit := do
  let (m, d, thm, nDom, _) ← vedU2HierEntryR decl
  liftTermElabM do
    let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
    unless ti.type == expectedOf decl nDom do throwError "{thm}: type is not U2HRStmt c m d decl"
    discard <| Tools.VedStrictAudit.strictAudit thm
    std3Only thm
    let openSuf := "ved_open_" ++ "_".intercalate (decl.components.map toString)
    let n := decl ++ Name.mkSimple (openSuf ++ "_" ++ port ++ "_deep_state")
    let some (.thmInfo _) := (← getEnv).find? n | throwError "{n} is not a theorem"
    std3Only n
    logInfo m!"u2 hier open-deep OK {thm}: {(regsOf m.body).length} parent registers, children {d.modules.map (·.name)}"

/-- info: u2 hier open-deep OK Tests.Ved.U2HierOpenDeepCheck.wideW.ved_u1: 4 parent registers, children [Tests.Ved.U2HierOpenDeepCheck.sumw] -/
#guard_msgs in
run_cmd checkOkFlat ``wideW "out"

/-! ## Refusals: the real module with ONE piece altered, the declaration's own deep facts -/

def setInit (o : String) (v : Int) (b : List Stmt) : List Stmt :=
  b.map fun s => match s with
    | .register o' c r e _ => if o' == o then .register o' c r e v else s
    | s => s

/-- Exchange the input nets of two registers. -/
def swapInputs (o1 o2 : String) (b : List Stmt) : List Stmt :=
  let inOf (o : String) : Option Sparkle.IR.AST.Expr := b.findSome? fun s => match s with
    | .register o' _ _ e _ => if o' == o then some e else none
    | _ => none
  match inOf o1, inOf o2 with
  | some e1, some e2 => b.map fun s => match s with
    | .register o' c r e i => if o' == o1 then .register o' c r e2 i
        else if o' == o2 then .register o' c r e1 i else .register o' c r e i
    | s => s
  | _, _ => b

def setAssign (n : String) (e : Sparkle.IR.AST.Expr) (b : List Stmt) : List Stmt :=
  b.map fun s => match s with
    | .assign l _ => if l == n then .assign l e else s
    | s => s

/-- Replace the connection of port `p` by `e` in the instance NUMBER `k` (0-based). -/
def setConnAt (k : Nat) (p : String) (e : Sparkle.IR.AST.Expr) (b : List Stmt) : List Stmt :=
  let rec go : List Stmt → Nat → List Stmt
    | [], _ => []
    | s :: r, n =>
      match s with
      | .inst mn i cs => (if n == k then .inst mn i (cs.map fun q => if q.1 == p then (p, e) else q) else s) :: go r (n + 1)
      | _ => s :: go r n
  go b 0

/-- The hierarchical checker on the altered module refuses at the named stage, leaving nothing. -/
def hierCtl (decl : Name) (stage : String) (f : List Stmt → List Stmt) : CommandElabM Unit := do
  let (m, d) ← synthOf decl
  let before ← localConsts
  let (stmt, nDom) ← liftTermElabM (specialiseDomain decl)
  let m' := { m with body := f m.body }
  if decide (m' = m) then throwError "the mutation is the identity"
  let r ← try
      discard <| checkU2HR decl stmt nDom m' d none
      pure none
    catch e => pure (some (← liftTermElabM (e.toMessageData.toString)))
  match r with
  | none => throwError "{decl}: the checker ACCEPTED the altered module"
  | some msg =>
    unless msg.startsWith s!"VED U1 REFUSED {decl} [{stage}]" do throwError "expected a [{stage}] refusal, got: {msg.take 400}"
    logInfo m!"refused [{stage}], clean"
  let added := (← localConsts).toList.filter (!before.contains ·)
  unless added.isEmpty do throwError "constants left after the refusal: {added}"

/- `topRef` (module): parent registers `_tmp_a_4` (c, input `_tmp_reg_input_3 = _tmp_arg1_1 + _tmp_arg2_2`) and
`_tmp_a_8` (d); the nested register `_tmp_a_15`; the child's `_gen_x` is `_tmp_arg1_13` (the nested register),
`_gen_y` is `_tmp_arg1_19 = c + d`. -/

-- An ARM VALUE altered: the counter increments by 2.
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``topRef "proof" (setAssign "_tmp_arg2_2" (.const 2 8))

-- The next-state nets of the two parent registers exchanged.
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``topRef "proof" (swapInputs "_tmp_a_4" "_tmp_a_8")

-- The nested register's init changed.
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``topRef "proof" (setInit "_tmp_a_15" 1)

-- The nested register exchanged with a parent register (their register inputs swapped).
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``topRef "proof" (swapInputs "_tmp_a_4" "_tmp_a_15")

-- The child's port reads the parent register `c` instead of the nested register.
/-- info: refused [kernel], clean -/
#guard_msgs in
run_cmd hierCtl ``topRef "kernel" (setConnAt 0 "_gen_x" (.ref "_tmp_arg1_1"))

/- `wideRef` (module): parent registers `_tmp_a_9` (a, 24 bits; next net `_tmp_reg_input_8`, load value `_tmp_mux_then_1`, guard
`_tmp_mux_cond_5 = ~~~(_tmp_arg1_4)`), `_tmp_a_13` (b, 8), `_tmp_a_21` (c, 24), `_tmp_a_29` (d, 1); the child's `_gen_x` is
`_tmp_reg_input_12` (the derived net `mux trig x b`). -/

-- The `~~~` guard removed: the counter increments exactly when it is idle.
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``wideRef "proof" (setAssign "_tmp_mux_cond_5" (.ref "_tmp_arg1_4"))

-- The load value of the counter changed.
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``wideRef "proof" (setAssign "_tmp_mux_then_1" (.const 2 24))

-- The latch's init changed.
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``wideRef "proof" (setInit "_tmp_a_13" 1)

-- The next-state nets of the counter and the accumulator exchanged (same width).
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd hierCtl ``wideRef "proof" (swapInputs "_tmp_a_9" "_tmp_a_21")

-- The child's port reads the latch register itself instead of the derived net.
/-- info: refused [kernel], clean -/
#guard_msgs in
run_cmd hierCtl ``wideRef "kernel" (setConnAt 0 "_gen_x" (.ref "_tmp_a_13"))

end Tests.Ved.U2HierOpenDeepCheck
