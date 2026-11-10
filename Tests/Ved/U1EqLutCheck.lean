import Tools.VedU1Entry
import Sparkle.Core.Lut

/-!
# Checks for `==`, constants and constant-table mux chains in the U1 script

The generated script handles `Operator.eq` (a 1-bit result), `.const` and the
mux chains of `kLut!` by evaluating the body symbolically and closing what is
left over the finite input domain (every data input generalised, the goal
reverted to `∀ x, x < 2^w → …` and decided by the kernel; no `native_decide`).

Positives: the theorem has exactly the type `U1Stmt c m (@decl defaultDomain)`
and the standard three axioms.  Controls: `checkU1E` is given another module
(the real module of the positive declaration, mutated, or the module of another
declaration) and must refuse at `[proof]` leaving no `ved_*` constant.
-/

namespace Tests.Ved.U1EqLutCheck

open Lean Elab Command Term Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry

/-! ## Declarations -/

/-- `==` of two signals (1-bit result) -/
def eq4 (a b : Signal Domain (BitVec 4)) : Signal Domain Bool := (· == ·) <$> a <*> b

/-- `==` against a constant -/
def eqK {dom : DomainConfig} (a : Signal dom (BitVec 6)) : Signal dom Bool :=
  (· == ·) <$> a <*> Signal.pure 37#6

/-- same type, another constant -/
def eqK2 {dom : DomainConfig} (a : Signal dom (BitVec 6)) : Signal dom Bool :=
  (· == ·) <$> a <*> Signal.pure 38#6

/-- a constant output -/
def constOut (a : Signal Domain (BitVec 4)) : Signal Domain (BitVec 8) := Signal.pure 90#8

/-- a local copy of the shape of `rconHW` / the K tables: a 4-entry `kLut!` -/
def lut4 {dom : DomainConfig} (i : Signal dom (BitVec 2)) : Signal dom (BitVec 8) :=
  kLut! i [
    Signal.pure 0x11#8, Signal.pure 0x22#8, Signal.pure 0x44#8, Signal.pure 0x88#8
  ]

/-- same shape and type, the table's entries 1 and 2 swapped -/
def lut4s {dom : DomainConfig} (i : Signal dom (BitVec 2)) : Signal dom (BitVec 8) :=
  kLut! i [
    Signal.pure 0x11#8, Signal.pure 0x44#8, Signal.pure 0x22#8, Signal.pure 0x88#8
  ]

/-- same shape and type, one table constant changed -/
def lut4c {dom : DomainConfig} (i : Signal dom (BitVec 2)) : Signal dom (BitVec 8) :=
  kLut! i [
    Signal.pure 0x11#8, Signal.pure 0x22#8, Signal.pure 0x45#8, Signal.pure 0x88#8
  ]

/-! ## Positives: the exact theorem type and the axioms -/

def specOf (decl : Name) : Lean.Expr := mkApp (Lean.mkConst decl) (Lean.mkConst ``defaultDomain)

def checkPos (decl : Name) (nDomExpected : Nat) : CommandElabM Unit := liftTermElabM do
  let (_, _, thm, nDom) ← vedU1EntryS decl
  unless nDom == nDomExpected do throwError "{decl}: instantiated binders {nDom}"
  let nm := Names.ofBase decl
  let stmt := if nDom == 0 then Lean.mkConst decl else specOf decl
  let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
  let some (.thmInfo ti) := (← getEnv).find? thm | throwError "{thm} is not a theorem"
  unless ti.type == expected do throwError "{thm}: type is not U1Stmt c m {stmt}"
  let r ← Tools.VedStrictAudit.strictAudit thm
  let ax ← collectAxioms thm
  let ok := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (ok.contains ·) && r.axioms.all (ok.contains ·) do
    throwError "{thm}: axioms {ax}"
  logInfo m!"OK {thm}"

/-- info: OK Tests.Ved.U1EqLutCheck.eq4.ved_u1 -/
#guard_msgs in
run_cmd checkPos ``eq4 1
/-- info: OK Tests.Ved.U1EqLutCheck.eqK.ved_u1 -/
#guard_msgs in
run_cmd checkPos ``eqK 1
/-- info: OK Tests.Ved.U1EqLutCheck.eqK2.ved_u1 -/
#guard_msgs in
run_cmd checkPos ``eqK2 1
/-- info: OK Tests.Ved.U1EqLutCheck.constOut.ved_u1 -/
#guard_msgs in
run_cmd checkPos ``constOut 1
/-- info: OK Tests.Ved.U1EqLutCheck.lut4.ved_u1 -/
#guard_msgs in
run_cmd checkPos ``lut4 1
/-- info: OK Tests.Ved.U1EqLutCheck.lut4s.ved_u1 -/
#guard_msgs in
run_cmd checkPos ``lut4s 1
/-- info: OK Tests.Ved.U1EqLutCheck.lut4c.ved_u1 -/
#guard_msgs in
run_cmd checkPos ``lut4c 1

/-! ## Controls: refused at `[proof]`, no `ved_*` constant left -/

def modOf (base : Name) : TermElabM Sparkle.IR.AST.Module := do
  let some v := (← getConstInfo (base ++ `ved_mod)).value? | throwError "no value"
  evalModule v

def checkerNames (base : Name) : List Name :=
  [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (base ++ ·)

def expectRefused (stage : String) (base : Name) (act : TermElabM Unit) :
    CommandElabM Unit := liftTermElabM do
  let accepted ← try act; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  for n in checkerNames base do
    if (← getEnv).contains n then throwError "left behind: {n}"
  logInfo m!"refused [{stage}], clean"

open Sparkle.IR.AST in
/-- replace the `n`-th statement `f` maps to `some` (the module is unchanged if there is none) -/
def mutNth (n : Nat) (f : Stmt → Option Stmt) (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  let (_, body) := m.body.foldl (init := (n, ([] : List Stmt))) fun (k, acc) s =>
    match f s with
    | some s' => if k == 0 then (k.pred, acc ++ [s']) else (k.pred, acc ++ [s])
    | none => (k, acc ++ [s])
  { m with body := body }

open Sparkle.IR.AST in
/-- the `n`-th constant of width `w` gets value `+1` -/
def bumpConst (w n : Nat) : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module :=
  mutNth n fun | .assign o (.const v w') => if w' == w then some (.assign o (.const (v + 1) w)) else none
               | _ => none

open Sparkle.IR.AST in
/-- the `n`-th constant of width `w`, the values of two constants exchanged -/
def swapConsts (w : Nat) (a b : Nat) (m : Sparkle.IR.AST.Module) : Sparkle.IR.AST.Module :=
  let vs : List Int := m.body.filterMap fun | .assign _ (.const v w') => if w' == w then some v else none | _ => none
  let va := vs.getD a 0
  let vb := vs.getD b 0
  mutNth a (fun | .assign o (.const _ w') => if w' == w then some (.assign o (.const vb w)) else none
                | _ => none) <|
  mutNth b (fun | .assign o (.const _ w') => if w' == w then some (.assign o (.const va w)) else none
                | _ => none) m

open Sparkle.IR.AST in
/-- the first `==` becomes `!=` (a comparison is 1 bit wide: its complement) -/
def eqToNe (n : Nat) : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module :=
  mutNth n fun | .assign o (.op .eq args) => some (.assign o (.op .not [.op .eq args]))
               | _ => none

/-- `(decl, base, module)`: the statement of `decl` against `module` -/
def ctl (base : Name) (decl : Name) (m : Sparkle.IR.AST.Module) : CommandElabM Unit :=
  expectRefused "proof" base do
    discard <| checkU1E decl base (specOf decl) m .generated

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlLutTableConst ``lut4 (bumpConst 8 2 (← liftTermElabM (modOf ``lut4)))

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlLutFirstEntry ``lut4 (bumpConst 8 0 (← liftTermElabM (modOf ``lut4)))

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlLutSwapped ``lut4 (swapConsts 8 1 2 (← liftTermElabM (modOf ``lut4)))

-- the module of the declaration with the table's entries swapped / one constant changed
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlLutDeclSwapped ``lut4 (← liftTermElabM (modOf ``lut4s))

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlLutDeclConst ``lut4 (← liftTermElabM (modOf ``lut4c))

-- `==` replaced by `!=`, in a table's compare and in a plain comparison
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlLutNe ``lut4 (eqToNe 1 (← liftTermElabM (modOf ``lut4)))

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlEqNe ``eq4 (eqToNe 0 (← liftTermElabM (modOf ``eq4)))

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlEqKNe ``eqK (eqToNe 0 (← liftTermElabM (modOf ``eqK)))

-- a compared constant changed (a 2-bit constant of the table; the 6-bit constant)
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlLutCompared ``lut4 (bumpConst 2 1 (← liftTermElabM (modOf ``lut4)))

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlEqKConst ``eqK (bumpConst 6 0 (← liftTermElabM (modOf ``eqK)))

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlEqKOther ``eqK (← liftTermElabM (modOf ``eqK2))

-- a constant output changed
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlConstOut ``constOut (bumpConst 8 0 (← liftTermElabM (modOf ``constOut)))

-- the comparison's module against another statement
/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd do ctl `ctlEqIntoLut ``eqK (← liftTermElabM (modOf ``eq4))

end Tests.Ved.U1EqLutCheck
