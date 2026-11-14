import Tools.VedU1Deep
import Sparkle.Core.CircuitMonad
import Sparkle.Core.CircuitDo

/-!
# `#ved_u1_deep` finds the facts `#verify_elab_deep` produced in the current scope

Issue sparkle-ved-deep-name.  `#verify_elab_deep d` declares `{last of d}_deep*`
in the CURRENT namespace; the deep route used to look in the declaration's
namespace.  It now looks in the current namespace first, then the declaration's
own; both present and different is refused.  A wrong choice is not a soundness
matter: the kernel check and the exact type comparison are unchanged.

Fixed here (`#guard_msgs`):
1. Positives: a declaration in `namespace A.B` with the facts made and consumed
   (a) after `end A.B` with `open A.B`, (b) at the root through the full name,
   (c) inside the namespace.  Each one: the exact type and std3.
   (d) a private declaration, facts made inside, consumed outside.
2. Refusals: facts in both namespaces; another declaration's facts with the same
   last component; no `#verify_elab_deep`.
-/

namespace Tests.Ved.DeepNameCheck

open Lean Elab Command Term Meta
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Deep

namespace A.B
def cntOut : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    a <~ a + 1#8
    return (a : Signal defaultDomain (BitVec 8))
def cntIn : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    a <~ a + 2#8
    return (a : Signal defaultDomain (BitVec 8))
def cntRoot : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    a <~ a + 3#8
    return (a : Signal defaultDomain (BitVec 8))
def amb : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    a <~ a + 4#8
    return (a : Signal defaultDomain (BitVec 8))
def same : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    a <~ a + 5#8
    return (a : Signal defaultDomain (BitVec 8))
def noFacts : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    a <~ a + 6#8
    return (a : Signal defaultDomain (BitVec 8))
private def priv : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    a <~ a + 7#8
    return (a : Signal defaultDomain (BitVec 8))

#guard_msgs (drop info) in
#verify_elab_deep cntIn
#guard_msgs (drop info) in
set_option Elab.async false in
#ved_u1_deep cntIn
#guard_msgs (drop info) in
#verify_elab_deep amb
#verify_elab_deep priv
end A.B

-- another declaration with the same last component, in another namespace
namespace D
def same : Signal defaultDomain (BitVec 8) :=
  circuit do
    let a ← Signal.reg 0#8
    a <~ a + 9#8
    return (a : Signal defaultDomain (BitVec 8))
end D

open A.B

/-! ## 1. Positives -/

-- (a) after `end A.B` with `open A.B`
#guard_msgs (drop info) in
#verify_elab_deep cntOut
#guard_msgs (drop info) in
set_option Elab.async false in
#ved_u1_deep cntOut

-- (b) at the root, through the full name
#guard_msgs (drop info) in
#verify_elab_deep A.B.cntRoot
#guard_msgs (drop info) in
set_option Elab.async false in
#ved_u1_deep A.B.cntRoot

/-- info: complete type and std3 axioms: cntOut, cntRoot, cntIn -/
#guard_msgs in
run_cmd liftTermElabM do
  for n in [``A.B.cntOut, ``A.B.cntRoot, ``A.B.cntIn] do
    let ti ← getConstInfo (n ++ `ved_u1)
    let expected := mkAppN (mkConst ``U1Stmt)
      #[mkConst (n ++ `ved_contract), mkConst (n ++ `ved_mod), mkConst n]
    unless ti.type == expected do throwError "type of {n}.ved_u1 is not the expected statement"
    let axs ← collectAxioms (n ++ `ved_u1)
    let std3 : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless axs.all (std3.contains ·) do throwError "{n}.ved_u1 axioms {axs}"
  logInfo "complete type and std3 axioms: cntOut, cntRoot, cntIn"

/-! ## 2. Refusals -/

def expectRefusedWith (decl : Name) (stage needle : String) : CommandElabM Unit :=
    liftTermElabM do
  let accepted ← try discard <| vedU1DeepEntry decl; pure true catch e =>
    let s ← e.toMessageData.toString
    unless s.startsWith "VED U1 REFUSED" && (s.splitOn s!"[{stage}]").length > 1
        && (s.splitOn needle).length > 1 do throw e
    pure false
  if accepted then throwError "control ACCEPTED (expected a refusal at [{stage}])"
  let env ← getEnv
  for n in [`ved_mod, `ved_contract, `ved_outs, `ved_body, `ved_u1].map (decl ++ ·) ++ auxNames decl do
    if env.contains n then throwError "left behind: {n}"
  logInfo m!"refused [{stage}], clean"

-- facts of `amb` in A.B (above) and a second, different `amb_deep` here.
-- (DeepElab's helper `amb_deep_body` clashes across namespaces, so the second
-- set is a copy of the constant the routine looks at first.)
def amb_deep := @A.B.amb_deep

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefusedWith ``A.B.amb "proof" "ambiguous"

-- `D.same`'s facts at the root; `A.B.same` has none of its own
#guard_msgs (drop info) in
#verify_elab_deep D.same

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefusedWith ``A.B.same "proof" "errors were logged"

/-- info: refused [proof], clean -/
#guard_msgs in
run_cmd expectRefusedWith ``A.B.noFacts "proof" "missing"

-- a private declaration: its facts are `priv_deep*` (last component), found from here
#guard_msgs (drop info) in
set_option Elab.async false in
#ved_u1_deep priv

/-- info: private: complete type and std3 axioms -/
#guard_msgs in
run_cmd liftTermElabM do
  let n ← realizeGlobalConstNoOverload (mkIdent `priv)
  let ti ← getConstInfo (n ++ `ved_u1)
  let expected := mkAppN (mkConst ``U1Stmt)
    #[mkConst (n ++ `ved_contract), mkConst (n ++ `ved_mod), mkConst n]
  unless ti.type == expected do throwError "type of {n}.ved_u1 is not the expected statement"
  let axs ← collectAxioms (n ++ `ved_u1)
  unless axs.all ([``propext, ``Classical.choice, ``Quot.sound].contains ·) do throwError "axioms {axs}"
  logInfo "private: complete type and std3 axioms"

end Tests.Ved.DeepNameCheck
