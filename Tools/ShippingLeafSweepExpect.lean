import Tools.ShippingLeafSweepCommand

/-! # `#leaf_sweep_expect f "CLASS" ["reason"]`: the MEASURED class of a swept declaration, asserted (round par/b-32)

WRITTEN, NOT BUILT.

`#leaf_sweep f` (BUILT at 35208d70) logs and never fails; `#leaf_sweep_summary`
fails only on an inconsistency of what the file measured. So a declaration
that was GENERATED and later comes back REFUSED or FAILED would not fail the
suite. This command asserts the class that was MEASURED by the integrator's
build (`docs/parallel/B-leaf-sweep.md`, "Integrator's build record"):

    #leaf_sweep_expect f "GENERATED"
    #leaf_sweep_expect f "REFUSED" "has calls"

It reads the row `#leaf_sweep f` left in this file's table and is an ERROR
when

* `f` was not swept in this file;
* the row's class is not the written one;
* for `GENERATED` / `REBUILT`: the row's audit is not `OK`, its listing has a
  NOT ALLOWED line, or `f.machine_design_leaf0` is not in the environment;
* for `REFUSED` with a reason: the generator's refusal line does not contain
  the written text.

It adds nothing to the environment. Each `#leaf_sweep_expect` is its own
command: one failing assertion does not hide the others. -/
namespace Tools.ShippingLeafSweepCommand
open Lean Meta Elab Command

elab "#leaf_sweep_expect " d:ident e:str r:(str)? : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let want : String := e.getString
  let rs ← rows.get
  let mine := (rs.filter fun x => x.decl == toString f).toList.reverse
  let row ← match mine with
    | x :: _ => pure x
    | [] => throwError "LEAFSWEEP EXPECT {f}: not swept in this file (no #leaf_sweep {f} before this line)"
  unless row.tag == want do
    throwError "LEAFSWEEP EXPECT {f}: measured {want} (docs/parallel/B-leaf-sweep.md), now {row.tag} — {row.note}"
  if want == "GENERATED" || want == "REBUILT" then
    unless row.audit == "OK" do
      throwError "LEAFSWEEP EXPECT {f}: {row.tag}, but its audit did not pass: {row.audit}"
    unless row.bad == 0 do
      throwError "LEAFSWEEP EXPECT {f}: {row.tag}, with {row.bad} NOT ALLOWED lines"
    unless (← getEnv).contains (f ++ `machine_design_leaf0) do
      throwError "LEAFSWEEP EXPECT {f}: {row.tag}, but {f ++ `machine_design_leaf0} is not in the environment"
  match r with
  | some s =>
    let sub : String := s.getString
    unless (row.note.splitOn sub).length > 1 do
      throwError "LEAFSWEEP EXPECT {f}: {row.tag}, but its reason does not contain \"{sub}\": {row.note}"
  | none => pure ()
  logInfo m!"LEAFSWEEP EXPECT {f}: {row.tag}, as measured"

end Tools.ShippingLeafSweepCommand
