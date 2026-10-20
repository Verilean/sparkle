import Tools.ShippingCombLeafClosedCommand

/-! # `#comb_closed_sweep_expect f "CLASS" ["reason"]`: the MEASURED class of a swept slotless leaf, asserted (round par/b-34)

WRITTEN, NOT BUILT.

`#comb_closed_sweep f` (BUILT at 7d8d56b1) logs and never fails. This
command asserts the class MEASURED by the integrator's build (all 32
`GENERATED`): it reads the row `#comb_closed_sweep f` left in this file's
table and is an ERROR when

* `f` was not swept in this file;
* the row's class is not the written one;
* for `GENERATED` / `REBUILT`: the row's audit is not `OK`, its listing has a
  NOT ALLOWED line, or `f.machine_design_comb0` is not in the environment;
* for a class with a reason: the generator's line does not contain the text.

It adds nothing to the environment. Each line is its own command. -/
namespace Tools.ShippingCombLeafClosedCommand
open Lean Meta Elab Command

elab "#comb_closed_sweep_expect " d:ident e:str r:(str)? : command => do
  let f ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let want : String := e.getString
  let rs ← rows.get
  let mine := (rs.filter fun x => x.decl == toString f).toList.reverse
  let row ← match mine with
    | x :: _ => pure x
    | [] => throwError "COMBCLOSED EXPECT {f}: not swept in this file (no #comb_closed_sweep {f} before this line)"
  unless row.tag == want do
    throwError "COMBCLOSED EXPECT {f}: measured {want}, now {row.tag} — {row.note}"
  if want == "GENERATED" || want == "REBUILT" then
    unless row.audit == "OK" do
      throwError "COMBCLOSED EXPECT {f}: {row.tag}, but its audit did not pass: {row.audit}"
    unless row.bad == 0 do
      throwError "COMBCLOSED EXPECT {f}: {row.tag}, with {row.bad} NOT ALLOWED lines"
    unless (← getEnv).contains (f ++ `machine_design_comb0) do
      throwError "COMBCLOSED EXPECT {f}: {row.tag}, but {f ++ `machine_design_comb0} is not in the environment"
  match r with
  | some s =>
    let sub : String := s.getString
    unless (row.note.splitOn sub).length > 1 do
      throwError "COMBCLOSED EXPECT {f}: {row.tag}, but its reason does not contain \"{sub}\": {row.note}"
  | none => pure ()
  logInfo m!"COMBCLOSED EXPECT {f}: {row.tag}, as measured"

end Tools.ShippingCombLeafClosedCommand
