import Lean.Elab.Command
import Tests.Compiler.MemDepthProbeTest
import Tools.ShippingKidFactsT
import Tools.ShippingDesignSVMem

/-! # Which depth index accepts the built memory module (a measurement, round par/d-1)

WRITTEN, NOT BUILT. TARGET-ONLY; not in `Tests.AllTests`. Nothing here is a
theorem about the compiler and nothing asserts: the file LOGS Booleans. It
settles, by the kernel, a claim that `docs/parallel/C-mem-depth-free.md` §2
made BY READING:

    KidFacts mref cref memCounterH … n   is false for every n

because `KidFacts.check` asks `kidCheck C n` of the kid's own module AND of
every module of its design at ONE index `n`, while

* the memory module of the kid's design passes `kidCheck C 0` (`leafCheck`)
  and fails `kidCheck C (m + 1)` (`designCheck C m`: `textCheckI`, whose
  first conjunct rejects a memory statement), and
* the kid's own module, which has an INSTANCE (of the memory module), fails
  `kidCheck C 0` (`leafCheck`: its first conjunct rejects an instance).

## How the Booleans are obtained

As `#norepeat_log` of `Tests/Compiler/NoRepeatFamilyTest.lean` (the command
is copied here so that this file does not import that test's dependencies):
`#memkid_check_log "<tag>" <term>` elaborates, in a scratch copy of the
command state that is restored afterwards,

    example : <term> = true  := by first | decide | decide +kernel
    example : <term> = false := by first | decide | decide +kernel

and logs which one the KERNEL accepted:

    MEMKIDCHECK <tag> = true | false | …

If neither `decide` goes through (the `true` cases evaluate string functions
of the emitter, which the kernel may not reduce), a THIRD attempt is made
and logged as such: `<term> = true` by the BUILT theorem
`Tools.ShippingDesignSV.leafCheck_memModule` (the memory module is a checked
leaf). `UNDECIDED` is not a verdict.

## The child maps

`CM`: the child map of the memory module's OWN design (`childMap
(memModule true 4 8).2.modules`: it resolves the module's own name to it).
`C0`: the child map of the empty module list (resolves nothing). The
`false` verdicts do not depend on the map: the conjunct that fails is the
first one, about the module's statements only.

## The kid's own module

`memCounterH`'s module is the output of a compiler run and is not a closed
term here. The second bullet is measured on its REASON: `leafCheck` of a
module whose body is one instance statement (`instLike`), and the conjunct
`body.all seqStmtOkA` on that body.

## PREDICTED (by reading; NOT observed)

| tag | predicted |
|---|---|
| S1, S2 (sanity) | true, false |
| M1 `leafCheck mem` | true — by `decide` or, failing that, by the built theorem |
| M2 `mem.body.all seqStmtOkI` | false |
| M3 `textCheckI CM mem`, M3' with `C0` | false |
| M4 `kidCheck CM 0 mem` | true (as M1) |
| M5 `kidCheck CM 1 mem`, M5' with `C0` | false |
| M6 `kidCheck CM 2 mem` | false |
| M7 `designCheck CM 0 mem` | false |
| K1 `[inst].all seqStmtOkA` | false |
| K2 `leafCheck instLike` | false |
| K3 `kidCheck CM 0 instLike` | false |

If M5 or K3 came out `true`, the plan of this round (`KidFactsT`: the check
of the kid's own module only) would rest on a wrong reading. -/
namespace Tests.Compiler.MemKidCheckProbe
open Sparkle.IR.AST
open Sparkle.Compiler.MachMemory (memModule)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingDesignSV (leafCheck textCheckI designCheck)
open Tools.ShippingChecksDesign (kidCheck)

/-- The combinational-read memory module of `memCounterH` (address width 4,
data width 8). -/
abbrev mem : Sparkle.IR.AST.Module := (memModule true 4 8).1

/-- The child map of the memory module's own design. -/
abbrev CM : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv) :=
  childMap (memModule true 4 8).2.modules

/-- The child map of no module. -/
abbrev C0 : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv) :=
  childMap []

/-- A module whose body is one instance statement (what `leafCheck` sees of a
kid with an instance). -/
abbrev instLike : Sparkle.IR.AST.Module :=
  { name := "kidLike", inputs := [], outputs := [], wires := [],
    body := [Stmt.inst "child" "inst_0" []] }

open Lean Elab Command in
/-- Elaborate `example : t = <b> := by <tac>` in a scratch copy of the
command state; `true` when it went through without an error. -/
def provesTo (t : TSyntax `term) (b : Bool) (tac : TSyntax `tactic) : CommandElabM Bool := do
  let saved ← get
  modify fun s => { s with messages := {} }
  let stx ←
    if b then `(command| example : $t = true := by $tac:tactic)
    else `(command| example : $t = false := by $tac:tactic)
  let ok : Bool ←
    try
      elabCommand stx
      pure (!(← get).messages.hasErrors)
    catch _ => pure false
  set saved
  pure ok

open Lean Elab Command in
/-- Log which of `t = true`, `t = false` the kernel decides; failing both,
whether `t = true` is the built theorem `leafCheck_memModule`. -/
elab "#memkid_check_log " tag:str t:term : command => do
  let name := tag.getString
  IO.eprintln s!"MEMKIDCHECK START {name}"
  (← IO.getStderr).flush
  let dec ← `(tactic| first | decide | decide +kernel)
  let thm ← `(tactic| exact Tools.ShippingDesignSV.leafCheck_memModule _ _ _)
  let mut verdict : String :=
    "UNDECIDED (neither `decide` went through, and it is not leafCheck_memModule)"
  let decT ← provesTo t true dec
  if decT then
    verdict := "true (kernel decide)"
  else
    let decF ← provesTo t false dec
    if decF then
      verdict := "false (kernel decide)"
    else
      let byThm ← provesTo t true thm
      if byThm then
        verdict := "true (by the built theorem leafCheck_memModule; neither `decide` went through)"
  IO.eprintln s!"MEMKIDCHECK {name} = {verdict}"
  (← IO.getStderr).flush
  logInfo m!"MEMKIDCHECK {name} = {verdict}"

-- the command on closed terms first: one `true`, one `false`
#memkid_check_log "S1 sanity (expected true)" (([] : List Stmt).all Tools.ShippingHierSVSoundness.seqStmtOkI)
#memkid_check_log "S2 sanity (expected false)"
  ([Stmt.memory "mem" 4 8 "clk" (.ref "wa") (.ref "wd") (.ref "we") (.ref "ra") "out_rdata" true
      [] []].all Tools.ShippingHierSVSoundness.seqStmtOkI)

-- the memory module
#memkid_check_log "M1 leafCheck mem (expected true)" (leafCheck mem)
#memkid_check_log "M2 mem.body.all seqStmtOkI (expected false)"
  (mem.body.all Tools.ShippingHierSVSoundness.seqStmtOkI)
#memkid_check_log "M3 textCheckI CM mem (expected false)" (textCheckI CM mem)
#memkid_check_log "M3' textCheckI C0 mem (expected false)" (textCheckI C0 mem)
#memkid_check_log "M4 kidCheck CM 0 mem (expected true)" (kidCheck CM 0 mem)
#memkid_check_log "M5 kidCheck CM 1 mem (expected false)" (kidCheck CM 1 mem)
#memkid_check_log "M5' kidCheck C0 1 mem (expected false)" (kidCheck C0 1 mem)
#memkid_check_log "M6 kidCheck CM 2 mem (expected false)" (kidCheck CM 2 mem)
#memkid_check_log "M7 designCheck CM 0 mem (expected false)" (designCheck CM 0 mem)

-- a module with an instance statement (the kid's own module, by its reason)
#memkid_check_log "K1 [inst].all seqStmtOkA (expected false)"
  (instLike.body.all Tools.ShippingDesignSV.seqStmtOkA)
#memkid_check_log "K2 leafCheck instLike (expected false)" (leafCheck instLike)
#memkid_check_log "K3 kidCheck CM 0 instLike (expected false)" (kidCheck CM 0 instLike)

end Tests.Compiler.MemKidCheckProbe
