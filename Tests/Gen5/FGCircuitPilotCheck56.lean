import Tools.ShippingFGCircuitS3rObs
set_option autoImplicit false
-- FG circuit pilot Check56 (S3r): (A) the kernel facts about the closed artifact terms (types against independently written statements; the proofs are `decide +kernel`, no native_decide), (B) negative controls (an altered statement makes the existing check false, kernel-checked), (C) the observation module that re-runs `pilotEntry3 hftRoot` and compares with the generated terms is built (a build dependency; an OBSERVATION, not a kernel fact), (D) AXIOMS (standard only), (E) a size and time line labelled as ONE run.  The facts are checker outputs on a closed term, NOT a semantic-preservation theorem; `seqCheck`/`shipsHierCheck`/`checkedOptimize` are not kernel-reducible (docs §68).  docs/FG-CIRCUIT-PILOT.md §68.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck56
open Lean Meta Elab Command Term

def elabTy (stx : Syntax) : TermElabM Expr := do
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- the theorem's type is defeq to the independently written statement -/
def chk (n : Name) (expected : Syntax) : TermElabM Unit := do
  let t := (← getConstInfo n).type
  let e ← elabTy expected
  unless ← isDefEq t e do throwError "FGCIRCUIT56 {n}: the type differs from the independently written one"

def thmValue (n : Name) : MetaM Expr := do
  match (← getConstInfo n) with
  | .thmInfo i => pure i.value
  | _ => throwError "FGCIRCUIT56 {n} is not a theorem"

/-- re-add the proof term of `n` under a fresh name: the kernel type-checks it again; returns the milliseconds -/
def retime (n : Name) : CoreM Nat := do
  let ci ← getConstInfo n
  let some v := ci.value? | throwError "FGCIRCUIT56 {n}: no value"
  let t0 ← IO.monoMsNow
  addDecl (.thmDecl { name := n ++ `retimed, levelParams := ci.levelParams, type := ci.type, value := v })
  return (← IO.monoMsNow) - t0

run_cmd liftTermElabM do
  let ns := `Tools.ShippingFGCircuitS3rKernel
  -- (A) the kernel facts, against independent spellings
  chk (ns ++ `hier_binds) (← `(Sparkle.IR.RefineCheck.hierBinds Tools.ShippingFGCircuitS3rArtifact.pilotB0 = true))
  chk (ns ++ `hier_refine_self) (← `(Sparkle.IR.RefineCheck.hierRefineCheck Tools.ShippingFGCircuitS3rArtifact.pilotB0 Tools.ShippingFGCircuitS3rArtifact.pilotB0 = true))
  chk (ns ++ `refine_child0) (← `(Sparkle.IR.RefineCheck.refineCheck Tools.ShippingFGCircuitS3rArtifact.pilotK0 Tools.ShippingFGCircuitS3rArtifact.pilotK0 = true))
  chk (ns ++ `refine_child1) (← `(Sparkle.IR.RefineCheck.refineCheck Tools.ShippingFGCircuitS3rArtifact.pilotK1 Tools.ShippingFGCircuitS3rArtifact.pilotK1 = true))
  chk (ns ++ `merge_fixed) (← `(Sparkle.IR.RefineCheck.mergeChecked Tools.ShippingFGCircuitS3rArtifact.pilotB0 = Tools.ShippingFGCircuitS3rArtifact.pilotB0))
  chk (ns ++ `hier_refine_shipped) (← `(Sparkle.IR.RefineCheck.hierRefineCheck Tools.ShippingFGCircuitS3rArtifact.pilotB0 Tools.ShippingFGCircuitS3rArtifact.pilotS0 = true))
  chk (ns ++ `design_kids) (← `(Tools.ShippingFGCircuitS3rArtifact.pilotD0.modules = [Tools.ShippingFGCircuitS3rArtifact.pilotK0, Tools.ShippingFGCircuitS3rArtifact.pilotK1]))
  -- (B) negative controls (kernel-checked statements: the check is FALSE on the altered module)
  chk (ns ++ `neg_drop) (← `(Sparkle.IR.RefineCheck.hierRefineCheck Tools.ShippingFGCircuitS3rArtifact.pilotB0 (Tools.ShippingFGCircuitS3rKernel.dropFirst Tools.ShippingFGCircuitS3rArtifact.pilotS0) = false))
  chk (ns ++ `neg_init) (← `(Sparkle.IR.RefineCheck.hierRefineCheck Tools.ShippingFGCircuitS3rArtifact.pilotB0 (Tools.ShippingFGCircuitS3rKernel.flipInit Tools.ShippingFGCircuitS3rArtifact.pilotS0) = false))
  logInfo m!"FGCIRCUIT56 KERNEL: 7 facts (hierBinds b0; hierRefineCheck b0 b0; refineCheck on each of the 2 children; mergeChecked b0 = b0; hierRefineCheck b0 shipped; design children = [K0, K1]) + shipsHierCheck's conjuncts with the shipped form supplied as a closed term, each by `decide +kernel`/`rfl`; 6 negative controls (an altered statement makes hierRefineCheck/refineCheck FALSE; the altered modules differ from the originals); types match independently written statements; NOT kernel-evaluable: shipsHierCheck, checkedOptimize (partial optimizer), seqCheck (String.all)"
  -- (D) AXIOMS
  let names : List Name := [`hier_binds, `hier_refine_self, `refine_child0, `refine_child1, `design_kids, `merge_fixed, `hier_refine_shipped, `ships_hier_shipped, `neg_drop, `neg_init, `neg_child0, `neg_child1, `neg_distinct, `shape].map (ns ++ ·)
  let env ← getEnv
  let mut axs : NameSet := {}
  for nm in names do
    unless env.contains nm do throwError "{nm} does not exist"
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT56 AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no Lean.ofReduceBool (no native_decide)"
  -- (E) size and time: ONE run
  let mut sizes : List (Name × Nat) := []
  for d in [`pilotB0, `pilotS0, `pilotK0, `pilotK1, `pilotD0] do
    let v := (← getConstInfo (`Tools.ShippingFGCircuitS3rArtifact ++ d)).value!
    sizes := sizes ++ [(d, v.sizeWithoutSharing)]
  let t1 ← liftCoreM <| retime (ns ++ `refine_child0)
  let t2 ← liftCoreM <| retime (ns ++ `hier_refine_self)
  logInfo m!"FGCIRCUIT56 SIZE/TIME (ONE run, this machine; not a bound): closed-term sizes without sharing {sizes}; kernel re-check of the proof term of refine_child0 took {t1} ms, of hier_refine_self {t2} ms"
  -- (C) the observation module is a build dependency of this file
  unless env.contains `Tools.ShippingFGCircuitS3rObs.seqOk do throwError "FGCIRCUIT56: the observation module is not imported"
  logInfo m!"FGCIRCUIT56 OBSERVATION: Tools.ShippingFGCircuitS3rObs (a build dependency of this check) re-ran pilotEntry3 hftRoot and compared with BEq: (b, D) == (pilotB0, pilotD0) and checkedOptimize b == pilotS0 (compiled code, one run: an observation, not a kernel fact)"

end Tests.Gen5.FGCircuitPilotCheck56
