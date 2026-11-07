import Tools.ShippingFGCircuitS3mField
import Tools.ShippingFGCircuitS3jStart
import Tools.ShippingFGCircuitS1kStmt
set_option autoImplicit false
-- FG circuit pilot Check53 (S3m): (A) the complete types of the constructed theorems against independently written expected types, with mutants; (B) the primitives the first blocking fields rest on are opaque constants, and the statements reach nothing else opaque; (C) the field inventory of CellPrem / Laws; (D) AXIOMS.  The last block is a MetaM EXECUTION OBSERVATION in the real compile process (category (d)); it proves nothing about the logic.  docs/FG-CIRCUIT-PILOT.md §63.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck53
open Lean Meta Elab Command Term
open Tools.ShippingFGCircuitS3m

/-- elaborate a type independently written here -/
def elabTy (stx : Syntax) : TermElabM Expr := do
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

def tyOfConst (n : Name) : MetaM Expr := do
  return (← getConstInfo n).type

/-- the theorem's type is defeq to the expected one, and each mutant is NOT -/
def chk (n : Name) (expected : Syntax) (mutants : List Syntax) : TermElabM Nat := do
  let t ← tyOfConst n
  let e ← elabTy expected
  unless ← isDefEq t e do throwError "FGCIRCUIT53 {n}: the type differs from the independently written one"
  let mut k := 0
  for m in mutants do
    let me ← elabTy m
    if ← isDefEq t me then throwError "FGCIRCUIT53 {n}: a mutant is accepted: {m}"
    k := k + 1
  return k

/-! ## (A) complete types against independent statements -/
run_cmd liftTermElabM do
  let mut nm := 0
  -- 1. the first CellPrem field, unfolded to the primitive (independent: spelled with ST.Ref.get, not getW)
  nm := nm + (← chk ``readWorld_cache_unfold
    (← `(Tools.ShippingStRefCorrespondence.ReadWorld Sparkle.Compiler.Elab.sparkleChildCache ↔
        ∀ w : Void IO.RealWorld, (match (ST.Ref.get Sparkle.Compiler.Elab.sparkleChildCache : ST IO.RealWorld _) w with | .mk _ w' => w') = w))
    [← `(Tools.ShippingStRefCorrespondence.ReadWorld Sparkle.Compiler.Elab.sparkleChildSynth ↔
        ∀ w : Void IO.RealWorld, (match (ST.Ref.get Sparkle.Compiler.Elab.sparkleChildSynth : ST IO.RealWorld _) w with | .mk _ w' => w') = w),
     ← `(Tools.ShippingStRefCorrespondence.ReadWorld Sparkle.Compiler.Elab.sparkleChildCache ↔
        ∀ w : Void IO.RealWorld, (match (ST.Ref.get Sparkle.Compiler.Elab.sparkleChildCache : ST IO.RealWorld _) w with | .mk _ _ => w) = w)])
  -- 2. pointer type: a subsingleton pointer type refutes CellPrem
  nm := nm + (← chk ``cellPrem_false_of_subsingleton
    (← `(Subsingleton ST.RefPointed.type → ∀ (Fresh : (σ : Type) → IO.Ref σ → Prop) (mref : ST.Ref IO.RealWorld Lean.Meta.State)
        (cref : ST.Ref IO.RealWorld Lean.Core.State), ¬ Tools.ShippingGen5EnvFrame3.CellPrem Fresh mref cref))
    [← `(Subsingleton ST.RefPointed.type → ∀ (Fresh : (σ : Type) → IO.Ref σ → Prop) (mref : ST.Ref IO.RealWorld Lean.Meta.State)
        (cref : ST.Ref IO.RealWorld Lean.Core.State), Tools.ShippingGen5EnvFrame3.CellPrem Fresh mref cref),
     ← `(∀ (Fresh : (σ : Type) → IO.Ref σ → Prop) (mref : ST.Ref IO.RealWorld Lean.Meta.State)
        (cref : ST.Ref IO.RealWorld Lean.Core.State), ¬ Tools.ShippingGen5EnvFrame3.CellPrem Fresh mref cref)])
  -- 3. Laws.O.diag entails StderrKeeps at the default Meta context (the statement spelled out)
  nm := nm + (← chk ``stderrKeeps_of_ops
    (← `(∀ {Fresh : (σ : Type) → IO.Ref σ → Prop} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} (O : Tools.ShippingChildInvA.RefLawsAOps Fresh mref cref) (_cctx : Lean.Core.Context),
        ∀ w : Void IO.RealWorld, O.quiet w →
          (Tools.ShippingChildBndCore.cv (stderrW w) = Tools.ShippingChildBndCore.cv w ∧
           Tools.ShippingChildBndCore.sv (stderrW w) = Tools.ShippingChildBndCore.sv w ∧
           Tools.ShippingChildBndCore.dv (stderrW w) = Tools.ShippingChildBndCore.dv w) ∧ O.quiet (stderrW w)))
    [← `(∀ {Fresh : (σ : Type) → IO.Ref σ → Prop} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} (O : Tools.ShippingChildInvA.RefLawsAOps Fresh mref cref) (_cctx : Lean.Core.Context),
        ∀ w : Void IO.RealWorld, O.quiet w →
          (Tools.ShippingChildBndCore.cv (stderrW w) = Tools.ShippingChildBndCore.cv w ∧
           Tools.ShippingChildBndCore.sv (stderrW w) = Tools.ShippingChildBndCore.sv w) ∧ O.quiet (stderrW w)),
     ← `(∀ {Fresh : (σ : Type) → IO.Ref σ → Prop} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
        {cref : ST.Ref IO.RealWorld Lean.Core.State} (O : Tools.ShippingChildInvA.RefLawsAOps Fresh mref cref) (_cctx : Lean.Core.Context),
        ∀ w : Void IO.RealWorld,
          (Tools.ShippingChildBndCore.cv (stderrW w) = Tools.ShippingChildBndCore.cv w ∧
           Tools.ShippingChildBndCore.sv (stderrW w) = Tools.ShippingChildBndCore.sv w ∧
           Tools.ShippingChildBndCore.dv (stderrW w) = Tools.ShippingChildBndCore.dv w) ∧ O.quiet (stderrW w))])
  -- 4. the smallest sufficient fact
  nm := nm + (← chk ``stderrKeeps_of_id
    (← `((∀ w, stderrW w = w) → ∀ quiet : Void IO.RealWorld → Prop, StderrKeeps quiet))
    [← `(∀ quiet : Void IO.RealWorld → Prop, StderrKeeps quiet),
     ← `((∀ w, stderrW w = w) → ∀ quiet : Void IO.RealWorld → Prop, False)])
  -- 5. the model lemma (category (a))
  nm := nm + (← chk ``readWorld_shape_both
    (← `((∃ g : Bool → Bool, ∀ w, g w = w) ∧ (∃ g : Bool → Bool, ¬ ∀ w, g w = w)))
    [← `((∃ g : Bool → Bool, ∀ w, g w = w) ∧ (∃ g : Bool → Bool, ∀ w, g w = w))])
  logInfo m!"FGCIRCUIT53 SIGNATURES: 5 constructed theorems (readWorld_cache_unfold, cellPrem_false_of_subsingleton, stderrKeeps_of_ops, stderrKeeps_of_id, readWorld_shape_both) equal their independently written types, {nm} mutants rejected (another ref, a constant match, CellPrem not negated, no quiet premise, dropped dv conjunct, no premise on stderrW, a vacuous conclusion)"

/-! ## (B) the primitives under the first blocking fields are opaque; nothing else opaque is reached -/
/-- the opaque constants reachable from `n` through definitions (theorems are not entered) -/
partial def opaquesOf (e0 : Expr) : MetaM (NameSet × Nat) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut ops : NameSet := {}
  let mut todo : List Name := e0.getUsedConstants.toList
  let mut fuel := 200000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      if seen.contains c then continue
      seen := seen.insert c
      match env.find? c with
      | some (.opaqueInfo _) => ops := ops.insert c
      | some (.defnInfo v) =>
        for d in v.type.getUsedConstants ++ v.value.getUsedConstants do
          unless seen.contains d do todo := d :: todo
      | some (.thmInfo _) => pure ()
      | some ci => for d in ci.type.getUsedConstants do
          unless seen.contains d do todo := d :: todo
      | none => pure ()
  return (ops, seen.size)

run_cmd liftTermElabM do
  let env ← getEnv
  for n in [``ST.Prim.Ref.get, ``ST.Prim.Ref.set, ``ST.Prim.mkRef, ``ST.RefPointed, ``Void.mk, ``Void.nonemptyType, ``IO.getStderr,
            ``Sparkle.Compiler.Elab.sparkleChildCache, ``Sparkle.Compiler.Elab.sparkleChildSynth, ``Sparkle.Compiler.Elab.sparkleSynthDepth] do
    match env.find? n with
    | some (.opaqueInfo _) => pure ()
    | _ => throwError "FGCIRCUIT53 OPAQUE: {n} is not an opaque constant"
  -- the first CellPrem field: ReadWorld sparkleChildCache
  let (o1, n1) ← opaquesOf (← tyOfConst ``readWorld_cache_unfold)
  let (o2, n2) ← opaquesOf (mkConst ``stderrW)
  let (o3, n3) ← opaquesOf (mkConst ``StderrKeeps)
  unless o1.contains ``ST.Prim.Ref.get && o1.contains ``Sparkle.Compiler.Elab.sparkleChildCache do throwError "FGCIRCUIT53 OPAQUE: the first field does not reach get/sparkleChildCache"
  unless o2.contains ``IO.getStderr do throwError "FGCIRCUIT53 OPAQUE: stderrW does not reach IO.getStderr"
  -- StderrKeeps reaches the ref-read primitives of cv/sv/dv and IO.getStderr, nothing about the stream's behaviour
  unless o3.contains ``IO.getStderr && o3.contains ``ST.Prim.Ref.get do throwError "FGCIRCUIT53 OPAQUE: StderrKeeps"
  logInfo m!"FGCIRCUIT53 OPAQUE: the ten primitives (ST.Prim.Ref.get/set/mkRef, ST.RefPointed, Void.mk, Void.nonemptyType, IO.getStderr, sparkleChildCache/Synth/SynthDepth) are opaque constants (kernel cannot unfold them).  The statement ReadWorld sparkleChildCache (the first CellPrem field) reaches {o1.size} opaque constants {o1.toList} through {n1} constants; stderrW (the world under the first Laws field) reaches {o2.toList} ({n2} constants); StderrKeeps reaches {o3.toList} ({n3} constants).  No defining equation of any of them is in the API"

/-! ## (C) the field inventory -/
run_cmd liftTermElabM do
  let env ← getEnv
  -- CellPremFields: count the conjuncts of the right spine
  let some (.defnInfo cp) := env.find? ``CellPremFields | throwError "no CellPremFields"
  let rec spine (e : Expr) : Nat := match e.getAppFn.constName?, e.getAppNumArgs with
    | some ``And, 2 => 1 + spine (e.getArg! 1)
    | _, _ => 1
  let rec lamBody (e : Expr) : Expr := match e with | .lam _ _ b _ => lamBody b | e => e
  let n := spine (lamBody cp.value)
  unless n == 16 do throwError "FGCIRCUIT53 FIELDS: CellPremFields has {n} conjuncts, expected 16"
  let fo := getStructureFields env ``Tools.ShippingChildInvA.RefLawsAOps
  let ft := getStructureFields env ``Tools.ShippingChildInvA.RefLawsATele
  unless fo.size == 10 && ft.size == 4 do throwError "FGCIRCUIT53 FIELDS: RefLawsAOps {fo.size} / RefLawsATele {ft.size}"
  unless fo[0]! == `quiet && fo[1]! == `diag do throwError "FGCIRCUIT53 FIELDS: order"
  logInfo m!"FGCIRCUIT53 FIELDS: CellPrem = 10 top-level conjuncts = {n} atomic conjuncts (cellPrem_iff_fields), the first ReadWorld sparkleChildCache; Laws = RefLawsAOps ({fo.size}: {fo.toList}) + RefLawsATele ({ft.size}: {ft.toList}); the first Prop field of Laws.O is diag"

/-! ## (D) AXIOMS -/
run_cmd liftTermElabM do
  let env ← getEnv
  let names : List Name := [``cellPrem_iff_fields, ``readWorld_cache_unfold, ``cellPrem_false_of_subsingleton, ``readWorld_shape_both, ``endW_getStderr,
    ``stderrKeeps_of_ops, ``stderrKeeps_of_laws, ``stderrKeeps_of_id, ``diag_stderr_at_depth0]
  for n in names do
    unless env.contains n do throwError "{n} does not exist"
  let mut axs : NameSet := {}
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT53 AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no native_decide"

/-! ## (E) category (d): MetaM EXECUTION OBSERVATION (no logical content) -/
run_cmd liftTermElabM do
  let ok (b : Bool) (msg : String) : MetaM Unit := unless b do throwError "FGCIRCUIT53 observation failed: {msg}"
  let ctx ← readThe Meta.Context
  ok ctx.canUnfold?.isNone "no canUnfold? callback in the run_cmd context"
  let c0 ← Sparkle.Compiler.Elab.sparkleChildCache.get
  let s0 ← Sparkle.Compiler.Elab.sparkleChildSynth.get
  let d0 ← Sparkle.Compiler.Elab.sparkleSynthDepth.get
  let _ ← IO.getStderr
  let c1 ← Sparkle.Compiler.Elab.sparkleChildCache.get
  let s1 ← Sparkle.Compiler.Elab.sparkleChildSynth.get
  let d1 ← Sparkle.Compiler.Elab.sparkleSynthDepth.get
  ok (c0.size == c1.size && d0 == d1 && s0.isSome == s1.isSome) "IO.getStderr changed a tracked cell"
  ok (d0 == 0) "depth reads 0"
  let r ← (Tools.ShippingFGCircuitS3jStart.pilotEntry3 Tools.ShippingFGCircuitS1kStmt.hftRoot).run'
  let _ := r
  ok ((← Sparkle.Compiler.Elab.sparkleSynthDepth.get) == d0) "depth after pilotEntry3"
  logInfo m!"FGCIRCUIT53 OBSERVATION (category (d), real process, not a proof): in this compile process the depth cell reads {d0}, sparkleChildSynth is some = {s0.isSome}, the cache has {c0.size} entries before and after IO.getStderr (unchanged), and pilotEntry3 hftRoot returns without error in the run_cmd context.  The world token is erased at runtime: ReadWorld / SetFrame are not observable, and the run's start world is not a Lean term"

end Tests.Gen5.FGCircuitPilotCheck53
