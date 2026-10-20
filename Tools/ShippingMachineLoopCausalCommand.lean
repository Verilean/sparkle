import Tools.ShippingMachineCommand
import Tools.ShippingMachineLoopCausal
import Tools.ShippingMachineLoopJoint

/-! # `#machine_ext_joint f`: the joint causality of a loop's calls (round par/c-1)

WRITTEN, NOT BUILT.

For a hand-written `Signal.loop` WITH calls (`f.machine_sound` has the head
`machine_trace_of_loop_causal`), `#machine_ext_joint f` adds

* `f.machine_sigma_inj : ∀ i x x', f.machineSigma i x = f.machineSigma i x' → x = x'`
  — the state encoding is injective: a left inverse is built from the
  encoding's own value (the leaves are projections of the state; the tree of
  pairs is rebuilt from them) and `eq_of_leftInv` is applied; the inverse's
  equation is `fun x => rfl` (the kernel's eta for pairs);
* `f.machine_ext_ctx : ∀ i (x x' : Ctx D α) t, CtxAgree x x' t → (the two
  extension families agree at t)` — the chain `extendBits_val` /
  `extendBools_val` over the BUILT per-entry theorems `f.machine_causal_{k}`
  (which `loopCalls` proves over contexts of the inputs and the raw state),
  from `CtxAgree.v` / `CtxAgree.b`. The entries are read off the values of
  `f.machineExt` / `f.machineExtB` (their positions are `nDecl + k`);
* `f.machine_ext_joint`: the `hjoint` of `src_causal_of_loop_causal` at
  `f`'s endpoint arguments, by `ext_joint_of_ctx`. Its statement is taken
  from that theorem's binder, so it fits by construction.

Nothing is evaluated: the three declarations are terms checked by the
kernel (`addDecl`), with no asynchronous checking. On a failure nothing is
added. A premise of no endpoint: `causalFactE` passes
`f.machine_ext_joint` to `src_causal_of_loop_causal` when `f` is a child. -/
namespace Tools.ShippingMachineLoopCausalCommand
open Lean Meta
open Tools.ShippingMachineCommand (progress)

/-- A natural-number literal (`OfNat.ofNat Nat n _` or the raw literal). -/
def natOf? (e : Lean.Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getAppArgs[1]! with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- The path of a projection chain of `x` (`true`: first component), from
the root. -/
partial def leafPath (x e : Lean.Expr) : Option (List Bool) :=
  if e == x then some []
  else match e with
    | .proj _ 0 y => (leafPath x y).map (· ++ [true])
    | .proj _ 1 y => (leafPath x y).map (· ++ [false])
    | _ =>
      if e.isAppOfArity ``Prod.fst 3 then (leafPath x e.appArg!).map (· ++ [true])
      else if e.isAppOfArity ``Prod.snd 3 then (leafPath x e.appArg!).map (· ++ [false])
      else none

/-- The state rebuilt from the encoding's leaves: the component at `pre` is
the leaf with that path, or the pair of the two components below it. -/
partial def invTree (declName : Name) (paths : Array (List Bool)) (leaf : Nat → MetaM Lean.Expr)
    (pre : List Bool) : MetaM Lean.Expr := do
  match paths.findIdx? (fun p => p == pre) with
  | some k => leaf k
  | none =>
    unless paths.any (fun p => pre.isPrefixOf p) do
      throwError "{declName}: the state encoding does not read the component {toString pre} of the state"
    let a ← invTree declName paths leaf (pre ++ [true])
    let b ← invTree declName paths leaf (pre ++ [false])
    mkAppM ``Prod.mk #[a, b]

/-- `f.machine_sigma_inj`, of the statement `injT`
(`∀ i x x', σ i x = σ i x' → x = x'`). -/
def sigmaInj (declName : Name) (σ injT : Lean.Expr) : MetaM Name := do
  let name := declName ++ `machine_sigma_inj
  let some σn := σ.constName? | throwError "{declName}: the state encoding is not a constant"
  let some v := (← getConstInfo σn).value? | throwError "{declName}: {σn} has no value"
  let value ← lambdaBoundedTelescope v 2 fun xs body => do
    unless xs.size == 2 do throwError "{declName}: {σn} is not a 2-argument encoding"
    let i := xs[0]!
    let x := xs[1]!
    -- the leaves of the right-nested tuple
    let mut leaves : Array Lean.Expr := #[]
    let mut e := body
    while e.isAppOfArity ``Prod.mk 4 do
      let a := e.getAppArgs
      leaves := leaves.push a[2]!
      e := a[3]!
    unless e.isConstOf ``Unit.unit do
      throwError "{declName}: {σn}'s tuple does not end in the unit"
    let paths ← leaves.mapM fun l => match leafPath x l with
      | some p => pure p
      | none => throwError "{declName}: a component of {σn} is not a projection of the state: {l}"
    let T ← inferType body
    let αi ← inferType x
    -- the left inverse, and its equation (`rfl`: eta for pairs)
    let τ ← withLocalDeclD `h T fun h => do
      let leaf (k : Nat) : MetaM Lean.Expr := do
        let mut c := h
        for _ in [0:k] do
          c ← mkAppM ``Prod.snd #[c]
        mkAppM ``Prod.fst #[c]
      mkLambdaFVars #[h] (← invTree declName paths leaf [])
    let σL ← mkLambdaFVars #[x] body
    let hτ ← mkLambdaFVars #[x] (← mkExpectedTypeHint (mkApp2 (mkConst ``Eq.refl [levelOne]) αi x)
      (mkApp3 (mkConst ``Eq [levelOne]) αi (τ.beta #[body]) x))
    let .forallE _ xT' _ _ := (← instantiateForall injT #[i, x])
      | throwError "{declName}: the injectivity statement (second state)"
    withLocalDeclD `x' xT' fun x' => do
      let .forallE _ hT _ _ := (← instantiateForall injT #[i, x, x'])
        | throwError "{declName}: the injectivity statement (premise)"
      withLocalDeclD `h hT fun h => do
        mkLambdaFVars #[i, x, x', h]
          (mkAppN (mkConst ``Tools.ShippingMachineLoopJoint.eq_of_leftInv)
            #[αi, T, σL, τ, hτ, x, x', h])
  progress s!"{name}: checking"
  try
    addDecl (.thmDecl { name, levelParams := [], type := injT, value })
  catch ex =>
    throwError "{declName}: machine_sigma_inj is not checked by the kernel: {ex.toMessageData}"
  return name

/-- The entries of a chain of `extendBits` ending in `base`, innermost
first: position, width, signal. -/
def readBits (declName : Name) (e base : Lean.Expr) :
    MetaM (Array (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let mut acc : Array (Lean.Expr × Lean.Expr × Lean.Expr) := #[]
  let mut e := e
  while e.isAppOfArity ``Tools.ShippingMachineAuto.extendBits 5 do
    let a := e.getAppArgs
    acc := acc.push (a[2]!, a[3]!, a[4]!)
    e := a[1]!
  unless e == base do
    throwError "{declName}: machineExt's chain does not end in the inputs"
  return acc.reverse

/-- The entries of a chain of `extendBools` ending in `base`, innermost
first: position, signal. -/
def readBools (declName : Name) (e base : Lean.Expr) :
    MetaM (Array (Lean.Expr × Lean.Expr)) := do
  let mut acc : Array (Lean.Expr × Lean.Expr) := #[]
  let mut e := e
  while e.isAppOfArity ``Tools.ShippingMachineCausal.extendBools 4 do
    let a := e.getAppArgs
    acc := acc.push (a[2]!, a[3]!)
    e := a[1]!
  unless e == base do
    throwError "{declName}: machineExtB's chain does not end in the inputs"
  return acc.reverse

/-- `f.machine_ext_ctx`, of the statement `ctxT`: the extensions are causal
over contexts, by the per-entry theorems `f.machine_causal_{k}`. -/
def extCtx (declName : Name) (ι dom α ext extB ctxT : Lean.Expr) : MetaM Name := do
  let name := declName ++ `machine_ext_ctx
  let nat := mkConst ``Nat
  let valueOf (c : Lean.Expr) : MetaM Lean.Expr := do
    let some n := c.constName? | throwError "{declName}: an extension is not a constant"
    let some v := (← getConstInfo n).value? | throwError "{declName}: {n} has no value"
    pure v
  let vV ← valueOf ext
  let vB ← valueOf extB
  let value ← withLocalDeclD `i ι fun i => do
    let D := dom.beta #[i]
    let αi := α.beta #[i]
    let ctx := mkApp2 (mkConst ``Tools.ShippingMachineCausal.Ctx) D αi
    let xB (x : Lean.Expr) := mkApp3 (mkConst ``Tools.ShippingMachineCausal.Ctx.B) D αi x
    let xV (x : Lean.Expr) := mkApp3 (mkConst ``Tools.ShippingMachineCausal.Ctx.V) D αi x
    let xS (x : Lean.Expr) := mkApp3 (mkConst ``Tools.ShippingMachineCausal.Ctx.S) D αi x
    withLocalDeclD `x ctx fun x => withLocalDeclD `x' ctx fun x' =>
      withLocalDeclD `t nat fun t => do
      withLocalDeclD `h (mkAppN (mkConst ``Tools.ShippingMachineCausal.CtxAgree) #[D, αi, x, x', t])
        fun h => do
      let at_ (y : Lean.Expr) : Array Lean.Expr := #[i, xB y, xV y, xS y]
      let chainV ← readBits declName (vV.beta (at_ x)) (xV x)
      let chainV' ← readBits declName (vV.beta (at_ x')) (xV x')
      let chainB ← readBools declName (vB.beta (at_ x)) (xB x)
      let chainB' ← readBools declName (vB.beta (at_ x')) (xB x')
      unless chainV.size == chainV'.size && chainB.size == chainB'.size do
        throwError "{declName}: the extensions at two contexts differ in length"
      -- the entries' indices: the positions are `nDecl + k`
      let posOf (p : Lean.Expr) : MetaM Nat := match natOf? p with
        | some n => pure n
        | none => throwError "{declName}: an extension position is not a literal: {p}"
      let mut all : Array Nat := #[]
      for (p, _, _) in chainV do
        all := all.push (← posOf p)
      for (p, _) in chainB do
        all := all.push (← posOf p)
      if all.isEmpty then throwError "{declName}: the extensions have no entry"
      let lo := all.foldl Nat.min all[0]!
      for j in [0:all.size] do
        unless all.contains (lo + j) do
          throwError "{declName}: the extension positions {toString all} are not consecutive"
      let fact (p : Nat) : MetaM Lean.Expr := do
        let nm := declName ++ Name.mkSimple s!"machine_causal_{p - lo}"
        unless (← getEnv).contains nm do
          throwError "{declName}: no {nm} (the endpoint generator's per-entry causality)"
        pure (mkAppN (mkConst nm) #[i, x, x', t, h])
      let mut hV := mkAppN (mkConst ``Tools.ShippingMachineCausal.CtxAgree.v) #[D, αi, x, x', t, h]
      let mut hB := mkAppN (mkConst ``Tools.ShippingMachineCausal.CtxAgree.b) #[D, αi, x, x', t, h]
      let mut curV := xV x
      let mut curV' := xV x'
      let mut curB := xB x
      let mut curB' := xB x'
      for j in [0:chainV.size] do
        let (p, w, sg) := chainV[j]!
        let (_, _, sg') := chainV'[j]!
        let fk ← fact (← posOf p)
        hV := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits_val)
          #[D, curV, curV', p, w, sg, sg', t, hV, fk]
        curV := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, curV, p, w, sg]
        curV' := mkAppN (mkConst ``Tools.ShippingMachineAuto.extendBits) #[D, curV', p, w, sg']
      for j in [0:chainB.size] do
        let (p, sg) := chainB[j]!
        let (_, sg') := chainB'[j]!
        let fk ← fact (← posOf p)
        hB := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools_val)
          #[D, curB, curB', p, sg, sg', t, hB, fk]
        curB := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, curB, p, sg]
        curB' := mkAppN (mkConst ``Tools.ShippingMachineCausal.extendBools) #[D, curB', p, sg']
      mkLambdaFVars #[i, x, x', t, h] (← mkAppM ``And.intro #[hV, hB])
  progress s!"{name}: checking"
  try
    addDecl (.thmDecl { name, levelParams := [], type := ctxT, value })
  catch ex =>
    throwError "{declName}: machine_ext_ctx is not checked by the kernel: {ex.toMessageData}"
  return name

/-- The three declarations of `#machine_ext_joint` (no restore on failure:
`generate`). -/
def generateCore (declName : Name) : MetaM Name := do
  let jointName := declName ++ `machine_ext_joint
  if (← getEnv).contains jointName then return jointName
  let some (.thmInfo th) := (← getEnv).find? (declName ++ `machine_sound)
    | throwError "{declName}: no endpoint (run #machine_endpoint {declName} first)"
  unless th.value.isAppOf ``Tools.ShippingMachineCausal.machine_trace_of_loop_causal do
    throwError "{declName}: the endpoint is not machine_trace_of_loop_causal (not a hand-written loop with calls, or a transported endpoint)"
  let cargs := th.value.getAppArgs
  unless cargs.size == 23 do
    throwError "{declName}: the endpoint's head has {cargs.size} arguments, 23 expected"
  let d := cargs[1]!
  let ι := cargs[2]!
  let dom := cargs[3]!
  let α := cargs[4]!
  let σ := cargs[7]!
  let ext := cargs[12]!
  let extB := cargs[13]!
  -- the statements, from the binders of the theorems they are passed to
  let .forallE _ jointT _ _ := (← inferType
      (mkAppN (mkConst ``Tools.ShippingMachineLoopCausal.src_causal_of_loop_causal) cargs))
    | throwError "{declName}: src_causal_of_loop_causal has no binder after the endpoint's arguments"
  let pre := mkAppN (mkConst ``Tools.ShippingMachineLoopJoint.ext_joint_of_ctx)
    #[d, ι, dom, α, σ, ext, extB]
  let .forallE _ injT _ _ := (← inferType pre)
    | throwError "{declName}: ext_joint_of_ctx (the injectivity binder)"
  let injName ← sigmaInj declName σ injT
  let pre := mkApp pre (mkConst injName)
  let .forallE _ ctxT _ _ := (← inferType pre)
    | throwError "{declName}: ext_joint_of_ctx (the context binder)"
  let ctxName ← extCtx declName ι dom α ext extB ctxT
  let value := mkApp pre (mkConst ctxName)
  progress s!"{jointName}: checking"
  try
    addDecl (.thmDecl { name := jointName, levelParams := [], type := jointT, value })
  catch ex =>
    throwError "{declName}: machine_ext_joint is not checked by the kernel: {ex.toMessageData}"
  for name in [injName, ctxName, jointName] do
    for ax in ← Lean.collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} uses a non-standard axiom: {ax}"
  return jointName

/-- `f.machine_ext_joint` (with `f.machine_sigma_inj`, `f.machine_ext_ctx`);
on failure nothing is added. Every declaration is checked by the kernel
before the next one is built. -/
def generate (declName : Name) : MetaM Name := do
  let saved ← getEnv
  try
    withOptions (fun o => Lean.Elab.async.set o false) (generateCore declName)
  catch ex =>
    setEnv saved
    throw ex

open Lean.Elab Lean.Elab.Command in
/-- `#machine_ext_joint f`: for a hand-written loop with calls, the joint
causality of its calls' extensions in the inputs and the encoded state
(`f.machine_ext_joint`, the `hjoint` of `src_causal_of_loop_causal`). -/
elab "#machine_ext_joint " d:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo d
  let name ← liftTermElabM (generate declName)
  logInfo m!"{name}: the loop's calls are causal in the inputs and the encoded state, checked by the kernel"

end Tools.ShippingMachineLoopCausalCommand
