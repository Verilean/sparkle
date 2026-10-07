import Lean
import Tools.ShippingLoopFusion

/-! # Fusing nested hand-written loops, per declaration

A declaration whose root `Signal.loop` holds other loops in its body (the
H.264 frame encoder's FSM around its inlined pipelines) is rewritten to ONE
loop over the tree of states (`Tools.ShippingLoopFusion`): every loop node
gets a packed parameter signal (its ancestors' states and its earlier
siblings), a fused body over it guarded jointly (`Guarded2`), and the
equation "the loop is the projection of the fused loop". The guardedness is
proved from the body's shape (registers over causal inputs, the memory reads
abstracted). The endpoint generator then reads the fused value
(`fuseNormalize`, like the sign operations' rewriting). -/
namespace Tools.ShippingMachineFuseGen
open Lean Meta

/-! ## Terms -/

def sigT (D α : Expr) : Expr := mkApp2 (mkConst ``Sparkle.Core.Signal.Signal [.zero]) D α
def prodT (a b : Expr) : Expr := mkApp2 (mkConst ``Prod [.zero, .zero]) a b
def fstS (D a b p : Expr) : Expr := mkApp4 (mkConst ``Tools.ShippingLoopFusion.fstS) D a b p
def sndS (D a b p : Expr) : Expr := mkApp4 (mkConst ``Tools.ShippingLoopFusion.sndS) D a b p
def pairS (D a b x y : Expr) : Expr := mkApp5 (mkConst ``Tools.ShippingLoopFusion.pairS) D a b x y
def valE (D α s t : Expr) : Expr :=
  mkApp (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.val [.zero]) D α s) t

/-- The element type of a Signal type. -/
def sigElem (ty : Expr) : MetaM Expr := do
  let ty ← whnfR ty
  match ty.getAppFn, ty.getAppArgs with
  | .const ``Sparkle.Core.Signal.Signal _, #[_, α] => pure α
  | _, _ => throwError "fuse: not a Signal type: {ty}"

/-- A `Signal.loop` application: domain, state type, `Inhabited`, body. -/
def loopApp? (e : Expr) : Option (Expr × Expr × Expr × Expr) :=
  if e.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
    let a := e.getAppArgs
    some (a[0]!, a[1]!, a[2]!, a[3]!)
  else none

def isMem (e : Expr) : Bool :=
  e.isAppOfArity ``Sparkle.Core.Signal.Signal.memory 7 ||
    e.isAppOfArity ``Sparkle.Core.Signal.Signal.memoryComboRead 7

/-! ## Causality of a register input, guardedness of a body -/

/-- `Causal (fun P => e)`: the memory reads of `e` (outermost first) are read
from a family at their positions, the rest is pointwise (a `rfl`), each
memory read is causal when its operands are (recursively). -/
partial def provCausal (D : Expr) (P : Expr) (e : Expr) : MetaM Expr := do
  let PT ← inferType P
  let σ ← sigElem PT
  let nat := mkConst ``Nat
  -- the outermost memory reads
  let mems : Array Expr := Id.run do
    let mut acc : Array Expr := #[]
    let mut todo : List Expr := [e]
    while !todo.isEmpty do
      match todo with
      | [] => break
      | x :: rest =>
        todo := rest
        if isMem x then
          if !acc.contains x then acc := acc.push x
        else match x with
          | .app f a => todo := f :: a :: todo
          | .lam _ _ b _ => todo := b :: todo
          | .mdata _ b => todo := b :: todo
          | _ => pure ()
    return acc
  let bitsT := Lean.Expr.forallE `j nat
    (.forallE `n nat (sigT D (mkApp (mkConst ``BitVec) (.bvar 0))) .default) .default
  let dwOf (m : Expr) : MetaM Nat := do
    let some n := (← instantiateMVars m.getAppArgs[2]!).nat? <|> (← whnf m.getAppArgs[2]!).rawNatLit?
      | throwError "fuse: a memory's data width {m.getAppArgs[2]!}"
    pure n
  -- g S V: the input with the memory reads at their positions
  let g ← withLocalDeclD `S PT fun S => withLocalDeclD `V bitsT fun V => do
    let mut body := e
    for k in [0:mems.size] do
      let m := mems[k]!
      let w ← dwOf m
      body := body.replace fun x => if x == m then some (mkApp2 V (mkNatLit k) (mkNatLit w)) else none
    mkLambdaFVars #[S, V] (body.replaceFVar P S)
  let base0 ← withLocalDeclD `p nat fun pv => withLocalDeclD `n nat fun n => mkLambdaFVars #[pv, n]
    (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.pure [.zero]) D (mkApp (mkConst ``BitVec) n)
      (mkApp2 (mkConst ``BitVec.ofNat) n (mkNatLit 0)))
  let famOf (S : Expr) : MetaM Expr := do
    let mut fv := base0
    for k in [0:mems.size] do
      let m := mems[k]!
      fv := mkAppN (mkConst ``Tools.ShippingLoopFusion.extV)
        #[D, fv, mkNatLit k, mkNatLit (← dwOf m), m.replaceFVar P S]
    pure fv
  let FV ← withLocalDeclD `S PT fun S => do mkLambdaFVars #[S] (← famOf S)
  -- pointwise: a `rfl`
  let stmt ← withLocalDeclD `S PT fun S => withLocalDeclD `V bitsT fun V =>
    withLocalDeclD `t nat fun t => do
      let γ ← sigElem (← inferType (g.beta #[S, V]))
      let Sc := mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.mk [.zero]) D σ (.lam `u nat (valE D σ S t) .default)
      let Vc ← withLocalDeclD `p nat fun pv => withLocalDeclD `n nat fun n => mkLambdaFVars #[pv, n]
        (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.mk [.zero]) D (mkApp (mkConst ``BitVec) n)
          (.lam `u nat (valE D (mkApp (mkConst ``BitVec) n) (mkApp2 V pv n) t) .default))
      mkForallFVars #[S, V, t] (← mkEq (valE D γ (g.beta #[S, V]) t) (valE D γ (g.beta #[Sc, Vc]) t))
  let hpt ← forallTelescope stmt fun xs eq => do
    let some (_, l, _) := eq.eq? | throwError "fuse: pointwise statement"
    mkLambdaFVars xs (← mkEqRefl l)
  -- the family causal: each memory read from its operands' causality
  let hFV ← withLocalDeclD `S PT fun S => withLocalDeclD `S' PT fun S' => withLocalDeclD `t nat fun t => do
    let agreeT ← withLocalDeclD `c nat fun c => do
      mkForallFVars #[c] (← mkArrow (← mkAppM ``LE.le #[c, t]) (← mkEq (valE D σ S c) (valE D σ S' c)))
    withLocalDeclD `h agreeT fun h => do
      let mut cur ← withLocalDeclD `j nat fun j => withLocalDeclD `n nat fun n => do
        mkLambdaFVars #[j, n] (← mkEqRefl (valE D (mkApp (mkConst ``BitVec) n) (mkApp2 base0 j n) t))
      let mut fS := base0
      let mut fS' := base0
      for k in [0:mems.size] do
        let m := mems[k]!
        let w ← dwOf m
        let a := m.getAppArgs
        let ops := #[a[3]!, a[4]!, a[5]!, a[6]!]
        let opFns ← ops.mapM fun o => mkLambdaFVars #[P] o
        let opPfs ← ops.mapM fun o => provCausal D P o
        let lemma := if m.isAppOf ``Sparkle.Core.Signal.Signal.memory then
            ``Tools.ShippingLoopFusion.memory_causal else ``Tools.ShippingLoopFusion.memoryComboRead_causal
        let mc := mkAppN (mkConst lemma) (#[D, σ, a[1]!, a[2]!] ++ opFns ++ opPfs)
        let fact := mkAppN mc #[S, S', t, h]
        cur := mkAppN (mkConst ``Tools.ShippingLoopFusion.extV_val)
          #[D, fS, fS', mkNatLit k, mkNatLit w, m.replaceFVar P S, m.replaceFVar P S', t, cur, fact]
        fS := mkAppN (mkConst ``Tools.ShippingLoopFusion.extV) #[D, fS, mkNatLit k, mkNatLit w, m.replaceFVar P S]
        fS' := mkAppN (mkConst ``Tools.ShippingLoopFusion.extV) #[D, fS', mkNatLit k, mkNatLit w, m.replaceFVar P S']
      mkLambdaFVars #[S, S', t, h] cur
  let γ ← sigElem (← inferType e)
  let pf := mkAppN (mkConst ``Tools.ShippingLoopFusion.causal_of_pointwise_V) #[D, σ, γ, g, FV, hpt, hFV]
  -- the input as written: its memory reads are the family's lookups (by evaluation)
  let ty := mkAppN (mkConst ``Tools.ShippingLoopFusion.Causal) #[D, σ, γ, ← mkLambdaFVars #[P] e]
  mkExpectedTypeHint pf ty

/-- `Guarded (fun P => e)` for `e` a tree (`bundle2` / `pairS`) of registers. -/
partial def provGuarded (D : Expr) (P : Expr) (e : Expr) : MetaM Expr := do
  let e := e.headBeta.consumeMData
  let σ ← sigElem (← inferType P)
  let mk2 (lemma : Name) (a b : Expr) : MetaM Expr := do
    let β ← sigElem (← inferType a)
    let γ ← sigElem (← inferType b)
    pure (mkAppN (mkConst lemma) #[D, σ, β, γ, ← mkLambdaFVars #[P] a, ← mkLambdaFVars #[P] b,
      ← provGuarded D P a, ← provGuarded D P b])
  if e.isAppOfArity ``Sparkle.Core.Signal.bundle2 5 then
    let a := e.getAppArgs
    mk2 ``Tools.ShippingLoopFusion.bundle2_guarded a[3]! a[4]!
  else if e.isAppOfArity ``Tools.ShippingLoopFusion.pairS 5 then
    let a := e.getAppArgs
    mk2 ``Tools.ShippingLoopFusion.pairS_guarded a[3]! a[4]!
  else if e.isAppOfArity ``Sparkle.Core.Signal.Signal.register 4 then
    let a := e.getAppArgs
    let γ := a[1]!
    pure (mkAppN (mkConst ``Tools.ShippingLoopFusion.register_guarded)
      #[D, σ, γ, a[2]!, ← mkLambdaFVars #[P] a[3]!, ← provCausal D P a[3]!])
  else throwError "fuse: a loop body is not a tree of registers: {e.getAppFn}"

/-! ## Congruence under a substitution -/

/-- `e = e[atomᵢ ↦ rhsᵢ]` from `eqᵢ : atomᵢ = rhsᵢ` (atoms replaced top-down). -/
def congrSubst (e : Expr) (atoms : Array Expr) (eqs : Array Expr) : MetaM Expr := do
  let tys ← atoms.mapM inferType
  let M ← withLocalDecls (tys.map fun ty => (`y, .default, fun _ => pure ty)) fun ys => do
    let body := e.replace fun x =>
      match atoms.findIdx? (· == x) with
      | some j => some ys[j]!
      | none => none
    mkLambdaFVars ys body
  let mut acc ← mkEqRefl M
  for h in eqs do
    acc ← mkCongr acc h
  pure acc

/-! ## The loop tree, the fused bodies, the equations -/

/-- The loops directly inside a body (not inside another of them), in the
reader's order: the `let`s in order (each value with the earlier ones
substituted), the tail last; each loop once. Returns them zeta-reduced, and
the zeta-reduced body. -/
partial def childLoops (b : Expr) : MetaM (Array Expr × Expr) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Array Expr × Expr) := do
    match e with
    | .letE _ _ v body _ =>
      let v ← zetaReduce v
      go (body.instantiate1 v) (found v acc)
    | .mdata _ b => go b acc
    | e => do
      let e ← zetaReduce e
      pure (found e acc, e)
  go b #[]
where
  found (e : Expr) (acc : Array Expr) : Array Expr := Id.run do
    let mut acc := acc
    let mut todo : List Expr := [e]
    while !todo.isEmpty do
      match todo with
      | [] => break
      | x :: rest =>
        todo := rest
        if (loopApp? x).isSome then
          if !acc.contains x then acc := acc.push x
        else match x with
          | .app f a => todo := f :: a :: todo
          | .lam _ _ b _ => todo := b :: todo
          | .letE _ _ v b _ => todo := v :: b :: todo
          | .mdata _ b => todo := b :: todo
          | _ => pure ()
    return acc

/-- What fusing a loop gives: its state type `α`, the fused state type `Φ`,
the fused body `H : Signal PT → Signal Φ → Signal Φ` (a lambda), its joint
guardedness, whether the loop is the first component (`fstS`) of the fused
loop or the fused loop itself, and `eq : ∀ π, e⟨π⟩ = proj (loop (H π))`. -/
structure Fused where
  α : Expr
  Φ : Expr
  /-- The children's combined state type (`Φ = α × rest` when composite). -/
  rest : Expr := mkConst ``Unit
  H : Expr
  guard : Expr
  composite : Bool
  eq : Expr
  /-- The children's fusions, in the reader's order. -/
  kids : Array Fused := #[]
  deriving Inhabited

/-- The loop's own state from its fused state. -/
def projOf (D : Expr) (r : Fused) (x : Expr) : Expr :=
  if r.composite then fstS D r.α r.rest x else x

/-- Child `i`'s fused state from the combined state of the first `n`
children (`Cpre[m]`: the combined type of the first `m`, left-nested). -/
def accessorIn (D : Expr) (Cpre : Array Expr) (res : Array Fused) : Nat → Nat → Expr → Expr
  | _, 0, q => q
  | _, 1, q => q
  | i, n + 1, q =>
    if i == n then sndS D Cpre[n]! (res[n]!).Φ q
    else accessorIn D Cpre res i n (fstS D Cpre[n]! (res[n]!).Φ q)

/-- Fuse the loop `e` over the parameter type `PT`; `atoms` are the terms its
body may read from outside (the enclosing parameter, the enclosing state, the
earlier siblings) with their accessors from the parameter signal. -/
partial def fuseNode (e : Expr) (PT : Expr) (atoms : Array (Expr × (Expr → Expr))) : MetaM Fused := do
  let some (D, α, inh, f) := loopApp? e | throwError "fuse: not a loop"
  let .lam sn _ _ _ := f | throwError "fuse: the loop body is not a function"
  withLocalDeclD `π (sigT D PT) fun π => do
  -- the loop with its outside reads from the parameter
  let eπ := e.replace fun x =>
    match atoms.findIdx? (·.1 == x) with
    | some j => some ((atoms[j]!).2 π)
    | none => none
  let some (_, _, _, fπ) := loopApp? eπ | throwError "fuse: the substituted loop"
  let .lam _ _ bodyπ _ := fπ | throwError "fuse: the substituted body"
  withLocalDeclD sn (sigT D α) fun s => do
  let (children, bodyZ) ← childLoops (bodyπ.instantiate1 s)
  if children.isEmpty then
    -- a leaf: the loop itself
    let H ← withLocalDeclD `p (sigT D α) fun p => do
      mkLambdaFVars #[π, p] (bodyZ.replaceFVar s p)
    let eqTy ← mkEq eπ (mkApp4 (mkConst ``Sparkle.Core.Signal.Signal.loop) D α inh (H.beta #[π]))
    let eqPf ← mkLambdaFVars #[π] (← mkExpectedTypeHint (← mkEqRefl eπ) eqTy)
    -- guarded jointly: the body over the packed pair
    let guard ← withLocalDeclD `P (sigT D (prodT PT α)) fun P => do
      let bodyP := (H.beta #[fstS D PT α P, sndS D PT α P]).headBeta
      let g ← provGuarded D P bodyP
      pure (mkAppN (mkConst ``Tools.ShippingLoopFusion.Guarded2.of_pair) #[D, PT, α, α, H, g])
    return { α, Φ := α, H, guard, composite := false, eq := eqPf }
  -- the children: each over the packed (parameter, state, earlier children)
  let PTc := prodT PT α
  let mut res : Array Fused := #[]
  let mut Cpre : Array Expr := #[mkConst ``Unit]
  for j in [0:children.size] do
    let c := children[j]!
    let PTj := if j == 0 then PTc else prodT PTc Cpre[j]!
    let Cj := Cpre[j]!
    let toC (x : Expr) : Expr := if j == 0 then x else fstS D PTc Cj x
    let mut catoms : Array (Expr × (Expr → Expr)) :=
      #[(π, fun x => fstS D PT α (toC x)), (s, fun x => sndS D PT α (toC x))]
    for i in [0:j] do
      let ri := res[i]!
      let Cp := Cpre
      let rs := res
      catoms := catoms.push (children[i]!, fun x => projOf D ri (accessorIn D Cp rs i j (sndS D PTc Cj x)))
    let r ← fuseNode c PTj catoms
    res := res.push r
    Cpre := Cpre.push (if j == 0 then r.Φ else prodT Cj r.Φ)
  let k := children.size
  let C := Cpre[k]!
  let inhOf (ty : Expr) : MetaM Expr := do
    synthInstance (← mkAppM ``Inhabited #[ty])
  -- F π s q: the body with the children read from q
  let F ← withLocalDeclD `q (sigT D C) fun q => do
    let body := bodyZ.replace fun x =>
      match children.findIdx? (· == x) with
      | some i => some (projOf D res[i]! (accessorIn D Cpre res i k q))
      | none => none
    mkLambdaFVars #[π, s, q] body
  -- the chain of the children, over (parameter, state)
  let mut Ch := res[0]!.H
  let mut gCh := res[0]!.guard
  let mut chs : Array (Expr × Expr) := #[(Ch, gCh)]
  for m in [1:k] do
    let Cm := Cpre[m]!
    let rm := res[m]!
    let Hm := rm.H
    let ChPrev := Ch
    let Ch' ← withLocalDeclD `x (sigT D PTc) fun x => withLocalDeclD `q (sigT D (prodT Cm rm.Φ)) fun q => do
      mkLambdaFVars #[x, q] (pairS D Cm rm.Φ (ChPrev.beta #[x, fstS D Cm rm.Φ q])
        (Hm.beta #[pairS D PTc Cm x (fstS D Cm rm.Φ q), sndS D Cm rm.Φ q]))
    let G₂ ← withLocalDeclD `x (sigT D PTc) fun x => withLocalDeclD `y (sigT D Cm) fun y =>
      withLocalDeclD `z (sigT D rm.Φ) fun z => do
        mkLambdaFVars #[x, y, z] (Hm.beta #[pairS D PTc Cm x y, z])
    let unp := mkAppN (mkConst ``Tools.ShippingLoopFusion.Guarded2.unpack) #[D, PTc, Cm, rm.Φ, Hm, rm.guard]
    gCh := mkAppN (mkConst ``Tools.ShippingLoopFusion.chain_guarded) #[D, PTc, Cm, rm.Φ, ChPrev, G₂, gCh, unp]
    Ch := Ch'
    chs := chs.push (Ch, gCh)
  -- G π s q := Ch (π, s) q; guarded jointly
  let G ← withLocalDeclD `q (sigT D C) fun q => do
    mkLambdaFVars #[π, s, q] (Ch.beta #[pairS D PT α π s, q])
  let gG := mkAppN (mkConst ``Tools.ShippingLoopFusion.Guarded2.unpack) #[D, PT, α, C, Ch, gCh]
  -- F guarded jointly: its body over the packed triple
  let gF ← withLocalDeclD `P (sigT D (prodT PT (prodT α C))) fun P => do
    let bodyP := (F.beta #[fstS D PT (prodT α C) P, fstS D α C (sndS D PT (prodT α C) P),
      sndS D α C (sndS D PT (prodT α C) P)]).headBeta
    let g ← provGuarded D P bodyP
    pure (mkAppN (mkConst ``Tools.ShippingLoopFusion.Guarded3.of_pair) #[D, PT, α, C, α, F, g])
  -- the fused body
  let Φ := prodT α C
  let H ← withLocalDeclD `p (sigT D Φ) fun p => do
    mkLambdaFVars #[π, p] (mkAppN (mkConst ``Tools.ShippingLoopFusion.fuse)
      #[D, α, C, F.beta #[π], G.beta #[π], p])
  let guard := mkAppN (mkConst ``Tools.ShippingLoopFusion.fuse_guarded2) #[D, PT, α, C, F, G, gF, gG]
  -- the equation, at this parameter π: first at the state s
  let πc := pairS D PT α π s
  let mut Ts : Array Expr := #[]
  let mut CTs : Array Expr := #[]
  let mut eqCs : Array Expr := #[]
  for i in [0:k] do
    let ri := res[i]!
    let πa := if i == 0 then πc else pairS D PTc Cpre[i]! πc CTs[i-1]!
    let T := mkApp4 (mkConst ``Sparkle.Core.Signal.Signal.loop) D ri.Φ (← inhOf ri.Φ) (ri.H.beta #[πa])
    -- the child as written equals its fused projection at the actual parameter
    let ci := children[i]!
    let eqGen := mkApp ri.eq πa
    let atomsI : Array Expr := #[π, s] ++ (children.extract 0 i)
    let eqsI ← do
      let mut acc : Array Expr := #[← mkEqRefl π, ← mkEqRefl s]
      for l in [0:i] do acc := acc.push eqCs[l]!
      pure acc
    let hc ← congrSubst ci atomsI eqsI
    let eqC ← mkEqTrans hc eqGen
    let eqC ← mkExpectedTypeHint eqC (← mkEq ci (projOf D ri T))
    Ts := Ts.push T
    eqCs := eqCs.push eqC
    CTs := CTs.push (if i == 0 then T else pairS D Cpre[i]! ri.Φ CTs[i-1]! T)
  -- the children's tuple is the chain's loop (`loop_chain`, one child at a time)
  let mut eqChain ← mkExpectedTypeHint (← mkEqRefl Ts[0]!)
    (← mkEq Ts[0]! (mkApp4 (mkConst ``Sparkle.Core.Signal.Signal.loop) D (res[0]!).Φ
      (← inhOf (res[0]!).Φ) ((chs[0]!).1.beta #[πc])))
  for m in [1:k] do
    let Cm := Cpre[m]!
    let rm := res[m]!
    let (ChPrev, gPrev) := chs[m-1]!
    let loopPrev := mkApp4 (mkConst ``Sparkle.Core.Signal.Signal.loop) D Cm (← inhOf Cm) (ChPrev.beta #[πc])
    -- pairS CT T = pairS (loop prev) (loop (Hm (πc, loop prev)))
    let mot ← withLocalDeclD `X (sigT D Cm) fun X => do
      mkLambdaFVars #[X] (pairS D Cm rm.Φ X
        (mkApp4 (mkConst ``Sparkle.Core.Signal.Signal.loop) D rm.Φ (← inhOf rm.Φ)
          (rm.H.beta #[pairS D PTc Cm πc X])))
    let step1 ← mkCongrArg mot eqChain
    let G₂ ← withLocalDeclD `x (sigT D PTc) fun x => withLocalDeclD `y (sigT D Cm) fun y =>
      withLocalDeclD `z (sigT D rm.Φ) fun z => do
        mkLambdaFVars #[x, y, z] (rm.H.beta #[pairS D PTc Cm x y, z])
    let unp := mkAppN (mkConst ``Tools.ShippingLoopFusion.Guarded2.unpack) #[D, PTc, Cm, rm.Φ, rm.H, rm.guard]
    let step2 := mkAppN (mkConst ``Tools.ShippingLoopFusion.loop_chain)
      #[D, PTc, Cm, rm.Φ, ← inhOf Cm, ← inhOf rm.Φ, ChPrev, G₂, gPrev, unp, πc]
    let lhs := pairS D Cm rm.Φ CTs[m-1]! Ts[m]!
    let rhs := mkApp4 (mkConst ``Sparkle.Core.Signal.Signal.loop) D (prodT Cm rm.Φ)
      (← inhOf (prodT Cm rm.Φ)) ((chs[m]!).1.beta #[πc])
    eqChain ← mkExpectedTypeHint (← mkEqTrans step1 step2) (← mkEq lhs rhs)
  -- the body as written is F at the children's loops
  let hb ← congrSubst bodyZ children eqCs
  let FCT := F.beta #[π, s, CTs[k-1]!]
  let hb ← mkExpectedTypeHint hb (← mkEq bodyZ FCT)
  let loopG := mkApp4 (mkConst ``Sparkle.Core.Signal.Signal.loop) D C (← inhOf C) (G.beta #[π, s])
  let hF ← mkCongrArg (F.beta #[π, s]) eqChain
  let hF ← mkExpectedTypeHint hF (← mkEq FCT (F.beta #[π, s, loopG]))
  let eqBody ← mkEqTrans hb hF
  -- over every state: the loops agree
  let fun1 ← mkLambdaFVars #[s] bodyZ
  let fun2 ← mkLambdaFVars #[s] (F.beta #[π, s, loopG])
  let hfun ← mkAppM ``funext #[← mkLambdaFVars #[s] eqBody]
  let hfun ← mkExpectedTypeHint hfun (← mkEq fun1 fun2)
  let hloop ← mkCongrArg (mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.loop) D α inh) hfun
  let gFπ := mkAppN (mkConst ``Tools.ShippingLoopFusion.Guarded3.fix1) #[D, PT, α, C, α, F, gF, π]
  let gGπ := mkAppN (mkConst ``Tools.ShippingLoopFusion.Guarded3.fix1) #[D, PT, α, C, C, G, gG, π]
  let nest := mkAppN (mkConst ``Tools.ShippingLoopFusion.loop_nest)
    #[D, α, C, inh, ← inhOf C, F.beta #[π], G.beta #[π], gFπ, gGπ]
  let nest1 ← mkAppM ``And.left #[nest]
  let eqAll ← mkEqTrans hloop nest1
  let fused := mkApp4 (mkConst ``Sparkle.Core.Signal.Signal.loop) D Φ (← inhOf Φ) (H.beta #[π])
  let eqAll ← mkExpectedTypeHint eqAll (← mkEq eπ (fstS D α C fused))
  let eqPf ← mkLambdaFVars #[π] eqAll
  return { α, Φ, rest := C, H, guard, composite := true, eq := eqPf, kids := res }


/-! ## The fused value as the endpoint generator reads it -/

/-- `fstS (pairS a b)` is `a`, `sndS (pairS a b)` is `b` (by evaluation), and
beta: the fused body's accessors reduced. -/
def normAcc (e : Expr) (beta : Bool := true) : MetaM Expr := do
  -- (cached: the values are DAGs with much sharing; a plain recursion copies
  -- every shared subterm)
  let step (e : Expr) : MetaM TransformStep := do
    if beta && e.isApp && e.getAppFn.isLambda then return .visit e.headBeta
    if e.isAppOfArity ``Tools.ShippingLoopFusion.fstS 4 then
      let p := e.getAppArgs[3]!
      if p.isAppOfArity ``Tools.ShippingLoopFusion.pairS 5 then return .done p.getAppArgs[3]!
    if e.isAppOfArity ``Tools.ShippingLoopFusion.sndS 4 then
      let p := e.getAppArgs[3]!
      if p.isAppOfArity ``Tools.ShippingLoopFusion.pairS 5 then return .done p.getAppArgs[4]!
    return .done e
  withTheReader Core.Context (fun c => { c with maxRecDepth := 1000000 }) do
    Core.transform e (post := step)

/-- The fused body as a tree of `pairS`, its leaves the loops' register trees:
`fuse` unfolded along the spine. -/
partial def spine (e : Expr) : Expr :=
  let e := e.headBeta
  if e.isAppOfArity ``Tools.ShippingLoopFusion.fuse 6 then
    let a := e.getAppArgs
    let (D, α, β, F, G, p) := (a[0]!, a[1]!, a[2]!, a[3]!, a[4]!, a[5]!)
    pairS D α β (spine (F.beta #[fstS D α β p, sndS D α β p])) (spine (G.beta #[fstS D α β p, sndS D α β p]))
  else if e.isAppOfArity ``Tools.ShippingLoopFusion.pairS 5 then
    let a := e.getAppArgs
    pairS a[0]! a[1]! a[2]! (spine a[3]!) (spine a[4]!)
  else e

/-- The loop of `raw` (its `let`s kept) whose zeta-reduction is `target`:
the reader's view of a loop, dead `let`s included (the compiler still reads
their calls; zeta-reduction drops them). A loop bound by a `let` of `raw`
directly is found without reducing anything else. -/
partial def rawOf (raw target : Expr) : MetaM (Option Expr) := do
  if (loopApp? raw).isSome then
    return if (← zetaReduce raw) == target then some raw else none
  match raw with
  | .letE _ _ v b _ =>
    if let some r ← rawOf v target then return some r
    if !b.hasLooseBVar 0 then return ← rawOf b target
    rawOf (b.instantiate1 (← zetaReduce v)) target
  | .mdata _ b => rawOf b target
  | .app .. =>
    for a in raw.getAppArgs do
      if (a.find? fun x => (loopApp? x).isSome).isSome then
        if let some r ← rawOf a target then return some r
    return none
  | _ => return none

/-- The let values and tails of the nested loops, in the reader's order, with
every loop state read from the fused state `L` — what the reader's calls are
read off (the calls of the fused body, ordered as the compiler read them). -/
partial def readerOrder (D : Expr) (root : Fused) (rootLoop : Expr) (L : Expr) : MetaM (Array Expr) := do
  go rootLoop root L #[]
where
  /-- `known`: the loops already read (the enclosing loops' earlier
  children, which a later sibling's body may read), with their accessors. -/
  go (e : Expr) (r : Fused) (fusedAcc : Expr) (known : Array (Expr × Expr)) : MetaM (Array Expr) := do
    let rd (x : Expr) : Expr := x.replace fun y =>
      match known.findIdx? (·.1 == y) with
      | some j => some (known[j]!).2
      | none => none
    let some (_, _, _, f) := loopApp? e | throwError "fuse: not a loop"
    let .lam _ _ body _ := rd f | throwError "fuse: loop body"
    let own := projOf D r fusedAcc
    let b := body.instantiate1 own
    -- the children, in the order they were fused (the zeta-reduced body's)
    let (children, _) ← childLoops (← zetaReduce b)
    unless children.size == r.kids.size do
      throwError "fuse: {children.size} inner loops read, {r.kids.size} fused"
    let kidAcc (j : Nat) : Expr :=
      let Cpre := (r.kids.size + 1 |> List.range).map fun m =>
        if m == 0 then mkConst ``Unit else
        ((List.range m).drop 1).foldl (fun acc l => prodT acc (r.kids[l]!).Φ) (r.kids[0]!).Φ
      accessorIn D Cpre.toArray r.kids j r.kids.size (sndS D r.α r.rest fusedAcc)
    let mine : Array (Expr × Expr) :=
      (List.range children.size).toArray.map fun j => (children[j]!, projOf D r.kids[j]! (kidAcc j))
    let subst (x : Expr) : Expr := x.replace fun y =>
      match mine.findIdx? (·.1 == y) with
      | some j => some (mine[j]!).2
      | none => none
    -- the let values in order (the earlier ones substituted), a child's own
    -- order at its place
    let mut out : Array Expr := #[]
    let mut walked : Array Nat := #[]
    let mut cur := b
    for _ in [0:100000] do
      let (v?, next?) ← match cur with
        | .letE _ _ v rest _ => do
          let vZ ← zetaReduce v
          pure (some (v, vZ), some (rest.instantiate1 vZ))
        | .mdata _ x => pure (none, some x)
        | t => do pure (some (t, ← zetaReduce t), none)
      if let some (vRaw, v) := v? then
        -- the children read inside this value first, then the value's own calls
        for j in [0:children.size] do
          if !walked.contains j && (v.find? (· == children[j]!)).isSome then
            walked := walked.push j
            -- (its `let`s kept: a dead one's calls are read too)
            let cRaw := (← rawOf vRaw children[j]!).getD children[j]!
            out := out ++ (← go cRaw r.kids[j]! (kidAcc j) (known ++ mine))
        if (children.findIdx? (· == v)).isNone then
          -- (no beta: a dead argument's calls are read, as the compiler does)
          out := out.push (← normAcc (subst v) (beta := false))
      match next? with
      | some n => cur := n
      | none => break
    return out

/-- The instance value with its root loop fused: `let p := loop H'; v[root ↦
proj p]` (`H'` the explicit tree of registers), the equation `v = that`, and,
over a fused state signal, the reader-order expression of its calls. `none`
when the value has no loop holding loops. -/
def fuseInst (v : Expr) : MetaM (Option (Expr × Expr × (Expr → MetaM Expr))) := do
  let (tops, vZ) ← childLoops v
  unless tops.size == 1 do return none
  let root := tops[0]!
  let some (D, _, _, f) := loopApp? root | return none
  let .lam _ _ body _ := f | return none
  let (inner, _) ← withLocalDeclD `s (← inferType root) fun s => childLoops (body.instantiate1 s)
  if inner.isEmpty then return none
  let r ← fuseNode root (mkConst ``Unit) #[]
  let u := mkApp3 (mkConst ``Sparkle.Core.Signal.Signal.pure [.zero]) D (mkConst ``Unit) (mkConst ``Unit.unit)
  let inhΦ ← synthInstance (← mkAppM ``Inhabited #[r.Φ])
  -- the explicit fused body
  let H' ← withLocalDeclD `p (sigT D r.Φ) fun p => do
    mkLambdaFVars #[p] (← normAcc (spine (r.H.beta #[u, p])))
  let loopF := mkApp4 (mkConst ``Sparkle.Core.Signal.Signal.loop) D r.Φ inhΦ H'
  let eqRoot ← mkExpectedTypeHint (mkApp r.eq u) (← mkEq root (projOf D r loopF))
  -- the value with the root loop read from the fused loop
  let v' ← withLetDecl `fusedState (sigT D r.Φ) loopF fun p => do
    mkLetFVars #[p] (vZ.replace fun x => if x == root then some (projOf D r p) else none)
  let hv ← congrSubst vZ #[root] #[eqRoot]
  let hv ← mkExpectedTypeHint hv (← mkEq v v')
  let order := fun (L : Expr) => do
    let rootRaw := (← rawOf v root).getD root
    let items ← readerOrder D r rootRaw L
    pure (mkAppN (mkConst ``Unit.unit) items)
  return some (v', hv, order)

end Tools.ShippingMachineFuseGen
