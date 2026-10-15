import Tools.ShippingReaderFuelOldEq
import Tools.ShippingSparseCasesTac

/-! # The old source equations VERBATIM (inline matches, local `let rec`s)

STATUS: round 3 (worker A, branch `par/r-10`, from poc fc697219) WRITTEN, NOT
BUILT. Round 2's text (`par/r-6`) did not build on poc fc697219 (the
integrator's run, after moving two `set_option … in` before their
docstrings); round 3 changes PROOFS ONLY, every statement and every verbatim
definition is unchanged:

* `regMatch_view` / `ashrMatch_view` (round 2: `simp_all` hit the maximum
  recursion depth): no `simp_all`. The array is split into its list first;
  the leaf where every name component and the size match is stuck on the
  array-literal cast while the list is abstract, so it is closed after
  splitting the list (length 4: `rfl`, the cast reduces; other lengths: the
  size hypothesis is contradictory);
* `.bvar` arm of `oConvV_eq` (round 2: `rfl` failed): the lifted local
  `let rec bundle` (`oConvV.bundle`) is proved equal to `bundleSlots` by
  recursion on the lists (`bundleV_eq`, `bundleV_fun`), rewritten, then `rfl`;
* `oInstSV_eq`: the same for the lifted `let rec inst` (`instV_eq`,
  `instV_fun`, recursion on the argument list generalising the type);
* `oInstV_eq` (round 2: not a definitional equality): `let st ← match res …`
  is a nested `do` action (join point per arm) while the refactored text binds
  `instEntry res st`; equal per constructor of `res` (`cases res`);
* `oLoopRootV_eq` (round 2: `rfl` after `split` failed): case on `loopView? e`
  first, then the verbatim pattern-`let` and the unfolded view in the
  hypothesis are split on the same discriminant `inlSpine e []`; the two
  pattern equations agree (`cases`), the mixed branches contradict. No string
  literal is evaluated.

No `sorry`, no axiom, no `native_decide`. The agreements here are CONDITIONAL
on `OldEqV` / `OldEqNV` (a tuple satisfying the verbatim source equations).
The riskiest file of the unit: it is separate so that a failure here takes
nothing else with it.

`Tools/ShippingReaderFuelOldEq.lean` (BUILT on poc fc697219) states the old
source equations with the refactorings listed there. This file states them as
the source text (`Sparkle/Compiler/Elab.lean` at `c1c651a0`, recursive calls
through the tuple) and proves every solution of the verbatim equations is a
solution of those (`oldEq_of_oldEqV`, `oldEqN_of_oldEqNV`).

Final: `readF_agree_verbatim` / `machNormF_agree_verbatim` — agreement of the
fuel candidate with every solution of the VERBATIM old source equations. Still
conditional: `OldEqV` is never assumed of the compiled `partial` constants
(outside the kernel). -/
namespace Tools.ShippingReaderFuel
open Lean
open Sparkle.Compiler.Elab
open Tools.ShippingSparseCasesTac

/-! ## The two inline matches, as views -/

set_option maxHeartbeats 16000000 in
/-- The inline `Signal.register` match of `machConv` (3913) is `regView?`. -/
theorem regMatch_view {β : Sort u} (fn : Lean.Expr) (args : Array Lean.Expr)
    (A : Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → β) (B : β) :
    (match fn, args with
     | .const ``Sparkle.Core.Signal.Signal.register _, #[dom, α, init, x] => A dom α init x
     | _, _ => B) =
    (match regView? fn args with
     | some (dom, α, init, x) => A dom α init x
     | none => B) := by
  unfold regView?
  rcases args with ⟨L⟩
  cases fn with
  | const n us =>
    rcases n with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (try unfold_matchers_aux)
    all_goals (try dsimp_sparse_aux)
    all_goals (repeat' split)
    -- no `simp_all` (round 2: maximum recursion depth). The leaf where every
    -- component string and the size match is stuck on the array-literal cast
    -- (`Array.toArrayLit_eq`) while the list is abstract: split the list, the
    -- cast reduces (K) at length 4, the other lengths contradict the size
    all_goals first
      | rfl
      | (subst_vars; rfl)
      | (exfalso; contradiction)
      | (rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, L'⟩⟩⟩⟩⟩ <;>
          first
            | rfl
            | (subst_vars; rfl)
            | (exfalso; contradiction)
            | (exfalso; simp at *; done)
            | (exfalso; simp at *; omega))
  | _ => rfl

set_option maxHeartbeats 16000000 in
/-- The inline `Signal.ashr` match of `machNorm` (4961) is `ashrView?`. -/
theorem ashrMatch_view {β : Sort u} (fn : Lean.Expr) (args : Array Lean.Expr)
    (A : Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → β) (B : β) :
    (match fn, args with
     | .const ``Sparkle.Core.Signal.Signal.ashr _, #[dom, nE, x, y] => A dom nE x y
     | _, _ => B) =
    (match ashrView? fn args with
     | some (dom, nE, x, y) => A dom nE x y
     | none => B) := by
  unfold ashrView?
  rcases args with ⟨L⟩
  cases fn with
  | const n us =>
    rcases n with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨p5, s5⟩ | ⟨p5, i5⟩, s4⟩ | ⟨p4, i4⟩, s3⟩ |
      ⟨p3, i3⟩, s2⟩ | ⟨p2, i2⟩, s1⟩ | ⟨p1, i1⟩, s0⟩ | ⟨p0, i0⟩
    all_goals (try unfold_matchers_aux)
    all_goals (try dsimp_sparse_aux)
    all_goals (repeat' split)
    -- no `simp_all` (round 2: maximum recursion depth). The leaf where every
    -- component string and the size match is stuck on the array-literal cast
    -- (`Array.toArrayLit_eq`) while the list is abstract: split the list, the
    -- cast reduces (K) at length 4, the other lengths contradict the size
    all_goals first
      | rfl
      | (subst_vars; rfl)
      | (exfalso; contradiction)
      | (rcases L with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, L'⟩⟩⟩⟩⟩ <;>
          first
            | rfl
            | (subst_vars; rfl)
            | (exfalso; contradiction)
            | (exfalso; simp at *; done)
            | (exfalso; simp at *; omega))
  | _ => rfl

/-! ## The verbatim texts -/

/-- `machConv` (3884–4010), VERBATIM (recursive calls through `G`). -/
def oConvV (senv : StructEnv) (G : OldFns) : List MachVal → Nat → Lean.Expr → MachRead →
    Option (Lean.Expr × MachRead)
  | env, d, .bvar j, st =>
    if j < d then some (.bvar j, st) else
    match env[j - d]? with
    | some (.val v) => some (v, st)
    | some (.state b 1) => some (machSlot b, st)
    -- a whole loop state of several slots: the bundle of its slots (equal to
    -- the state signal by structure eta)
    | some (.state b n) => do
      let dom ← st.dom
      let tyOf (k : MixedGateBinder) : Option Lean.Expr := match k with
        | .bits w => some (mkApp (.const ``BitVec []) (inlNatLit w))
        | .bool => some (.const ``Bool [])
        | .domain => none
      let tys ← ((List.range n).map (b + ·)).mapM fun i => st.kinds[i]? >>= tyOf
      let rec bundle : List Nat → List Lean.Expr → Option (Lean.Expr × Lean.Expr)
        | [i], [t] => some (machSlot i, t)
        | i :: is, t :: ts => do
          let (rest, restT) ← bundle is ts
          some (mkApp5 (.const ``Sparkle.Core.Signal.bundle2 [.zero]) dom t restT (machSlot i) rest,
            mkApp2 (.const ``Prod [.zero, .zero]) t restT)
        | _, _ => none
      let (e, _) ← bundle ((List.range n).map (b + ·)) tys
      some (e, st)
    | some _ => none
    | none => some (machIn (j - d - env.length), st)
  | env, d, e@(.app f a), st =>
    -- a bare register (no loop, no `circuit do` in the declaration): a slot
    -- whose next value is its input
    match e.getAppFn, e.getAppArgs with
    | .const ``Sparkle.Core.Signal.Signal.register _, #[dom, α, init, x] =>
      if d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty then none else do
      match st.bareRegs.find? (·.1 == e) with
      | some (_, k) => some (machSlot k, st)
      | none =>
      let kind ← machSlotKind? α
      let initN ← machInit? senv.natOf kind init
      let (dom', st) ← G.conv env 0 dom st
      match st.dom with
      | some d0 => if d0 != dom' then none else pure ()
      | none => pure ()
      let base := st.kinds.size
      let st := { st with
        kinds := st.kinds.push kind, inits := st.inits.push initN
        names := st.names.push (Name.mkSimple s!"reg{base}"), dom := some dom'
        bareRegs := st.bareRegs.push (e, base) }
      let (x', st) ← G.conv env 0 x st
      some (machSlot base, { st with ws := st.ws.push (base, x') })
    | _, _ =>
    match machLoopRead? env d (.app f a) with
    | some i => if i < st.kinds.size then some (machSlot i, st) else none
    | none =>
    match machRunApp? (.app f a) with
    | some (dom, αs, initsE, body) =>
      if d != 0 then none else G.nested env dom αs initsE body st
    | none =>
    match machInstCall? senv (.app f a) with
    | some (c, kinds, res, args) =>
      if d != 0 then none else G.inst env c kinds res args st
    | none =>
    match machInstCallS? senv (.app f a) with
    | some (c, kinds, ty, args) =>
      if d != 0 then none else G.instS env c kinds ty args st
    | none =>
    -- a memory: a call of a memory-only child (`MachMemory`)
    match Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e)
        (.app f a) with
    | some (combo, aw, dw, dom, ops) =>
      if d != 0 then none else do
        let (v, st) ← G.inst env (Sparkle.Compiler.MachMemory.memChildName combo aw dw)
          [.domain, .bits aw, .bits dw, .bool, .bits aw] (.bits dw) (dom :: ops) st
        some (v, { st with instStruct := true })
    | none =>
    match machReadV env d (.app f a) with
    | some i => if i < st.kinds.size then some (machSlot i, st) else none
    | none =>
      match G.conv env d f st with
      | some (f', st) =>
        match G.conv env d a st with
        | some (a', st) =>
          some (Sparkle.Compiler.MachRawSurface.bundleIota
            (machProjIota senv.proj (.app f' a')), st)
        | none => none
      | none => none
  | env, d, .lam nm t b bi, st =>
    match G.conv env d t st with
    | some (t', st) =>
      match G.conv env (d + 1) b st with
      | some (b', st) => some (.lam nm t' b' bi, st)
      | none => none
    | none => none
  | env, d, .forallE nm t b bi, st =>
    match G.conv env d t st with
    | some (t', st) =>
      match G.conv env (d + 1) b st with
      | some (b', st) => some (.forallE nm t' b' bi, st)
      | none => none
    | none => none
  | env, d, .letE nm ty v b nd, st =>
    if d != 0 then none else
    -- a `let` block in the value: its `let`s first
    match Sparkle.Compiler.MachRawSurface.rootFloat v with
    | .letE n2 t2 v2 w nd2 =>
      G.conv env 0
        (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) st
    | v =>
    -- a hand-written loop: a sub-machine of its own
    if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
      match G.loopRoot env v st with
      | some (mv, st) => G.conv (mv :: env) 0 b st
      | none => none
    else
    match machTailV env 0 v with
    | some p => G.conv (.regs p :: env) 0 b st
    | none =>
      match machHandleV env 0 v with
      | some i => G.conv (.handle i :: env) 0 b st
      | none =>
        match G.conv env 0 v st with
        | some (v', st) =>
          let (x, lets) := machBindLet nm ty v' st.lets
          G.conv (.val x :: env) 0 b { st with lets := lets }
        | none => none
  | _, _, .mdata .., _ => none
  | _, _, .proj .., _ => none
  | _, _, e, st => some (e, st)

/-- The lifted local `let rec bundle` of `oConvV` is `bundleSlots` (round 2's
`rfl` on the `.bvar` arm failed: the two lifted recursive functions are not
compared definitionally; here by recursion on the lists). -/
theorem bundleV_eq (dom : Lean.Expr) :
    ∀ (is : List Nat) (ts : List Lean.Expr), oConvV.bundle dom is ts = bundleSlots dom is ts
  | [], _ => by
    first | rfl | (unfold oConvV.bundle bundleSlots; rfl) | simp [oConvV.bundle, bundleSlots]
  | [_], [] => by
    first | rfl | (unfold oConvV.bundle bundleSlots; rfl) | simp [oConvV.bundle, bundleSlots]
  | [_], [_] => by
    first | rfl | (unfold oConvV.bundle bundleSlots; rfl) | simp [oConvV.bundle, bundleSlots]
  | [_], _ :: _ :: _ => by
    first | rfl | (unfold oConvV.bundle bundleSlots; rfl) | simp [oConvV.bundle, bundleSlots]
  | _ :: _ :: _, [] => by
    first | rfl | (unfold oConvV.bundle bundleSlots; rfl) | simp [oConvV.bundle, bundleSlots]
  | _ :: _ :: _, [_] => by
    first | rfl | (unfold oConvV.bundle bundleSlots; rfl) | simp [oConvV.bundle, bundleSlots]
  | i :: j :: is, t :: u :: ts => by
    have ih := bundleV_eq dom (j :: is) (u :: ts)
    have h2 := congrArg (fun r : Option (Lean.Expr × Lean.Expr) => (do
        let (rest, restT) ← r
        some (mkApp5 (.const ``Sparkle.Core.Signal.bundle2 [.zero]) dom t restT (machSlot i) rest,
          mkApp2 (.const ``Prod [.zero, .zero]) t restT) : Option (Lean.Expr × Lean.Expr))) ih
    first
      | exact h2
      | (unfold oConvV.bundle bundleSlots; simp only [ih])
      | (simp only [oConvV.bundle, bundleSlots, ih])
      | (rw [oConvV.bundle, bundleSlots, ih])

theorem bundleV_fun : oConvV.bundle = bundleSlots :=
  funext fun dom => funext fun is => funext fun ts => bundleV_eq dom is ts

/-- `machNested` (4016–4037), VERBATIM. -/
def oNestedV (senv : StructEnv) (G : OldFns) (env : List MachVal) (dom αs initsE body : Lean.Expr)
    (st : MachRead) : Option (Lean.Expr × MachRead) := do
  if st.inInner then none else
  let (dom', st) ← G.conv env 0 dom st
  let shared := st.nested.findSome? fun (base, d, a, ini, ws, v) =>
    if d == dom' && a == αs && ini == initsE then
      match G.chain (.regs base :: env) body st with
      | some (ws', v', st') => if ws' == ws && v' == v then some (v, st') else none
      | none => none
    else none
  match shared with
  | some r => some r
  | none =>
    let (base, st) ← machReserve senv.natOf dom' αs initsE body st
    let outer := st.inInner
    let (ws, v, st) ← G.chain (.regs base :: env) body { st with inInner := true }
    some (v, { st with ws := st.ws ++ ws.toArray, inInner := outer,
                       nested := st.nested.push (base, dom', αs, initsE, ws, v) })

/-- `machInstance` (4045–4069), VERBATIM. -/
def oInstV (G : OldFns) (env : List MachVal) (c : Name) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) :
    Option (Lean.Expr × MachRead) := do
  let st ← match res with
    | .bits _ => pure st
    | .bool => pure { st with instStruct := true }
    | _ => none
  let k := st.insts.size
  let (js, st) ← (kinds.zip args).foldlM (init := (([] : List Nat), st))
    fun (js, st) (kind, arg) => do
      let (v', st) ← G.conv env 0 arg st
      match kind with
      | .domain =>
        match st.dom with
        | some d => if d != v' then none else some (js, st)
        | none => some (js, { st with dom := some v' })
      | _ =>
        let (j, lets) := machLetIndex (Name.mkSimple s!"inst{k}_arg{js.length}") kind v' st.lets
        some (js ++ [j], { st with lets := lets })
  match st.insts.findIdx? (fun i => i.1 == c && i.2.1 == js) with
  | some k' => some (machInstOut k', st)
  | none => some (machInstOut k, { st with insts := st.insts.push (c, js, res),
                                           instFields := st.instFields.push "out" })

/-- `machInstanceS` (4079–4117), VERBATIM. -/
def oInstSV (senv : StructEnv) (G : OldFns) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead) :
    Option (Lean.Expr × MachRead) := do
  if st.inInner then none else
  let rec inst : Lean.Expr → List Lean.Expr → Option Lean.Expr
    | e, [] => some e
    | .forallE _ _ b _, a :: as => inst (b.instantiate1 a) as
    | _, _ => none
  let resTy ← inst ty args
  let (some ctor, fields) ← machOuts? senv resTy | none
  if fields.isEmpty || fields.any (fun f => f.2 == .domain) then none else
  let (js, st) ← (kinds.zip args).foldlM (init := (([] : List Nat), st))
    fun (js, st) (kind, arg) => do
      let (v', st) ← G.conv env 0 arg st
      match kind with
      | .domain =>
        match st.dom with
        | some d => if d != v' then none else some (js, st)
        | none => some (js, { st with dom := some v' })
      | _ =>
        let (j, lets) := machLetIndex (Name.mkSimple s!"inst{st.insts.size}_arg{js.length}")
          kind v' st.lets
        some (js ++ [j], { st with lets := lets })
  let (params, st) ← resTy.getAppArgs.toList.foldlM (init := (([] : List Lean.Expr), st))
    fun (ps, st) p => do
      let (p', st) ← G.conv env 0 p st
      some (ps ++ [p'], st)
  let lvls := resTy.getAppFn.constLevels!
  let (k0, st) := match st.insts.findIdx? (fun i => i.1 == c && i.2.1 == js) with
    | some k0 => (k0, st)
    | none =>
      (st.insts.size, { st with
        insts := st.insts ++ (fields.map fun f => (c, js, f.2)).toArray
        instFields := st.instFields ++ (fields.map (·.1)).toArray
        instStruct := true })
  some (mkAppN (.const ctor lvls)
    (params.toArray ++ ((List.range fields.length).map fun i => machInstOut (k0 + i)).toArray), st)

/-- The lifted local `let rec inst` of `oInstSV` is `instRes` (by recursion on
the argument list, generalising the type). -/
theorem instV_eq : ∀ (args : List Lean.Expr) (e : Lean.Expr), oInstSV.inst e args = instRes e args
  | [], e => by
    first
      | rfl
      | (cases e <;> rfl)
      | (unfold oInstSV.inst instRes; rfl)
      | (cases e <;> (unfold oInstSV.inst instRes; rfl))
  | a :: as, e => by
    have ih := instV_eq as
    cases e with
    | forallE n t b bi =>
      first
        | exact ih (b.instantiate1 a)
        | (unfold oInstSV.inst instRes; exact ih (b.instantiate1 a))
        | (simp only [oInstSV.inst, instRes]; exact ih (b.instantiate1 a))
        | (rw [oInstSV.inst, instRes]; exact ih (b.instantiate1 a))
    | _ =>
      first
        | rfl
        | (unfold oInstSV.inst instRes; rfl)
        | simp [oInstSV.inst, instRes]

theorem instV_fun : oInstSV.inst = instRes :=
  funext fun e => funext fun args => instV_eq args e

/-- `machLoopBody` (4171–4185), VERBATIM. -/
def oLoopBodyV (G : OldFns) (base : Nat) :
    List MachVal → Lean.Expr → MachRead → Option MachRead
  | env, .letE nm ty v b _, st => do
    let (v', st) ← G.conv env 0 v st
    let (x, lets) := if machIsSlot v' then machBindLetNamed nm ty v' st.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets
      else machBindLet nm ty v' st.lets
    G.loopBody base (.val x :: env) b { st with lets := lets }
  | env, tail, st => do
    let regs ← machLoopRegs tail
    let (ws, st) ← regs.foldlM (init := (([] : List (Nat × Lean.Expr)), st))
      fun (ws, st) (_, _, nx) => do
        let (nx', st) ← G.conv env 0 nx st
        pure (ws ++ [(base + ws.length, nx')], st)
    some { st with ws := st.ws ++ ws.toArray }

/-- `machLoopRoot` (4193–4230), VERBATIM. -/
def oLoopRootV (senv : StructEnv) (G : OldFns) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) : Option (MachVal × MachRead) := do
  let (.const ``Sparkle.Core.Signal.Signal.loop _, [dom, _, _, .lam _ _ body _]) := inlSpine e []
    | none
  if st.inInner then none else
  let regs ← machLoopRegs (machLetTail body)
  if regs.any (fun (ty, init, _) => ty.hasLooseBVars || init.hasLooseBVars) then none else
  let kinds ← regs.mapM fun (ty, _, _) => machSlotKind? ty
  let inits ← (kinds.zip regs).mapM fun (k, (_, init, _)) => machInit? senv.natOf k init
  let (dom', st) ← G.conv env 0 dom st
  match st.dom with
  | some d0 => if d0 != dom' then none else pure ()
  | none => pure ()
  let n := kinds.length
  let shared := st.loopWs.findSome? fun (b0, n0, ws0) =>
    if n0 != n then none else
    match G.loopBody b0 (.state b0 n :: env) body { st with ws := #[] } with
    | some st' => if st'.ws.toList == ws0 then some (b0, { st' with ws := st.ws }) else none
    | none => none
  match shared with
  | some (b0, st') => some (.state b0 n, st')
  | none =>
  let base := st.kinds.size
  let depth := st.loopDepth
  let st := { st with
    kinds := st.kinds ++ kinds.toArray
    inits := st.inits ++ inits.toArray
    names := st.names ++ ((List.range n).map fun i =>
      Name.mkSimple s!"loop{st.loops.size}_r{i}").toArray
    dom := some dom'
    loops := st.loops.push (base, n)
    nestedLoops := if depth ≥ 1 then st.nestedLoops + 1 else st.nestedLoops
    loopDepth := depth + 1 }
  let before := st.ws.size
  let st ← G.loopBody base (.state base n :: env) body st
  some (.state base n,
    { st with loopWs := st.loopWs.push (base, n, (st.ws.toList.drop before)), loopDepth := depth })

/-- **The old source equations of the block, VERBATIM** (`machChain`'s text
needs no refactoring: `oChain` is verbatim). -/
def OldEqV (senv : StructEnv) (G : OldFns) : Prop :=
  (∀ env d e st, G.conv env d e st = oConvV senv G env d e st) ∧
  (∀ env dom αs initsE body st,
    G.nested env dom αs initsE body st = oNestedV senv G env dom αs initsE body st) ∧
  (∀ env c kinds res args st, G.inst env c kinds res args st = oInstV G env c kinds res args st) ∧
  (∀ env c kinds ty args st,
    G.instS env c kinds ty args st = oInstSV senv G env c kinds ty args st) ∧
  (∀ env e st, G.chain env e st = oChain G env e st) ∧
  (∀ base env e st, G.loopBody base env e st = oLoopBodyV G base env e st) ∧
  (∀ env e st, G.loopRoot env e st = oLoopRootV senv G env e st)

/-! ## Verbatim = refactored -/

section Eqs
variable (senv : StructEnv) (G : OldFns)

theorem oConvV_eq (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead) :
    oConvV senv G env d e st = oConv senv G env d e st := by
  cases e with
  | app f a =>
    first
      | simp only [oConvV, oConv]
      | (unfold oConvV oConv; dsimp only)
    rw [regMatch_view]
    all_goals rfl
  | bvar j =>
    -- the lifted `let rec bundle` replaced by `bundleSlots` (`bundleV_fun`),
    -- then the two `.bvar` arms are the same text
    first
      | rfl
      | ((delta oConvV; rw [bundleV_fun]) <;> rfl)
      | ((unfold oConvV; rw [bundleV_fun]) <;> rfl)
      | ((simp only [oConvV]; rw [bundleV_fun]) <;> rfl)
      | (simp only [oConvV, oConv, convBvar, bundleV_fun]; done)
  | _ => rfl

theorem oNestedV_eq (env : List MachVal) (dom αs initsE body : Lean.Expr) (st : MachRead) :
    oNestedV senv G env dom αs initsE body st = oNested senv G env dom αs initsE body st := rfl

theorem oInstV_eq (env : List MachVal) (c : Name) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) :
    oInstV G env c kinds res args st = oInst G env c kinds res args st := by
  -- `let st ← match res with …` is a nested `do` action (a join point taken in
  -- each arm), `instEntry res st` a bind of a function: equal per constructor
  cases res <;> first
    | rfl
    | (unfold oInstV oInst instEntry; rfl)
    | (simp only [oInstV, oInst, instEntry]; done)

theorem oInstSV_eq (env : List MachVal) (c : Name) (kinds : List MixedGateBinder)
    (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead) :
    oInstSV senv G env c kinds ty args st = oInstS senv G env c kinds ty args st := by
  -- the lifted `let rec inst` replaced by `instRes` (`instV_fun`)
  first
    | ((unfold oInstSV; rw [instV_fun]) <;> rfl)
    | ((delta oInstSV; rw [instV_fun]) <;> rfl)
    | ((simp only [oInstSV]; rw [instV_fun]) <;> rfl)
    | (simp only [oInstSV, oInstS, instV_fun]; done)

theorem oLoopBodyV_eq (base : Nat) (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    oLoopBodyV G base env e st = oLoopBody G base env e st := by
  cases e <;> rfl

/-- The pattern-`let` of `machLoopRoot` is `loopView?` (a `match` on the same
discriminant). Aligned on the discriminant: case on `loopView? e` first (the
refactored text reduces), then split the verbatim pattern-`let` and the
unfolded view in the hypothesis — both on `inlSpine e []`; the two pattern
equations agree (`cases`), the mixed branches contradict. No string literal is
ever evaluated. -/
theorem oLoopRootV_eq (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    oLoopRootV senv G env e st = oLoopRoot senv G env e st := by
  cases hv : loopView? e with
  | none =>
    unfold oLoopRoot
    rw [hv]
    unfold oLoopRootV
    unfold loopView? at hv
    split
    · rename_i heq
      split at hv
      · cases hv
      · exfalso; solve_by_elim
    · rfl
  | some p =>
    obtain ⟨dom, body⟩ := p
    unfold oLoopRoot
    rw [hv]
    unfold oLoopRootV
    unfold loopView? at hv
    split
    · rename_i heq
      split at hv
      · rename_i heq2
        rw [heq] at heq2
        cases heq2
        cases hv
        rfl
      · cases hv
    · split at hv
      · exfalso; solve_by_elim
      · cases hv

end Eqs

theorem oldEq_of_oldEqV {senv : StructEnv} {G : OldFns} (h : OldEqV senv G) : OldEq senv G := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨fun env d e st => (h1 env d e st).trans (oConvV_eq senv G env d e st),
    fun env dom αs initsE body st =>
      (h2 env dom αs initsE body st).trans (oNestedV_eq senv G env dom αs initsE body st),
    fun env c kinds res args st =>
      (h3 env c kinds res args st).trans (oInstV_eq G env c kinds res args st),
    fun env c kinds ty args st =>
      (h4 env c kinds ty args st).trans (oInstSV_eq senv G env c kinds ty args st),
    h5,
    fun base env e st => (h6 base env e st).trans (oLoopBodyV_eq G base env e st),
    fun env e st => (h7 env e st).trans (oLoopRootV_eq senv G env e st)⟩

/-- **Agreement with the VERBATIM old source equations** (block). -/
theorem readF_agree_verbatim {senv : StructEnv} {G : OldFns} (h : OldEqV senv G) {n : Nat}
    {c : Call} {r : RB c} (hr : readF senv n c = some r) : G.app c = r :=
  readF_agree_old (oldEq_of_oldEqV h) hr

/-! ## `machNorm` -/

/-- `machNorm` (4957–4986), VERBATIM (the recursive call `g`). -/
def oNormV (senv : StructEnv) (g : Lean.Expr → Lean.Expr) : Lean.Expr → Lean.Expr
  | e@(.app f a) =>
    -- `Signal.ashr a b`: its derived form (`MachSignOps`, `ShippingSignOps.ashr_eq`)
    match e.getAppFn, e.getAppArgs with
    | .const ``Sparkle.Core.Signal.Signal.ashr _, #[dom, nE, x, y] =>
      match canonicalNatLitValue? nE with
      | some n =>
        if n == 0 then e else
        Sparkle.Compiler.MachSignOps.ashrE inlNatLit
          (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b)
          dom n (g x) (g y)
      | none => e
    | _, _ =>
    -- the raw `runCircuitH` surface first (`MachRawSurface`)
    match Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch e with
    | some e' => g e'
    | none => machNormNode senv (.app (g f) (g a))
  | .lam n t b bi => .lam n t (g b) bi
  | .letE n t v b nd =>
    if t.isConstOf ``Nat then g (b.instantiate1 v)
    else if (machBits? t).isSome && !v.hasLooseBVars then g (b.instantiate1 v)
    else .letE n t (g v) (g b) nd
  | e => e

def OldEqNV (senv : StructEnv) (g : Lean.Expr → Lean.Expr) : Prop :=
  ∀ e, g e = oNormV senv g e

theorem oNormV_eq (senv : StructEnv) (g : Lean.Expr → Lean.Expr) (e : Lean.Expr) :
    oNormV senv g e = oNorm senv g e := by
  cases e with
  | app f a =>
    first
      | simp only [oNormV, oNorm]
      | (unfold oNormV oNorm; dsimp only)
    rw [ashrMatch_view]
    all_goals rfl
  | _ => rfl

theorem oldEqN_of_oldEqNV {senv : StructEnv} {g : Lean.Expr → Lean.Expr} (h : OldEqNV senv g) :
    OldEqN senv g := fun e => (h e).trans (oNormV_eq senv g e)

/-- **Agreement of the fuel `machNorm` with the VERBATIM old source equation.** -/
theorem machNormF_agree_verbatim {senv : StructEnv} {g : Lean.Expr → Lean.Expr}
    (h : OldEqNV senv g) {n : Nat} {e r : Lean.Expr} (hr : machNormF n senv e = some r) :
    g e = r :=
  machNormF_agree_old (oldEqN_of_oldEqNV h) hr

end Tools.ShippingReaderFuel
