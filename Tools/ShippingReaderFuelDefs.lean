import Sparkle.Compiler.Elab

/-! # A fuel-indexed TOTAL candidate of the machine reader — definitions only

BUILT on poc 22908c5f (run `a1`, cgrun -j 1; integrator fix: `Call.*` constructors qualified). Worker A, branch `par/r-3`; record
`docs/parallel/R-reader-fuel.md`). No `sorry`, no axiom, no `native_decide`.

Ruling 2026-10-15 (A): fuel-indexed total versions of `machNorm` and of the
seven-function `mutual` block (`machConv`, `machNested`, `machInstance`,
`machInstanceS`, `machChain`, `machLoopBody`, `machLoopRoot`) as an ISOLATED
candidate. NOTHING here is imported by `Sparkle/Compiler/Elab.lean`; the real
compiler path is unchanged (the `partial def`s are not edited and nothing
that calls them is). This file is under `Tools/` (not `Sparkle/Compiler/`), so
that no `sparkleModuleDeps` entry and no `Sparkle` library change is needed.

## Design

* **One body, not seven mutual functions.** Every call into the block is a
  value of `Call` (the seven argument tuples, `senv` fixed), its result type
  `Call.Res`. Each of the seven bodies is a NON-recursive function
  (`convStep`, `nestedStep`, …): a recursive call is the effect `FM.call c`.
  `step senv : (c : Call) → BM (Option c.Res)` dispatches. No `mutual`, no
  termination argument: the fuel function `fuel Φ n` is structural on `n`.
* **Three-valued result.** `fuel Φ n c : Option (Option c.Res)`:
  `none` = OUT (fuel exhausted), `some none` = FAIL (the old `none`),
  `some (some r)` = OK (the old `some r`). OUT is never read as FAIL
  anywhere: it is the outer `Option`, propagated by `FM.bind` only.
* **Monotone by construction.** `FM κ R α` is a computation over a call
  table `h : (c : κ) → Option (R c)` (`none` = "not answered at this fuel")
  TOGETHER with the proof that it is monotone in the table (`FM.mono`).
  `pure`, `bind`, `call` are monotone, so every body written with them is.
  Hence stability across fuel, monotonicity and agreement with every
  solution of the source equations are generic theorems
  (`Tools/ShippingReaderFuelKleene.lean`), proved ONCE.
* **The two sharing probes** (`machNested` 4024–4030, `machLoopRoot`
  4207–4211): `findSomeO` runs the probe in `FM`; a probe whose call is OUT
  makes the WHOLE call OUT (`FM.bind`), a probe's FAIL means "not this one"
  (as `findSome?`). Reading OUT as "not shared" would allocate a fresh
  sub-machine and change the OUTPUT; that cannot happen here — and could not
  be monotone.
* **Evaluation order mirrors the old text**: `foldO` stops at the first FAIL
  (`foldlM` in `Option`), `findSomeO` at the first hit (`findSome?`), guards
  short-circuit before any call, and `machChain`'s `next` arm evaluates
  `machConv rhs` BEFORE looking at `machHandleV h` (the old
  `match machHandleV env 0 h, machConv senv env 0 rhs st with`, 4133).
* **Pure fragments are the source text.** Arms with no recursive call are
  the source text under `FM.pure` (the `.bvar` arm is `convBvar`, its local
  `let rec bundle` lifted to the structural `bundleSlots`; `machInstanceS`'s
  `let rec inst` is `instRes`; `machInstance`'s first `match res` is
  `instEntry`; `machLoopRoot`'s pattern-`let` is `loopView?` and its three
  list functions `loopRegBad` / `loopRegKind` / `loopRegInit`). The old
  equations (`Tools/ShippingReaderFuelOldEq.lean`) use the SAME fragments, so
  the two sides of each arm match on identical discriminants. The two matchers v4.32.1 cannot split
  (name-literal + array-literal patterns: the bare `Signal.register` arm of
  `machConv`, the `Signal.ashr` arm of `machNorm`) are read through the views
  `regView?` / `ashrView?`, whose bodies ARE those matches
  (`Tools/ShippingReaderFuelVerbatim.lean` relates them to the inline text).
* **The still-`partial` helpers** (`rootFloat`, `zetaAll` inside
  `machReserve`, `machNormNode`'s callees, `rawNode`'s) are called unchanged,
  as opaque constants: they are not part of the fuel.

What is NOT here: a fuel version of the wrapper `machineShape?` (one fuel
threaded through its six reader calls) and any driver. Never a fixed FUEL
with OUT → `none` → legacy (not acceptance-preserving). -/
namespace Tools.ShippingReaderFuel
open Lean
open Sparkle.Compiler.Elab

/-! ## The monotone computation over a call table -/

/-- The information order on call tables: `h₂` answers every call `h₁`
answers, with the same answer. -/
def HLe {κ : Type} {R : κ → Type} (h₁ h₂ : (c : κ) → Option (R c)) : Prop :=
  ∀ c r, h₁ c = some r → h₂ c = some r

/-- A computation reading a call table `h` (`h c = none`: call `c` is not
answered — OUT), with its monotonicity: a result obtained with `h₁` is
obtained with every `h₂` above it. -/
structure FM (κ : Type) (R : κ → Type) (α : Type) where
  run : ((c : κ) → Option (R c)) → Option α
  mono : ∀ h₁ h₂, HLe h₁ h₂ → ∀ a, run h₁ = some a → run h₂ = some a

namespace FM
variable {κ : Type} {R : κ → Type} {α β : Type}

def pure (a : α) : FM κ R α where
  run _ := some a
  mono _ _ _ _ h := h

def bind (x : FM κ R α) (f : α → FM κ R β) : FM κ R β where
  run h := (x.run h).bind fun a => (f a).run h
  mono h₁ h₂ hle b hb := by
    obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp hb
    exact Option.bind_eq_some_iff.mpr ⟨a, x.mono h₁ h₂ hle a ha, (f a).mono h₁ h₂ hle b hb⟩

/-- A recursive call: the table's answer. -/
def call (c : κ) : FM κ R (R c) where
  run h := h c
  mono _ _ hle a ha := hle _ a ha

end FM

/-! ## `Option`-valued computations (FAIL = `some none`) -/

section Combinators
variable {κ : Type} {R : κ → Type} {α β σ : Type}

/-- The old `some a`. -/
def okO (a : α) : FM κ R (Option α) := FM.pure (some a)

/-- The old `none` (a refusal, NOT fuel exhaustion). -/
def failO : FM κ R (Option α) := FM.pure none

/-- Continue on `some a`, FAIL on `none` (a pure `Option` value or the inner
result of a call). -/
def optK (o : Option α) (f : α → FM κ R (Option β)) : FM κ R (Option β) :=
  match o with
  | some a => f a
  | none => FM.pure none

/-- `do let a ← x; f a` of the old `Option` text. -/
def bindO (x : FM κ R (Option α)) (f : α → FM κ R (Option β)) : FM κ R (Option β) :=
  FM.bind x fun o => optK o f

/-- `match o with | some d0 => if d0 != dom' then none else pure () | none =>
pure ()`, followed by `k`. -/
def domGuard (o : Option Lean.Expr) (dom' : Lean.Expr) (k : FM κ R (Option β)) :
    FM κ R (Option β) :=
  match o with
  | some d0 => if d0 != dom' then FM.pure none else k
  | none => k

/-- `List.foldlM` in `Option`: stops at the first FAIL. -/
def foldO (f : σ → α → FM κ R (Option σ)) : σ → List α → FM κ R (Option σ)
  | s, [] => okO s
  | s, a :: as => bindO (f s a) fun s' => foldO f s' as

/-- `List.findSome?`: stops at the first hit; a FAIL of `f a` is "not this
one"; an OUT of `f a` is OUT of the whole search (`FM.bind`). -/
def findSomeO (f : α → FM κ R (Option β)) : List α → FM κ R (Option β)
  | [] => FM.pure none
  | a :: as => FM.bind (f a) fun o =>
    match o with
    | some b => FM.pure (some b)
    | none => findSomeO f as

end Combinators

/-- The fuel iteration of a body: fuel `0` answers nothing (OUT), fuel
`n + 1` runs the body against the answers of fuel `n`. -/
def fuel {κ : Type} {R : κ → Type} (Φ : (c : κ) → FM κ R (R c)) :
    Nat → (c : κ) → Option (R c)
  | 0, _ => none
  | n + 1, c => (Φ c).run (fuel Φ n)

/-! ## The calls of the block -/

/-- The seven functions of the block, as one call type (`senv` fixed). -/
inductive Call where
  | conv (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead)
  | nested (env : List MachVal) (dom αs initsE body : Lean.Expr) (st : MachRead)
  | inst (env : List MachVal) (c : Name) (kinds : List MixedGateBinder) (res : MixedGateBinder)
      (args : List Lean.Expr) (st : MachRead)
  | instS (env : List MachVal) (c : Name) (kinds : List MixedGateBinder) (ty : Lean.Expr)
      (args : List Lean.Expr) (st : MachRead)
  | chain (env : List MachVal) (e : Lean.Expr) (st : MachRead)
  | loopBody (base : Nat) (env : List MachVal) (e : Lean.Expr) (st : MachRead)
  | loopRoot (env : List MachVal) (e : Lean.Expr) (st : MachRead)

/-- The old result type of each function (inside its `Option`). -/
@[reducible] def Call.Res : Call → Type
  | .conv .. => Lean.Expr × MachRead
  | .nested .. => Lean.Expr × MachRead
  | .inst .. => Lean.Expr × MachRead
  | .instS .. => Lean.Expr × MachRead
  | .chain .. => List (Nat × Lean.Expr) × Lean.Expr × MachRead
  | .loopBody .. => MachRead
  | .loopRoot .. => MachVal × MachRead

/-- A call's answer: the old `Option` result (`none` = FAIL). -/
abbrev RB : Call → Type := fun c => Option c.Res

/-- Computations of the block. -/
abbrev BM (α : Type) := FM Call RB α

/-- A call table of the block (`none` = OUT). -/
abbrev Hs := (c : Call) → Option (RB c)

def cConv (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead) :
    BM (Option (Lean.Expr × MachRead)) :=
  FM.call (Call.conv env d e st)

def cNested (env : List MachVal) (dom αs initsE body : Lean.Expr) (st : MachRead) :
    BM (Option (Lean.Expr × MachRead)) :=
  FM.call (Call.nested env dom αs initsE body st)

def cInst (env : List MachVal) (c : Name) (kinds : List MixedGateBinder) (res : MixedGateBinder)
    (args : List Lean.Expr) (st : MachRead) : BM (Option (Lean.Expr × MachRead)) :=
  FM.call (Call.inst env c kinds res args st)

def cInstS (env : List MachVal) (c : Name) (kinds : List MixedGateBinder) (ty : Lean.Expr)
    (args : List Lean.Expr) (st : MachRead) : BM (Option (Lean.Expr × MachRead)) :=
  FM.call (Call.instS env c kinds ty args st)

def cChain (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    BM (Option (List (Nat × Lean.Expr) × Lean.Expr × MachRead)) :=
  FM.call (Call.chain env e st)

def cLoopBody (base : Nat) (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    BM (Option MachRead) :=
  FM.call (Call.loopBody base env e st)

def cLoopRoot (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    BM (Option (MachVal × MachRead)) :=
  FM.call (Call.loopRoot env e st)

/-! ## Pure fragments (source text; shared with the old equations) -/

/-- `machConv`'s local `let rec bundle` (3897–3903), lifted (structural on
the list, no fuel). -/
def bundleSlots (dom : Lean.Expr) : List Nat → List Lean.Expr → Option (Lean.Expr × Lean.Expr)
  | [i], [t] => some (machSlot i, t)
  | i :: is, t :: ts => do
    let (rest, restT) ← bundleSlots dom is ts
    some (mkApp5 (.const ``Sparkle.Core.Signal.bundle2 [.zero]) dom t restT (machSlot i) rest,
      mkApp2 (.const ``Prod [.zero, .zero]) t restT)
  | _, _ => none

/-- `machConv`'s `.bvar` arm (3885–3906): no recursive call. -/
def convBvar (env : List MachVal) (d j : Nat) (st : MachRead) : Option (Lean.Expr × MachRead) :=
  if j < d then some (.bvar j, st) else
  match env[j - d]? with
  | some (.val v) => some (v, st)
  | some (.state b 1) => some (machSlot b, st)
  | some (.state b n) => do
    let dom ← st.dom
    let tyOf (k : MixedGateBinder) : Option Lean.Expr := match k with
      | .bits w => some (mkApp (.const ``BitVec []) (inlNatLit w))
      | .bool => some (.const ``Bool [])
      | .domain => none
    let tys ← ((List.range n).map (b + ·)).mapM fun i => st.kinds[i]? >>= tyOf
    let (e, _) ← bundleSlots dom ((List.range n).map (b + ·)) tys
    some (e, st)
  | some _ => none
  | none => some (machIn (j - d - env.length), st)

/-- The bare-register test of `machConv` (3913): the match on
`e.getAppFn, e.getAppArgs` itself, as a view. -/
def regView? (fn : Lean.Expr) (args : Array Lean.Expr) :
    Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) :=
  match fn, args with
  | .const ``Sparkle.Core.Signal.Signal.register _, #[dom, α, init, x] => some (dom, α, init, x)
  | _, _ => none

/-- `machInstanceS`'s local `let rec inst` (4085–4088), lifted. -/
def instRes : Lean.Expr → List Lean.Expr → Option Lean.Expr
  | e, [] => some e
  | .forallE _ _ b _, a :: as => instRes (b.instantiate1 a) as
  | _, _ => none

/-- `machInstance`'s first step (4049–4052): the state for the result kind. -/
def instEntry (res : MixedGateBinder) (st : MachRead) : Option MachRead :=
  match res with
  | .bits _ => pure st
  | .bool => pure { st with instStruct := true }
  | _ => none

/-- `machLoopRoot`'s pattern `let (.const ``Signal.loop _, [dom, _, _, .lam _ _
body _]) := inlSpine e [] | none` (4195–4196), as a view: `(dom, body)`. -/
def loopView? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  match inlSpine e [] with
  | (.const ``Sparkle.Core.Signal.Signal.loop _, [dom, _, _, .lam _ _ body _]) => some (dom, body)
  | _ => none

/-- `machLoopRoot`'s `regs.any` function (4198). -/
def loopRegBad : Lean.Expr × Lean.Expr × Lean.Expr → Bool
  | (ty, init, _) => ty.hasLooseBVars || init.hasLooseBVars

/-- `machLoopRoot`'s first `mapM` function (4199). -/
def loopRegKind : Lean.Expr × Lean.Expr × Lean.Expr → Option MixedGateBinder
  | (ty, _, _) => machSlotKind? ty

/-- `machLoopRoot`'s second `mapM` function (4200). -/
def loopRegInit (natOf : Lean.Expr → Option Nat) :
    MixedGateBinder × (Lean.Expr × Lean.Expr × Lean.Expr) → Option Nat
  | (k, (_, init, _)) => machInit? natOf k init

/-! ## The seven bodies (a recursive call is `FM.call`) -/

/-- `machConv` (3884–4010). -/
def convStep (senv : StructEnv) : List MachVal → Nat → Lean.Expr → MachRead →
    BM (Option (Lean.Expr × MachRead))
  | env, d, .bvar j, st => FM.pure (convBvar env d j st)
  | env, d, e@(.app f a), st =>
    match regView? e.getAppFn e.getAppArgs with
    | some (dom, α, init, x) =>
      if d != 0 || st.inInner || !st.loops.isEmpty || !st.runs.isEmpty then failO else
      match st.bareRegs.find? (·.1 == e) with
      | some (_, k) => okO (machSlot k, st)
      | none =>
      optK (machSlotKind? α) fun kind =>
      optK (machInit? senv.natOf kind init) fun initN =>
      bindO (cConv env 0 dom st) fun (dom', st) =>
      domGuard st.dom dom'
        (let base := st.kinds.size
         let st := { st with
           kinds := st.kinds.push kind, inits := st.inits.push initN
           names := st.names.push (Name.mkSimple s!"reg{base}"), dom := some dom'
           bareRegs := st.bareRegs.push (e, base) }
         bindO (cConv env 0 x st) fun (x', st) =>
         okO (machSlot base, { st with ws := st.ws.push (base, x') }))
    | none =>
    match machLoopRead? env d (.app f a) with
    | some i => FM.pure (if i < st.kinds.size then some (machSlot i, st) else none)
    | none =>
    match machRunApp? (.app f a) with
    | some (dom, αs, initsE, body) =>
      if d != 0 then failO else cNested env dom αs initsE body st
    | none =>
    match machInstCall? senv (.app f a) with
    | some (c, kinds, res, args) =>
      if d != 0 then failO else cInst env c kinds res args st
    | none =>
    match machInstCallS? senv (.app f a) with
    | some (c, kinds, ty, args) =>
      if d != 0 then failO else cInstS env c kinds ty args st
    | none =>
    match Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e)
        (.app f a) with
    | some (combo, aw, dw, dom, ops) =>
      if d != 0 then failO else
        bindO (cInst env (Sparkle.Compiler.MachMemory.memChildName combo aw dw)
            [.domain, .bits aw, .bits dw, .bool, .bits aw] (.bits dw) (dom :: ops) st)
          fun (v, st) => okO (v, { st with instStruct := true })
    | none =>
    match machReadV env d (.app f a) with
    | some i => FM.pure (if i < st.kinds.size then some (machSlot i, st) else none)
    | none =>
      bindO (cConv env d f st) fun (f', st) =>
      bindO (cConv env d a st) fun (a', st) =>
      okO (Sparkle.Compiler.MachRawSurface.bundleIota (machProjIota senv.proj (.app f' a')), st)
  | env, d, .lam nm t b bi, st =>
    bindO (cConv env d t st) fun (t', st) =>
    bindO (cConv env (d + 1) b st) fun (b', st) =>
    okO (.lam nm t' b' bi, st)
  | env, d, .forallE nm t b bi, st =>
    bindO (cConv env d t st) fun (t', st) =>
    bindO (cConv env (d + 1) b st) fun (b', st) =>
    okO (.forallE nm t' b' bi, st)
  | env, d, .letE nm ty v b nd, st =>
    if d != 0 then failO else
    match Sparkle.Compiler.MachRawSurface.rootFloat v with
    | .letE n2 t2 v2 w nd2 =>
      cConv env 0
        (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) st
    | v =>
    if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
      bindO (cLoopRoot env v st) fun (mv, st) => cConv (mv :: env) 0 b st
    else
    match machTailV env 0 v with
    | some p => cConv (.regs p :: env) 0 b st
    | none =>
      match machHandleV env 0 v with
      | some i => cConv (.handle i :: env) 0 b st
      | none =>
        bindO (cConv env 0 v st) fun (v', st) =>
          let (x, lets) := machBindLet nm ty v' st.lets
          cConv (.val x :: env) 0 b { st with lets := lets }
  | _, _, .mdata .., _ => failO
  | _, _, .proj .., _ => failO
  | _, _, e, st => okO (e, st)

/-- `machNested`'s sharing probe (the `findSome?` function, 4024–4030). -/
def nestedProbe (env : List MachVal) (dom' αs initsE body : Lean.Expr) (st : MachRead) :
    (Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr) →
      BM (Option (Lean.Expr × MachRead))
  | (base, d, a, ini, ws, v) =>
    if d == dom' && a == αs && ini == initsE then
      FM.bind (cChain (.regs base :: env) body st) fun r =>
      FM.pure (match r with
        | some (ws', v', st') => if ws' == ws && v' == v then some (v, st') else none
        | none => none)
    else FM.pure none

/-- `machNested` (4016–4037). -/
def nestedStep (senv : StructEnv) (env : List MachVal) (dom αs initsE body : Lean.Expr)
    (st : MachRead) : BM (Option (Lean.Expr × MachRead)) :=
  if st.inInner then failO else
  bindO (cConv env 0 dom st) fun (dom', st) =>
  FM.bind (findSomeO (nestedProbe env dom' αs initsE body st) st.nested.toList) fun shared =>
  match shared with
  | some r => okO r
  | none =>
    optK (machReserve senv.natOf dom' αs initsE body st) fun (base, st) =>
    let outer := st.inInner
    bindO (cChain (.regs base :: env) body { st with inInner := true }) fun (ws, v, st) =>
    okO (v, { st with ws := st.ws ++ ws.toArray, inInner := outer,
                       nested := st.nested.push (base, dom', αs, initsE, ws, v) })

/-- `machInstance`'s `foldlM` function (4057–4066). -/
def instArg (env : List MachVal) (k : Nat) :
    List Nat × MachRead → MixedGateBinder × Lean.Expr → BM (Option (List Nat × MachRead))
  | (js, st), (kind, arg) =>
    bindO (cConv env 0 arg st) fun (v', st) =>
    FM.pure (match kind with
      | .domain =>
        match st.dom with
        | some d => if d != v' then none else some (js, st)
        | none => some (js, { st with dom := some v' })
      | _ =>
        let (j, lets) := machLetIndex (Name.mkSimple s!"inst{k}_arg{js.length}") kind v' st.lets
        some (js ++ [j], { st with lets := lets }))

/-- `machInstance` (4045–4069). -/
def instStep (env : List MachVal) (c : Name) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) :
    BM (Option (Lean.Expr × MachRead)) :=
  optK (instEntry res st) fun st =>
  let k := st.insts.size
  bindO (foldO (instArg env k) (([] : List Nat), st) (kinds.zip args)) fun (js, st) =>
  FM.pure (match st.insts.findIdx? (fun i => i.1 == c && i.2.1 == js) with
    | some k' => some (machInstOut k', st)
    | none => some (machInstOut k, { st with insts := st.insts.push (c, js, res),
                                             instFields := st.instFields.push "out" }))

/-- `machInstanceS`'s first `foldlM` function (4091–4101). -/
def instSArg (env : List MachVal) :
    List Nat × MachRead → MixedGateBinder × Lean.Expr → BM (Option (List Nat × MachRead))
  | (js, st), (kind, arg) =>
    bindO (cConv env 0 arg st) fun (v', st) =>
    FM.pure (match kind with
      | .domain =>
        match st.dom with
        | some d => if d != v' then none else some (js, st)
        | none => some (js, { st with dom := some v' })
      | _ =>
        let (j, lets) := machLetIndex (Name.mkSimple s!"inst{st.insts.size}_arg{js.length}")
          kind v' st.lets
        some (js ++ [j], { st with lets := lets }))

/-- `machInstanceS`'s second `foldlM` function (4103–4107). -/
def instSParam (env : List MachVal) :
    List Lean.Expr × MachRead → Lean.Expr → BM (Option (List Lean.Expr × MachRead))
  | (ps, st), p =>
    bindO (cConv env 0 p st) fun (p', st) => okO (ps ++ [p'], st)

/-- `machInstanceS` (4079–4117). The final `let (k0, st) := match … ; some …`
is distributed over the `match` (the same value in each case). -/
def instSStep (senv : StructEnv) (env : List MachVal) (c : Name) (kinds : List MixedGateBinder)
    (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead) :
    BM (Option (Lean.Expr × MachRead)) :=
  if st.inInner then failO else
  optK (instRes ty args) fun resTy =>
  optK (machOuts? senv resTy) fun r =>
  match r with
  | (some ctor, fields) =>
    if fields.isEmpty || fields.any (fun f => f.2 == .domain) then failO else
    bindO (foldO (instSArg env) (([] : List Nat), st) (kinds.zip args)) fun (js, st) =>
    bindO (foldO (instSParam env) (([] : List Lean.Expr), st) resTy.getAppArgs.toList)
      fun (params, st) =>
    let lvls := resTy.getAppFn.constLevels!
    match st.insts.findIdx? (fun i => i.1 == c && i.2.1 == js) with
    | some k0 =>
      okO (mkAppN (.const ctor lvls)
        (params.toArray ++ ((List.range fields.length).map fun i => machInstOut (k0 + i)).toArray),
        st)
    | none =>
      okO (mkAppN (.const ctor lvls)
        (params.toArray ++
          ((List.range fields.length).map fun i => machInstOut (st.insts.size + i)).toArray),
        { st with
          insts := st.insts ++ (fields.map fun f => (c, js, f.2)).toArray
          instFields := st.instFields ++ (fields.map (·.1)).toArray
          instStruct := true })
  | (none, _) => failO

/-- `machChain` (4124–4165). -/
def chainStep (senv : StructEnv) : List MachVal → Lean.Expr → MachRead →
    BM (Option (List (Nat × Lean.Expr) × Lean.Expr × MachRead))
  | env, .app (.app (.app (.app (.const ``Sparkle.Core.Circuit.pure' _) _) _) _) v, st =>
    bindO (cConv env 0 v st) fun (v', st) => okO ([], v', st)
  | env, .app (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.bind _) _) _) _) _)
      (.app (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.next _) _) _) _) _)
        h) rhs)) (.lam _ _ rest _), st =>
    -- the old text evaluates `machConv rhs` together with `machHandleV h`
    FM.bind (cConv env 0 rhs st) fun r =>
    match machHandleV env 0 h, r with
    | some i, some (rhs', st) =>
      if i < st.kinds.size then
        bindO (cChain (.unit :: env) rest st) fun (ws, v, st) => okO ((i, rhs') :: ws, v, st)
      else failO
    | _, _ => failO
  | env, .letE nm ty v b nd, st =>
    match Sparkle.Compiler.MachRawSurface.rootFloat v with
    | .letE n2 t2 v2 w nd2 =>
      cChain env
        (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) st
    | v =>
    if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
      bindO (cLoopRoot env v st) fun (mv, st) => cChain (mv :: env) b st
    else
    match machTailV env 0 v with
    | some p => cChain (.regs p :: env) b st
    | none =>
      match machHandleV env 0 v with
      | some i => cChain (.handle i :: env) b st
      | none =>
        bindO (cConv env 0 v st) fun (v', st) =>
          let (x, lets) := machBindLet nm ty v' st.lets
          cChain (.val x :: env) b { st with lets := lets }
  | _, _, _ => failO

/-- `machLoopBody`'s `foldlM` function (4181–4184). -/
def loopNext (env : List MachVal) (base : Nat) :
    List (Nat × Lean.Expr) × MachRead → Lean.Expr × Lean.Expr × Lean.Expr →
      BM (Option (List (Nat × Lean.Expr) × MachRead))
  | (ws, st), (_, _, nx) =>
    bindO (cConv env 0 nx st) fun (nx', st) => okO (ws ++ [(base + ws.length, nx')], st)

/-- `machLoopBody` (4171–4185). -/
def loopBodyStep (base : Nat) : List MachVal → Lean.Expr → MachRead → BM (Option MachRead)
  | env, .letE nm ty v b _, st =>
    bindO (cConv env 0 v st) fun (v', st) =>
    let (x, lets) := if machIsSlot v' then machBindLetNamed nm ty v' st.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets
      else machBindLet nm ty v' st.lets
    cLoopBody base (.val x :: env) b { st with lets := lets }
  | env, tail, st =>
    optK (machLoopRegs tail) fun regs =>
    bindO (foldO (loopNext env base) (([] : List (Nat × Lean.Expr)), st) regs) fun (ws, st) =>
    okO { st with ws := st.ws ++ ws.toArray }

/-- `machLoopRoot`'s sharing probe (the `findSome?` function, 4207–4211). -/
def loopProbe (env : List MachVal) (body : Lean.Expr) (n : Nat) (st : MachRead) :
    Nat × Nat × List (Nat × Lean.Expr) → BM (Option (Nat × MachRead))
  | (b0, n0, ws0) =>
    if n0 != n then FM.pure none else
    FM.bind (cLoopBody b0 (.state b0 n :: env) body { st with ws := #[] }) fun r =>
    FM.pure (match r with
      | some st' => if st'.ws.toList == ws0 then some (b0, { st' with ws := st.ws }) else none
      | none => none)

/-- `machLoopRoot` (4193–4230). -/
def loopRootStep (senv : StructEnv) (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    BM (Option (MachVal × MachRead)) :=
  match loopView? e with
  | some (dom, body) =>
    if st.inInner then failO else
    optK (machLoopRegs (machLetTail body)) fun regs =>
    if regs.any loopRegBad then failO else
    optK (regs.mapM loopRegKind) fun kinds =>
    optK ((kinds.zip regs).mapM (loopRegInit senv.natOf)) fun inits =>
    bindO (cConv env 0 dom st) fun (dom', st) =>
    domGuard st.dom dom'
      (let n := kinds.length
       FM.bind (findSomeO (loopProbe env body n st) st.loopWs.toList) fun shared =>
       match shared with
       | some (b0, st') => okO (.state b0 n, st')
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
         bindO (cLoopBody base (.state base n :: env) body st) fun st =>
         okO (.state base n,
           { st with loopWs := st.loopWs.push (base, n, (st.ws.toList.drop before)),
                     loopDepth := depth }))
  | none => failO

/-- The block's body: one step of each of the seven functions. -/
def step (senv : StructEnv) : (c : Call) → BM (RB c)
  | .conv env d e st => convStep senv env d e st
  | .nested env dom αs initsE body st => nestedStep senv env dom αs initsE body st
  | .inst env c kinds res args st => instStep env c kinds res args st
  | .instS env c kinds ty args st => instSStep senv env c kinds ty args st
  | .chain env e st => chainStep senv env e st
  | .loopBody base env e st => loopBodyStep base env e st
  | .loopRoot env e st => loopRootStep senv env e st

/-- **The total block at fuel `n`.** `none` = OUT, `some none` = the old
`none`, `some (some r)` = the old `some r`. -/
def readF (senv : StructEnv) (n : Nat) : Hs :=
  fuel (step senv) n

def machConvF (n : Nat) (senv : StructEnv) (env : List MachVal) (d : Nat) (e : Lean.Expr)
    (st : MachRead) : Option (Option (Lean.Expr × MachRead)) :=
  readF senv n (.conv env d e st)

def machNestedF (n : Nat) (senv : StructEnv) (env : List MachVal)
    (dom αs initsE body : Lean.Expr) (st : MachRead) : Option (Option (Lean.Expr × MachRead)) :=
  readF senv n (.nested env dom αs initsE body st)

def machInstanceF (n : Nat) (senv : StructEnv) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (res : MixedGateBinder) (args : List Lean.Expr)
    (st : MachRead) : Option (Option (Lean.Expr × MachRead)) :=
  readF senv n (.inst env c kinds res args st)

def machInstanceSF (n : Nat) (senv : StructEnv) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr)
    (st : MachRead) : Option (Option (Lean.Expr × MachRead)) :=
  readF senv n (.instS env c kinds ty args st)

def machChainF (n : Nat) (senv : StructEnv) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) : Option (Option (List (Nat × Lean.Expr) × Lean.Expr × MachRead)) :=
  readF senv n (.chain env e st)

def machLoopBodyF (n : Nat) (senv : StructEnv) (base : Nat) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) : Option (Option MachRead) :=
  readF senv n (.loopBody base env e st)

def machLoopRootF (n : Nat) (senv : StructEnv) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) : Option (Option (MachVal × MachRead)) :=
  readF senv n (.loopRoot env e st)

/-! ## `machNorm` -/

/-- `machNorm`'s computations: calls on expressions, answers expressions. -/
abbrev NM (α : Type) := FM Lean.Expr (fun _ => Lean.Expr) α

/-- The `Signal.ashr` test of `machNorm` (4961): the match itself, as a view. -/
def ashrView? (fn : Lean.Expr) (args : Array Lean.Expr) :
    Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) :=
  match fn, args with
  | .const ``Sparkle.Core.Signal.Signal.ashr _, #[dom, nE, x, y] => some (dom, nE, x, y)
  | _, _ => none

/-- `machNorm` (4957–4986). It never refuses: its only "failure" is OUT. -/
def normStep (senv : StructEnv) : Lean.Expr → NM Lean.Expr
  | e@(.app f a) =>
    match ashrView? e.getAppFn e.getAppArgs with
    | some (dom, nE, x, y) =>
      match canonicalNatLitValue? nE with
      | some n =>
        if n == 0 then FM.pure e else
        FM.bind (FM.call x) fun x' => FM.bind (FM.call y) fun y' =>
        FM.pure (Sparkle.Compiler.MachSignOps.ashrE inlNatLit
          (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b)
          dom n x' y')
      | none => FM.pure e
    | none =>
    match Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch e with
    | some e' => FM.call e'
    | none =>
      FM.bind (FM.call f) fun f' => FM.bind (FM.call a) fun a' =>
      FM.pure (machNormNode senv (.app f' a'))
  | .lam n t b bi => FM.bind (FM.call b) fun b' => FM.pure (.lam n t b' bi)
  | .letE n t v b nd =>
    if t.isConstOf ``Nat then FM.call (b.instantiate1 v)
    else if (machBits? t).isSome && !v.hasLooseBVars then FM.call (b.instantiate1 v)
    else FM.bind (FM.call v) fun v' => FM.bind (FM.call b) fun b' => FM.pure (.letE n t v' b' nd)
  | e => FM.pure e

/-- **The total `machNorm` at fuel `n`.** `none` = OUT. -/
def machNormF (n : Nat) (senv : StructEnv) (e : Lean.Expr) : Option Lean.Expr :=
  @fuel Lean.Expr (fun _ => Lean.Expr) (normStep senv) n e

end Tools.ShippingReaderFuel
