import Tools.ShippingReaderFuelKleene
import Tools.ShippingReaderFuelRun

/-! # The OLD source equations of the reader, and agreement of the fuel candidate

STATUS: BUILT on poc fc697219 (integrator run `a2`; round 2, worker A, branch
`par/r-6`). Header status corrected 2026-10-16 (comment only). Round 1
(`par/r-3`, run `a1` on poc 0a53bd9e) did NOT build: `conv_tot` timed out
(200000 heartbeats) and `chain_tot` / `loopRoot_tot` left cross-product
leaves (`some none` vs `some (some …)`, both sides' `match` on the same
discriminant split independently; contradictory leaves that `simp_all` did
not close — no real difference between the texts was found). Round 2: those
three arms decomposed per constructor / per view with the discriminant
equations as explicit hypotheses and the aligned crunch `tot_align` (each
`split` hypothesis rewritten on both sides at once); the other arms are
round 1's text unchanged (they built in `a1`). `run_pure` / `run_bind` /
`run_bindO` now come from `Tools/ShippingReaderFuelRun.lean`. No `sorry`, no
axiom, no `native_decide`.

`OldEq senv G` / `OldEqN senv g` are the old source equations of the seven
`partial def`s of the block (`Sparkle/Compiler/Elab.lean` 3874–4233 at
`c1c651a0`) and of `machNorm` (4957–4986), as a `Prop` over a function TUPLE
(`OldFns`) / a function — the pattern of `prodMatcherArity?`'s `OldEq`
(`Tools/ShippingReaderMatcherArityArray.lean`). Each body below is the source
text with every recursive call `machX senv …` replaced by the tuple's field
`G.x …`, and with these refactorings ONLY (each a definitional unfolding,
except the two views):

* the pure fragments shared with the fuel bodies (`Tools/ShippingReaderFuelDefs.lean`):
  the `.bvar` arm (`convBvar`, its `let rec bundle` = `bundleSlots`),
  `machInstanceS`'s `let rec inst` (`instRes`), `machInstance`'s first
  `match res` (`instEntry`), `machLoopRoot`'s three list functions
  (`loopRegBad`, `loopRegKind`, `loopRegInit`) and its pattern-`let` (`loopView?`);
* the functions passed to `foldlM` / `findSome?` lifted to named functions
  (`oInstArg`, `oInstSArg`, `oInstSParam`, `oLoopNext`, `oNestedProbe`,
  `oLoopProbe`), their bodies verbatim;
* the two matches v4.32.1 cannot split (`Signal.register` in `machConv`,
  `Signal.ashr` in `machNorm`) through `regView?` / `ashrView?`, whose bodies
  ARE those matches. `Tools/ShippingReaderFuelVerbatim.lean` states the
  inline-text versions and relates them.

Main results:

* `step_tot` / `normStep_tot`: the fuel body run against the TOTAL table of
  ANY tuple is the old text at that tuple (per arm, by unfolding and case
  analysis; nothing about `partial` is used);
* hence `isSol_of_oldEq`: every solution of the old source equations is a
  solution of the body's equation (`IsSol`), and **`readF_agree_old`**:
  `readF senv n c = some r → OldEq senv G → G.app c = r` (the old `some r`
  AND the old `none`), the same for `machNorm` (`machNormF_agree_old`).

These are CONDITIONAL agreements: with every tuple `G` that SATISFIES the old
source equations (`OldEq senv G` is a hypothesis). They say nothing about
the compiled `partial` constants unless those satisfy `OldEq` — which is
outside the kernel (the meaning of `partial`), as is coverage (an old answer
reached by some fuel). `readF_agree` (Kleene file) is weaker still: it is
conditional on `IsSol (step senv) g`, the body's own equation, and is not an
agreement with the old reader by itself. -/
namespace Tools.ShippingReaderFuel
open Lean
open Sparkle.Compiler.Elab

/-! ## The tuple of old functions -/

structure OldFns where
  conv : List MachVal → Nat → Lean.Expr → MachRead → Option (Lean.Expr × MachRead)
  nested : List MachVal → Lean.Expr → Lean.Expr → Lean.Expr → Lean.Expr → MachRead →
    Option (Lean.Expr × MachRead)
  inst : List MachVal → Name → List MixedGateBinder → MixedGateBinder → List Lean.Expr →
    MachRead → Option (Lean.Expr × MachRead)
  instS : List MachVal → Name → List MixedGateBinder → Lean.Expr → List Lean.Expr →
    MachRead → Option (Lean.Expr × MachRead)
  chain : List MachVal → Lean.Expr → MachRead →
    Option (List (Nat × Lean.Expr) × Lean.Expr × MachRead)
  loopBody : Nat → List MachVal → Lean.Expr → MachRead → Option MachRead
  loopRoot : List MachVal → Lean.Expr → MachRead → Option (MachVal × MachRead)

def OldFns.app (G : OldFns) : (c : Call) → RB c
  | .conv env d e st => G.conv env d e st
  | .nested env dom αs initsE body st => G.nested env dom αs initsE body st
  | .inst env c kinds res args st => G.inst env c kinds res args st
  | .instS env c kinds ty args st => G.instS env c kinds ty args st
  | .chain env e st => G.chain env e st
  | .loopBody base env e st => G.loopBody base env e st
  | .loopRoot env e st => G.loopRoot env e st

/-- The total table of a tuple. -/
def tot (G : OldFns) : Hs := fun c => some (G.app c)

/-! ## The old texts -/

/-- `machConv` (3884–4010). -/
def oConv (senv : StructEnv) (G : OldFns) : List MachVal → Nat → Lean.Expr → MachRead →
    Option (Lean.Expr × MachRead)
  | env, d, .bvar j, st => convBvar env d j st
  | env, d, e@(.app f a), st =>
    match regView? e.getAppFn e.getAppArgs with
    | some (dom, α, init, x) =>
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
    | none =>
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
    match Sparkle.Compiler.MachRawSurface.rootFloat v with
    | .letE n2 t2 v2 w nd2 =>
      G.conv env 0
        (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) st
    | v =>
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

/-- `machNested`'s `findSome?` function (4024–4030). -/
def oNestedProbe (G : OldFns) (env : List MachVal) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) :
    (Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) × Lean.Expr) →
      Option (Lean.Expr × MachRead)
  | (base, d, a, ini, ws, v) =>
    if d == dom' && a == αs && ini == initsE then
      match G.chain (.regs base :: env) body st with
      | some (ws', v', st') => if ws' == ws && v' == v then some (v, st') else none
      | none => none
    else none

/-- `machNested` (4016–4037). -/
def oNested (senv : StructEnv) (G : OldFns) (env : List MachVal) (dom αs initsE body : Lean.Expr)
    (st : MachRead) : Option (Lean.Expr × MachRead) := do
  if st.inInner then none else
  let (dom', st) ← G.conv env 0 dom st
  let shared := st.nested.findSome? (oNestedProbe G env dom' αs initsE body st)
  match shared with
  | some r => some r
  | none =>
    let (base, st) ← machReserve senv.natOf dom' αs initsE body st
    let outer := st.inInner
    let (ws, v, st) ← G.chain (.regs base :: env) body { st with inInner := true }
    some (v, { st with ws := st.ws ++ ws.toArray, inInner := outer,
                       nested := st.nested.push (base, dom', αs, initsE, ws, v) })

/-- `machInstance`'s `foldlM` function (4057–4066). -/
def oInstArg (G : OldFns) (env : List MachVal) (k : Nat) :
    List Nat × MachRead → MixedGateBinder × Lean.Expr → Option (List Nat × MachRead)
  | (js, st), (kind, arg) => do
    let (v', st) ← G.conv env 0 arg st
    match kind with
    | .domain =>
      match st.dom with
      | some d => if d != v' then none else some (js, st)
      | none => some (js, { st with dom := some v' })
    | _ =>
      let (j, lets) := machLetIndex (Name.mkSimple s!"inst{k}_arg{js.length}") kind v' st.lets
      some (js ++ [j], { st with lets := lets })

/-- `machInstance` (4045–4069). -/
def oInst (G : OldFns) (env : List MachVal) (c : Name) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) :
    Option (Lean.Expr × MachRead) := do
  let st ← instEntry res st
  let k := st.insts.size
  let (js, st) ← (kinds.zip args).foldlM (init := (([] : List Nat), st)) (oInstArg G env k)
  match st.insts.findIdx? (fun i => i.1 == c && i.2.1 == js) with
  | some k' => some (machInstOut k', st)
  | none => some (machInstOut k, { st with insts := st.insts.push (c, js, res),
                                           instFields := st.instFields.push "out" })

/-- `machInstanceS`'s first `foldlM` function (4091–4101). -/
def oInstSArg (G : OldFns) (env : List MachVal) :
    List Nat × MachRead → MixedGateBinder × Lean.Expr → Option (List Nat × MachRead)
  | (js, st), (kind, arg) => do
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

/-- `machInstanceS`'s second `foldlM` function (4103–4107). -/
def oInstSParam (G : OldFns) (env : List MachVal) :
    List Lean.Expr × MachRead → Lean.Expr → Option (List Lean.Expr × MachRead)
  | (ps, st), p => do
    let (p', st) ← G.conv env 0 p st
    some (ps ++ [p'], st)

/-- `machInstanceS` (4079–4117). -/
def oInstS (senv : StructEnv) (G : OldFns) (env : List MachVal) (c : Name)
    (kinds : List MixedGateBinder) (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead) :
    Option (Lean.Expr × MachRead) := do
  if st.inInner then none else
  let resTy ← instRes ty args
  let (some ctor, fields) ← machOuts? senv resTy | none
  if fields.isEmpty || fields.any (fun f => f.2 == .domain) then none else
  let (js, st) ← (kinds.zip args).foldlM (init := (([] : List Nat), st)) (oInstSArg G env)
  let (params, st) ← resTy.getAppArgs.toList.foldlM (init := (([] : List Lean.Expr), st))
    (oInstSParam G env)
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

/-- `machChain` (4124–4165). -/
def oChain (G : OldFns) : List MachVal → Lean.Expr → MachRead →
    Option (List (Nat × Lean.Expr) × Lean.Expr × MachRead)
  | env, .app (.app (.app (.app (.const ``Sparkle.Core.Circuit.pure' _) _) _) _) v, st =>
    match G.conv env 0 v st with
    | some (v', st) => some ([], v', st)
    | none => none
  | env, .app (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.bind _) _) _) _) _)
      (.app (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.next _) _) _) _) _)
        h) rhs)) (.lam _ _ rest _), st =>
    match machHandleV env 0 h, G.conv env 0 rhs st with
    | some i, some (rhs', st) =>
      if i < st.kinds.size then
        match G.chain (.unit :: env) rest st with
        | some (ws, v, st) => some ((i, rhs') :: ws, v, st)
        | none => none
      else none
    | _, _ => none
  | env, .letE nm ty v b nd, st =>
    match Sparkle.Compiler.MachRawSurface.rootFloat v with
    | .letE n2 t2 v2 w nd2 =>
      G.chain env
        (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2) st
    | v =>
    if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
      match G.loopRoot env v st with
      | some (mv, st) => G.chain (mv :: env) b st
      | none => none
    else
    match machTailV env 0 v with
    | some p => G.chain (.regs p :: env) b st
    | none =>
      match machHandleV env 0 v with
      | some i => G.chain (.handle i :: env) b st
      | none =>
        match G.conv env 0 v st with
        | some (v', st) =>
          let (x, lets) := machBindLet nm ty v' st.lets
          G.chain (.val x :: env) b { st with lets := lets }
        | none => none
  | _, _, _ => none

/-- `machLoopBody`'s `foldlM` function (4181–4184). -/
def oLoopNext (G : OldFns) (env : List MachVal) (base : Nat) :
    List (Nat × Lean.Expr) × MachRead → Lean.Expr × Lean.Expr × Lean.Expr →
      Option (List (Nat × Lean.Expr) × MachRead)
  | (ws, st), (_, _, nx) => do
    let (nx', st) ← G.conv env 0 nx st
    pure (ws ++ [(base + ws.length, nx')], st)

/-- `machLoopBody` (4171–4185). -/
def oLoopBody (G : OldFns) (base : Nat) :
    List MachVal → Lean.Expr → MachRead → Option MachRead
  | env, .letE nm ty v b _, st => do
    let (v', st) ← G.conv env 0 v st
    let (x, lets) := if machIsSlot v' then machBindLetNamed nm ty v' st.lets
      else if machIsLetVar v' then machBindLetAlias nm ty v' st.lets
      else machBindLet nm ty v' st.lets
    G.loopBody base (.val x :: env) b { st with lets := lets }
  | env, tail, st => do
    let regs ← machLoopRegs tail
    let (ws, st) ← regs.foldlM (init := (([] : List (Nat × Lean.Expr)), st)) (oLoopNext G env base)
    some { st with ws := st.ws ++ ws.toArray }

/-- `machLoopRoot`'s `findSome?` function (4207–4211). -/
def oLoopProbe (G : OldFns) (env : List MachVal) (body : Lean.Expr) (n : Nat) (st : MachRead) :
    Nat × Nat × List (Nat × Lean.Expr) → Option (Nat × MachRead)
  | (b0, n0, ws0) =>
    if n0 != n then none else
    match G.loopBody b0 (.state b0 n :: env) body { st with ws := #[] } with
    | some st' => if st'.ws.toList == ws0 then some (b0, { st' with ws := st.ws }) else none
    | none => none

/-- `machLoopRoot` (4193–4230). -/
def oLoopRoot (senv : StructEnv) (G : OldFns) (env : List MachVal) (e : Lean.Expr)
    (st : MachRead) : Option (MachVal × MachRead) := do
  let some (dom, body) := loopView? e | none
  if st.inInner then none else
  let regs ← machLoopRegs (machLetTail body)
  if regs.any loopRegBad then none else
  let kinds ← regs.mapM loopRegKind
  let inits ← (kinds.zip regs).mapM (loopRegInit senv.natOf)
  let (dom', st) ← G.conv env 0 dom st
  match st.dom with
  | some d0 => if d0 != dom' then none else pure ()
  | none => pure ()
  let n := kinds.length
  let shared := st.loopWs.findSome? (oLoopProbe G env body n st)
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

/-- The old texts, dispatched. -/
def oApp (senv : StructEnv) (G : OldFns) : (c : Call) → RB c
  | .conv env d e st => oConv senv G env d e st
  | .nested env dom αs initsE body st => oNested senv G env dom αs initsE body st
  | .inst env c kinds res args st => oInst G env c kinds res args st
  | .instS env c kinds ty args st => oInstS senv G env c kinds ty args st
  | .chain env e st => oChain G env e st
  | .loopBody base env e st => oLoopBody G base env e st
  | .loopRoot env e st => oLoopRoot senv G env e st

/-- **The old source equations of the block**, over a tuple. -/
def OldEq (senv : StructEnv) (G : OldFns) : Prop :=
  (∀ env d e st, G.conv env d e st = oConv senv G env d e st) ∧
  (∀ env dom αs initsE body st,
    G.nested env dom αs initsE body st = oNested senv G env dom αs initsE body st) ∧
  (∀ env c kinds res args st, G.inst env c kinds res args st = oInst G env c kinds res args st) ∧
  (∀ env c kinds ty args st,
    G.instS env c kinds ty args st = oInstS senv G env c kinds ty args st) ∧
  (∀ env e st, G.chain env e st = oChain G env e st) ∧
  (∀ base env e st, G.loopBody base env e st = oLoopBody G base env e st) ∧
  (∀ env e st, G.loopRoot env e st = oLoopRoot senv G env e st)

theorem oldEq_app {senv : StructEnv} {G : OldFns} (h : OldEq senv G) :
    ∀ c, G.app c = oApp senv G c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  intro c
  cases c with
  | conv env d e st => exact h1 env d e st
  | nested env dom αs initsE body st => exact h2 env dom αs initsE body st
  | inst env c kinds res args st => exact h3 env c kinds res args st
  | instS env c kinds ty args st => exact h4 env c kinds ty args st
  | chain env e st => exact h5 env e st
  | loopBody base env e st => exact h6 base env e st
  | loopRoot env e st => exact h7 env e st

/-! ## Rewriting a run -/

section Run
variable {κ : Type} {R : κ → Type} {α β : Type}

-- `run_pure`, `run_bind`, `run_bindO`: `Tools/ShippingReaderFuelRun.lean`
-- (moved there by worker R5, same names, same namespace, same statements).

theorem run_call (h : (c : κ) → Option (R c)) (c : κ) :
    (FM.call c : FM κ R (R c)).run h = h c := rfl

theorem run_okO (h : (c : κ) → Option (R c)) (a : α) :
    (okO a : FM κ R (Option α)).run h = some (some a) := rfl

theorem run_failO (h : (c : κ) → Option (R c)) :
    (failO : FM κ R (Option α)).run h = some none := rfl

theorem run_optK (h : (c : κ) → Option (R c)) (o : Option α) (f : α → FM κ R (Option β)) :
    (optK o f).run h = (match o with
      | some a => (f a).run h
      | none => some none) := by
  cases o <;> rfl

theorem run_ite (h : (c : κ) → Option (R c)) (p : Prop) [Decidable p] (x y : FM κ R α) :
    (if p then x else y).run h = if p then x.run h else y.run h :=
  apply_ite (fun z : FM κ R α => z.run h) p x y

theorem run_domGuard (h : (c : κ) → Option (R c)) (o : Option Lean.Expr) (dom' : Lean.Expr)
    (k : FM κ R (Option β)) :
    (domGuard o dom' k).run h = (match o with
      | some d0 => if d0 != dom' then some none else k.run h
      | none => k.run h) := by
  cases o with
  | none => rfl
  | some d0 =>
    show (if d0 != dom' then (FM.pure none : FM κ R (Option β)) else k).run h =
      (if d0 != dom' then some none else k.run h)
    rw [run_ite]
    rfl

theorem obind_match (x : Option α) (f : α → Option β) :
    x.bind f = (match x with
      | some a => f a
      | none => none) := by
  cases x <;> rfl

theorem obind_match' (x : Option α) (f : α → Option β) :
    (x >>= f) = (match x with
      | some a => f a
      | none => none) := by
  cases x <;> rfl

theorem opure (a : α) : (pure a : Option α) = some a := rfl

end Run

theorem run_foldO_eq {σ α : Type} {f : σ → α → BM (Option σ)} {g : σ → α → Option σ} (h : Hs)
    (hfg : ∀ s a, (f s a).run h = some (g s a)) :
    ∀ (l : List α) (s : σ), (foldO f s l).run h = some (l.foldlM g s)
  | [], s => rfl
  | a :: l, s => by
    rw [List.foldlM_cons]
    first
      | show (bindO (f s a) fun s' => foldO f s' l).run h = _
      | simp only [foldO]
    rw [run_bindO, hfg s a, Option.bind_some]
    cases hg : g s a with
    | none => rfl
    | some s' => exact run_foldO_eq h hfg l s'

theorem run_findSomeO_eq {α β : Type} {f : α → BM (Option β)} {g : α → Option β} (h : Hs)
    (hfg : ∀ a, (f a).run h = some (g a)) :
    ∀ l : List α, (findSomeO f l).run h = some (l.findSome? g)
  | [] => rfl
  | a :: l => by
    rw [List.findSome?_cons]
    first
      | simp only [findSomeO]
      | show (FM.bind (f a) fun o => match o with
          | some b => FM.pure (some b)
          | none => findSomeO f l).run h = _
    rw [run_bind, hfg a, Option.bind_some]
    cases hg : g a with
    | none => exact run_findSomeO_eq h hfg l
    | some b => rfl

/-! ## The bodies at the total table of a tuple -/

section Tot
variable (senv : StructEnv) (G : OldFns)

theorem run_cConv_tot (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead) :
    (cConv env d e st).run (tot G) = some (G.conv env d e st) := rfl
theorem run_cNested_tot (env : List MachVal) (dom αs initsE body : Lean.Expr) (st : MachRead) :
    (cNested env dom αs initsE body st).run (tot G) = some (G.nested env dom αs initsE body st) :=
  rfl
theorem run_cInst_tot (env : List MachVal) (c : Name) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) :
    (cInst env c kinds res args st).run (tot G) = some (G.inst env c kinds res args st) := rfl
theorem run_cInstS_tot (env : List MachVal) (c : Name) (kinds : List MixedGateBinder)
    (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead) :
    (cInstS env c kinds ty args st).run (tot G) = some (G.instS env c kinds ty args st) := rfl
theorem run_cChain_tot (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    (cChain env e st).run (tot G) = some (G.chain env e st) := rfl
theorem run_cLoopBody_tot (base : Nat) (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    (cLoopBody base env e st).run (tot G) = some (G.loopBody base env e st) := rfl
theorem run_cLoopRoot_tot (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    (cLoopRoot env e st).run (tot G) = some (G.loopRoot env e st) := rfl

end Tot

/-- Case analysis of a body against an old text at the total table: rewrite
every run, turn every `Option.bind` into a `match`, split every `match` /
`if` (both sides see the same discriminant), close each leaf by reduction. -/
macro "tot_crunch" : tactic => `(tactic| (
  repeat' (first
    | simp only [run_pure, run_bind, run_call, run_okO, run_failO, run_optK,
        run_bindO, run_ite, run_domGuard, run_cConv_tot, run_cNested_tot, run_cInst_tot,
        run_cInstS_tot, run_cChain_tot, run_cLoopBody_tot, run_cLoopRoot_tot,
        obind_match, obind_match', opure, Option.bind_some, Option.bind_none,
        Array.findSome?_toList]
    | split)
  all_goals first
    | rfl
    | (simp_all; done)
    | (subst_vars; rfl)))

section Arms
variable (senv : StructEnv) (G : OldFns)

theorem instArg_tot (env : List MachVal) (k : Nat) :
    ∀ s a, (instArg env k s a).run (tot G) = some (oInstArg G env k s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩
  simp only [instArg, oInstArg]
  tot_crunch

theorem instSArg_tot (env : List MachVal) :
    ∀ s a, (instSArg env s a).run (tot G) = some (oInstSArg G env s a) := by
  rintro ⟨js, st⟩ ⟨kind, arg⟩
  simp only [instSArg, oInstSArg]
  tot_crunch

theorem instSParam_tot (env : List MachVal) :
    ∀ s a, (instSParam env s a).run (tot G) = some (oInstSParam G env s a) := by
  rintro ⟨ps, st⟩ p
  simp only [instSParam, oInstSParam]
  tot_crunch

theorem loopNext_tot (env : List MachVal) (base : Nat) :
    ∀ s a, (loopNext env base s a).run (tot G) = some (oLoopNext G env base s a) := by
  rintro ⟨ws, st⟩ ⟨t, i, nx⟩
  simp only [loopNext, oLoopNext]
  tot_crunch

theorem nestedProbe_tot (env : List MachVal) (dom' αs initsE body : Lean.Expr) (st : MachRead) :
    ∀ a, (nestedProbe env dom' αs initsE body st a).run (tot G) =
      some (oNestedProbe G env dom' αs initsE body st a) := by
  rintro ⟨base, d, a, ini, ws, v⟩
  simp only [nestedProbe, oNestedProbe]
  tot_crunch

theorem loopProbe_tot (env : List MachVal) (body : Lean.Expr) (n : Nat) (st : MachRead) :
    ∀ a, (loopProbe env body n st a).run (tot G) = some (oLoopProbe G env body n st a) := by
  rintro ⟨b0, n0, ws0⟩
  simp only [loopProbe, oLoopProbe]
  tot_crunch

theorem foldO_instArg_tot (env : List MachVal) (k : Nat) (l : List (MixedGateBinder × Lean.Expr))
    (s : List Nat × MachRead) :
    (foldO (instArg env k) s l).run (tot G) = some (l.foldlM (oInstArg G env k) s) :=
  run_foldO_eq (tot G) (instArg_tot G env k) l s

theorem foldO_instSArg_tot (env : List MachVal) (l : List (MixedGateBinder × Lean.Expr))
    (s : List Nat × MachRead) :
    (foldO (instSArg env) s l).run (tot G) = some (l.foldlM (oInstSArg G env) s) :=
  run_foldO_eq (tot G) (instSArg_tot G env) l s

theorem foldO_instSParam_tot (env : List MachVal) (l : List Lean.Expr)
    (s : List Lean.Expr × MachRead) :
    (foldO (instSParam env) s l).run (tot G) = some (l.foldlM (oInstSParam G env) s) :=
  run_foldO_eq (tot G) (instSParam_tot G env) l s

theorem foldO_loopNext_tot (env : List MachVal) (base : Nat)
    (l : List (Lean.Expr × Lean.Expr × Lean.Expr)) (s : List (Nat × Lean.Expr) × MachRead) :
    (foldO (loopNext env base) s l).run (tot G) = some (l.foldlM (oLoopNext G env base) s) :=
  run_foldO_eq (tot G) (loopNext_tot G env base) l s

theorem findSomeO_nestedProbe_tot (env : List MachVal) (dom' αs initsE body : Lean.Expr)
    (st : MachRead) (l : List (Nat × Lean.Expr × Lean.Expr × Lean.Expr × List (Nat × Lean.Expr) ×
      Lean.Expr)) :
    (findSomeO (nestedProbe env dom' αs initsE body st) l).run (tot G) =
      some (l.findSome? (oNestedProbe G env dom' αs initsE body st)) :=
  run_findSomeO_eq (tot G) (nestedProbe_tot G env dom' αs initsE body st) l

theorem findSomeO_loopProbe_tot (env : List MachVal) (body : Lean.Expr) (n : Nat) (st : MachRead)
    (l : List (Nat × Nat × List (Nat × Lean.Expr))) :
    (findSomeO (loopProbe env body n st) l).run (tot G) =
      some (l.findSome? (oLoopProbe G env body n st)) :=
  run_findSomeO_eq (tot G) (loopProbe_tot G env body n st) l

end Arms

/-- The same case analysis with the `foldO` / `findSomeO` facts above. Used
(round 1, BUILT there) for the arms `nested`, `inst`, `instS`, `loopBody`. -/
macro "tot_crunch2" : tactic => `(tactic| (
  repeat' (first
    | simp only [run_pure, run_bind, run_call, run_okO, run_failO, run_optK,
        run_bindO, run_ite, run_domGuard, run_cConv_tot, run_cNested_tot, run_cInst_tot,
        run_cInstS_tot, run_cChain_tot, run_cLoopBody_tot, run_cLoopRoot_tot,
        foldO_instArg_tot, foldO_instSArg_tot, foldO_instSParam_tot, foldO_loopNext_tot,
        findSomeO_nestedProbe_tot, findSomeO_loopProbe_tot,
        obind_match, obind_match', opure, Option.bind_some, Option.bind_none,
        Array.findSome?_toList]
    | split)
  all_goals first
    | rfl
    | (simp_all; done)
    | (subst_vars; rfl)))

/-- **Aligned case analysis** (round 2; replaces `tot_crunch2` in the three
arms that failed in round 1).

`split` splits ONE `match` / `if` — the first one in the goal, i.e. the fuel
body's (left of `=`). The new hypothesis it introduces is the discriminant
equation of that branch (`X = some a`, `X = none`, `c`, `¬c`); the next
`simp only [*, …]` rewrites with it on BOTH sides, so the old text's own
`match` / `if` on the SAME discriminant `X` reduces in the same branch. Every
discriminant is split once per path (round 1's `tot_crunch2` split the two
sides' matches independently: a cross product whose mixed leaves are the
`some none` vs `some (some …)` goals of chain / loopRoot, and whose size
timed out on `conv`).

A catch-all alternative (`| v => …` of `rootFloat`, `| _, _ => …` of
`machChain`'s `next` arm, the outer `| _, _, _ => …`) leaves a negative
hypothesis `∀ …, X = pattern → False`; the old text's copy of that `match`
is split later and its contradictory branch is closed by applying the
negative hypothesis to the new discriminant equation (`solve_by_elim`). A
leaf where both sides are reduced and still differ is NOT closed by any of
the closers (none of them proves `some none = some (some _)` without a
contradictory hypothesis): it would be a real difference between the fuel
body and the old text and fails the build. -/
macro "tot_align" : tactic => `(tactic| (
  repeat' (first
    | simp only [*, run_pure, run_bind, run_call, run_okO, run_failO, run_optK,
        run_bindO, run_ite, run_domGuard, run_cConv_tot, run_cNested_tot, run_cInst_tot,
        run_cInstS_tot, run_cChain_tot, run_cLoopBody_tot, run_cLoopRoot_tot,
        foldO_instArg_tot, foldO_instSArg_tot, foldO_instSParam_tot, foldO_loopNext_tot,
        findSomeO_nestedProbe_tot, findSomeO_loopProbe_tot,
        obind_match, obind_match', opure, Option.bind_some, Option.bind_none,
        Array.findSome?_toList, ite_true, ite_false, eq_self_iff_true, Bool.false_eq_true,
        ↓reduceIte]
    | split)
  all_goals first
    | rfl
    | (exfalso; solve_by_elim)
    | contradiction
    | (subst_vars; rfl)
    | (simp_all; done)))

/-! ## The three arms that failed in round 1, decomposed

`conv` per constructor of the input expression, its `.app` arm per VIEW
(`regView?`, `machLoopRead?`, `machRunApp?`, `machInstCall?`,
`machInstCallS?`, `memCall?`, `machReadV`, default), its `.letE` arm per
constructor of `rootFloat v`; `chain` per constructor (`.app`: the `pure'` /
`next` arms; `.letE` per constructor of `rootFloat v`); `loopRoot` per
`loopView? e`. Each piece takes the discriminant equations of its case as
explicit hypotheses — the SAME term on both sides — which the first
`simp only [*, …]` of `tot_align` rewrites in the fuel body and in the old
text before any `split`. Expected time / goal counts per lemma:
`docs/parallel/R-reader-fuel.md` (round 2). -/

section Split
variable {senv : StructEnv} {G : OldFns} {env : List MachVal} {d : Nat} {st : MachRead}

/-! ### `conv`, `.app`, per view -/

set_option maxHeartbeats 400000 in
/-- View 1: a bare `Signal.register` (`regView? … = some _`). -/
theorem conv_app_reg {f a : Lean.Expr} {p : Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr}
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some p) :
    (convStep senv env d (.app f a) st).run (tot G) = some (oConv senv G env d (.app f a) st) := by
  obtain ⟨dom, α, init, x⟩ := p
  unfold convStep oConv
  tot_align

/-- View 2: a loop-state read. -/
theorem conv_app_loopRead {f a : Lean.Expr} {i : Nat}
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = some i) :
    (convStep senv env d (.app f a) st).run (tot G) = some (oConv senv G env d (.app f a) st) := by
  unfold convStep oConv
  tot_align

/-- View 3: a nested run (`machNested`). -/
theorem conv_app_run {f a : Lean.Expr} {p : Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr}
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none)
    (h3 : machRunApp? (.app f a) = some p) :
    (convStep senv env d (.app f a) st).run (tot G) = some (oConv senv G env d (.app f a) st) := by
  obtain ⟨dom, αs, initsE, body⟩ := p
  unfold convStep oConv
  tot_align

/-- View 4: a scalar-result instance (`machInstance`). -/
theorem conv_app_inst {f a : Lean.Expr}
    {p : Name × List MixedGateBinder × MixedGateBinder × List Lean.Expr}
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none)
    (h3 : machRunApp? (.app f a) = none)
    (h4 : machInstCall? senv (.app f a) = some p) :
    (convStep senv env d (.app f a) st).run (tot G) = some (oConv senv G env d (.app f a) st) := by
  obtain ⟨c, kinds, res, args⟩ := p
  unfold convStep oConv
  tot_align

/-- View 5: a structure-result instance (`machInstanceS`). -/
theorem conv_app_instS {f a : Lean.Expr}
    {p : Name × List MixedGateBinder × Lean.Expr × List Lean.Expr}
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none)
    (h3 : machRunApp? (.app f a) = none)
    (h4 : machInstCall? senv (.app f a) = none)
    (h5 : machInstCallS? senv (.app f a) = some p) :
    (convStep senv env d (.app f a) st).run (tot G) = some (oConv senv G env d (.app f a) st) := by
  obtain ⟨c, kinds, ty, args⟩ := p
  unfold convStep oConv
  tot_align

/-- View 6: a memory (a call of a memory-only child). -/
theorem conv_app_mem {f a : Lean.Expr} {p : Bool × Nat × Nat × Lean.Expr × List Lean.Expr}
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none)
    (h3 : machRunApp? (.app f a) = none)
    (h4 : machInstCall? senv (.app f a) = none)
    (h5 : machInstCallS? senv (.app f a) = none)
    (h6 : Sparkle.Compiler.MachMemory.memCall?
      (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = some p) :
    (convStep senv env d (.app f a) st).run (tot G) = some (oConv senv G env d (.app f a) st) := by
  obtain ⟨combo, aw, dw, dom, ops⟩ := p
  unfold convStep oConv
  tot_align

/-- View 7: a read of a value in the environment. -/
theorem conv_app_readV {f a : Lean.Expr} {i : Nat}
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none)
    (h3 : machRunApp? (.app f a) = none)
    (h4 : machInstCall? senv (.app f a) = none)
    (h5 : machInstCallS? senv (.app f a) = none)
    (h6 : Sparkle.Compiler.MachMemory.memCall?
      (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none)
    (h7 : machReadV env d (.app f a) = some i) :
    (convStep senv env d (.app f a) st).run (tot G) = some (oConv senv G env d (.app f a) st) := by
  unfold convStep oConv
  tot_align

/-- No view: the application, function and argument converted. -/
theorem conv_app_default {f a : Lean.Expr}
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none)
    (h3 : machRunApp? (.app f a) = none)
    (h4 : machInstCall? senv (.app f a) = none)
    (h5 : machInstCallS? senv (.app f a) = none)
    (h6 : Sparkle.Compiler.MachMemory.memCall?
      (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) = none)
    (h7 : machReadV env d (.app f a) = none) :
    (convStep senv env d (.app f a) st).run (tot G) = some (oConv senv G env d (.app f a) st) := by
  unfold convStep oConv
  tot_align

/-- The `.app` arm: dispatch on the seven views, in the order of the text. -/
theorem conv_app_tot {f a : Lean.Expr} :
    (convStep senv env d (.app f a) st).run (tot G) = some (oConv senv G env d (.app f a) st) := by
  cases h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs with
  | some p => exact conv_app_reg h1
  | none =>
    cases h2 : machLoopRead? env d (.app f a) with
    | some i => exact conv_app_loopRead h1 h2
    | none =>
      cases h3 : machRunApp? (.app f a) with
      | some p => exact conv_app_run h1 h2 h3
      | none =>
        cases h4 : machInstCall? senv (.app f a) with
        | some p => exact conv_app_inst h1 h2 h3 h4
        | none =>
          cases h5 : machInstCallS? senv (.app f a) with
          | some p => exact conv_app_instS h1 h2 h3 h4 h5
          | none =>
            cases h6 : Sparkle.Compiler.MachMemory.memCall?
                (fun e => canonicalNatLitValue? e <|> senv.natOf e) (.app f a) with
            | some p => exact conv_app_mem h1 h2 h3 h4 h5 h6
            | none =>
              cases h7 : machReadV env d (.app f a) with
              | some i => exact conv_app_readV h1 h2 h3 h4 h5 h6 h7
              | none => exact conv_app_default h1 h2 h3 h4 h5 h6 h7

/-! ### `conv`, binders and `let` -/

theorem conv_lam_tot {nm : Name} {t b : Lean.Expr} {bi : BinderInfo} :
    (convStep senv env d (.lam nm t b bi) st).run (tot G) =
      some (oConv senv G env d (.lam nm t b bi) st) := by
  unfold convStep oConv
  tot_align

theorem conv_forallE_tot {nm : Name} {t b : Lean.Expr} {bi : BinderInfo} :
    (convStep senv env d (.forallE nm t b bi) st).run (tot G) =
      some (oConv senv G env d (.forallE nm t b bi) st) := by
  unfold convStep oConv
  tot_align

set_option maxHeartbeats 1600000 in
/-- The `.letE` arm, per constructor of `rootFloat v` (the discriminant of the
catch-all `match` of both texts: `| .letE … => … | v => …`). In each case
`hR : rootFloat v = <constructor>` reduces both `match`es; no negative
hypothesis is left. -/
theorem conv_letE_tot {nm : Name} {ty v b : Lean.Expr} {nd : Bool} :
    (convStep senv env d (.letE nm ty v b nd) st).run (tot G) =
      some (oConv senv G env d (.letE nm ty v b nd) st) := by
  cases hR : Sparkle.Compiler.MachRawSurface.rootFloat v <;>
    (unfold convStep oConv; tot_align)

/-! ### `chain` -/

set_option maxHeartbeats 800000 in
/-- The `.app` inputs: the `pure'` and `next` arms and the catch-all. -/
theorem chain_app_tot {g x : Lean.Expr} :
    (chainStep senv env (.app g x) st).run (tot G) = some (oChain G env (.app g x) st) := by
  unfold chainStep oChain
  tot_align

set_option maxHeartbeats 1600000 in
/-- The `.letE` arm, per constructor of `rootFloat v` (as `conv_letE_tot`). -/
theorem chain_letE_tot {nm : Name} {ty v b : Lean.Expr} {nd : Bool} :
    (chainStep senv env (.letE nm ty v b nd) st).run (tot G) =
      some (oChain G env (.letE nm ty v b nd) st) := by
  cases hR : Sparkle.Compiler.MachRawSurface.rootFloat v <;>
    (unfold chainStep oChain; tot_align)

/-! ### `loopRoot` -/

theorem loopRoot_none {e : Lean.Expr} (hv : loopView? e = none) :
    (loopRootStep senv env e st).run (tot G) = some (oLoopRoot senv G env e st) := by
  simp only [loopRootStep, oLoopRoot]
  tot_align

set_option maxHeartbeats 800000 in
theorem loopRoot_some {e : Lean.Expr} {p : Lean.Expr × Lean.Expr} (hv : loopView? e = some p) :
    (loopRootStep senv env e st).run (tot G) = some (oLoopRoot senv G env e st) := by
  obtain ⟨dom, body⟩ := p
  simp only [loopRootStep, oLoopRoot]
  tot_align

end Split

section Arms2
variable (senv : StructEnv) (G : OldFns)

theorem conv_tot (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead) :
    (convStep senv env d e st).run (tot G) = some (oConv senv G env d e st) := by
  cases e with
  | bvar j => rfl
  | mdata m x => rfl
  | proj s i x => rfl
  | fvar x => rfl
  | mvar x => rfl
  | sort u => rfl
  | const n us => rfl
  | lit l => rfl
  | app f a => exact conv_app_tot
  | lam nm t b bi => exact conv_lam_tot
  | forallE nm t b bi => exact conv_forallE_tot
  | letE nm ty v b nd => exact conv_letE_tot

theorem nested_tot (env : List MachVal) (dom αs initsE body : Lean.Expr) (st : MachRead) :
    (nestedStep senv env dom αs initsE body st).run (tot G) =
      some (oNested senv G env dom αs initsE body st) := by
  simp only [nestedStep, oNested]
  tot_crunch2

theorem inst_tot (env : List MachVal) (c : Name) (kinds : List MixedGateBinder)
    (res : MixedGateBinder) (args : List Lean.Expr) (st : MachRead) :
    (instStep env c kinds res args st).run (tot G) = some (oInst G env c kinds res args st) := by
  simp only [instStep, oInst]
  tot_crunch2

theorem instS_tot (env : List MachVal) (c : Name) (kinds : List MixedGateBinder)
    (ty : Lean.Expr) (args : List Lean.Expr) (st : MachRead) :
    (instSStep senv env c kinds ty args st).run (tot G) =
      some (oInstS senv G env c kinds ty args st) := by
  simp only [instSStep, oInstS]
  tot_crunch2

theorem chain_tot (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    (chainStep senv env e st).run (tot G) = some (oChain G env e st) := by
  cases e with
  | app g x => exact chain_app_tot
  | letE nm ty v b nd => exact chain_letE_tot
  | _ => rfl

theorem loopBody_tot (base : Nat) (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    (loopBodyStep base env e st).run (tot G) = some (oLoopBody G base env e st) := by
  unfold loopBodyStep oLoopBody
  tot_crunch2

theorem loopRoot_tot (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    (loopRootStep senv env e st).run (tot G) = some (oLoopRoot senv G env e st) := by
  cases hv : loopView? e with
  | none => exact loopRoot_none hv
  | some p => exact loopRoot_some hv

/-- **The body at the total table of ANY tuple is the old text at that
tuple.** -/
theorem step_tot : ∀ c, (step senv c).run (tot G) = some (oApp senv G c)
  | .conv env d e st => conv_tot senv G env d e st
  | .nested env dom αs initsE body st => nested_tot senv G env dom αs initsE body st
  | .inst env c kinds res args st => inst_tot G env c kinds res args st
  | .instS env c kinds ty args st => instS_tot senv G env c kinds ty args st
  | .chain env e st => chain_tot senv G env e st
  | .loopBody base env e st => loopBody_tot G base env e st
  | .loopRoot env e st => loopRoot_tot senv G env e st

end Arms2

/-- **Every solution of the old source equations solves the body's
equation.** -/
theorem isSol_of_oldEq {senv : StructEnv} {G : OldFns} (h : OldEq senv G) :
    IsSol (step senv) G.app := fun c =>
  (step_tot senv G c).trans (congrArg some (oldEq_app h c).symm)

/-- **Agreement with the old reader's source equations** (block): a non-OUT
answer of the fuel candidate at ANY fuel is the value of EVERY tuple solving
the old source equations — the old `some r` and the old `none` alike.
Conditional on `OldEq senv G`: that the compiled `partial` constants form
such a tuple is outside the kernel. -/
theorem readF_agree_old {senv : StructEnv} {G : OldFns} (h : OldEq senv G) {n : Nat} {c : Call}
    {r : RB c} (hr : readF senv n c = some r) : G.app c = r :=
  readF_agree senv G.app (isSol_of_oldEq h) hr

theorem machConvF_agree_old {senv : StructEnv} {G : OldFns} (h : OldEq senv G) {n : Nat}
    {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead}
    {r : Option (Lean.Expr × MachRead)} (hr : machConvF n senv env d e st = some r) :
    G.conv env d e st = r :=
  readF_agree_old h hr

theorem machChainF_agree_old {senv : StructEnv} {G : OldFns} (h : OldEq senv G) {n : Nat}
    {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {r : Option (List (Nat × Lean.Expr) × Lean.Expr × MachRead)}
    (hr : machChainF n senv env e st = some r) : G.chain env e st = r :=
  readF_agree_old h hr

theorem machLoopRootF_agree_old {senv : StructEnv} {G : OldFns} (h : OldEq senv G) {n : Nat}
    {env : List MachVal} {e : Lean.Expr} {st : MachRead} {r : Option (MachVal × MachRead)}
    (hr : machLoopRootF n senv env e st = some r) : G.loopRoot env e st = r :=
  readF_agree_old h hr

/-! ## `machNorm` -/

/-- `machNorm` (4957–4986), the recursive call `g`. -/
def oNorm (senv : StructEnv) (g : Lean.Expr → Lean.Expr) : Lean.Expr → Lean.Expr
  | e@(.app f a) =>
    match ashrView? e.getAppFn e.getAppArgs with
    | some (dom, nE, x, y) =>
      match canonicalNatLitValue? nE with
      | some n =>
        if n == 0 then e else
        Sparkle.Compiler.MachSignOps.ashrE inlNatLit
          (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b)
          dom n (g x) (g y)
      | none => e
    | none =>
    match Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch e with
    | some e' => g e'
    | none => machNormNode senv (.app (g f) (g a))
  | .lam n t b bi => .lam n t (g b) bi
  | .letE n t v b nd =>
    if t.isConstOf ``Nat then g (b.instantiate1 v)
    else if (machBits? t).isSome && !v.hasLooseBVars then g (b.instantiate1 v)
    else .letE n t (g v) (g b) nd
  | e => e

/-- **The old source equation of `machNorm`.** -/
def OldEqN (senv : StructEnv) (g : Lean.Expr → Lean.Expr) : Prop :=
  ∀ e, g e = oNorm senv g e

theorem normStep_tot (senv : StructEnv) (g : Lean.Expr → Lean.Expr) (e : Lean.Expr) :
    (normStep senv e).run (fun e => some (g e)) = some (oNorm senv g e) := by
  cases e with
  | app f a =>
    simp only [normStep, oNorm]
    repeat' (first
      | simp only [run_pure, run_bind, run_call, run_ite, Option.bind_some]
      | split)
    all_goals first
      | rfl
      | (simp_all; done)
  | lam n t b bi => rfl
  | letE n t v b nd =>
    simp only [normStep, oNorm]
    repeat' (first
      | simp only [run_pure, run_bind, run_call, run_ite, Option.bind_some]
      | split)
    all_goals first
      | rfl
      | (simp_all; done)
  | bvar j => rfl
  | fvar x => rfl
  | mvar x => rfl
  | sort u => rfl
  | const n us => rfl
  | forallE n t b bi => rfl
  | lit l => rfl
  | mdata m x => rfl
  | proj s i x => rfl

theorem isSolN_of_oldEqN {senv : StructEnv} {g : Lean.Expr → Lean.Expr} (h : OldEqN senv g) :
    IsSol (normStep senv) g := fun e =>
  (normStep_tot senv g e).trans (congrArg some (h e).symm)

/-- **Agreement of the fuel `machNorm`** with every solution of the old
source equation (conditional on `OldEqN senv g`, as `readF_agree_old`). -/
theorem machNormF_agree_old {senv : StructEnv} {g : Lean.Expr → Lean.Expr} (h : OldEqN senv g)
    {n : Nat} {e r : Lean.Expr} (hr : machNormF n senv e = some r) : g e = r :=
  machNormF_agree senv g (isSolN_of_oldEqN h) hr

end Tools.ShippingReaderFuel
