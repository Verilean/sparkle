import Tools.ShippingReaderFuelKleene

/-! # A fuel version of the reader wrapper `machineShape?` (three-valued)

STATUS 2026-10-19 (worker O, branch `par/o-cand`): BUILT (integration run ig4, exit 0) against
the patched compiler (explicit call-entry origin, `MachRead.instOrigins`).
`shapePost` copies the patched record: `instOrigins := st.instOrigins.toList`.

BUILT on poc 65eaccbb (run `f1`; header status corrected 2026-10-16, comment
only) (worker F, branch `par/r-9`; record
`docs/parallel/R-reader-fuel-driver.md`). No `sorry`, no axiom, no
`native_decide`. NOTHING here is imported by `Sparkle/Compiler/Elab.lean`;
the real compiler path is unchanged (`machineShape?` and the `partial def`s
are not edited, nothing that calls them is).

`machineShapeF n … : Option (Option MachineShape)`:
`none` = OUT (fuel exhausted somewhere), `some none` = FAIL (the old
`none`), `some (some s)` = OK (the old `some s`).

## Design

* **One fuel for the whole wrapper.** The wrapper reads two kinds of
  recursive answers: `machNorm` (an expression) and the seven-function block
  (`machConv` ×2, `machLoopRoot`, `machChain` — six reader calls counting
  `machNorm`). Both are calls of ONE call type `WCall` (`norm e` / `blk c`),
  answered by ONE table `wtab senv n` (`machNormF n` / `readF n`). The wrapper
  is a computation `shapeW : FM WCall WCall.Res _` — monotone by construction
  (`FM`, `Tools/ShippingReaderFuelDefs.lean`) — run against that table.
  The wrapper itself does not consume fuel: fuel only bounds the depth of
  the recursive readers it calls.
* **Pure fragments are the source text** (Elab.lean 5059–5186):
  `shapePre` (5061–5072, up to the `machNorm` call), `shapeMid`
  (5075–5096, after it, pure), `shapePost` (5132–5185, after the last reader
  call). The reader part (5097–5131) is `shapeStart` / `shapeRootLet` /
  `shapeBody`, in the old order (FAIL of an earlier step wins over a later
  step; `foldO` stops at the first FAIL like `foldlM`).
* **OUT is never FAIL.** OUT is the outer `Option`, propagated by `FM.bind`
  only. In the sharing searches (`findSomeO`, `machNested` / `machLoopRoot`
  probes) a probe's OUT is OUT of the whole search (`findSomeO_out_cons`,
  `findSomeO_out_append`, `nestedStep_out_of_search`); a FAILED search means
  EVERY probe FAILED (`findSomeO_fail_all`) — "not shared" is never read off
  an OUT.

## Lemmas

* `wtab_mono`, `machineShapeF_stable`, `machineShapeF_det`,
  `machineShapeF_out_le` (stability of non-OUT answers across fuel via
  `readF_stable` / `machNormF_stable`; OUT at `m` ⇒ OUT at every `n ≤ m`);
* `machineShapeF_of_pre_none` (an ordinary refusal before the first reader
  call is FAIL at EVERY fuel, `0` included) and `machineShapeF_zero`
  (otherwise fuel `0` is OUT — a driver must start above `0`);
* OUT propagation: `FM.bind_run_out`, `bindO_run_out`, `bindO_run_ok`,
  `findSomeO_*`, `nestedStep_out_of_search`. -/
namespace Tools.ShippingReaderFuel
open Lean
open Sparkle.Compiler.Elab

/-! ## One call type for the wrapper -/

/-- A recursive answer the wrapper reads: a `machNorm` call or a call of the
seven-function block. -/
inductive WCall where
  | norm (e : Lean.Expr)
  | blk (c : Call)

@[reducible] def WCall.Res : WCall → Type
  | .norm _ => Lean.Expr
  | .blk c => RB c

/-- Computations of the wrapper. -/
abbrev WM (α : Type) := FM WCall WCall.Res α

/-- The wrapper's table at fuel `n` (`none` = OUT). -/
def wtab (senv : StructEnv) (n : Nat) : (c : WCall) → Option (WCall.Res c)
  | .norm e => machNormF n senv e
  | .blk c => readF senv n c

def wNorm (e : Lean.Expr) : WM Lean.Expr :=
  FM.call (WCall.norm e)

def wConv (env : List MachVal) (d : Nat) (e : Lean.Expr) (st : MachRead) :
    WM (Option (Lean.Expr × MachRead)) :=
  FM.call (WCall.blk (Call.conv env d e st))

def wChain (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    WM (Option (List (Nat × Lean.Expr) × Lean.Expr × MachRead)) :=
  FM.call (WCall.blk (Call.chain env e st))

def wLoopRoot (env : List MachVal) (e : Lean.Expr) (st : MachRead) :
    WM (Option (MachVal × MachRead)) :=
  FM.call (WCall.blk (Call.loopRoot env e st))

/-! ## The pure fragments (source text) -/

/-- What the wrapper has before its `machNorm` call. -/
structure ShapePre where
  d : DefinitionVal
  bs : List (Name × MixedGateBinder)
  e : Lean.Expr
  tup? : Option (List MixedGateBinder)
  ctor? : Option Name
  outs : List (String × MixedGateBinder)

/-- `machineShape?` 5061–5072: up to the `machNorm` call. -/
def shapePre (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : ConstantInfo)
    (senv : StructEnv) : Option ShapePre :=
  match ci with
  | .defnInfo d =>
    if symbolicMode || !parameters.isEmpty then none else do
    -- a tuple-typed input is one packed port (`MachTupleIn`)
    let (bs, e) ← mixedGatePeel (Sparkle.Compiler.MachTupleIn.packTupleInputs d.value)
    -- a tuple result is ONE port `out`, the components packed
    let tup? := machTupleKinds? d.type
    let (ctor?, outs) ← match tup? with
      | some ks => some (none, [("out", MixedGateBinder.bits (ks.map machWidth).sum)])
      | none => machOuts? senv d.type
    if outs.isEmpty || !outs.all (fun o => Sparkle.IR.Machine.outNameOk o.1) ||
        !decide (outs.map (·.1)).Nodup then none else
    pure { d := d, bs := bs, e := e, tup? := tup?, ctor? := ctor?, outs := outs }
  | _ => none

/-- What the wrapper has after its `machNorm` call (pure). -/
structure ShapeMid where
  rootLets : List (Name × Lean.Expr × Lean.Expr)
  sel : Option (Name × Nat × Nat)
  root : Lean.Expr
  wrap? : Option (Lean.Expr × Array Lean.Expr)
  /-- The enclosing run, already through `machRunApp?` (5096). -/
  run? : Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr)

/-- `machineShape?` 5075–5096 on the normalised body `en` (`machNorm senv e`). -/
def shapeMid (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : ShapeMid :=
  let e := machLoopAsLet (Sparkle.Compiler.MachRawSurface.rootFloat
    (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue?
      (inlFoldNat en)))
  let (rootLets, sel, run?, root) := machRoot senv.proj e []
  let wrap? : Option (Lean.Expr × Array Lean.Expr) := match run?, p.ctor? with
    | none, some c =>
      if root.getAppFn.isConstOf c && p.outs.length == 1 then
        let args := root.getAppArgs
        match args.back? with
        | some r => if (machRunApp? r).isSome then some (root.getAppFn, args.pop) else none
        | none => none
      else none
    | _, _ => none
  let run? := match wrap? with
    | some _ => root.getAppArgs.back?
    | none => run?
  { rootLets := rootLets, sel := sel, root := root, wrap? := wrap?,
    run? := run?.bind machRunApp? }

/-- `machineShape?` 5132–5185: after the last reader call. -/
def shapePost (allowInsts : Bool) (p : ShapePre) (m : ShapeMid) (st : MachRead) (v : Lean.Expr) :
    Option MachineShape := do
  let n := st.kinds.size
  if n = 0 && ((!st.insts.isEmpty && !st.instStruct) || !st.loops.isEmpty ||
      !st.runs.isEmpty) then none else
  if !allowInsts && !st.insts.isEmpty then none else
  if !st.loops.isEmpty && st.runs.isEmpty &&
      ((!st.insts.isEmpty && !st.instStruct) || st.loops.size != 1 + st.nestedLoops) then
    none else
  let kinds := st.kinds.toList
  let k := st.lets.size
  let kI := st.insts.size
  let domE ← st.dom <|> machTypeDom? p.d.type
  let (dom', resetKind) ← machDom? (kI + n + k) domE
  let letFields ← st.lets.toList.mapM fun (_, kind, value) =>
    machField dom' kind (machClose kI n k 0 value)
  let outFields ← match p.tup? with
    | some ks => do
      let parts ← machBundleParts? ks.length v
      let fs ← (ks.zip parts).mapM fun (kind, q) => machField dom' kind (machClose kI n k 0 q)
      let packed ← machPack dom' fs
      pure [packed]
    | none => do
      let outEs ← machResults? m.sel p.ctor? p.outs.length v
      if outEs.length != p.outs.length then none else
      (p.outs.zip outEs).mapM fun ((_, kind), outE) =>
        machField dom' kind (machClose kI n k 0 outE)
  let slotFields ← ((List.range n).zip kinds).mapM fun (i, kind) =>
    machField dom' kind (machClose kI n k 0 (machNext i st.ws.toList))
  let (_, packed) ← machPack dom' (letFields ++ outFields ++ slotFields)
  let body := machCanonAp packed
  let instBinders := (List.range kI).zip (st.insts.toList.map (·.2.2)) |>.map
    fun (j, kind) => (Name.mkSimple s!"inst{j}", kind)
  let binders : List (Name × MixedGateBinder) := p.bs ++ instBinders ++
    (st.names.toList.zip kinds) ++ st.lets.toList.map fun (nm, kind, _) => (nm, kind)
  if unifiedGateRoot (binders.map (·.2)).toArray body then
    some
      { binders := binders
        body := body
        layout :=
          { slots := machSlotFields ((kinds.map machWidth).zip st.inits.toList)
            outs := machOutFields (kinds.map machWidth).sum p.outs
            resetKind := resetKind
            lets := k }
        runs := st.runs.toList
        insts := st.insts.toList
        instFields := if st.instStruct then st.instFields.toList else []
        instOrigins := st.instOrigins.toList
        loops := st.loops.toList }
  else none

/-! ## The reader part (5097–5131; a recursive call is a table read) -/

/-- 5097–5104: the enclosing machine's slots first. -/
def shapeStart (senv : StructEnv) (m : ShapeMid) : WM (Option MachRead) :=
  match m.run? with
  | some (dom, αs, initsE, body) =>
    bindO (wConv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead)) fun (dom', _) =>
    optK (machReserve senv.natOf dom' αs initsE body ({} : MachRead)) fun (_, st) => okO st
  | none => okO ({} : MachRead)

/-- 5106–5120: the `foldlM` function over the root lets. -/
def shapeRootLet (senv : StructEnv) :
    List MachVal × MachRead → Name × Lean.Expr × Lean.Expr →
      WM (Option (List MachVal × MachRead))
  | (env, st), (nm, ty, v) =>
    if v.isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 then
      bindO (wLoopRoot env v st) fun (mv, st) => okO (mv :: env, st)
    else
    match machTailV env 0 v, machHandleV env 0 v with
    | none, none =>
      bindO (wConv env 0 v st) fun (v', st) =>
      let (x, lets) := if !st.loops.isEmpty && machIsSlot v' then machBindLetNamed nm ty v' st.lets
        else machBindLet nm ty v' st.lets
      okO (MachVal.val x :: env, { st with lets := lets })
    | _, _ => failO

/-- 5122–5131: the enclosing machine's chain, or the root expression. -/
def shapeBody (m : ShapeMid) (env : List MachVal) (st : MachRead) :
    WM (Option (MachRead × Lean.Expr)) :=
  match m.run? with
  | some (_, _, _, body) =>
    bindO (wChain (MachVal.regs 0 :: env) body st) fun (ws, v, st) =>
    let v := match m.wrap? with
      | some (c, params) => mkAppN c (params.push v)
      | none => v
    okO ({ st with ws := st.ws ++ ws.toArray }, v)
  | none =>
    bindO (wConv env 0 m.root st) fun (v, st) => okO (st, v)

/-- **The wrapper as one monotone computation.** -/
def shapeW (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : ConstantInfo)
    (senv : StructEnv) (allowInsts : Bool) : WM (Option MachineShape) :=
  optK (shapePre symbolicMode parameters ci senv) fun p =>
  FM.bind (wNorm p.e) fun en =>
  let m := shapeMid senv p en
  bindO (shapeStart senv m) fun st =>
  bindO (foldO (shapeRootLet senv) (([] : List MachVal), st) m.rootLets) fun (env, st) =>
  bindO (shapeBody m env st) fun (st, v) =>
  FM.pure (shapePost allowInsts p m st v)

/-- **The total wrapper at fuel `n`.** `none` = OUT, `some none` = the old
`none`, `some (some s)` = the old `some s`. -/
def machineShapeF (n : Nat) (symbolicMode : Bool) (parameters : List (String × Nat))
    (ci : ConstantInfo) (senv : StructEnv) (allowInsts : Bool := true) :
    Option (Option MachineShape) :=
  (shapeW symbolicMode parameters ci senv allowInsts).run (wtab senv n)

/-! ## Stability across fuel -/

theorem wtab_mono (senv : StructEnv) {n m : Nat} (hnm : n ≤ m) :
    HLe (wtab senv n) (wtab senv m) := by
  intro c r h
  cases c with
  | norm e =>
    have h' : machNormF n senv e = some r := h
    exact machNormF_stable h' hnm
  | blk c =>
    have h' : readF senv n c = some r := h
    exact readF_stable senv h' hnm

section Wrapper
variable {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo} {senv : StructEnv}
  {ai : Bool}

/-- **Stability**: a non-OUT answer of the wrapper is its answer at every
larger fuel. -/
theorem machineShapeF_stable {n m : Nat} {r : Option MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some r) (hnm : n ≤ m) :
    machineShapeF m sm ps ci senv ai = some r :=
  (shapeW sm ps ci senv ai).mono _ _ (wtab_mono senv hnm) r h

/-- **Fuel independence**: two non-OUT answers are the same answer. -/
theorem machineShapeF_det {n m : Nat} {r r' : Option MachineShape}
    (h : machineShapeF n sm ps ci senv ai = some r)
    (h' : machineShapeF m sm ps ci senv ai = some r') : r = r' := by
  rcases Nat.le_total n m with hnm | hmn
  · have h2 := machineShapeF_stable h hnm
    rw [h'] at h2
    exact (Option.some.inj h2).symm
  · have h2 := machineShapeF_stable h' hmn
    rw [h] at h2
    exact Option.some.inj h2

/-- OUT at `m` is OUT at every smaller fuel. -/
theorem machineShapeF_out_le {n m : Nat}
    (h : machineShapeF m sm ps ci senv ai = none) (hnm : n ≤ m) :
    machineShapeF n sm ps ci senv ai = none := by
  cases hn : machineShapeF n sm ps ci senv ai with
  | none => rfl
  | some r =>
    have h2 := machineShapeF_stable hn hnm
    rw [h] at h2
    cases h2

/-- An ordinary refusal before the first reader call (not a definition,
symbolic mode, parameters, binders, outputs) is FAIL at EVERY fuel. -/
theorem machineShapeF_of_pre_none (n : Nat) (hpre : shapePre sm ps ci senv = none) :
    machineShapeF n sm ps ci senv ai = some none := by
  unfold machineShapeF shapeW
  rw [hpre]
  all_goals rfl

/-- Otherwise fuel `0` is OUT (the `machNorm` call is not answered): a
driver must start above `0`. -/
theorem machineShapeF_zero {p : ShapePre} (hpre : shapePre sm ps ci senv = some p) :
    machineShapeF 0 sm ps ci senv ai = none := by
  unfold machineShapeF shapeW
  rw [hpre]
  all_goals rfl

end Wrapper

/-! ## OUT propagation (never read as FAIL / "not shared") -/

section Out
variable {κ : Type} {R : κ → Type} {α β : Type}

theorem FM.bind_run_out {x : FM κ R α} {f : α → FM κ R β} {h : (c : κ) → Option (R c)}
    (hx : x.run h = none) : (FM.bind x f).run h = none := by
  show Option.bind (x.run h) (fun a => (f a).run h) = none
  rw [hx]
  all_goals rfl

theorem bindO_run_out {x : FM κ R (Option α)} {f : α → FM κ R (Option β)}
    {h : (c : κ) → Option (R c)} (hx : x.run h = none) : (bindO x f).run h = none :=
  FM.bind_run_out hx

theorem bindO_run_ok {x : FM κ R (Option α)} {f : α → FM κ R (Option β)}
    {h : (c : κ) → Option (R c)} {a : α} (hx : x.run h = some (some a)) :
    (bindO x f).run h = (f a).run h := by
  show Option.bind (x.run h) (fun o => (optK o f).run h) = (f a).run h
  rw [hx]
  all_goals rfl

/-- A probe's OUT is OUT of the whole search. -/
theorem findSomeO_out_cons {f : α → FM κ R (Option β)} {h : (c : κ) → Option (R c)}
    {a : α} {as : List α} (hfa : (f a).run h = none) : (findSomeO f (a :: as)).run h = none := by
  first
    | exact FM.bind_run_out hfa
    | (simp only [findSomeO]; exact FM.bind_run_out hfa)

/-- A probe's FAIL is "not this one": the search goes on. -/
theorem findSomeO_fail_cons {f : α → FM κ R (Option β)} {h : (c : κ) → Option (R c)}
    {a : α} {as : List α} (hfa : (f a).run h = some none) :
    (findSomeO f (a :: as)).run h = (findSomeO f as).run h := by
  first
    | (show Option.bind ((f a).run h) _ = _
       rw [hfa]
       all_goals rfl)
    | simp [findSomeO, FM.bind, hfa]

/-- A probe's hit is the search's answer. -/
theorem findSomeO_hit_cons {f : α → FM κ R (Option β)} {h : (c : κ) → Option (R c)}
    {a : α} {as : List α} {b : β} (hfa : (f a).run h = some (some b)) :
    (findSomeO f (a :: as)).run h = some (some b) := by
  first
    | (show Option.bind ((f a).run h) _ = _
       rw [hfa]
       all_goals rfl)
    | simp [findSomeO, FM.bind, FM.pure, hfa]

/-- An OUT probe after FAILED probes makes the search OUT: it is never
skipped. -/
theorem findSomeO_out_append {f : α → FM κ R (Option β)} {h : (c : κ) → Option (R c)}
    {a : α} {as : List α} :
    ∀ (pre : List α), (∀ b ∈ pre, (f b).run h = some none) → (f a).run h = none →
      (findSomeO f (pre ++ a :: as)).run h = none := by
  intro pre
  induction pre with
  | nil => intro _ ha; exact findSomeO_out_cons ha
  | cons b pre ih =>
    intro hpre ha
    rw [List.cons_append, findSomeO_fail_cons (hpre b (by simp))]
    exact ih (fun c hc => hpre c (by simp [hc])) ha

/-- **A FAILED search FAILED every probe**: "not shared" is never read off
an OUT (nor off a hit). -/
theorem findSomeO_fail_all {f : α → FM κ R (Option β)} {h : (c : κ) → Option (R c)} :
    ∀ (l : List α), (findSomeO f l).run h = some none → ∀ a ∈ l, (f a).run h = some none := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons b l ih =>
    intro hl a ha
    cases hb : (f b).run h with
    | none =>
      rw [findSomeO_out_cons hb] at hl
      simp at hl
    | some o =>
      cases o with
      | some x =>
        rw [findSomeO_hit_cons hb] at hl
        simp at hl
      | none =>
        rw [findSomeO_fail_cons hb] at hl
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact hb
        · exact ih hl a ha'

end Out

/-- `machNested`: an OUT sharing search (after the domain was read) makes the
call OUT — the fresh sub-machine branch is never taken on an OUT. -/
theorem nestedStep_out_of_search {senv : StructEnv} {env : List MachVal}
    {dom αs initsE body : Lean.Expr} {st : MachRead} {h : Hs} {dom' : Lean.Expr} {st' : MachRead}
    (hin : st.inInner = false)
    (hconv : (cConv env 0 dom st).run h = some (some (dom', st')))
    (hs : (findSomeO (nestedProbe env dom' αs initsE body st') st'.nested.toList).run h = none) :
    (nestedStep senv env dom αs initsE body st).run h = none := by
  have hc : ¬ (st.inInner = true) := by simp [hin]
  unfold nestedStep
  rw [if_neg hc, bindO_run_ok hconv]
  exact FM.bind_run_out hs

end Tools.ShippingReaderFuel
