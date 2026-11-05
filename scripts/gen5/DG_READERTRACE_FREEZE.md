# DG-READERTRACE freeze rev0 — trace invariant of the fuel reader `readF` (Issue sparkle-gen5-dg-readertrace)

**STATUS (synced at g5rt-r3).** This rev0 text was written docs-only; rev0 and rev1 (`DG_READERTRACE_FREEZE_REV1.md`) were then committed TOGETHER with the U-R1 independent-part Lean in `521b3e8a` (the freeze did not precede the Lean commit). `Tools/ShippingGen5ReaderTrace.lean` and `Tests/Gen5/ReaderTraceCheck.lean` built in the Pod (build `rt3v-1f8d15d6`, exit 0, 722 jobs, **approved at `1f8d15d6`** for the U-R1 independent part and the R1/R2 audit fixes only; earlier `rt2v-1fd3e5d9` was superseded). Whole-domain agreement of NoPh / BvarLt with the independent specs is the two kernel theorems `noPh_eq_exp` / `bvarLt_eq_exp`; the 247 samples in the Check only detect mutants. Mutants are rejected by signature/defeq/sample mismatch, not semantic counterexamples. Only the U-R1 independent part is elaborated; everything else below stays an *unelaborated proposal* and is not approved (U-R4 / U-R5, R-trace as a whole: not approved, not supplied). Original rev0 note: every Lean text below is an *unelaborated proposal* written against definitions read in this tree
(names/arities were read from the files cited; an elaboration error found later is fixed in a rev addendum, never silently).
Base `44d72eaf` (kjob/g5rt-r1 = kjob/g5cv-r13 + approved U-E3a: `CtrlEq`, `FReachC`, 6 lemmas, helper `fullInv_ctrl`).
Continues `scripts/gen5/DG_COVER_FREEZE_REV7.md` §0 (S1-S5), §2.2 (U-E3b roadmap), §6.2 (supplier table).
No guarantee, law, TRUSTED boundary, FG scope, compiler or shared definition is changed or proposed to be changed. `GenWF` is not strengthened. No decision is requested.

Wording rule (as rev0–rev7): "not found" = *this investigation found no supplier or route*, never "impossible / not derivable". A mutant is a rejection of a changed statement by signature / defeq,
not a semantic counterexample. A conditional wrapper is **not** a supply. Conditional results are INTERMEDIATE.

## 0. What was read, and the findings that shape the types

Read: `Tools/ShippingReaderFuelDefs.lean` (all seven bodies, `Call`, `Call.Res`, `step`, `readF`), `Tools/ShippingReaderFuelShape.lean` (`shapePre/shapeMid/shapeStart/shapeRootLet/shapeBody/shapePost/shapeW`),
`Tools/ShippingLetsReaderInv.lean` + `…Base.lean` + `…Main.lean` (`Pre/Post/Good/readF_good`, `LetOk`, `EnvOk`, `RdOk`, `Adv`, `PureFacts`, the five range premises),
`Tools/ShippingGen5Cover2.lean` (`MentionsPh`, `PhInRange`), `…Cover3.lean` (`InRange/RangeInv/FullInv/FStep/FReach`, `LooseOcc`, `LetsNoLoose`), `…Cover5.lean` (T3), `…Cover6.lean` (U-E3a),
`Sparkle/Compiler/Elab.lean` (`MachRead`, `MachVal`, `machBindLet*`, `machLetIndex`, `machReserve`, `machLoopRegs`, `machLetTail`, `machProjIota`), `Sparkle/Compiler/MachRawSurface.lean` (`rootFloat`, `bundleIota`).

* **F1. Where `_machIn i` is created.** Only `convBvar` (`FuelDefs:255`): `machIn (j - d - env.length)` for a loose bvar `j ≥ d + env.length`. Hence R-in is exactly a bound on loose bvars of every expression
  handed to `conv`: `j < d + env.length + nDecl`. This is the arithmetic that `BvarLt` (§2.1) carries. It needs *extern* facts (lift / instantiate1 / rootFloat keep the bound), §4.
* **F2. `MentionsPh` does not descend `letE / mdata / proj`**, while `LetOk` does. Outputs of `conv` never contain those (they are `failO` or eliminated), so `InRange` (MentionsPh-based, what `FStep` needs) is the right range
  for *outputs*; for *inputs* a recursive placeholder-freeness `NoPh` that does descend `letE` is needed (the `letE` arm recurses on `v`, `b`).
* **F3. Not every pure helper stays inside the range by itself.** The following reads of the state need an *invariant on a free field* (a field `CtrlEq` lets change), so they cannot be carried by `FReachC` and are carried per call
  in `CtlPh` (§2.1): `bareRegs` (`machSlot k` of a hit, `FuelDefs:310`), `loopWs` (`b0 + n ≤ kinds.size`, `loopProbe`), `nested` (shared result `v`, `nestedStep`; this is why `RdOk` already has a `nested` clause —
  `Expr` `==` is the opaque `Expr.eqv`, `a == b = true` is **not** used as `a = b` anywhere below), `dom` (R-dom), the `insts` *group* completeness behind `machInstOut (k0 + i)` (`instSStep` dedup), and `LetsNoLoose` (R-nl).
* **F4. `shapeStart` drops the state of the `dom` conversion** (`bindO (wConv … dom {}) fun (dom', _) => … machReserve … dom' … ({} : MachRead)`): the range of `dom'` is relative to the discarded state. See §3.3 (`DomAtomic`).
* **F5. `wrap?` of `shapeMid`** makes the final `v` of `shapeBody` `mkAppN c (params.push v_chain)` with `params` *unconverted* subterms of the root. The range of the final `v` is therefore claimed only when `wrap? = none` (§3.4).
* **F6. The loop write index** `base + ws.length` (`loopNext`) is unchecked in the code; its range `< kinds.size` rests on `base + regs.length ≤ kinds.size` (a `loopBody` input condition, §2.2) which holds at both call sites
  (`loopRootStep` after pushing `n = kinds.length = regs.length` slots; `loopProbe` via `loopWs`).

## 1. Row status (R-trace, R-in, R-nl, R-dom) — unchanged by this document; this is the plan

| row | what this Issue states | status after this freeze |
|---|---|---|
| R-trace | `TraceGood` (§2.3): every successful `readF` answer is an `FReachC` from the call's input to its output state | **plan frozen; unproved**, `readF_traceGood` (U-R4) |
| R-in | clause `InRange nDecl st' st'.lets.size r` of `PhPost` + input side `BvarLt`/`NoPh`/`EnvPh` | **plan frozen; unproved** |
| R-nl | clause `NoLoose d r` of `PhPost` + `LetsNoLoose` in `CtlPh` | **plan frozen; unproved** |
| R-dom | `DomRange` conjunct of `CtlPh` (separate obligation from `FReachC`: `CtrlEq` leaves `dom` free); start state needs `DomAtomic` (§3.3) | **plan frozen; unproved** |
| "dom equals the R5-R6 composition" (rev5 row 4, second half) | **not** stated here | 未供給 / この調査で経路未発見 |

## 2. Full types (new files; unelaborated)

New Lean goes only in new files, namespace `Tools.ShippingGen5ReaderTrace`, `set_option autoImplicit false`, no `axiom`, no `sorry`, no `native_decide`, no edit of any built file:

| file | content | unit |
|---|---|---|
| `Tools/ShippingGen5ReaderTrace.lean` | §2 definitions, glue lemmas, `convBvar_trace` | U-R1 |
| `Tools/ShippingGen5ReaderTracePh.lean` | Ph / `BvarLt` versions of the pattern extractors (total functions) | U-R2 |
| `Tools/ShippingGen5ReaderTraceArms.lean` | the seven arms, `step_trace`, `readF_traceGood` | U-R3, U-R4 |
| `Tools/ShippingGen5ReaderTraceShape.lean` | `shapeStart/RootLet/Body` traces, `ShapeInputs`, `machineShapeF_reach` | U-R5 |

`lakefile.lean` gets one `lean_lib` per file and per Check (additions only). Imports: `Tools.ShippingGen5Cover6` (⇒ Cover3), `Tools.ShippingGen5Cover5`, `Tools.ShippingLetsReaderInv`,
`Tools.ShippingReaderFuelShape` (whichever are not transitive). Opens: `Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv Sparkle.Compiler.MachInstOrigin`.

### 2.1 Predicates (U-R1)

```lean
/-- the four placeholder tags -/
def phTag (t : String) : Bool := t == "_machIn" || t == "_machInst" || t == "_machSlot" || t == "_machLet"

/-- recursive placeholder-freeness (descends letE/mdata/proj like `LetOk`; `MentionsPh` does not) -/
def NoPh : Lean.Expr → Bool
  | .fvar ⟨.num (.str .anonymous t) _⟩ => !phTag t
  | .app f a => NoPh f && NoPh a
  | .lam _ t b _ => NoPh t && NoPh b
  | .forallE _ t b _ => NoPh t && NoPh b
  | .letE _ t v b _ => NoPh t && NoPh v && NoPh b
  | .mdata _ e => NoPh e
  | .proj _ _ e => NoPh e
  | _ => true

/-- every loose bvar index of `e` (relative to its root; bound ones are admitted by the `+1` per binder) is `< L`. -/
def BvarLt : Nat → Lean.Expr → Bool
  | L, .bvar j => decide (j < L)
  | L, .app f a => BvarLt L f && BvarLt L a
  | L, .lam _ t b _ => BvarLt L t && BvarLt (L + 1) b
  | L, .forallE _ t b _ => BvarLt L t && BvarLt (L + 1) b
  | L, .letE _ t v b _ => BvarLt L t && BvarLt L v && BvarLt (L + 1) b
  | L, .mdata _ e => BvarLt L e
  | L, .proj _ _ e => BvarLt L e
  | _, _ => true

/-- R-nl atom: no loose bvar of `v` (read at binder depth `d`, exactly `LooseOcc`). -/
def NoLoose (d : Nat) (v : Lean.Expr) : Prop := ∀ b, ¬ LooseOcc d v b

/-- converted values of the environment are in range of the CURRENT state and loose-free; loop states name existing slots. -/
def EnvPh (nDecl : Nat) (st : MachRead) (env : List MachVal) : Prop :=
  (∀ v, MachVal.val v ∈ env → InRange nDecl st st.lets.size v ∧ NoLoose 0 v) ∧
  (∀ b n, MachVal.state b n ∈ env → b + n ≤ st.kinds.size)

/-- invariants on fields that `CtrlEq` leaves free (so `FReachC` says nothing about them), plus `LetsNoLoose` and the `instS` group bound. -/
def CtlPh (senv : StructEnv) (nDecl : Nat) (st : MachRead) : Prop :=
  (∀ x ∈ st.loopWs.toList, x.1 + x.2.1 ≤ st.kinds.size) ∧
  (∀ x ∈ st.bareRegs.toList, x.2 < st.kinds.size) ∧
  (∀ x ∈ st.nested.toList, InRange nDecl st st.lets.size x.2.2.2.2.2 ∧ NoLoose 0 x.2.2.2.2.2) ∧
  (∀ d, st.dom = some d → InRange nDecl st st.lets.size d ∧ NoLoose 0 d) ∧           -- R-dom (+ loose-free)
  LetsNoLoose st ∧                                                                    -- R-nl on the table
  (∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder),
     st.insts[k]? = some (c, js, r) → st.instOrigins[k]? = some (InstOrigin.field 0) →
     ∃ (kinds : List MixedGateBinder) (ty resTy : Lean.Expr) (args : List Lean.Expr) (ctor : Name)
       (fields : List (String × MixedGateBinder)),
       senv.instS c = some (kinds, ty) ∧ instRes ty args = some resTy ∧
       machOuts? senv resTy = some (some ctor, fields) ∧ k + fields.length ≤ st.insts.size)

/-- the state invariant carried by every call. -/
def TrInv (senv : StructEnv) (nDecl : Nat) (st : MachRead) : Prop := FullInv nDecl st ∧ CtlPh senv nDecl st
```

### 2.2 Call projections, input and output ranges (U-R1)

```lean
def callSt : Call → MachRead
  | .conv _ _ _ st | .nested _ _ _ _ _ st | .inst _ _ _ _ _ _ st | .instS _ _ _ _ _ st
  | .chain _ _ st | .loopBody _ _ _ st | .loopRoot _ _ st => st

/-- the output state of an answer (the second component of every result; the answer itself for `loopBody`). -/
def callOut : (c : Call) → c.Res → MachRead
  | .conv .., p => (p : Lean.Expr × MachRead).2
  | .nested .., p => (p : Lean.Expr × MachRead).2
  | .inst .., p => (p : Lean.Expr × MachRead).2
  | .instS .., p => (p : Lean.Expr × MachRead).2
  | .chain .., p => (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead).2.2
  | .loopBody .., s => (s : MachRead)
  | .loopRoot .., p => (p : MachVal × MachRead).2

/-- input side of the new invariant (`Pre c` of `ShippingLetsReaderInv` is kept separately in `TracePre`). -/
def PhPre (senv : StructEnv) (nDecl : Nat) : Call → Prop
  | .conv env d e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (d + env.length + nDecl) e = true
  | .nested env dom _ _ body st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh dom = true ∧ BvarLt (env.length + nDecl) dom = true ∧
      NoPh body = true ∧ BvarLt (env.length + 1 + nDecl) body = true
  | .inst env _ org kinds res args st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧
      (∀ a ∈ args, NoPh a = true ∧ BvarLt (env.length + nDecl) a = true) ∧
      (∀ cb aw dw, org = InstOrigin.mem cb aw dw →
        kinds = [MixedGateBinder.domain, .bits aw, .bits dw, .bool, .bits aw] ∧ res = .bits dw ∧ args.length = 5)
  | .instS env _ _ ty args st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧
      (∀ a ∈ args, NoPh a = true ∧ BvarLt (env.length + nDecl) a = true) ∧
      NoPh ty = true ∧ BvarLt (env.length + nDecl) ty = true
  | .chain env e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (env.length + nDecl) e = true
  | .loopBody base env e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (env.length + nDecl) e = true ∧
      (∀ regs, machLoopRegs (machLetTail e) = some regs → base + regs.length ≤ st.kinds.size)
  | .loopRoot env e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (env.length + nDecl) e = true

/-- returned expression: in range of the OUTPUT state (R-in) and loose-free at the call depth (R-nl). -/
abbrev ExprPh (senv : StructEnv) (nDecl d : Nat) (p : Lean.Expr × MachRead) : Prop :=
  TrInv senv nDecl p.2 ∧ InRange nDecl p.2 p.2.lets.size p.1 ∧ NoLoose d p.1

abbrev ChainPh (senv : StructEnv) (nDecl : Nat) (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead) : Prop :=
  TrInv senv nDecl p.2.2 ∧
  (∀ w ∈ p.1, w.1 < p.2.2.kinds.size ∧ InRange nDecl p.2.2 p.2.2.lets.size w.2) ∧
  InRange nDecl p.2.2 p.2.2.lets.size p.2.1 ∧ NoLoose 0 p.2.1

abbrev RootPh (senv : StructEnv) (nDecl : Nat) (p : MachVal × MachRead) : Prop :=
  TrInv senv nDecl p.2 ∧
  (∀ b n, p.1 = MachVal.state b n → b + n ≤ p.2.kinds.size) ∧
  (∀ v, p.1 = MachVal.val v → InRange nDecl p.2 p.2.lets.size v ∧ NoLoose 0 v)

def PhPost (senv : StructEnv) (nDecl : Nat) : (c : Call) → c.Res → Prop
  | .conv _ d _ _, p => ExprPh senv nDecl d (p : Lean.Expr × MachRead)
  | .nested .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .inst .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .instS .., p => ExprPh senv nDecl 0 (p : Lean.Expr × MachRead)
  | .chain .., p => ChainPh senv nDecl (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead)
  | .loopBody .., s => TrInv senv nDecl (s : MachRead)
  | .loopRoot .., p => RootPh senv nDecl (p : MachVal × MachRead)
```
`nested/inst/instS` are called only at `d = 0` by `convStep` (`if d != 0 then failO`), hence `NoLoose 0`.

### 2.3 TracePre / TracePost / TraceGood (U-R1 statement, U-R4 proof)

```lean
/-- `Pre c` (existing: `RdOk`, `EnvOk`, `LetOk 0`) AND the new input side. -/
def TracePre (senv : StructEnv) (nDecl : Nat) (c : Call) : Prop := Pre c ∧ PhPre senv nDecl c

/-- `Post c v` (existing) AND the closure-reach from the input state to the output state AND the new output side. -/
def TracePost (senv : StructEnv) (nDecl : Nat) (c : Call) (v : c.Res) : Prop :=
  Post c v ∧ FReachC nDecl (callSt c) (callOut c v) ∧ PhPost senv nDecl c v

/-- the trace invariant of a call table (the type of rev7 §2.2, now with bodies). -/
def TraceGood (senv : StructEnv) (nDecl : Nat) (h : Hs) : Prop :=
  ∀ c, TracePre senv nDecl c → ∀ v, h c = some (some v) → TracePost senv nDecl c v
```
`Pre` / `Post` are `Tools.ShippingLetsReaderInv.Pre/Post` (read; unchanged). `NoPh e = true` implies `LetOk n e = true` for every `n` (lemma `noPh_letOk`, U-R1), so the `LetOk 0` conjunct of `Pre` is supplied from the same input fact.
`EnvPh` does **not** imply `EnvOk` (MentionsPh vs LetOk on `letE`), so `Pre` and `PhPre` are kept as two conjuncts and both are propagated by the arms.

### 2.4 The state glue (U-R1; all in-tree, no extern)

```lean
theorem reachC_ws {nDecl : Nat} (st : MachRead) (ws' : Array (Nat × Lean.Expr))
    (h : ∀ w ∈ ws', w.1 < st.kinds.size ∧ InRange nDecl st st.lets.size w.2) : FReachC nDecl st { st with ws := ws' }
theorem reachC_letv {nDecl : Nat} (st : MachRead) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr)
    (h : InRange nDecl st st.lets.size v) : FReachC nDecl st { st with lets := st.lets.push (nm, kd, v) }
theorem reachC_slots {nDecl : Nat} (st : MachRead) (ks : List MixedGateBinder) (is : List Nat) (ns : List Name) :
    FReachC nDecl st { st with kinds := st.kinds ++ ks.toArray, inits := st.inits ++ is.toArray, names := st.names ++ ns.toArray }
theorem noPh_letOk (n : Nat) (e : Lean.Expr) (h : NoPh e = true) : LetOk n e = true
theorem noLoose_zero_le {d : Nat} {v : Lean.Expr} (h : NoLoose 0 v) : NoLoose d v
theorem envPh_mono {nDecl : Nat} {st st' : MachRead} {env : List MachVal} (h : EnvPh nDecl st env)
    (hr : FReachC nDecl st st') : EnvPh nDecl st' env
theorem envPh_cons_val {nDecl : Nat} {st : MachRead} {env : List MachVal} {x : Lean.Expr} (h : EnvPh nDecl st env)
    (hx : InRange nDecl st st.lets.size x) (hn : NoLoose 0 x) : EnvPh nDecl st (MachVal.val x :: env)
theorem trInv_empty {senv : StructEnv} {nDecl : Nat} : TrInv senv nDecl ({} : MachRead)
theorem bindLet_reach {nDecl : Nat} {st : MachRead} {nm : Name} {ty v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    FReachC nDecl st { st with lets := (machBindLet nm ty v' st.lets).2 } ∧
    InRange nDecl { st with lets := (machBindLet nm ty v' st.lets).2 } (machBindLet nm ty v' st.lets).2.size (machBindLet nm ty v' st.lets).1 ∧
    NoLoose 0 (machBindLet nm ty v' st.lets).1
-- same shape for machBindLetNamed; machBindLetAlias (needs the `resolve` range lemma, U-R3); machLetIndex (index < size).
```
`envPh_mono` uses `reachC_sizes_mono` + `inRange_mono` (both in tree). `reachC_ws` is `FReachC.tail (refl) (FStep.ws …)`; `reachC_letv`/`reachC_slots` likewise with `FStep.letv` / `FStep.slots`.

### 2.5 The single R-in creation site (U-R1)

```lean
theorem convBvar_trace {senv : StructEnv} {nDecl : Nat} {env : List MachVal} {d j : Nat} {st : MachRead}
    {r : Lean.Expr × MachRead} (hI : TrInv senv nDecl st) (hE : EnvPh nDecl st env)
    (hb : BvarLt (d + env.length + nDecl) (Lean.Expr.bvar j) = true) (h : convBvar env d j st = some r) :
    r.2 = st ∧ InRange nDecl st st.lets.size r.1 ∧ NoLoose d r.1
```
Its proof: `j < d` ⇒ `.bvar j` (no fvar; `LooseOcc d (.bvar j) b` is `j = b + d`, false); env `.val v` ⇒ `EnvPh`; `.state b 1` ⇒ `machSlot b`, `b + 1 ≤ kinds.size`; `.state b n` ⇒ `bundleSlots` over `kinds[i]?`-checked slots (a lemma `bundleSlots_ph`: every `machSlot i` has `i < kinds.size`, `st.dom` from `CtlPh`) ;
`none` ⇒ `machIn (j - d - env.length)` with `j - d - env.length < nDecl` from `hb` (**this is the R-in line**); `some _` ⇒ `none` (vacuous).

## 3. The seven bodies: plan to show `TraceGood nDecl (readF senv n)` (mirror of `readF_good`)

Induction on the fuel exactly as `readF_good`: `n = 0` vacuous (`none ≠ some (some _)`); `n+1`: `step_trace senv F G (hG : TraceGood … h) : TraceGood … (fun c => (step senv c).run h)` by `cases c`, one `*_trace` lemma per body
(`conv_trace`, `nested_trace`, `inst_trace`, `instS_trace`, `chain_trace`, `loopBody_trace`, `loopRoot_trace`), each proved with the combinators `satp_bindO / satp_optK / satp_findSomeO / satp_foldO` already in `ShippingLetsReaderInv.lean` (applied to the predicate `TracePost` with the call fixed).
Notation: `A ⟶ B` = `FReachC nDecl A B`; chain = `reachC_trans`. After each sub-call the next call's `TracePre` is obtained from the previous `TracePost` (`TrInv` of the output, `envPh_mono`, range monotonicity by `reachC_sizes_mono`, `Pre` from `Post`/`Adv` exactly as in `*_sat`).

**convStep** (11 arms; `d` = depth, `L = d + |env| + nDecl`):
1. `bvar j`: `convBvar_trace` (state unchanged: `refl`).
2. bare `Signal.register` (needs `d = 0`, `¬inInner`, no loops/runs): hit in `bareRegs` ⇒ `machSlot k`, `k < kinds.size` from `CtlPh.bareRegs`, `refl`. Miss ⇒ `cConv env 0 dom st` [call 1: `PhPre` from `RegViewPh`, §4] giving `st ⟶ s1`; `domGuard`; then
   `s1 ⟶ s1'` by `FStep.slot` (`kinds/inits/names` push) and `ctrl` (`dom`, `bareRegs`: `CtrlEq` holds, `ws` equal); `cConv env 0 x s1'` [call 2] `s1' ⟶ s2`; result `machSlot base`, `base = s1.kinds.size < s1'.kinds.size`; last write `ws.push (base, x')` is `reachC_ws` (old `ws` in range by `FullInv s2`, `x'` by call 2's `PhPost`). `CtlPh` after: `dom := some dom'` (range of `dom'` at `s1`, monotone), `bareRegs` push `(e, base)` with `base < size`, others monotone.
3. `machLoopRead?` / `machReadV` ⇒ `i < kinds.size` guard ⇒ `machSlot i`, `refl`.
4. run application ⇒ `cNested env dom αs initsE body st` (`d = 0`; body at `L+1` from `RunAppPh`). Output = that call's.
5. `machInstCall?` ⇒ `cInst env c .ord kinds res args st` (`.ord`: the `mem` clause of `PhPre` is vacuous).
6. `machInstCallS?` ⇒ `cInstS env c kinds ty args st`, `ty` from `senv.instS c` (`SigTyPh`, §4), `args` from `InstCallSPh`.
7. memory call ⇒ `cInst env (memChildName …) (.mem combo aw dw) [.domain,.bits aw,.bits dw,.bool,.bits aw] (.bits dw) (dom :: ops) st`; the `mem` clause needs `ops.length = 4` (`MemCallArity`, §4); then `instStruct := true` is a `ctrl` step.
8. generic application: `cConv env d f st` ⟶ `cConv env d a s1` ⟶, result `bundleIota (machProjIota senv.proj (.app f' a'))`: `InRange` of an application is the conjunction (MentionsPh), `ProjIotaPh`/`BundleIotaPh` (§4) keep range and `NoLoose d`.
9. `lam` / 10. `forallE`: two calls (`d`, `d+1`; `L+1 = (d+1)+|env|+nDecl` by `omega`), result `.lam nm t' b' bi`; `NoLoose d (.lam …) = NoLoose d t' ∨ NoLoose (d+1) b'`-shape matches the two IH.
11. `letE` (`d = 0`): `rootFloat v` is `letE` ⇒ `cConv env 0 (rearranged)` with `RootFloatPh` + `LiftPh` (§4) for the `BvarLt (L+…)`/`NoPh` of the rearranged term; `Signal.loop` ⇒ `cLoopRoot env v st` then `cConv (mv :: env) 0 b` (`RootPh` ⇒ `EnvPh (mv :: env)`); `machTailV`/`machHandleV` ⇒ `cConv (.regs p :: env) 0 b` / `(.handle i :: env)` (no `EnvPh` content);
   default ⇒ `cConv env 0 v st` ⟶ `bindLet_reach` (`FStep.letv` or `refl`) ⟶ `cConv (.val x :: env) 0 b {st with lets}` (`envPh_cons_val`, `NoLoose 0 x`). `mdata`/`proj` ⇒ `failO`. Catch-all `okO (e, st)`: `e` atomic and `NoPh` ⇒ no mention; `refl`.

**nestedStep**: `cConv env 0 dom st` ⟶ `s1` (call 1); `findSomeO (nestedProbe …) s1.nested.toList`: a hit is `cChain (.regs base :: env) body s1` ⟶ `st'` (call, `PhPre` with `L+1`), result `(v, st')` with stored `v` (`CtlPh.nested` at `s1`, `inRange_mono` along `s1 ⟶ st'`); a miss ⇒ `machReserve` (`kinds/inits/names` slots + `dom/runs` ctrl; the spec lemma `machReserve_eq_spec` of `ShippingReaderLenOkReserve` gives the shape) then
`cChain (.regs base :: env) body {s with inInner := true}` ⟶ `(ws, v, st')`; final `{st' with ws := st'.ws ++ ws.toArray, inInner := outer, nested := push …}` = `reachC_ws` then `ctrl` (`inInner`, `nested`); `CtlPh.nested` of the push: `v` range at `st'`.

**instStep**: `instEntry` (`ctrl`: `instStruct`; `none` for `domain`) ⟶ `foldO (instArg env k) ([], st) (kinds.zip args)`: per arg `cConv env 0 arg` ⟶, `domain` kind ⇒ `dom := some v'` (`ctrl`, `CtlPh.dom` with `v'`'s range) else `machLetIndex`: `_machLet j` ⇒ `j < lets.size` from `InRange`; found ⇒ `j < lets.size`; pushed ⇒ `reachC_letv`; fold invariant `∀ a ∈ js, a < lets.size` and `js.length` (for the `mem` clause of `FStep.inst`: `js.length = 4` from `kinds` = 5 entries with one `domain`, `args.length = 5`; lemma `foldO_js_length`, U-R3).
Final: dedup hit ⇒ `machInstOut k'`, `k' < insts.size` (`findIdx?` over `zipIdx`), `refl`; miss ⇒ `FStep.inst` (premises: `js < lets.size`, `res ≠ domain` by `instEntry`, `mem` clause by `PhPre`) then `ctrl` (`instFields`); `machInstOut k`, `k < insts.size + 1`; `CtlPh.groups`: new origin is `ord`/`mem`, never `field 0`.

**instSStep**: `inInner` guard; `instRes ty args` (`Inst1Ph`, `SigTyPh`) ⇒ `resTy`; `machOuts?`; `fields` non-empty, none `domain` (guard). `foldO (instSArg env)` (as `instArg`) then `foldO (instSParam env)` over `resTy.getAppArgs` (`NoPh`/`BvarLt` of the spine args, `GetAppArgsPh`, §4): each a `cConv env 0` call. Dedup hit (origin `.field 0`) ⇒ `machInstOut (k0 + i)`, `k0 + fields.length ≤ insts.size` from `CtlPh.groups` **and `InstSFieldsDet`** (§4, the earlier group has the same number of fields); miss ⇒ `FStep.group` (`rs.length = os.length`, `js < lets.size`, no `domain`, no `mem`) then `ctrl` (`instFields`, `instStruct`); `CtlPh.groups` extended with the new group (`k + fields.length ≤ insts.size'`).

**chainStep**: `Circuit.pure'` ⇒ `cConv env 0 v`; `bind/next` ⇒ `cConv env 0 rhs` ⟶ `s1`, `machHandleV` ⇒ `i`, guard `i < s1.kinds.size`, `cChain (.unit :: env) rest s1` ⟶ `(ws, v, s2)`; result `((i, rhs') :: ws, v, s2)` with `i < s2.kinds.size`, `rhs'` range lifted `s1 ⟶ s2` by `inRange_mono`; `letE` as the `convStep` arm 11 with `cChain`. The patterns destructure explicit constructors, so `NoPh`/`BvarLt` of `v`, `rhs`, `rest` (`L+1`), `h` are by definition of `NoPh`/`BvarLt` (no extractor lemma).

**loopBodyStep**: `letE`: `cConv env 0 v` ⟶ `s1`; `machBindLetNamed` / `machBindLetAlias` / `machBindLet` (U-R3: `bindLetAlias_reach` needs the range of `resolve lets.size v'`, i.e. of a stored `value`, from `FullInv`) ⟶ `cLoopBody base (.val x :: env) b {s1 with lets}`.
Tail: `machLoopRegs tail` ⇒ `foldO (loopNext env base)` of `cConv env 0 nx` calls; write index `base + ws.length < kinds.size` from the `loopBody` input clause (`base + regs.length ≤ kinds.size`, with `machLetTail (.letE …) = machLetTail b`); final `{st with ws := st.ws ++ ws.toArray}` = `reachC_ws`.

**loopRootStep**: `loopView?` (`LoopViewPh`), guards, `kinds/inits` pure (lengths: `regs.mapM loopRegKind = some kinds ⇒ kinds.length = regs.length`, lemma `mapM_length_some`). `cConv env 0 dom st` ⟶ `s1`; `domGuard`; probe `findSomeO (loopProbe …) s1.loopWs.toList`: hit ⇒ `reachC_ws s1 #[]` ⟶ `cLoopBody b0 (.state b0 n :: env) body {s1 with ws := #[]}` ⟶ `st'` ⟶ `reachC_ws … s1.ws` (range of the restored `ws` at `st'` by `FullInv s1` + monotonicity), result `.state b0 n`, `b0 + n ≤ kinds.size` from `CtlPh.loopWs`. Miss ⇒ `reachC_slots` + `ctrl` (`dom`, `loops`, `nestedLoops`, `loopDepth`) ⟶ `cLoopBody base (.state base n :: env) body st''` (`base + n ≤ kinds.size`) ⟶ `ctrl` (`loopWs`, `loopDepth`); `CtlPh.loopWs` push `(base, n, …)` has `base + n ≤ kinds.size`.

The shape wrapper (U-R5), same style:
`shapeStart`: `m.run? = none` ⇒ `{}` (`trInv_empty`, `rdOk_init`); `some` ⇒ `wConv (unit…) 0 dom {}` (§3.3) then `machReserve` from `{}` ⇒ `reachC_slots`+`ctrl` (this is `reserved_reachC` of U-E3a). `foldO shapeRootLet`: per root let either `wLoopRoot` (`RootPh`) or `wConv` + `bindLet_reach` (env length = index `k`). `shapeBody`: `wChain (regs 0 :: env) body` or `wConv env root`; final `ws := st.ws ++ ws.toArray` = `reachC_ws`.

### 3.1 `readF_traceGood` (U-R4)

```lean
theorem readF_traceGood (senv : StructEnv) (nDecl : Nat) (F : PureFacts senv) (G : PhFacts senv) :
    ∀ n, TraceGood senv nDecl (readF senv n)
```
`F : PureFacts senv` is the existing record (five LetOk named premises; `pureFacts_of`). `G : PhFacts senv` is §4. Both are hypotheses, not axioms.

### 3.2 R-in / R-nl / R-dom are clauses, not separate theorems

R-in = the `InRange` conjunct of `ExprPh/ChainPh/RootPh` (+ `PhPre` bounds). R-nl = `NoLoose` conjunct + `LetsNoLoose` in `CtlPh`. R-dom = the `dom` conjunct of `CtlPh`. After U-R4 each is *read off* `readF_traceGood`; what is not proved by that theorem is §4's list and the start-of-run facts of §3.3.

### 3.3 Start-of-run facts (U-R5) — the `dom` of `shapeStart`

`shapeStart` converts `dom` from `{}`, **discards** the resulting state, and resets to `{}`. `PhPost` gives `InRange nDecl s' s'.lets.size dom'` for the discarded `s'`; the reserved state has `lets.size = 0`, `insts.size = 0`, `kinds.size = |reserved kinds|`.
So `CtlPh.dom` at `st0` additionally needs "`dom'` mentions no `_machLet` / `_machInst`". The plan is the named input condition

```lean
def DomAtomic (e : Lean.Expr) : Prop := (∃ j, e = .bvar j) ∨ (∃ c ls, e = .const c ls)
```
(then `conv` of `e` is `convBvar` over an all-`unit` environment or the catch-all arm, so `dom'` is `machIn (j - |rootLets|)` or the constant, no `_machLet/_machInst/_machSlot`; proved directly from the one-step unfolding of `readF senv (n'+1)`, no trace needed).
If some accepted source has a non-atomic domain, R-dom at `st0` stays an unproved named condition and this is reported; the claim is not weakened silently.

### 3.4 `wrap?`

`shapeBody` returns `mkAppN c (params.push v)` when `m.wrap? = some (c, params)`, `params` unconverted. The final-`v` range clause is claimed only for `wrap? = none` (§5).

## 4. Extern / partial / environment facts — row by row

`PhFacts` (named hypotheses of `readF_traceGood`; none is an axiom; none is proved by this freeze):

```lean
structure PhFacts (senv : StructEnv) : Prop where
  rootFloat : ∀ (L : Nat) (v : Lean.Expr), BvarLt L v = true → NoPh v = true →
    BvarLt L (Sparkle.Compiler.MachRawSurface.rootFloat v) = true ∧ NoPh (Sparkle.Compiler.MachRawSurface.rootFloat v) = true
  lift : ∀ (s L : Nat) (e : Lean.Expr), BvarLt L e = true → NoPh e = true →
    BvarLt (L + 1) (e.liftLooseBVars s 1) = true ∧ NoPh (e.liftLooseBVars s 1) = true
  inst1 : ∀ (L : Nat) (b a : Lean.Expr), BvarLt (L + 1) b = true → BvarLt L a = true → NoPh b = true → NoPh a = true →
    BvarLt L (b.instantiate1 a) = true ∧ NoPh (b.instantiate1 a) = true
  sigTy : SigTyPh senv
  instSFieldsDet : InstSFieldsDet senv

def SigTyPh (senv : StructEnv) : Prop :=
  ∀ c kinds ty, senv.instS c = some (kinds, ty) → NoPh ty = true ∧ BvarLt 0 ty = true
def InstSFieldsDet (senv : StructEnv) : Prop :=
  ∀ c kinds ty (args args' : List Lean.Expr) (r r' : Lean.Expr) (o o' : Option Name) (fs fs' : List (String × MixedGateBinder)),
    senv.instS c = some (kinds, ty) → instRes ty args = some r → instRes ty args' = some r' →
    machOuts? senv r = some (o, fs) → machOuts? senv r' = some (o', fs') → fs.length = fs'.length
```
(`BvarLt L ty` for the `instS` call follows from `BvarLt 0 ty` by `bvarLt_mono`, U-R1.) Binder-name clash with the existing `PureFacts` fields is avoided by the namespace.

| item | what is needed (exact name) | proved or kept | why / supplier |
|---|---|---|---|
| `rootFloat` (partial) | `PhFacts.rootFloat` (placeholder + loose-bvar version of `RootFloatRange`) | **kept as a named condition** | `rootFloat` is a `partial def`: an opaque constant for the logic, no equation lemma to unfold. No supplier Issue found. (A fuel twin `rootFloatF` + an equality fact would be a different Issue; not proposed here.) |
| `liftLooseBVars` (extern) | `PhFacts.lift` (`LiftRange`'s placeholder + bvar version). The statement is a true property of the C implementation (shifting indices ≥ `s` by 1) | **kept as a named condition** | `opaque … @[extern]` in core (`Lean/Expr.lean:1363`); not unfoldable. |
| `instantiate1` (extern) | `PhFacts.inst1` (`Inst1Range` version) | **kept as a named condition** | `opaque … @[extern]` (`:1447`). |
| `SigTy` | `SigTyPh senv`: types in `senv.instS` are placeholder-free and closed | **kept; owner `sparkle-gen5-dg-env`** (SigTy/SigEq are dg-env's; not re-implemented here) | environment condition on `structEnv`. |
| group size of `instS` | `InstSFieldsDet senv`: the number of fields of `machOuts?` does not depend on the arguments of the call (only on `c`) | **kept as a named condition; owner proposed `sparkle-gen5-dg-env`** (it is a fact about `senv.instS`/`senv.fields`; this investigation did not look for it elsewhere) | needed only for the dedup arm of `instSStep` (`machInstOut (k0 + i)` in range). |
| `nDecl` | only `p.bs.length ≤ nDecl` is used (`MidInputs`, §5). Identification `nDecl = kDOf d` / `d.nIn` is **`sparkle-gen5-dg-dataof`'s** | not done here | the inequality direction suffices for `j - d - |env| < nDecl`; no duplicate implementation of row 6b. |
| `bundleIota` (total `def`) | `BundleIotaPh`: `∀ nDecl kI n k e, PhInRange nDecl kI n k e → PhInRange nDecl kI n k (bundleIota e)` and `∀ d e, NoLoose d e → NoLoose d (bundleIota e)` | **to be attempted in U-R2** (result is a subterm of `e` or `bundle2` applied to subterms; the `LetOk` version `BundleIotaRange` was left unproved because of the nested name/array-literal `match`, not because of an opaque constant). If the case split is not completed, it becomes a named hypothesis `BundleIotaPh` of `readF_traceGood` (type fixed here) and is reported as such | total function, unfoldable. |
| `machProjIota` (total) | `ProjIotaPh` same shape | **to be attempted in U-R2** (`projIota_ok` for `LetOk` exists in `…InvPure.lean`, so a route exists) | |
| extractors `regView? / machRunApp? / machInstCall? / machInstCallS? / memCall? / loopView? / machLetTail / machLoopRegs` | `RegViewPh, RunAppPh, InstCallPh, InstCallSPh, MemCallPh (+ MemCallArity: ops.length = 4), LoopViewPh, LetTailPh, LoopRegsPh`: results are subterms ⇒ `NoPh`, `BvarLt` (with `+1` for the `lam` body of `machRunApp?`/`loopView?`) | **to be proved in U-R2** (total, same method as the `LetOk` versions in `…InvPure.lean`/`InvPure2.lean`) | |
| `getAppArgs` spine | `GetAppArgsPh`: arguments of an application with `NoPh`/`BvarLt` have both | **to be proved in U-R2** | used by `instSParam` and by the extractors. |
| `Expr` `==` | not needed: stored values come from `CtlPh.nested/bareRegs/loopWs`, never from `a == b ⇒ a = b` | — | avoids assuming an equality for the opaque `Expr.eqv`. |

No new law / TRUSTED boundary: every row above is either proved in this Issue or is a hypothesis of a theorem whose conclusion is conditional and so stated.

## 5. U-E3b — `machineShapeF_reach` (full type; U-R5)

```lean
structure ShapePre -- existing (ShippingReaderFuelShape): d bs e tup? ctor? outs ;   ShapeMid -- existing: rootLets sel root wrap? run?

def MidInputs (nDecl : Nat) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  p.bs.length ≤ nDecl ∧
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (shapeMid senv p en).rootLets[k]? = some x →
      NoPh x.2.2 = true ∧ BvarLt (k + nDecl) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) dom = true ∧ DomAtomic dom ∧
      NoPh b = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + 1 + nDecl) b = true) ∧
  ((shapeMid senv p en).run? = none →
      NoPh (shapeMid senv p en).root = true ∧
      BvarLt ((shapeMid senv p en).rootLets.length + nDecl) (shapeMid senv p en).root = true)

/-- R-in, root side: whatever the run's `p` and normalised body `en` are, `MidInputs` holds. -/
def ShapeInputs (nDecl : Nat) (senv : StructEnv) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo) (n : Nat) : Prop :=
  ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p → machNormF n senv p.e = some en →
    MidInputs nDecl senv p en

theorem machineShapeF_reach {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape} {nDecl : Nat}
    (F : PureFacts senv) (G : PhFacts senv)
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hIn : ShapeInputs nDecl senv sm ps ci n) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size ∧
      FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
      TrInv senv nDecl st ∧
      ((shapeMid senv p en).wrap? = none → InRange nDecl st st.lets.size v)
```
The first eleven conjuncts are the text of `machineShapeF_state_side` (Cover5, T3) — six run equations, `LenOk`, four facts; the proof starts from `machineShapeF_state_side h` and does not re-prove them.
`TrInv senv nDecl st` contains `FullInv nDecl st` (via `fullInv_reachC` + `fullInv_empty`), `LetsNoLoose st` (R-nl) and the `dom` range (R-dom).

**Not in this type** (stated so nobody reads more): "`st.dom` equals the R5-R6 composition" (rev5 row 4, second half), `LetQuoteEq`, row 6b (`d.shape = sp`, `nDecl = kDOf d` — `sparkle-gen5-dg-dataof`), `hbr` (`ShapeFuelBridge`, reader-bridge), B3 (src-argw), the derivation of `ShapeInputs` from the declaration value.
**`ShapeInputs` supply:** `MidInputs` talks about `shapeMid senv p en`, i.e. about the output of `machNormF`, `inlFoldNat`, `zeroLit`, `rootFloat`, `machLoopAsLet`, `machRoot`, and `p.bs` from `mixedGatePeel (packTupleInputs d.value)`. **This investigation did not examine them**; the route (loose-bvar bound of a closed declaration body after peeling `p.bs.length` lambdas, `machNormF`
preserving it, `NoPh` of source terms) is unexamined and is its own later unit (U-R6, investigation first). `hIn` stays a named premise until then; `machineShapeF_reach` is **conditional** and an intermediate result.

## 6. Units, order, and the first unit

| unit | content | needs | status |
|---|---|---|---|
| **U-R1** | §2 definitions, §2.4 glue (`reachC_ws/letv/slots`, `noPh_letOk`, `noLoose_zero_le`, `bvarLt_mono`, `envPh_mono`, `envPh_cons_val`, `trInv_empty`, `bindLet_reach` family except Alias), `bundleSlots_ph`, `convBvar_trace` | in-tree only | **first** |
| U-R2 | Ph/`BvarLt` extractors, `getAppArgs`, `bundleIota`, `projIota`, `memCall` arity | in-tree only | after U-R1 |
| U-R3 | leaf lemmas: `bindLetAlias_reach` (`resolve` range), `foldO_js_length`, `mapM_length_some`, `instArg/instSArg/loopNext` fold invariants, `machReserve` reach | U-R1 | |
| U-R4 | seven `*_trace` + `step_trace` + `readF_traceGood` | U-R1–U-R3, `PhFacts`, `PureFacts` | conditional on §4 |
| U-R5 | `shapeStart/RootLet/Body` traces, `DomAtomic` start, `machineShapeF_reach` | U-R4 | conditional on §4 and `ShapeInputs` |
| U-R6 | investigation of `ShapeInputs` supply | — | not started |

**First unit: U-R1.** Reasons: (1) every later unit imports its types, and fixing the types in a compiled file is what makes the later freeze text checkable (this document is unelaborated); (2) it needs nothing outside this tree — no extern/partial fact, no dg-env / dg-dataof output, no premise — so the result is unconditional;
(3) it contains `convBvar_trace`, the only place in the reader where `_machIn` is created, so R-in's arithmetic (`j - d - |env| < nDecl` from `BvarLt (d + |env| + nDecl)`) is proved, not just named; (4) it exposes early whether `CtlPh`'s conjuncts (F3) are the right set: a missing invariant shows up in U-R1's glue and not after the seven-arm induction.
Not chosen first: U-R4 (needs U-R1–U-R3 and the §4 premises, the proof would be a conditional wrapper), U-R5 (needs U-R4), U-R2 alone (does not fix the types).

## 7. Checks planned (`Tests/Gen5/ReaderTraceCheck.lean`, form of `Cover6Check.lean`)

Counts are real counts reported with the category and the counting rule (one compared declaration = 1); `def`/`inductive` are counted separately from theorems.

* **TYPE.** Each declaration of U-R1 (`NoPh, BvarLt, NoLoose, EnvPh, CtlPh, TrInv, callSt, callOut, PhPre, PhPost, TracePre, TracePost, TraceGood`, the glue theorems, `convBvar_trace`) against an `Exp…` written from §2 **without looking at the Tools file** (own spelling, own binder order where the freeze allows; `def` values compared, not only types), by the same reducible comparer used for the positive and negative controls (`checkExpected` of `Tests/Gen3/ExpectedType.lean`).
* **MUTANT** (well-typed single changes only; signature/defeq rejection, **not** semantic counterexamples): `BvarLt` with `L` instead of `L + 1` under a binder; `convBvar_trace` bound `d + env.length + nDecl` ↦ `env.length + nDecl`; `convBvar_trace` conclusion with the `NoLoose` conjunct dropped (and one with `InRange` dropped); `TracePost` without the `FReachC` conjunct; `EnvPh` without the `state` clause; `CtlPh` without the `dom` conjunct; `NoPh` with one tag removed from `phTag`; `reachC_ws` without the range premise; `bindLet_reach` with `FReach` for `FReachC`. Each mutant is compared by the same comparer and must be rejected; counted separately from TYPE.
* **AXIOMS**: `collectAxioms` per theorem: `propext / Classical.choice / Quot.sound` only.
* **CLOSURE** (as Cover6Check): value-closure walk from each root *and the root itself*; an unknown name `throwError`s; 3 negative controls and 2 clean controls; unknown-name controls: root, helper value, and an existing helper whose *type only* is unknown, with a clean control; each intended name is asserted; every invalid fixture is built inside `withoutModifyingEnv`. The intended `sorry` negatives (their number and position are written in the header as observed in the Pod) are the only `sorry`; none is in a proof root.
* Source: no `sorry`, `axiom`, `native_decide`.
* Build: `kjob lake build Tools.ShippingGen5ReaderTrace`, then `Tests.Gen5.ReaderTraceCheck`, one at a time, logs outside the tree; the success SHA is recorded in the `NOT BUILT` header by a comment-only commit. After a Lean commit the Issue stays `doing` with "clean build は coder".

## 8. Not claimed

* R-trace, R-in, R-nl, R-dom for `readF` calls: **未供給**; this document fixes the statements and the plan only. `TraceGood`, `readF_traceGood`, `machineShapeF_reach` are unproved at this revision.
* `PhFacts` (rootFloat, lift, inst1, sigTy, instSFieldsDet), `BundleIotaPh`/`ProjIotaPh` (if U-R2 does not close them), `ShapeInputs`, `DomAtomic`: named premises; any result using them is conditional and INTERMEDIATE.
* Row 6b, `nDecl = kDOf d`, `hbr`, `LetQuoteEq`, B3, "dom equals the composition", real reader coverage (`TwinCover`/`OldEq`), production: unchanged. The Issue and FG are not complete.
* The `F : PureFacts senv` premises (five `LetOk` named premises of `machConvF_post`) are still required by `readF_traceGood` (the old `Pre/Post` half is carried). Deriving them from `PhFacts` for `NoPh` inputs is possible in outline but is not part of this plan.
* No new law, TRUSTED boundary, FG/guarantee change, compiler or shared-definition change; `GenWF` not strengthened.
