# DG-READERTRACE freeze rev2 — next unit U-R1b (types of the dependent part + leaf lemmas that close from existing definitions)

**FOR REVIEW. Docs only; no Lean is written before approval.** Issue `sparkle-gen5-dg-readertrace`. Base: `kjob/g5rt-r4`, header-sync commit on top of `1f8d15d6` (approved: U-R1 independent part + R1/R2 audit fixes only, build `rt3v-1f8d15d6`).
Continues `DG_READERTRACE_FREEZE.md` (rev0) and `DG_READERTRACE_FREEZE_REV1.md`. Wording: "not found" = this investigation found no supplier/route, never "impossible"; a mutant is a signature/defeq rejection, not a semantic counterexample; conditional results are INTERMEDIATE.
No new law / TRUSTED boundary / shared-definition change / FG change / GenWF strengthening is needed or proposed; **no decision is requested**. Still **not approved and not supplied**: U-R4, U-R5, R-trace as a whole (`TraceGood nDecl (readF senv n)`), R-in/R-nl/R-dom for `readF` calls, FG, `PhFacts`, `ShapeInputs`.

## 0. What was checked to choose the unit

Rows examined (names read in the tree at this base):

| row | closes from existing names? | finding |
|---|---|---|
| rev0 §2.1/§2.2 defs `GroupsPh, CtlPh, TrInv, callSt, callOut, PhPre, ExprPh, ChainPh, RootPh, PhPost, TracePre, TracePost, TraceGood` | yes (definitions only; every constant they mention exists: `LetsNoLoose` Cover3:699, `FullInv` Cover3:316, `FReachC` Cover6:21, `Pre/Post` LetsReaderInv:139/167, `Call/Call.Res/Hs` FuelDefs:167/180/196, `InstOrigin` MachInstOrigin:16, `instRes` FuelDefs:266, `machOuts?` Elab:3859, `machLoopRegs` Elab:3790, `machLetTail` Elab:3798) | closes (types) |
| `trInv_empty` | `fullInv_empty` (Cover6:70) + the remaining five `CtlPh` conjuncts of `({} : MachRead)` are about empty arrays / `dom = none` | closes |
| `bindLetNamed_reach` | same proof shape as `bindLet_reach` (`machBindLetNamed` = `machBindLet` without the `machIsVar` test, Elab:3640) | closes |
| `machLetIndex_reach` | `machLetIndex` (Elab:3743): `_machLet j` case needs `j < lets.size`, which is the `_machLet` clause of `InRange` of the argument (4th component of `PhInRange`) | closes |
| `machInstCall?_spec`, `machInstCallS?_spec` (supplier of R1/R2 call-site facts) | statement only uses the `if args.length == kinds.length` and the `senv.inst/instS c` match; `inlSpine` need not be unfolded (split on the match, rewrite) | closes (expected; if the `inlSpine` match blocks the `split`, it is reported, not weakened) |
| `bindLetAlias_reach` | needs a range lemma for `resolve` (local `let rec` of `machBindLetAlias`) | **not chosen**: this investigation did not find a ready lemma; separate unit (U-R3) |
| extractors `RegViewPh … LoopRegsPh`, `GetAppArgsPh`, `BundleIotaPh`, `ProjIotaPh` | need case analysis on `regView?/machRunApp?/loopView?/bundleIota/machProjIota` bodies | **未供給 / この調査で経路未調査** (U-R2 proper) |
| `PhFacts.rootFloat/lift/inst1` | `partial def` / `@[extern]` constants, no equation to unfold | **未供給 / 経路未発見**; stays a named condition |
| `SigTyPh`, `InstSFieldsDet` | environment facts, owner `sparkle-gen5-dg-env` | 未供給 |
| `convStep` arms, `step_trace`, `readF_traceGood` (U-R4) | need U-R2/U-R3 + `PhFacts` | not chosen first |
| `ShapeInputs` (U-R6) | **未供給 / この調査で経路未調査** | — |

**Chosen unit: U-R1b.** Reasons: (1) it is the part of rev0 §2 that rev1 left out of the first Lean file because it was under review (`CtlPh/TrInv/PhPre/PhPost/TracePre/TracePost/TraceGood`); fixing these types in a compiled file is what lets every later unit (U-R2..U-R5) be checked against them. (2) Everything in it is in-tree: no extern fact, no dg-env/dg-dataof output, no premise, so the result is unconditional — but it is only definitions and four leaf lemmas, **not** R-trace. (3) The two `*_spec` lemmas are the call-site suppliers for the R1 tie (`senv.instS c = some (kinds, ty)`) and the arm-5 `senv.inst` fact that rev1 §1 only described in prose.

## 1. Full types (new file `Tools/ShippingGen5ReaderTraceCtl.lean`, namespace `Tools.ShippingGen5ReaderTrace`)

Imports: `Tools.ShippingGen5ReaderTrace`, `Tools.ShippingLetsReaderInv` (⇒ `Pre/Post`), `Tools.ShippingReaderFuelDefs`. `set_option autoImplicit false`. Opens: `Lean Sparkle.Compiler.Elab Sparkle.Compiler.MachInstOrigin Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover6 Tools.ShippingReaderFuel Tools.ShippingLetsReaderInv`. `lakefile.lean`: one `lean_lib` for the file and one for its Check (additions only). `ReaderTrace.lean` is not edited.

```lean
def GroupsPh (senv : StructEnv) (st : MachRead) : Prop :=
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder),
     st.insts[k]? = some (c, js, r) → st.instOrigins[k]? = some (InstOrigin.field 0) →
     ∃ (kinds : List MixedGateBinder) (ty resTy : Lean.Expr) (args : List Lean.Expr) (ctor : Name)
       (fields : List (String × MixedGateBinder)),
       senv.instS c = some (kinds, ty) ∧ instRes ty args = some resTy ∧
       machOuts? senv resTy = some (some ctor, fields) ∧ k + fields.length ≤ st.insts.size

def CtlPh (senv : StructEnv) (nDecl : Nat) (st : MachRead) : Prop :=
  (∀ x ∈ st.loopWs.toList, x.1 + x.2.1 ≤ st.kinds.size) ∧
  (∀ x ∈ st.bareRegs.toList, x.2 < st.kinds.size) ∧
  (∀ x ∈ st.nested.toList, InRange nDecl st st.lets.size x.2.2.2.2.2 ∧ NoLoose 0 x.2.2.2.2.2) ∧
  DomPh nDecl st ∧
  LetsNoLoose st ∧
  GroupsPh senv st

def TrInv (senv : StructEnv) (nDecl : Nat) (st : MachRead) : Prop := FullInv nDecl st ∧ CtlPh senv nDecl st

def callSt : Call → MachRead
  | .conv _ _ _ st | .nested _ _ _ _ _ st | .inst _ _ _ _ _ _ st | .instS _ _ _ _ _ st
  | .chain _ _ st | .loopBody _ _ _ st | .loopRoot _ _ st => st

def callOut : (c : Call) → c.Res → MachRead
  | .conv .., p => (p : Lean.Expr × MachRead).2
  | .nested .., p => (p : Lean.Expr × MachRead).2
  | .inst .., p => (p : Lean.Expr × MachRead).2
  | .instS .., p => (p : Lean.Expr × MachRead).2
  | .chain .., p => (p : List (Nat × Lean.Expr) × Lean.Expr × MachRead).2.2
  | .loopBody .., s => (s : MachRead)
  | .loopRoot .., p => (p : MachVal × MachRead).2

def PhPre (senv : StructEnv) (nDecl : Nat) : Call → Prop
  | .conv env d e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (d + env.length + nDecl) e = true
  | .nested env dom _ _ body st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh dom = true ∧ BvarLt (env.length + nDecl) dom = true ∧
      NoPh body = true ∧ BvarLt (env.length + 1 + nDecl) body = true
  | .inst env _ org kinds res args st =>                                   -- rev1 §1.1 (R2)
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧
      (∀ a ∈ args, NoPh a = true ∧ BvarLt (env.length + nDecl) a = true) ∧
      (org = InstOrigin.ord ∨
        ∃ cb aw dw, org = InstOrigin.mem cb aw dw ∧
          kinds = [MixedGateBinder.domain, .bits aw, .bits dw, .bool, .bits aw] ∧ res = .bits dw ∧ args.length = 5)
  | .instS env c kinds ty args st =>                                       -- rev1 §1.2 (R1)
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧
      senv.instS c = some (kinds, ty) ∧ args.length = kinds.length ∧
      (∀ a ∈ args, NoPh a = true ∧ BvarLt (env.length + nDecl) a = true) ∧
      NoPh ty = true ∧ BvarLt (env.length + nDecl) ty = true
  | .chain env e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (env.length + nDecl) e = true
  | .loopBody base env e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (env.length + nDecl) e = true ∧
      (∀ regs, machLoopRegs (machLetTail e) = some regs → base + regs.length ≤ st.kinds.size)
  | .loopRoot env e st =>
      TrInv senv nDecl st ∧ EnvPh nDecl st env ∧ NoPh e = true ∧ BvarLt (env.length + nDecl) e = true

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

def TracePre (senv : StructEnv) (nDecl : Nat) (c : Call) : Prop := Pre c ∧ PhPre senv nDecl c

def TracePost (senv : StructEnv) (nDecl : Nat) (c : Call) (v : c.Res) : Prop :=
  Post c v ∧ FReachC nDecl (callSt c) (callOut c v) ∧ PhPost senv nDecl c v

def TraceGood (senv : StructEnv) (nDecl : Nat) (h : Hs) : Prop :=
  ∀ c, TracePre senv nDecl c → ∀ v, h c = some (some v) → TracePost senv nDecl c v
```
Texts are those of rev0 §2.1–2.3 with the rev1 corrections (R1/R2, `DomPh`/`GroupsPh` named). These are **definitions**: stating `TraceGood` proves nothing about `readF`.

```lean
theorem trInv_empty {senv : StructEnv} {nDecl : Nat} : TrInv senv nDecl ({} : MachRead)

theorem bindLetNamed_reach {nDecl : Nat} {st : MachRead} {nm : Name} {ty v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') (hn : NoLoose 0 v') :
    FReachC nDecl st { st with lets := (machBindLetNamed nm ty v' st.lets).2 } ∧
    InRange nDecl { st with lets := (machBindLetNamed nm ty v' st.lets).2 } (machBindLetNamed nm ty v' st.lets).2.size
      (machBindLetNamed nm ty v' st.lets).1 ∧
    NoLoose 0 (machBindLetNamed nm ty v' st.lets).1

theorem letIndex_reach {nDecl : Nat} {st : MachRead} {nm : Name} {kd : MixedGateBinder} {v' : Lean.Expr}
    (h : InRange nDecl st st.lets.size v') :
    FReachC nDecl st { st with lets := (machLetIndex nm kd v' st.lets).2 } ∧
    (machLetIndex nm kd v' st.lets).1 < (machLetIndex nm kd v' st.lets).2.size

theorem machInstCall?_spec {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {res : MixedGateBinder} {args : List Lean.Expr} (h : machInstCall? senv e = some (c, kinds, res, args)) :
    senv.inst c = some (kinds, res) ∧ args.length = kinds.length

theorem machInstCallS?_spec {senv : StructEnv} {e : Lean.Expr} {c : Name} {kinds : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} (h : machInstCallS? senv e = some (c, kinds, ty, args)) :
    senv.instS c = some (kinds, ty) ∧ args.length = kinds.length
```
Proof outlines (not elaborated): `trInv_empty` = `⟨fullInv_empty, …⟩` with each `CtlPh` conjunct `by simp` on empty arrays / `dom = none`; `bindLetNamed_reach` = `bindLet_reach` proof with the `machIsVar` branch removed; `letIndex_reach`: `v'` = `_machLet j` ⇒ `FReachC.refl`, `j < lets.size` from `h.2.2.2 j` (the `_machLet` clause); hit ⇒ `refl` + `Array.findIdx?_eq_some_iff_getElem`; miss ⇒ `reachC_letv` (premise `h`) + `Array.size_push`; `*_spec` by `split` on `inlSpine`'s result and `senv.inst/instS c`, `if args.length == kinds.length` ⇒ `beq_iff_eq`.
`letIndex_reach` needs only `InRange`, not `NoLoose` (the `FStep.letv` premise is `InRange` alone; the index result is a `Nat`).

## 2. Not in this unit (explicit)

`bindLetAlias_reach`, all extractor `…Ph` lemmas, `foldO_js_length`, `mapM_length_some`, `step_trace`, the seven `*_trace`, `readF_traceGood`, `PhFacts`, `SigTyPh`/`InstSFieldsDet` as used by a proof, `machineShapeF_reach`, `ShapeInputs`, `DomAtomic`: unchanged from rev0/rev1 (unapproved, **未供給**). R-trace, R-in, R-nl, R-dom for `readF` calls remain **未供給**. This unit adds definitions and four leaf lemmas; it does not reduce any FG premise and is not an acceptance of the Issue.

## 3. Check (new `Tests/Gen5/ReaderTraceCtlCheck.lean`; same requirements as `ReaderTraceCheck`)

* **TYPE.** Each def (`GroupsPh, CtlPh, TrInv, callSt, callOut, PhPre, ExprPh, ChainPh, RootPh, PhPost, TracePre, TracePost, TraceGood`) and each theorem (`trInv_empty, bindLetNamed_reach, letIndex_reach, machInstCall?_spec, machInstCallS?_spec`) compared by the same reducible comparer (`checkExpected`, `Tests/Gen3/ExpectedType.lean`) against an independent `Exp…` written from §1 above without copying the Tools file (own spelling). Non-recursive def bodies compared by value. Counting rule: one compared declaration = 1; defs and theorems counted separately; abbrevs counted with defs.
* **Recursive / match defs** `callSt, callOut, PhPre, PhPost`: independent `Exp` version plus a **full-argument agreement theorem** per def (∀ call, ∀ st / ∀ n …) proved by `cases` + `rfl`/`Iff.rfl`, not a sample (the lesson of `noPh_eq_exp`/`bvarLt_eq_exp`); finite samples may be added for mutant detection only and are reported as such.
* **MUTANT** (well-typed single changes only; rejected by signature/defeq/mismatch — **not** semantic counterexamples): `PhPre.instS` without `senv.instS c = some (kinds, ty)`; `PhPre.inst` `ord ∨ mem` ↦ `mem` only; `PhPre.inst` mem clause `args.length = 5` removed; `CtlPh` with `DomPh` dropped; `CtlPh` with `GroupsPh` dropped; `GroupsPh` bound `k + fields.length ≤` ↦ `k <`; `TracePost` without `FReachC`; `TracePost` without `PhPost`; `PhPost.conv` `NoLoose d` ↦ `NoLoose 0`; `PhPost.loopBody` `TrInv` ↦ `FullInv`; `callOut.chain` `.2.2` ↦ `.2.1`-shape (type-correct variant chosen at implementation); `TraceGood` `h c = some (some v)` ↦ `h c = some none`; `letIndex_reach` conclusion without `<`; `bindLetNamed_reach` with `FReach` for `FReachC`; `machInstCallS?_spec` without `args.length = kinds.length`. Each theorem/def mutant compared by the same comparer and counted separately from TYPE.
* **AXIOMS**: `collectAxioms` per theorem: `propext / Classical.choice / Quot.sound` only.
* **CLOSURE** (as `ReaderTraceCheck`): value-closure walk from each root *and the root itself*, unknown name `throwError`s, 3 negative controls, 2 clean controls, forbidden roots (`sorryAx / ofReduceBool / trustCompiler`) self-hit controls; unknown-name controls for root, helper value, helper type, with a clean control; every invalid fixture inside `withoutModifyingEnv`; each intended name asserted. The intended `sorry` negatives are the only `sorry` and their number is written in the header as observed in the Pod.
* Source: no `sorry`, `axiom`, `native_decide`. Real counts and categories reported; a sample count is never described as a whole-domain proof.
* Build: `kjob lake build Tools.ShippingGen5ReaderTraceCtl`, then `Tests.Gen5.ReaderTraceCtlCheck`, one at a time, logs outside the tree; success SHA recorded in the header by a comment-only commit; after the Lean commit the Issue stays `doing` with "clean build は coder". The freeze (this file) is committed **before** and separately from the Lean.
