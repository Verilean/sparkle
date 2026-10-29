# U-ARITY freeze draft rev0: call arity `(insts[k]).2.1.length = q.ports.length` from ONE trace witness

**FOR REVIEW — design only, nothing built or proved.** No Lean file, lakefile or shared definition was written or
edited, and no Lean was run. Every statement below is TEXT ONLY.

Issue `sparkle-gen3-uarity` (supply child under `sparkle-gen3-data-supply`). Base: branch `par/gen2-spec` at
**10377764**. All `file:line` citations are at 10377764. The `.lean` files are byte-identical to 649a6bf5, the base
of the DPORT report (`git diff --stat 649a6bf5 10377764` touches only two `.md` files). Route: DPORT_ROUTE_REPORT.md
rev1 §1 row L4 and §3 item 1. This document reuses its §0 inventory and does not redo it.

Citation corrections to the brief and to DPORT §0/§1 L4: the length conjunct of `CombChildRunN` is
**Tools/ShippingGen2Defs.lean:67**, not :65 (:65 is the clk/rst conjunct). The length conjunct of `SeqChildRunN` is
**Tools/ShippingMachineDepth.lean:71**, not :70 (:70 is outputs ∉ inputs). Both are the 6th conjunct, so the
projection is `.2.2.2.2.2.1` in both branches; Connect.lean:143 already uses it on the seq branch.
`Pkg.ports` is Tools/ShippingGen2Pkg.lean:80-81.

## 0. What the lemma discharges
`hlenK : (p.d.shape.insts[k]).2.1.length = q.ports.length` is a premise of `call_inRange_at`
(Tools/ShippingGen2Adapt.lean:106-112) and `callDec_of_hPointAt_at` (Adapt:167-176). It is also the arity conjunct
`args.length = q.ports.length` of `CallDec` (Defs:105). U-ARITY derives it from the run (given an inhabitant `i : ι`, §4), so at that consumer it is no longer a
premise. This does not by itself supply `CallDec` (its arity conjunct is outside `∀ i`, §4). A second consumer is `SeqFactsRN`'s `(argPorts mc).length = args.length`
(Tools/ShippingMachineCallsLinkedTNR.lean:34). Today Connect.lean:143 gets it from `CallDec`'s `hlen`.

## 1. Ingredients (all exist at 10377764)
| # | fact | file:line |
|---|---|---|
| I1 | trace witness: `∃ ids … cache … regs … lets …, MachineWired … ∧ X ids cache ∧ …` | Tools/ShippingMachineTraceX.lean:377-393 (`MachineTraceLBX`); destructuring pattern `⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, trace⟩` at Tools/ShippingGen2OneOut.lean:175 |
| I2 | one-output call k has `args mc st`, `st ∈ m.body`, `moduleByName`, `CallStmt` (5th conjunct) | Tools/ShippingMachineEntry.lean:664-666 |
| I3 | group call k has `st ∈ m.body`, `args outs mc`, `CallStmtG`, `moduleByName`, `(k, instFields.getD k "") ∈ outs`, args (13th conjunct) | MachineEntry:720-724; obtain pattern (5th = `calls1`, 13th = `gCalls`) at Tools/ShippingGen2C6.lean:60 |
| I4 | `CallStmt`: `args.mapM (fun j => names[nIn+kI+n+j]?) = some argWs`, `(mc.inputs.filter …).length = argWs.length` | Tools/ShippingMachineInst.lean:190-203 (:193, :196) |
| I5 | `CallStmtG`: same two conjuncts; `st = .inst mc.name iname (…)`, whose connection list is literally `connsG mc argWs outs outWs` | Tools/ShippingMachineInstG.lean:19-37 (:23, :24, :32-37); `connsG` Tools/ShippingMachineLinkedT.lean:28-34 |
| I6 | `mapM_some`: `r.length = l.length ∧ ∀ i < l.length, ∃ y, f l[i] = some y ∧ r[i]? = some y` | MachineInst:167-169 |
| I7 | `argPorts mc = mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst")` (definitional) | Tools/ShippingMachineCompose.lean:234-235 |
| I8 | `Served1P Q …`: for every `k hk args mc st` with `CallStmt` in the trace names and `moduleByName`: memory-origin ∨ `∃ Dc, Q (insts[k]).1 (mc, Dc) ∧ Dc ⊆ dsn` | Defs:231-240 |
| I9 | `ServedGP Q …`: same for `Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ m.body`, `outs.mapM … = some outWs`, `∃ e ∈ outs, e.1 = k` | Defs:216-227 |
| I10 | `ServedP = ServedGP ∧ Served1P` (`hx.1` group, `hx.2` one-output) | Defs:242-244; `hx.2` used at OneOut:194, FitChain:940 |
| I11 | `ShipsRes L P c r := RealChildA L.O c r ∧ ∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2` | Defs:135-136 |
| I12 | `ChildShips q n mc Dc := ∀ dsn, Dc ⊆ dsn → moduleByName dsn mc.name = some mc → ∀ i, ChildRunN … mc (q.d.bsIn.take q.kD) …` | Defs:87-90 |
| I13 | `ChildRunN = SeqChildRunN ∨ CombChildRunN`; 6th conjunct `(argPorts mc).length = (bsC.filter fun b => b.2 != .domain).length` | Defs:77-80, :67; Depth:64-71 |
| I14 | `Pkg.ports q = (q.d.bsIn.take q.kD).filter fun b => b.2 != .domain` | Gen2Pkg:80-81 |
| I15 | package identification idiom: `obtain ⟨_, q', n', hq', _, hcs'⟩ := hship; have hqq : q' = q := Option.some.inj (hq'.symm.trans hq)` | OneOut:200-202 |

## 2. Complete statements (new file `Tools/ShippingGen3Arity.lean`)
Ambient header (text):
```lean
import Tools.ShippingGen2Defs
set_option autoImplicit false

namespace Tools.ShippingGen3Arity
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Tools.ShippingGen2 Tools.ShippingMachineEntry Tools.ShippingMachineLinked
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingChildInv (Res)
```
`Tools.ShippingGen2Defs` already imports `Tools.ShippingGen2Pkg`, `ShippingMachineTraceX` (through `Srm33Core`, used
at Defs:259), `ShippingMachineInst` and `ShippingMachineInstG` (through `ShippingMachineLinkedT`). The import list is
checked when the file is built. Every declaration below has all of its binders written out; no `variable` is used.

```lean
/-- (A0) The `args` read from the instance list is call `k`'s argument list. -/
theorem insts_args_eq {shape : MachineShape} {k : Nat} (hk : k < shape.insts.length) {args : List Nat}
    (hargs : (shape.insts.map (·.2.1))[k]? = some args) :
    args = (shape.insts[k]).2.1

/-- (A1) The length conjunct of `ChildRunN`, both branches (Defs:67, MachineDepth:71). -/
theorem childRunN_argLen {children : String → Option (Module × Sparkle.IR.Semantics.WEnv)}
    {dsn : Design} {n : Nat} {mc : Module} {bsC : List (Name × MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (h : ChildRunN children dsn n mc bsC outsC S) :
    (argPorts mc).length = (bsC.filter fun b => b.2 != .domain).length

/-- (A2) `CallStmt` fixes the arity of the statement: the argument list and the module's argument ports. -/
theorem callStmt_argLen {nIn kI n k : Nat} {names : List String} {args : List Nat} {mc : Module} {st : Stmt}
    (h : Tools.ShippingMachineInst.CallStmt nIn kI n names k args mc st) :
    args.length = (argPorts mc).length

/-- (A3) The same for `CallStmtG`. -/
theorem callStmtG_argLen {nIn kI n : Nat} {names : List String} {args : List Nat}
    {outs : List (Nat × String)} {mc : Module} {st : Stmt}
    (h : Tools.ShippingMachineInstG.CallStmtG nIn kI n names args outs mc st) :
    args.length = (argPorts mc).length

/-- (A4) A shipping served result has as many argument ports as the package `q` that `P` selects. -/
theorem argLen_of_shipsRes {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) {c : Name} {q : Pkg ι dom} {mc : Module} {Dc D : Design}
    (i : ι)
    (hship : ShipsRes L P c (mc, Dc)) (hP : P c = some q)
    (hDc : ∀ g ∈ Dc.modules, moduleByName D.modules g.name = some g)
    (hmod : moduleByName D.modules mc.name = some mc) :
    (argPorts mc).length = q.ports.length

/-- **(A5) U-ARITY, one-output parent, fixed witnesses.** `hS` is `hx.2` of the trace's own `ids`/`cache`; `(k, args, mc,
st)` is the call's instance from the SAME `MachineWired`. The second conjunct exposes the successful `mapM`. -/
theorem callArity_one {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Module} {D : Design} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (hS : Served1P (ShipsRes L P) p.decl p.d.shape raw D ids cache)
    (hf0 : p.d.shape.instFields = []) (i : ι)
    {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q)
    {args : List Nat} {mc : Module} {st : Stmt}
    (hargs : (p.d.shape.insts.map (·.2.1))[k]? = some args) (hst : st ∈ raw.body)
    (hcs : Tools.ShippingMachineInst.CallStmt (machNIn p.d.shape) p.d.shape.insts.length
      p.d.shape.layout.slots.length ((machPorts p.decl ids cache p.d.shape.binders).map (·.name)) k args mc st)
    (hmod : moduleByName D.modules mc.name = some mc) :
    (p.d.shape.insts[k]).2.1.length = q.ports.length ∧
    ∀ (argWs : List String),
      args.mapM (fun j => ((machPorts p.decl ids cache p.d.shape.binders).map (·.name))[machNIn p.d.shape +
        p.d.shape.insts.length + p.d.shape.layout.slots.length + j]?) = some argWs →
      argWs.length = q.ports.length

/-- **(A6) U-ARITY, group parent, fixed witnesses.** `hS` is `hx.1`; `(st, args, outs, mc)` is call `k`'s group
statement from the SAME `MachineWired` (MachineEntry:720-724). -/
theorem callArity_group {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Module} {D : Design} {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    (hS : ServedGP (ShipsRes L P) p.decl p.d.shape raw D ids cache)
    (hfne : p.d.shape.instFields ≠ []) (i : ι)
    {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q)
    {args : List Nat} {outs : List (Nat × String)} {mc : Module} {st : Stmt}
    (hargs : (p.d.shape.insts.map (·.2.1))[k]? = some args) (hst : st ∈ raw.body)
    (hcs : Tools.ShippingMachineInstG.CallStmtG (machNIn p.d.shape) p.d.shape.insts.length
      p.d.shape.layout.slots.length ((machPorts p.decl ids cache p.d.shape.binders).map (·.name)) args outs mc st)
    (hkout : (k, p.d.shape.instFields.getD k "") ∈ outs)
    (hmod : moduleByName D.modules mc.name = some mc) :
    (p.d.shape.insts[k]).2.1.length = q.ports.length ∧
    ∀ (argWs : List String),
      args.mapM (fun j => ((machPorts p.decl ids cache p.d.shape.binders).map (·.name))[machNIn p.d.shape +
        p.d.shape.insts.length + p.d.shape.layout.slots.length + j]?) = some argWs →
      argWs.length = q.ports.length

/-- **(A7) U-ARITY from ONE `MachineTraceLBX` witness** (both parent kinds, by cases on `instFields`). This is the form
that discharges `hlenK` of Adapt:110 / :174. -/
theorem callArity_of_trace {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {raw : Module} {D : Design}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (i : ι) {k : Nat} (hk : k < p.d.shape.insts.length)
    (hnone : (p.d.shape.instOrigins.getD k .ord).child? = none)
    {q : Pkg ι dom} (hP : P (p.d.shape.insts[k]).1 = some q) :
    (p.d.shape.insts[k]).2.1.length = q.ports.length
```

## 3. Proof route, step by step (premise that supplies each step)
**A0** `insts_args_eq`: `rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hargs`; then
`exact (Option.some.inj hargs).symm`. Premise: `hk`.

**A1** `childRunN_argLen`: `rcases h with h | h <;> exact h.2.2.2.2.2.1`. Supplied by the 6th conjunct (Depth:71 /
Defs:67). The pattern is already used at Connect:143.

**A2** `callStmt_argLen`: `obtain ⟨_, argWs, _, _, _, hmap, _, _, hlen, _⟩ := h`, giving I4 (:193, :196). Then
`(mapM_some _ _ _ hmap).1 : argWs.length = args.length` (I6), and `hlen` is
`(argPorts mc).length = argWs.length` by `argPorts`'s definition (I7, `show`/`rfl`). Finish with `omega` or `trans`.

**A3** `callStmtG_argLen`: `obtain ⟨_, argWs, _, _, hmap, hlen, _⟩ := h` (I5 :23-24), then the same as A2.

**A4** `argLen_of_shipsRes`: `obtain ⟨_, q', n', hq', _, hCS⟩ := hship` (I11). `q' = q` by I15. Then
`childRunN_argLen (hCS D hDc hmod i)` (I12, A1). Finish with `unfold Pkg.ports` (I14). `bsC` is literally
`q.d.bsIn.take q.kD`, and the filter predicate is syntactically the same lambda.

**A5** `callArity_one`:
1. `rcases hS hf0 k hk args mc st hargs hst hcs hmod with ⟨md, hmd, _⟩ | ⟨Dc, hship, hDc⟩` (I8; the same pattern as
   OneOut:194).
2. Memory disjunct: `rw [hnone] at hmd; cases hmd`. Premise: `hnone`. The `getD` normalisation of OneOut:197 may be
   needed.
3. `hA := argLen_of_shipsRes L P i hship hP hDc hmod` (A4). Premises: `hP` and `i`.
4. `hB := callStmt_argLen hcs` (A2).
5. Conjunct 1: `rw [← insts_args_eq hk hargs]; omega` (A0).
6. Conjunct 2: `intro argWs hm; have := (mapM_some _ _ _ hm).1; omega`. The mapM function in the statement is the
   one inside `hcs`; the arity follows from A2/A4 alone and needs no uniqueness of `argWs`.

**A6** `callArity_group`:
1. `obtain ⟨outWs, argWs, iname, hout, hmapA, -, -, -, -, -, -, -, -, -, heq⟩ := hcs` (I5, 12 conjuncts). Then
   `subst heq`, so that `hst : Stmt.inst mc.name iname (…) ∈ raw.body`.
2. `rcases hS hfne k hk mc iname argWs outs outWs hst hout ⟨_, hkout, rfl⟩ hmod with ⟨md, hmd, _⟩ | ⟨Dc, hship, hDc⟩`
   (I9). The `hst` argument relies on `connsG` (LinkedT:28-34) being VERBATIM the connection list of CallStmtG:33-37,
   so it is accepted by `exact`/defeq. `hout`'s function `fun (k, _) => names[nIn + k]?` (CallStmtG, nIn :=
   `machNIn p.d.shape`) must be defeq to ServedGP's `fun (j, _) => names[machNIn shape + j]?`. **Build risk B1:** the
   two pattern lambdas elaborate to two different auxiliary matchers. They are defeq by delta, but there is no
   consumer precedent (grep: no `ServedGP`/`ServedRealGA` is consumed at 10377764). Fallback: `simpa using hout`, or
   rewrite through `List.mapM_congr` with `fun ⟨j, _⟩ => rfl`. The S3 group work (another agent, in progress) hits the
   same point, so coordinate.
3. Memory disjunct excluded by `hnone`, as in A5.2.
4. Then A4, A3 (on the un-destructured `hcs`, kept with `have hcs0 := hcs` before step 1), A0, and `mapM_some`, as in
   A5.3-6.

**A7** `callArity_of_trace`:
1. `obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, -⟩ := h` (I1). This is the ONE obtain: the
   same `ids`/`cache` feed `wired` and `hx`.
2. `obtain ⟨-, -, -, -, calls1, -, -, -, -, -, -, -, gCalls, -⟩ := wired` (I2/I3; positions as C6:60). The exact
   tail pattern is checked when built.
3. `by_cases hf0 : p.d.shape.instFields = []`.
   - one-output: `obtain ⟨args, mc, st, hargs, hst, hmod, hcs⟩ := calls1 hf0 k hk`, then
     `exact (callArity_one L P p hx.2 hf0 i hk hnone hP hargs hst hcs hmod).1`.
   - group: `obtain ⟨st, hst, args, outs, mc, hcs, hmod, hkout, hargs⟩ := gCalls hf0 k hk`, then
     `exact (callArity_group L P p hx.1 hf0 i hk hnone hP hargs hst hcs hkout hmod).1`.

## 4. What is conditional, and what is not
- **Package identification (R3 of the DPORT review): NOT conditional for arity.** The `q` used is the `hP` package.
  `ServedP` yields `ShipsRes L P (insts[k]).1 (mc, Dc)`, whose package `q'` satisfies `P (insts[k]).1 = some q'`.
  Then `q' = q` by `Option.some.inj` (I15), since `P` is a function. The module `mc` is fixed because
  `Served1P`/`ServedGP` are universally quantified over `(k, args, mc, st)` and are instantiated at the very witness
  that `MachineWired` (same obtain) gives. `core_callPorts_ranA` and its `RealChildA O … y` are NOT used. The R3
  identification gap (RunFactsA:432-433's `y` vs ServedP's `q`) therefore does not arise for arity. It reappears only
  if a later composition takes `mc` from `core_callPorts_ranA` rather than from this witness (see UARGW §4).
- **CONDITIONAL on an inhabitant `i : ι`** (named premise `i`). `ChildShips` gives `ChildRunN` only under `∀ (i : ι)`
  (Defs:90), and arity does not depend on `i`. With empty `ι`, the length cannot be extracted from the existing
  `ChildShips` along this route. No general non-derivability theorem is shown (this is a statement about this route
  only). `CallDec`'s arity conjunct (Defs:105) is OUTSIDE its `∀ i` (:106), so `CallDec` is NOT claimed supplied
  merely because FG's `∀ i` parts are vacuous for empty `ι`: the arity conjunct still has to be supplied there. A
  consumer that builds `CallDec` for an arbitrary `ι` must split on `Nonempty ι`, as `oneOut_topShips` does
  (OneOutTop:17-19, `Classical.em (Nonempty ι)`). For the empty case: a per-declaration decided row
  `(insts[k]).2.1.length = q.ports.length` through a concrete `P` (DataBridge b1 style, supplier-local, not general
  coverage), or, later, a `ChildPortWidths` conjunct supplied OUTSIDE `∀ i` (UCHILD_PORTTYS_TABLE.md §1), whose
  `List.length_map` gives a static length and would lift this restriction. Which one is used is a consumer decision and
  is not taken here. A7 is implemented now, with the premise `i`, without waiting for either.
- **`hnone` (ordinary origin)** is a premise. It is `CallDec.1` (Defs:103) and `callDec_of_hPointAt_at`'s `hnone`
  (Adapt:169), so it is already in hand at the consumer.
- **Not claimed:** nothing about widths (that is L2/L5/L6, UARGW_PARENT_SURVEY.md / UCHILD_PORTTYS_TABLE.md).
  Arity alone does not supply `callArgsOkAt`.

## 5. Controls (new file `Tests/Gen3/ArityCheck.lean`)
Fixtures reused, not imported twice: `pbhPkg`/`PL` are copied in the style of Tests/Gen2/DataBridgeCheck.lean:37-50,
and `callerL` is Tests/Compiler/ShippingMachineLinkedTest.lean:31 (one call of `pickByteH`, 2 arguments `w`, `selS`,
`instFields = []`).
- **P1 (pure, one-output, real data):** `callerL_arity_row : (callerL.machineData.shape.insts[0]'(by decide)).2.1.length
  = pbhPkg.ports.length` by `decide`/`decide +kernel` (expected 2 = 2). The premises are also decided, so the lemma
  is not vacuous on this data: `callerL_hnone : (callerL.machineData.shape.instOrigins.getD 0 .ord).child? = none`, and
  `callerL_hP : PL (callerL.machineData.shape.insts[0]'_).1 = some pbhPkg`. The latter goes through `PL`, as
  `callerL_strictPL`, DataBridgeCheck:85-88.
- **P2 (conditional instance, one-output):** `callerL_arity (L) (p : Pkg Unit U) (hp : p.d = callerL.machineData) {raw D}
  (h : MachineTraceLBX (ServedP (ShipsRes L PL) p.decl p.d.shape raw D) …) : (p.d.shape.insts[0]'_).2.1.length =
  pbhPkg.ports.length := callArity_of_trace L PL p h () _ (hp ▸ callerL_hnone) (hp ▸ callerL_hP)`. This exercises the
  application path only: this unit exhibits no package/run witness for `callerL` (DataBridgeCheck:10-15).
- **P3 (group, real data):** `parent` (Tests/Compiler/ShippingMachineSeqTest.lean:28; structure result of the
  sequential `cnt`, :20; `instFields ≠ []`; ordinary origin). Decide `parent.machineData.shape.instFields ≠ []`, `hnone`
  at k = 0, and `(parent.machineData.shape.insts[0]'_).2.1.length = ((cnt.machineData.bsIn.take
  cnt.machineData.bsIn.length).filter fun b => b.2 != .domain).length` (expected 1 = 1; `{dom}` is a domain binder and
  is filtered). This is data only. No `cnt` package is built here, and `parent_insts_cnt` exists at
  Tests/Compiler/ParentEndpointFactsATest.lean:38-39.
- **N1 (arity-mismatch shape, pure):** a toy `mc2` with two non-clk/rst inputs, `args := [0]`, and any `names` such
  that the `mapM` succeeds. Prove `¬ CallStmt nIn kI n names k [0] mc2 st` and `¬ CallStmtG …` from A2/A3 by
  `decide`-closing `1 ≠ 2`. This shows the compiler's count check is what A2 reads.
- **N2 (mismatched package excluded):** `∀ (P' : Pkgs Unit U) (q2 : Pkg Unit U), P' ``pickByteH = some q2 →
  q2.ports.length ≠ 2 → ∀ p, p.d = callerL.machineData → ¬ MachineTraceLBX (ServedP (ShipsRes L P') p.decl …) …`.
  The proof is A7 plus the decided row. A concrete `q2` with a decided `q2.ports.length ≠ 2` is the existing `lmPkg`
  (Tests/Gen2/MemParentInstance.lean:28) or `leaf16Pkg` (Tests/Gen2/LeafInstance.lean); decide first, and report if
  the count happens to be 2.
- **V (vacuity):** restricted to the DATA part: the data premises of A5/A6/A7 (`hk`, `hnone`, `hP`, `instFields`)
  are jointly satisfiable on real data (P1/P3). P1/P3 are data controls only; they say nothing about the run premises. A run-level positive
  instance has the same status as in S4/S3 (none in Tests/, S3_GROUP_FREEZE.md:59-63).

## 6. Audit (stated in the file headers when built)
1. Expected types: each statement of §2 is compared MECHANICALLY (`==` after `instantiateMVars`, else `isDefEq`) with an
   independent `Expected…` Prop written in the check file, and meaning-changing mutants must FAIL that comparison. A
   `#check` display is not a substitute for this frozen-type comparison.
2. `#print axioms` of `childRunN_argLen`, `callStmt_argLen`, `callStmtG_argLen`, `argLen_of_shipsRes`,
   `callArity_one`, `callArity_group`, `callArity_of_trace` and every control: standard axioms
   (`propext`, `Classical.choice`, `Quot.sound`) or a subset. No `sorry`/`axiom`/`native_decide`.
3. A7 has ONE `obtain` of the `MachineTraceLBX` (`wired` and `hx` share `ids`/`cache`).
4. The file references neither `core_callPorts_ranA` nor `RealChildA` (grep). `q` is identified only through
   `Option.some.inj` on `P`.
5. No shared definition changed: `git diff --stat` touches only the two new files plus the lakefile registration.

## Result dependencies (shared by UARITY_FREEZE.md, UARGW_PARENT_SURVEY.md, UCHILD_PORTTYS_TABLE.md)
| unit | supplies | side | alone reaches `callArgsOkAt`? |
|---|---|---|---|
| U-ARGW-PARENT (`core_inputWidth_A`, `core_callArgPorts_oneA`/`_ranA`) | `declWidth b argWs[j] = (kindTy binders[nDecl+(kI+(n+a))].2).bitWidth` | PARENT (let wire) | no |
| U-CHILD-PORTTYS (`ChildPortWidths`, N-A/N-B, P1-P4) | `(argPorts mc).map (·.ty.bitWidth) = q.ports.map (kindTy ·.2).bitWidth` | CHILD (served module) | no |
| U-ARITY (`callArity_of_trace`) | `(insts[k]).2.1.length = q.ports.length` | the matching INDEX RANGE | no |
| SRC-ARGW (scripts/gen3/SRC_ARGW_FREEZE.md, separate unit) | the width equality L6/L6w for the same call | source | — |

The three results above reach `callArgsOkAt p.d p.kD k q.portWidths` only when composed with SRC-ARGW's width equality
for the SAME call (same `k`, statement, `mc`, `q`, and one `MachineTraceLBX` witness). None of them, nor any pair of
them, supplies the row alone.

## 7. Size, files, build
- `Tools/ShippingGen3Arity.lean`: about 110-140 lines (A0-A4 about 40, A5/A6 about 30 each, A7 about 25).
- `Tests/Gen3/ArityCheck.lean`: about 80-100 lines.
- lakefile: one `lean_lib` per new root (pattern lakefile.lean:4458-4468). It is edited only at build time and
  serialized with the other agent's concurrent lakefile edit.
- Build through `kjob … run --issue sparkle-gen3-uarity -- kjob lake build Tools.ShippingGen3Arity
  Tests.Gen3.ArityCheck` at the exact head, linked to the issue; incremental. Build time is an unmeasured estimate (no
  fixed duration, and no mandatory cold rebuild).
- **Interface drift note:** `par/gen3-induct` (96cbd548, Defs:136) makes `ShipsRes` a 3-conjunct
  `RealChildA ∧ (∃ q n, …) ∧ InstClosed r` (G-POST). If U-ARITY is built on that base, A4's obtain becomes
  `obtain ⟨_, ⟨q', n', hq', _, hCS⟩, _⟩ := hship`. This is a one-line change and the statements are unaffected.
