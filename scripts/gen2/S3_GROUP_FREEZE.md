# S3 group parents (`instFields ≠ []`, `closeInstsG`): the general comb child — freeze DRAFT rev0, FOR REVIEW (nothing built or proved)

- **Issue:** `sparkle-gen2-step` (S3 of STEP_IFACE_FREEZE.md rev3 §4, lines 145-152; order §5 item 4).
- **Branch:** `par/gen2-spec`. Frozen source SHA **649a6bf5**; every `file:line` below is at 649a6bf5, from a read-only survey.
- **What this is:** exact types for S3 (new files only), stages, controls, audit. No Lean is changed by this document;
  nothing in it is built or proved. Compiler/Elab and shared definitions (`Tools/ShippingGen2Defs.lean`, `MachineDepth`,
  `CallsLinkedTNR`, `Consumer`, `Connect`) are untouched. FG/T1Stmt/StepStmt unchanged; no new semantic premise.

## 1. The existing types (as read)
| name | file:line | what matters for S3 |
|---|---|---|
| `connsG mc argWs outs outWs` | Tools/ShippingMachineLinkedT.lean:28-34 | clk/rst pair appended **only if** `mc.inputs.any (clk ∨ rst)` (:31-32); args zip with `mc.inputs.filter (≠clk,≠rst)` (= `argPorts`, Compose.lean:234) |
| compiler `instStmtG` | Sparkle/IR/MachineInstG.lean:30-53 | `seq := mc.inputs.any (clk ∨ rst)` (:43); comb child (`seq = false`) gets NO clk/rst — same text as `connsG`. `closeInstsG` (:115) accepts comb children |
| `isSeqChild` | Tools/ShippingInstStmtG.lean:20-21 | `mc.inputs.any (clk ∨ rst)` |
| `RunOn` / `runKS_RunOn` | Tools/ShippingMachineDepth.lean:27-31 / :34-40 | `runKS (KSn children n) mc … = RunOn children n mc (connEnvS cin ∘ P) T s`, for **every** `mc`, `n`; no `instFree`, no clk/rst premise |
| `ResetN` | Depth:52-61 | regs/mems/latches, instances one level down; nothing sequential-specific |
| `SeqChildRunN` | Depth:64-79 | `"clk" ∈`, `"rst" ∈` inputs (:68-69); run premises `ins t "rst" = 0`, `ins t "clk" = 0` (:76) |
| `seq_inst_runN` | Depth:98-250 (type :98-122) | uses clk/rst at: `hclk`/`hrst` from `hrun` (:123); `input_cases` clk/rst branch + `connsG_clkrst hclk` (:142, :163-169); `hrstP`/`hclkP` (type :107, used :212-221); `connsG_keys` clk/rst disjuncts refuted by `hclk`/`hrst` (:184-189); `connsG_field hclk hrst` (:229) |
| `CombChildRunN` | Tools/ShippingGen2Defs.lean:60-75 | `"clk" ∉`, `"rst" ∉` (:66); no clk/rst run premise; same `RunOn`/`ResetN`/conclusion as `SeqChildRunN` |
| `ChildRunN` | Defs:77-80 | `SeqChildRunN ∨ CombChildRunN` |
| `ChildShips` / `ShipsRes` / `ShipsAt` | Defs:87-90 / :135-136 / :147-148 | `ShipsAt` fixes the height `n` |
| `ServedGP` / `Served1P` / `ServedP` | Defs:216-229 / :231-240 / :242-244 | group disjunct: the `connsG` instance of call `k` is a `Q`-result of `(insts[k]).1` |
| `ServedPC Q dsn` | Defs:264-266 | `fun c mc => moduleByName … = some mc ∧ ∃ Dc, Q c (mc, Dc) ∧ Dc ⊆ dsn` |
| `StepStmt` | Defs:300-315 | premise `∀ k hk, MemDec p k _ ∨ ∃ q, P _ = some q ∧ CallDec p q k` (:309-310); trace over `ServedP (ShipsRes L P)` |
| `SeqFactsRN` | Tools/ShippingMachineCallsLinkedTNR.lean:23-41 | `∀ mc, PC c mc → SeqChildRunN … ∧ argPorts length` (:33-34) + non-run conjuncts |
| `calls_hchildRN` | TNR:46-191 (type :46-91) | `hcalls : MemFacts ∨ SeqFactsRN … PC` (:62-64); seq branch calls `seq_inst_runN` with `hrstP hclkP` (:153-155) |
| `MemFacts` | Tools/ShippingMachineCallsLinkedT.lean:31 | unchanged |
| `machine_linkedT_callsServed` | Tools/ShippingGen2Consumer.lean:30-105 | `hcalls` 2-way with `PC := ServedPC Q dsn` (:55-60); `hsv` discharged from `hx.1` (:96-104) |
| `machine_linkedTG_of` | Tools/ShippingMachineLinkedTG.lean:30-110 | child callback (:84-110) has no sequential assumption; supplies `Pw t "rst" = 0`, `Pw t "clk" = 0` |
| `seqFactsRN_of_callDec` | Tools/ShippingGen2Connect.lean:120-147 | `hseq : ∀ mc, ServedPC (ShipsAt L P n) dsn c mc → "clk" ∈ …` (:125); C2 at :140 |
| C1-C3 | Tools/ShippingGen2AComb.lean:18, :23, :28 | `childRunN_of_seq`, `not_seq_and_comb`, `childRunN_iff_seq` |
| `combChildRunN_of_noClk` | Tools/ShippingGen2OneOut.lean:78-83 | `"clk" ∉ → ChildRunN → CombChildRunN` |
| precedent 3-way | Tools/ShippingMachineCallsLinkedTG.lean:257-460 | depth 0, per-NAME flag `gk c`; mixed instance refuted via the clock (:415-420) |
| memory route | Tools/ShippingGen2MemParent.lean:75-103, MemShips.lean:39-84 | `pkg_memComposedNW` → `ComposedNW` → C6 (`seqChildRunN_of_composedNW_run`, Gen2C6.lean:28) with `closeInstsG_acyclic` |

## 2. Findings
1. **Where the sequential assumption sits.** Only in `seq_inst_runN` (the five places in §1) and in `SeqFactsRN`'s
   predicate. `machine_linkedTG_of`, `ServedP`, `ServedPC`, `ResetN`, `RunOn`, `runKS_RunOn` carry none.
2. **What `comb_inst_runN` needs instead.** With `"clk" ∉` and `"rst" ∉`: the `if` of `connsG` (LinkedT:31) is false, so
   the keys are argument ports and read fields only; every input is an argument port (`input_cases`' clk/rst branch is
   refuted by `hclk`/`hrst`); no clk/rst stream premise. Two new small `connsG` lemmas (§3 A1, A2); `connsG_arg`
   (SeqInst:110) and `lookup_filter_keep/none` (SeqInst:83-108) are already generic.
3. **Hierarchical comb children: no extra premise at S3.** `comb_inst_runN` ends with `runKS_RunOn` (Depth:34), valid for
   every `mc` and depth with no `instFree`; `CombChildRunN` is itself stated with `RunOn children n` (Defs:72), so a child
   with instances is covered; its kids' reset is inside `ResetN` (Depth:58-61), supplied by the consumer's `hreset`
   (TNR:53-54). The producer of `CombChildRunN` for a child WITH instances is S5
   (`combChildRunN_of_composedNW_run`), not S3. **No STOP for the consumer.**
4. **Why the literal disjunction `MemFacts ∨ SeqFactsRN ∨ CombFactsRN` (per call) does not work.** `PC c` is per callee
   NAME; a disjunct chosen per call must hold for every module `PC c` admits — i.e. a universal `hseq` (or its negation).
   The served module is known only inside the consumer, after `intro mc`. Hence the per-call premise is a CONJUNCTION with
   `PC` restricted by the branch (allowed by STEP_IFACE_FREEZE §4 S3 bullet "`hseq` obligation"), and the consumer
   branches on the actual instance module (decision D1).
5. **The `hseq` obligation is met without `hseq`.** The supplier proves `SeqFactsRN (seqPC PC)` using the `"clk" ∈` carried
   by `seqPC` (C2), and `CombFactsRN (combPC PC)` using `"clk" ∉` (`combChildRunN_of_noClk`). No universal `hseq`; no new
   T1/FG premise.
6. **Heights.** Hierarchical (and sequential) kids need the fixed height: `Q := ShipsAt L P n`, as `Connect` already
   does. The trace from G-SERVED is over `ShipsRes`; bridging is G-LIFT (open). S4 could use `ShipsRes` only because its
   kids are instance-free.
7. **Positive real-declaration instance: none found in Tests/.** Group parents in the corpus (`ShippingMachineSeqTest`,
   `KaryThreeTest`, `MultiInstanceTest`, memory parents) have sequential or memory children; machine-route comb children
   (`pickByteH`, Tests/Compiler/ShippingMachineLinkedTest.lean:20) are called by one-output parents (`callerL`,
   `callerLN`). A group closing arises from structure results, memory calls or Bool results (Elab.lean:3960, 4058,
   4123-4125; selection :5261-5263). See control P2 (probe, §6).

## 3. Stage A — pure lemmas and the per-instance consumer (new file `Tools/ShippingGen2GroupComb.lean`)
Ambient: `import Tools.ShippingGen2OneOut`, `import Tools.ShippingMachineCallsLinkedTNR`, `import Tools.ShippingInstStmtG`;
`set_option autoImplicit false`; `namespace Tools.ShippingGen2`; the `open`s of TNR:9-17 and Depth:15-22 verbatim, plus
`open Tools.ShippingMachineSeqInst (lookup_filter_keep lookup_filter_none lookup_some_mem connsG_arg)`;
`variable (children : String → Option (Module × WEnv))` (explicit, as Depth:24, so argument order matches).

**A1 `connsG_keys_comb`** — copy of `connsG_keys` (SeqInst:48-68); rule: add `hclk`/`hrst` (∉), drop the clk/rst disjuncts.
```lean
theorem connsG_keys_comb {mc : Module} {argWs : List String} {outs : List (Nat × String)}
    {outWs : List String} {x : String} {e : Expr}
    (hclk : "clk" ∉ mc.inputs.map (·.name)) (hrst : "rst" ∉ mc.inputs.map (·.name))
    (h : (x, e) ∈ connsG mc argWs outs outWs) :
    x ∈ (argPorts mc).map (·.name) ∨ x ∈ outs.map (·.2)
```
**A2 `connsG_field_comb`** — copy of `connsG_field` (SeqInst:166-190); rule: `hclk`/`hrst` from `∈` to `∉`.
```lean
theorem connsG_field_comb {mc : Module} {argWs : List String} {outs : List (Nat × String)}
    {outWs : List String} (hclk : "clk" ∉ mc.inputs.map (·.name))
    (hrst : "rst" ∉ mc.inputs.map (·.name)) {x : String} {e : Expr}
    (h : (x, e) ∈ connsG mc argWs outs outWs) (hx : x ∉ mc.inputs.map (·.name)) :
    ∃ w, e = .ref w ∧ (x, w) ∈ (outs.map (·.2)).zip outWs
```
**A3 `comb_inst_runN`** — copy of the TYPE of `seq_inst_runN` (Depth:98-122); rule: `SeqChildRunN` → `CombChildRunN` in
`hrun` and in `hout`; `hrstP`/`hclkP` DELETED (decision D3). Proof: Depth:123-250 minus the clk/rst parts (§2.2).
```lean
theorem comb_inst_runN (dsn : Design) (n : Nat) {mc : Module} {bsC : List (Name × MixedGateBinder)}
    {outsC : List OutField} {S : (Nat → List Nat) → List (Nat → Nat)}
    (hrun : CombChildRunN children dsn n mc bsC outsC S) (argWs : List String) (outs : List (Nat × String))
    (outWs : List String) (Pw : Nat → Env) (T : Nat) (kid : KT n) (vals : Nat → List Nat)
    (hlen : argWs.length = (argPorts mc).length)
    (hfields : ∀ f ∈ outs.map (·.2), f ∈ mc.outputs.map (·.name))
    (hrange : ∀ τ, τ < T → Tools.ShippingMachineChild.InRange (vals τ) (bsC.filter fun b => b.2 != .domain))
    (hargs : ∀ t, t < T → argWs.map (Pw t) = vals (T - 1 - t))
    (hreset : ResetN dsn n mc kid)
    (hout : ∀ (idx : Nat) (e : Nat × String) (w : String), outs[idx]? = some e → outWs[idx]? = some w →
      ∃ (bsC' : List (Name × MixedGateBinder)) (outsC' : List OutField) (S' : (Nat → List Nat) → List (Nat → Nat)),
        CombChildRunN children dsn n mc bsC' outsC' S' ∧
        (∀ τ, τ < T → Tools.ShippingMachineChild.InRange (vals τ) (bsC'.filter fun b => b.2 != .domain)) ∧
        ∃ (k : Nat) (o : OutField) (f : Nat → Nat), outsC'[k]? = some o ∧ o.name = e.2 ∧
          (S' vals)[k]? = some f ∧ ∀ t, t < T → Pw t w = f (T - 1 - t)) :
    ∃ cenvs, runKS (KSn children n) mc (Sparkle.IR.RegDedup.declWidth mc)
        (inConns mc.outputs (connsG mc argWs outs outWs)) Pw T kid = some cenvs ∧
      ∀ j, j < T → ∀ p ∈ mc.outputs, ∀ w,
        (connsG mc argWs outs outWs).lookup p.name = some (.ref w) →
        (cenvs[j]?).map (· p.name) = some (Pw (T - 1 - j) w)
```
**A4 branch predicates and `isSeqChild` agreement** (new; D2):
```lean
def seqPC (PC : Name → Module → Prop) : Name → Module → Prop := fun c mc => PC c mc ∧ "clk" ∈ mc.inputs.map (·.name)
def combPC (PC : Name → Module → Prop) : Name → Module → Prop := fun c mc => PC c mc ∧ "clk" ∉ mc.inputs.map (·.name)
theorem isSeqChild_of_seqRunN {dsn n mc bsC outsC S} (h : SeqChildRunN children dsn n mc bsC outsC S) :
    Tools.ShippingInstStmtG.isSeqChild mc = true
theorem isSeqChild_of_combRunN {dsn n mc bsC outsC S} (h : CombChildRunN children dsn n mc bsC outsC S) :
    Tools.ShippingInstStmtG.isSeqChild mc = false
```
(implicit binders typed as in A3.)
**A5 `CombFactsRN`** — verbatim copy of `SeqFactsRN` (TNR:23-41); rule: `SeqChildRunN children dsn n mc` (:34) →
`CombChildRunN children dsn n mc`. Same binders, order, conclusion otherwise.
```lean
def CombFactsRN (children : String → Option (Module × WEnv)) (n : Nat) {D : DomainConfig}
    (shape : Sparkle.Compiler.Elab.MachineShape) (dsn : Design) (body : List Stmt) (lsrc : List (Nat → Nat)) (nL : Nat)
    (bsI : List (Name × MixedGateBinder)) (kD : Nat) (extB : Nat → Signal D Bool)
    (ext : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (bsC : Name → List (Name × MixedGateBinder))
    (outsC : Name → List OutField) (S : Name → (Nat → List Nat) → List (Nat → Nat))
    (PC : Name → Module → Prop) (k : Nat) (c : Name) : Prop :=
  (shape.instOrigins.getD k .ord).child? = none ∧
  ∃ args : List Nat, (shape.insts.map (·.2.1))[k]? = some args ∧
    (∀ mc : Module, PC c mc →
      CombChildRunN children dsn n mc (bsC c) (outsC c) (S c) ∧ (argPorts mc).length = args.length) ∧
    (∀ (q : Nat) (hq : q < args.length), args[q] < nL ∧ ∃ g, lsrc[args[q]]? = some g) ∧
    (∀ τ, Tools.ShippingMachineChild.InRange (valsOf lsrc args τ) ((bsC c).filter fun b => b.2 != .domain)) ∧
    ∃ (k' : Nat) (o : OutField) (f : Nat → Nat), (outsC c)[k']? = some o ∧
      o.name = shape.instFields.getD k "" ∧ (S c (valsOf lsrc args))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => (extB p).val τ) (fun p n => (ext p n).val τ)
        (kD + k) ((bsI[k]?.map (·.2)).getD .domain) = f τ
```
**A6 `calls_hchildRNC`** — verbatim copy of `calls_hchildRN` (TNR:46-91); rule: ONLY `hcalls` (:62-64) changes to
```lean
    (hcalls : ∀ k c, (shape.insts.map (·.1))[k]? = some c →
      MemFacts shape lsrc nL bsI kD ext k c ∨
      (SeqFactsRN children n shape dsn body lsrc nL bsI kD extB ext bsC outsC S (seqPC PC) k c ∧
       CombFactsRN children n shape dsn body lsrc nL bsI kD extB ext bsC outsC S (combPC PC) k c))
```
`hsv` (still `→ PC c mc`), `hreset`, the `Pw` premises incl. `hrstP`/`hclkP`, and the conclusion are unchanged (it must
fit `machine_linkedTG_of`'s callback, LinkedTG:84-110). Proof plan: TNR:92-146 (memory branch, `memOne`) verbatim; then
`memNot` as TG:345-353; for the ordinary entry `e0`, AFTER `intro … mc …`: `by_cases hclk : "clk" ∈ mc.inputs.map (·.name)`.
`pos`: `hsv … : PC c0 mc`, `⟨PC, hclk⟩ : seqPC PC c0 mc`, `seq_inst_runN` as TNR:147-191; every other entry `e` of the same
instance uses its own `.1` conjunct with the SAME `hclk`. `neg`: `hrun.2.2.1`-style `"rst" ∉` from `CombChildRunN`,
`comb_inst_runN` with each entry's `.2` conjunct and `⟨PC, hclk⟩ : combPC PC c mc`. One instance = one `mc`, so entries
cannot disagree on the branch.
**A7 compatibility (old premise ⇒ new premise; embedding check)**
```lean
theorem hcallsC_of_seq {…same binders as SeqFactsRN…} (PC : Name → Module → Prop) (k : Nat) (c : Name) :
    MemFacts shape lsrc nL bsI kD ext k c ∨ SeqFactsRN children n shape dsn body lsrc nL bsI kD extB ext bsC outsC S PC k c →
    MemFacts shape lsrc nL bsI kD ext k c ∨
      (SeqFactsRN children n shape dsn body lsrc nL bsI kD extB ext bsC outsC S (seqPC PC) k c ∧
       CombFactsRN children n shape dsn body lsrc nL bsI kD extB ext bsC outsC S (combPC PC) k c)
```
(Seq part: `seqPC PC ⊆ PC`; comb part: `SeqChildRunN`'s `"clk" ∈` against `combPC`'s `∉`, ex falso.) Plus
`calls_hchildRN_viaC`: the accepted `calls_hchildRN` statement restated VERBATIM, proved by A6 ∘ A7 (shows A6 is no
stronger than the accepted consumer on sequential-only data).

## 4. Stage B — served consumer, `ComposedNW`, the parent's `ChildShips` (new file `Tools/ShippingGen2GroupServed.lean`)
Ambient: `import Tools.ShippingGen2GroupComb`, `import Tools.ShippingGen2Connect`; `namespace Tools.ShippingGen2`; `open`s of
Connect.lean:14-34 verbatim; `variable {ι dom mref cref}` as Connect:36-37.

**B1 `ordFactsRN_of_callDec`** — copy of `seqFactsRN_of_callDec` (Connect:120-147); rule: `hseq` DELETED; `PC` replaced by
`seqPC (ServedPC (ShipsAt L P n) dsn)`; conclusion conjoined with the `CombFactsRN … (combPC …)` copy.
```lean
theorem ordFactsRN_of_callDec {L : Laws mref cref} {P : Pkgs ι dom} {p q : Pkg ι dom} {k n : Nat} {c : Name}
    (dsn : Design) (body : List Stmt) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (hG : p.d.shape.instFields ≠ []) (hP : P c = some q) (hdec : CallDec p q k) :
    Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN (childMap dsn.modules) n p.d.shape dsn body
      (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extBS i bools bits) (p.extS i bools bits)
      (pkgBsC P) (pkgOutsC P) (pkgS P i) (seqPC (ServedPC (ShipsAt L P n) dsn)) k c ∧
    CombFactsRN (childMap dsn.modules) n p.d.shape dsn body
      (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extBS i bools bits) (p.extS i bools bits)
      (pkgBsC P) (pkgOutsC P) (pkgS P i) (combPC (ServedPC (ShipsAt L P n) dsn)) k c
```
Seq half: Connect:129-147 with `hseq mc hmc` replaced by `hmc.2`; comb half: same with `combChildRunN_of_noClk hmc.2`
in place of `childRunN_iff_seq`; the argPorts length is conjunct `.2.2.2.2.2.1` in both.
**B2 `groupHcalls_of_dec`** — new; its premise is `StepStmt`'s (Defs:309-310) VERBATIM.
```lean
theorem groupHcalls_of_dec {L : Laws mref cref} {P : Pkgs ι dom} {p : Pkg ι dom} (n : Nat) (dsn : Design)
    (body : List Stmt) (hG : p.d.shape.instFields ≠ [])
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) :
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k c,
      (p.d.shape.insts.map (·.1))[k]? = some c →
      MemFacts p.d.shape (p.lsrc i bools bits) p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extS i bools bits) k c ∨
      (Tools.ShippingMachineCallsLinkedTNR.SeqFactsRN (childMap dsn.modules) n p.d.shape dsn body (p.lsrc i bools bits)
          p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extBS i bools bits) (p.extS i bools bits)
          (pkgBsC P) (pkgOutsC P) (pkgS P i) (seqPC (ServedPC (ShipsAt L P n) dsn)) k c ∧
       CombFactsRN (childMap dsn.modules) n p.d.shape dsn body (p.lsrc i bools bits)
          p.d.ls.length (p.d.bsIn.drop p.kD) p.kD (p.extBS i bools bits) (p.extS i bools bits)
          (pkgBsC P) (pkgOutsC P) (pkgS P i) (combPC (ServedPC (ShipsAt L P n) dsn)) k c)
```
(`MemDec` = `MemFacts` by `memFacts_of_memDec`, Connect:93; ordinary entries by B1.)
**B3 `machine_linkedT_callsServedC`** — verbatim copy of `machine_linkedT_callsServed` (Consumer:30-105, in namespace
`Tools.ShippingGen2Consumer` reopened with Consumer:12-28 `open`s); rule: `hcalls` (:55-60) becomes the A6 form at
`PC := ServedPC Q dsn`; `calls_hchildRN` (:93) → `calls_hchildRNC`; `hsv` discharge (:96-104) verbatim. Conclusion unchanged
(the `ComposedNW` body).
**B4 `group_composedNW`**
```lean
theorem group_composedNW (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {raw : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hfe : p.d.shape.instFields ≠ [])
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc) :
    Tools.ShippingMachineDepthRun.ComposedNW n p.decl p.d p.kD raw D dom p.src p.extS p.extBS
```
(`MemParentDataOk` rows only — they say nothing about memories, S4 §3; `data_h*` MemData:37-66; `hI` from
`bsIn_drop_nodomain`, QuadComposed:89; B3 at `Q := ShipsAt L P n`, `bsC/outsC/S := pkgBsC P/pkgOutsC P/pkgS P`, B2.)
**B5 `group_childShips`** — `memParent_childShips` (MemShips:39-84) with `hmo`/`hmd` replaced by `hdec`, `h`, and
`pkg_memComposedNW` by B4.
```lean
theorem group_childShips (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hext : ExtInS p)
    (hins : p.d.shape.insts ≠ []) (hfe : p.d.shape.instFields ≠ []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      MemDec p k (p.d.shape.insts[k]).1 ∨ ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (n : Nat)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsAt L P n) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc) :
    ChildShips p (n + 1) b D
```
(`Or.inl` of C6, as MemShips:83-84; `acyc` from `closeInstsG_acyclic`, ChildServe:223, via `machineRanA_of_runJQC`,
RanABridge:38. The parent has slots, so its own branch is sequential; slotless group parents are S5.)

**Residues of stages A/B (premises, not supplied):** `h` over `ServedP (ShipsAt L P n)` = G-SERVED (`ServedShipsStmt`,
Defs:251) + G-LIFT (`ShipsRes` → `ShipsAt n`); data rows `MemParentDataOk p`, `ExtInS p` (DataOk, as M2-a/S4); case
`hins`/`hfe`/`hsl` (this unit's scope, not an FG restriction).

## 5. Stage C — connection to `StepStmt`/T1 (checks only; no `StepStmt` claim)
- **C-1 premise match (Tests).** An `example` with exactly `StepStmt`'s binders (Defs:301-313) plus the residues listed
  above derives `ChildShips p (n + 1) b D` by B5; its `hdec` is `StepStmt`'s premise passed unchanged (no case
  restriction: group parents consume `MemDec` natively, unlike S4-MEM).
- **Not in S3:** the `TopShips` half for group parents with comb kids — consumer 1 needs `RunFacts` (`kidP`/`kidW`/
  `outsIn` for comb kids, cf. MemTop:69-80) and a `KSBoundedIn` invariant (cf. `memInvN`, MemTop:85-87): G-BD/G-RUNFACTS
  "mixed", assigned to the StepStmt-route freeze (STEP_IFACE_FREEZE §5 item 5). `∃ n` with G-LIFT likewise.
- **T1:** nothing; `hseq` appears in no S3 statement, so nothing reaches `T1Hyp`/FG.

## 6. Controls
- **P1 positive (pure, required).** A toy comb module `mcT` (inputs `[a]`, outputs `[o]`, body `[assign o := ref a]`):
  hand proof of `CombChildRunN … 0 mcT [a-binder] [o] (fun v => [fun j => …])` (and at every `n` via `RunOn_instFree`),
  then `comb_inst_runN` on a concrete `connsG mcT ["wa"] [(0,"o")] ["wo"]`: a concrete `cenvs` and the output value.
  If the toy run proof does not close within budget, report; do NOT replace it by a vacuous instance.
- **P2 positive (real declaration, probe first).** New test fixture: a `circuit do` parent with a register that calls a
  slotless machine child with a Bool or structure result (or `pickByteH` plus a memory read), so that `instFields ≠ []`.
  First a computational route probe (route 3 taken, `closeInstsG`, child module has no clk/rst). If the compiler refuses
  or falls back, report it as a coverage finding (no positive real instance), not as an S3 failure.
- **N1 negative.** `¬ CombChildRunN … mc …` for a module with a `"clk"` input; `seqPC PC c mc → ¬ combPC PC c mc`.
- **N2 compat.** `calls_hchildRN_viaC` (A7) type-checks against the accepted text.
- **V1 vacuity.** `MemParentDataOk` decided on an existing group parent package (as MemParentInstance); `hdec`'s
  ordinary disjunct exercised by CallDecInstance's `CallDec`.

## 7. AUDIT clause (checked on the built proofs, stated in the file headers)
1. B3/B4: `wired`, `hx`, `trace` from ONE `obtain` of the single `MachineTraceLBX`; same `ids`/`cache`.
2. B2/B4: `hcalls` built at the `intro`'d `i bools bits`; no `Nonempty ι`, no chosen `i`.
3. A6: the `by_cases` on `"clk" ∈ mc.inputs.map (·.name)` is AFTER `intro … mc …` (the instance's module). No new
   declaration has a binder of type `∀ mc, ServedPC … c mc → "clk" ∈ …` or its negation; `seqFactsRN_of_callDec` is not
   referenced by the new files (grep + binder listing in the check file).
4. `#print axioms` of every new root: standard axioms or a subset.
5. Expected types: a MetaM check compares each copied constant's type with its source at 649a6bf5 after the stated rule
   (constant replacement `SeqChildRunN ↦ CombChildRunN`, `SeqFactsRN ↦ …`, deleted binders listed), as PMem4Check did;
   `git diff --stat 649a6bf5 -- '*.lean'` lists only the new files (and an `AllTests` line, after the joint-import probe).

## 8. Size and build plan
- Stage A ≈ 450 lines (A3 ≈ 120, A6 ≈ 230, rest ≈ 100); stage B ≈ 250; Tests/Gen2/S3GroupCheck.lean ≈ 200 (P2 probe
  separate, ≈ 60). Total ≈ 900.
- Normal issue-linked focused incremental builds, serial: `kjob run --issue sparkle-gen2-step … -- kjob lake build
  Tools.ShippingGen2GroupComb`, then `Tools.ShippingGen2GroupServed`, then `Tests.Gen2.S3GroupCheck` (job names
  `g2s3a-<sha>`, `g2s3b-<sha>`, `g2s3c-<sha>`). New targets: expect a cold-ish first build.

## 9. Decision items (for review; no STOP found)
- **D1 per-call premise form.** (a, recommended) `MemFacts ∨ (SeqFactsRN (seqPC PC) ∧ CombFactsRN (combPC PC))`, branch per
  instance in the consumer; (b) one `ChildFactsRN` with `ChildRunN` in place of `SeqChildRunN`, split inside the consumer
  (same strength, departs from the frozen name `CombFactsRN`); (c) the literal 3-way disjunction — rejected (§2.4: needs a
  universal `hseq`).
- **D2 split key.** `"clk" ∈ mc.inputs.map (·.name)` (what C2 and `combChildRunN_of_noClk` use) instead of `isSeqChild mc`;
  A4 proves they agree on every module of either branch.
- **D3 `comb_inst_runN` drops `hrstP`/`hclkP`** (more general than "one predicate replaced"; the callers still receive them).
- **D4 scope.** `ChildShips` only for group parents with slots; slotless group parents → S5; `TopShips` → StepStmt-route.
- **D5 height.** `Q := ShipsAt L P n` (G-LIFT residue), not `ShipsRes`.

## 10. Not claimed / open
- Nothing here is built or proved. No `TopShips`, no `StepStmt`, no M2 claim.
- Open: G-SERVED, G-LIFT, `hW`/width and G-BD/G-RUNFACTS for comb kids (TopShips half), coverage (P2 may find no real
  group parent with a comb child), S5 (slotless parents; producer of `CombChildRunN` for kids with instances), StepStmt.
- The final-guarantee preservation over A-COMB stays open until S3, S4 and S5 are all done.
