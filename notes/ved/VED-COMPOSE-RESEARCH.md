# VED-COMPOSE-RESEARCH: published decomposition methods vs. `step_local` / `oracleIE` / open parent / returned IR

> **Development record, not user documentation; not kept current.** The current description is [docs/VED.md](../../docs/VED.md).

> Historical design record. Describes branch `ved/compose-research` (base `bbd88dd0`), merged with PR #167; it is not kept in step with current `main` (file names, line numbers and option defaults may have moved). Index: [notes/README.md](../README.md); current description: [docs/VED.md](../../docs/VED.md).

Issue `sparkle-ved-compose-research`, branch `ved/compose-research` (base bbd88dd0).  New files only:
`Tools/VedComposeResearchCut.lean` (prototype + toy + controls), this note.  Single runs are "observed".  Machine:
`kjob lake env lean`, guard 12582912 kB.  Nothing here is a real-IP result; no R193 run.

## 0. Verdict in six lines

1. Both published methods reduce the recombination to ONE generic theorem plus ONE per-design check.  Sparkle already has the
   generic theorem for the instance cut (`fold_oracle`, `outputsOnHS_of_stepRK`, `step_local`) and the per-design ordering check
   (`WOH`/`OrderOkHS`, now `OrderOkFast`).  What it lacks is not the cut: it is a kernel statement that the RETURNED statement list,
   read from the cut leaves, computes the cone that the open parent's deep run was proved about.  ACL2 never needs that statement
   because (my reading of the sources, not a quoted claim) the object that is simulated and the object that is proved about are the same `svex-alist`; Kami never needs it
   because (inference from the paper, an analogy) widths are in the Coq types and inlining is a verified function (Thm 5.5).
2. That statement is small to *state* and to PROVE for the inlining and bundle-slice parts (`cone_connect`, `cone_connect_bn`,
   type-checked and PROVED, prototype below; the remaining pieces are the slot renaming with its width transfer and the mechanical link to the deep literals; `cone_connect_bn`'s
   range premise is restricted to the leaves actually read, see §4(a)), but it exposes
   type/semantics mismatches that the 600-1000-line estimate did not list: (M1) inlining is NOT sound in the IR semantics
   unless the assignments are width-consistent (`widthOf` reads the syntax); (M2) bundle slices (`slice (concat ..)`) remain
   after inlining on the real synthesiser output; (M3) the cone literal's slot names differ from the returned module's names;
   (M4) string lookups cost ~0.5 ms per compare in the kernel, so the lookup table needs the byte-key tree of `VedComposeOrder`.
3. Observed on the REAL returned module of the registered families: width consistency holds for all 9 (only the output port
   `out` is "inconsistent", because a port is not a declared wire); on `multiTwo.ved_mod` the inlined, bundle-normalised register
   inputs equal the deep route's cone literals (`_deep_fidelity_r0/r1`) under a slot renaming, by a closed `rfl` (literal typed
   by hand from the printed theorem type: not machine-linked yet).
4. The stage it can shorten is the parent `hstep` (per-cone closers) only.  The R193 table says the run does not reach `hstep`;
   74-76 % of the time is before the parent proof (child 231 s, deep run 442 s).  HYPOTHESIS (not established): the first unmet
   stage is the closed shape facts (>= 185 s unfinished; which of the four facts is slow, and whether String compares are the
   cause, was not measured).  If that hypothesis holds the cone check is not the next thing for R193; it would come after the
   closed facts are cut.
5. Recommendation: **adopt** (b) with the keyed closed facts as the next R193 unit (other worker's files); **hold** (a) the
   cone check, with an explicit next unit (below) whose first acceptance is a machine-linked match on `multiTwo`/`multiShared`;
   **do not pursue** the cone-of-influence/partition idea (c) for instances without changing the current `fold_oracle` (it needs
   every instance output, so it cannot prune instance proofs as is); register-side COI stays on HOLD (not rejected).
6. External solver success is not used anywhere; EQY is background from memory only (section 5, route c).

## 1. Sources: statements, hypotheses, generic vs per design, trust boundary

### 1.1 ACL2 SV (github.com/acl2/acl2 books/centaur/sv; doc text in `research-src/acl2-sv/`)

* The methodology (svtv-generalize.lisp:2614 `svex-decomposition-methodology`).  Override run: a theorem about the design with
  internal signals replaced by free values (`multiplier-pp-sum-correct-override`, :2638).  Generalised form: the inputs
  become a free `input-env` with hypotheses, and the override value becomes the OBSERVED value of the same signal in the same
  run (`multiplier-pp-sum-correct-gen`, :2671: `partial-products-value (lookup 'partial-product-signal run)` of
  `(run-design (multiplier) :inputs input-env)`).  Two such theorems about the same `run` compose by the shared observation.
  The bridge is the transparency property (:2740-2765): overriding a signal with the value it has anyway changes no signal.
* Transparency, formally (override-transparency.lisp):
  `svex-overridekey-transparent-p x overridekeys subst` (:875) `:= ∀ impl-env spec-env, overridekeys-envs-agree overridekeys
  impl-env spec-env (svex-alist-eval subst spec-env) → svex-eval x impl-env = svex-eval x spec-env`; same for lists (:954) and
  alists (:1036).  `overridekeys-envs-agree` (:689; the four clauses are in the doc at :1314): non-override variables agree;
  every bit overridden in the spec env is overridden in the impl env, to the same value; a bit overridden only in the impl env is
  overridden to the VALUE THE SUBSTITUTION `subst` COMPUTES in the spec env.  That last clause is the correlation of cut points.
* Lifting to the FSM: `fsm-overridekey-transparent-p x keys` (used svtv-to-fsm.lisp:1836, 1867, 1914, 1931) is transparency of
  `values` and `nextstate`; it is preserved by the cycle construction (`fsm-to-cycle`, svtv-to-fsm.lisp:1994, with side
  conditions `svarlist-override-p` on nextstate keys and unique i/o phases) and splits by key sets
  (`fsm-overridekey-transparent-p-by-decomp`, fsm-override-smart-check.lisp:476).
* The check (fsm-override-smart-check.lisp): `fsm-override-syntax-check x keys` (:73) returns the keys whose override muxes are
  NOT syntactically faithful; `fsm-override-smart-check` (:495) runs it, and for the bad keys falls back to
  `fsm-override-semantic-check` (:398, equivalence over environments; FGL/SAT per the doc); soundness
  `fsm-override-smart-check-implies-on-env` (:524).  The doc (svtv-generalize.lisp:2793-2806): overrides are muxes
  `(if override-condition override-value original-signal-value)`; the syntactic check finds every mux and ensures the original value
  in each is the final value of the overridden signal.  Why syntactic: faithfulness then follows by structural induction on the
  composed expressions, without enumerating environments; it is incomplete exactly when there are (apparent) combinational loops
  (:2806-2812), where it falls back to the semantic check or to the second method.
* Second method (:2784-2790, def-svtv-ideal): prove transparency of an idealised fixpoint version; the composed theorem is then
  about the IDEAL, not the actual SVTV.  For Sparkle this is excluded by contract (the artifact is the returned IR).
* Generic vs per design: transparency lemmas, cycle preservation and `def-svtv-generalized-thm` (:3005) are proved once; per
  design: the syntactic/semantic check on the FSM and the user's override lemma.
* Trust boundary: all theorems are ACL2 theorems; the semantic fallback depends on FGL/SAT (from memory: via ACL2's
  clause-processor mechanism; not in the downloaded sources).  The syntactic check is a verified-in-logic Lisp function.

### 1.2 Kami (ICFP'17, `research-src/KamiICFP17.txt`)

* Def 5.3 (:894) `m ⊑_p m' := ∀ n α. m ⇓ ⟨n,α⟩ → ∃ n'. m' ⇓ ⟨n', map p̂ α⟩`, with `p` a label map that treats called and executed
  method elements symmetrically.
* Thm 5.4 modular refinement (:898-903), the substitution theorem: (1) if no method called in `m1` is defined in `m2` and vice
  versa (same for `m1'`, `m2'`): `m1 ⊑_p m1' ∧ m2 ⊑_p m2' → m1+m2 ⊑_p m1'+m2'`; (2) if `p` changes label elements only for methods
  called in `m1` and defined in `m2` or vice versa: the same with no label modification (those labels are erased by the
  composition).  Side conditions of `+`/`⊎` (:417-419, :549-562): disjoint register maps and disjoint method names, and a method
  is called at most once per transition (method calls are wires, one wire set per method).
* Thm 5.5 inlining (:926): `m ⊑ |m|`, a Gallina function proved correct once; for parametrised modules it is interleaved with
  rewrite rules (:957-962).  Thm 5.6 (:981): refinement from an initial-state relation and a one-substep simulation under `R`,
  when `m` defines no methods or every method/rule writes a common register.
* Generic vs per design: 5.1-5.6 once; per design: `m ⊑ m'` for the replaced module (the child) and `R` plus the rule/method
  correspondence for the parent.  Trust boundary: the Coq kernel for everything (inlining is a verified function, no checker
  outside).
* Reading for Sparkle (synchronous, per-cycle registers): instance wires = method labels (a child output is called once, written
  once: `WOH`); Kami's `⊎` disjointness of registers = the hierarchical state `HSt` keyed `(path, name)`, instance-specific by
  construction, N instances of one module share one child theorem and N state slices; Kami has no reset or time (atomic rules),
  Sparkle has the synchronous `rst` of `regNexts` and the contract `InputsOk` (reset = 0); Kami widths are `Bit n` types, so
  "widths" are free there and are exactly what Sparkle must re-establish (M1); Kami's existential on the spec trace is
  replaced here by an equation with a deterministic declaration.  SEPARATION: the correspondence above is an ANALOGY (my reading
  of the paper); nothing in Lean here instantiates Kami's Thm 5.4.  What is PROVED is Sparkle's own `fold_oracle` /
  `outputsOnHS_of_stepRK` / `step_local` (oracle = the child's output), of which Thm 5.4(2) is only the conceptual counterpart.

### 1.3 Sparkle, as it stands (all at bbd88dd0)

* `U2HRStmt` (Tools/VedU2HierReg.lean:38) = `CorrStmt ∧ ShapeCore ∧ clkRst ∧ HierShapeS ∧ WidthStmt ∧ OrderHS ∧ (∀ child, OrderStmt)
  ∧ (∃ arr, AdmArr) ∧ OutputsStmtHS c m d f`.
* `outputsOnHS_of_stepRK` (Tools/VedU2HierState.lean:27): hypotheses `hkid` (the oracle `Ow ins y t` equals the closed run's value of
  every instance output at every cycle where `R` holds: the OBSERVATION, as in ACL2's `lookup`) and `hstep` (from any `p` with
  `R ins t p`, the OPEN fold of the arrangement `b0` with `oracleIE` succeeds, outputs equal `srcOf c f`, `R` holds of the updated
  slice) and `h0`.  Generic, proved once.
* Transparency generic part: `fold_oracle` (Tools/VedU2HierStmt.lean:105) with `oracleIE` (:91), `oracleIE_laws` (:96): if the closed
  fold gives `E` and `E y = O y` on every instance output, the open fold with `O` gives the same `E`.  Precondition: `WOH d b`
  (Tools/VedU1HierSem.lean:235), established per design by `OrderOkHS` (VedU2HierOrder.lean:36) / `OrderOkFast` (VedComposeOrder).
* `step_local` (Tools/VedComposeStep.lean:40): takes the fold apart once; the remaining obligation is `hloc` for an abstract `E`
  with `hasg` (every assignment holds), `hEin`, `hEreg`, `hEorc`.  Nothing is assumed.
* Open parent: `#verify_elab_deep` gives a `Cdo Γr Γi wOut` (Tools/DeepElab.lean:328: `inits`, `next : ∀ i, CExpr (Γr ++ Γi) _`,
  `out`) and per register `_deep_fidelity_r i : CExpr.compile nm (deep.next i) = <literal IR Expr>` (compile: DeepElab.lean:103);
  `Cdo.elab_general` (:587) the Signal↔IR statement.  The literal cones come from a SEPARATE meta re-synthesis of the open parent
  (cut1 report, reviewer-confirmed).  The knot (`loop_knot`, Tools/VedU2HierMultiLoop.lean:45) ties the declaration's loop to the
  open loop.
* Returned IR: a `Module` whose body has assigns, `inst` and `register` statements, bundle wires (`concat` of register outputs) and
  slices.

## 2. Mapping table: published notion → Sparkle

(Analogy table.  "EXISTS" means the Sparkle theorem/definition exists and is proved on its own; it does NOT mean it is an instance of
the published theorem named in the first column.)

| published notion | Sparkle counterpart | Lean type it needs / status |
|---|---|---|
| override/cut variable `s_v` (+ test `s_t`, always overridden here) | oracle wire `Ow ins y t` for an instance output `y` | `Ow : (Nat → String → Nat) → String → Nat → Nat` in `outputsOnHS_of_stepRK` (VedU2HierState.lean:27); cut set `instOutsOf d b0` (VedU2HierStmt.lean:142). EXISTS |
| other cut points of a cone: inputs, registers | `inNames m`, `regOuts b0` | `cutNames d m b0 := inNames m ++ regOuts b0 ++ instOutsOf d b0` (new, prototype, :`cutNames`) |
| transparency (override with the value it has anyway) | `fold_oracle` | VedU2HierStmt.lean:105. EXISTS, generic |
| env-agreement clause 4 (override = value `subst` computes) | `hkid` (`E y = Ow ins y t`) | in `outputsOnHS_of_stepRK`; in `step_local` as `hEorc`. EXISTS |
| syntactic check that makes overriding sound | `WOH d b0` via `OrderOkHS`/`OrderOkFast` | EXISTS.  Differs: there are no override muxes to match, the cut is the free semantics of an instance (`oracleIE`); the check is that instance output wires are written once, before any read |
| generalised theorem (override → observation) | `outputsOnHS_of_stepRK` | EXISTS |
| composed per-cycle update functions (`fsm->values`, `nextstate`) | none on the returned side; `Cdo.next` cones (CExpr) on the open-parent side | MISSING: a kernel function from `b0` to cone literals: `inl` (new, prototype) `inl : (String → Option Expr) → Nat → Expr → Expr`, `inl_sound` (proved) |
| spec/impl env consistency | `leafEnv m b0 ins t p Ow` | new def; `cone_connect` (proved) |
| Kami `m1 ⊑ m1'` for the replaced module | child theorem `kid_inst` (Tools/VedU2HierKid.lean) | EXISTS (reused) |
| Kami Thm 5.4 (substitution) | `outputsOnHS_of_stepRK` + `fold_oracle` | EXISTS; side conditions = `WOH`, `hsupp`, state keyed `(path, name)` |
| Kami Thm 5.5 inlining `m ⊑ |m|` | `inl_sound` | MISSING before this unit.  The current proof inlines implicitly by `simp` over 340 statements |
| Kami Thm 5.6 (init + one-step simulation under `R`) | `h0`, `hstep` of `outputsOnHS_of_stepRK` | EXISTS |
| Kami `Bit n` typing (widths free) | `declWidth m`, `widthOf we`, `WidthStmt` | PARTIAL: widths are a function, `evalExpr` reads them from syntax; the side condition `WOKb` (new) is needed to inline (M1) |
| Kami `⊎` register disjointness | `HSt` keyed `(path, name)`, `regOuts` Nodup (`hnd`) | EXISTS |

## 3. Type/semantics mismatches that stop a naive connection

* **M1 (new finding).**  `evalExpr` depends on `widthOf we`, which is computed from the SYNTAX: `widthOf (ref x) = we x` but
  `widthOf (rhs)` for the wire's definition may differ; `evalOp` uses `widthOf (.op ..)`, the concatenation reads each element's
  `widthOf`, `not` and the signed comparisons read their operands'.  So replacing `ref x` by its definition can change the value
  even if every assignment holds.  Controls (Toy `ctl_width_*`): wire `b` declared 4 bits with a 2-bit constant rhs and
  `c = {a, b}` declared 8 bits: both assignments hold in an environment (`b = 3`, `c = 83`) and `evalExpr (ref c) = some 83`, but
  `evalExpr (inl .. (ref c)) = some 23`.  `inl_sound` therefore carries `widthOf we rhs = we lhs` for every inlined assignment
  (`WOKb`, decidable).  Cut1's O1 ("cheap, 100-200 lines") missed this.
* **M2.**  After inlining, bundle reads remain: observed on `multiTwo.ved_mod`: register `_tmp_a_4` input =
  `add [slice (concat [ref _tmp_a_4, ref _tmp_a_15]) 7 4, const 1 4]`, register `_tmp_a_15` input contains
  `slice (slice (concat ..) 3 0) 3 0`.  The deep literal has `ref _tmp_a_10`.  Resolving needs `slice (concat refs) = ref` for an
  exactly aligned slice (existing name-level lemmas: `slice_concat_val`, `bundle_slice_fact`, Tools/VedU2HierMultiBundle.lean:140,
  159) and range facts `E x < 2^we x` on the leaves (register invariant, `concat_range` :177).
* **M3.**  Slot names: the cone literal uses the re-synthesis' names (`_tmp_a_10`, `_gen_ved_o0`), the returned module others
  (`_tmp_a_15`, `_tmp_op_b_9`).  Either a renaming map (`ren`, which the entry already computes for the register-slot map and the
  instance↔call pairing) or the entry passes the returned names as `nm` to `CExpr.compile`.
* **M4.**  Cost: the lookup `asgOf b l` is a `String` scan.  Observed (scratch/runs/4100, 4200, chain of N assigns, one cone of depth N,
  baseline file 13.3-13.7 s): N=100 +1.7 s, N=200 +11 s (single runs).  R193: 349 statements and next-arms syntax of 107,095 characters
  (compose5, reify stage).  A character count is NOT a cone node count; the number of cone nodes and lookups at R193 was not measured.
  Inference: lookups at that size are likely too many for the `asgOf` scan, so the `nameKey` byte-key tree (`VedComposeOrder`) is the candidate.
* **M5.**  Cones carry no reset/init (`Cdo` has `inits`, no `rst`); `regNexts` has `if E rst ≠ 0 then init`.  `hloc` must still
  discharge the reset branch from `InputsOk` (reset = 0).  Unchanged by the cone check.
* **M6.**  Instance ARGUMENT nets (`hkid`, O4) are not cones of the open parent: the deep run reifies registers and the port, not the
  call arguments.  The cone check does not cover them; the present per-instance blocks (`hAlx`) stay.

## 4. Routes

### (a) Cut the RETURNED IR directly, keep the correlation (ACL2 style)

* (i) Propositions (all type-checked; the first two PROVED in `Tools/VedComposeResearchCut.lean`):
  `theorem inl_sound (we E A) (hA : ∀ l r, A l = some r → evalExpr we E r = some (E l) ∧ widthOf we r = we l) : ∀ n e, evalExpr we E (inl A n e) = evalExpr we E e ∧ widthOf we (inl A n e) = widthOf we e`
  `theorem cone_connect … (hW : WOKb (declWidth m) m b0 = true) … (hasg hEin hEreg hEorc : the step_local facts) (hc : inl (Atab m b0) n e = c) (hl : leafOk (cutNames d m b0) c = true) : evalExpr (declWidth m) E e = evalExpr (declWidth m) (leafEnv m b0 ins t p Ow) c`
  Reading: the value of a register's (or output's) right-hand side at the abstract environment equals the value of the cone
  literal at the LEAF valuation (cycle inputs, pre-state, oracle `Ow`), which is the valuation the deep trace evaluates its cones at;
  `hc` and `hW`, `hl` are closed facts for the kernel (`rfl`, `decide +kernel`).  With bundle slices (M2), also PROVED:
  `theorem bn_sound (we E) : ∀ n e, (∀ x ∈ refs e, E x < 2 ^ we x) → evalExpr we E (bn we n e) = evalExpr we E e ∧ widthOf we (bn we n e) = widthOf we e`
  `theorem cone_connect_bn … (hrange : ∀ x ∈ refs (inl (Atab m b0) n e), E x < 2 ^ declWidth m x) (hc : bn (declWidth m) n2 (inl (Atab m b0) n e) = c) (hl0 : leafOk (cutNames d m b0) (inl (Atab m b0) n e) = true) : evalExpr (declWidth m) E e = evalExpr (declWidth m) (leafEnv m b0 ins t p Ow) c`
  `hrange` (register invariant, input contract, child output width) is an obligation of the per-cone step, not assumed done.
  REVIEW FIX: it is restricted to the NEEDED leaves (those the inlined expression reads).  The first version quantified over all of
  `cutNames`, which includes unread names such as `clk`; in `parB`, `declWidth clk = 0`, so `hEin` + that `hrange` would demand
  `clock < 1`, which the clock-universal `InputsOk` cannot supply.  Now PROVED and controlled: `ctl_clock_old_hrange` (the old form is
  refuted at `envC`, clock = 1) and `parB_connect_clock1` (the connection applies at clock = 1 with `hasg`, `hEin`, `hEreg`, `hEorc`
  and the needed-leaf `hrange` all discharged, no free premise).  Remaining obstacle: supplying the needed-leaf range from the register
  invariant / input contract / child width in a real row is still an obligation (§7).
  Still to state and prove: `ren_sound` for the slot renaming (M3) including the transfer from the returned module's width
  function to `weOfC nm widths` — see section 7 (or avoid it by passing the returned names as `nm`).
* (ii) Obligations: O1 done (plus the new width condition); O2 reduced from "general normaliser" to aligned bundle slices over
  register leaves plus `ConcatNorm` (exists, `norm2_eval`, Tools/ConcatNorm.lean:102); O3 reduced to a slot renaming and a
  width-environment transfer (`weOfC nm widths` vs `declWidth m` on leaves); O4 NOT needed for cones (stays as is); O5 (generator)
  needed: the script must call `cone_connect` per register/output instead of per-cone `simp`.
* (iii) Stage: parent `hstep` closers only.  Evidence: compose5 §5: parent proof for the n=8 toy 162 s (70 statements); R193 never
  reached `hstep`; the hstep share of the n=8 total is NOT measured (cut1 correction).  No effect on child check (231 s), deep run
  (442 s) or the closed shape facts (>= 185 s).
* (iv) Benefit: removes the per-cone `simp`/`omega` evaluation, replaces it by closed kernel evaluation; the checked fact is
  also a faithful "the returned IR is the open parent's IR with instances replaced by oracle wires" (the "Next" of
  VED-HIER-H3OPEN.md).  Cost: bundle normaliser + soundness (est. 1-2 units), generator.  Failure: on a real row the normalised
  returned cone differs from the literal after only {aligned slices, `ConcatNorm`, renaming}; or lookup at 349 statements stays
  slow with the byte-key tree.
* (v) STOP: drop (a) if, on the n=8 returned module, any register's `bn ∘ inl` differs from its `_deep_fidelity_r` literal under the
  entry's renaming after the three rules; or if the keyed `inl` for one R193-sized cone set takes > 60 s.

### (b) Local proofs connected to the existing cones (current route, `ved.compose.step`)

* (i) The connection proposition is `hloc` of `step_local` itself (Tools/VedComposeStep.lean:40, type-checks as is); nothing new
  is needed to STATE it.  The recommended addition is not a theorem but the compose5 lesson applied to the closed shape facts.
* (ii) Obligations: none of O1-O3 (the facts are proved per cone, as now); O4/O5 as now.
* (iii) Stage: the closed shape facts (`refine ⟨by decide +kernel ×4, …⟩`, >= 185 s unfinished at R193), by replacing String
  compares by byte keys exactly as `OrderOkFast` did (hOK: ~285 s for the old check is an ESTIMATE (extrapolation, not measured);
  10.6 s was measured for the new one; the ratio ~27 and difference ~275 s are therefore estimates too);
  `WidthStmt` contains `(m.wires.map (·.name)).Nodup` (Tools/VedU1Contract.lean:345), a quadratic String scan, and `declWidth`
  is a `find?` over `m.wires`.  Which of the four facts is slow was NOT measured.
* (iv) Benefit up to ~185 s+ at R193; cost small (one unit, like `OrderOkFast`); failure: the slow fact is not String-bound.
* (v) STOP: tick inside the `refine`; if the slowest fact is not a String-compare/`declWidth` scan, or after keying the four
  facts the stage still takes > 60 s, drop this and re-profile.

### (c) Partition / cone of influence (EQY-style cutpoints; BACKGROUND FROM MEMORY, no source)

* (i) Proposition (type-checks as a def): `def CoiClosed (S : List String) (reads : String → List String) : Prop := ∀ r ∈ S, ∀ x ∈ reads r, x ∈ S ∨ x ∉ regOuts b0` — an invariant `R` that mentions only registers in the fan-in of the output port.
* (ii) Obligations: needs a different `hstep`/`R` shape, and `fold_oracle` needs `hkid` for EVERY instance output (the closed fold
  computes all instances), so instances cannot be pruned without changing a shared theorem.
* (iii) Stage: deep run / parent for registers outside the fan-in of `out0`.  Whether that is many registers is unknown (the digest
  depends on almost all working registers of sha512; not measured, no R193 run).
* (iv) Benefit unknown, bounded; cost: statement change of `R`, deep-port selection exists (`sparkle.deepPorts`).  Failure: fan-in
  of `out0` ≥ 90 % of the 34 registers.
* (v) STOP: a syntactic fan-in count from the literal cones of `_deep` for R193 (needs the deep run, i.e. an R193 run) showing > 90 %;
  until then HOLD, do not spend a unit.

## 5. Prototype (route a, cone level) — `Tools/VedComposeResearchCut.lean`

* Contents (≈ 520 lines incl. toys): `inl`, `refs`, `width_op_map`, `width_concat_map`, `evalOp_map`, `evalList_map`,
  `foldl_zip_map`, `go_map`, `inl_sound`, `eval_congr`/`evalList_congr`, `outsOf`, `Atab`, `WOKb`/`WOKb_sound`, `cutNames`,
  `leafOk`/`leafOk_sound`, `mem_instOutsOf`, `leafEnv`, `cone_connect`; `alignedIdx`, `refNames`, `bnS`, `bn`, `alignedIdx_spec`,
  `refNames_eq`, `bnS_sound`, `refs_bnS`, `refs_bn`, `bn_sound`, `cone_connect_bn`; then the Toys (namespace
  `Tools.VedComposeResearch.Toy`): toy 1 `par`: a register and TWO instances of the same child `kid` (the second reads the first's
  output), accepted (`par_widths`, `par_cone`, `par_out_cone`, `par_leaves`, `par_connect`); toy 2 `parB`: two registers read through
  a bundle `concat` and `slice`/`slice∘slice` (the shape of the real output), one instance, accepted (`parB_widths`, `parB_c0`,
  `parB_c1`, `parB_l0`, `parB_l1`, `parB_connect0` (needed-leaf `hrange`)), and the clock = 1 control (`envC`, `envC_hasg`, `envC_hrange`,
  `ctl_clock_old_hrange`, `parB_connect_clock1`).
* Same artifact / contract: `cone_connect` takes exactly the hypotheses `step_local` hands to `hloc` (`hasg hEin hEreg hEorc`)
  and its conclusion is the per-cone value fact `hloc` needs; no statement (`U2HRStmt`, `U1Stmt`, `MemStmt`) and no existing file is
  changed; no new hypothesis in any final statement.  It is NOT yet wired into an entry (that is O5).
* Axioms (observed, `#print axioms` in the file): `cone_connect`, `par_connect`: `[propext, Quot.sound]`; `ctl_swap`:
  `[propext, Classical.choice, Quot.sound]`; `cone_connect_bn`, `bn_sound`, `parB_connect0`: `[propext, Quot.sound]`; `inl_sound`,
  `ctl_misaligned`, `ctl_range`: `[propext]` (run 69); after the review fix (unit 2, run 11): `parB_connect_clock1`, `envC_hasg`:
  `[propext, Quot.sound]`, `ctl_clock_old_hrange`: `[propext]`.  No `sorry`, no `native_decide`, no new axiom (grep on the file: none).
* Refused controls (kernel-evaluated, run 57): (1) mis-wiring: `inl … ≠ coneSwap` (the two oracle wires swapped, instance i0 paired
  with i1's call); (2) independence faking: a cone that stops at the computed wire `w2` — the equation `inl A 2 w3 = coneFake` HOLDS
  (`ctl_fake_eq`) and `leafOk … coneFake = false` (`ctl_fake_leaf`): the transparency/leaf condition is what refuses it;
  (3) different artifact: `inl … ≠ coneOther` (a cone of another module) and `leafOk (cutNames dsgNoOut …) coneR = false` (same
  literal, a design whose child has no output `y`); (5) a misaligned slice is not resolved (`ctl_misaligned`: `bun[6:3]` stays a slice, the equation with the cone literal is refuted);
  (6) the range hypothesis is real (`ctl_range`: `slice (ref x) 3 0 ≠ ref x` when the value does not fit); (4) the width side condition is real: `ctl_width_check` (`WOKb … = false`) and
  `ctl_width_semantics` (inlining changes the value although both assignments hold).
* Timing (observed, single runs): an import-only file 11.8 s wall; the whole prototype file (proofs + both toys + controls)
  13.3-17.0 s wall over runs 57-71, i.e. ~2-5 s over the import cost, difference dominated by elaborating the proofs; the
  profiler (run 72) shows a type-checking step of ~1.1-1.3 s for the largest theorems and nothing in the closed toy facts above the
  100 ms threshold.  Generation (meta) time of a cone set is not in scope here.  The M4 scaling runs (above) are the only cost data and are bounded to N=200.
* Real-shape observations (scratch/runs/58, 64; scratch/Real.lean, Real3.lean, not committed):
  `WOKb (declWidth M) M M.body` holds (by `decide +kernel`) for all nine returned modules of `Tests.Ved.U2HierMultiCheck`
  (multiTwo, multiShared, multiKids) and `Tests.Ved.U2HierWireCheck` (wireMix, wireOrd, wireShared, wireTwo, wireRn, wireAdd) —
  with output ports excluded; with them included it is false for all nine (run 54); the offenders listed for `multiTwo` and `wireAdd` (run 55) are only the
  wire `out` (widths 4 and 8 vs declared 0).  On `multiTwo.ved_mod`, `bn (inl A 300 (register input)) = ren ρ literal` holds by closed `rfl` for both registers
  (run 64), where `bn` resolves aligned bundle slices (soundness PROVED: `bn_sound`, given range facts on the leaves) and `literal` is typed from the printed
  `_deep_fidelity_r0/r1` types (NOT machine-linked yet).

## 6. Decisions

| route | decision | reason |
|---|---|---|
| (b) local proofs + keyed closed facts | ADOPT as the next R193 unit (not this worker's files) | HYPOTHESIS: the first unmet R193 stage is the closed facts (>= 185 s unfinished; cause not established), a candidate quadratic-String cost class whose analogue (`OrderOkFast`: ~285 s estimated → 10.6 s measured) is encouraging; the cone check cannot help until that stage is passed.  Verify first by the tick in §4(b)(v) |
| (a) returned-IR cone check | HOLD, next small unit below | connection statement proved and controlled; two mismatches (M2, M3) have observed real-shape answers; shortens only `hstep`, which R193 does not reach yet |
| (c) COI partition | NOT PURSUED for instances without changing the current `fold_oracle`; registers HOLD (not rejected) | `fold_oracle` needs all instance outputs; the register fan-in is unmeasured |

## 7. Next small unit (2-3 h) and its acceptance

The next (a) prototype must state explicitly three things: (W) WIDTH TRANSPORT: the transfer from the returned module's width
function (`declWidth m`) to the width environment of the deep cone literal (`weOfC nm widths`) on the leaves; (R) NEEDED-LEAF RANGE:
the range premise `E x < 2 ^ declWidth m x` for exactly the leaves the inlined cone reads (not all cut names; the clock-universal
contract must supply it), derived from the register invariant, the input contract and the child's output width; (F) MECHANICAL
FIDELITY CONNECTION: the match between the normalised returned cone and the deep `_deep_fidelity_r` literal obtained from the
theorem type by machine, not typed by hand.

"Cone check on the real shapes": in a new file (no shared edits) (1) define the byte-key table `Atab` on top of `VedComposeOrder`'s
`nameKey`/`NTree` and prove it agrees with `Atab` above (the cone theorems then apply unchanged); (2) prove `ren_sound` (renaming of
leaves plus width transfer to `weOfC nm widths`), or have the entry pass the returned names as `nm` and skip it; (`bn_sound` is done);
(3) machine-link the literal: state, for
`Tests.Ved.U2HierMultiCheck.multiTwo` and `multiShared`, `bn (inl A n input_r) = ren ρ (literal of the type of `_deep_fidelity_r`)` with
the literal obtained from the theorem's type by `Lean.Meta`/`type_of%`, not typed by hand; (4) controls as in section 5 plus a
mis-paired renaming `ρ` (refused).  Acceptance: kernel-accepted, std3 axioms, all registers of both toys match, the three controls
refused, and a keyed-lookup microbenchmark at 349 synthetic statements with a stated synthetic cone-node count (the R193 node count is not measured) under 20 s (report ratio and absolute
difference against the `asgOf` scan).  Stop: any register of either toy not matching after the three rules.

## 8. Commits

See `git log ved/compose-research` (`Tools/VedComposeResearchCut.lean`, this note).
