# DG-ENV T2 unit U6 freeze: survey of the rows still unsupplied after U5, and the first unit (`RealChildN` is bundle-independent under `QuietStrength`, plus `QuietStrength` trans / refl-characterisation) (docs only, before any Lean)

Issue `sparkle-gen5-dg-env`. Base: `kjob/g5env-r13` 9b886655 (U5 N0-N4 approved, build env13v-9b886655 exit 0, 759 jobs, TYPE 5 / MUT 8 / AX 4), plus a2bc782c (comment/docs sync only).
Nothing here adopts a new law, adds a `Laws` / `RefLawsAOps` / `RefLawsATele` field, a TRUSTED boundary, a new premise with runtime content, or changes a shared definition; nothing narrows FG or strengthens `GenWF`.
Nothing here supplies `L′`, `QuietStrength`, `hE`, `hn`, `hN` for a real cache, `CellPrem`, `¬ DRow`, callbacks, C0 or FG. "未供給 / この調査で経路未発見" is a result of THIS survey (existing lemmas read at 9b886655), not a claim of impossibility.
The audit of the Check covers kernel types / values with the permitted projections as leaves; it does not show that a law bundle was constructed.

## 0. Rows examined (existing lemmas, full names)
| row | existing lemmas read | result |
|---|---|---|
| real-cache `hN` (every entry of `cv w₀` is `RealChildN`) | `Tools.ShippingChildCacheA.RealChildA` / `CacheInvA`, `Tools.ShippingGen5EnvCache.RealChildN`; `Start L` stores `CacheInvA L.O (cv w₀)` | 未供給 / この調査で経路未発見. `RealChildA` is a `Prop` inductive; its stored `AdmCtx` does not give `canUnfold? = none` of the entry's `mctx`, and its stored `L.O.quiet w` does not give `ReadsAt env₀ cref w`; both would have to come from premises about the runtime, none of which is introduced here |
| non-empty concrete example of `RealChildN` | `RealChildN.run` needs `ReadsAt`, `sv w = some synthesizeChild`, `RunsTo (synthesizeCombinational c) …` | 未供給 / この調査で経路未発見 (a concrete `RunsTo` witness needs an opaque `Meta`/`Core` run; U4 §1.2) |
| `L′` / `QuietStrength` real supply | `Laws.O` (13 fields), `Laws.T`; `Tools.ShippingGen5EnvQ.QuietStrength` | 未供給 / この調査で経路未発見 (building `L′` needs all 13 `O` fields and `T`; U4 §1.3) |
| `¬ DRow p` | `drow_toFramedA`, `envFrameEnd_framedA` | 未供給 / この調査で経路未発見 (U4 §1.1) |
| `CellPrem` | `ReadWorld`, `SetFrame`, `SetGet`, `ReadWorld.readKeeps` | 未供給 / この調査で経路未発見 (U4 §1.2) |
| `AdmDown` for `canUnfold? = some f` | `AdmDown`, `InertUnfold`, `admCtx_none`, `admCtx_down_of_none` | 未供給 / この調査で経路未発見. `InertUnfold L′.O.quiet f ⇒ InertUnfold L.O.quiet f` would need `f` to behave on worlds quiet for `L` but not `ReadsAt env₀`; a route would add a premise on `f`, not introduced here (U5 §0) |
| relations among the existing premises themselves (`QuietStrength` composition, `RealChildN` under a change of bundle) | `QuietStrength`, `quiet_down`, `readsAt_of_quiet`, `RealChildN`, `realChildA_up_of_N` | CLOSES from existing lemmas by name: the chosen unit (§1) |
`40 − 13 = 27` remains a constructor count only. C0 and FG are not complete and not touched.

## 1. Chosen first unit: U6 = the premises `hN` / `QuietStrength` do not depend on which of two related bundles is named
Reason: it is the only row of §0 whose statements follow from existing definitions by structural induction on `RealChildN` and unfolding `QuietStrength`, with no `Laws` field beyond `O.quiet`, no `CellPrem`, `AdmDown`, `¬ DRow`. It does not supply any premise. Its value is bookkeeping: once a real `hN` is ever supplied at `L` (or at `L′`), it is available at the other bundle, and `QuietStrength` chains (`L → L′ → L″`) at one fixed `env₀`, so later units need not re-prove these.
What it does NOT do: it does not show `hN`, `hn`, `QuietStrength` hold of anything real, and gives no non-empty example.

## 2. Frozen types. New file `Tools/ShippingGen5EnvCacheB.lean` (lean_lib `Tools.ShippingGen5EnvCacheB`), imports `Tools.ShippingGen5EnvCache`
```lean
namespace Tools.ShippingGen5EnvCacheB
open Lean
open Tools.ShippingChildInv (Res)
open Tools.ShippingGen2 (Laws)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingGen5EnvQ (QuietStrength)
open Tools.ShippingGen5EnvCache (RealChildN)
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- (B1) `QuietStrength` composes at one fixed `env₀`. -/
theorem quietStrength_trans {L L' L'' : Laws mref cref} {env₀ : Environment}
    (h1 : QuietStrength L L' env₀) (h2 : QuietStrength L' L'' env₀) : QuietStrength L L'' env₀

/-- (B2) `QuietStrength L L env₀` is exactly "every `L`-quiet world reads `env₀`". -/
theorem quietStrength_self_iff {L : Laws mref cref} {env₀ : Environment} :
    QuietStrength L L env₀ ↔ ∀ w : Void IO.RealWorld, L.O.quiet w → ReadsAt env₀ cref w

/-- (B3) a restricted entry at `L` is a restricted entry at `L′` (induction on `RealChildN`). -/
theorem realChildN_up {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {c : Name} {r : Res} (h : RealChildN L env₀ c r) : RealChildN L' env₀ c r

/-- (B4) and conversely (induction on `RealChildN`). -/
theorem realChildN_down {L L' : Laws mref cref} {env₀ : Environment} (hq : QuietStrength L L' env₀)
    {c : Name} {r : Res} (h : RealChildN L' env₀ c r) : RealChildN L env₀ c r
end Tools.ShippingGen5EnvCacheB
```
Proof plans. B1: `fun w => (h2 w).trans (and_congr_left' (h1 w) …)` or by `constructor` per direction using `h1 w`, `h2 w`. B2: `→`: `(h w).mp` with `Iff.rfl` (`L.O.quiet w` gives `L.O.quiet w ∧ ReadsAt` hence `ReadsAt`); `←`: `⟨fun hw => ⟨hw, h w hw⟩, fun hw => hw.1⟩`. B3: induction on `h`, `.run mctx cctx w w' hn rd ih synth ((hq w).mpr ⟨quiet, rd⟩) hr`. B4: induction on `h`, `.run mctx cctx w w' hn rd ih synth ((hq w).mp quiet).1 hr`.
Statements are the frozen content; if an `open` / implicit-argument shape needs adjusting when elaborating, any change is reported before review. Counting: 4 theorems = 4 Expected comparisons (TYPE 4).
Note the `RealChildN` cache field is `∀ c' r', (cv w).get? c' = some r' → RealChildN …`; its recursive call is on the same `L`/`L′`, so the induction hypothesis is used directly.

## 3. Checks (`Tests/Gen5/EnvCacheBCheck.lean`, lean_lib `Tests.Gen5.EnvCacheBCheck`), Expected written from §2 of THIS file
Same discipline as `EnvCacheCheck`: `Tests.Gen3.ExpectedType` (`checkExpected`), independent Expected, the walker `reachQ` from `Tests.Gen5.EnvFrame3Check`.
* TYPE: B1-B4 against independently written Expected propositions, one comparator (`withReducible checkExpected`). TYPE 4.
* MUTANT (well-typed single changes rejected by the same comparator; signature / defeq rejections, NOT semantic counterexamples; only mutants well-typed with the changed binder counted): M1 B1 with `h2` dropped (concluding `QuietStrength L L'' env₀` from `h1` only); M2 B1 with `env₀` of `h2` a different bound `env₁`; M3 B2 `→` direction only (`QuietStrength L L env₀ → …`); M4 B2 with `ReadsAt env₁` for a second bound `env₁`; M5 B3 without `hq`; M6 B3 concluding `RealChildN L env₁ c r` (second environment bound); M7 B4 without `hq`; M8 B4 concluding `RealChildN L' env₀ c r` (the direction of B3, well-typed, needs `hq`). Total 8, sum rule.
* CLOSURE (walker, root self judged, unknown name `throwError`, intended name and path asserted): quiet-only mode as in U5: guarded constants reached from B1-B4 are exactly `Laws.O` and `RefLawsAOps.quiet`. Forbidden everywhere: any other `RefLawsAOps` field, `Laws.T`, `RefLawsATele.*`, `T1Hyp.*`, `T1HypND.*`, recursors on those, raw projections, `GetEnvFrame` / `EnvSnapshot`.
  Controls: positive = B1-B4; negative law-bearing fixtures reaching `L.O.frame`, `L.T`, `L.T.telescope`, `T1Hyp.defines` (direct and helper counted separately); `unknown` (unresolved, throwing, including a helper whose type alone is an unknown name) and `forbidden` (flagged) kept as separate controls; self-root controls; clean controls. Counts reported as `n roots / n negatives + n unresolved + n self-root / n clean`.
* AXIOMS: standard only (`propext`, `Classical.choice`, `Quot.sound`) for every root; no `sorry`, no `native_decide`.
* `lakefile.lean`: two `lean_lib` entries; build `kjob lake build Tests.Gen5.EnvCacheBCheck` (one target, `-c 2`). Lean commit ⇒ the Issue stays `doing`; the note says "clean build は coder".

## 4. Not claimed
* `hn`, `hN` and `QuietStrength` remain hypotheses; real-cache `hN`, a non-empty concrete example, `L′`, `hE`, `CellPrem`, `¬ DRow`, callbacks, C0, FG, M5 are not supplied and not touched (未供給 / この調査で経路未発見). This is bookkeeping between existing premises; it is not progress toward supplying them and is not Issue completion.
* No new law or TRUSTED; no decision document is needed. Mutants are signature / defeq rejections, not semantic counterexamples. No edit of `Tools/ShippingGen2Defs.lean`, `T1Hyp`, `T1HypND`, `Elab*.lean`, compiler, FG or `GenWF`; only `lakefile.lean` (two `lean_lib` entries) among existing files.
