# Necessary conditions for a correspondence with the real `ST.Ref` (unit SR2i)

Status words: **PROVED** (kernel-checked, `Tools/ShippingStRefCorrespondence.lean`, built r1 exit 0), **PREMISE**
(a Prop that would have to hold of the runtime; assumed nowhere new), **OPEN**. Nothing is added to
`RefLawsAOps`/`RefLawsATele`. **No correspondence with the real `ST.Ref` exists**; this lists what one would need.
"Not proved" ≠ "unprovable".

## 0. Setting
`ST.Prim.Ref.get/set/take/mkRef` are `@[extern] opaque` (`Init/System/ST.lean:186-196`); the world is the opaque
`Void IO.RealWorld`; `ST.Ref σ α = {ref : RefPointed.type, h : Nonempty α}` (untyped pointer). `readOf r w` is
DEFINED as the value of `ST.Ref.get r w` (ShippingChildInv:102). So in the logic `get`, `set` are uninterpreted
functions; every law below is about them. A set-theoretic model (heap) could interpret them; the real runtime fit
is a separate question (cf. `heap-model-audit.md`, `ShippingHeapModel.lean`).
`cv/sv/dv w` = `readOf` of the three tracked cells; `envAt cref w = (readOf cref w).env`.

## 1. The conditions (Lean statements, file `Tools/ShippingStRefCorrespondence.lean`)

With `getW r w`/`setW r v w` the world after `get`/`set` (match on the `ST` result):

| # | name | statement | status |
|---|---|---|---|
| C0 | value | `get r w = .mk (readOf r w) (getW r w)` | **PROVED** `readOf_get` (definitional) |
| C0' | determinism | `RunsTo m … w a w' → RunsTo m … w b w'' → a = b ∧ w' = w''` | **PROVED** `runsTo_det`, law-free. This is determinism of a *function in the logic*; it says nothing about the real runtime (threads, `take` blocking). |
| C1 | read keeps cell | `ReadKeeps r := ∀ w, readOf r (getW r w) = readOf r w` | PREMISE |
| C1' | read keeps world | `ReadWorld r := ∀ w, getW r w = w` | PREMISE; **PROVED** `ReadWorld.readKeeps : ReadWorld r → ReadKeeps r` |
| C3 | get after set | `SetGet r := ∀ v w, readOf r (setW r v w) = v` | PREMISE |
| C4 | frame of other cell | `SetFrame r r' := r.ref ≠ r'.ref → ∀ v w, readOf r' (setW r v w) = readOf r' w` | PREMISE |
| C5 | distinct cells | `sparkleChildCache.ref`, `sparkleSynthDepth.ref`, the 24 SideRefs, `mref.ref`, `cref.ref` pairwise `≠` | PREMISE (`initialize` allocates fresh cells; the logic cannot see it; refs are untyped so even same-typed `sparkleSubModuleCache`/`Nat` refs need it) |
| C6 | take/modify gap | `ST.Ref.modify` is `get; set` in the logic but `implemented_by Ref.modifyUnsafe` = `take; set` at runtime | OPEN: the logical definition and the compiled code differ; a runtime model needs `take` (cell emptied until `set`), not covered by C1–C5 |
| C7 | whole-record write | `Core.State` is ONE cell: a `modifyTraceState`/`modifyCache` writes the whole record, so env-preservation needs `SetGet cref` + the function `f` leaving `.env` | OPEN (not proved; `coreModifyTrace` is a `Framed` op in `ShippingChildInv:228` but `Framed`'s laws speak only of cv/sv/dv) |

## 2. Implications that hold (PROVED)

* `getEnvFrame_of_readKeeps : ReadKeeps cref → GetEnvFrame mctx mref cctx cref`. SR2h's single-primitive premise is
  **implied by** the weaker cell condition C1 at `cref` (a read of the Core cell does not change what the Core
  cell reads). So the trust base for `EnvSnapshot` (w1,w2) is exactly C1 at `cref` — not a wrapper: different
  statement (cell-level, about `ST.Ref.get`, not about `getEnv`), and the derivation unfolds `getEnv`.
* `envFrame_set : r.ref ≠ cref.ref → SetFrame r cref → EnvFrame (ST.Ref.set r v : MetaM Unit)`. A write to any cell
  other than `cref` (side refs, `mref`, tracked cells via `sideSet`, `localSet`, `Meta` `modify`) keeps the env, from C4 at `cref`
  and C5 for that cell. (The `modify` forms are not covered: C6.)
* `EnvFrame` is closed under `pure`/`bind` (SR2h `EnvFrame.pure/.bind`), so these compose along a `do` block.

## 3. Relation to `RefLawsAOps` (what is already stated or used)

| condition | in `RefLawsAOps`? | comment |
|---|---|---|
| C1 at cache/synth/depth | YES, on quiet worlds in admissible contexts, via `frame` at `FramedA.cacheGet/synthGet/depthGet`: `cv (endW get w) = cv w` etc. | literally C1 for the three tracked cells, restricted to `quiet w ∧ AdmCtx` (not `ReadWorld`). No wrapper theorem is stated. |
| C1 at `cref`, `mref`, side refs | NO | `frame` speaks only of `cv/sv/dv`; `Framed`/`FramedA.env` is in the op list but its law concludes cv/sv/dv only. **`RefLawsAOps` does not imply `ReadKeeps cref`** (syntactic: no field mentions `readOf cref`; an independence proof needs a model of the laws over the real types, which the opaque world forbids — OPEN). |
| C3 at cache/depth | YES, `cacheSet`/`depthSet` (cv w' = v), quiet worlds, admissible contexts | |
| C4 among cache/synth/depth | YES, `cacheSet`/`depthSet` (sv, dv unchanged / cv, sv unchanged) | for the other 21 side refs and `cref`: NOT stated |
| C4 into `cref` (env) | NO | |
| C5 | partly: `Fresh` provenance for local refs (`FramedA`), `ShippingHeapProvenance.lean` | not for `cref` |
| C0' | trivial in the logic | |
| C6, C7 | NO | |
Also: `Tools/ShippingHeapModel.lean` (`Heap σ`, `hget/hset`, `get_set_same`, `get_set_other`, `set_reg`, `HeapLaws`
with `heapLaws_sat`) models C1/C3/C4/C5 for the THREE tracked cells plus untyped `other n` cells, as a pure heap with
typed refs; it has no `Core.State` cell and no map from `Void IO.RealWorld`. `Tools/ShippingEnvSnapshot.lean` `Model.*`
is the `env`-field analogue (a read preserves `env`). `heap-model-audit.md` rows 7–9 record the fit concerns (re-typed
pointers, same-type cells, callbacks).

## 4. `Core.State` fields vs `Meta.State`
`cref : ST.Ref IO.RealWorld Core.State` and `mref : ST.Ref IO.RealWorld Meta.State` are different cells (C5).
Fields are NOT cells: `env`, `traceState`, `cache`, … live in one record read/written as a whole (C7). Hence
"`Meta.State` writes do not change `env`" is `envFrame_set` with `r := mref` (needs C4, C5), whereas "a `Core.State`
field write keeps `env`" needs SetGet at `cref` and a property of the update function — neither is derivable from C1.
`modify`-style `Meta` operations (`metaModify`) go through `take` (C6).

## 5. What remains new (not implied by anything assumed)
1. C1 at `cref` (equivalently, via `getEnvFrame_of_readKeeps`, `GetEnvFrame`): needed for `EnvSnapshot`(w1,w2).
2. C4 into `cref` for every cell written between w3 and w4 plus C5 for these cells.
3. C6 (take-based modify) and C7 (whole-record Core.State update keeps `env`; no `addDecl`/`setEnv` in source,
   but Lean's `whnf`/`mkAppM`/instance search are unmodelled — `env-snapshot-design.md` §4).
4. Any bridge `Void IO.RealWorld → Heap σ` interpreting `ST.Ref.get/set` (cf. `heap-model-audit.md`); the file
   states what that bridge must satisfy, it does not construct one. Logical inconsistency of C1–C5 jointly with
   `RefLawsAOps`: NOT PROVEN (no proof either way); runtime fit: NOT shown.
