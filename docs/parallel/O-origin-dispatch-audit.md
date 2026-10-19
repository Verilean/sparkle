# O — origin dispatch audit (grouping, module names, child cache)

Branch `par/o-close`. Patched compiler = the MAIN checkout's working tree
(`Sparkle/Compiler/Elab.lean` with the "explicit call-entry origin" change,
`Sparkle/Compiler/MachInstOrigin.lean`). Line numbers below are of that
patched `Elab.lean`. Audit by reading; nothing built.

## 1. Entry deduplication in the reader

* `machInstance` (Elab 4049–4080): an entry is reused when callee, argument
  `let`s AND origin agree (`st.instOrigins[k']? == some org`, 4075–4076).
  A memory call (origin `.mem combo aw dw`, pushed at 3958–3959 under the name
  `memChildName combo aw dw`) and an ordinary call of a declaration carrying
  that placeholder name (origin `.ord`, 3947) are therefore DIFFERENT entries
  even on the same argument `let`s. Before the patch they were merged
  (name + args only).
* `machInstanceS` (Elab 4118–4127): a structure call is reused when an entry
  with the same callee and arguments has origin `.field 0` (4118–4119); its
  fields are then `k0, k0+1, …`. That index is the first field of an earlier
  structure call of the same declaration on the same arguments (structure
  calls push all their field entries contiguously, 4123–4127, origins
  `.field 0 … .field (n-1)`), so the reuse is of the same call. An `.ord` or
  `.mem` entry can never be matched (origin test), and a declaration has one
  result type, so it cannot be both an ordinary and a structure callee.
* `insts` and `instOrigins` grow together at every push (4078–4080,
  4123–4127; no other writer of `MachRead.insts`, grep `insts :=`), so the
  index `k'` of `insts.zipIdx` reads the entry's own origin. The shape copies
  both (5195, 5197); `MachineShape.instTagged` (5224–5225) defaults a missing
  origin to `.ord`.

## 2. Call groups of the general closing

`closeInstsG` groups entries by `callGroups` (`Sparkle/IR/MachineInstG.lean`
21–25, used by `stmtsG` 57–68) on the key (emitted child MODULE name,
argument `let`s), one instance per group.

* Ordinary/structure entry vs memory entry: the memory child is
  `memModule combo aw dw`, named `ModuleName.ofMem combo aw dw`
  (`Sparkle/Compiler/MachMemory.lean` 47–51); a compiled declaration's module
  is named `ModuleName.ofDecl c` (the child interface's `name` field). These
  never coincide: `Tools.ShippingModuleName.ofDecl_ne_ofMem`
  (`Tools/ShippingModuleName.lean` 778). So no group mixes a memory with a
  declaration — in particular not the collision pair (a declaration named
  `memChildName combo aw dw` emits `ofDecl (memChildName …)`, the memory
  `ofMem combo aw dw`).
* Two memory entries of one `(combo, aw, dw)` on the same argument `let`s:
  one group, one instance. The two reads are the same function of the same
  inputs (the memory's state is a function of its write stream), so one
  instance is correct; the reader would have merged them anyway when the
  origins agree (4075–4076).
* Two structure calls: same declaration and arguments are one call (merged
  by `machInstanceS`); entries of one group are told apart by their fields
  (`hfieldsNd` / the closing's field check). Different declarations have
  different module names (`ofDecl` injective), so they never share a group.
* Ordinary entries of one declaration on one argument list: one group, the
  same child (cache), as before.

No wrong grouping found.

## 3. Child cache

`sparkleChildCache` (Elab 1032) is keyed by DECLARATION name;
`synthesizeChild` (8929–8932) reads/writes it. With the patch,
`closeInstsGM` (5229–5244) calls `synth c` only for entries whose origin has
no built child (`o.child? = none`, 5236–5239): memory-origin entries never
reach the cache. `closeInstsM` (5206–5219) synthesises every entry, but it
runs only when `instFields = []` (5261–5262), and every memory call sets
`instStruct := true` (3960), so a memory entry never reaches `closeInstsM`.
A declaration named `memChildName …` is cached under that name like any
declaration; no memory entry reads that slot. No cache confusion.

## 4. Proof-side consequences (this branch)

* `MemChildren` (`Tools/ShippingMachineEntry.lean`) and `ChildrenReal`
  (`Tools/ShippingChildInv.lean`) are restated on the origin
  (`shape.instOrigins.getD k .ord`); the producers (`closeInstsGM_returns`,
  `closeInstsGM_inv`, `closeInstsGM_run`) follow the tagged `mapM`.
* "No memory child" premises of the general closing are tag-based:
  `∀ o ∈ shape.instTagged, o.2.child?.isNone = true` (decidable).
* Name-based memory statements (`Kid`, `memNameAt`, `hsep` over names) are
  kept only under `TagsAgree` (`Tools/ShippingInstTagged.lean`: every entry's
  name decodes to what its origin builds — decided per declaration, false for a
  collision shape, which those theorems then do not cover).
* OPEN: see the report of `par/o-close` for the consumers not yet restated.

## 5. Round 2 (integrator decision): what the proofs now ask

* `hnomem` (every theorem of the general / one-output closing chains, the
  `nomem` fields of `GenKid` / `GenKidT` / `OneOutKid`, the generated
  `f.oneout_nomem` lemmas) is
  `∀ x ∈ d.shape.instTagged, x.2.child?.isNone = true ∧ (memChild? x.1).isNone = true`:
  no memory ORIGIN and no memory placeholder NAME. The tag half refutes the
  left disjunct of the (tag-based) `ChildrenReal`
  (`Tools.ShippingChildInv.nomem_tag`); the name half is what the old `core_*`
  statements need to reach the `core_*M` theorems through the name-based `Kid`
  (`real_of_kid`, `nomem_name`, `tagsAgree_of_nomem`). Decidable; generators
  that discharged `hnomem` by `decide` still do.
* The `core_*M` chain (`kid_of` callers and everything above them) asks
  `hagree : TagsAgree d.shape` (`Tools/ShippingKid.lean`, namespace
  `Tools.ShippingInstTagged`), passed by NAME (`(hagree := …)`); the old chain
  supplies `tagsAgree_of_nomem hnomem`, the memory generators `decide`,
  `GenKidM` / `MemOnlyData` / `MemOnlyDataR` / `MemOnlyCloseData` carry it as
  a field `agree`.
* Coverage: for a collision shape (a declaration named as a memory
  placeholder, read as an ordinary or structure call) `TagsAgree` and the name
  half of `hnomem` are false, so `decide` fails and those endpoints are simply
  not generated. That narrows PROOF coverage only; the compiler still accepts
  and correctly compiles the shape (origin dispatch, §1–3). Migrating the `M`
  chain to the tag-based kid `KidT` (which would lift this) is a later unit.
* Meta-level classification moved to the tag in `ShippingNoPortsMemSeqCommand`
  (`scope`: memory = origin `.mem`, and a shape failing `tagAgrees` is refused),
  `ShippingMachineClosesAtGenG` and `ShippingEntryOkCommand`. Other generators
  (`ShippingMachineDepthCommandR`, `…SeqCommand(R)`, `…MemKidCommand`,
  `…NoPortsCommand`, `…NoPortsKidsCommand`, `…LeafEntryCommand`,
  `…ShipsHierCommand`) still classify by name: for a collision shape their
  generated proofs fail (`decide` / `rfl`), which refuses, never mis-proves.
* Linked-run chain (`ShippingMachineCallsLinkedT*`, `ShippingMachineComposeR`,
  `ShippingMachineTraceX.ServedRealG/ServedReal1`, `MemFacts`, `SeqFacts*`,
  `hsv`, `hrefl`, `hrunN`, `hfn`): "memory" / "not a memory" at entry `k` is
  `(shape.instOrigins.getD k .ord).child? = some (memModule …)` / `= none`
  (it was `memChild? c`); the generators prove these by `rfl` / `decide` on
  the data, which carries `instOrigins` (`ShippingMachineCommand.dataE`).
