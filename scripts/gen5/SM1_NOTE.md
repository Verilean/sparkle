# C.SM-1: hs fixed to the concrete initsOf (Issue sparkle-ledger-sm1)

- `Tools/ShippingGen5SM1.lean`: `dataOfSound_initsOf lvl : DataOfSound (dataOfAt lvl) DataOfPure.initsOf` (= `dataOfAt_sound`),
  `FGLedgerPremisesStmtH` (G without the binders `{initsOf}` and `hs`; `genGP lvl (dataOfSound_initsOf lvl) genData₀`),
  `fgLedgerPremisesStmtH_of_G`. Axioms: propext, Classical.choice, Quot.sound.
- `Tests/Gen5/SM1Check.lean`: removed = [initsOf, hs]; added = []; changed = []; all other binders and the whole conjunction `==`;
  8 `genGP` in H all have the constant `initsOf` and `hs = dataOfSound_initsOf lvl`. Controls: no specialization fails, wrong
  initsOf fails, G-vs-G empty, H-vs-G is not a removal.
- Why meaningful: `DataOfPure.lean:354` `def initsOf d := initsFrom d.shape.layout.slots d.ss` (reset values from the layout slots
  of `d`, via `decInit`); `DataOfSound dataOf initsOf` asks `d.initOk (initsOf d)` for every `d` returned by `dataOf`, and
  `dataOfAt_sound` / `initOk_of_ok` prove it for exactly this function. `initsOf` is a spec-side function of the reset values
  (the generator `dataOfAt` itself does not take it); G's universal quantification over `initsOf` is therefore an artificial
  generalization that H removes without losing a case the generator can produce.
- Not a binder of G: C.AC-4 (`ReachCover`/`hcl`) is not an outer binder of G, so the Check cannot show it "remains" as a binder;
  it is untouched because all other binders and inner hypotheses are `==`.
- The row C.SM-1 itself needs the reviewer's decision to count -1; ledger unchanged here.
