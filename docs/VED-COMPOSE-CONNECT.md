# VED-COMPOSE-CONNECT: the returned IR's cones connected to the open parent's deep cones (small examples)

Issue `sparkle-ved-compose-connect`, branch `ved/compose-connect1` (base 425119c7 = `ved/proof-compose` 6ff184d4 + the approved
research ca892a1f).  Option `ved.compose.connect` (default `false`).  New files: `Tools/VedComposeConnect.lean`,
`Tools/VedComposeConnectGen.lean`, `Tests/Ved/ComposeConnectCheck.lean`; edited: `lakefile.lean` (four stanzas), a one-field
addition to `DeepInfo` (`Tools/VedU2HierStateArgs.lean`) and one option-gated hunk in `Tools/VedU2HierRegEntry.lean`.

## Scope (do not read more into it)

Small-example result: `multiTwo` and `multiShared` of `Tests/Ved/U2HierMultiCheck.lean` (copied into the Check).  No real-IP row
was run; the coverage stays 244/327; this is not the completion of circuit composition in general.  The statement `U2HRStmt`
is unchanged (the stored type is compared with `==`), the guarantee is that of docs/VED-MAIN-INTRO.md ("What it guarantees, and
what it does not") and docs/VED-U1-MAIN.md ("What it does not claim").  The parent's loop is still tied to the declaration by the
existing knot; the child theorem is the child's own `ved_u1`.

## What the option changes

With the option on (and `ved.compose.step` on), `scriptTextR` returns, right after the prelude of the step (`intro E hasgF hEin
hEreg hEorc`, the register/input/oracle facts `hEr`, `hlS`, `hE_`, `hEo`, `hlto`), the lines of
`Tools.VedComposeConnectGen.hlocLines` and nothing else: the chain walk, the `bundle_slice_fact` reads and the per-cone `simp`
closers are NOT emitted, so there is no old fallback in that mode.  The hkid blocks (instance arguments, child theorems,
H2/H3 wiring) are the existing ones.  Every connection logs `VED COMPOSE CONNECT: ...` (tactic `ved_connect_log`).

## Supply table: `cone_connect_bnf` (the approved `cone_connect_bn` plus the flattening step)

| hypothesis | supplied by |
|---|---|
| `hwi hri hwr` | the three `hb0.*` facts the `refine step_local` already passes |
| `hW : WOKb (declWidth m) m b0 = true` | closed, `decide +kernel`, once per `hloc` (W, returned side) |
| `hasg hEin hEreg hEorc` | the binders of `hloc` (`step_local`) |
| `hl0 : leafOk (cutNames d m b0) (inl ..) = true` | closed, `decide +kernel`, per cone |
| `hrange` (needed leaves only) | `hrangeN : ∀ y ∈ needed, E y < 2 ^ declWidth m y` proved once from the prelude facts (register: `hEr`+`hlS`, i.e. `BitVec.isLt`; data input: `hok.1 t` (`InputsOk`), the clock is not in `needed`; instance output: `hlto` from the child's output `isLt`), and `neededOk needed (inl ..) = true` (closed) per cone (R) |
| `hc` | the cone `bn (declWidth m) n2 (flat n3 (inl (Atab m b0) n e))`, never written out |

## The new lemmas (`Tools/VedComposeConnect.lean`)

* `ren_eval` (W): `evalExpr we' E' (renE τ c) = evalExpr we E c ∧ widthOf we' (renE τ c) = widthOf we c` when every leaf `x` of `c`
  has `we' (τ x) = we x` and `E' (τ x) = E x` (the two-environment versions of the research file's `*_map` lemmas).
* `tauOf`, `tabW` (closed), `tabW_sound`, `cone_deep_eval`: the leaf table `tab : List (String × Nat)` (returned name ↦ slot of the deep
  context) gives the renaming into `nm`; `tabW` checks that every leaf of the returned cone is in the table and that
  `declWidth m x` is the width of the slot in the deep context `Γr ++ Γi`; `hV` (`VOk`) is the leaf-value obligation (registers by
  `hR`, data inputs by `InputsOk` + `bit_toNat`/`bv_toNat`, oracle inputs by the definition of `Ow`: ONE cone input serves every
  instance of the class).
* `flat`, `slc`, `flat_sound`, `refs_flat`, `cone_connect_bnf`: the right-nested register bundle of the synthesiser
  (`concat [r0, concat [r1, r2]]`) is flattened (`Tools.ConcatNorm.concat_pivot`) and a slice of a slice that stays inside is composed
  (`slice_slice_val`, by `Nat.testBit`); needed because the approved `bn` resolves slices of FLAT concatenations only (this is
  what stopped `multiShared`, three registers).
* `connect_value`, `reg_connect`, `out_connect` (F): `reg_connect` concludes `Cdo.irState deep nm inp (t+1) i = E x`, `out_connect` the
  `getD 0 (evalExpr .. (compile nm deep.out))` form of `_deep_trace`; the fidelity theorem `_deep_fidelity_*` enters as an argument
  and its TYPE supplies the literal (`renE (tauOf ..) (bn ..) = L` is closed, proved by `rfl`).

## Observations

* `multiTwo`: 2 registers + the port, `multiShared`: 3 registers + the port, all by the connection lemmas; proof elaboration ~4.4 s
  (the option-off compose script ~6 s for `multiTwo`; single runs, not a measurement of anything at scale).
* The connection equation is checked by `rfl` in the elaborator (Meta `isDefEq`); the kernel then re-evaluates it.  At R193 size
  this and the `String` scans in `asgOf` are the expected costs (research §M4); nothing is claimed.

## Commits

See `git log ved/compose-connect1`.

## Batched closed checks (unit 2)

`reg_connect` takes four closed facts per register. Proving them by four `decide +kernel` / `rfl` calls per register re-evaluated the
inlined cone from a cold cache every time (observed on the kMux toy, 13 registers: ~1 s each, 48 of 81 s of the parent proof; 24 registers: 368 s).
`RegsOk` is one Bool over all register slots, evaluated once by the kernel; `regs_spec` returns each slot's four facts
(`hren` through `eqE_sound` against `CExpr.compile nm (deep.next i)`, identified with the fidelity literal by `hfid`).
The approved lemma statements are unchanged. Observed (single runs): parent proof 8/12/24 registers 19.3 / 27.1 / 64.4 s (before: 42.9 / 80.7 / 368.4 s).
Scope: local-lemma result on toys; a real-IP row (R194) was run once and is NOT accepted (budget exhausted before the connection block, see the unit report).
