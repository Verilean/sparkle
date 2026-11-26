# VED hierarchy H3-child: combinational children whose leaf proof failed (R224, R236, R246)

> Historical design record. Describes base `5486b424`, merged with PR #163; it is not kept in step with current `main` (file names, line numbers and option defaults may have moved). Index: [docs/README.md](README.md#historical-ved-design-records).

Issue sparkle-ved-hier3-child.  Base 5486b424.  Nothing here changes the statement (`U1Stmt` / `U2HRStmt` /
`U2HStmt`), the axioms (propext, Classical.choice, Quot.sound), the returned artifact (the module the single
`synthesizeCombinational` call returned) or any refusal: the new code only picks another SCRIPT for a
register-free child; the kernel checks everything, and a child the new routes refuse falls back to the
generated script of `Tools/VedU1Entry.lean` (what the entries did before).

## What failed

For R224 `synth_httpRespByte`, R236 `synth_tcpChecksum`, R246 `synth_usbWebServer` the hierarchical entry
refused at `child` (`VED U1 REFUSED … [proof]: … simp failed: maximum number of steps exceeded`): the child's
own U1 theorem could not be proved by the generated script.  Three shapes:

| row | child | shape | why the generated script fails |
|---|---|---|---|
| R224 | `httpRespByte` | hand-written mux chain over `let`-bound constants (`Signal.mux (eqK cnt k) bₖ …`, 34 bytes, 6-bit index) | the position-skeleton table route (`tblDataOf?`) needs `4t+2` statements named `Wt t p` and indices `0…t-1`; this body has `_gen_b*` wires, indices from 1, shared constants (134 statements); the flat `simp` does not scale |
| R246 | `respByteMux` | `kLut!` table of 74 bytes with repeated entries | the compiler shares equal constants: 256 statements instead of `4·74+2` |
| R236 | `tcpHeaderChecksumSig` | prelude + 14 `IPv4.onesAdd16Sig` stages + `~~~` | a stage uses its sum twice, so the unfolded term is a tree of size `2^stages`; 3 stages pass, 4 do not finish in 300 s, 14 exhaust the default `simp` budget; budget alone does not help (maxSteps 2·10⁷ on every `simp`: killed at 800 s) |

## Routes

* **Named constant tables** (`Tools/VedH3ChildTbl.lean`, `Tools/VedH3ChildTblEntry.lean`).  The module body is read
  as data (`NData`: wire name and form `const` / alias / `eq`-against-the-input / `mux` of each position, the
  value of every position at every input value packed `fw` bits per field).  The kernel checks that the body
  IS `NData.body`, one Bool (`NData.ok`: forms read earlier positions, names distinct without string
  comparison (`enc`), none is the input, the last is `out`), the rows (`rowsOk`: each position equals its form
  on the row), and `decide +kernel` over the input domain that the row's output equals the declaration's own
  value.  `step_ntbl` (one induction, `eval_bodyN` of the skeleton route) evaluates the body.  No shape of the
  chain (offset, order, repeats) is built into the proof.  Input width ≤ 10 bits.
* **Add-stage chains** (`Tools/VedH3ChildChain.lean`, `Tools/VedH3ChildChainEntry.lean`).  Each stage (7
  statements: `Stg`) is proved ONCE (`s1_eval`, `s2_eval`, `stg_eval`: `evalAssigns` on any environment with
  the width / range hypotheses) and the chain is composed by induction (`chain_eval`), `body_eval` adds the
  prelude and the `~~~`.  The value is `onesAddN` folded over the words: linear in the number of stages.  The
  signal side rewrites `IPv4.onesAdd16Sig` to the copy `onesStageSig` (`rfl`, checked) and uses
  `onesStageSig_toNat` stage by stage.
* **Choice** (`Tools/VedH3ChildEntry.lean`, `checkCombChild`): chain, else named table (only when `tblDataOf?` does
  not take the body), else generated; a refusal of the chosen source falls back to the generated script.
  Hooks: one call in `Tools/VedU2HierEntry.lean` (`checkU2H`) and one in `Tools/VedU2HierRegEntry.lean`
  (`phase1`).

"Reuse and compose": each child is proved once (`<decl>.ved_child.<child>.ved_u1`) and the parent composes that
theorem by the existing U2 hierarchy composition; the leaf routes make the child theorem cheap
(R224: 4.5 s for the leaf against a refusal after 53 s; R246's child 15 s against 135 s / 20 GB refused; R236's
14-stage leaf 18 s against a refusal after 36 s).  Full inlining of the child into the parent was not tried
(it is not the default and would grow the size).

## What remains: R246

The child `respByteMux` is now proved, but the parent `usbWebServer` is refused at `[open]`:
`the declaration's value does not reduce to a call of respByteMux`.  The child's output feeds the slip framer
and the UART (registers of the parent), it is not the declaration's output; H2c-state (`genOpenSt`) covers a
declaration that IS one call of the child.  Minimal reproduction: `usbMin` below (register `ph` drives the
child, the child's output feeds register `o`).

```lean
def usbMin (trigger : Signal defaultDomain Bool) : Signal defaultDomain (BitVec 8) :=
  circuit do
    let ph ← Signal.reg (0#3)
    let o ← Signal.reg (0#8)
    let phS := (ph : Signal defaultDomain (BitVec 3))
    ph <~ Signal.mux trigger (phS + 1#3) phS
    o <~ tabC phS            -- tabC: a `@[hardware_module]` kLut! child
    return (o : Signal defaultDomain (BitVec 8))
#ved_u2_hier usbMin           -- refused [open] (10 s)
```

A fix needs the open parent for a child whose output feeds the parent's own state: the child's output at
cycle `t` is `g (a t)` where `a t` is a function of the same state, so the state invariant and the child's
output equation have to be proved in one induction over cycles (H2c-state does this for the output only).
