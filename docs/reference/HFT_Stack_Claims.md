# HFT TCP/IP Stack — What Is and Isn't Proven

This doc captures honestly what the Phase A–D work landed
in `IP/Net/{Ethernet, ARP, IPv4, ICMP, TCP, TCPState,
HTTP, HFTStrategy}.lean` actually demonstrates — and,
just as importantly, what it does NOT.

Future maintainers and reviewers should read this BEFORE
making external claims about Sparkle's network stack.

---

## TL;DR

| Claim level                                  | Status              |
|----------------------------------------------|---------------------|
| Builds clean (`lake build`)                  | ✅ Yes              |
| Passes per-cycle sim against hand references | ✅ Yes              |
| Emits Verilog that iverilog accepts and runs | ✅ Yes (13/13)      |
| iverilog output matches Lean sim cycle-by-cycle | ✅ Yes           |
| Formally verified equivalence (Lean theorem) | ❌ No (none today)  |
| Formally verified RFC conformance            | ❌ No               |
| Fuzz / property test coverage                | ❌ No (golden only) |
| Production-ready                             | ❌ No               |

---

## What "passes" actually means in the current tests

Each layer (Ethernet TX, ARP, IPv4, ICMP, TCP header, TCP
FSM, HTTP emit/parse, HFTStrategy) ships:

1. **A Lean cycle-by-cycle sim test** (`Tests/IP/Net/*Test.lean`),
   which:
   - Drives the module with `Signal.val k` for `k = 0..N`.
   - Compares each cycle's output (byte / state / flag) to
     a **hand-authored expected list**.
   - Calls `IO.Process.exit 1` on the first mismatch, so the
     `lake test` release gate goes red.

2. **A `#synthesizeVerilog` build-time check** in a
   `section SynthesisChecks` block.  This proves the IR
   elaborator can lower the module's body into a Verilog
   module — i.e. the design is structurally synthesizable.
   It does NOT check that the emitted Verilog is *correct*.

3. **(Most layers) an iverilog round-trip fixture** in
   `Tests/RoundTrip/IVerilogSim.lean`, which:
   - Synthesizes the module to SystemVerilog at elab time
     via `verilogOf!`.
   - Writes the SV + a hand-crafted testbench to `/tmp`.
   - Invokes `iverilog -g2012` + `vvp` from the test
     driver.
   - Parses vvp's `$display` output, one decimal value per
     cycle.
   - Diffs the captured trace against a hand-authored
     `expected : List Nat`.

The iverilog round-trip is the **strongest** check today
because it's a **cross-simulator equivalence**: Sparkle's
Lean-side semantics agrees with Icarus Verilog 13.0's
SystemVerilog semantics on the per-cycle wire trace.  But:

- The expected list is hand-authored, so it can only test
  paths the human thought of.
- A regression that breaks a path NOT in the expected list
  is invisible.
- The latency / cycle accounting is captured in comments
  like "iverilog cycle k = sim cycle k+1" — these are
  observations, not theorems.

---

## What is NOT proven

### 1. No formal theorems

Search the repo:

```
$ grep -rn "theorem\|lemma" IP/Net/ Tests/IP/Net/
(no output)
```

There are zero `theorem`s in any of the Phase A–D files.
Nothing has been verified in Lean's logic.  The framework
exists (`#verify_eq` / `#verify_eq_at` / `#verify_eq_git`
in `docs/reference/Verification_Framework.md`) but was not
used.

What this means concretely:

- The TCP state machine's transitions are tested on ONE
  scripted scenario, not proven to follow RFC 793 for all
  possible input sequences.
- The IPv4 / ICMP / TCP checksum is tested against
  reference values computed from the same Lean function
  it's implementing — so the test proves "the Signal-side
  matches the pure-data side", not "the pure-data side
  computes the RFC checksum".  (The pure-data side is
  trivially the RFC formula by inspection, but we have no
  machine-checked link.)
- The HFT Strategy's "5-cycle reaction latency" is
  observed on ONE inbound waveform.  It's not proven for
  any input pattern.

### 2. No fuzz / property testing

All tests use a single golden vector per module.  There's
no QuickCheck / property-based testing layer:

- "feed any RFC-valid ARP request, get a valid ARP reply"
  — not tested.
- "no IPv4 checksum has a false positive on a corrupted
  header" — not tested.
- "TCP server FSM never reaches a state outside
  {CLOSED, LISTEN, SYN_RCVD, ESTABLISHED, CLOSE_WAIT,
   LAST_ACK}" — not proven (could be by `bv_decide` over
  the 4-bit state space, but isn't).

### 3. No RFC conformance audit

The bytes the modules emit match what an engineer would
*hand-write* from reading the RFC, but no machine-checked
RFC parser confirms it.  Off-by-one errors in flag bit
positions, wrong byte order, or wrong field widths could
slip through.

### 4. No real-NIC integration

- No PHY-side MAC.
- No XGMII / SGMII serdes.
- No DMA / host-side bridge.
- No bus interface.
- No timing closure analysis (the synthesized Verilog has
  not been through yosys, nextpnr, or any FPGA P&R tool).

### 5. No throughput / latency measurement at scale

"5 cycles" is a sim observation, not a wall-clock
measurement.  At what clock frequency? On what FPGA? Held
by which place-and-route? Open questions.

---

## What CAN be claimed honestly

These statements are defensible from the current evidence:

✅ "Sparkle's DSL can express the wire-format pieces of
   an HTTP-over-TCP-over-IPv4-over-Ethernet stack."

✅ "Sparkle's IR elaborator can synthesize that stack into
   SystemVerilog."

✅ "iverilog accepts the emitted SystemVerilog and produces
   the same per-cycle byte trace that Sparkle's Lean-side
   simulator produces, on every fixture we tested
   (13/13 PASS)."

✅ "A simple NIC-side strategy block, wired together from
   the stack's parser and emitter, exhibits a 5-cycle
   reaction latency from inbound `GET ` to outbound first
   byte, in both Lean sim and iverilog."

✅ "All scripted scenarios round-trip end-to-end without
   the host CPU appearing anywhere in the design."

What MUST NOT be claimed:

❌ "The TCP state machine is RFC 793 compliant."
   (No formal proof; only one scripted scenario.)

❌ "The IPv4 checksum is correct for all inputs."
   (No proof; only the implementation's own reference.)

❌ "This is production-ready HFT hardware."
   (No PHY, no timing closure, no fuzz testing, no formal
   verification.)

❌ "Sparkle proves the stack correct."
   (No theorems exist over any of the stack modules.)

---

## What it would take to upgrade each claim

### From "sim + iverilog cross-check" → "formal equivalence"

For each module, add a `#verify_eq` between its Lean
sim function and a Lean reference function on `BitVec`
inputs (typically over 1..2 cycles of the FSM).  See
`docs/reference/Verification_Framework.md` for the
machinery.  For combinational pieces (byte muxes,
checksum, packet encoders) this should be ~5 lines per
module.  For sequential FSMs, `#verify_eq_at` is the
right tool.

### From "scripted scenario" → "RFC conformance"

Need a machine-readable RFC fragment (or a
QuickCheck-style generator constrained by the RFC) and a
property check that every generated input either:

- (a) is rejected by the parser AND would have been rejected
  by the RFC, or
- (b) is accepted AND produces the same parse result a
  reference parser does.

This is genuinely substantial work — not a follow-up,
a project.

### From "iverilog passes" → "FPGA passes"

Run the emitted SystemVerilog through yosys (synthesis)
and nextpnr (place-and-route) for a target FPGA, then
either a Verilator co-sim or a real hardware test.
Documenting the achieved frequency makes the "5 cycle
~32 ns" claim concrete.

---

## Recommended posture for external claims

When writing a blog post, paper, or talk about Phase
A–D:

> Sparkle implements an HFT-leaning TCP/IP stack
> (Ethernet → IPv4 → TCP → HTTP) plus an inbound-trigger →
> outbound-emit "strategy" block end-to-end in its
> Lean-DSL.  The implementation passes a per-cycle Lean
> simulator and a Sparkle → SystemVerilog → iverilog
> round-trip on hand-authored fixtures for every layer.
> All scripted scenarios run without host-CPU
> involvement and exhibit a 5-cycle reaction latency in
> sim.

That's the maximum honest claim.  Anything stronger
either requires the additional work above, or is
overclaiming.
