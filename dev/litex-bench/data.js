window.BENCHMARK_DATA = {
  "lastUpdate": 1778544521798,
  "repoUrl": "https://github.com/Verilean/sparkle",
  "entries": {
    "LiteX PicoRV32 SoC Benchmark (Verilator vs JIT)": [
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "98ac7361c5dad230d81c0c6a091d0a9034ea75c7",
          "message": "fix(ci): make LiteX benchmark JSON bulletproof\n\nThe 'Run LiteX benchmark (10M cycles)' step was piping raw Verilator /\nbench_litex stdout through bash command substitution and interpolating\nthe values directly into a heredoc that wrote litex-bench-results.json.\nWhen either binary emitted anything non-numeric on stdout (stray\nwarnings, newlines, a nonzero exit, dlopen error messages, etc.) the\nresulting JSON became malformed and benchmark-action aborted with\n\n    Error: Output file for 'custom-(bigger|smaller)-is-better' must be\n    JSON file containing an array of entries in BenchmarkResult format\n\nChanges:\n- set -euo pipefail inside the step so silent failures are caught.\n- Capture raw stdout/stderr of both benchmarks, echo them to the log\n  for post-mortem diagnostics, then sanitize with 'tail -n1 | tr -cd 0-9'\n  to keep only the trailing numeric result.\n- Fall back to 0 when either value is empty (instead of leaving the\n  shell variable unset, which would produce a JSON syntax error).\n- Harden bench_litex.cpp: null-check dlopen/dlsym before use so we\n  get a clear error message on stderr rather than a segfault.\n- Write the JSON via 'python3 - <<PYEOF | json.dumps' rather than a\n  bash heredoc containing literal braces. This eliminates the whole\n  class of shell-quoting bugs and gives deterministic formatting.\n- Add a post-write python3 validator that parses the JSON, checks\n  it's a non-empty list of {name, unit, value} dicts with numeric\n  values, and fails loudly if not — so we never hand a half-broken\n  file to benchmark-action again.",
          "timestamp": "2026-04-09T00:03:34+09:00",
          "tree_id": "5f1142e3171511e82c6b575de467e70a1b94f065",
          "url": "https://github.com/Verilean/sparkle/commit/98ac7361c5dad230d81c0c6a091d0a9034ea75c7"
        },
        "date": 1775661011353,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4724820,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2157105,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "12ee4e1f1232a39fbb5226d30f7c45baf09dbdba",
          "message": "fix(ci): harden multicore + rv32 benchmark JSON writers too\n\nThe push CI failed with a decisive error message:\n\n    Error: Output file for 'custom-(bigger|smaller)-is-better' must be\n    JSON file containing an array of entries in BenchmarkResult format:\n    Unexpected token '%', ..\"\"value\": %Warning: \"... is not valid JSON\n\nSo Verilator's 8-core Vsim binary was emitting %Warning-UNSIGNED /\n%Warning-WIDTHEXPAND diagnostics on stdout at runtime; those got\ncaptured into VLTR_8CORE via command substitution and interpolated\nliterally into multicore-bench-results.json, producing\n\n    \"value\": %Warning: ...\n\nApply the same bulletproof treatment the LiteX bench step already got:\n\n- set -euo pipefail for fast failure detection.\n- sanitize_num() helper: tail -n1 | tr -cd '0-9' + fallback to 0,\n  guaranteeing the shell variable is always a pure digit string.\n- 2>&1 capture so stderr shows up in the CI log but doesn't pollute\n  the numeric extraction.\n- dlopen/dlsym NULL-checks in bench_1core/bench_8seq/bench_8par so\n  load failures print a clear stderr message instead of segfaulting.\n- Write multicore-bench-results.json via python3 json.dumps instead\n  of a bash heredoc full of literal { } / $vars — removes the whole\n  class of shell-quoting bugs.\n- Post-write python3 validator that asserts list shape and numeric\n  'value' fields, failing the step loudly if the file is malformed\n  (instead of handing it to benchmark-action and getting a cryptic\n  truncated error message).\n\nAlso apply the same sanitize_num + python writer + validator to the\nearlier rv32-bench-results.json step so the same pattern can't bite\nit later — the old grep-based extractor was probably fine but this\nkeeps all three bench steps consistent.",
          "timestamp": "2026-04-09T00:30:36+09:00",
          "tree_id": "c7aa73af466a0460b156f6325645838adae6fcc9",
          "url": "https://github.com/Verilean/sparkle/commit/12ee4e1f1232a39fbb5226d30f7c45baf09dbdba"
        },
        "date": 1775662684511,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 5614325,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2510739,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "fb6d0f775a24d47031c7f229549005929c985258",
          "message": "fix(ci): bump Lean to v4.28.0 so LSpec olean matches toolchain\n\nThe push CI was aborting mid-run inside Tests/AllTests with:\n\n    uncaught exception: failed to read file\n    '.lake/packages/LSpec/.lake/build/lib/lean/LSpec.olean.server',\n    incompatible header\n\nRoot cause: LSpec's pinned commit (8e6ddb17, dated pre-bump) shipped a\nlean-toolchain file declaring v4.26.0, while our project was pinned at\nv4.28.0-rc1. When lake recursed into the LSpec package elan switched to\nv4.26.0 to build it — producing oleans tagged with the v4.26.0 header\nformat — and our project then tried to load them under v4.28.0-rc1 at\nruntime, failing the header check the first time lspecIO was invoked\n(right after the BitNet test suite finished).\n\nlake update LSpec bumps the package to dc0904293d and re-aligns its\ntoolchain to v4.28.0 (stable). Our project's lean-toolchain is updated\nto match (v4.28.0-rc1 → v4.28.0) so everything compiles and loads under\none consistent Lean version.\n\nVerified locally:\n  lake build                            clean\n  lake exe test                         exit 0 (full BitNet + YOLOv8 +\n                                                 CAVLC + H.264 + AXI4)\n  lake exe svparser-test                34/34\n  lake exe sim-runner-test              27/27\n  lake exe cdc-multi-clock-test         PASS",
          "timestamp": "2026-04-09T03:41:08+09:00",
          "tree_id": "37c5d3da0589b8a891b2eb0f5dffb134831e6c34",
          "url": "https://github.com/Verilean/sparkle/commit/fb6d0f775a24d47031c7f229549005929c985258"
        },
        "date": 1775674170045,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4645079,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2161033,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junjihashimoto@users.noreply.github.com",
            "name": "junji hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "642e7b54a3659285ae5b037a95f335cc0cb2d38b",
          "message": "Merge pull request #19 from Verilean/feature/sim-parallel\n\nfeat(sim): add runSim auto-dispatcher for multi-domain simulation",
          "timestamp": "2026-04-09T03:57:18+09:00",
          "tree_id": "37c5d3da0589b8a891b2eb0f5dffb134831e6c34",
          "url": "https://github.com/Verilean/sparkle/commit/642e7b54a3659285ae5b037a95f335cc0cb2d38b"
        },
        "date": 1775674976112,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4815224,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2166369,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "74b2b8638cbb54e96555e315dd2df6a43138c513",
          "message": "feat(sim): add endpointCycles for asymmetric CDC + fix Tutorial\n\nThe CDC example in Tutorial.md Step 6 was misleading: both 'producer'\nand 'consumer' modules wrote 'input clk' and the call site passed a\nsingle uniform 'cycles := 1_000_000', making it look like the two\nendpoints shared a clock. They don't — runSim runs each endpoint on\nits own thread with its own independent evalTick loop — but the\nexample provided no way to express a frequency ratio either.\n\nWorse, the runSim refactor that introduced the typed API had silently\nregressed the original JIT.runCDC functionality: runCDC accepted two\ndistinct cycle budgets (cyclesA, cyclesB) which let callers model e.g.\na 2:1 clock ratio, but my runSim wrapper passed the same 'cycles' value\nto both sides, flattening every CDC sim to a 1:1 ratio. Tests/CDC/\nMultiClockTest had quietly inherited this by switching from 200k/100k\nto 200k/200k when I ported it.\n\nChanges:\n\n- Sparkle/Core/SimParallel.lean: runSim gains an optional\n  'endpointCycles : List UInt64 := []' parameter. When non-empty it\n  must have the same length as endpoints, and each entry becomes that\n  endpoint's cycle budget (overriding the uniform 'cycles'). When\n  empty the old behaviour is preserved. runSingleSim and\n  runMultiDomainSim are unchanged.\n\n- Tests/CDC/MultiClockTest.lean: restore the historical 200k / 100k\n  asymmetry with endpointCycles := [200000, 100000]. The CDC queue now\n  genuinely exercises the 2:1 ratio again (81k sent, 80k received vs\n  the symmetric 100k/100k).\n\n- Tests/Sim/SimRunnerTest.lean: three new regression tests (now 30/30):\n  F1 asymmetric endpointCycles [200k,100k] delivers messages\n  F2 length mismatch between endpoints and endpointCycles is rejected\n  F3 endpointCycles overrides 'cycles' when both are given\n\n- docs/Tutorial.md: rewrote the CDC section. Renamed the example\n  modules to producer_mod / consumer_mod, introduced endpointCycles\n  with an explicit 200 MHz / 100 MHz cycle ratio, and added a plain-\n  language warning that writing 'input clk' in two sim! modules does\n  NOT by itself create two domains — the two-domain-ness comes from\n  runSim running each endpoint on its own thread plus the SPSC queue\n  that CDC-synchronizes the payload. Users who need a hard 2-flop\n  synchronizer still have to add it in their Verilog explicitly.\n\nVerified:\n  lake exe svparser-test           34/34\n  lake exe sim-runner-test         30/30  (+3 from F1-F3)\n  lake exe cdc-multi-clock-test    PASS   (now exercising 200k/100k)",
          "timestamp": "2026-04-09T04:15:45+09:00",
          "tree_id": "b941864ad03949d373f4a0bb76a9de417d52e765",
          "url": "https://github.com/Verilean/sparkle/commit/74b2b8638cbb54e96555e315dd2df6a43138c513"
        },
        "date": 1775676105958,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4733846,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2166747,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junjihashimoto@users.noreply.github.com",
            "name": "junji hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "96c7ade9e7c9c2db4739e9142459185f92a96a4c",
          "message": "Merge pull request #20 from Verilean/feature/sim-parallel\n\nfeat(sim): add endpointCycles for asymmetric CDC + fix Tutorial",
          "timestamp": "2026-04-09T04:17:40+09:00",
          "tree_id": "b941864ad03949d373f4a0bb76a9de417d52e765",
          "url": "https://github.com/Verilean/sparkle/commit/96c7ade9e7c9c2db4739e9142459185f92a96a4c"
        },
        "date": 1775676186928,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 5738133,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2509913,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "ac50cf32b82af6fcb7714343de745424f6e92766",
          "message": "fix: CppSim wide integer (>64bit) support in evalTick and slice/concat\n\nTwo fixes for std::array<uint32_t, N> handling in CppSim:\n\n1. evalTick wire localization: wires >64 bits were excluded from\n   evalTick's local declarations (isScalar check), causing\n   \"undeclared identifier\" errors when evalTick referenced them.\n   Fix: declare wide integer locals with std::array zero-init.\n\n2. slice on wide integers: >> operator doesn't work on std::array.\n   Fix: emit word-level array indexing (array[wordIdx] >> bitOffset)\n   for source widths >64 bits, handling cross-word boundary cases.\n\n3. concat producing >64 bits: shift+OR chain doesn't work for\n   std::array results. Fix: emit std::array initializer with\n   word-level packing.\n\nFixes oracle-accuracy-test which exercises the SoC with BitNet\nperipheral using 80-bit intermediates (48×32 scale multiply via\nsignExtendSignal).\n\nAll tests pass: 34/34 parser, 30/30 sim-runner, 4/4 oracle-accuracy,\n3/3 BitNet SoC, 3/3 TimeMux, 7/7 golden compare, FFN golden.",
          "timestamp": "2026-04-11T09:03:47+09:00",
          "tree_id": "9342988b570d851d1e422d8021f4638f7ae1c775",
          "url": "https://github.com/Verilean/sparkle/commit/ac50cf32b82af6fcb7714343de745424f6e92766"
        },
        "date": 1775866197802,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4729772,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2167794,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "a84111bc5db1b691b16a1a4b0f0fd083c4356211",
          "message": "fix: update TestLayers for rmsNormSignal and ffnBlockSignal signature changes\n\nrmsNormSignal now takes recipN : BitVec 32 parameter (Nat.pow doesn't\nreduce through synthesis). ffnBlockSignal takes explicit residualInput\nparameter (Array.getD generates unsynthesizable ite).\n\nAll tests pass including lake exe test.",
          "timestamp": "2026-04-11T09:20:12+09:00",
          "tree_id": "e8c666154ccd6711e7f4b6c4112c0fb5b471bfc6",
          "url": "https://github.com/Verilean/sparkle/commit/a84111bc5db1b691b16a1a4b0f0fd083c4356211"
        },
        "date": 1775867319448,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 5814438,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2512686,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "b1fcbd602aa6dc44ebb64886d3fbce3a056011bf",
          "message": "fix: CppSim wide integer evalTick locals + structural test update\n\nCppSim: wide integer (>64 bit) wires declared in evalTick without\nzero-initialization (just type declaration). Avoids both the\nundeclared variable error and the per-cycle init performance hit.\nWires are always written before read (Verilog wire semantics).\n\nBitNetSoCTest: structural check updated from _gen_bitnetOut (old\nplaceholder wire name) to _gen_gateAcc + sext_msb (FFN pipeline\nindicators that survive inlining). The real BitNet FFN is now\nfully inlined into the SoC, so the old wrapper wire name is gone.\n\nAll tests pass: oracle-accuracy 4/4, BitNet SoC 3/3, parser 34/34,\nsim-runner 30/30.",
          "timestamp": "2026-04-11T09:50:30+09:00",
          "tree_id": "84774db419418400b9f173eaccf0a4062d1a839a",
          "url": "https://github.com/Verilean/sparkle/commit/b1fcbd602aa6dc44ebb64886d3fbce3a056011bf"
        },
        "date": 1775870127189,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 5853735,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2565134,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "ed32cb5ae26562810d4b7ee689c9c002799c6c6b",
          "message": "fix: update BitNet MMIO test expected value in firmware\n\nTest 9 (BitNet MMIO) expected 0xDEADBEEF from AI_OUTPUT, which was\nthe old placeholder value. Now bitNetPeripheral runs the real FFN\npipeline, so bitNetPeripheral(0) = 0. Updated expected value to 0.\n\nRebuilt firmware.hex with riscv32-none-elf-gcc.\nCppSim: ALL TESTS PASSED (including Test 9 BitNet MMIO).",
          "timestamp": "2026-04-11T11:25:27+09:00",
          "tree_id": "2dd432ea40b1de137eea99bb37b4526bf4f3e250",
          "url": "https://github.com/Verilean/sparkle/commit/ed32cb5ae26562810d4b7ee689c9c002799c6c6b"
        },
        "date": 1775874730909,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4707648,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2162696,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junjihashimoto@users.noreply.github.com",
            "name": "junji hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0a6400738936eb1f6f4931958e28f395bc04554a",
          "message": "Merge pull request #21 from Verilean/feature/fpga\n\nAdd Equivalence Verification Checking and SoC with Bitnet",
          "timestamp": "2026-04-11T12:22:35+09:00",
          "tree_id": "2dd432ea40b1de137eea99bb37b4526bf4f3e250",
          "url": "https://github.com/Verilean/sparkle/commit/0a6400738936eb1f6f4931958e28f395bc04554a"
        },
        "date": 1775878092379,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4832108,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2160440,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "f3af4e38661e152661c704c4bf9f990a542b8bd3",
          "message": "test: top-level integration sim — pipeline starts correctly\n\nTopLevelSim.lean drives the full BitNet accelerator through HostIF:\n  cycle 2: write TOKEN_IN = 0x10000\n  cycle 3: write CTRL.go = 1\n  cycle 4+: observe status\n\nResults (50 cycles):\n  ✅ busy=true after go pulse (accelerator started)\n  ✅ perfCycles counting (performance counter active)\n  ✅ STATUS=0x2 (busy bit set)\n  ✅ No crash (all 50 cycles complete)\n  ⚠ done not asserted (expected: zero weights + no HBM response\n     means forward pass cannot complete)\n\nThis proves the top-level wiring is correct: HostIF register writes\npropagate through AutoRegressive → FullModel, and the FSM enters\nthe expected busy state. Full completion requires weight data from\nHBM (or a simulation model providing valid responses).",
          "timestamp": "2026-04-11T20:36:09+09:00",
          "tree_id": "2c6c8c58822980c49eb476abb49347b863805f7f",
          "url": "https://github.com/Verilean/sparkle/commit/f3af4e38661e152661c704c4bf9f990a542b8bd3"
        },
        "date": 1775908757114,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4725709,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2161179,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junjihashimoto@users.noreply.github.com",
            "name": "junji hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f9dc9ba819940dcf58c58be55d103e40b7d8a28c",
          "message": "Merge pull request #22 from Verilean/feature/fpga\n\nUpdate the FPGA implementation",
          "timestamp": "2026-04-11T22:39:12+09:00",
          "tree_id": "2c6c8c58822980c49eb476abb49347b863805f7f",
          "url": "https://github.com/Verilean/sparkle/commit/f9dc9ba819940dcf58c58be55d103e40b7d8a28c"
        },
        "date": 1775915072182,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 5832318,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2509119,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "4dd22e917045193905bc1a073ce25f535f09d2f9",
          "message": "feat: position/velocity/altitude control + spray mission simulation\n\nAdd the missing navigation stack between path planner and attitude PID:\n  - PositionController.lean: position P → velocity PID → attitude setpoint\n  - Altitude PID → throttle command\n  - SprayDroneSoCParallel: full pipeline wired (planner → nav → attitude → motors)\n\nClosed-loop simulation validates 4 capabilities:\n  1. Hover stability: altitude holds at 3.000m (±0.001m)\n  2. Altitude control: climbs from 0→3m, settles within 5s\n  3. Waypoint tracking: reaches 7.5m/10m target in 10s\n  4. Spray mission: 3-pass serpentine over 50m field\n     - 64m total distance, 1 waypoint hit\n     - Max attitude: roll=0.033 rad, pitch=0.034 rad\n     - Altitude error: 0.0006m (sub-millimeter hold)\n     - Spray active during flight legs\n\nRegressions: 34/34 parser, 30/30 sim-runner.",
          "timestamp": "2026-04-12T18:23:40+09:00",
          "tree_id": "607e197de3098b50a8bc9fa7c6c28b745a1fd444",
          "url": "https://github.com/Verilean/sparkle/commit/4dd22e917045193905bc1a073ce25f535f09d2f9"
        },
        "date": 1776049308420,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4764466,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2159884,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junjihashimoto@users.noreply.github.com",
            "name": "junji hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "fb1e464b5381830a7de792f3f9e80613dae8a05f",
          "message": "Merge pull request #23 from Verilean/feature/fpga\n\nAdd the drone SoC",
          "timestamp": "2026-04-13T11:58:18+09:00",
          "tree_id": "607e197de3098b50a8bc9fa7c6c28b745a1fd444",
          "url": "https://github.com/Verilean/sparkle/commit/fb1e464b5381830a7de792f3f9e80613dae8a05f"
        },
        "date": 1776049435540,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4820033,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2144875,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junjihashimoto@users.noreply.github.com",
            "name": "junji hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "599c8125c368bffd3646c516366a9087d0b89519",
          "message": "Merge pull request #25 from Verilean/fix/tutorial\n\nFix documents to test the codes in Tutorial",
          "timestamp": "2026-04-18T14:53:18+09:00",
          "tree_id": "302335bd11e124786db88ee2d4a7442eae56b092",
          "url": "https://github.com/Verilean/sparkle/commit/599c8125c368bffd3646c516366a9087d0b89519"
        },
        "date": 1776491958427,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4791580,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2157833,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junjihashimoto@users.noreply.github.com",
            "name": "junji hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "252341078dba3c2612719746e6a459dada2248ea",
          "message": "Merge pull request #26 from xiangze/howtouse\n\nadd How to import and use external project",
          "timestamp": "2026-04-25T04:23:32+09:00",
          "tree_id": "45b6373675b2204947fb0686cab378fb02540d76",
          "url": "https://github.com/Verilean/sparkle/commit/252341078dba3c2612719746e6a459dada2248ea"
        },
        "date": 1777058943341,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4763538,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2162020,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junjihashimoto@users.noreply.github.com",
            "name": "junji hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "2aea0922ae984f1b16af2e9a17ef7d97b9a79c62",
          "message": "Merge pull request #29 from Verilean/fix/tutorial\n\nAdd proofs for RV32",
          "timestamp": "2026-05-05T16:44:11+09:00",
          "tree_id": "d9c500480127c25a7f1ea554471eccddbb8116dd",
          "url": "https://github.com/Verilean/sparkle/commit/2aea0922ae984f1b16af2e9a17ef7d97b9a79c62"
        },
        "date": 1777967427499,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 5746350,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2517907,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "634d55b13042e15f2b296031bfb9156c17d47e74",
          "message": "declare_signal_state: generate Name.mk named-field constructor\n\nAdds a record-style constructor `Name.mk` to the\n`declare_signal_state` macro. For an n-field state declared as\n\n    declare_signal_state CounterParityOut\n      | count  : BitVec 8 := 0#8\n      | parity : Bool     := false\n\nthe macro now also emits\n\n    def CounterParityOut.mk {dom : DomainConfig}\n      : (count : Signal dom (BitVec 8)) →\n        (parity : Signal dom Bool) →\n        Signal dom CounterParityOut :=\n      fun count parity => bundle2 count parity\n\nso callers can build the output side by field name, mirroring how\nthey read it:\n\n    -- read by field name\n    let count := CounterParityOut.count self\n\n    -- write by field name (NEW)\n    CounterParityOut.mk (count := countOut) (parity := parityOut)\n\nBundle order comes from the macro, not from the call site, so a\nfield reorder in `declare_signal_state` cannot silently swap the\noutput data — Lean's named-argument resolution catches it.\n\nUpdates:\n\n  - `Sparkle/Core/StateMacro.lean`: append step 7 to the\n    macro's elaboration that emits `Name.mk` via a typed\n    function abstraction (no bracketedBinder syntax tricks).\n  - `tutorial-extended/TutorialExtended/Step2_MultipleOutputs.lean`:\n    add a 4th variant `counterAndParity_record_mk` demonstrating\n    the new pattern. The runDemo prints all 4 traces; they match.\n  - `tutorial-extended/TutorialExtended/Step2_VerilogDump.lean`:\n    `#synthesizeVerilog` the new variant; confirms the same\n    `_gen_countOut`/`_gen_parityOut` wires are produced.\n  - `docs/Tutorial_Extended.md`: new \"(d)\" section, updated\n    summary table.\n\nVerified:\n  - Full project build clean (64 jobs)\n  - All existing `declare_signal_state` invocations across\n    IP/RV32, IP/Bus, IP/Video, IP/YOLOv8, etc. continue to compile\n  - tutorial-extended-run prints identical traces for variants\n    (a), (b), (c), (d)\n  - Verilog output for (c) and (d) is structurally identical\n    (same wire names, same always_ff blocks, same bundle assign)",
          "timestamp": "2026-05-05T17:11:56+09:00",
          "tree_id": "f3320b83c4838e6ed3f5412134a5d242f492384d",
          "url": "https://github.com/Verilean/sparkle/commit/634d55b13042e15f2b296031bfb9156c17d47e74"
        },
        "date": 1777969329226,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4765563,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2147694,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "32f41e332ed170e21247ce1f6f8241aabad9e285",
          "message": "Tutorial.md: introduce declare_signal_state and Name.mk in Step 1\n\nAdd a \"Multi-output modules and declare_signal_state\" subsection\nright after the single-counter example, demonstrating:\n\n  - declare_signal_state field-list syntax\n  - read-by-name (CounterParityOut.count self)\n  - write-by-name (CounterParityOut.mk (count := ...) (parity := ...))\n  - the auto-generated default / wireNames / fromWires helpers\n\nA concrete `counterAndParity` example mirrors the anonymous-tuple\npattern but uses the record + Name.mk variant directly. Caller\nside also uses field-name accessors.\n\nForward-links to docs/Tutorial_Extended.md for the full\nwalkthrough (anonymous tuple → let-named → record + bundleAll!\n→ record + Name.mk) with trade-offs of each.\n\nBridges the gap between Tutorial.md's single-counter intro and\nTutorial_Extended.md's deeper module-composition material:\nreaders learn the named-record I/O pattern as soon as they need\nmore than one output, without having to hunt for the right\nchapter.",
          "timestamp": "2026-05-05T17:20:36+09:00",
          "tree_id": "6d05573aace61658debcc604969319048e3ff2e9",
          "url": "https://github.com/Verilean/sparkle/commit/32f41e332ed170e21247ce1f6f8241aabad9e285"
        },
        "date": 1777970057439,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4817525,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2159183,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junjihashimoto@users.noreply.github.com",
            "name": "junji hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "e46ab57c8e2b76a40020de57074666e1c58bb3f7",
          "message": "Merge pull request #30 from Verilean/feature/named-outputs\n\ndeclare_signal_state: generate Name.mk named-field constructor",
          "timestamp": "2026-05-05T17:35:27+09:00",
          "tree_id": "79db2a2a501c5a31266cfea81b5d641c4ccec2c5",
          "url": "https://github.com/Verilean/sparkle/commit/e46ab57c8e2b76a40020de57074666e1c58bb3f7"
        },
        "date": 1777970483641,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 7497591,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 3248227,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "a34600b42b0ee4288268a956e9245ecac6c305ce",
          "message": "Tutorial.md: introduce Signal.circuit do imperative HW DSL\n\nAdd a \"Imperative-style hardware: Signal.circuit do\" subsection\nright after the named-record I/O introduction in Step 1, with:\n\n  - Syntax overview (let x ← Signal.reg init, x <~ rhs, let y :=\n    rhs, return expr)\n  - Counter rewrite — same circuit as the canonical Step 1 example\n  - 3-stage shift pipeline as a multi-register example\n  - Note on when NOT to use it (need multiple named outputs →\n    Name.mk + Signal.loop is more flexible; Signal.circuit do\n    returns a single Signal)\n  - Forward link to the runnable example file\n\nNew runnable example:\n\n  - tutorial-extended/TutorialExtended/Step8_CircuitDoNotation.lean —\n    four worked examples (counter / up-down / 3-stage shift /\n    enabled counter) demonstrating both registered-state assignment\n    (`<~`) and combinational `let` bindings in the same do block.\n  - tutorial-extended/TutorialExtended/Run.lean — extended to\n    invoke Step 8's runDemo, which prints the four traces and\n    confirms (a) the counter increments, (b) up/down respects en,\n    (c) 3-stage shift introduces 3-cycle latency (input 0xAA at\n    cycle 1 emerges at cycle 4), (d) enabled counter only ticks\n    on the cycles when en is true.\n\nThe macro desugars to Signal.loop + Signal.register + bundleAll!\nover the next-state expressions, so synthesis output, JIT codegen,\nand Signal.atTime evaluation are identical to the hand-written\nversion. Verified by `lake build` (64 jobs clean) and\n`lake exe tutorial-extended-run` (Step 8 traces match expected\noutput).",
          "timestamp": "2026-05-05T17:33:02+09:00",
          "tree_id": "79db2a2a501c5a31266cfea81b5d641c4ccec2c5",
          "url": "https://github.com/Verilean/sparkle/commit/a34600b42b0ee4288268a956e9245ecac6c305ce"
        },
        "date": 1777970507878,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 5724478,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2515727,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "ee8a7e9081c12eac0653578ca4ea30d40cd70e0c",
          "message": "Add .claude/ to .gitignore (Claude Code working dir)\n\nRemoves the accidentally-committed `.claude/scheduled_tasks.lock`\nand prevents future commits from picking up Claude Code's\nlocal working state.",
          "timestamp": "2026-05-08T13:43:54+09:00",
          "tree_id": "a6ae3cae493812d83f165c9bd90b970a376a48bd",
          "url": "https://github.com/Verilean/sparkle/commit/ee8a7e9081c12eac0653578ca4ea30d40cd70e0c"
        },
        "date": 1778216462366,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 5810053,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2512520,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junjihashimoto@users.noreply.github.com",
            "name": "junji hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "6e9fd99fd9261e19fd53ddabdd6bb87710a78f79",
          "message": "Merge pull request #31 from xiangze/FPU\n\nFPU with proofs",
          "timestamp": "2026-05-09T13:47:58+09:00",
          "tree_id": "31fb81df206f8438dc1464858a7508d1ea73ad23",
          "url": "https://github.com/Verilean/sparkle/commit/6e9fd99fd9261e19fd53ddabdd6bb87710a78f79"
        },
        "date": 1778302487666,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4574623,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2155500,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junjihashimoto@users.noreply.github.com",
            "name": "junji hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "41333d2b8fc6d756fcaffd1b939f7b30c8ea4a5c",
          "message": "Merge pull request #27 from xiangze/slice_operator_comma\n\ndefine and prove bit slice operatror v[hi,lo]",
          "timestamp": "2026-05-09T13:50:20+09:00",
          "tree_id": "07dc69b7ca76c85c3666b2b168667f186b756c19",
          "url": "https://github.com/Verilean/sparkle/commit/41333d2b8fc6d756fcaffd1b939f7b30c8ea4a5c"
        },
        "date": 1778302630806,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4825204,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2161028,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "9d1cb48c28dc2d658f05017c02290165daf85702",
          "message": ".dockerignore: refresh comments to match the current Dockerfile\n\nThe header explained the file as protection against a blanket\n`COPY . /workspace/sparkle` that the tutorial Dockerfile used\nto do.  That `COPY .` was replaced months ago with a hand-picked\nlist of directories (`Sparkle/`, `c_src/`, `lakefile.toml`,\ndocs/tutorial/, tutorial-extended/, …), so the entries below\nare now defence-in-depth rather than load-bearing.\n\nJust rewrite the comment block to say so; no entries\nadded/removed.",
          "timestamp": "2026-05-12T06:33:50+09:00",
          "tree_id": "ae97298253e9c8e925c12f31c04fd632972bbcef",
          "url": "https://github.com/Verilean/sparkle/commit/9d1cb48c28dc2d658f05017c02290165daf85702"
        },
        "date": 1778536996840,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4836895,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2168118,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "junji.hashimoto@gree.net",
            "name": "Junji Hashimoto",
            "username": "junjihashimoto"
          },
          "distinct": true,
          "id": "670c8de6e3ba3759f8d42e2d3746a46eeca4a302",
          "message": ".dockerignore: refresh comments to match the current Dockerfile\n\nThe header explained the file as protection against a blanket\n`COPY . /workspace/sparkle` that the tutorial Dockerfile used\nto do.  That `COPY .` was replaced months ago with a hand-picked\nlist of directories (`Sparkle/`, `c_src/`, `lakefile.toml`,\ndocs/tutorial/, tutorial-extended/, …), so the entries below\nare now defence-in-depth rather than load-bearing.\n\nJust rewrite the comment block to say so; no entries\nadded/removed.",
          "timestamp": "2026-05-12T08:34:00+09:00",
          "tree_id": "82445a88dadf1b6ddac84c68315596821b552612",
          "url": "https://github.com/Verilean/sparkle/commit/670c8de6e3ba3759f8d42e2d3746a46eeca4a302"
        },
        "date": 1778542870899,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 5748588,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2513272,
            "unit": "cycles/sec"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "junjihashimoto@users.noreply.github.com",
            "name": "junji hashimoto",
            "username": "junjihashimoto"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "1d51cb0d20de0a7bc8a573f4b30bd975371ede4e",
          "message": "Merge pull request #32 from Verilean/feature/notebook\n\nFeature/notebook",
          "timestamp": "2026-05-12T09:02:08+09:00",
          "tree_id": "4984953fc994bbcd491ac3da12d9dbcc91774301",
          "url": "https://github.com/Verilean/sparkle/commit/1d51cb0d20de0a7bc8a573f4b30bd975371ede4e"
        },
        "date": 1778544521499,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "LiteX Verilator (10M cycles)",
            "value": 4822589,
            "unit": "cycles/sec"
          },
          {
            "name": "LiteX JIT evalTick (10M cycles)",
            "value": 2160632,
            "unit": "cycles/sec"
          }
        ]
      }
    ]
  }
}