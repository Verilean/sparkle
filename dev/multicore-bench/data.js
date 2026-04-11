window.BENCHMARK_DATA = {
  "lastUpdate": 1775866271794,
  "repoUrl": "https://github.com/Verilean/sparkle",
  "entries": {
    "Multi-Core Benchmark (8-core LiteX PicoRV32)": [
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
        "date": 1775662753181,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "JIT 1-core single-thread",
            "value": 4513503,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT 8-core sequential",
            "value": 560062,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT 8-core parallel (batch=10K)",
            "value": 1129492,
            "unit": "cycles/sec"
          },
          {
            "name": "Verilator 8-core",
            "value": 692857,
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
        "date": 1775674244052,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "JIT 1-core single-thread",
            "value": 4051150,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT 8-core sequential",
            "value": 491195,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT 8-core parallel (batch=10K)",
            "value": 1009853,
            "unit": "cycles/sec"
          },
          {
            "name": "Verilator 8-core",
            "value": 643492,
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
        "date": 1775675048995,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "JIT 1-core single-thread",
            "value": 4055955,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT 8-core sequential",
            "value": 501013,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT 8-core parallel (batch=10K)",
            "value": 1012483,
            "unit": "cycles/sec"
          },
          {
            "name": "Verilator 8-core",
            "value": 647875,
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
        "date": 1775676179084,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "JIT 1-core single-thread",
            "value": 4042875,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT 8-core sequential",
            "value": 501555,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT 8-core parallel (batch=10K)",
            "value": 1011235,
            "unit": "cycles/sec"
          },
          {
            "name": "Verilator 8-core",
            "value": 646589,
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
        "date": 1775676255513,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "JIT 1-core single-thread",
            "value": 4517161,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT 8-core sequential",
            "value": 551696,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT 8-core parallel (batch=10K)",
            "value": 1122305,
            "unit": "cycles/sec"
          },
          {
            "name": "Verilator 8-core",
            "value": 689881,
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
        "date": 1775866271327,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "JIT 1-core single-thread",
            "value": 4051718,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT 8-core sequential",
            "value": 500635,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT 8-core parallel (batch=10K)",
            "value": 1009490,
            "unit": "cycles/sec"
          },
          {
            "name": "Verilator 8-core",
            "value": 644918,
            "unit": "cycles/sec"
          }
        ]
      }
    ]
  }
}