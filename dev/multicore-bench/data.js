window.BENCHMARK_DATA = {
  "lastUpdate": 1775674244714,
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
      }
    ]
  }
}