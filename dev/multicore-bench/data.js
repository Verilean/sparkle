window.BENCHMARK_DATA = {
  "lastUpdate": 1775662753538,
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
      }
    ]
  }
}