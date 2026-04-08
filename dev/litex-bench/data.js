window.BENCHMARK_DATA = {
  "lastUpdate": 1775661012077,
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
      }
    ]
  }
}