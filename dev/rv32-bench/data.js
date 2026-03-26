window.BENCHMARK_DATA = {
  "lastUpdate": 1774495790025,
  "repoUrl": "https://github.com/Verilean/sparkle",
  "entries": {
    "RV32 SoC Simulation Benchmark (Verilator vs JIT)": [
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
          "id": "013443ba59c63ef7a13f40270d2db4230cbb4a0e",
          "message": "ci: preserve benchmark JSON across git stash",
          "timestamp": "2026-03-26T12:24:42+09:00",
          "tree_id": "2c4e9dd57e4df348ac816af39b6d0bb5e2192a7f",
          "url": "https://github.com/Verilean/sparkle/commit/013443ba59c63ef7a13f40270d2db4230cbb4a0e"
        },
        "date": 1774495789741,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "Verilator (10M cycles)",
            "value": 3285506,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT eval+tick (10M cycles)",
            "value": 4856146,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT evalTick fused (10M cycles)",
            "value": 5465489,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT evalTick+6wires (10M cycles)",
            "value": 4968426,
            "unit": "cycles/sec"
          }
        ]
      }
    ]
  }
}