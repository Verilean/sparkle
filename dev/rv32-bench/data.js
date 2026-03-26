window.BENCHMARK_DATA = {
  "lastUpdate": 1774495850362,
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
          "id": "e1c53641a220e3c602c86ab73517f8ed8ea92f93",
          "message": "Merge pull request #14 from Verilean/feature/rv32\n\nci: preserve benchmark JSON across git stash",
          "timestamp": "2026-03-26T12:25:40+09:00",
          "tree_id": "2c4e9dd57e4df348ac816af39b6d0bb5e2192a7f",
          "url": "https://github.com/Verilean/sparkle/commit/e1c53641a220e3c602c86ab73517f8ed8ea92f93"
        },
        "date": 1774495849619,
        "tool": "customBiggerIsBetter",
        "benches": [
          {
            "name": "Verilator (10M cycles)",
            "value": 3280838,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT eval+tick (10M cycles)",
            "value": 4946544,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT evalTick fused (10M cycles)",
            "value": 5469307,
            "unit": "cycles/sec"
          },
          {
            "name": "JIT evalTick+6wires (10M cycles)",
            "value": 4978734,
            "unit": "cycles/sec"
          }
        ]
      }
    ]
  }
}