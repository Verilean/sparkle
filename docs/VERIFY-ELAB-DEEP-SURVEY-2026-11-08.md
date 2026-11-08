# verify_elab_deep 拡張の調査（2026-11-08）

読み取りだけの調査で、何も build していない。base: par/fgc-retro 7423e4e1。必要 IP の一覧は par/fgc-s0（および par/fgc-s1q-cmpnew、同一）の `scripts/gen5/fgc_baseline/inventory.tsv`、定義は `docs/FG-CIRCUIT-BASELINE.md` の「必要IPの定義」。327 コマンドそれぞれの分類（TSV）はこのコミットには入れていない（測定データをソースツリーに置かない）。


対象: worktree `/home/junji-hashimoto/git/.kjob/src-fgc-retro`（branch par/fgc-retro, HEAD 0ac77362）。ビルド・lake・lean は実行していない。数値は、ファイル・git 履歴・保存済みの Job 出力から読んだ値だけを書いた。記録がないものは「不明」と書いた。

付属: 必要IP 327 件の行ごとの分類（下の C 節）は coder の作業領域に置いた（ソースツリーには入れていない）。再現には inventory.tsv と下の分類規則を使う。

---

## A. 必要IPの固定一覧

### 結論
- **定義している文書**: `docs/FG-CIRCUIT-BASELINE.md`（branch `par/fgc-s0`、最新 f694355f）。「必要IPの定義」の節に「必要IP = P1 の全コマンドから、`exclusions.tsv` の行を引いたもの」とあり、除外は 0 件。
- **一覧そのもの**: `scripts/gen5/fgc_baseline/inventory.tsv`（同じ branch）。**327 コマンド**（ヘッダを除く行数。`#synthesizeVerilog` 301、`#writeDesign` 16、`#synthesizeParameterizedVerilog` 4、`#synthesizeVerilogDesign` 4、`#writeVerilogDesign` 2）、136 ファイル。層 A（出荷 IP: `IP/**` `Examples/**` `Tests/IP/**`）225、層 B（機能・回帰の `Tests/**`）102。
- **置き場所の注意**: この一覧と BASELINE.md は、**この worktree にも poc/roundtrip-proof にも無い**（`git ls-tree` で 0 件）。あるのは `par/fgc-s0` と `par/fgc-s1q-cmpnew` で、両者の inventory.tsv は同一（diff なし）。FG-CIRCUIT-PILOT.md:113 にも「`docs/FG-CIRCUIT-BASELINE.md` は par/fgc-s0 5fe31f83 にあり、この worktree には無い」と書かれている。
- **動的な結果**: 327/327 が合成成功（OK 309、OK-nostdout 18）、除外 0、未説明 0（Job kjob-run-src-fgc-s0run-0474、土台 46874da9）。生データは `~/git/.kjob-state/namespaces/sparkle-dev/kjob-run-src-fgc-s0run-0474/fgc_baseline_raw/`（`baseline_commands.tsv`、`baseline_modules.tsv`、`out/*.txt`）。出力ファイル 18 件の hash は `output_baseline.tsv`（kjob-run-src-fgc-s0d-4c68）。
- 戦略文書 `docs/FG-CIRCUIT-STRATEGY-2026-11-06.md`:28/79 が「必要IP一覧と baseline を記録する」を S0 の作業とし、その S0 の成果が上の文書。振り返り `docs/FG-RETROSPECTIVE-2026-11-08.md`:106 の完了条件 (2)「必要IPの固定一覧」もこれを指していると読める（振り返りは一覧のパスを書いていない）。

### ほかの候補（必要IPとは呼ばれていないもの）
BASELINE.md の「母集団の区別」の表が、次のものを同一視しないと明記している。

| 候補 | 件数 | 出所 | 扱い |
|---|---|---|---|
| P1 = inventory.tsv | 327 | 上記 | **必要IP（固定）** |
| P2: API を直接呼ぶファイル | 372 ファイル / 1875 呼び出し | files.tsv | 必要IPに入れない |
| P3: 「235 root」 | 235 | D.D-4 e37da005 の測定。一覧はリポジトリに無い | 同一視しない |
| P4: 「以前の 1369 成功コンパイル」 | 1369 | 一覧はリポジトリに無い | 同一視しない |
| `scripts/shipping-coverage/run.sh` の「391 real declarations」（gold53） | 391 | 動的な測定（子の宣言も数える）。docs/ShippingCompiler-Milestones.md:34、TrustBase.md:1702。宣言の一覧は commit されていない | 経路の測定。必要IPとは呼ばれていない |

---

## B. `#verify_elab_deep` が今扱う範囲

`Tools/DeepElab.lean`（5,569 行。最終変更 df5f0b09、2026-09-24）。

### B1. 文法
- `CExpr Γ w`（46–66 行）: `const`（非負の Nat）, `var`, `add`, `sub`, `mux`, `eq`, `and`, `or`, `xor`, `mul`, `shl`, `shr`, `lt`, `le`, `cat`, `slt`, `sle`, `slice`, `not`, `neg`。意味は `CExpr.denote`（73 行、BitVec の値）。`CExpr.compile`（98 行）は IR の `Expr` へ。演算子ごとの `CExpr.compile_correct`（199 行）が `evalExpr (weOfC …) (envOfC …) (compile e) = some (denote e).toNat` の形。
- 逆向きの読み取り `toCExpr`（1500 行）は IR の `gt_u/ge_u/gt_s/ge_s` を lt/le の左右入れ替えで、n 引数の `concat` を右に入れ子の `cat` で受ける。**文法の外**: IR 演算子 `asr`、`Expr.sliceDim`、`Expr.index`、負の定数（"negative const"）。1562–1564 行で `throwError "… operator {o}/{n} outside the deep grammar"` / `"{repr e} outside the deep grammar"`。
- `Cdo Γr Γi wOut`（323 行）: レジスタの初期値、レジスタごとの次状態式 1 本、出力式 1 本。
- `CdoM`（714 行）: `Signal.memory` 由来の同期メモリ（書き込みポート 1 本、読み出しラッチ）と組合せ読み出し（`Γc`）。複数ポートは 1811 行で拒否（"multi-port memories are outside the deep grammar"）。組合せ読み出しのアドレスが別の組合せ読み出しを読むものは 1882 行で拒否。
- `CdoW Γr Γi Γw`（1049 行）: 共有 wire の層（cone の共有）。`set_option sparkle.deepShare true`（1331 行）か `SPARKLE_DEEP_SHARE=1` のときだけ使う。この経路（v1）は、メモリ、複数出力ポート、Bool 出力、入れ子の loop を拒否する（2448–2455 行）。
- 一般定理: `Cdo.elab_general`（582 行）、`CdoM.elab_general`（832 行）、`CdoW.elab_general`（1230 行）。中身は「deep 値の Signal 出力 = deep 値を `CExpr.compile` したもの を `evalExpr` で評価した値」で、**比べる IR は deep 値自身の compile であり、コンパイラの IR ではない**。

### B2. 経路の選択
3621 行: `if (← IO.getEnv "SPARKLE_DEEP_SHARE").isSome || sparkle.deepShare.get (← getOptions) then sharedRoute (); return`。それ以外は既定の経路（ポートごとに `Cdo`、メモリがあれば `CdoM`）。自動の選択はしない。

### B3. 単一モジュールの制限
1790–1796 行:
```lean
  let design ← liftTermElabM
    (Sparkle.Compiler.Elab.synthesizeHierarchical declName)
  ...
  let m ← match design.modules with
    | [m] => pure m
    | _ => throwError "#verify_elab_deep: single-module designs only"
```
ほかに入口で拒否するもの: レジスタ 0 個（1835 行 `"#verify_elab_deep: no registers"`、同期メモリのラッチも数える）、出力 0 個（1890 行）、依存型の引数（1937 行）、top の `runCircuitH` が見つからない（2384 行 "register types / initial values must be closed literals"）、IR のレジスタの組と DSL のレジスタが合わない（2401 行）。

### B4. `circuit do` から Cdo への reify（E3）の状態
- 1025–1031 行の説明どおり、reify は**ソースの構文ではなく、コンパイラが作った IR の cone を読み戻す**メタプログラム。`inlineConeT`（レジスタ・入力・組合せ読み出しで止める）→ `resolveSlicesT` → `toCExpr`（1857–1897 行）。
- ソース（Signal）との接続は宣言ごとに生成する証明（`{f}_deep_trace`。`signal_lets`、展開、`bv_decide` などで閉じる。4262 行に `bv_decide` の closer）。kernel が検査するが、reify そのものの全域性・正しさの定理はない。
- docs/CertifiedRoundtrip-TODO.md:3477 の F1 は「Stage 1 CLOSED: reflection は kernel が検証、corpus 測定で監視」とし、reify を全域の定理にする Stage 3 は未着手。

### B5. 「fidelity by unfolding」が示すこと
既定経路で、ポート 0 のときにレジスタごと・出力ごとに生成する（3690–3790 行）。メモリなしの形（3731–3739 行の生成文）:
```lean
theorem {f}_deep_fidelity_r{i} :
  CExpr.compile {f}_nm (Cdo.next {f}_deep ⟨i, _⟩) = <concatNorm 10000 (inlineConeT/resolveSlicesT 後の IR cone) の repr を構文として読み戻した項>
theorem {f}_deep_fidelity_out :
  CExpr.compile {f}_nm (Cdo.out {f}_deep) = <同じく出力 cone>
```
証明は `simp only [nextEq, CExpr.compile, nm]` と `rfl`。つまり「reify した値を compile すると、メタ側で inline・正規化した IR cone の**構文**に戻る」という等式で、右辺は `repr` を構文として読み戻した項（`quoteIR`、2403 行）。cone を作った `inlineConeT` と実際のモジュール本体の関係は、続く G1 補題（`mkG1`、3846 行。`inlineConeT (buildDefMap bodyC) … = .ok coneRaw` と `resolveSlicesT` を `native_decide` で示す）と、IR の replay で付ける:
```lean
theorem {f}_deep_signal_run (inputs…) (K : Nat) :
  ∃ envs, Sparkle.IR.Semantics.runModule {f}_deep_weM {f}_deep_body
            (fun td s => envSt … (K - 1 - td) s) K st0 (fun _ _ => 0) = some envs
    ∧ ∀ t, t < K → ∃ env1, envs[t]? = some env1 ∧ ((f inputs…).val t).toNat = env1 "port"
```
（生成文は 5497 行、メモリありは 5436 行）。`{f}_deep_body` は `deepOrderBody m.body`（3902 行）で、**返されたモジュール本体の並べ替え**（同期メモリ先頭、組合せ部分を Kahn 順、最後にレジスタ）。この並べ替えと元の `m.body` の run が等しいという定理は見つからなかった。replay は `bridgeOk` が偽なら省かれ、その場合も成功を報告する（5538 行の logInfo "IR replay skipped …"、エラーではない）。

### B6. どの宣言で実行され、結果はどう記録されているか
| ファイル | 対象 | 記録された結果 |
|---|---|---|
| Tests/Verification/DeepElabReifyDemo.lean | cnt8 ほか 20 のデモ（入れ子、値引数の wrapper、メモリ 3 件を含む） | ci_check.sh:225–243 が PROVEN 行 21 以上を要求。docs/CertifiedRoundtrip-TODO.md:2185「Default route unchanged (43 PROVEN across RealIP / ValueParamInit / ReifyDemo)」（2026-09-14） |
| Tests/Verification/DeepElabRealIP.lean | crc32Engine, uartTxHW, EcdsaSignSmall.regFile, DroneCANHW.transferIdTrackerHW, SBUSHW.frameAccumulatorHW, SPIHW.spiMasterHW | ci_check.sh:245–262 が PROVEN 行 17 以上（ポート数）。ファイル冒頭の説明が拒否の境界を記録: closedLoopCircuit は定義段階で timeout、crc16CcittHW は既定経路で cone 16.25M 文字・1500 秒で未完、kvHw は 15 arm を超えると Fin の match が通らない |
| Tests/Verification/ValueParamInitRepro.lean | accK9 ほか 5 | ci_check.sh:296–318、RefusalLedger.md:107（`_deep_trace` は標準 axiom のみ、`_deep_signal_run` は native_decide の補助 axiom 23 個（initCirc7）） |
| ConeSharingGen.lean / ConeSharingCrc16.lean | shareX4, shareX8 / crc16CcittHW（shared 経路） | docs/SharedRoute-Guarantees.md §6 の表（2026-09-20/22）: 3 本とも trace・replay・Opt・RT は PROVEN、crc16 の SV 順方向は SKIPPED（shl の幅規則）。crc16 は 93 秒 / 1.98 GB |
| ConeSharingProto / Replay / Premises、ConeKernelSlot* | 手書きの試作 | ci_check.sh:324–419 |

- これらのテストは `Tests/AllTests.lean` にも lakefile の lean_lib にも入っていない（lakefile.lean:320 は `Tools.DeepElab` だけ）。実行は `bench/xiangshan/ci_check.sh` から。
- **今の HEAD での結果は不明**。DeepElab.lean とテストの最終変更は 2026-09-24 で、その後に合成側で次の変更が入った: 印字前の `checkedOptimize`（9d0abaca、2026-09-25）、メモリを子モジュールにする方針（2026-10-06 のユーザー決定。baseline の SV では `SparkleMem_*` のインスタンスになっている）、`synthesizeEntry`/Off 入口（3d5ed1bf、2026-11-06）。この期間の実行記録は見つからなかった（`.kjob-state` の全文検索は大きすぎて途中で打ち切った）。メモリを持つ regFile / memAcc / memTwo / comboAcc については、メモリがインスタンスになっていれば B3 の単一モジュール検査で拒否されるはずだが、実測はない。
- **必要IP 327 件との重なり**: 上の宣言は inventory.tsv に**1 つも入っていない**。inventory にあるのは wrapper の `crc32EngineTop`（Tests/IP/Net/CRC32Test.lean:27、`crc32Engine` を呼ぶだけ）と `synth_uartTx`（Tests/IP/Net/UARTTest.lean:122、`(uartTxHW …).txLine`）で、これらに対する `#verify_elab_deep` の実行記録はない。

### B7. コンパイラが返す／印字するものと同じものを検査しているか
**していない。** 違いは 3 つ。
1. **入口が違う**。`#verify_elab_deep` は `Sparkle.Compiler.Elab.synthesizeHierarchical declName` を呼ぶ（DeepElab.lean:1791）。これは `synthesizeCombinational`（診断入口、`SPARKLE_PROFILE` を読む）に `validateDesignNames` を足したもの（Elab.lean:9470–9473）。一方 `#synthesizeVerilog` は `synthesizeEntry`（Elab.lean:9205–9208）を通り、`SPARKLE_PROFILE` が無ければ `synthesizeCombinationalOff` を使う。2 つの入口が同じ出力を出すことは、FG-CIRCUIT-PILOT.md §21.5–21.7 の出力比較（5 root で 1312 行が一致、baseline で 272/272 がバイト一致）で観測されているだけで、定理はない（§21.5 は「同一性の定理は置かない」と明記）。
2. **コマンドが別**。`#verify_elab_deep` は自分の中で合成をやり直す。印字コマンドの実行結果を受け取るのではない。
3. **段が違う**。`#synthesizeVerilog` が印字するのは `toVerilog (checkedOptimize module)`（Elab.lean:9323–9324、9361）。既定経路の deep の定理は最適化前の `m` についてで、しかも並べ替えた本体（B5）。shared 経路の Opt/RT の橋は `Sparkle.IR.Optimize.optimizeModule m`（DeepElab.lean:3564）と `toVerilog mo`（3569）についてで、`checkedOptimize m` ではない（`checkedOptimize` は検査に落ちると `m` を返す。RefineCheck.lean:387–405）。SharedRoute-Guarantees.md §3 の「印字されるのは `optimizeModule m`」は 2026-09-14 時点の記述で、9d0abaca 以降は事実と合わない。`#synthesizeVerilogDesign`/`#writeVerilogDesign` は `toVerilogDesignChecked`（top だけ `checkedOptimize`、VerilogDesign.lean:25–32）。

参考: FG の検査付き入口 `certifiedEntryC`（S3yEntry.lean:29）も、検査するのは `synthesizeCombinationalCoreOff` の `(b, D)` で、印字される `checkedOptimize (mergeChecked (dropZeroWidthModule b))`（Elab.lean:9188–9198 の後処理の後）ではない。

### B8. axiom と決定手続きへの依存
- **shared 経路**: 監査がある（3598–3620 行）。各定理について `collectAxioms` を取り、`sorryAx` があれば失敗。許すのは `propext`/`Classical.choice`/`Quot.sound` と、`Lean.ofReduceBool`、名前が `…._native.native_decide.ax_*` / `…._native.bv_decide.ax_*` の形のものだけで、ほかは `throwError`。PROVEN 行は `"… IR replay {id} PROVEN (axioms: standard + {nAux} decision-procedure auxiliaries)"`（3620 行）で、`nAux` はその許可された補助 axiom の数。記録: replay/Opt/RT は trace の `bv_decide` 補助 1–2 個、`_text_parses` は native_decide 1 個（parser を評価する oracle）、`_signal_svOpt` はさらに `seqCheck` の native_decide 1 個（SharedRoute-Guarantees.md §6–7）。
- **既定経路**: 監査は `sorryAx` と metavariable だけ（5541–5554 行）。**許可 axiom の集合を検査していない**のに、PROVEN 行は "axioms clean" と出す（5558/5560 行）。実際には G1 補題が `native_decide` を使い（3863–3872 行ほか）、replay は `Lean.ofReduceBool` に依存する（RefusalLedger.md:107 の訂正記録: initCirc7 で 23 個）。trace も `bv_decide` を使いうる。許可集合の検査は ValueParamInitRepro.lean の `run_cmd` と `Tools/CertifyShared.lean:19–37`（`#certify_shared_roundtrip` / `#seal_shared_roundtrip`、shared 経路だけ）にある。

---

## C. 必要IPごとの不足（327 件 > 60 なので機能ごとにまとめる）

### 分類の方法と限界
- 使ったのは S0 baseline の生データ（Job 0474）: `baseline_commands.tsv` の module 列で `baseline_modules.tsv`（印字された top モジュールの SV から取った静的な値: ポート数、レジスタ数、インスタンス数）と結合した。インスタンスは SV のインスタンス行を数え、309 件すべてで `n_inst` と一致した。子のモジュール名が `SparkleMem_` で始まるものを「メモリの子」とした。
- 値は**最適化後に印字された SV** から取った。deep が見るのは最適化前の IR なので、レジスタ数などは近似。
- 印字された top 309 件の SV には `>>>`（asr）も `$signed` も 0 件。`sliceDim`/`index`/負の定数は SV からは判定できない（不明）。
- baseline_modules.tsv の `mems` 列は 309 件すべて空（メモリは子モジュールのインスタンスとして出るため）。
- 「今日受理するか」は、327 件どれにも**実行記録がない**ので、すべて「不明」とした。参考として、B3 の入口検査のコードから読める見込みを別の列に書いた。これは観測ではない。

| 群 | 件数（層A/層B） | 例 | 階層 | 状態 | メモリ | 複数出力 | CExpr 外の演算子 | その他の構文 | 既知の性能問題 | 今日受理するか（記録） | コードから読める見込み（観測ではない） |
|---|---|---|---|---|---|---|---|---|---|---|---|
| S: 平坦、レジスタあり、インスタンスなし | 179（149/30） | arbiterSignal, axi4LiteMaster, clintSignal, dividerSignal, mmuTopSignal, `Tests/IP/**` の `synth_*` 128 件 | なし | あり（SV のレジスタ数 1–37） | なし | n_out>1 は 4 件（pairCounterCdo, pairRecordCdo, synth_rxFramerAll 6, synth_txFramerAll 4）。ほかは 1 ポート | SV では観測されない | wrapper・struct の射影（`synth_uartTx` など）。runCircuitH を見つけられるかは不明 | 状態スロット（レジスタ+データ入力）が 15 を超えるもの 23 件（RealIP.lean に記録された kvHw の Fin の match の上限。今も効くかは不明）。cone の大きさ（crc16 の型）は既定経路で未完 | 不明（0 件記録） | 入口検査は通りうる。cone の形・性能・射影は未測定 |
| C: 平坦、組合せ（レジスタ 0） | 82（22/60） | adder16, aluSignal, busDecoderSignal, decoderFieldsSignal, `Tests/Synthesis/**` 25 | なし | なし | なし | 0 件 | SV では観測されない | `circuit do` でない定義が多いと見られる（runCircuitH の要件） | 不明 | 不明 | 1835 行 "no registers" で拒否 |
| H: メモリ以外の子インスタンスあり | 40（37/3） | synth_aesSbox, mesh2x2, baselineKvHw1Reg, synth_hftPcieOutByte, synth_signCore, synth_sha512Block_out0, synth_usbWebServer | あり | 0–30 | 一部の子に含まれうる（不明） | 0 件 | 不明 | 子の呼び出し | 不明 | 不明 | 1796 行 "single-module designs only" で拒否（子が design に入る場合） |
| M: メモリの子だけ | 4（2/2） | rv32iCore（レジスタ 44）, activationDoubleBuffer, withMemory, synth_loop_bram | `SparkleMem_*` の子 | 0–44 | あり（子モジュール） | 0 件 | 不明 | — | rv32iCore は 44 レジスタ | 不明 | 1796 行で拒否（CdoM はインライン `.memory` 用で、子インスタンスを扱わない） |
| D: 設計・ファイル出力のコマンド（top の行なし） | 18（15/3） | H.264 の 12 件（cavlcSynthModule など）, rv32iSoCSynth, domainA/BCounter, latch8x2 | 保存 SV で 1–9 モジュール | あり | H.264 と SoC はあり（保存 SV にメモリ配列 2–11） | 不明 | SoC の SV に `>>>` 2 件・`signed` 7 件 | `#writeDesign` / `#writeVerilogDesign` の出力形（JIT/cppsim を含む） | H.264 の 3 件はシミュレーションで既存の不具合（JIT の wire が無い） | 不明 | 多くは複数モジュールで 1796 行で拒否。1 モジュールの 5 件（domainA/B, nal_stream, snDup, latch8x2）は不明 |
| P: パラメータ付き | 4（0/4） | symbolicXor, symbolicConcat, symbolicSliceLow, symbolicZeroExtend | なし | 不明 | なし | 不明 | `sliceDim` などの記号幅の可能性 | `#synthesizeParameterizedVerilog` は別の入口（`synthesizeCombinationalWithParameters`） | 不明 | 不明 | `#verify_elab_deep` は具体化した宣言しか取らない（引数は ident 1 つ）。対象外 |

合計 179+82+40+4+18+4 = 327。

---

## D. 一時停止中の FG 作業から再利用できるもの

判定の基準: 型と意味が DeepElab（`CExpr.denote`、`evalExpr`、`Cdo.irState`、`runModule`）と合っているか。帰納の形が似ているだけのものは再利用に数えない。

| 名前 | 場所 | 型・意味 | DeepElab との一致 |
|---|---|---|---|
| `checkComb_sound` | Tools/ShippingFGCircuitS3tComb.lean:391（検査器 `checkComb` は 361 行、`CTerm` は 15 行） | `CTerm`（var/lit/eq/mux/slice/cat の 6 個。Nat の値 `den`、型の幅を持たない）について、`checkComb s m` が真なら `evalAssigns (declWidth m) mems m.body env` が成功し、出力ポートが `c.den V` | **一致しない**。項は型なしの Nat で演算子は 6 個（CExpr は BitVec で 20 個）。意味は `evalAssigns (declWidth m)` で本体全体を見る（DeepElab は `weOfC`/`weM` で cone を評価）。「返されたモジュール本体そのものを Bool で検査する」という方式は組合せ群（C）の参考になるが、そのままは使えない |
| `ofData_sound` | Tools/ShippingFGCircuitS3vBridge.lean:283 | `MachineData` と `Frag`、状態なし（`hss : d.ss.length = 0`）。`Term.eval` から `CTerm` への関係 `Rel` | **一致しない**（ソースが `MachineData` で、Signal/Cdo ではない） |
| `checkData_sound` | Tools/ShippingFGCircuitS3yGen.lean:138（`checkData` 64 行、`DataShows` 31 行） | `DataShows d m := ∀ x, ChildFn m (childRange d) (dataValue d x)`。1 出力、状態なし | **一致しない**。`ChildFn` は `evalAssigns (declWidth mc)`（Sparkle.IR.Semantics の同じ関数）なので IR 側の意味は共通だが、幅環境（`declWidth` と `weM`）とソース側（`MachineData`）が違う |
| `certifiedEntryC_sound` | Tools/ShippingFGCircuitS3yEntry.lean:48（入口 29 行、拒否 `certifiedEntryC_refuses` はその直後） | MetaM の run の成功 `RunsTo (certifiedEntryC …) … (b, D) w'` から「同じ run が読んだ d」「同じ run が返した (b, D)」「`checkData d b ∧ designOk b D`」を出す | 定理そのものは**一致しない**（Bool の `checkData` 前提。DeepElab の検査は生成した kernel 証明で、Bool 関数ではない）。部品の `RunsTo.bind`（Tools/ShippingEntrySoundness.lean:946）、`RunsTo.throwError_false`（957）、`runsTo_pure`（S3yEntry.lean:41）は型がそのまま使える。完了条件 (1)「検証したものだけを返す」の形の雛形にはなる。ただし B7 のとおり `synthesizeCombinationalCoreOff` の出力を検査しており、印字される成果物ではない |
| `designOk` | Tools/ShippingFGCircuitS3tSpec.lean:71 | `Module`/`Design` の Bool: top 名、モジュール名が重複しない、子が top と同名でない | **型は一致**（IR AST の `Module`/`Design`）。階層に広げるときの設計表の前提としてそのまま使える |
| `topInOk` | Tools/ShippingFGCircuitS3tSpec.lean:66 | `MixedGateBinder` と FG のポート名の約束 | 一部だけ（FG の binder 表現に依存） |
| IR 意味論の補題 | `optCheck_sound`（Tools/ShippingOptSoundness.lean:248）、`refineCheck_transfer`（Tools/ShippingRefineSoundness.lean:1039）、`refineCheck_transfer_noReg`（Tools/ShippingRefineNoRst.lean:224）、`checkedOptimize_seqOk`（Sparkle/IR/RefineCheck.lean:405）。DeepElab が既に使うもの: `concatNorm_eval`（ConeFoldSlices.lean:1934）、`evalExpr_we_congr`（1720）、`inlineConeT_refs`（1225）、`runModule_stepIter`（2133）、`evalExpr_bounded`（ConeFoldMem.lean:950）、`evalAssigns_bounded`（1020）、`rtBridgeK_eval`（ConeFoldRT.lean:1243）、`certified_forward_trace_module`（SVParser/EmitSem.lean:4651） | `refineCheck_transfer`: `runModule (declWidth m) m.body (seedIn m ins) k stM mems = some envs → ∃ envsO, runModule (declWidth o) o.body … ∧ 出力が等しい` | `runModule`/`evalAssigns` は**同じ関数**（Sparkle.IR.Semantics）。ただし DeepElab の `signal_run` とは、幅環境（`weM` と `declWidth m`）、本体の順序（`deepOrderBody m.body` と `m.body`）、seed（生成した `envSt` と `seedIn m ins`）が違う。そろえる補題（幅の一致、並べ替えでの run の不変、seed の一致）を足せば、最適化段（checkedOptimize）の接続に使える見込み。今は**未接続** |
| 階層: `runModuleH` / `runModuleH_of_open` | Tools/ShippingMachineLinked.lean:283 / 294（`ChildComputes` 25 行） | 子をつないだ run は、子が開いた run の出力 wire の値を計算するとき、開いた run と等しい | **型は一致**（`WEnv`、`List Stmt`、`seed : Nat → (String → Nat) → Env`。DeepElab の `runModule` は `.inst` を何もしない文として扱う＝開いた run）。ただし `ChildComputes` は子を `evalAssigns` で見る組合せの子だけ。状態を持つ子は `runModuleT`（Tools/ShippingHierState.lean:264）/ `runModuleTG`（ShippingHierStateG.lean:67） |
| 階層: `ChildFn` | Tools/ShippingMachineCompose.lean:241 | 1 出力の組合せの子が `f` を計算する | IR 側は同じ `evalAssigns (declWidth mc)`。子を deep で検証した結果をこの形に直す補題は無い |
| 階層: `machine_linked` | Tools/ShippingMachineCompose.lean:802 | `MachineTraceL declName d m dsn …`（`#machine_endpoint` の世界、`MachineData`） | **一致しない**（Cdo/CExpr ではなく MachineData） |

---

## E. 段ごとの保証の骨組み

| 段 | 今証明していること | 観測だけのもの | 未接続 |
|---|---|---|---|
| 元の Signal → deep 値 | `{f}_deep_trace`: `((f inputs).val t).toNat = (evalExpr (weOfC nm …) (envOfC nm irEnv) (CExpr.compile nm out)).getD 0`（DeepElab.lean:4548–4560 の生成文）。一般部は `Cdo/CdoM/CdoW.elab_general`（582/832/1230 行）、宣言ごとの部分は kernel が検査する生成証明 | — | reify（`toCExpr` などのメタプログラム）の全域性。F1 Stage 3 |
| deep 値 → 返された IR | fidelity `compile (reify) = concatNorm (inline された cone)` は構文の等式（3690–3790 行）。G1（3846 行、`native_decide`）と `{f}_deep_signal_run`（5497 行）で `runModule weM (deepOrderBody m.body) …` | 別の入口（Off）との出力の一致（FG-CIRCUIT-PILOT §21.6、baseline 272/272） | 返された `m` は `synthesizeHierarchical`（診断入口）のもので、印字コマンドの入口（`synthesizeEntry`）と別（B7）。replay は並べ替えた本体についてで、`m.body` そのものではない。replay が省かれても成功扱い（5538 行） |
| 最適化（`checkedOptimize` / `refineCheck`） | 既定経路: 何もない。shared 経路: `optimizeModule m` について `_signal_runOpt`（3517 行で登録。docs/SharedRoute-Guarantees.md §3） | コンパイラ側の `checkedOptimize` には別の定理がある（`optCheck_sound`、`refineCheck_transfer`、`checkedOptimize_seqOk`）が、deep の chain とはつないでいない | 印字される `checkedOptimize m` と deep の結論の接続。shared 経路の Opt は `checkedOptimize` が `m` を返す場合とずれる |
| SV の印字 | 既定経路: 何もない。shared 経路: (a) 順方向 `_signal_svOpt`（3527–3555 行）は**双子の emitter**（`emitAssigns`/`emitRegs`/`emitMemWrites`）の意味で、`toVerilog` そのものではない。`seqCheck` は native_decide。(b) 往復 `_text_parses`（3583–3590 行）は shipping の parser を `native_decide` で評価する oracle、`_signal_runRT` は読み戻した本体の replay | 双子 emitter と `toVerilog` の一致は `#guard` と corpus（SharedRoute-Guarantees.md §4a） | 印字されるのは `toVerilog (checkedOptimize m)`（Elab.lean:9324）で、shared 経路が扱う `toVerilog (optimizeModule m)` と別の文字列でありうる。parser の証明は無い（F3） |
| axiom・決定手続き | shared 経路は許可集合で監査（3598–3613 行） | — | 既定経路は sorryAx と metavariable だけを見て "axioms clean" と出す（5541–5560 行）。許可集合の検査が無い |

完了条件 (5)（shipping compiler 全体の健全性を主張しない）について: `Tools/DeepElab.lean` 冒頭の説明は「THE GENERAL Signal↔IR theorem」「CompCert-shaped」と書いているが、定理の中身は deep 文法の値についてで、コンパイラの run についてではない（振り返り FG-RETROSPECTIVE:102 も同じ指摘）。文書の言い方を直すかどうかは別の判断。

---

## F. 最初の小さな単位の提案

### どの不足が一番多くを止めているか
1. **成果物が同じでない（327 件すべて）**: 完了条件 (1) はどの必要IPでも満たされていない。入口が違い（診断入口と Off）、検査は最適化前で並べ替えた本体、印字は `checkedOptimize` の後（B7）。
2. **組合せモジュール（82 件、C 群）**: "no registers" で拒否される。`Cdo` の型は `Γr = []` を許すので一般定理の側の障害ではなく、入口の検査と、Signal 側の橋が `runCircuitH` の loop を前提にしていることが障害。
3. **階層（H 40 + M 4 + D の多く、少なくとも 44 件。D を含めると最大 62 件）**: "single-module designs only"。メモリは 2026-10-06 から子モジュールなので、CdoM が対象にしたインライン `.memory` は今の machine 経路にほぼ現れない見込み（M 群の SV で確認。DeepElabRealIP の regFile が今どうなるかは未測定）。

ただし、S 群 179 件を含め**どの必要IPにも今日の受理の記録が無い**ので、上の 2・3 はコードから読んだ見込みである。

### 提案: U1「同じ成果物に対する deep 検査付き入口（平坦・レジスタあり）」
- **前提の測定（U0。コードは変えない）**: 今の HEAD で `#verify_elab_deep` を必要IPの S 群 179 件（できれば 327 件）に当て、行ごとに PROVEN / 拒否の文言 / timeout と時間・メモリを表にする。DeepElabReifyDemo（21）、DeepElabRealIP（17 ポート）、ValueParamInitRepro（5）、ConeSharingGen/Crc16 を同じ SHA で再実行し、2026-09 の記録と比べる。C 節の「不明」を埋め、U1 の対象を実測で絞るため。
- **U1 の範囲**:
  1. 新しいファイル（compiler のファイルを小さく保つ方針に従う）に入口を作る。`synthesizeEntry`（`#synthesizeVerilog` と同じ入口）を 1 回だけ呼び、その戻り値 `m` を deep の生成器に渡す（生成器を「宣言名から合成する」から「渡された `m` を検査する」に分ける。`synthesizeHierarchical` は呼ばない）。
  2. replay を `m.body` そのもの（並べ替えない本体）について示す。または `runModule weM (deepOrderBody m.body) = runModule weM m.body` の補題を証明する。どちらでもよいが、結論は返す `m` について述べる。
  3. 既定経路の監査を shared 経路と同じ許可集合にする（標準 axiom + 名前の形で認めた `native_decide`/`bv_decide` 補助だけ。ほかは失敗）。"axioms clean" の文言を実際の数に置き換える。
  4. 検査が 1 つでも落ちたら（replay を省いた場合も）`throwError` し、IR を返さない。代わりの経路に落とさない。
  5. 返すのは IR の `m` まで。`checkedOptimize` と SV は U1 では「未接続」と記録し、主張しない（条件 (3) の段は次の単位: `refineCheck_transfer` / `optCheck_sound` との合成）。
- **範囲外**: 組合せ（C）、階層（H/M/D）、パラメータ（P）、最適化・SV の接続、文法の拡張、shared 経路の v1 制限。
- **検証の基準**:
  - (a) 返された `m` と、定理の中の本体の定数が同じ値から作られていることを Check で確かめる（`{f}_deep_body` の値と、入口が返した `m.body` を `Expr` として比べる。変えた module（1 文を入れ替える、定数を 1 つ変える）では入口が throw する負の対照を 2 件以上）。
  - (b) 監査の負の対照: 利用者の axiom、名前だけ似た補助 axiom、別の宣言の補助 axiom を拒否することを示す（ValueParamInitRepro の方式）。
  - (c) U0 の S 群の表で PROVEN だった行が、新しい入口でも PROVEN で、返される IR が `synthesizeEntry` の `m` とバイト単位で等しい（`printModule` の文字列で比べる）。拒否された行は理由の文言を記録し、成功扱いにしない。
  - (d) 既存のコマンド（`#synthesizeVerilog` など）の出力 baseline 327/327（stdout の hash と output_baseline.tsv）が変わらない。
  - (e) 既存の deep のテスト（Demo 21、RealIP 17、VPI 5、ConeSharing）が新しい入口でも退行しない。退行したものは原因を記録する。
  - (f) 主張の文面: 「宣言 f について、`synthesizeEntry` が返した IR `m` の run が f の Signal と全時刻で一致する（axiom: 標準 + 列挙した補助 N 個）」までに限る。最適化と SV は未接続と書く。shipping compiler 全体の健全性とは書かない。

U1 の後の候補（参考）: U2 = 組合せモジュール（82 件。`Γr = []` を許し、loop を前提にしない Signal 側の橋）、U3 = 階層（`runModuleH_of_open` と `designOk` を使い、子ごとの deep の結果を `ChildComputes` の形に直す。メモリの子は `SparkleMem_*` の意味を別に置く）、U4 = 最適化段（`checkedOptimize m` への `refineCheck_transfer` の合成）。
