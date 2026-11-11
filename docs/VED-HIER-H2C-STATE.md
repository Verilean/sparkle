# VED 階層 H2c-state: 子の call 引数が親の register の（更新前）状態のとき

基準: int/ved-cand12 08fbcd2f（H2b、H2c の導出 net、U1 の定数表経路を含む）。設計: docs/VED-HIER-H2-DESIGN.md、docs/VED-HIER-H2C.md、reviewer の設計回答
（組合せ子限定、更新前 state、実 child、1 つの帰納法での合成補題）。本文書は実装記録で、文の凍結、327 行への加算、hierarchical strict の inventory 主張、release を主張しない。

## 0. 結論

- **文 `U2HRStmt` は変更していない**（`Tools/VedU2HierReg.lean`、`Tools/VedU2HierStmt.lean` は差分 0）。binder は増えていない。
- 実 R223（`Tests/IP/Net/HTTPTest.lean` の private `synth_httpGetByte`、原宣言そのまま）が標準入口 `#ved_u2_hier` で strict
  （axioms は propext、Classical.choice、Quot.sound のみ、型は `U2HRStmt c m d decl` と `==`）。
- 子は組合せ回路（assign だけ）に限る。stateful 子、任意の stream 関数、別の子の出力 → 子は範囲外（`[conns]` のまま）。

## 1. 何が通らなかったか

`(httpGetEmitter trigger).byte` は `httpGetByte cnt`。`circuit do` の中で子（関数として `burstEmit` に渡される）が register `cnt` に適用される。
`runCircuitH` を展開すると、子の呼出しは (i) `Signal.loop` の中（`.snd` の書込みだけが使われるので死んだ位置）と (ii) loop の外の出力
`(body regs (mkHolds stateLoop)).fst`（引数は入力だけの閉項）に現れる。H2c は引数を「入力だけの net」に限り、register 出力を `[conns]` で拒否していた。

## 2. 設計（reviewer の回答どおり）

1. **内部合成補題 `outputsOnHS_of_stepRK`**（`Tools/VedU2HierState.lean`）: `outputsOnHS_of_stepR` の `hkid` を、cycle `t`、その trace 自身の更新前
   state `S`、不変条件 `R ins t (S [])` の下でだけ要求する。同じ 1 つの帰納法（`chain`）で、不変条件 → 子の同時刻出力（`hkid`）→ 開いた評価
   （`fold_oracle`）→ 出力と次の state（`hstep`）→ `R (t+1)`。子は更新前 state を読む（次 state は読まない）。run の存在は `runHS_exists`。
2. **同 cycle の子出力 `kid_step`**（`Tools/VedU2HierStep.lean`）: 組合せ子（`asgOnly`）では閉じた run の cycle `t` の環境は cycle `t` の seed だけで決まる
   （`runModule_asg_local`）。子自身の U1 定理を任意の範囲内の全域 stream `F` に適用し、親は `F t port = (その cycle の配線の値)` だけを供給する。
   `closed_run_reg`: 親 register の出力は cycle `t` の更新前 state。
3. **開いた親 `genOpenSt`**（`Tools/VedU2HierStGen.lean`）: 宣言の値を `whnfCore` と定義の展開で外側の call `g a`（`a` は入力だけの閉項、親自身の loop を含む）まで簡約し、
   カーネルで `decl xs = g a`（`Eq.refl`）。開いた親は、子が渡された回路（`burstEmit trigger 18 f`）の子を `fun _ => keepAlive o` に置換した項
   （`keepAlive` は子の引数を読み続け、引数の register が合成で捨てられないようにする。意味は `o`）。
4. **state の結び**: 開いた親の `#verify_elab_deep` が、top loop の状態を Signal の事実として書き出す（DeepElab の `ved_have_export`: `<decl>_<port>_deep_state`）。
   宣言側の引数 signal `a` の loop は死んだコードだけが開いた親の loop と違うので、カーネルだけの変換（`ved_kernel_exact`）で結ぶ。これで
   `(a.val t).toNat = irS ins t (slot)`（`irS` は開いた親の IR 状態）。IR 側の配線の値は `closed_run_asgOf` と `closed_run_reg` から。

## 3. DeepElab の変更（最小）

- `ved_have_export`: top loop の `hLt` を `<decl>_<port>_deep_state` として定理に書き出す（`first` の別案が既に書き出していれば何もしない、名前は現在の namespace 付き）。
- trace 定理の末尾を `all_goals` で包む: 状態を読まない port（入力そのままの出力）は `congr 1` で閉じ、残りの tactic が "No goals" で失敗していた。

未知の関数を primitive として扱う変更も、compile の正しさを仮定する変更もない。子の意味は子の U1 定理（`kid_step`）から来る。

## 4. 検査

`Tests/Ved/U2HierStateCallCheck.lean`（lakefile と ved.yml に登録）: 正例（3 register と 2 port の子を持つ小さな族 `stFam`、R223 の同一宣言の複製と原宣言との値の `==`）、
閉じた run = 宣言（具体値）、対照 7 件（別 register、更新後 state、1 cycle ずれ ×2、引数交換、同時刻循環、子 module の交換）。ved.yml は原宣言そのもの
（private `synth_httpGetByte`）にも入口を適用する（その module の末尾へ追記して実行）。

## 5. 範囲外 / 未了

- R220 `synth_hftOutByte`、R92 `synth_hftPcieOutByte`: 入口は `[deep]` まで進むが、親が大きい（parser / mmio endpoint が入る）ため DeepElab が止まる。結果は報告に記す。
- 引数が register の単純な再配線（alias、slice、bundle の slice）でない式（`(cnt の下位 7 bit) - 1` など）は slot を決められず `[proof]` / `[kernel]` で拒否（偽の受理はない）。
