# VED 階層 H2c-state: 子の call 引数が親の register の（更新前）状態のとき

基準: int/ved-cand12 08fbcd2f（H2b、H2c の導出 net、U1 の定数表経路を含む）。設計: docs/VED-HIER-H2-DESIGN.md、docs/VED-HIER-H2C.md、および reviewer の設計指示のうち
本文書の「限定した方法」（組合せ子限定、更新前 state、実 child、1 つの帰納法での合成補題）。本文書は実装記録で、文の凍結、327 行への加算、hierarchical strict の inventory 主張、release を主張しない。

## 0. 結論

- **文 `U2HRStmt` は変更していない**（`Tools/VedU2HierReg.lean`、`Tools/VedU2HierStmt.lean` は差分 0）。binder は増えていない。
- 実 R223（`Tests/IP/Net/HTTPTest.lean` の private `synth_httpGetByte`、原宣言そのまま）が標準入口 `#ved_u2_hier` で strict
  （axioms は propext、Classical.choice、Quot.sound のみ、型は `U2HRStmt c m d decl` と `==`）。
- 子は組合せ回路（assign だけ）に限る。stateful 子、任意の stream 関数、別の子の出力 → 子は範囲外（`[conns]` のまま）。

## 1. 何が通らなかったか

`(httpGetEmitter trigger).byte` は `httpGetByte cnt`。`circuit do` の中で子（関数として `burstEmit` に渡される）が register `cnt` に適用される。
`runCircuitH` を展開すると、子の呼出しは (i) `Signal.loop` の中（`.snd` の書込みだけが使われるので死んだ位置）と (ii) loop の外の出力
`(body regs (mkHolds stateLoop)).fst`（引数は入力だけの閉項）に現れる。H2c は引数を「入力だけの net」に限り、register 出力を `[conns]` で拒否していた。

## 2. 設計（限定した方法）

reviewer の設計指示の全体を実装したのではなく、次の限定した方法だけを実装した。**開いた親は証明の補助**（親 register の state を供給するだけ）で、
開いた親と宣言の間の等式は主張しない。**宣言は「call」と「引数の state の等式」のカーネルでの結合**で結ぶ: 宣言 = 外側の call
（`decl xs = g a`、`Eq.refl`、定理 `_ceq`）、call の引数 = 親 register の state（開いた親の deep run が書き出す state 定理と、カーネルだけの
変換による引数 state の等式）。文 `U2HRStmt` は変えない。

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
5. **引数の保持**: 開いた親は、子の置換先で引数を読み続ける（`mux (x === x) o o`、意味は `o`）ことで引数の register を合成から残す。
   もし合成器がこの式を畳むと register が消え、入口は `[deep]` で拒否する（偽の受理にはならない）。
6. **部分生成の扱い**: 開いた親の `#verify_elab_deep` は port ごとに証明する。証明が使わない port の失敗だけを許し、その場合は
   `VED U2 HIER PARTIAL-DEEP` の info 行（開いた親、使った port、失敗した port、error 数、port ごとの最初の error）を残す。使う port の error、
   port に結べない error、証明が要る state 定理の欠落は `[deep]` で拒否する。使った fact の `sorry` と非標準 axiom は最終定理の strict audit が拒否する。
   clean な生成はこの行を出さない。

## 3. DeepElab の変更（最小）

- `ved_have_export`: top loop の `hLt` を `<decl>_<port>_deep_state` として定理に書き出す（`first` の別案が既に書き出していれば何もしない、名前は現在の namespace 付き）。
- trace 定理の末尾を `all_goals` で包む: 状態を読まない port（入力そのままの出力）は `congr 1` で閉じ、残りの tactic が "No goals" で失敗していた。

未知の関数を primitive として扱う変更も、compile の正しさを仮定する変更もない。子の意味は子の U1 定理（`kid_step`）から来る。

## 4. 検査

`Tests/Ved/U2HierStateCallCheck.lean`（lakefile と ved.yml に登録）: 正例（3 register と 2 port の子を持つ小さな族 `stFam`、R223 の同一宣言の複製と原宣言との値の `==`）、
閉じた run = 宣言（具体値）、対照 7 件（別 register、更新後 state、1 cycle ずれ ×2、引数交換、同時刻循環、子 module の交換）。ved.yml は原宣言そのもの
（private `synth_httpGetByte`）にも入口を適用する（その module の末尾へ追記して実行）。

`Tests/Ved/U2HierPartialDeepCheck.lean`（lakefile と ved.yml に登録）: 2 port（`x` は子 `diff2` の呼出し、`y` は register `c`）と 3 register を持つ親 `stPortX` 系。
clean な正例（`PARTIAL-DEEP` 行なし、`#guard_msgs` で空）、使わない port `y` の失敗（受理 + `PARTIAL-DEEP` 行 2 本）、拒否 5 件（使う port の error、port に結べない
error、state 定理の欠落、使う fact の `sorry`、使う fact の局所 `axiom`）。判定の純関数（`attributeDeepErrors`、`deepVerdict`）の `#guard` も含む。
この small module では実際に失敗する port を作れないため、失敗は checker の試験用 hook `tamper`（deep run の直後、実際の `Phase1` と実際の message に作用）で再現する:
port の `PROVEN` 行を消して error を足す、または開いた親の deep 定数一式を別名で複製して used fact 1 つだけを `sorry` / 局所 axiom に替える。
最終の証明と audit は実物。

## 5. 範囲外 / 未了

- R220 `synth_hftOutByte`: 入口は `[deep]` を通るが止まる。記録された run では、strict audit が非標準 axiom を報告した（DeepElab が入れ子の parser の
  loop state を証明するときに `bv_decide` を使い、`..._byte_deep_trace._native.bv_decide.ax_11` が残る）。また本来の hstep は isDefEq で 8M heartbeats に達した。
- R92 `synth_hftPcieOutByte`: `[proof]` の `simp` が "maximum number of steps exceeded" で止まった（1399 秒後）。この run は 1200 秒の timeout の下では行っていない。
- 引数が register の単純な再配線（alias、slice、bundle の slice）でない式（`(cnt の下位 7 bit) - 1` など）は slot を決められず `[proof]` / `[kernel]` で拒否（偽の受理はない）。
