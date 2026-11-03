# KWALK_LEGACY_WINDOW_DECISION: legacy 腕の「窓」が telescope の内側にある — ユーザー判断資料

Status: 判断資料（Lean は変えていない。新しい文・law は足していない）。base b981b54e（kjob/rt169）。台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。
「読んだ」= 私の読み（Lean では未確認）、「数えた」= grep の出力。KWALK_DIAG_DECISION.md（Diag の判断）とは**別の**判断項目。

## 1. 前提知識なしの説明

* K 不変量 = 「memo 表のキーは子の cache のキー」。入口 `synthesizeFromConst` は、結果を作った**最後に** memo 表へ `declName` を書く（Elab.lean 5297, 5304, 5323, 5388）。その後、子の cache への挿入（`synthesizeChild`）までの間だけ、K は「`declName` 1 つを除いて」成り立つ（K_declName、窓）。窓の中で例外が出ると、memo にあって child cache に無い名前が残り、後の `catch` 側で K が壊れる。だから「窓の中では例外が出ない」ことが要る（KWALK_PLAN §4 (a)）。
* certified / mixed / machine の 3 腕は、memo 書き込みが**腕の最後の効果**なので、失敗は常に書き込みの前（K のまま）で、成功は K_declName。これは証明できた（`fromConst_{certified,mixed,machine}_windowK`、BUILT）。
* **legacy 腕**（ゲートも機械も当たらない腕、Elab.lean 5340-5389）は、memo 書き込み（5388）が `Lean.Meta.lambdaTelescope body fun xs innerBody => do …` の**継続の内側**の最後の効果。`lambdaTelescope` の既存の保証（`MemoFamily.tele.lamTelescope`、承認済み）は「継続が `Keeps I`（`I` から始まり、返っても投げても `I` で終わる）なら、telescope 全体も `Keeps I`」という形で、`I` は 1 つしか取れない。
* 継続は、成功すると K_declName（書き込み後）、失敗すると K（書き込み前）で終わる。`I := K_declName` を取ると成功側は閉じるが、失敗側は「K_declName」としか言えず、K に戻せない。`I := K` は成功側が閉じない（書き込み後は K でない）。この調査では、`MemoFamily` の既存 12 文から、失敗側を K に戻す経路は見つからなかった。意味的には、書き込みの後には `return result` しか無いので失敗は書き込みの前（K）のはずだが、telescope の外からは書けない。

## 2. 影響

* 止まるもの: legacy 腕（`hlegacy`）、したがって `fromConst_frontends_windowK` と `entryNested_windowK` の `hbody` を**無条件には**渡せない（legacy 腕に当たる定数について）。S6（`synthesizeChild`、深さ帰納）と M4.MEMO-01（家族の +1）の受入が、legacy 腕の分だけ条件付きのまま。
* 証明できた legacy 腕の部品（`openRecordInputs`、`splitReturnLeaves`、`bindInputsLegacy`、helper 群）は、下のどの選択肢でも使える。

## 3. 選択肢

| | 内容 | 台帳・保証への影響 | コスト | 可逆性 |
|---|---|---|---|---|
| A（推奨） | `MemoTele` に Triple 形の 1 文を足す: `lamTelescope` について「継続が `P` から返れば `Q`、投げれば `R` で終わるなら、telescope も同じ」（成功と失敗の事後条件を分けた形、`Keeps` は `Q = R = I` の特別な場合）。同じ形が既存の `Triple.tryFinally` にもある | 家族の文が 12 → 13（`frameDiag` が承認されるなら 14）。TRUSTED 境界の文が 1 つ増える。承認済み freeze（MEMO_FAMILY_FREEZE rev2）の変更なので reviewer の承認が要る | 小（文 1 つ + 使う補題 1 つ + freeze の改訂）。legacy 腕は rt169 の部品でそのまま閉じる見込み（読み） | 文を消せば legacy 腕が再び仮説になる。他が依存した後は外しにくい |
| B | 可換則: 継続の末尾が `… >>= f`（`f` は `xs`, `b` に依らない）のとき `lambdaTelescope e (fun xs b => k xs b >>= f) = lambdaTelescope e k >>= f`。これで memo 書き込みを telescope の外に出せる | 家族に等式の文が 1 つ増える（Meta の telescope 実装の性質を直接主張するので、A より強い主張） | 小。ただし主張が強く、真偽の根拠が A より薄い | A と同じ |
| C | K walk の目標を弱める: legacy 腕の失敗側は K_declName までとし、その後の `catch` 側で K を別の議論で示す | 新しい文は無いが、K walk の保証が変わる（FG の縮小に当たる可能性。禁止事項に触れるので、ユーザー判断が要る） | 大（`catch` を全部見直す） | — |
| D | Elab.lean の編集（memo 書き込みを telescope の外へ） | 本番コンパイラの変更。禁止（ユーザー未承認） | 大 | 不可逆に近い |

推奨: A。理由: 既存の `MemoTele` の 4 文は「継続が `Keeps I`」の形で、`Q = R` に限った特別な場合。A は同じ種類の文を事後条件を分けて言い直すだけで、意味は「継続が正しく返る・投げるなら telescope もそう」（telescope 結合子は継続を 1 回走らせるだけ、読み）。B は実装の等式を言うので避ける。

## 4. 判断しない場合

* K walk は legacy 腕について**条件付き**のまま（`hlegacy` が仮説）。`段階: 条件付き` で止まる。certified / mixed / machine の腕と入れ子の入口は、legacy 腕以外の定数について無条件（Diag の判断を除く）。

## 5. 追記: Diag の数えの訂正（KWALK_DIAG_DECISION.md に関係する）

KWALK_DIAG_DECISION.md §2 の Diag の数え（翻訳器の範囲 5700-8960）には、helper 内の `ppExpr` ×3（Elab.lean 681, 686, 715。`extractDimExprStep` と `inferHWTypeWithDimensionsStep` の `throwError` の前のエラーメッセージ整形、`symbolicMode` の枝）が入っていない（helper は 5700 より前）。`inferHWTypeFromSignal` はハンドラと legacy 腕の `bindInputsLegacy` の両方から呼ばれるので、LegacyImplK と legacy 腕の両方がこの `ppExpr` に依存する。`frameDiag`（選択肢 A）が `ppExpr` も覆う形ならこれも解ける。仮説 `PpMvK`（`ppExpr e` が `mv` を変えない）を def で取って helper の K 版を証明した（`Tools/ShippingGen4KWalkHelpers.lean`、BUILT）。

## 6. 根拠

* `scripts/gen4/KWALK_PLAN.md`（S4 の結果、「legacy 腕で見つかった 2 点」）、`Tools/Assume/MemoFamily.lean`（`MemoTele`）、`Sparkle/Compiler/Elab.lean` 5340-5389。
