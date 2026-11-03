# KWALK_DIAG_DECISION: LegacyImplK が止まる点（診断用操作 `Diag` の memo 枠）— ユーザー判断資料

Status: 判断資料（Lean は変えていない）。base ecdbc7fa（kjob/rt167）。台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。
「読んだ」= 私の読み（Lean では未確認）、「数えた」= grep の出力。

## 1. 前提知識なしの説明

* K 不変量 = 「memo 表（`sparkleSubModuleCache`）のキーは子の cache（`sparkleChildCache`）のキー」。K walk（KWALK_PLAN）は、翻訳器が走る間 K が保たれることを一文ずつ証明する。
* 各文の保証は承認済みの `MemoFamily`（12 文）から取る。`frame` は `FramedNM` に入る操作（副セルの get/set、`getEnv`、`whnf` など約 40 種）が memo 表を変えないと述べる。
* 診断用の操作 `Diag`（`ppExpr`、`IO.eprintln`、`flushStderr`、`IO.FS.Handle.mk` / `putStrLn` / `flush`、`IO.getStderr`、`profLogIO`）は `FramedNM` に**入っていない**。既存の A 境界（`RefLawsAOps.diag`）は、`Diag` について quiet / `cv` / `sv` / `dv` の保存だけを述べ、`mv`（memo 表）の保存は述べない。
* したがって K 版では `Diag` の操作が memo 表を変えない、という文が家族の中に無い。この調査では、`Diag` から memo 表の保存を導く供給元・経路は見つからなかった（`Diag` の操作は opaque な IO で、論理側から memo セルへの影響を除けない）。

## 2. どこで止まるか

S3 の `LegacyImplK`（`Rec.translateExprToWireImpl`、A 版 `ShippingChildLegacyHandlersA` 等）の中に `Diag` が現れる（数えた、`Sparkle/Compiler/Elab.lean` の翻訳器の範囲 5700-8960）:
`ppExpr` 3 箇所（5709, 7025, 7366）、`IO.eprintln` + `flushStderr` 2 組（6423-6425, 6973-6974）、`IO.FS.Handle.mk` + `putStrLn` + `flush`（6975-6977）。6423 側は `SPARKLE_DEBUG_HWCALL` の環境変数の下、6973 側は profile 出力の下（読んだ）。ただし証明では実行時の条件に頼れない（環境変数は `IO.getEnv` の結果）。
`LegacyImplK` 以外（`Emit` / `Inst` / `ProjField` / `Canon` / `Fallback` / `LegacyCached`、rt167 で BUILT）には `Diag` は現れず、新しい前提は要らなかった。

## 3. 選択肢

| | 内容 | 台帳・保証への影響 | コスト | 可逆性 |
|---|---|---|---|---|
| A（推奨） | `MemoFamily` に 13 文目 `frameDiag` を足す: `Diag p` の操作 1 回を実行しても `mv` は変わらない（`O.quiet w` かつ許される文脈のとき）。`O.diag`（既存）が quiet / `cv` / `sv` / `dv` を述べているのと同じ形で `mv` を足すだけ | 家族の文が 12 → 13。TRUSTED 境界の文が 1 つ増える（T1 の件数に数えるかは reviewer / ユーザーが決める。今は T1 57 のまま）。承認済み freeze（MEMO_FAMILY_FREEZE rev2）の変更なので reviewer の承認が要る | 小（文 1 つ + `keeps_KW_diag` の 1 補題 + freeze の改訂）。LegacyImplK の `vca` K 版（WalkA 873 + Helpers/Handlers/Impl/Tail の写し、推定 1000-1600 行、実測ではない）は別途 | 後から外せる（文を消せば `Diag` を含む箇所が再び仮説になる）。ただし他が依存した後は外しにくい |
| B | `FramedNM` に `Diag` の構成子を足す（`frame` の定義域を広げる） | A と同じ効果。`frame` の文そのものは変わらないが、`frame` が主張する操作の集合が広がる | 小。ただし 40 constructor の生成物（`-- GENERATED`）の再生成が要る | A と同じ |
| C | 足さない。`LegacyImplK` を最終定理の仮説として残す | 条件付きのまま（`translate_keepsK` は `LegacyImplK` と `ChildEntryK` を仮説に取る）。完了にはできない | 0 | — |
| D | コンパイラ側の診断出力を取り除く（Elab.lean の編集） | 本番コンパイラの変更。禁止（ユーザー未承認）で、出力の仕様も変わる | 大 | 不可逆に近い |

推奨: A。理由: `Diag` の操作が持つのは標準エラーの出力、ファイルへの追記、`ppExpr`（Meta の整形）で、memo 表の `IO.Ref` に触れる経路は読んだ限り無い。既存の `O.diag` が同じ操作について `cv` / `sv` / `dv` の保存をすでに仮定しているので、`mv` を足すのは同じ種類の仮定の延長。

## 4. 判断しない場合

* S3 の `LegacyImplK` は仮説のまま残り、K walk 全体は「条件付き」（`段階: 条件付き`、`LegacyImplK` と `ChildEntryK` が仮定）で止まる。家族の +1（M4.MEMO-01）は受入できない。
* `LegacyImplK` に `Diag` を含まない部分（例: `handleApplicative` 等のうち `Diag` に当たらない handler）は、`vca` の K 版を作れば先に証明できる見込みだが、この調査では `vca` の K 版に着手していない（時間内に終わらないと見積った。WalkA 873 行の写し）。

## 5. 止まった理由と次

* 止まった理由: 新しい TRUSTED 文（A / B）はユーザー未承認の範囲（共通ルール 5, 10）。
* 影響を受ける後続: S4-S6（入口の腕・窓・深さ帰納）は `LegacyImplK` に依存しない見込み（読み、未確認）。`Diag` が入口側（5290-5600）に現れるかは、`ppExpr` の 3 箇所が全て 5700 以降であることまでは数えたが、入口側の `IO.eprintln` は数えていない。
* 根拠: `Tools/ShippingChildInv.lean:264`（`Diag` の定義）、`Tools/ShippingChildVCA.lean:85`（`keepsA_diag` は `O.diag` を使う）、`Tools/Assume/MemoFamily.lean:52`（`FramedNM`、`Diag` の構成子なし）、`scripts/gen4/MEMO_FAMILY_FREEZE.md` rev2 §2。
