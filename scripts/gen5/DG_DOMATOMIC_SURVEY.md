# DG-READERTRACE: `DomAtomic` の D-b 調査（rev15 §4 の「別の道」）（文書のみ）

Issue `sparkle-gen5-dg-readertrace`。Base: `kjob/rt20` be72e9ca。調査対象は rev15 §4 の D-b:「`MidInputs` から `DomAtomic` を外せるか」。
用語: 「見つからなかった」は「この調査で辿った経路では見つからなかった」の意味で、不可能・導出不能の主張ではない。この調査は**ソースの読解と grep だけ**で、Lean の証明・build・scratch 実行はしていない。成立は**未証明**。条件付き・中間結果。

**台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。** D-b は減算として数えない（reviewer 指摘）。この文書は台帳を 1 行も変えない。

## 0. 読んだもの

`Tools/ShippingGen5ReaderTraceShape.lean`（`DomAtomic`、`MidInputs`、`shapeStart_trace`、`machineShapeF_reach`）、`Tools/ShippingReaderFuelShape.lean`（`shapeStart`、`shapePost`）、`Sparkle/Compiler/Elab.lean`（`machReserve` 3703、`machConv` 3888、`machInstance` 4049、`machInstanceS` 4087、`machLoopRoot` 4204、`machDom?` 4269、`machineShape?` 5072〜5175）、`Tools/ShippingGen5Cover6.lean`（`CtrlEq` / `FReachC`）、`Tools/ShippingGen5Cover2.lean`（`PhInRange` / `MentionsPh`）、`Tools/ShippingGen5Cover3.lean`（`InRange`）、`Tools/ShippingGen5ReaderTrace.lean`（`DomPh`）、`Tools/ShippingGen5ReaderTraceNested.lean`（`trInv_reserved`）、`Tools/ShippingReaderLenOk.lean`（`reserved`）。

## 1. `DomAtomic` が今どこで使われているか

`shapeStart`（`ShippingReaderFuelShape.lean:207`）は、`run? = some (dom, αs, initsE, body)` のとき `dom` を空状態 `{}` で変換して `(dom', stc)` を得て、**`stc` を捨て**、`machReserve … dom' … {}` で空状態に予約する。

`shapeStart_trace`（`Shape.lean:78`）は予約後の状態が `TrInv`（特に `DomPh`: `st.dom = some d → InRange nDecl st st.lets.size d ∧ NoLoose 0 d`）を満たすことを示す。`trInv_reserved`（`Nested.lean:15`）は `InRange nDecl s s.lets.size dom'` と `NoLoose 0 dom'` を**予約先の状態 `s`**（ここでは `{}`）で要求する。ところが変換のトレース `hT` が与えるのは**変換後の状態 `stc`** での範囲である。両者をつなぐために、現在は**変換前**の `dom` が `bvar` か `const` であること（`DomAtomic dom`）を仮定し、`readF` の `conv` 腕を 1 段展開して `stc = {}` を出している。

## 2. 調査の問い

`DomAtomic dom`（変換前）の代わりに、成功した `machineShapeF` が必ず満たす事実から、`dom'` の範囲を `{}` で言えるか。

## 3. 辿った経路

### 3.1 `st.dom` を書く場所は 5 つで、すべて「設定済みなら同じ値のときだけ通る」

`Elab.lean` で `dom := some …` を含む行を grep した結果（`dom :=` の他の出現はコメントのみ）:

| 行 | 関数 | 書き方 | 設定済みのとき |
|---|---|---|---|
| 3716 | `machReserve` | `dom := some dom'` | 3708–3710: `st.dom = some d` かつ `d != dom'` なら `none` |
| 3933 | `machConv`（bare register 腕） | `dom := some dom'` | 3927–3929: 同じ形の検査 |
| 4068 | `machInstance`（`.domain` 引数） | `none ⇒ { st with dom := some v' }` | 4066–4067: `some d ⇒ if d != v' then none else そのまま` |
| 4107 | `machInstanceS`（`.domain` 引数） | 同上 | 4105–4106: 同上 |
| 4235 | `machLoopRoot` | `dom := some dom'` | 4215–4217: 同じ形の検査 |

`MachRead` を `{}` から作る箇所は `machineShape?` の 5108（`let st : MachRead := {}`）だけだった（grep。網羅の証明ではない）。したがって**設定済みの `st.dom` は、読み取りの間、同じ値のまま残る**ように読める。ただしこれは Elab 側のソースの読みで、`readF`（燃料つきの twin）の全腕について**証明したものではない**。

### 3.2 成功した run では最終 `st.dom` は開始時の `dom'` になる

`run? = some …` のとき、`shapeStart` が先に `dom := some dom'` を設定する（3716）。3.1 の保存性があれば、最終状態の `st.dom = some dom'`（同じ式）。`shapePost`（`ShippingReaderFuelShape.lean:165–166`）は `domE ← st.dom <|> machTypeDom? p.d.type` から `machDom? (kI + n + k) domE` を要する。`machDom?`（`Elab.lean:4269`）は `domE` が `fvar ⟨.num (.str .anonymous "_machIn") i⟩` か `const defaultDomain` のときだけ `some`。したがって**成功した run では、`dom'`（変換後）は `fvar _machIn i` か `const Domain.defaultDomain ls` である**（3.1 の保存性が使えれば）。

### 3.3 その形なら `{}` での範囲は変換状態によらない

`InRange nDecl st k v := PhInRange nDecl st.insts.size st.kinds.size k v`（`Cover3.lean:302`）。`PhInRange`（`Cover2.lean:62`）は 4 つの `MentionsPh` 節。`MentionsPh`（`Cover2.lean:19`）は `fvar` / `app` / `lam` / `forallE` だけを辿り、`const` は `False`。
* `dom' = const c ls`: 4 節とも空虚に成り立つ（状態に依存しない）。`NoLoose 0` も自明。
* `dom' = fvar _machIn i`: `_machIn` 節は `i < nDecl`（状態に依存しない）、他の 3 節（`_machInst` / `_machSlot` / `_machLet`）は `MentionsPh` がタグ不一致で `False` なので空虚。`NoLoose 0` は自明。

つまり、`hT` が `stc` で与える `InRange nDecl stc … dom'` から `i < nDecl` を取り出せば、`InRange nDecl {} 0 dom'` が出る。`DomAtomic dom`（変換前）も `stc = {}` も要らない見込み。

## 4. 結論と、D-b を実装する場合に必要なもの

**この調査で辿った経路では、D-b の道が見つかった（未証明）。新しい前提は要らない見込み。** ただし次の 2 点が要る:

1. **新しい不変条件の補題 `DomKeep`（未存在）。** 「`readF` の任意の呼び出しについて、入力状態の `dom = some d` なら出力状態の `dom = some d`」を、`step`（`readF` の全腕）について示す。既存の `TraceGood` / `FReachC` では示せない: `CtrlEq`（`Cover6.lean:17`）は `dom` を**自由**にしており、ヘッダに「`fullInv_reachC` says nothing about `dom` (R-dom is a separate obligation)」と明記されている。`TraceGood`（`Ctl.lean`）の結論にも `dom` の保存はない。したがって `TraceGood` の拡張か、独立の帰納（7 つの `Call` 型 × 各腕）になる。`Tools/ShippingGen5ReaderTrace*.lean` は 23 ファイル・合計 4649 行（`Shape` / `ShapeIn` を含む）で、`DomKeep` は `TraceGood` と同じ腕の数だけ要る見込み。**規模は見積もっていない**（数えていない）。
2. **型の変更（承認が要る）。** `shapeStart_trace` の `hdom` 仮定から `DomAtomic dom` を外し、代わりに「変換後 `dom'` が `_machIn i`（`i < nDecl` は `hT` から）または `const`」を、`machineShapeF_reach` が最終状態（`DomKeep` と `shapePost` の成功）から供給する形に組み替える。`MidInputs` の run 節から `DomAtomic dom` が消える（`ShapeInputs` が弱くなる）。`shapeStart_trace` の仮定と `MidInputs` の型が変わるので、承認済みの型の変更になる。別 freeze（reviewer の承認が要る）。

別の道（`DomKeep` を使わない）として、`shapeStart` が `stc` を捨てることを使わず、`stc` の `lets` が空であることを `dom` の形から示す案も読んだが、変換前の `dom` が atomic でないとき `conv` が `lets` を積む（`_machLet` を返す）可能性があり、**変換後の形に頼らない道は見つからなかった**。

## 5. 選択肢と台帳（すべて未計数）

| 案 | 内容 | FG / T1 | 影響・コスト |
|---|---|---|---|
| **D-b（この調査の道）** | `DomKeep` を証明し、`shapeStart_trace` / `MidInputs` から `DomAtomic dom` を外す | FG ±0（`DomAtomic` を台帳に足さずに済む）/ T1 ±0 | 新規補題（全腕の帰納）と型の変更。成立は未証明。外れれば `ShapeInputs` の未供給成分が 1 つ減る |
| D-a | `DomAtomicIn`（run の `dom` は bvar / const）を FG の名前付き条件として足す | FG +1 見込み / T1 ±0 | 受理されたソースでの成立は未確認。reviewer 指示により、D-b の結果が出るまで足さない |
| D-c | `ShapeInputs` を仮定のまま | ±0 | `DomAtomic` が仮定として残る |

**推奨: D-b を別 freeze で提案する（次の単位）。** D-b が証明できなかったときだけ D-a を検討する。この文書は D-a を台帳に足さない。

## 6. 主張しないこと

`DomKeep` が成り立つこと（`readF` の全腕で確認していない）、D-b が証明できること、`ShapeInputs`（`p.bs.length ≤ nDecl` を含む）が受理されたソースで成り立つこと、台帳の増減。コンパイラ・共有定義・TRUSTED 境界・law は変えていない。`GenWF` は強化しない。
