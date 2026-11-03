# (1c) 再入を必ず失敗させるコンパイラ変更: freeze rev2（文書のみ）

- **rev2（Issue rt160）**: rev1 = bba569e2 への reviewer 指摘 2 点に対する改訂。(1) `Start` の完全型を固定（§3.2、scratch で elaborate）。(2) 新 cell が process-global な `IO.Ref` であることについて、top-level 合成が重ならない根拠を調査（§2.6）。直した点の対応表は §8。台帳: 新前提 0、D.E-12 は部分供給 0。

- Issue: `sparkle-gen4-fallback-supply`（agent rt159）。base: par/fb-cycle = 8714354b（FB_HNO_STUDY、reviewer 承認: hno は義務のまま）。
- ユーザー判断 2026-11-03（scripts/gen4/M4_DECISION.md §7）: 項目 1 は (1c)「同じ宣言への再入を、catch に飲まれない形で必ず失敗させるコンパイラ変更」。項目 2（legacy shim）は (2c) 保留、この文書は触れない。
- 種別: freeze 文書。Lean・コンパイラ（Sparkle/Compiler/Elab.lean 等）・Tools/ は編集していない。ビルド・測定もしていない。承認まで実装に進まない。
- 「見つからなかった」は、読んだ範囲で供給元・経路が見つからなかったという意味で、不可能・導出不能とは言っていない。mutant は扱っていない。**読解**（コードを読んだだけ）と**既存定理**を区別する。行番号は 8714354b の `Sparkle/Compiler/Elab.lean`（9513 行）。
- 台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。**D.E-12 は「G7 の hno / htop」で 1 行。hno の非 machine 分を供給しても、htop（legacy htop は未解決）が残る限り部分供給で、この行は 0（−1 ではない）**。新前提 0 の見込み（§6）。

## 0. 結論（先に）

1. 宣言のコンパイルが同じ宣言へ戻りうる入口は、読んだ範囲では**すべて `synthesizeCombinationalCoreWith`（Elab.lean:5423）を通る**（§1.1）。ここに「コンパイル中の宣言名の stack」と「再入した事実を残す sticky な旗（tripwire）」を置けば、入口ごとに手を入れる必要がない。
2. 入れ子の失敗を飲む catch のうち、入れ子の entry 呼び出しを内側に含むのは `tryInlineUnfold` の `catch ex1` / `catch ex2`（6358, 6374）だけ（§1.3）。他の `catch` は Meta 内の `inferType` / `getConstInfo` 等か IO だけで、entry を呼ぶ式を含まない（読解）。
3. 推奨設計は **A: stack + tripwire**。再入を見たら (i) 旗を立て、(ii) 専用 error を投げる。**旗は catch に飲まれても消えず、entry は成功で戻る直前に旗を見て、立っていれば必ず throw する**。catch 側の改造が要らないので、将来 catch が増えても `hno` の証明が壊れない。B（catch ごとに再送出）は §2.5 に比較として置く。
4. 供給定理（§3）は「成功した run の出力 design に `ofDecl declName` の名前の module が無い」。使う既存定理は `ofDecl_injective`（Tools/ShippingModuleName.lean:766）、`hno_iff_not_any`（FB_HNO_STUDY §2.2）。**新しく要る事実は 3 つ**（F1 旗の単調性、F2 design の module 名の出自、F3 stack の釣り合い）。いずれも定理として証明する対象で、**新しい TRUSTED / law は要らない見込み**。ただし F2 は addModule の全箇所の walk で規模が大きい（§3.3）。F2 が立たないと分かったら止まって判断資料に回す。
5. 動作の変化: 正常な（循環しない）コンパイルの出力は変わらない（§2.4）。**変わりうるのは、再入を含む試行が今は catch+retry で成功している設計**（§2.4 の (c)）。corpus 測定でそれが 0 件であることを確認し、出たら止めて報告する（§4）。

## 1. 再入の経路

### 1.1 入口の表（宣言のコンパイルが入れ子で同じ宣言へ戻りうる箇所）

| # | 入口 | 関数 / 行 | 次に呼ぶもの | entry までの経路 |
|---|---|---|---|---|
| E0 | entry 本体 | `synthesizeCombinationalCoreWith` 5423 | `synthesizeFromConst` 5284（doSynth 5553） | ここが唯一の合流点 |
| E1 | 最上位 | `synthesizeCombinationalWith` 5592、`synthesizeCombinationalWithParameters` 8940 | E0 を `[] false` / `true` で呼ぶ | outermost（depth 0）。stack は空から始まる |
| E2 | `@[hardware_module]` の子 | `handleDefinitionUnfold` 6568-6603 の `synthesizeCombinational name`（6586, 6598） | `Rec.synthesizeCombinational` 6332 → `childSynthEntry` 5620 → `sparkleChildSynth` → `synthesizeChild` 8929 → `synthesizeCombinational`（8920）→ E1 → E0 | 6598 は `tryInlineUnfold` 失敗後の fallback 経路 |
| E3 | 子の instance 腕（certified） | `translateInstanceOrFallback` 8695-8735 の `childSynthEntry mn` / `childSynthEntry recName`（8712, 8730） | 同上 `synthesizeChild` | memo（`sparkleChildCache`）経由 |
| E4 | machine の子 | `closeInstsM` 5206 / `closeInstsGM` 5228 の `synth c`（`sparkleChildSynth.get`） | 同上 | memory は build で entry を通らない（5232 付近のコメント）。declaration が memory placeholder 名を持つ場合は `synth c` |
| E5 | inline の中の hardware_module | `tryInlineUnfold` 6345 → `translateExprToWire eReduced`（6358, 6374 の retry）→ E2/E3 | inline 展開した body の中の `@[hardware_module]` 呼び出し | **catch に飲まれうる唯一の経路**（§1.3） |
| E6 | parametric | `synthesizeCombinationalWithParameters` 8940 は E1 と同じ outermost。parametric の子は E2〜E4 の一般経路 | — | 子の symbolicMode は常に `false`（`childSynthEntry` は `parameters=[]`） |
| E7 | memo | `synthesizeFromConst` の `sparkleSubModuleCache.get`（5335-5339）、`synthesizeChild` の `sparkleChildCache.get`（8930） | hit なら entry の本体に入らず `return cached` | **hit は完了済みの結果だけを返す**（insert は success 後: 5297, 5304, 5323, 5388, 8932）。進行中の宣言は cache に無いので、再入は常に miss |
| E8 | fallback | `synthesizeFromConst` の certified / mixed / machine の前段 5292-5325 が不成立のとき legacy（`openRecordInputs` → `bindInputsLegacy` → `translateExprToWire`）に落ちる | legacy translator の再帰は E2/E3/E5 のみ | entry 呼び出しの新しい経路は見つからなかった |

読んだ範囲で、`synthesizeCombinationalCoreWith` を呼ぶ式は E1（5594, 8943）だけで、E2〜E5 はすべて `childSynthEntry`（5620）か `Rec.synthesizeCombinational`（6332）か `synthesizeChild`（8929）を経由して E1 に着く。Sparkle/ 以下で `childSynthEntry` を使う外部ファイルは見つからなかった（grep）。Tools/ の証明側は entry 定義を引用するだけ。

### 1.2 depth cell / child cache との関係

- `sparkleSynthDepth`（963）: E0 が入口で読んで `depth ≥ 1024` なら throw（5464-5466）、`depth+1` を set（5561）、`finally` で `-1`（5577）。**depth は「入れ子の深さ」であって、どの宣言かを持たない**。
- `sparkleChildCache`（1032）/ `sparkleSubModuleCache`（1024）: depth 0 の入口で `{}` にする（5540-5541）。新しい cell も同じ場所で初期化する。
- 新 cell は depth cell と**同じ寿命・同じ場所**（entry 入口で push、`finally` で pop）に置く。depth cell の意味（well-founded measure、Tools/ShippingChildKeeps.lean）は変えない。

### 1.3 入れ子の失敗を飲む構文（catch / `<|>` / try）の全列挙

Elab.lean の `try … catch`・`<|>`・`observing` の出現を読んで、本文に entry への呼び出し（E1〜E5 の経路）を含むかを調べた（読解）。

| 行 | 内容 | 本文に nested entry を含むか | 扱い |
|---|---|---|---|
| 6358 `catch ex1`、6374 `catch ex2`（`tryInlineUnfold`） | `translateExprToWire eReduced` の失敗を飲み、`restoreWireCaches` して retry / `(none, some ex)` で返す | **含む（E5）** | 飲む。**A では旗が残るので問題にならない**。B では再送出が必要 |
| 6587 `catch _`（hardware_module の子） | 子の失敗を「Sub-module synthesis failed」に**書き換えて再 throw** | 含む（E2） | 失敗は伝わる。専用 error 型は失われる（A は旗に頼るので影響なし） |
| 6599 `catch _`（inline 失敗後の fallback） | 同様に書き換えて再 throw | 含む（E2） | 同上 |
| 5577 `finally`（E0） | depth を戻し per-module cache を復元 | — | 例外を飲まない。stack の pop をここに置く |
| 754, 1928, 1957, 2022, 2143, 6408, 6473, 7024-7025, 7020, 7329-7335, 7829, 7935, 8500 | `whnf` / `inferType` / `getConstInfo` / `inferHWTypeFromSignal` / `mkAppM` / `extractBitVecLiteral` / `reduce` 等の Meta 呼び出しを囲む | 含まない（entry を呼ぶ式なし） | 対象外 |
| 7157-7166 | `extractBitVecLiteral` を囲み、`catch` の腕で `translateExprToWire constValue` | **腕**（catch 本体ではなく handler 側）に translator 呼び出し。handler が投げた例外は飲まれない | 対象外（handler 側は throw が伝わる） |
| 9389 `catch _ => pure ()` | sim ファイル出力（IO） | 含まない | 対象外 |
| `<|>`: 3954, 4657-4733, 4799, 5162 | `Option` の `<|>`（`canonicalNatLitValue?` 等の純関数） | 含まない | 対象外 |
| `observing` | 出現なし | — | — |

「含まない」は読んだ範囲の判断で、E0 を呼ぶ式が catch の本文にあれば表に追加する。実装時に `grep -n "catch\|<|>\|observing\|tryCatch\|orElse"` を再実行して表と突き合わせる（freeze の検査項目、§5 の 1）。

## 2. 変更の設計

### 2.1 状態の置き場所

新規ファイル `Sparkle/Compiler/SynthStack.lean`（Elab.lean は小さく保つ規則に従い、定義と補助を全部ここに置く）。Elab.lean の `import` に 1 行足し、entry に数行足す。

```lean
namespace Sparkle.Compiler.SynthStack
open Lean

/-- いまコンパイル中の宣言名。先頭が最も内側。outermost の入口で空にする。 -/
initialize synthStack : IO.Ref (List Name) ← IO.mkRef []

/-- 再入を一度でも見たら、その宣言名（最初の 1 件）を持つ。catch で戻っても消えない。outermost の入口で none にする。 -/
initialize synthReentry : IO.Ref (Option Name) ← IO.mkRef none

/-- 入口: declName が stack にあれば旗を立てて throw。無ければ push。 -/
def enter (declName : Name) : MetaM Unit := do
  if (← synthStack.get).contains declName then
    synthReentry.modify fun o => o.orElse fun _ => some declName
    throwError "hardware module '{declName}' is re-entered while it is being synthesised (a call cycle)"
  synthStack.modify (declName :: ·)

/-- 出口（成功時）: 旗が立っていれば throw。 -/
def checkNoReentry : MetaM Unit := do
  if let some n ← synthReentry.get then
    throwError "hardware module '{n}' was re-entered during this synthesis (a call cycle)"

/-- 出口（`finally`）: declName を pop。 -/
def leave : IO Unit := synthStack.modify (·.drop 1)

end Sparkle.Compiler.SynthStack
```

`leave` は `drop 1`。`enter` が成功した entry だけが push するので、push と pop は対になる（F3、§3.3）。enter が throw した場合は push していないので `leave` を呼ばない。

### 2.2 entry への差分（素案）

`synthesizeCombinationalCoreWith` 5423、現在の depth 判定（5464-5466）と `doSynth`（5553-5577）の周辺:

```lean
  let depth ← sparkleSynthDepth.get
  if depth ≥ sparkleSynthDepthLimit then
    throwError "hardware modules nested deeper than the synthesis depth limit"
+ if depth == 0 then
+   SynthStack.synthStack.set []
+   SynthStack.synthReentry.set none
+ SynthStack.enter declName          -- 再入なら旗を立てて throw（push 前）
  ...（既存の cache 保存 / depth+1）...
  try
-   doSynth
+   let r ← doSynth
+   SynthStack.checkNoReentry        -- 旗が立っていれば成功させない
+   pure r
  finally
+   SynthStack.leave
    sparkleSynthDepth.modify (· - 1)
    ...
```

- `enter` を depth 判定の**後**・`sparkleSynthDepth.set (depth+1)` の**前**に置くと、enter の throw 時に depth はまだ増えていないので `finally` に入らず、depth の釣り合いが変わらない。そうなるように実装時は `enter` を `try` の外の、`depth+1` の set より前に置く（`enter` が throw したら push も depth も変わっていない）。
- 差分の規模: 新規ファイル約 40 行、Elab.lean は `import` 1 行 + entry に約 8 行。`tryInlineUnfold` / `handleDefinitionUnfold` / `closeInstsM` には**手を入れない**（A の利点）。
- 旗は outermost の入口で none に戻す（depth 0）。これで次の `#synthesizeVerilog` に前の失敗が漏れない。`sparkleSubModuleCache.set {}` などの depth 0 の初期化（5535-5546）と同じ場所。

### 2.3 例外と catch の関係

- `enter` が投げる error は通常の `throwError`（専用の型ではない）。catch に飲まれうるが、**旗が立っているので、飲まれた後に entry のどの階層が成功しても `checkNoReentry` が throw する**。outermost まで、成功で戻ろうとする各 entry が 1 つずつ落ちる。
- 「専用の例外」は A では必須ではない。案内（エラー文）に使う。旗が真の保証。ユーザーが見るエラー文は最初の再入の宣言名を含む（`synthReentry` の値）。

### 2.4 正常な（循環しない）コンパイルの出力が変わらない理由

出力は design と module の値だけで、新しい cell は出力に書かれない。差が出うるのは control flow（throw するか）だけで、throw は次の場合に限る:

- (a) `enter` が `declName ∈ stack` で throw: 入れ子の同じ宣言への再入。循環しない（呼び出しが DAG の）コンパイルでは stack に同じ名前が 2 度現れないので起きない。同じ宣言を 2 回呼ぶ（diamond、同じ子を 2 つの field で使う）場合は、1 回目が `leave` で pop された後に 2 回目が来るので再入ではない（F3）。
- (b) `checkNoReentry` が旗で throw: 旗は (a) でしか立たない。
- (c) **差が出る唯一の場合**: 今のコンパイラでは、再入を含む試行が `tryInlineUnfold` の retry で救われ、または depth 上限 1024 に達する前に成功する設計。これは循環を含むので「正常な（循環しない）コンパイル」ではないが、**今成功しているものが失敗に変わる**。今の成功が循環を含むかは、読解では判断できない（FB_HNO_STUDY §2.3: 反例は作れていない）ので、**corpus 測定（§4）で 0 件を確認する**。出れば止めて報告する。

その他の副作用: `enter` / `leave` は IO.Ref の読み書きだけで、`CircuitState` にも既存の cache にも触れない。`synthStack` / `synthReentry` は他の cell と共有しない。`finally` の順序（pop → depth → cache 復元）は、既存の復元が独立した cell なので出力に影響しない。

### 2.5 比較: B（catch ごとに再送出）を採らない理由

B は専用の例外型を作り、`tryInlineUnfold` の 2 つの catch で「その型なら再送出」にし、6587 / 6599 の書き換え catch も「その型なら通す」にする。必要な catch を 1 箇所でも落とすと穴になり、将来の catch の追加でも壊れる。証明も「各 catch が再送出する法則」を Tools/ShippingChild* の `tryInlineUnfold` の walk に足すことになる。A は旗が単調で、catch の形に依らない（F1）。A を採る。B は旗の保険として併用しない（二重になるだけ）。

### 2.6 新 cell が process-global であることの調査（reviewer 指摘 (2)）

問い: 同じ process の中で、2 つの top-level 合成（outermost の `synthesizeCombinationalCoreWith`）が時間的に重なりうるか。重なれば `synthStack` / `synthReentry` が共有されて壊れる。「既存の depth が global だから」は根拠にしない。以下は**読んだ範囲の事実**（toolchain は `leanprover/lean4:v4.32.1`、ソースは `~/.elan/toolchains/.../src/lean` 相当の toolchain ディレクトリ。以下パスは `Lean/` 以下）。

**(a) top-level 合成を起動するのは command だけ（sparkle 側）**:
- `elab "#synthesizeVerilog" …`（Elab.lean:8999 → `liftTermElabM` 内で `synthesizeCombinational`）、`#synthesize` 8969、`#showVerilog` 9074、`#synthesizeDesign` 9136、`#synthesizeVerilogDesign` 9145、`#writeVerilogDesign` 9155、`#writeCppSimDesign` 9168、`#writeCudaDesign` 9217 以降、`#writeDesign` 9324/9332、`#sim` 9369、`elab_rules` 9045/9186/9235、`#showDiagram` / `#showDesign`（Sparkle/Display/Synthesise.lean:65, 80）、`#verify_cost` / `#verify_fpga`（Sparkle/Verification/CostCmd.lean:53-59, 82-88、`@[command_elab]`）。すべて `command` で、term/tactic/theorem-body から呼ぶ経路は Sparkle/ には見つからなかった（`synthesizeCombinational*` / `synthesizeHierarchical*` / `synthesizeChild` の呼び出し元を grep。Tests/ の `theorem … (hcore : RunsTo (synthesizeCombinationalCore …) …)` は**命題の中の項**で、実行されない）。
- `Task` / `IO.asTask` / `Elab.async` / `wrapAsyncAsSnapshot` / `BaseIO.mapTask` / `Task.spawn` は Sparkle/ に出現しない（grep、0 件）。

**(b) `initialize` の cell は process ごと**: `initialize … : IO.Ref … ← IO.mkRef …`（Elab.lean:963, 1024, 1032, 1040 等。新 cell も同じ形）は、その module の initializer が process 内で一度走ったときの `IO.Ref`。thread ごとでも command ごとでもない。したがって同じ process の全 elaboration thread が同じ cell を見る。

**(c) 1 つのファイルの command は逐次**: `Lean/Language/Lean.lean` の `doElab`（751）は `Elab.Command.elabCommandTopLevel` を **await する形で呼び**（679）、その後に次の command の `parseCmd`（749）が来る。1 つの `lean FILE` の中で、command は parse → elab → parse → elab の鎖で、2 つの command の elab は重ならない。`Lean/Elab/Frontend.lean:266` は `Elab.async` を既定 true にする。`Elab.async` が非同期にするのは `Lean/Elab/MutualDef.lean:1238-1331` の **theorem の本体**（`view.kind.isTheorem`）と、`Command.lean:363` の linter、kernel / codegen の task で、**`elab` で定義した command の本体は含まれない**。つまり command の elaborate は main の鎖で実行される。

**(d) `lake build` の module 単位の並行は別 process**: `lake/Lake/Build/Actions.lean:28-48` の `compileLeanModule` は module ごとに `lean` を別 process として起動する（`lean : FilePath := "lean"`）。process が違えば `IO.Ref` も別。重ならない。

**(e) 重なりうる経路（この調査で閉じられなかったもの）**:
1. **language server（編集で再 elaborate）**: 編集で古い command の task は cancel token を立てられるが、cancel は協調的（`Lean/CoreM.lean:463-464` の `checkInterrupted` が `cancelTk?` を見る。`checkSystem` 496-498 経由）。`checkInterrupted` を通らない区間の間は古い合成が走り続け、その間に新しい鎖が同じファイル worker process で `#synthesizeVerilog` に到達しうる。**cancel が効くまでの窓で 2 つの合成が重なる可能性は、この調査では除外できなかった**。worker が 1 file 1 process であること自体は、server ソースを私は読んでいない（未確認）。
2. **非同期な theorem body から合成を呼ぶユーザー tactic / `run_meta`**: 上の (c) のとおり theorem の本体は別 thread で走りうる。repo には見つからなかったが、**ユーザーがそう書くことは妨げられていない**。

**結論**: 通常の `lake build` / `lean FILE` 実行では、読んだ範囲で重ならない。**重ならないことを保証する根拠は、server の cancel の窓と非同期 theorem body の 2 点で見つからなかった**。

**既存の cell との関係（報告のみ・扱いは変えない）**: `sparkleSynthDepth`（963）、`sparkleChildCache`（1032）、`sparkleSubModuleCache`（1024）、`sparkleFvarValueMap`（986）等、depth 0 で `set {}` する既存 cell は**すべて同じ「process-global・単一合成を仮定」の問題を持つ**。重なれば depth の釣り合い・cache の混入・出力 design の混入が既に起きる。つまり新 cell が新しい種類の露出を足すのではなく、**既存の仮定（単一スレッドの合成）に依存する cell が 2 つ増える**。証明側も `Start`/`JQC` が 1 つの world `w` を逐次に走らせるモデル（`RunsTo`）で、並行を表していない。

**設計の選択（reviewer / ユーザー判断が要る点を含む）**:

| 案 | 内容 | 利点 | 費用・影響 |
|---|---|---|---|
| A-global（rev1 の設計） | process-global cell（§2.1） | 差分が約 10 行。`Start` に 2 欄足すだけ | 上の (e) の 2 経路で重なれば壊れる。既存 cell と同じ露出 |
| A-local（invocation-local） | outermost の入口で `SynthRun`（stack と tripwire の 2 つの新しい `IO.Ref`）を作り、引数で持ち回す | 合成 1 回ごとに独立。(e) の重なりでも他の合成の stack を壊さない | `synthesizeCombinationalCoreWith` / `childSynthEntry`（5620）/ `sparkleChildSynth` の型（現在 `Name → MetaM Res`）/ `synthesizeChild` の引数が増える。`sv w = some synthesizeChild`（`JQC`、Tools 側の定義と証明）が型ごと変わる＝**共有定義の変更**で、ユーザー承認が要る。この単位ではやらない |
| A-thread-local | `Task` / thread id をキーにした map | 既存の型を変えない | Lean に標準の thread-local は見つからなかった（この調査では）。map は結局 global cell。thread id（`IO.getTID`）が同じ task 内で安定する保証は未確認 |

**推奨**: 「重なる経路を閉じられなかった」ので、本来は A-local が安全側。ただし A-local は `sparkleChildSynth` の型と `JQC` を含む共有定義を変えるため、この rev2 では**設計を A-global に固定したまま、(e) の露出を既存 cell と同列の既知の制限として明記**（§7）し、**A-local への移行は reviewer / ユーザーの判断事項として残す**。A-local を選ぶ場合、本文書の §2.1/2.2/3 は引数持ち回しに書き直す（`StartNR` は `Start` のままで済み、(6)(7) の欄は消える）。どちらも**既存の cell の扱いは変えない**。**可逆性**: A-global → A-local は、実装前なら文書の変更だけ。実装後は共有定義の変更。**判断しない場合**: A-global のまま実装に進むが、server 経路の重なりは未解決の制限として残る。

## 3. 供給定理の完全な型

### 3.1 対象

`hno` は `Tools/ShippingDesignWriterRun.lean` の仮説（FB_HNO_STUDY §2.2）:
`hno : ∀ x ∈ D.modules, x.name ≠ raw.name`。outermost の core run の結果 `(raw, D)` について、`raw.name = ofDecl declName`（FB_HNO_STUDY §1 の `htop_core` の第一成分）と合わせて、次の形にする。

### 3.2 開始状態 `StartNR` と定理（まだ定理ではない。freeze 候補の型）

**`StartNR`（新規ファイル `Tools/ShippingGen4Cycle.lean` に置く。`Tools/ShippingGen2Defs.lean` の `Start` は編集しない）**。既存の `Start`（Gen2Defs.lean:52 = `AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w`。`JQC` は ChildCacheA.lean:120: quiet、`sv w = some synthesizeChild`、`dv w = 0`、cache 半分 `CacheInvA`）に、新 cell の 2 欄を足す:

```lean
def StartNR {mref cref} (L : Laws mref cref) (mctx : Meta.Context) (cctx : Core.Context)
    (w : Void IO.RealWorld) : Prop :=
  Start L mctx cctx w ∧ readOf synthStack w = [] ∧ readOf synthReentry w = none
```

開始状態の全欄（展開後）: (1) `AdmCtx L.O.quiet mctx cctx`（contexts が admissible）、(2) `quiet w`、(3) `sparkleChildSynth` の中身 `= some synthesizeChild`、(4) **depth `dv w = 0`**、(5) cache 初期条件 `CacheInvA L.O (cv w)`（`sparkleChildCache` の中身は real-child の entry だけ）、(6) **`synthStack` の中身 `= []`**、(7) **`synthReentry` の中身 `= none`**。

注意（正直に）: entry は depth 0 で (6)(7) を自分でリセットする（§2.2）ので、証明の中身は (6)(7) を使わなくても立つ見込み。それでも (6)(7) を前提に含めるのは、reviewer 指摘どおり開始状態を明示するため。**前の失敗した top-level 合成が旗を立てたまま残した world は `StartNR` を満たさない**（旗は sticky）。その場合 `hno_of_noReentry` は適用されず、リセット後の世界に対する別の補題（`StartNR` を entry のリセット後の world に取る）が要る。どちらを使うかは実装時に reviewer と詰める。この段階では「完全な型の固定」を優先し、強い前提（(6)(7) 付き）で固定する。

**scratch での確認**: `StartNR` と、これを使った定理の文そのもの（`def … : Prop`、証明なし、sorry なし）を、新 cell を `initialize` で同じ形（§2.1）に置いた scratch で elaborate した。`kjob lake env lean`（rt160、Lean 4.32.1）、exit 0、`#print axioms` は `[propext, Classical.choice, Quot.sound]` のみ。scratch はソースツリー外（scratchpad）で、抜粋のみ引用する:

```lean
def StartNR {mref cref} (L : Laws mref cref) (mctx : Meta.Context) (cctx : Core.Context)
    (w : Void IO.RealWorld) : Prop :=
  Start L mctx cctx w ∧ readOf synthStack w = [] ∧ readOf synthReentry w = none

def HnoOfNoReentryStmt : Prop :=
  ∀ {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (declName : Name) (mctx : Meta.Context) (cctx : Core.Context)
    (w w2 : Void IO.RealWorld) (raw : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    StartNR L mctx cctx w →
    RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w2 →
    raw.name = Sparkle.IR.ModuleName.ofDecl declName →
    ∀ x ∈ D.modules, x.name ≠ raw.name
```

（これは文の型検査で、証明ではない。`synthesizeCombinationalCore` は現行の定義で elaborate した。変更後の定義は同じ名前・引数。）

定理（上の `StartNR` を使う形。binder の順は scratch と同じ）:


```lean
theorem hno_of_noReentry
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) {declName : Name} {mctx : Meta.Context}
    {cctx : Core.Context}
    {w w2 : Void IO.RealWorld}
    {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hstart : StartNR L mctx cctx w)   -- outermost の開始状態（下の `StartNR`。全欄を明示）
    (hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w2)
    (hname : raw.name = Sparkle.IR.ModuleName.ofDecl declName) :
    ∀ x ∈ D.modules, x.name ≠ raw.name
```

（`synthesizeCombinationalCore` は変更後の定義。名前・引数は変えない。）これに `hno_iff_not_any`（FB_HNO_STUDY §2.2）を合成して、`synthesizeHierarchical` が `addModule` 分岐に入ることを得る。**これは D.E-12 の `hno` 側だけ**で、`htop` の legacy 分が残るので、行は部分供給（0）。

### 3.3 証明の構成と新しく要る事実

1. **F1（旗の単調性）**: entry の run の間、`synthReentry` が `some n` になったら run の終わりまで `some`。理由: `synthReentry` に書くのは `enter`（`orElse` で上書きしない）と depth 0 の入口の `set none` だけで、後者は outermost の最初にしか実行されない（nested は `depth ≥ 1`）。`Keeps` 型の不変量（`I w := synthReentry.get w = some n → …`）で、`@[keeps]` の walk に載せる。**この cell を書く式は新ファイルの 2 つと entry の 1 行だけ**。他の handler が cell を触らないこと（IO.Ref の名前が新しいので、既存の `@[keeps]` 補題は `I` を変えないと分かる）を使う。
2. **F2（design の module 名の出自）**: run の結果 `(raw, D)` について、`D.modules` の各 module の name は `ofDecl k`（`k` は run の途中で `enter` された宣言）か、`ofDecl` と異なる系（`ofMem`、aux: `ofDecl_ne_ofMem`、`ofDecl_ne_aux` が既存）のいずれか。入れ子の design が `addModuleToDesign`（Elab.lean 6625, 6628, 8519, 8561）で親へ合流する箇所と machine の `closeInsts` / `designWith`（Tools/ShippingCacheCoherentCert.lean 系の `IsMem a ∨ IsTop`）を覆う帰納法。**machine route には既存の出自不変量があり、非 machine の legacy / certified の合流（6625-6628, 8519, 8561）に同じ形の補題を足す**。F2 は規模が最も大きい（addModule の全 4 箇所 + closeInsts 側の既存定理の再利用）。
3. **F3（stack の釣り合い）**: entry の成功 run の前後で `synthStack` は同じ。`enter` が push、`finally` が `drop 1`。nested の run が失敗しても `finally` が pop するので、例外経路でも成立する。`declName ∈ stack` ⇒ `enter` が throw、は定義から。

組み立て: 成功した outermost run で、(i) F1 と `checkNoReentry` により、run 中に旗は立たなかった。(ii) 旗が立たないので `enter` は throw しなかった、すなわち nested の `enter k` は毎回 `k ∉ stack`。(iii) outermost の stack は `[declName]` から始まるので、nested の `k` で `k = declName` のものは無い（`k ∈ stack` になる）。(iv) F2 から `D.modules` に `ofDecl declName` の名前の module があれば、`k = declName` の nested `enter` があったことになり矛盾。(v) `ofDecl_injective`（766）で名前の等号から宣言の等号を得る。(vi) `raw.name = ofDecl declName`（`hname`、htop 側の成分）から結論。

**使う既存定理**: `ofDecl_injective`、`ofDecl_ne_ofMem`、`ofDecl_ne_aux`（Tools/ShippingModuleName.lean）、`hno_iff_not_any`（FB_HNO_STUDY §6 の scratch。freeze 後に Tools の新ファイルへ）、`finishSynth_returns`（Tools/ShippingEntrySoundness.lean:521）、machine 側の出自不変量（Tools/ShippingCacheCoherentCert.lean）。
**新しい TRUSTED / law**: なし（F1〜F3 は定理として証明する）。**止まる条件**: F2 の walk が、`RefLawsM`（保留）や memo 法則、新しい仮説なしでは立たないと分かった場合は、実装を止めて判断資料にする。
**この定理が供給しないもの**: `htop` の legacy 分（circuit state を追う walk、FB_HNO_STUDY §1.3）。D.E-12 の「htop」は未解決のまま。

## 4. 測定計画（この単位では実施しない）

- 対象: scripts/shipping-coverage の corpus。手順は既存の `design_sweep.sh`（出力を `WORK/out` に出す）と `compare_outputs.py OLD_WORK/out NEW_WORK/out`。
- 手順: (1) 変更前（base = 8714354b）のコンパイラで corpus 全体の出力を `OLD_WORK` に作る。(2) 実装 commit で同じ手順を `NEW_WORK` に作る。(3) `compare_outputs.py` で design ごとにバイト比較。ログ・測定データはソースツリーに置かない（scratchpad）。
- **止める条件**: (a) 1 件でも出力が変わる、(b) 今成功している設計が新しいエラー（再入）で失敗する、(c) corpus 以外の `Tests/` の合成で今成功しているものが失敗する。いずれも止めて報告し、続行はしない。変更後に失敗した設計は「循環の実例」か「retry で救われていた設計」かを、失敗の宣言名と stack で個別に調べて記録する（意味的反例を言い立てない）。
- 期待: 全件一致。`hno` の観測（FB_HNO_STUDY §2.4: 直接の自己再帰 1 例は depth 上限で throw）は、変更後は再入エラーに変わるので、その例は**意図した差**として別枠で記録する（corpus には無い見込み）。
- 性能: `enter` は `List.contains`（深さ ≤ 1024、実際は数段）。corpus の時間差を同じ sweep で測る（目安: 有意差なし）。

## 5. 検査項目と進め方

1. freeze 承認前の確認（実装者が実装の最初にやる）: §1.3 の grep の再実行、entry を呼ぶ式が E1 のみであることの再確認。表に無い入口が出たら止まって報告。
2. 実装は新規 `Sparkle/Compiler/SynthStack.lean` + Elab.lean の約 10 行。**コンパイラの編集は freeze の承認後**（この文書は承認の前）。
3. 実装 commit では clean build はしない（coder が実行）。証明（F1〜F3、`hno_of_noReentry`）は別の単位で、manifest 付き proof-accept の対象にする。
4. 実装の順序: (i) SynthStack.lean + entry 差分 + corpus 出力不変（§4）。(ii) F3 → F1 → F2 → 定理。(iii) reviewer 承認後に台帳へ。

## 6. 台帳の差分

| 行 | 現状 | 今回 | 見込み |
|---|---|---|---|
| D.E-12（G7 の `hno` / `htop`、1 行） | M4 の義務（現在行ではない） | 0 | `hno` の非 machine 分を供給しても `htop`（legacy は未解決）が残る限り**部分供給で 0**。−1 にしない。`htop` も立ったときに reviewer が判断 |
| 新しい仮定（FG） | — | +0 | F1〜F3 は定理。F2 が立たなければ止まる |
| T1 | 57 | 0 | 触らない |
| 新しい TRUSTED / law / compiler 境界 | — | なし | **コンパイラ変更そのもの**はユーザーが承認済み（M4_DECISION §7）。出力が変わらないことを §4 で測る |

台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。条件付き台帳: なし。

## 7. 限界

- この文書は設計と型の freeze で、Lean は書いていない。§1.1・§1.3 の表と §2.4 の「出力が変わらない」は読解で、**実装前の確認項目**（§5 の 1）と corpus 測定（§4）で確かめる。
- A は「再入を見たら必ず失敗」を保証するが、**循環が無い設計が失敗に変わらない**ことの保証は §2.4(a) の読解と §4 の測定だけ。変更により今成功している設計が失敗する場合は、ユーザーの判断（M4_DECISION §7: 出力が変わったら止める）に戻る。
- F2 の規模は見積もれていない（addModule 4 箇所 + closeInsts 側の再利用）。着手後に規模が大きいと分かれば、止まって note に書く。
- `htop` の legacy 分、(2c) legacy shim、memo 法則家族（項目 3）はこの文書の範囲外。
- **rev2 追記**: 新 cell が process-global であることの重なり（language server の cancel の窓、非同期 theorem body から合成を呼ぶユーザー tactic）は閉じられていない（§2.6 (e)）。既存の cell と同じ露出で、この文書は A-global を固定する。A-local への移行は共有定義（`sparkleChildSynth` の型、`JQC`）の変更になるので判断事項（§2.6 の表）。

## 8. rev2 で直した点（reviewer 指摘ごと）

| 指摘 | 直した所 | 内容 |
|---|---|---|
| (1) `Start` が「freeze 後に写す」のまま未定義 | §3.2 | `StartNR` を完全な型で固定。欄: `AdmCtx`、quiet、`sv = some synthesizeChild`、**depth 0**、cache 初期条件 `CacheInvA`、**`synthStack = []`**、**`synthReentry = none`**。定理の文そのものが `StartNR` を使う形に変更。scratch で elaborate（exit 0、axioms は propext / Classical.choice / Quot.sound のみ、sorry なし）。注意: sticky 旗が残った world は `StartNR` を満たさない（entry は depth 0 でリセットする）旨を明記 |
| (2) 新 cell が process-global な `IO.Ref` | §2.6（新設）、§7 | 起動する command の全列挙、`initialize` の寿命、Lean の `doElab` が command を逐次に走らせること（Language/Lean.lean:679, 749）、`Elab.async` が theorem 本体に限られること（Frontend.lean:266, MutualDef.lean:1238-1331）、`lake build` は module ごとに別 process（Lake/Build/Actions.lean:28-48）を、ファイルと行で記載。**閉じられなかった経路**: server の cancel の窓と非同期 theorem body。既存 cell（depth / child cache / memo）も同じ問題を持つことを報告（扱いは変えない）。A-global / A-local / A-thread-local の比較表と推奨 |

台帳: FG 91 / T1 57（今回 FG -0 +0 / T1 -0 +0）。新前提 0。D.E-12 は hno / htop の 1 行で、hno だけの供給は部分供給 0。
