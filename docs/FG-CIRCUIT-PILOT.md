# FG 回路の核 S1 パイロット（Issue `sparkle-fg-circuit-pilot`）

土台 `ff3d31c6`（par/fgc）。戦略: `docs/FG-CIRCUIT-STRATEGY-2026-11-06.md` §4–§7。S1 は方式の検証であり、**FG の完了ではない**（台帳 FG 75 / T1 57、今回 FG -0 +0 / T1 -0 +0）。
追加ファイル: `Tools/ShippingFGCircuit.lean`、`Tools/ShippingFGCircuitRoots.lean`、`Tests/Gen5/FGCircuitPilotCheck.lean`、本書。既存ファイルは書き換えていない（lakefile への追記のみ、最初の commit で 1 回）。
新しい TRUSTED・axiom・sorry・native_decide はない（`#print axioms` は全て `propext, Classical.choice, Quot.sound`）。

## 1. 結論の型（先に固定）

概念上の形:

```
compileCircuit env source params = .ok artifact
  → ∃ sourceMeaning, SourceDenotes env source params sourceMeaning ∧ HasConcretePackage artifact ∧ ObservationsEqual sourceMeaning artifact
```

Lean での対応（`Tools/ShippingFGCircuit.lean`）:

| 概念 | Lean | 既存の FG 型との対応 |
|---|---|---|
| `compileCircuit … = .ok artifact` | `EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D`（`artifact = (b, D)`、`env = envAt cref w`） | `FGLedgerPremisesStmtH` の外側の前提そのもの（新しい仮定なし） |
| `SourceDenotes env X params sh m` | `params = [] ∧ ∃ ci, env.find? X = some ci ∧ shapeOf ci = some sh ∧ CircCV env X sh.Ty m`（定義域が固定された宣言には `SourceDenotesMono`） | `DeclConnect` の `CV env X sh.Ty v`。**`CV` を binder から具体的な `CircCV` に置き換えた** |
| `HasConcretePackage` | `p.decl = declName ∧ TopShips p n declName b raw D` | H の第 3 連言 `TopShips`（全入力列・全 `T`、clk/rst は `b` の入力として扱う既存契約） |
| `ObservationsEqual sh m p` | `ShapeMatches sh p.d p.kD ∧ ∀ i bools bits, sh.obs m i bools bits = p.src i bools bits`（定義域固定: `ObservationsEqualMono`、位置は 0 から） | `DeclConnect` の `ShapeMatches` と `ObsC` |
| 全体 | `FGCircuitConclusion env P Post declName parameters b D` | H の結論の後半（`∃ raw, Post` と `P declName = some p` と `TopShips`）に `SourceDenotes`/`ObservationsEqual` を同じ `p` で束ねたもの |
| 対応定理 | `fgCircuit_of_H : FGLedgerPremisesStmtH → … → FGCircuitConclusion …`（H は未証明。参考部品）（`genP_decl` で `p.decl = declName`、`declConnect_mono` で `TgtRun` から top へ） | H から S1 の結論が出る。追加の前提は `parameters = []` のみ |

`SourceDenotes` は生成出力・package・IR から定義していない。引数に `Pkg` も `Module` もない（`Tests/Gen5/FGCircuitPilotCheck.lean` の `rfl` 照合）。元ソースの宣言の値の `Expr` を、Signal/BitVec の適用単位の意味 `CD`（§3）で読んだ値が意味である。
clock / reset: `TopShips` の既存契約（`clk`/`rst` が `b` の入力にあれば全時刻 0、レジスタは reset 値 `f.init` から開始）。**reset を assert した挙動は S1 の主張に含まれない**（ソースの `Signal.register` に reset がないため、IR の reset 分岐は意味の外）。

## 2. 部品の出所（SHA）

| 部品 | 出所 | 使い方 |
|---|---|---|
| `Dyn` / `Entry` / `Val` | par/dd4-int `fe106963` の `Tools/ShippingGen5ConstValueE.lean`（変更なし） | `CD` の環境の型だけ。**ConstValueEKey/ES/ESProof/EV など他の 7 ファイルは持ち込んだが未使用**（下記の理由）。 |
| 組立 | `5e5c9bd2`（土台に含まれる）、`SM1`（H） | `fgCircuit_of_H` の入力（H）としてだけ使う |
| 3 root の測定 | `e37da005` §Trace | 3 root の選択と「停止して再帰子 0」の確認（`Signal.*`/`BitVec.*` を展開しない） |
| 宣言ごとの端点 | 既存の `#machine_endpoint`（`Tools/ShippingMachineCommand.lean`） | 既存の reader/genData → IR の経路。各 root で `X.machine_sound` / `X.machine_ships_wired` を生成（kernel の `Eq.refl` 検査） |
| Q-B shard / Q-C | 未使用（`d4shard 20772d29` / `d4qc 3616089c`）| 今回の 4 root は shard を要しない |

**CVEKV を使わなかった理由（実測した事実）**: `CVEKVB.prim` と `TDenV.tcon` は `¬ IsDefn env c` を要求するので、`Signal.register` / `Signal.loop` / `Signal.mux` / `BitVec.ofNat`（すべて `defnInfo`）を「停止する prim」にできず、`unfold` すると `Signal.loop` が `loopGo`（整礎再帰）に入る。また `HAdd.hAdd` は射影関数（`defnInfo`）で、`unfold` すると値が `Expr.proj` になるが `CVEKV` に `proj` の規則がない（規則一覧を読んだ結果。導出を実際に試したのではない）。したがって e37da005 の「停止 7 key」は今の `CVEKV` の規則では導出できない。パイロットは、**適用単位の規則**（定数・level・引数すべてを 1 規則で認識する）を持つ小さい関係 `CD`/`TD` を新設した。`CVEKV` の関数性・弱化の証明は流用していない（`CD` の関数性は未証明、§6）。

## 3. 具体化した primitive（適用の単位）

`CD ρ e α v`: 式 `e` が Lean の値 `v : α` を意味する（`Type 0` のみ）。型は `TD`。規則は 1 つの完全な適用に 1 つ。値は**同じ Lean 定数**で作る（IR からではない）。表の行だけでは意味を与えたことにならないので、各行に証明を付けた（`primTable`、`Check` で「各証明が存在し標準 axiom のみ」を検査）。

| 宣言 / level | 引数 | 結果型 | 値の意味 | IR 演算 | 時相・reset | 証明 |
|---|---|---|---|---|---|---|
| `OfNat.ofNat.{0}` | `Nat, lit n, instOfNatNat n` | `Nat` | `n` | なし（静的） | 静的 | 規則 `natLit` |
| `BitVec.ofNat` | `w, n` | `BitVec w` | `BitVec.ofNat w n` | `Expr.const n w` | 静的 | `ir_const_agrees`（IR の `evalExpr (.const n w) = (BitVec.ofNat w n).toNat`） |
| `Signal.pure.{0}` | `dom, T, a` | `Signal dom T` | 全時刻 `a` | const/ref | 全 cycle 同値 | `pure_val`、`ir_const_agrees` |
| `Signal.register.{0}` | `dom, T, init, s` | `Signal dom T` | `t=0: init`、`t+1: s t` | `Stmt.register out clk (rst,k) in init` | cycle t ↔ IR cycle t。`rst` は 0 に固定（`TopShips`）。開始値は slot の init | `register_val_zero`、`register_val_succ`、`ir_register_step_rst0`、`ir_register_reset_value` |
| `Signal.mux.{0}` | `dom, T, c, a, b` | `Signal dom T` | `if c t then a t else b t` | `Expr.op .mux [c,a,b]`（Bool は 0/1） | 組合せ | `mux_val`、`ir_mux_agrees` |
| `HAdd.hAdd.{0,0,0}`（`instHAddSignalBitVec dom w`） | `S,S,S,inst,a,b` | `Signal dom (BitVec w)` | `a t + b t`（mod 2^w） | `Expr.op .add [a,b]`（幅 w でマスク） | 組合せ | `addBV_val`、`ir_add_agrees` |
| `Signal.loop`（level なし） | `dom, T, Inhabited T, f` | `Signal dom T` | `loopGo f`（`Signal.loop` の純粋な定義。`implemented_by` は実行だけ） | レジスタ帰還（ループ変数 = レジスタ出力線） | t=0 は register の init、t+1 は cycle t を読む | `loop_val_zero`、`loop_register_map_succ`（`register i (map h s)` の形で `val (t+1) = h (val t)`） |
| `Signal.beq`（`instBEqOfDecidableEq (instDecidableEqBitVec w)`） | `α, dom, inst, a, b` | `Signal dom Bool` | `a t == b t` | `Expr.op .eq` | 組合せ | 規則 `sigBeqBV`（IR 側の一致は**この S1 では個別の補題を置いていない**: 端点の `machine_sound` に依る、§6） |
| `HAnd/HOr/Complement`（`instH…SignalBool`） | `S,S,S,inst,a,b` / `S,inst,a` | `Signal dom Bool` | `&&`, `||`, `!`（時刻ごと） | `.and/.or/.not` | 組合せ | 規則 `sigAndBool/sigOrBool/sigNotBool`（同上） |
| `let`/`have` | — | — | 束縛値を評価して環境に積む | なし | — | 規則 `letE` |
| `lam` | — | 依存関数型 | `fun a => …`（全称前提） | なし | — | 規則 `lam`（結果型が束縛変数に依存してよい: `(dom : DomainConfig) → …`） |
| `stIdle/stGrantA/stGrantB`（`abbrev … : BitVec 2`） | — | `BitVec 2` | `0#2/1#2/2#2` | `Expr.const` | 静的 | **具体的な境界** `bvAbbrevRow`（3 行、宣言の本体がそのリテラルであることを `FGCircuitPilotCheck` の meta 検査で照合。kernel では証明していない） |

per-cycle の合成（状態の受け渡し、`runModuleTG` の cycle 順、`Signal.loop` を register 帰還として読むこと全体）は、端点が使う既存の生成定理 `machine_trace_of_loop` / `machine_trace_of_data` に依る。パイロットはそれを再証明していない。

## 4. 元ソースから出力までの条件付きの接続（4 本）

対象: `Tests.SignalLoopTest` の `counterLoop` / `shift4Loop` / `counterEnableLoop`（D.D-4 e37da005 の 3 root）と、S0 の一覧が土台になかったので**フォールバックとして選んだ実 IP `Sparkle.IP.Arbiter.RoundRobin.arbiterSignal`**。理由: 出荷されている `IP/` の宣言で、Signal/BitVec の核（`loop/register/mux/===/&&&/|||/~~~`/`let`）だけで書かれ、定義域多相（既存の `shapeOf` の経路）、入力 2 本、状態ループ、出力 2 ビットを持ち、`#machine_endpoint` が通る。

各 root `X` について（`Tools/ShippingFGCircuitRoots.lean`。**公開する形は S1b の `X_root_at` / `X_ships_at`（`Tools/ShippingFGCircuitRootsAt.lean`、§6a）**。ここの `X_root` は env が run と独立の自由変数で、内部の部品として残す）:

1. `X_cd : CD [] <X の値の Expr> <型> X` — 値の `Expr` が `CD` で読め、読んだ値が**宣言 X そのもの**（`Signal.loop …` の unfold は kernel の delta で `rfl`）。3 root は手で組み、arbiter は `quote_value%`（宣言の値を `Expr` 項に引用）と `cdt` 戦術で導出。
2. `X_root`: 前提 `RootInEnv env X 型 値 d`・端点の run・`MachineDefines`・`MachineCloses` の下で
   `∃ mm, SourceDenotes(Mono) env X [] sh mm ∧ MachineTrace X X.machineData m dom (fun i bools bits => obs sh mm i bools bits)`。
   端点の `X.machineSource` は宣言自身の観測であり、`obs sh mm` と一致する（型が defeq で通る）。
3. `X_ships`: 同じ前提（`synthesizeCombinational`、`machine_ships_wired`）で、印字される module `b`（`dropZeroWidthModule`/`mergeChecked`、`checkedOptimize`、emit した Verilog の seq 検査）についての `MachineShips`。ソースは同じ観測。

`fgCircuit_of_H` は、生成表 `genGP` を通る一般の経路（`EntryWitness` からの `TopShips` と `DeclConnect CircCV`）が上と同じ結論の形になることを示す。**4 root の端点経路（`MachineTrace`）と `genGP` 経路（`Pkg`/`TopShips`）の統合は未実施**（§6）。

非自明性の確認（`FGCircuitPilotCheck`）: 引用した 4 つの値・型が実環境の宣言と `==`（meta）、`bvAbbrevRow` の 3 行が宣言のリテラルと `==`（meta）、`wrong_meaning_refused`（`shift4Loop` の観測は、常に 0 を返す偽の意味と同じ package で両立しない）、`params` が非空なら拒否、`Post := False` なら拒否、未知の定数は `CD` に入らない。

## 5. 実行結果

- build: `kjob lake build Tests.Gen5.FGCircuitPilotCheck`（exact-head と結果は Issue note）。
- S1b: `kjob lake build Tests.Gen5.FGCircuitPilotCheckAt`（`FGCIRCUIT SIGNATURES` / `SNAPSHOT` / `AXIOMS-AT` 行、§6a）。
- 出力行: `FGCIRCUIT META: 4 quoted roots equal the environment; 3 abbreviation rows equal their literals; machine_closes and machine_ships_wired exist for the 4 roots`、`FGCIRCUIT PRIMS: 7 rows, 13 proof references, all exist`、`FGCIRCUIT AXIOMS: … standard axioms only`。

## 6. 未解決の仮説（名前付き）と次に閉じる束

root 定理の前提（隠していない）:

| 名前 | 内容 | 状態 |
|---|---|---|
| `RootInEnv env X ty val d` | run の環境に `X` が型 `ty`・値 `val`（引用）で入っている | 実環境との一致は meta 検査のみ（kernel は環境を見ない）。`ENV/cache` の束（S2）に載る |
| run / `MachineDefines` / `MachineCloses` | 実行 `RunsTo (synthesizeCombinationalCore X [] false)`。`closes` は `X.machine_closes` がデータから出る（`closeEndpoint`）が、root 定理の前提としては置いたまま | S2（成功検査から導出） |
| 端点経路 ↔ `genGP` 経路 | root は `MachineTrace`/`MachineShips`、一般は `Pkg`/`TopShips`。`SrcPkg` を端点から作り `StepStmt` で `TopShips` に上げる接続は未実施 | S2 |
| `fgCircuit_of_H` の入力（未証明の H。FG 本体の根拠に数えない） | `FGLedgerPremisesStmtH`、`ReflectsAll Post lvl genData₀ L h_C_EN4 h_C_RK6 h_C_CV4`、内側の `h_A_P06`/`h_D_T4` | 既存の束のまま（FG 75 / T1 57 は減らしていない） |
| `ConstValueFunctional CircCV` | H の第 1 連言として H が出力する。`CD` の関数性は**未証明** | S2。`CD` は規則が構文で決まるので、証明は規則ごとの場合分けで済む見込みだが未測定 |
| `parameters = []` | S1 は記号パラメータなし | 必要 IP の一覧（S0）が出たら判断 |
| `bvAbbrevRow`（3 行） | 具体的な境界。値の一致は meta 検査 | 本体のリテラルを `unfold` する規則（環境つきの `CD`）に置き換えれば消せる |
| `sigBeqBV`/`sigAndBool`/`sigOrBool`/`sigNotBool`/`natLit` の IR 側の個別補題 | `machine_sound` の `Eq.refl` が実質の保証だが、パイロットの primitive 表の「IR の演算との一致」は register/mux/add/const/loop だけ個別に証明した | S2 で `eq/and/or/not` を追加 |

固定した信頼境界（新設）: なし。使うものは Lean kernel と標準 axiom、既存の IR 意味（`Sparkle.IR.Semantics`）、`Signal.loop` の純粋な定義（`@[implemented_by loopImpl]` は実行の高速化であり、論理の定義とは別。両者の一致は主張していない）。

発見した事実（reviewer への報告）:

1. 既存の `shapeOf`（`sigShape?`）は先頭に `(dom : DomainConfig)` の束縛がある宣言だけを受け付ける。`defaultDomain` に固定された 3 root は `shapeOf = none` なので、現行の `DeclConnect` は**対象にしない**。パイロットは `monoShapeOf`/`SourceDenotesMono`/`ObservationsEqualMono` を足した（位置は 0 から。`machineSource` の `bools 0`/`bits 0 8` と同じ規約）。必要 IP に定義域固定の宣言がある場合は S2 で `DeclConnect` 側の扱いを決める必要がある。
2. `CVEKV` の `prim`/`tcon` が `¬ IsDefn` を要求するため、`Signal.*` を停止する規則が書けない（§2）。「停止 7 key は Dyn に入る」という測定は、`PrimTableK` に defn の行を許す規則か、適用単位の規則（本パイロット）がなければ導出に使えない。

次に閉じる束（S2 への提案）: (1) 端点経路を `genGP` 経路へ（`SrcPkg` 化）、(2) `ENV/cache`（`RootInEnv` を run の環境から供給）、(3) `CD` の関数性と `eq/and/or/not` の IR 一致、(4) `closes` の供給、(5) S0 の必要 IP 全件に対する未対応構文の追跡。

## 7. 進捗の記録（戦略 §9、S1b で訂正）

(1) 必要 IP の成功数/総数: S0 の一覧がないので未計測。
(2) 元ソースから出力までの**条件付きの接続 4 本**（「閉じた経路」ではない）。各接続は次の前提を**まだ供給していない**:
- run の成功（`hr : RunsTo (synthesizeCombinational…)`）。【S1d で訂正】これは「供給できない」前提ではなく、「compile が成功したなら」の定理に自然に残る前件である。任意の入力について成功を証明する必要はない。必要 IP については、実際の compile の成功（S0 の baseline で 327/327。`docs/FG-CIRCUIT-BASELINE.md` は par/fgc-s0 5fe31f83 にあり、この worktree には無い）と、空虚でない適用例（§9.5）を別に示す。
- `RootInEnv (envAt cref w) X …`（run の開始環境に引用した `X` が入っていること）、
- `MachineDefines`（`hd`）、
- arbiter では `BoundaryRowsInEnv (envAt cref w)`（`hB`、§6a）。

`MachineCloses` は 4 root で供給済み（`X.machine_closes` はデータから出る全 context への定理で、`*_root_at` / `*_ships_at` が実際に適用する。型は `FGCircuitPilotCheckAt` が別記した期待型と照合する）。
(3) 位置づけ: `fgCircuit_of_H` は**未証明の H**（旧 CV の全称の問題を持つ `FGLedgerPremisesStmtH`）を `CV := CircCV` に特殊化しただけの橋で、FG 本体の証明にも非空虚性の根拠にも数えない。独立の参考部品である。
(4) `MachineShips` / `WiredConclusion` は `simpleBody`・`seqCheck`・`declWidth` の条件を結論の**内部**に持つ。印字した SV が元の意味を満たすことを無条件に保証したのではない（条件が成り立つ場合の含意）。
(5) 最終 root の未解決仮説と固定した信頼境界: §6。次に閉じる束: §6, §6a。
台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 6a. S1b の訂正と境界（snapshot と任意の run 環境を区別する）

**公開する root（`Tools/ShippingFGCircuitRootsAt.lean`）**: `X_root_at` / `X_ships_at`（X = counterLoop / shift4Loop / counterEnableLoop / arbiterSignal）。`SourceDenotes(Mono)` の環境と `RootInEnv` の環境は、同じ run の開始環境 `envAt cref w` である。S1 の `X_root`（自由な `env`）は run と独立の環境を取れたので、別環境から引用を持ち込む取り違えを型が許していた。`X_root_at` はそれを許さない（`FGCircuitPilotCheckAt` が、`RootInEnv` または `SourceDenotes` を終了環境 `envAt cref w'` に置いた型、旧 `X_root`、を棄却する）。`RootInEnv (envAt cref w) …` の供給は、依然として**未解決の名前付き前提**（`hE`）である。

**独立の型 Check（`Tests/Gen5/FGCircuitPilotCheckAt.lean`）**: 4 root と 4 ships について期待型を別に書く（root 名・shape・machineData・開始 env・返す module をリテラルで）。実際の型と `MetaM` の `isDefEq`（machineData を評価しない構造照合）で比べ、一致しなければ失敗する。root 名、引用 type/value、shape、machineData、`RootInEnv` の env、`SourceDenotes` の env、boundary rows の env、返す module を 1 点ずつ取り違えた 15 mutant と、旧 `X_root` 4 本（計 19）を棄却する。`example … = … := rfl` や `#check` は署名の検査ではないので、これには数えない（旧 `FGCircuitPilotCheck` の該当行は参考）。

**arbiter の補助宣言（`bvAbbrevRow`）の境界**:
- `CD.bvAbbrev` は環境を読まず、`stIdle/stGrantA/stGrantB` に固定値 `0#2/1#2/2#2` を与える。`RootInEnv` は arbiter の root 自身についてだけで、3 つの補助宣言の意味との一致は含まない。
- **snapshot の事実**: この build の環境では、3 宣言は `bvAbbrevRow` のリテラルに等しい（`FGCIRCUIT SNAPSHOT` 行、`MetaM`）。これは固定した 1 つの環境についての検査であり、任意の run の環境についての主張ではない。
- **任意の run の環境についての主張**: 明示の条件 `BoundaryRowsInEnv (envAt cref w)`（`hB`）を `arbiterSignal_root_at` / `_ships_at` の前提に置いた。供給は未実施。kernel の証明は `hB` を使わない（`CD` は環境を見ない）ので、`hB` なしの旧 `arbiterSignal_root` は、環境の補助宣言が違えば `CD` の値と宣言の値が食い違い得る。
- **次の単位**（新しい TRUSTED にしない）: 環境付きの `CD`（`bvAbbrev` を `env.find?` と `unfold` で結ぶ規則: 宣言が `defnInfo` で値が `k#n` リテラルなら、その値を意味とする）に置き換えるか、`hB` を run から供給する（`ENV/cache` の束）。【S1d で訂正】`hB` を run から供給するだけでは `bvAbbrevRow`（表）の定義は消えない（`CD.bvAbbrev` は表を引き続き読む）。消えるのは「表の値が環境の定義と食い違い得る」という隙間だけで、それは環境付きの unfold（`AbbrevDenotes`、S1c-4 の試作）を `CD` 本体の規則にしたときに限る。それまでは `bvAbbrevRow` は `hB` の下でだけ正しい具体的な境界である。

次の束（S1b の後）: 4 root の run の前提（`hr`, `hE`, `hd`）の供給、`CD` の関数性、`genGP` と同じ artifact への接続。U/P/I や全 51 行の作業には戻らない。

## 8. S1c（Issue `sparkle-fg-circuit-pilot` の次の束）: 閉じたもの・残る仮説・FG 行 ID

土台 `34ff2792`（par/fgc-s1）。追加ファイル（既存は書き換えていない）: `Tools/ShippingFGCircuitFunc.lean`、`Tools/ShippingFGCircuitArtifact.lean`、`Tools/ShippingFGCircuitSupply.lean`、`Tools/ShippingFGCircuitEnvCD.lean`、`Tests/Gen5/FGCircuitPilotCheck2.lean`（lakefile へは最初の commit で 1 回だけ登録）。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT2 AXIOMS`: 35 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。この束の成果は**条件付き**であり、「閉じた経路」とは書かない。
行 ID は `FGLedgerPremisesStmtG` の文面に現れる名前（A.P-02 / A.P-04 / D.D-1 / h_A_P06 / C.EN-4 / C.RK-6 / C.CV-4 / D.D-4 / D.D-3 / C.SM-1 / D.T-4 / A.P-05）で書く。台帳本体（8649968e §12.24）はこの worktree に無く読んでいないため、台帳の行番号との突き合わせは reviewer に残す。

### 8.1 閉じたもの（kernel で証明済み。無条件）

| 内容 | 定理 | 対応する FG の行 |
|---|---|---|
| 作業 1: `CD`/`TD` の関数性。同じ式・同じ valuation の 2 つの導出は同じ型・同じ値（`HEq`）。18 規則すべての組を検査（規則の衝突は先頭定数・構文の相違で棄却、同じ規則は部分式の帰納法） | `cd_fun`、`td_fun`、`cd_eq` | D.D-4 の `ConstValueFunctional` の一般形 |
| `CircCV` の関数性（D.D-4 の第 1 連言 `ConstValueFunctional CV` を `CV := CircCV` で満たす） | `circCV_functional` | D.D-4（H の第 1 連言）。**H 全体は未証明なので FG の行は減らさない** |
| 元ソースの意味は一意（同じ env・同じ宣言なら shape も意味も同じ） | `sourceDenotes_unique`、`sourceDenotesMono_unique` | — |
| 作業 2 の部品: package の `decl` は `genGP` から出る（仮定なし） | `genGP_decl`（`genP_decl`） | D.D-3（GP の固定） |
| 作業 2 の部品: 端点データ `X.machineData` と root の shape（引数数・出力ポート）が一致 | `counterLoop_shape` ほか 4 本（kernel の `decide`） | — |
| 作業 3 の部品: `MachineDefines` は「Core 状態が 1 つの環境 `E` を持ち続ける」と `E` についての環境レベルの命題 `MachineDefinesAt E X shape` に**還元できる** | `machineDefines_of_static`、`rootInEnv_of_static`、`boundaryRows_of_static` | h_A_P06（MachineDefines） |
| 作業 3 の部品: 成功した run は `X` を読む（`getConstInfo` の世界 `w1` の環境に `X` がある）。frame 仮定も引用の一致も不要 | `run_reads_root`、`run_reads_root_static` | A.P-04 |
| 作業 4: bvAbbrev の環境付き unfold の試作（`CD` 自体は変更なし）。`AbbrevDenotes env c n v` = 環境の定義の値を `CD` で読んだ値。`BoundaryRowsInEnv env` ⇒ 各行の `AbbrevDenotes`、環境の unfold による任意の意味は表の値に等しい（`cd_fun` による）、`BoundaryRowsInEnv` は env 定義の型・リテラル形と同値で、弱めていない | `abbrevDenotes_of_boundary`、`abbrev_unfold_eq_row`、`boundaryRows_iff_unfold` | ENV/cache（補助宣言） |

### 8.2 条件付きの接続（仮説を名前で残す）

- `X_artifact_at`（X = counterLoop / shift4Loop / counterEnableLoop / arbiterSignal）と、`genGP` を実際に使う `X_artifact_genGP`: 同じ env `envAt cref w`・同じ source 名・params `[]`・同じ `b`/`D` で、(i) `SourceDenotes(Mono)`、(ii) 同じ `mm` での package `p` との `ObservationsEqual(Mono)`、(iii) `HasConcretePackage p n X b raw D`（`TopShips`）、(iv) `WiredConclusion`（run が返す印字 module `b`）を束ねる（`RootArtifact(Mono)`）。`p` は `genGP lvl hs genData₀ (envAt cref w) X = some p` で与えられ、`p.decl = X` は仮定なしで出る。
- `X_root_static`: `hE`/`hd`/`hB` を、1 つの環境 `E` についての環境レベルの命題と `StaticEnv cref E` に置き換えたもの（作業 3）。
- 結論は FG の形 `FGCircuitConclusionMono`（`fgCircuitConclusionMono_of_artifact`）に収まる。

### 8.3 残る仮説（名前付き。Check2 の `FGCIRCUIT2 HYPS` が型から読み出す）

| 仮説 | 内容 | 供給できない理由 | FG の行 |
|---|---|---|---|
| `hr` | run の成功 `RunsTo (synthesizeCombinational…) … w (b, D) w'` | 【S1d で訂正】供給する対象ではなく、「compile が成功したなら」の定理の前件として残す（コンパイラが宣言に対して走って返ることを全入力で証明する必要はない）。`MachineCloses` は「機械合成が走ったなら `none` を返さない」であり、成功そのものの存在は主張しない | A.P-04（`EntryWitness` の run）、A.P-02（Start） |
| `hE`（`RootInEnv (envAt cref w) …`） | run の開始環境に引用した `X` が入っている | 環境は実行時の値。kernel は `counterLoop` という Lean 定数の値を知るが、コンパイラが読む `Environment` 値がそれであることは言えない。`run_reads_root` は「何らかの `ci` を読む」までしか出さない（引用との一致は meta 照合 `SNAPSHOT2`） | C.EN-4（CellPrem）、ENV/cache |
| `StaticEnv cref E`（`_static` 版） | Core 状態が全 world で同じ環境 `E` | run の途中で Core 状態の `env` が変わらないという frame 性質。`Tools/ShippingEntryReadsLinked.lean` の `EnvSnapshot`（開いたまま）の全 world 版 | C.EN-4 |
| `MachineDefinesAt E X shape`（`hd`） | `E` の `X` について `certifiedShape?`/`mixedCertifiedShape?` が `none`、`machineShape?` が `some shape` | `instancePredicate E`/`userInliner E`/`structEnv E` は環境全体を読む。`RootInEnv` は `X` 自身の型と値しか言わない | h_A_P06、C.RK-6、C.CV-4 |
| `hB`（arbiter の `BoundaryRowsInEnv`） | 補助 abbrev 3 つが `bvAbbrevRow` のリテラル | 作業 4 で環境の unfold と同値であることは示したが、環境の定義が何かは実行時の環境の事実 | ENV/cache |
| `hl`（`EndpointLink`） | `p.d = X.machineData`、`p.kD`、`p.src` が端点の観測 | `p.d` は `dataOfAt …`（`GenPDEdgesStmt`）、`X.machineData` は `readMachine`。`Tools/ShippingGen5DataOf.lean` が「木に無い」と書く `dataOfAt` ↔ `readMachine` の橋。`p.src` は `genSem` の観測 | DG-DATAOF / DG-COVER（`C.SM-1` の `hs` と別の行） |
| `hTop` | 印字 `b` についての `TopShips p n X b raw D` | `WiredConclusion`/`MachineShips` から `TopShips` に上げる定理は木に無い（`StepStmt` の領分）。`WiredConclusion` は `simpleBody`・`seqCheck`・`declWidth` の条件を内部に持つ | D.T-4 / `StepStmt` |
| `hP` | `genGP … X = some p` | 生成表が `X` で `some` を返すこと（被覆）。**この束では供給していない** | D.D-3 / O2（coverage） |
| `fgCircuit_of_H` の入力 | 未証明の H | 変更なし。FG 本体の根拠に数えない | H 全体 |

### 8.4 作業 2 の結論と未実施

root の文（`X_ships_at`）と生成表（`genGP`）は、**同じ環境・同じソース名・同じ `b`/`D`・同じ `mm`** で 1 つの定理に束ねた。ただし束ねたのは「`p` が端点であること（`hl`）と `TopShips`（`hTop`）を仮定したとき」であり、`genGP` の `p` が実際に端点データを持つこと、印字 `b` が `TopShips` を満たすことは**示していない**（8.3）。したがって「閉じた経路」ではなく、条件付きの接続である。

### 8.5 台帳

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。`circCV_functional` は H の 1 連言（D.D-4）を `CV := CircCV` で満たすが、H の他の連言と `CV` binder の置換が受理されていないので数を減らさない。

### 8.6 次の束

(1) `StaticEnv` と `MachineDefinesAt` の供給（`coreHead` が Core 状態の `env` を変えない frame 補題と、`MachineDefinesAt` を具体の `Environment` 値に対して評価する meta 検査）。(2) `dataOfAt` ↔ `readMachine` の橋（`hl` の `p.d`）。(3) `WiredConclusion` → `TopShips`（`StepStmt` の単一モジュール版）。(4) `hr`: run の存在。

## 9. S1d（Issue `sparkle-fg-circuit-pilot` の次の束）: 供給した前提・残る前提・訂正

土台 `87c713c6`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile へは最初の commit で 1 回だけ登録）: `Tools/ShippingFGCircuitSupply2.lean`、`Tools/ShippingFGCircuitCover.lean`、`Tools/ShippingFGCircuitBridge.lean`、`Tools/ShippingFGCircuitApply.lean`、`Tests/Gen5/FGCircuitPilotCheck3.lean`。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT3 AXIOMS`: 29 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。この束の成果も**条件付き**であり、FG の行は減らさない。
訂正（§6a 末尾の「どちらでも表は消える」、§7 と §8.3 の `hr` の書き方）は該当箇所に「S1d で訂正」と書いた。

### 9.1 作業 1: `StaticEnv` / `MachineDefinesAt` / `hE` の供給

| 内容 | 定理 | 結果 |
|---|---|---|
| **`StaticEnv` は C.EN-4 の下で偽**。`StaticEnv cref E` は全 world で `envAt cref w = E` と言うが、`CellPrem`（C.EN-4）の一部 `SetGet cref` の下で、Core 状態を別の環境（`setMainModule` で作った 2 つ）に `set` した world が作れるので `¬ StaticEnv cref E` | `not_staticEnv` | S1c の `X_root_static`（§8.2）は前提が C.EN-4 と両立しない含意になる。**供給の経路として使わない**。§8.3 の `StaticEnv` の行は「供給できない」ではなく「述べ方が不適」に訂正する |
| `hd`（`MachineDefines mctx mref cctx cref X shape`）を **h_A_P06**（`FGLedgerPremisesStmtG` の内側の仮説）の root での適用（`TgtRun.top`）から供給。`Start`（A.P-02）から admissible context、`genGP` の package から `p.d.shape = X.machineData.shape` | `machineDefines_of_hA6`、`machineDefines_of_witness` | 供給（h_A_P06 は名前付き前提のまま） |
| `hc`（`MachineCloses`） | `X.machine_closes`（S1c から。`machineClosesAtA_of_closes` で `Bridge` の run 証拠にも使う） | 供給 |
| `hE`（`RootInEnv (envAt cref w) …`）: run が実際に読んだ `getConstInfo X` の world `w1` の環境に `X` がある（存在は run から出る）。開始環境への移送は **run 局所**の `EnvSnapshot cref w1 w`（既存の open な文）。中身（その定義が引用と一致）は `QuoteFact`。`∀ w` の `StaticEnv` は使わない | `run_reads_const`、`rootInEnv_of_quote`、`hE_of_run` | 存在は供給。残る: `QuoteFact`（環境の `X` の中身）と `EnvSnapshot`（C.EN-4 / ENV cache） |
| `MachineDefinesAt` の実環境での値 | `FGCIRCUIT3 SNAPSHOT3` | この build の環境で 4 root について `certifiedShape? = none`・`mixedCertifiedShape? = none`・`machineShape? = some` を MetaM で評価（一つの環境の値であり、任意の run の環境についての主張ではない） |

注意（reviewer へ）: `MachineDefines` と h_A_P06 は run と無関係な world `w1 w5 w7` について `∀` で書かれている（`RunsTo getEnv … w5 envR w6` は任意の world で成り立つ）。`StaticEnv` と同じ形の強さがあり、`SetGet cref` の下で充足可能かどうかは**この束では調べていない**。`hd` を供給できたのは、この強い形の h_A_P06 を前提として受け取ったからである。

### 9.2 作業 2: `hl`（`dataOfAt` と `readMachine` の橋）

`EndpointLink` の 3 つの連言のうち `data`（`p.d = X.machineData`）と `kD_eq`（`p.kD = kDOf X.machineData`）を示した（`genGP_root`、`genGP_root_canon`）。`genGP` が返す package の `d` は `genP_d_edges` により table の行 `g` の `g.d` で、`g.hdata : dataOfAt lvl E senv g.d.shape = some g.d`、`g.hshape : machineShape? … = some g.d.shape`。したがって次の**名前付き前提**があれば `p.d = X.machineData`:

`RootReader lvl env X d := ∃ E, entry₀ env X = some E ∧ machineShape? false [] E (structEnv env) = some d.shape ∧ dataOfAt lvl E (structEnv env) d.shape = some d`（`d := X.machineData`）。

これは `dataOfAt` と `readMachine` の出力の一致をリテラル `X.machineData` に対して述べたもの（FG 行: DG-DATAOF / DG-COVER / DG-ENV。C.SM-1 の `hs` とは別）。**kernel では示せない**: `dataOfAt` が `partial` の `packTupleInputs` / `rootFloat` を呼び、kernel は評価できない。`FGCIRCUIT3 SNAPSHOT3` は実環境で `dataOfAt`（fuel `fun _ => 1000000`）を評価し、4 root で nIn・#state・#outs・#lets・#insts・#binders・ok・GenWF がリテラルと一致することを確かめた。`MachineData` に `Repr`/`DecidableEq` が無いので**完全な一致ではなく不変量の比較**である。

`src`（`p.src = X の観測`）は示していない。`p.src` は `genSemGenE` の `stateLoop` による観測、右辺は宣言自身の `Signal.loop` の観測で、両者の一致は D.D-3 のこの root での意味の内容そのものである。必要なもの: (a) `stateLoop` と `Signal.loop` の時刻 t についての帰納（`machine_source` と `machine_result` が右辺側を与える。左辺の `refBodyE` は insts = [] で `extB/extS` が恒等になる）、または (b) 同じ run の module に対する 2 つの trace（`Pkg.trace` と `X.machine_sound`）から、出力値の一意性で `p.src = obs` を出す（`SourceInputs` を実現する `ins` の構成が要る）。どちらも未実施で、`hsrc` として残す。

### 9.3 作業 3: `hTop`（`WiredConclusion` から `TopShips`）

`WiredConclusion` からは作らない（`MachineShips` は最適化後 module と Verilog の `wof` についての文で、`TopShips` は階層実行 `runModuleTG` の文）。代わりに、4 root が**レジスタ付きの leaf**（`insts = []`、`slots ≠ []`）であることを使い、既存の `leaf_topShips_of_LB`（`Tools/ShippingGen2Leaf.lean`）と trace の生成子 `Pkg.trace L.O L.T hA p ran` を使った。`ran` は `machineRunJQC_of_closesA`（core run、`MachineDefines`、`MachineClosesAtA`）から作る。

- `leaf_topShips_of_run`: `Start`・core run・`hd`・`hc`・`PostT1 b raw`・data の判定可能な事実 `LeafFacts`（`decide`。4 root で成功）から `TopShips p n X b raw D₀`（**D₀ = core run の design**）。
- `hTop_of_leaf`: `Post := PostRun`（core run に結んだ後処理関係）の下で `∀ raw, PostRun … → ∃ n, HasConcretePackage p n X b raw D'`。ただし **core design D₀ から印字 design D' への移送 `DesignTransport`** を名前付き前提とする。移送の部品は `Tools/ShippingGen5DCEntryT.lean`（`childMap_transport`、`runModuleTG_transport`）にあるが、同ファイルは NOT BUILT・条件付き（`NoRawBelow`、lookup の一致）で、`TopShips` 自体の移送は木に無い。
- `A.P-05` の `Post` は抽象の carrier なので、そこから `raw` が core run の出力だと言えない。`PostRun` はその関係を run に結んだ値である（`∃ raw, Post` は `hr` と `synthesizeCombinational_postEntry` から供給）。

### 9.4 作業 4: `hP`（`genGP` の被覆）

`genGP_root`: leaf の root で、table `genData₀ env` が `entry₀ env X` に行 `g` を持つなら `genGP … X = some p`（`insts = []` なので `Acc (CallRel K) X` は空虚に成り立ち、`ordCallees` は空で、`ReachCover` は一つの名前に落ちる）。`p.decl = X`、`p.d = g.d`、`p.kD = kDOf g.d` も同時に出る。`canonGD`（`GenData` が存在すれば選ぶ table）では、行は `RootReader` と `GenWF`（`decide`）から作れる（`genGP_root_canon`）。`genGP` を具体的に計算する経路は無い（環境が閉じた項でない）ので、被覆は具体計算ではなく `RootReader` に還元した。任意の `genData₀` については行の存在が前提になる（`genGP_root` の `hg`）。

### 9.5 作業 5: 適用例

`counterLoop_final`、`shift4Loop_final`、`counterEnableLoop_final`、`arbiterSignal_final`（`Tools/ShippingFGCircuitApply.lean`）。各定理の仮説は次の**だけ**（`FGCIRCUIT3 HYPS` が型から読み出し、期待の一覧と一致することを検査する。`hd`/`hc`/`hP`/`hl`/`hTop`/`hpost` が仮説に戻ったら失敗する）:

| 仮説 | 内容 | FG の行 |
|---|---|---|
| `hw : EntryWitness …`、`hr` | compile が成功した（antecedent） | A.P-02 Start、A.P-04 run |
| `hA6` | h_A_P06 | h_A_P06 |
| `hRead : RootReader` | `dataOfAt`/`machineShape?` が実環境の root でリテラルのデータを返す | DG-DATAOF / DG-COVER / DG-ENV |
| `hE`（arbiter は `hB` も） | 環境の `X` の中身（`QuoteFact` + `EnvSnapshot`） | C.EN-4 / ENV cache |
| `hsrc` | `p.src` が宣言の観測 | D.D-3（DG-SEM） |
| `htr : DesignTransport` | core design → 印字 design | D.T-4 / `StepStmt` |

定理の内部で供給したもの: `hd`（h_A_P06 から）、`hc`、`hP`、`p.decl`/`p.d`/`p.kD`、leaf の判定可能な事実、core design での `TopShips`、`∃ raw, PostRun`、shape の一致、`SourceDenotes`。結論は `∃ raw, PostRun …` と、`P := genGP … (canonGD lvl) (envAt cref w)` の `RootArtifact(Mono)`。

**満たせない前提（明記）**: kernel の中で `hw`/`hr`（走った run）、環境に関する `hE`/`hB`/`hRead`、`hsrc`、`htr` を実際の値で満たすことはできない（run も `Environment` も閉じた項でない）。したがって「全前提を実際の値で満たした適用例」は kernel の中には**作れていない**。代わりに: (a) leaf の事実・`GenWF`・`kD` は 4 root で実際のリテラルに対して `decide` した（`X_leafFacts`、`X_wf`、`X_kD`）、(b) 環境に関する `hE`/`hB`/`hRead` と `MachineDefinesAt` の 3 つの事実は、この build の実環境で MetaM が評価した（`SNAPSHOT2`、`SNAPSHOT3`）、(c) compile の成功そのものは S0 の baseline（327/327）が示す。`hsrc`/`htr` はどこでも評価されていない。この束で条件付き定理が空虚でないことの根拠はここまでで、それ以上ではない。

### 9.6 Check3 の出力

`kjob lake build Tests.Gen5.FGCircuitPilotCheck3`（exact-head と結果は Issue note）。出力行: `FGCIRCUIT3 SIGNATURES`（`not_staticEnv`・`machineDefines_of_hA6`・`genGP_root_canon` の期待型と 6 mutant）、`FGCIRCUIT3 HYPS`（4 root の仮説一覧）、`FGCIRCUIT3 AXIOMS`（29 名）、`FGCIRCUIT3 SNAPSHOT3`。`X_final` の期待型の独立記述と mutant は作っていない（仮説一覧と「自分の root だけを含む」検査で代えた）。

### 9.7 残る仮説（名前付き。台帳は FG 75 / T1 57 のまま）

`hr`/`hw`（A.P-04、A.P-02。前件）、`hA6`（h_A_P06。`∀`-world の形に注意、§9.1）、`RootReader`（DG-DATAOF / DG-COVER / DG-ENV）、`QuoteFact` + `EnvSnapshot`（C.EN-4 / ENV cache。arbiter は `hB`）、`hsrc`（D.D-3）、`DesignTransport`（D.T-4）。任意の `genData₀` では table の行の存在。`fgCircuit_of_H` の入力（未証明の H）は変更なし。
次の束: (1) `hsrc`（stateLoop と Signal.loop の帰納、または 2 trace の一意性）、(2) `DesignTransport`（`DCEntryT` の移送を `TopShips` まで持ち上げる）、(3) `MachineDefines`/h_A_P06 の `∀`-world の形が `SetGet` の下で充足可能かの確認、(4) `RootReader` を kernel で扱える形（`partial` helper の外出し）にするか、MetaM の検査器として固定するかの判断。

## 10. S1e（Issue `sparkle-fg-circuit-pilot` の次の束）: counterLoop 1 root の実接続

土台 `306716c3`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は最初の commit で 1 回だけ）: `Tools/ShippingFGCircuitSrc.lean`、`Tools/ShippingFGCircuitTransport.lean`、`Tools/ShippingFGCircuitFinal.lean`、`Tests/Gen5/FGCircuitPilotCheck4.lean`。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT4 AXIOMS`: 12 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**（残る前提あり）。方針どおり 4 root を並行せず counterLoop だけを閉じた（他 3 root は `X_final` のまま、`hsrc`/`htr` が前提に残る）。

### 10.1 作業 1: `hsrc`（D.D-3: stateLoop と Signal.loop）— 供給した

`counterLoop_hsrc`（`Tools/ShippingFGCircuitSrc.lean`）: `RootReader lvl env counterLoop counterLoop.machineData` から、`genGP … (canonGD lvl) env counterLoop = some p` なる `p` が存在し、`p.src i bools bits = monoObs shCounter counterLoop bools bits`。
経路: (1) `genGP_root_src` / `genGP_root_canon_src`: package の `src` は表の行 `g` について `(genSemI (genS K) X (g.toIn hs)).src`（`genP_some_inv`、`src_toSem`、`GenData.genSem` は定義上 `genSemI`）。`g.d = X.machineData`（`canon_row`）、`inits = initsOf g.d`（`toIn` が定義上そう置く）。
(2) `counterLoop_src_eq`: そのような `GenIn` について `(genSemGen Q X gi).src = counterLoop.machineSource`。`insts = []` なので `extBOf/extOf` は恒等（`ExtStage … 0`）。生成側の状態ループ `stateLoop inits (refBodyE …)` と宣言側の `Signal.loop counterLoop.machineBody` の状態が、cycle t ごとに `machineSigma`（`x ↦ (x, ())`）で対応することを t の帰納で示した: 初期値は `initsOf machineData = machineInits`（`rfl`）と `R.val 0 = 0#8`、1 step は `loop_state`（生成側）・`genSemGenE_writes`・`counterLoop.machine_writes`（宣言側。`evalTerms (typedVal …)` が同じ項 `machineData.nexts` を評価する）。出力は `genSemGenE_result` と `counterLoop.machine_result` / `machine_source` から各 cycle で一致し、`list_ext_of_map_eval` でリストが等しい。
意味: 両辺は**同じ項**（`machineData.nexts/outs`）を評価するので、この一致は「reader が読んだデータが宣言のコピー（`RootReader`）であること」を使っており、データが宣言の意味であること自体は `X.machine_sound` / `machine_writes`（endpoint の kernel `Eq.refl`）に依る。示せていないもの: `RootReader`（`dataOfAt` の実環境での値、MetaM 検査のみ）。

### 10.2 作業 2: `DesignTransport`（D.T-4）— レジスタ leaf について供給した

`designTransport_of_leaf`（`Tools/ShippingFGCircuitTransport.lean`）: core run の `(raw, D₀)` と印字 design `D'` について `TopShips p n X b raw D₀ → TopShips p n X b raw D'`。`D'` は任意の design でよい（`PostEntry` の `topMap …` である必要もない）。
理由: `TopShips` は design を `childMap D.modules`（instance の oracle）と `ResetNk n raw D kids` を通してのみ読む。レジスタ leaf の `raw.body`・`b.body`・`(checkedOptimize b).body` は `seqStmtOk`（assign/register/memory）で **instance を持たない**（`MachineWired` の `hclean` と `leaf_b_facts` から読む。`leaf_instFree_of_run`）。よって `runModuleTG_instFree` で run は oracle に依らず、`ResetNk` は空虚、`bodyInstOuts _ b.body = []`（`bodyInstOuts_instFree`）。`topShips_design_irrel`。
`Tools/ShippingGen5DCEntryT.lean`（`childMap_transport`、`runModuleTG_transport`）は **instance を持つ module 用**で、この経路では使っていない。同ファイルは単独で build できる（`kjob lake build Tools.ShippingGen5DCEntryT` exit 0、354 jobs）。非 leaf の root への持ち上げでは `NoRawBelow` と lookup 一致が要る。
追加の前提は無い（`hr` の core run、`hd`、`hc`、`LeafFacts`、`PostT1` は S1d で既に供給済みのもの）。

### 10.3 作業 3: counterLoop の最終定理

`counterLoop_final2`（`Tools/ShippingFGCircuitFinal.lean`）。仮説は **`hw`、`hr`、`hA6`、`hRead`（RootReader）、`hE`** だけ。`hsrc` と `htr` は仮説から消えた（`counterLoop_final` から比較）。`hTop_of_leaf2` は transport の前提なしで `∀ raw, PostRun … → ∃ n, HasConcretePackage p n X b raw D'`。
結論は S1d と同じ: `(∃ raw, PostRun …) ∧ ∃ mm p, RootArtifactMono (envAt cref w) (genGP … (canonGD lvl) (envAt cref w)) (PostRun …) counterLoop shCounter mm b D' p`。

残る前提（名前付き。台帳は FG 75 / T1 57 のまま）:

| 仮説 | 内容 | 状況 |
|---|---|---|
| `hw` / `hr` | compile が成功した（`EntryWitness`、`RunsTo (synthesizeCombinational counterLoop)`） | 前件。S0 baseline で成功は確認済みだが kernel の中では供給しない |
| `hA6` | h_A_P06（`∀`-world の形） | reviewer が `SetGet` 下の充足可能性を確認中。この束では扱わない |
| `hRead : RootReader` | `dataOfAt`/`machineShape?` が実環境で `counterLoop.machineData` を返す | MetaM の実環境検査（`SNAPSHOT3`）。kernel では `partial` helper のため不可 |
| `hE : RootInEnv` | 環境の `counterLoop` が引用した値 | `QuoteFact` + `EnvSnapshot`（C.EN-4 / ENV cache） |

`hsrc` と `DesignTransport` は counterLoop の最終定理から消えたが、`hsrc` は `RootReader` を使う。他の 3 root（shift4Loop、counterEnableLoop、arbiterSignal）の `X_final` はそのまま（`hsrc`/`htr` を仮説に持つ）。`hsrc` の証明は `counterLoop` 固有の項（`machineBody`、`machineSigma`、`machine_writes`）で書いたため、他 root には root ごとの同形の証明が要る（`DesignTransport` は 4 root とも同じ理由で供給できる）。

### 10.4 Check4 の出力

`kjob lake build Tests.Gen5.FGCircuitPilotCheck4`（884 jobs、exit 0）。出力行: `FGCIRCUIT4 SIGNATURES`（`counterLoop_hsrc`、`designTransport_of_leaf`、`counterLoop_final2` の期待型 3 本が独立記述と一致、8 mutant 棄却）、`FGCIRCUIT4 HYPS`（`counterLoop_final2` の仮説は `L lvl hw hr hA6 hRead hE`。`hsrc`/`htr`/`hd`/`hc`/`hP`/`hl`/`hTop` は仮説に無い）、`FGCIRCUIT4 AXIOMS`（12 名、標準 axiom のみ）、`FGCIRCUIT4 SNAPSHOT4`（`counterLoop.val 0 = 0`、`counterLoop.val 3 = 3` を kernel が証明: 観測が自明でない）。
限定: 適用例（全前提を実際の値で満たす例）は kernel の中には作れていない（§9.5 と同じ理由。run も `Environment` も閉じた項でない）。

### 10.5 次の束

(1) 他 3 root の `hsrc`（shift4Loop はレジスタ 4 段、counterEnableLoop は mux、arbiterSignal は domain 多相で、counterLoop と同形の帰納が使えるかを root ごとに確認）。(2) `hA6`（reviewer 判断待ち）。(3) `RootReader` / `hE` を MetaM の検査器として固定するか、kernel で扱える形にするかの判断。
