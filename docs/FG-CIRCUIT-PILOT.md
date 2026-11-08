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

| 仮説 | 内容 | 未供給の理由 | FG の行 |
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

これは `dataOfAt` と `readMachine` の出力の一致をリテラル `X.machineData` に対して述べたもの（FG 行: DG-DATAOF / DG-COVER / DG-ENV。C.SM-1 の `hs` とは別）。**kernel では未供給**（【S1f で訂正】「示せない」とは断定しない）: `dataOfAt` が `partial` の `packTupleInputs` / `rootFloat` を呼び、kernel は評価できない。`FGCIRCUIT3 SNAPSHOT3` は実環境で `dataOfAt`（fuel `fun _ => 1000000`）を評価し、4 root で nIn・#state・#outs・#lets・#insts・#binders・ok・GenWF がリテラルと一致することを確かめた。`MachineData` に `Repr`/`DecidableEq` が無いので**完全な一致ではなく不変量の比較**である。

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

**未供給の前提（明記）**（【S1f で訂正】「満たせない／作れない」ではなく、現在の定式化では未供給）: kernel の中で `hw`/`hr`（走った run）、環境に関する `hE`/`hB`/`hRead`、`hsrc`、`htr` を実際の値で満たした項は現状ない（run も `Environment` も、この束では閉じた項として構成していない）。したがって「全前提を実際の値で満たした適用例」は kernel の中には**未構成**である。代わりに: (a) leaf の事実・`GenWF`・`kD` は 4 root で実際のリテラルに対して `decide` した（`X_leafFacts`、`X_wf`、`X_kD`）、(b) 環境に関する `hE`/`hB`/`hRead` と `MachineDefinesAt` の 3 つの事実は、この build の実環境で MetaM が評価した（`SNAPSHOT2`、`SNAPSHOT3`）、(c) compile の成功そのものは S0 の baseline（327/327）が示す。`hsrc`/`htr` はどこでも評価されていない。この束で条件付き定理が空虚でないことの根拠はここまでで、それ以上ではない。

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
| `hRead : RootReader` | `dataOfAt`/`machineShape?` が実環境で `counterLoop.machineData` を返す | MetaM の実環境検査（`SNAPSHOT3`）。kernel では未供給（`partial` helper を呼ぶため、現在の定式化では評価していない） |
| `hE : RootInEnv` | 環境の `counterLoop` が引用した値 | `QuoteFact` + `EnvSnapshot`（C.EN-4 / ENV cache） |

`hsrc` と `DesignTransport` は counterLoop の最終定理から消えたが、`hsrc` は `RootReader` を使う。他の 3 root（shift4Loop、counterEnableLoop、arbiterSignal）の `X_final` はそのまま（`hsrc`/`htr` を仮説に持つ）。`hsrc` の証明は `counterLoop` 固有の項（`machineBody`、`machineSigma`、`machine_writes`）で書いたため、他 root には root ごとの同形の証明が要る（`DesignTransport` は 4 root とも同じ理由で供給できる）。

### 10.4 Check4 の出力

`kjob lake build Tests.Gen5.FGCircuitPilotCheck4`（884 jobs、exit 0）。出力行: `FGCIRCUIT4 SIGNATURES`（`counterLoop_hsrc`、`designTransport_of_leaf`、`counterLoop_final2` の期待型 3 本が独立記述と一致、8 mutant 棄却）、`FGCIRCUIT4 HYPS`（`counterLoop_final2` の仮説は `L lvl hw hr hA6 hRead hE`。`hsrc`/`htr`/`hd`/`hc`/`hP`/`hl`/`hTop` は仮説に無い）、`FGCIRCUIT4 AXIOMS`（12 名、標準 axiom のみ）、`FGCIRCUIT4 SNAPSHOT4`（`counterLoop.val 0 = 0`、`counterLoop.val 3 = 3` を kernel が証明: 観測が自明でない）。
限定: 適用例（全前提を実際の値で満たす例）は kernel の中には未構成（§9.5 と同じ。run も `Environment` もこの束では閉じた項にしていない。【S1f で訂正】「作れない」とは断定しない）。

### 10.5 次の束

(1) 他 3 root の `hsrc`（shift4Loop はレジスタ 4 段、counterEnableLoop は mux、arbiterSignal は domain 多相で、counterLoop と同形の帰納が使えるかを root ごとに確認）。(2) `hA6`（reviewer 判断待ち）。(3) `RootReader` / `hE` を MetaM の検査器として固定するか、kernel で扱える形にするかの判断。

## 11. S1f（Issue `sparkle-fg-circuit-pilot` の次の束）: counterLoop の run 局所化

土台 `07e5b53c`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は最初の commit で 1 回だけ）: `Tools/ShippingFGCircuitRunLocal.lean`、`Tools/ShippingFGCircuitRunLocal2.lean`、`Tools/ShippingFGCircuitFinal3.lean`、`Tests/Gen5/FGCircuitPilotCheck5.lean`。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT5 AXIOMS`: 18 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で、approved/done ではない。方針どおり 1 root（counterLoop）だけを扱った。§9・§10 の「作れない／示せない」の断定は「未供給」に訂正した（§8.3 の表の見出し、§9.2、§9.5、§10.3、§10.4 の該当文）。

### 11.1 `hw` を `Start` + `hr` に絞った（`counterLoop_final3`）

`hw : EntryWitness ReflectsAll L …` は `Start`・run・`ReflectsAll L declName parameters` の連言だった。S1e までの証明が使っていたのは `hw.1`（`Start`）と `hr` だけで、`ReflectsAll` は供給も使用もされていなかった。`counterLoop_final3`（`Tools/ShippingFGCircuitFinal3.lean`）の仮説は `L lvl hstart hr hdRun hRead hE`（`hw`・`ReflectsAll`・`hA6` なし）。`Laws L`（A.P-02 の runtime laws。`Start` の `AdmCtx`/`JQC` の前提でもある）は明示引数のまま**残る義務**で、型に出ている。

### 11.2 `MachineDefines` → `MachineDefinesRun`（run に局所化した境界）

`MachineDefines`（および h_A_P06 の `hA6`）は、run と接続されていない world `w1 w5 w7` の `getConstInfo`/`getEnv` について `∀` で書かれている。後継 `MachineDefinesRun mctx mref cctx cref X shape w M D w'`（`Tools/ShippingFGCircuitRunLocal.lean`）は同じ 3 つの事実（`certifiedShape?` = none、`mixedCertifiedShape?` = none、`machineShape? = some shape`）を、**core run `synthesizeCombinationalCore X … w (M, D) w'` が実際に読んだ値**についてだけ要求する:

- `ci` と `envR` は、run の本体 `synthesizeFromConst … ci envR` が呼ばれた値（`synthesizeCombinationalCore_reads` の分解。その run `w3 → w4` が `(M, D)` を返すことが前提）。
- `envR'` は、`synthesizeFromConst` が最初に行う `getEnv` の結果で、**その本体の開始 world `w3` に結んである**（`synthesizeFromConst_machine_invR` / `synthesizeFromConst_machineR`: 既存の `…_invA` / `…_machine` は `w5` が任意の world だった。証明を写して文だけ強めた）。
- 読み取り world `w1`（getConstInfo）と `w5`（最初の getEnv）は、返した値が同じになる任意の world で、run の実際の world に固定してはいない（`RunsTo` は決定的だが、値だけを固定している）。この点で「run の分解に対する ∀」であり、全 world の ∀ より狭いが、1 つの world への一点指定ではない。

`machineDefinesRun_of_defines`: `MachineDefines` ⇒ `MachineDefinesRun`（逆は主張しない）。SetGet だけから `MachineDefines` が偽だとは断定しない（S1d の判断どおり）。局所化後の述語は充足可能性を主張せず、供給もしていない。

**消費者まで接続した**:
- `machine_run_of_coreR` / `machineRunJQC_of_closesR`（package の trace、leaf の `TopShips`、`DesignTransport` が使う `MachineRunJQC`）。
- `synthesizeCombinationalCore_machine_soundR`。
- endpoint 側: 生成された `counterLoop.machine_ships_wired hr hd hc` は `hd : MachineDefines` を取る。`Tools/ShippingFGCircuitRunLocal2.lean` は既存の `machine_trace_lets_of_streamB` / `machine_trace_lets_of_stream` / `machine_traceL_of_stream` / `machine_traceL_of_loop` / `machine_ships_wired` の**証明の写し**で、境界の前提だけを `MachineDefinesRun`（`machine_ships_wiredR` では `∀ raw D w1, MachineDefinesRun … w raw D w1`）に替えた（`…R` 名）。`counterLoop` の endpoint は `machine_ships_wired d (machine_traceL_of_loop …)` の形（生成された項を `#print` で確認）なので、同じ引数で `…R` に差し替えられる。
- `hTop_of_leaf3` / `leaf_topShips_of_runR` / `leaf_instFree_of_runR`（`DesignTransport` を含む）、`counterLoop_artifact_atR`、`counterLoop_final3`。

`counterLoop_final3` の `hdRun : ∀ raw D₀ w1, MachineDefinesRun … ``counterLoop counterLoop.machineData.shape w raw D₀ w1` が、旧 `hA6` の代わりに残る**未供給の義務**（FG の h_A_P06 の run 局所形）。h_A_P06 から `MachineDefines` が出れば `machineDefinesRun_of_defines` で `hdRun` が出る、という一方向の関係だけを主張する。

### 11.3 `hRead` / `hE` の局所化（試行: `counterLoop_final3L`）

run が実際に到達する地点は 3 つ: `getConstInfo X`（world `w1`）、最初の `getEnv`（`w5`、entry constant の計算元）、`synthesizeFromConst` 内の 2 度目の `getEnv`（`w3`、`machineShape?` の読み取り元）。`OnRunReads`（`MachineDefinesRun` と同じ分解）の上に 3 つの名前付き義務を作った:

- `RunSnap`: 3 つの読み取り world の環境が開始 world の環境と等しい（run 局所の `EnvSnapshot`。C.EN-4 / ENV cache）。
- `RunQuote`: run が読んだ `ci` は引用した定義（`QuoteFact` を run の `ci` に限ったもの）。
- `RunReader`: 読み取り関数 `dataOfAt` を、run の `ci`/`envR` の entry constant と開始環境の `structEnv` に適用した結果が `X.machineData`（DG-DATAOF / DG-COVER / DG-ENV）。

`rootEnv_of_run`（`hdRun` の 3 つ目の事実と合わせて）から `RootInEnv (envAt cref w)` と `RootReader lvl (envAt cref w)` が出る（`RootReader` の `machineShape?` の連言は仮定ではなく `MachineDefinesRun` の 3 つ目の事実になる）。`counterLoop_final3L` の仮説は `L lvl hstart hr hdRun hsnap hquote hreader`。結果: **局所化はできた**が、`RunSnap` の 3 条件（C.EN-4 の下で `∀ w` ではなく run の 3 地点だけ）、`RunQuote`、`RunReader` は未供給のままで、数は `hE`（QuoteFact + EnvSnapshot）+ `hRead` から減っていない（`MachineDefinesRun` の 3 事実のうち `machineShape?` を `RunSnap` で移して `RootReader` から落とした分だけ義務の置き場所が変わった）。`hRead`/`hE` 形の `counterLoop_final3` も残してある。`RunSnap` が `SetGet` の下で充足可能かは調べていない。

### 11.4 Check5 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck5`、887 jobs、exit 0）

- `FGCIRCUIT5 SIGNATURES`: `MachineDefinesRun`、`counterLoop_final3`、`counterLoop_final3L`、`hTop_of_leaf3`、`rootEnv_of_run` の期待型を**型全体**（仮説・結論・環境・design・binder の種類）で独立に書いて `isDefEq` で照合（`MachineDefinesRun` は独立に書いた文と照合）。22 mutant 棄却: 環境（P/結論・`hRead`・`hE`・`RunSnap`）、design/Post の root、`hdRun` の shape、`hRead` の data、package の table（`lvl`）、`Start`/`hr` の欠落、旧 `EntryWitness` の追加、結論の弱め、`MachineDefinesRun` の world の結び（w3→w5）・shape を読む環境・`entryConst` の bool・`getConstInfo` の名前。
- `FGCIRCUIT5 HYPS` / `REMAINING`: 2 つの最終定理の仮説名と型。`hw`・`ReflectsAll`・`hA6`・全 world の `MachineDefines`・`hsrc`・`DesignTransport` は仮説に無いことを検査。
- `FGCIRCUIT5 AXIOMS`: 18 名、標準 axiom のみ。
- `FGCIRCUIT5 SNAPSHOT5`: この build の環境で `dataOfAt`（fuel 1000000）の結果を、endpoint の `counterLoop.machineData` の**全構造**（endpoint コマンドが組み立てる Expr を観測値からフィールドごとに再構成: shape の binders/body/layout/runs/insts/loops/instFields/instOrigins、nIn、dom、位置、sort、lets、outs、nexts を項として）と比較して一致。負対照: shift4Loop の data と、10 個の 1 フィールド摂動を棄却。観測値（nIn=0、状態 1 本 8 bit、binder `loop0_r0`、layout、outs=`bitsInput 8 0`、nexts=`add (bitsInput 8 0) (bitsLit 8 1)`、body）も表示。`certifiedShape?` = `mixedCertifiedShape?` = none、`machineShape?` が reader の shape と一致。これは**ひとつの環境の値**で、任意の run についての `RootReader`/`RunReader`/`MachineDefinesRun` の kernel の文ではなく、前提が同時に充足可能であることの証明でもない。

### 11.5 閉じたもの、残る仮説、FG の行 ID との対応

閉じた（kernel 証明として、仮説つきで）:

| 内容 | 定理 | FG の行 |
|---|---|---|
| `hw` から `ReflectsAll` を外し `Start`+`hr` へ | `counterLoop_final3` | A.P-02 / A.P-04 |
| `MachineDefines` の局所版と、それを使う endpoint 連鎖 | `MachineDefinesRun`、`machine_ships_wiredR` ほか | A.P-06（h_A_P06） |
| leaf の `TopShips`・`DesignTransport` を局所版の境界で | `hTop_of_leaf3` | D.T-4 |
| 条件付きの run 局所の `hRead`/`hE` | `rootEnv_of_run`、`counterLoop_final3L` | DG-DATAOF/COVER/ENV、C.EN-4 |

これらは**条件付きの接続**で、下の仮説が残る間は「閉じた経路」ではない。

残る仮説（台帳は FG 75 / T1 57 のまま）:

| 仮説 | 内容 | FG の行 |
|---|---|---|
| `Laws L` | runtime laws（明示引数） | A.P-01（= T1L-01。merged B.F-3, D.E-10）。【S3j 訂正】この表は以前 A.P-02 と書いていた（誤り）。台帳 `scripts/gen2/PREMISE_LEDGER.md`（8649968e、coder 確認: 56–57, 99–100, 164, 325–326 行）で `Laws` = A.P-01、`Start` = A.P-02（= T1L-02。merged A.P-03, C.RR-1, B.F-2, D.E-11, D.D-6）、`CellPrem` = C.EN-4。同台帳の注記: 非空虚な `Laws` の値は、この調査では見つからなかった |
| `hstart : Start L mctx cctx w` | 最外の呼び出しの開始（`AdmCtx`、`JQC 0`） | A.P-02 |
| `hr` | compile が成功した（前件） | A.P-04 |
| `hdRun` | run 局所の機械境界（旧 `hA6`/h_A_P06 の局所形） | h_A_P06 |
| `hRead`, `hE`（`final3`）または `hsnap`, `hquote`, `hreader`（`final3L`） | 環境の `X`・読み取り関数の出力 | DG-DATAOF/COVER/ENV、C.EN-4 / ENV cache |

他の 3 root（shift4Loop、counterEnableLoop、arbiterSignal）の `X_final` は不変（`hsrc`/`htr`/`hA6` が前提に残る）。`fgCircuit_of_H` の入力（未証明の H）は変更なし。

### 11.6 次の束

(1) `hdRun`（MachineDefinesRun）の供給: `synthesizeFromConst` が読む `ci`/`envR`/`envR'` が run の開始環境と一致すること（`RunSnap`）と、entry constant の 3 事実の関係を run の外から示せるか。(2) `RunReader` を kernel で扱える形（`partial` helper の外出し）にするか MetaM 検査器として固定するか。(3) 他 3 root へ同形の `…R` 連鎖と `hsrc`。

## 12. S1g（Issue `sparkle-fg-circuit-pilot` の次の束）: hdRun の供給、run の存在、他 3 root

土台 `4948898c`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は最初の commit で 1 回だけ）: `Tools/ShippingFGCircuitLinked.lean`、`Tools/ShippingFGCircuitLinked2.lean`、`Tools/ShippingFGCircuitFinal4.lean`、`Tools/ShippingFGCircuitRoots4.lean`、`Tests/Gen5/FGCircuitPilotCheck6.lean`。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT6 AXIOMS`: 36 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で、approved/done ではなく、下のどの接続も「閉じた経路」ではない。

### 12.1 作業 1: `hdRun`（MachineDefinesRun）の供給

**S1f の `MachineDefinesRun` は供給の足場にならない**（訂正）。その `w1`（getConstInfo）、`w5`（最初の getEnv）、`w3`（run 本体の開始）は、`RunsTo` の式を満たす任意の world で、run の連鎖に結ばれていない。値 `ci`/`envR` を固定するだけなので、連鎖で伝わる性質（`ReadsAt`）から導けない。そこで連鎖に結んだ形を作った。

- `MachineDefinesLinked`（`Tools/ShippingFGCircuitLinked.lean`）: `core_chain` の連鎖 `w --coreHead--> w1 --getConstInfo--> w2 --getEnv--> w3 --synthesizeFromConst（その最初の getEnv は w3）-->` について、同じ 3 事実（`certifiedShape?` = none、`mixedCertifiedShape?` = none、`machineShape? = some shape`）を要求する。消費側（`machine_run_of_coreC`、`machineRunJQC_of_closesC`、`synthesizeCombinationalCore_machine_soundC`）は `core_chain` で分解する写し（`…R` の証明の写し）。endpoint 連鎖は `Linked2.lean`（`RunLocal2` の機械的な写し。`MachineDefinesRun` → `MachineDefinesLinked`、名前の `R` → `C`）。`hTop_of_leaf4`、`counterLoop_artifact_atC`、`counterLoop_final4D` は `Final4.lean`。
- **供給**: `machineDefinesLinked_of_env`。既存の machineDefines の補題（`machineDefines_at_chain` / `machineDefinesR_of_env` / `readsSupply_of_quiet`）の形を run 局所に写した。前提は `Start`（`AdmCtx` と `JQ 0`）、`hquiet : ∀ u, L.O.quiet u → ReadsAt e cref u`（DG-ENV の quiet 強化。単一の `L` に対する前提として置いた）、`GetEnvFrame`（`getEnv` の枠の法則）、環境 `e` の事実（`e.find? X`、2 つの拒否、`machineShape?`）。既存の `readsSupply_of_quiet` は 2 つ目の `getEnv` の存在を前提に取るので、そのまま使わず `envR'` を要求しない形で書き直した。
- **`counterLoop_final4`**: 仮説は `L lvl hstart hr hquiet hg hgates hRead hE`。`hdRun` は無い（`machineDefinesLinked_of_reader` で導く）。`hgates : EntryGates (envAt cref w) X` は、`entry₀ env X` が `certifiedShape?`/`mixedCertifiedShape?` で拒否されるという**開始環境 1 個の事実**（第 3 の事実 `machineShape?` は `RootReader` の連言）。`counterLoop_final4D` は linked 境界を仮説に持つ版。

**導けない部分（何が要るか）**:

| 前提 | 内容 | 要るもの | FG の行 |
|---|---|---|---|
| `hquiet` | quiet な world はどれも開始環境と同じ導出引数（`instancePredicate`/`userInliner`/`structEnv`）を持つ | `O.quiet` は `Laws L` の不透明な述語。DG-ENV の `L'`（`QuietStrength`）を `L` に取り込む行が要る | C.EN-4 / ENV |
| `GetEnvFrame` | `getEnv` が Core 状態の環境を変えない | `ST.Ref.get` は `@[extern] opaque`。`CellPrem`（C.EN-4）の `ReadWorld` 等から `EnvFrameEnd` は出る（`ShippingGen5EnvFrame3`）が、`GetEnvFrame` との接続は確認していない | C.EN-4 |
| `hgates` | 入口定数の 2 つの拒否 | `entryConst` は `userInliner env`/`instancePredicate env` に依る。`ci` 部分だけなら決まるが、`inlinedConst inl ci` は抽象環境では kernel で評価できない。環境 1 個の値としては SNAPSHOT6 で確認 | h_A_P06（env 水準） |

### 12.2 作業 2: run から出る事実と、残る名前付き前提

- `root_find_of_run`: run の連鎖の `getConstInfo X` の world は `ReadsAt (envAt cref w)` を持つので、`X` は開始環境の定数（`hE` の**存在**の部分。`hquiet` だけで出る。`QuoteFact` は不要）。
- `QuoteAt`（定数の内容が引用と一致。条件は上の lookup）と `ReaderAt`（入口定数に対する `machineShape?` と `dataOfAt` の結果）を、lookup を条件とする名前付き前提にした。`rootEnv_of_lookup` で `RootInEnv` と `RootReader` が出る。`counterLoop_final5` の仮説は `L lvl hstart hr hquiet hg hgates hquote hreader`。
- S1f の `RunSnap`（3 つの読み取り world の環境が**等しい**）は不要になった。連鎖で伝わる弱い `ReadsAt`（find? の包含 + 3 導出引数の等号）で足りる。`RunQuote` の「`ci` が `defnInfo`」は `QuoteAt`、`RunReader` は `ReaderAt`。
- **供給できていないもの**: `QuoteAt`（C.EN-4 の `QuoteFact`、ENV cache）、`ReaderAt` の `dataOfAt` の結果（`partial` の helper を呼ぶ。DG-DATAOF / DG-COVER / DG-ENV）。`machineShape?` の結果は `ReaderAt` に残る。

### 12.3 作業 3: 他の 3 root

4 root とも `LeafFacts`（`decide`）が成り立つ（arbiterSignal も `insts = []` の register leaf）ので、`DesignTransport` は `designTransport_of_leaf` の経路で 4 root とも供給される。**この束には leaf でない root は無い**。

- `hsrc`（D.D-3）: `src_eq_of_states`（`counterLoop_src_eq` の一般形。root 固有の項を使わない）、`loop_states`（`Signal.loop` の状態列。`truncLoop` で切った生き信号を使う）、`hst_of_loop`、`hsrc_of_states` を作り、`shift4Loop_hsrc`（レジスタ列: `machine_reset`/`machine_writes`/`machine_result`）、`counterEnableLoop_hsrc` と `arbiterSignal_hsrc`（`Signal.loop`: `machine_reset`/`machine_writes`/`machine_result`/`machine_source`。arbiter は `DomainConfig` 多相のまま）を kernel で供給した。仮説は `RootReader` のみ。
- 各 root の `X_final4`（`machine_traceL_of_regsC` を `shift4Loop` 用に追加）と `X_final5`: counterLoop と同じ形。arbiterSignal は `hB : BoundaryRowsInEnv` が残る。
- 非 leaf の root が来た場合に要るもの（今回は適用なし）: `NoRawBelow` と lookup の一致（`Tools/ShippingGen5DCEntryT.lean` の `childMap_transport`、`runModuleTG_transport`）、`hsrc` は呼び出し stage（`ExtStage`）に対する帰納、`DesignTransport` は instance の oracle を通る。

### 12.4 Check6 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck6`、893 jobs、exit 0）

- `FGCIRCUIT6 SIGNATURES`: `MachineDefinesLinked`、`machineDefinesLinked_of_env`、`root_find_of_run`、`rootEnv_of_lookup`、`X_final4`/`X_final5`（4 root）、`X_hsrc`（3 root）の期待型を**型全体**で独立に書いて `isDefEq` で照合。mutant（premise の環境、root の design、shape/data、`Start`/`hr`/`hquiet`/`GetEnvFrame`/`hgates` の欠落、旧 `MachineDefines`/`hsrc`/`hdRun` の追加、world の結び 3 種、flag、名前、root 間の入れ替え）を棄却。
- `FGCIRCUIT6 HYPS` / `REMAINING`: 全 final 定理の仮説名と型。`hw`・`ReflectsAll`・`hA6`・全 world の `MachineDefines`・`MachineDefinesRun`/`Linked`・`hsrc`・`DesignTransport` は仮説に無い。
- `FGCIRCUIT6 AXIOMS`: 36 名、標準 axiom のみ。
- `FGCIRCUIT6 SNAPSHOT6`: この build の環境 1 個で、4 root それぞれについて `EntryGates`（2 つの拒否）、`machineShape?`、`dataOfAt`（fuel 1000000）の結果が endpoint の `machineData` と全構造で一致し、10 個の 1 フィールド摂動と他 root のデータを棄却。**環境 1 個の値**で、任意の run についての `hquiet`/`hgates`/`hRead` の kernel の文ではなく、全前提が同時に満たされる例でもない（`Laws`・run・`Environment` の閉じた項は作っていない）。
- `FGCIRCUIT6 STREAMS`: **別種の証拠**。kernel が `counterLoop.val 0 = 0`、`counterLoop.val 3 = 3`、`shift4Loop (pure 5)` の `val 3 = 0`、`val 4 = 5` を証明する（観測 0/3 の形）。`hsrc` が `p.src` と等しいとする観測が自明な流れでないことを示すだけで、前提の充足とは無関係。

### 12.5 root ごとの状況と残る仮説（FG の行 ID）

| root | 閉じたもの（条件付き） | 残る仮説 |
|---|---|---|
| counterLoop | `hdRun` 消去（final4）、`hsrc`、leaf `DesignTransport`、`Start`+`hr`、final5 | `Laws L`・`hstart`（A.P-02）、`hr`（A.P-04）、`hquiet`+`GetEnvFrame`（C.EN-4/ENV）、`hgates`（h_A_P06 の env 水準）、`hRead`/`hE`（final4）または `hreader`/`hquote`（final5。DG-DATAOF/COVER/ENV、C.EN-4 QuoteFact） |
| shift4Loop | 同上（レジスタ列の `hsrc`） | 同上 |
| counterEnableLoop | 同上（`Signal.loop` の `hsrc`） | 同上 |
| arbiterSignal | 同上（`DomainConfig` 多相の `hsrc`） | 同上 + `hB`（`BoundaryRowsInEnv`: ENV） |

`fgCircuit_of_H` の入力（未証明の H）は変更なし。

### 12.6 次の束

(1) `hquiet`/`GetEnvFrame` と `CellPrem`（C.EN-4）の接続（`GetEnvFrame` を `CellPrem` から導けるか、`L'` の取り込み方）。(2) `hgates` を env 水準の決定可能な検査器にするか、`inlinedConst` の性質から出すか。(3) `QuoteAt`/`ReaderAt` の供給（`partial` helper の外出し、または MetaM 検査器として固定）。(4) 非 leaf の root への持ち上げ。

## 13. S1h（Issue `sparkle-fg-circuit-pilot` の次の束）: hquiet/GetEnvFrame の接続、hgates の検査器、QuoteAt/ReaderAt の移送、非 leaf root の調査

土台 `74d5ca1d`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は最初の commit で 1 回）: `Tools/ShippingFGCircuitS1hFrame.lean`、`Tools/ShippingFGCircuitS1hGates.lean`、`Tools/ShippingFGCircuitS1hQuote.lean`、`Tests/Gen5/FGCircuitPilotCheck7.lean`。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT7 AXIOMS`: 19 名、標準 axiom のみ）。`MachineDefinesLinked` の定義は変えていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で、approved/done ではない。

### 13.1 作業 1: hquiet / GetEnvFrame と CellPrem（C.EN-4）

- **`GetEnvFrame` は独立の前提ではなくなった**: `getEnvFrame_of_readWorld : ReadWorld cref → GetEnvFrame`（`CellPrem` の成分 `hc`。`getEnvFrame_of_cellPrem` は `CellPrem` 全体から）。`envFrame_of_envFrameEnd` は `EnvFrameEnd`（`endW` 形）から `RunsTo` 形への一般補題。
- **`hquiet` は CellPrem から導けない**: `hquiet : ∀ u, L.O.quiet u → ReadsAt e cref u` は不透明な述語 `L.O.quiet` の全称で、`CellPrem` に現れない。`hquiet_of_strength` は `QuietStrength L L' e` の `→` 向きが `L'` に対する `hquiet` そのものであることを示すだけ（構成済みの `L'` が要る）。
- **証明が使っていたのは 1 点だけ**: run の連鎖の `coreHead` の後の world `w1` で `ReadsAt (envAt cref w) cref w1`。これは開始 world で自明（`readsAt_self`）で、`EnvFrame (coreHead X)`（1 つの MetaM 動作の環境枠）から出る（`readsAt_after_head`）。そこで `machineDefinesLinked_of_head`、`root_find_of_head`、`machineDefinesLinked_of_reader_head`、`counterLoop_final6` は `hquiet` と `GetEnvFrame` の代わりに `hhead : EnvFrame (coreHead X)` と `hcell : ReadWorld cref` を取る。
- **残る**: `hhead`。`coreHead` は `IO.getEnv`・（`SPARKLE_PROFILE` 時の）ファイル IO・`sparkleSynthDepth.get`/`sparkleFvarValueMap.get` を実行する。ref の get は `CellOK`（`CellPrem`）で足りるが、IO 動作は class-D の `ioEnv` 行（`DRow`、U3 で未供給）で、「IO 動作は `cref` のセルを変えない」法則が要る。`ReadWorld cref` 自体も `CellPrem` の成分（実ランタイムでは前提）。

### 13.2 作業 2: hgates の検査器

`entryGatesB (env) (X) : Bool`（`Tools/ShippingFGCircuitS1hGates.lean`）は `entry₀ env X` を引き、`certifiedShape? = none` と `mixedCertifiedShape? = none` の 2 つの `isNone` を検査するだけ。`entryGatesB_sound`（true ⇒ `EntryGates`）、`entryGatesB_complete`、`entryGatesB_iff`、`not_entryGates_of_false`。意味保存を Bool の名前に置き換えていない（`EntryGates` の 2 条件そのもの）。`counterLoop_final7` は `hgates` を `entryGatesB (envAt cref w) X = true` に替えた。
`Environment` は閉じた kernel 項ではないので `decide` では評価できない。4 root の評価は、コンパイル済みの関数を MetaM で走らせる（Check7 の SNAPSHOT7: 4 root で `true`、certified な組合せ回路の対照 `combControl` で `false`）。これは**環境 1 個の値**で、任意の run の開始環境についての kernel の文ではない。

### 13.3 作業 3: QuoteAt / ReaderAt の供給

`dataOfAt`・`machineShape?` は `partial` helper を呼び、`MachineData` は `Lean.Expr` を含み（`Expr.eqv` は extern）、健全な Bool 等価検査器は、現在の方式では未実装（不可能性は証明していない）。kernel でできる範囲として、これらの事実が環境に依るのは `find? X`・`instancePredicate`・`userInliner`・`structEnv` だけであることを使った移送を供給した（`Tools/ShippingFGCircuitS1hQuote.lean`）: `ReadsAt env₀ cref w`（開始 world が `env₀` を読む）と、開始環境に root がある（run から出る: `root_find_of_head`）ことから、`entryGatesB`・`QuoteAt`・`ReaderAt` が `env₀` から開始環境へ移る（`entryGatesB_of_readsAt`、`quoteAt_of_readsAt`、`readerAt_of_readsAt`）。`counterLoop_final8` の前提は `L lvl env₀ hstart hr hhead hcell hread hgatesB hquote hreader`。
減ったもの: 「任意の run の開始環境についての 3 つの評価の文」が、「1 つの検査済み環境 `env₀` についての同じ 3 つの文（MetaM で確認する）」と「環境の同定 `ReadsAt env₀ cref w`（DG-ENV C0）」に分かれた。残るもの（FG の行 ID）: `QuoteAt env₀`（C.EN-4 `QuoteFact`）、`ReaderAt env₀`（DG-DATAOF/COVER/ENV）、`ReadsAt env₀ cref w`（DG-ENV C0）。`env₀` が具体環境であること（kernel の閉じた項としての供給）は、現在の方式では未供給（不可能性は証明していない）。snapshot は 1 つの env、`lvl = (fun _ => 1000000)` での評価で、任意の `lvl` についての `ReaderAt` の供給ではない。

### 13.4 作業 4: 非 leaf の root

選んだ root: **`synth_hftPcieOutByte`**（`Tests/IP/Bus/PCIeHFTTest.lean:89`、S0 一覧の Tests/IP/Bus。`hftPcieLoop`（`IP/Bus/PCIeHFT.lean`）を包む）。プローブ（`kjob lake env lean`、build 済み環境）: `certifiedShape?` = none、`mixedCertifiedShape?` = none、`machineShape?` = some（insts = [`Sparkle.IP.Net.HTTP.httpGetByte`, `Sparkle.IP.Bus.PCIe.tlpCplByte`]、slots 17、runs 3、loops 0）。つまり machine 経路で、`EntryGates` 型の条件は S1 の経路にそのまま乗る。`Examples/HierarchicalCPU` の `twoStageAdder` は組合せ回路で machine 経路ではないため選ばなかった。
足りないもの（読んだ範囲。未ビルド・未検証の調査）:
1. `LeafFacts` は `insts = []` を含み、`leaf_topShips_of_run`（Bridge:50 と Final3/Final4 の写し）、`leaf_instFree_of_run`、`designTransport_of_leaf`、`hTop_of_leaf2/3/4`、`genGP_root`/`genGP_root_canon`（Cover）、`src_eq_of_states`（`ExtStage … 0 = id`）、`machine_ships_wiredC` の `hnoI`/`hsl`/`hSS` が leaf 専用。`hTop` には `TopShips`/`ChildShips`（Gen2Defs）を使う非 leaf の経路（`StepStmt`、`t1_of_stepPF_ND`、`T1Stmt`）があるが、具体 root に対する `StepStmt` の無条件の証明は見つかっていない。大。
2. 子 2 個（`@[hardware_module]`）の各 package（`genGP` の `Acc (CallRel K) X` を子の行を通した整礎性で）、子ごとの `RootReader`/`machine_closes`/`MachineDefines`、`ResetNk`。
3. `hsrc`: `ExtStage` に対する帰納と子の package `src` の再帰（`loop_states`/`hsrc_of_states` は状態列部分で再利用できる見込み）。中〜大。
4. `DesignTransport`: `childMap_transport`/`runModuleTG_transport`（`Tools/ShippingGen5DCEntryT.lean`）に `NoRawBelow` と lookup 一致が要る。中。
5. 機械の endpoint 定理（`machine_*`、`machineData`）が `synth_hftPcieOutByte` に対して生成されるか、`insts` 付きの shape で `dataOfAt` が正しいデータを返すかは未確認（SNAPSHOT 型の MetaM 検査が要る）。`MachineDefinesLinked`・`EntryGates`・`QuoteAt`/`ReaderAt`・`root_find_of_head` は `insts` に依らない形。
実装は次の束。

### 13.5 Check7 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck7`、897 jobs、exit 0）

- `FGCIRCUIT7 SIGNATURES`: `getEnvFrame_of_readWorld`、`machineDefinesLinked_of_head`、`root_find_of_head`、`counterLoop_final6/7/8`、`entryGatesB_sound/complete`、`entryGatesB_of_readsAt`、`quoteAt_of_readsAt`、`readerAt_of_readsAt` の完全な期待型を独立に書いて `isDefEq`（default 透過度。`match` 補助関数の違いを吸収するため）で照合。40 mutant 棄却（検査ごとに数える。以前の 41 は sound/transfer の 7 件に 8 を足した数え間違い。`isDefEq` は default 透過度で whitelist 以外の定義も展開しうるので、「whitelist だけを展開する」とは言わない。他 root の head 枠、end world の `ReadsAt`＝別の run の world、head/cell/read 前提の欠落、別の env / root / Post / data、移送の逆向き、検査器と命題の取り違え）。
- `FGCIRCUIT7 HYPS`/`REMAINING`: final6/7/8 の仮説名と型。`hquiet`（quiet 述語の全称）・`GetEnvFrame`・`hw`・`hA6`・`MachineDefines*`・`hsrc`・`hdRun`・`DesignTransport` は仮説に無いことを検査。
- `FGCIRCUIT7 AXIOMS`: 19 名、標準 axiom のみ。
- `FGCIRCUIT7 SNAPSHOT7`: 上のとおり、環境 1 個の値（4 root で `entryGatesB` = true、quote が pilot の定数と一致、SNAPSHOT6 を再実行、対照で false）。全前提が同時に成り立つ例ではない。

### 13.6 残る仮説（counterLoop_final8 の形）と次の束

`Laws L`・`hstart`（A.P-02）、`hr`（A.P-04）、`hhead`（C.EN-4: IO 動作の環境枠）、`hcell : ReadWorld cref`（C.EN-4 CellPrem）、`hread : ReadsAt env₀ cref w`（DG-ENV C0）、`hgatesB`（h_A_P06 env 水準）、`hquote`（C.EN-4 QuoteFact）、`hreader`（DG-DATAOF/COVER/ENV）。他 3 root への final6〜8 の持ち上げは機械的（未実施）。次: `hhead` の IO 枠法則、`env₀` の具体化の仕方、非 leaf root（§13.4 の 1〜5）。

## 14. S1i（Issue `sparkle-fg-circuit-pilot` の次の束）: hhead の導出、CheckedStart、4 root への持ち上げ、非 leaf の一歩

土台 `a4c6e62d`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は最初の commit で 1 回）: `Tools/ShippingFGCircuitS1iHead.lean`、`S1iEnv.lean`、`S1iRoots.lean`、`S1iChild.lean`、`Tests/Gen5/FGCircuitPilotCheck8.lean`。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT8 AXIOMS`: 27 名、標準 axiom のみ）。`MachineDefinesLinked` と `Laws` は変えていない。新しい law は足していない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は**条件付き**で、下のどの接続も「閉じた経路」ではない。

### 14.1 作業 1: hhead（`EnvFrame (coreHead X)`）

`coreHead X` は一直線の MetaM 動作: `IO.getEnv "SPARKLE_PROFILE"`、（変数があるときだけ）stderr とファイルへのログ IO、副キャッシュ（`SideRef`）と `sparkleSynthDepth`/`sparkleChildCache` の `ST.Ref.get/set`、深さ制限の `throwError`。
- **導けた部分**: `envFrame_coreHead X (hcell : CellPrem MkRefd mref cref) (hio : HeadIO …) : EnvFrame (coreHead X)`。`ST.Ref` の get/set と `throwError` は `CellPrem`（`ReadWorld` と `CellOK`）から出る（join point を含む do ブロック全体を、構文に沿った小さな tactic `ef_step` で分解。`letFun`/`ite`/`bind`/`pure`/get/set/throwError の 7 種）。
- **現時点で供給経路が見つかっていない部分 = `HeadIO`（2件のIO動作の義務）**: (1) `EnvFrame (liftM (IO.getEnv "SPARKLE_PROFILE"))`、(2) `∀ msg, EnvFrame (liftM (profLogIO true msg))`（`profLogIO false` は `pure ()` として証明済み）。足りないもの: 既存の法則はどれも IO 動作の `envAt cref` を語らない。`Laws` の `frame`/`frameQ`/`same`（`FramedA.ioEnv`）は `cv`/`sv`/`dv`/quiet だけ、`QuietStrength` は強化した `L'` の連言として `ReadsAt` を足すだけで、`frameQ_plus` は class-D の行（`DRow.ioEnv`）を `¬ DRow p` で除外している。`ReadWorld` は `ST.Ref` の get の法則。つまり「IO.getEnv とログ IO は `cref` のセルを変えない」は、(1) は `IO.getEnv` 1 件、(2) は profile ログ（複数の IO 動作の合成。「2 個の primitive」ではない）についての義務で、`Laws`/`CellPrem`/`QuietStrength`/`ReadWorld` からは**供給経路が今のところ見つかっていない**（導出不能の証明はない）。
- **最小の形**: `HeadAt X mctx mref cctx cref w`（`coreHead` の run が開始 world `w` から到達する world だけ: `∀ s w1, RunsTo (coreHead X) … w s w1 → envAt cref w1 = envAt cref w`）。`headAt_of_frame`（`EnvFrame` から）、`headAt_of_cellPrem`（`CellPrem` + `HeadIO` から）。`readsAt_after_headAt`、`root_find_of_headAt`、`machineDefinesLinked_of_headAt`/`_of_reader_headAt`、`counterLoop_final9`（final8 の `hhead : EnvFrame` を `HeadAt X w` に）、`counterLoop_final9C`（`CellPrem` + `HeadIO` から）。
- 減ったもの: 全 world の `EnvFrame (coreHead X)` が、run の開始 world 1 点の `HeadAt`、あるいは（`CellPrem` が供給される前提で）2件のIO動作の義務（`HeadIO`）になった。`hr` は前件のまま。

### 14.2 作業 2: `CheckedStart`（env₀ と開始環境を 1 つの名前付き前提に）

- `CheckedEnv lvl env₀ X ty val dd`: `root : ∃ d, RootInEnv env₀ X ty val d`（**型の上の文**: `env₀.find? X = some (.defnInfo d)`、`d.levelParams = []`、`d.type = ty`、`d.value = val`。`ty`/`val` は宣言の閉じた kernel 項）、`gates : entryGatesB env₀ X = true`、`reader : ReaderAt lvl env₀ X dd`。
- `CheckedStart lvl env₀ cref w X ty val dd`: `CheckedEnv` + `link : ReadsAt env₀ cref w`（DG-ENV C0）。`startFacts_of_checked`: run が供給する lookup（`root_find_of_headAt`）とあわせて、開始環境の `EntryGates`、`RootInEnv`、`RootReader` が出る。`quoteAt_of_rootInEnv`（`QuoteAt` は `root` から）。
- **型の上で示せる範囲**: `entry₀_of_rootInEnv`、`entryGatesB_of_rootInEnv`: `root` があれば `env₀` の入口定数は `entryConst true false [] (.defnInfo d) (instancePredicate env₀) (userInliner env₀) (structEnv env₀)` で、ゲート検査器はこの項への 2 つの `isNone` 検査である。つまり `gates` と `reader` が `env₀` に依るのは、閉じた宣言 `d` のほかは `ReadsAt` が等しいとする 3 つの導出引数だけ。**評価が要る部分**: `certifiedShape?`/`mixedCertifiedShape?`/`machineShape?`/`dataOfAt` の値（`userInliner` は環境を展開し、`dataOfAt` は `partial` helper。`Environment` は閉じた kernel 項でない）。これは MetaM の評価（SNAPSHOT8a）で、前提の供給とは数えない。
- 現在の方式では `Environment` の値を kernel の閉じた項として供給していない（未供給。`mkEmptyEnvironment` は IO で、不可能性の証明はない）。したがって今の範囲は、`root` の型の上の文と、評価した 1 環境の値（SNAPSHOT8: 1 つの env、`lvl = (fun _ => 1000000)` での評価）までで、任意の `lvl` についての `ReaderAt` の供給ではない。

### 14.3 作業 3: 他の 3 root

`X_final4D`（S1g の `X_final4` から `hquiet`/`GetEnvFrame` を作る 2 行を除き、`hdRun` を仮説に取る形。証明は S1g のコピー）と、`X_final10`（4 root: `counterLoop_final10`、`shift4Loop_final10`、`counterEnableLoop_final10`、`arbiterSignal_final10`）。仮説は `L lvl env₀ hstart hr hhead(HeadAt) hcell(ReadWorld cref) hchk(CheckedStart)`。final6〜8 の形が 4 root で揃った。
- **arbiter の `hB`**: `BoundaryRowsInEnv (envAt cref w)` は 3 つの補助定数が開始環境に**存在する**という文で、`ReadsAt` は一方向（開始 ⊆ env₀）なので移送できない。そこで逆向きの包含を 3 つの名前に限った名前付き前提 `ContainsAt env₀ cref w boundaryNames` を足し、`BoundaryRowsInEnv env₀`（1 環境の文。MetaM で評価）から `boundaryRows_of_contains` で `hB` を出す。`arbiterSignal_final10` の追加仮説は `hB0 hcont`。`hB` を `ReadsAt` の形に**そのままは寄せられない**（positive な存在を `ReadsAt` は運ばない）。

### 14.4 作業 4: 非 leaf の root（`synth_hftPcieOutByte`）

- 実装: `topShips_transport`（`S1iChild.lean`）: `TopShips p n X b raw D → TopShips p n X b raw D'` を、`PostEntry b raw D D'`、`NoRawBelow D raw.name (n+1) raw`、`NoRawBelow D raw.name (n+1) (checkedOptimize b)`、「`b.body` の instance は top を指さない」から導く。既存の `resetNk_transport`、`runModuleTG_transport`、`postEntry_lookup_ne` を使い、新しいのは `TopShips` への持ち上げと `bodyInstOuts_congr`。`designTransport_of_noRawBelow`（`DesignTransport` の形）。計算できる検査器 `noRawBelowB`（`noRawBelowB_sound`）と `instsNeB`（`instsNeB_sound`）で、側条件を実際の出力で評価できる。
- leaf の補題で済まないもの（実装で確かめた）: `topShips_design_irrel`/`designTransport_of_leaf` は `raw`/`b`/`checkedOptimize b` が instance-free であることで設計 `D` を無視する。instance があると `TopShips` は `childMap D.modules`、`ResetNk n raw D kids`、`bodyInstOuts (childMap D.modules) b.body` を通して `D` を読む。`D' = topMap … D` は top（`raw.name`）だけを置き換えるので、移送は「top を指す instance が下にない」（`NoRawBelow`）に帰着する。この文は `raw`/`b` の中身（instance の targets）についての事実で、leaf では機械 trace から instFree を読んだ（`leaf_instFree_of_run`）が、非 leaf では**読む補題が今のところ見つかっていない**ので、`topShips_transport` の仮説として残る。`NoRawBelow` は「top に戻らない」条件で、グラフ全体の非巡回性は十分条件の一候補にすぎず、必須とは言わない。`designTransport_of_noRawBelow` は**全 n** の `NoRawBelow` を要求し、SNAPSHOT8b の深さ 1〜6 の評価はそれを供給しない。
- SNAPSHOT8b（**プローブ `hftOutProbe`**＝`(hftPcieLoop ..).outByte` の compile。private な `synth_hftPcieOutByte` 自身ではない。S1l で記録訂正）: machine 経路（certified none、mixed none、`machineShape?` some、insts 2、slots 17）。raw の instance は `httpGetByte` と `tlpCplByte`、`D₀`/`D'` の modules は等しい（top は含まれない）、`raw` は `synthesizeCombinationalCore`、`b`/`D'` は外側の `synthesizeCombinational` の**別々の 2 回の実行**で、比べたもの。PostEntry は `dropZeroWidth` **または** `mergeChecked` の選言で、どちらの枝が成り立ったかは Check8 が計算してログに出す（S1l）。同一 run の PostEntry の証拠とは数えない。`noRawBelowB` は raw と `checkedOptimize b` で深さ 1〜6 すべて true、`instsNeB` true。対照（子を top に見立てる）は false。これは**プローブの 2 回の実行の値**で、任意の run の kernel の文ではない。
- `CheckedStart`（root/gates/reader/link を 1 つの binder に束ねたもの）は束ねただけで、前提の**減算ではない**（台帳に数えない）。
- 残る（未実装）: (1) `TopShips p n X b raw D` 自体（machine 経路で `insts ≠ []`。`LeafFacts` が leaf 専用）、`NoRawBelow` を run から出す補題（instance の module 名の分離。非巡回性は十分条件の一候補で必須とは断言しない）。(2) 子ごとの package（`genGP` の `Acc (CallRel K) X`）、`RootReader`/`machine_closes`/`MachineDefines`。(3) `hsrc`: `src_eq_of_states` は `ExtStage … 0 = id`（`insts = []`）を使う。非 leaf は `ExtStage … k` を子の package の `src` に結ぶ帰納が要る（`ShippingGen5SemExt` の `calleeOut`/`ExtStage_succ` が材料）。(4) `machineData` が `insts` 付きで正しいか（`dataOfAt` の評価）。

### 14.5 Check8 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck8`、909 jobs、exit 0）

- `FGCIRCUIT8 SIGNATURES`（66 mutant。head/ReadsAt/CheckedStart の「end world」対照は**同じ run の終点 w'** で、MDLBODY の独立 world `u` 対照とは別物）: `envFrame_coreHead`、`root_find_of_headAt`、`machineDefinesLinked_of_headAt`、`counterLoop_final9`/`9C`、`CheckedEnv.mk`、`CheckedStart.mk`、`HeadIO.mk`、`startFacts_of_checked`、4 root の `X_final10`、`boundaryRows_of_contains`、`topShips_transport`、`noRawBelowB_sound`、`instsNeB_sound` の完全型（仮説・結論・binder の種類）を独立に書いて `isDefEq` で照合。66 mutant 棄却: 別の root の head、同じ run の終点（end world w'）での head / `ReadsAt` / `CheckedStart`、接続を切ったもの（head 事実・cell・IO 事実・link・`NoRawBelow` の欠落）、別の env / root / Post / data、別の root の final 定理、移送の逆向き。
- `FGCIRCUIT8 MDLBODY`（S1j、S1h 指摘 2）: `MachineDefinesLinked` の定義の本文の独立な写し `MDLBody` と一致することを確認した上で、本文を比べる対照 3 件を、SIGNATURES の 66 とは別に数えて棄却（3 mutant）: (a) 連鎖の前半（coreHead / getConstInfo / getEnv）の全削除、(b) `coreHead` の開始を独立した world `u` に替えたもの（独立 u 対照）、(c) 本文（`synthesizeFromConst`）の開始を独立した world `u` に替えたもの。
- `FGCIRCUIT8 HYPS` / `REMAINING`: 各 final の仮説名と型。`hquiet`・`GetEnvFrame`・全 world の `EnvFrame`・`hdRun`・`MachineDefinesLinked`・`hsrc`・`DesignTransport`・`hw` は仮説に無い。
- `FGCIRCUIT8 AXIOMS`: 27 名、標準 axiom のみ。
- `FGCIRCUIT8 SNAPSHOT8a/8b/8c`: 上のとおり（8b はプローブ `hftOutProbe` の 2 回の実行）。1 環境・プローブの実行の値で、全前提が同時に成り立つ例ではない。

### 14.6 残る仮説と次の束

4 root の final10 の仮説: `Laws L`・`hstart`（A.P-02）、`hr`（A.P-04）、`hhead : HeadAt`（C.EN-4: `coreHead` の IO 2 件の環境枠。`CellPrem` + `HeadIO` から）、`hcell : ReadWorld cref`（CellPrem）、`hchk : CheckedStart`（`root` = 型の文、`gates`/`reader` = 1 環境の評価、`link` = DG-ENV C0）、arbiter は `hB0`/`hcont`。
次: (1) `HeadIO` の 2 件（IO 枠）。(2) `reader`/`gates` の評価を kernel の文に（`dataOfAt` の `partial` helper の外出し）。(3) 非 leaf: `NoRawBelow` を run から出す補題と `TopShips` の machine 経路（insts 付き）、`hsrc` の `ExtStage` 帰納。

## 15. S1k（Issue `sparkle-fg-circuit-pilot` の次の束）: 非 leaf root `synth_hftPcieOutByte` の最終定理の型の固定と、証明できた部分

土台 `8b4c135b`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は各 lib 1 回）: `Tools/ShippingFGCircuitS1kRoot.lean`、`S1kStmt.lean`、`S1kPkg.lean`、`Tests/Gen5/FGCircuitPilotCheck9.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない（`FGCIRCUIT9 AXIOMS`: 12 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は**条件付き**で、閉じた経路ではない。Issue の状態は変えていない。
注: root は `Tests/IP/Bus/PCIeHFTTest.lean:89` の `private def` なので名前を指せない。同じ本体の公開版 `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte` を新ファイルに置いた（Check8 の `hftOutProbe` と型・値が同一であることを SNAPSHOT9 で検査）。元の private 定義そのものについての定理ではない。

### 15.1 手順 1: プローブ（`kjob lake build Tools.ShippingFGCircuitS1kRoot`、exit 0）

- 子 2 個の endpoint は**既にある**: `httpGetByte`（`Tests/Compiler/ShippingMachineCombTest.lean` の `#machine_endpoint`）と `tlpCplByte`（今回 `#machine_endpoint` で生成。通った）。どちらも `machineData`/`machine_ok`/`machine_body`/`machine_closes`/`machine_sound`/`machine_ships`/`machine_ships_comb` を持つ。
- root は `#machine_endpoint` が通り、`machineData`/`machine_ok`/`machine_body`/`machine_sound` はあるが、**`machine_closes`・`machine_ships` は生成されない**（instance を持つ module には出ない。コマンドの設計）。root の closing は未供給。
- reader の接続: `dataOfAt`（fuel 1000000）は 3 宣言とも `machineData` リテラルと**全構造で等しい**値を返す（`dataExprOf d == literalExpr`）。root の `insts` = [`httpGetByte`, `tlpCplByte`]（2 個）、子は `insts = []`。3 宣言とも `entryGatesB` true、machine 経路（certified none、mixed none、`machineShape?` some）。1 環境の値であり、任意の run の kernel の文ではない。
- `CD`（`SourceDenotesMono` の核）には**利用者定義定数の適用規則も構造体射影の規則もない**。root の値 `fun … => HFTPcieOut.outByte (hftPcieLoop …)` に `CD` の導出を作れない（未供給。規則の追加は既存ファイルの変更）。

### 15.2 手順 2: 完全な型（`HftFinalStmt`、`synth_hftPcieOutByte_final : HftFinalStmt`）

`X_final10` と同じ結論 `(∃ raw, PostRun …) ∧ ∃ mm p, RootArtifactMono (envAt cref w) (genGP …) (PostRun …) root shHft mm b D' p` で、前提は:
`L lvl env₀`、`hstart`（A.P-02）、`hr`（A.P-04）、`hhead : HeadAt`（C.EN-4）、`hcell : ReadWorld cref`、`hchk : CheckedStart`（root の `machineData`、型 `hftRootType`・値 `hftRootValue`）に、**子の package の前提** `hreadH`/`hreadT : RootReader lvl (envAt cref w) child child.machineData`（DG-DATAOF/COVER/ENV）、**名前付きの 4 obligation**:

| 前提 | 内容 | FG 行 | 状態 |
|---|---|---|---|
| `hcd : HftObCD` | `CD [] hftRootValue (MonoTy shHft) synth_hftPcieOutByte` | D.D-1 / D.D-4（`CircCV`） | 未供給（`CD` に規則がない） |
| `hsrc : HftObSrc` | `genGP` が返す package の `src` が宣言の観測 | D.D-3 / DG-SEM | 未実装（`ExtStage … 2` を子の package の `src` に結ぶ帰納。`src_eq_of_states` は `ExtStage … 0 = id`） |
| `htop : ∀ p, genGP … = some p → HftObTopCore …` | run の `raw` が核の設計 `D₀` で `TopShips p n`（`hdRun` を前提に取る） | D.D-4（T1 の machine 経路、insts 付き） | 未実装（`LeafFacts` は leaf 専用。子の package と `ChildShips`） |
| `hnoraw : HftObNoRaw` | `raw`/`checkedOptimize b`/`b` の instance が top を指さない | D.T-4 | 未実装（run から出す補題がない。1 回の compile では `noRawBelowB` が true: Check8 SNAPSHOT8b） |

`hdRun`（`MachineDefinesLinked`）は前提ではなく、`hchk`/`hhead`/`hcell` から導出して `htop` に渡す。`hgates`/`hRead`/`hE` も `hchk` から出る。`hsrc`・`hcd` は root 固有の文、`htop`/`hnoraw` は run についての文。

### 15.3 手順 3: 証明した部分

- `genGP_root_kids`（`genGP_root` の一般化）: root の callee が全て table の leaf 行なら `genGP … root = some p`、`p.decl = root`、`p.d = g.d`、`p.kD = kDOf g.d`（`Acc (CallRel K) root` を子の leaf 行から、`genS_leaf_isSome`）。
- kernel の事実（`decide +kernel`）: 3 宣言の `GenWF`、子の `insts = []`、root の `insts.map (·.1) = [httpGetByte, tlpCplByte]`、`kDOf = 5`、`ShapeMatchesMono shHft … 5`、`monoGo [] hftRootType = some shHft`。
- `synth_hftPcieOutByte_final`: 上の 4 obligation と子の reader から、`genGP` の被覆・`EndpointLink`・`SourceDenotesMono`（`RootInEnv` + `hcd`）・`ObservationsEqualMono`・`HasConcretePackage`（`htop` + `hnoraw` から `topShips_transport` で `D'` へ）を導く。**`DesignTransport` は前提でなく証明**になった（`hnoraw` が前提）。
- 証明していない（上表の 4 件）。子の `MachineDefines`/`closes`、`ResetNk` は `htop` の中身として残る。

### 15.4 Check9 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck9`、916 jobs、exit 0）

- `FGCIRCUIT9 SIGNATURES`: 最終定理と `HftFinalStmt` の完全な型、4 obligation、root の kernel 事実、`genGP_root_kids` を独立に書いた文面と `isDefEq`（default 透過度）で照合。**41 mutant 棄却**（検査ごとに数える: 最終定理と `HftFinalStmt` の各 14 = 28、`HftObCD` 1、他の 3 obligation 4、kernel 事実 7、`genGP_root_kids` 1）: run の root / head / post が別、`hchk` が別宣言の data、head・cell・子 reader・4 obligation の各欠落、core obligation の `hdRun` 欠落、子 reader や結論が end world、instance 順の入れ替え、`kD = 4`、別の shape、callee 欠落、`TopShips` を印刷後の設計で述べたもの。注: `GenWF d = true` のように両辺が評価で `true` になる命題は `isDefEq` が同一視するため、wf/leaf の対照は偽の文（`= false`、`≠ []`）にした。
- `FGCIRCUIT9 HYPS`/`REMAINING`: 前提名 `L lvl env₀ hstart hr hhead hcell hchk hreadH hreadT hcd hsrc htop hnoraw` と型。`hquiet`・`GetEnvFrame`・全 world の `EnvFrame`・`hdRun`・`hgates`/`hRead`/`hE`・`hP`・`DesignTransport`・`EntryWitness` は前提に無いことを検査。
- `FGCIRCUIT9 AXIOMS`: 12 名、標準 axiom のみ。
- `FGCIRCUIT9 SNAPSHOT9`: 上の 15.1（1 環境の値）。`machine_closes` が root に**無い**ことも検査（生成されたら更新が必要）。

### 15.5 残り

`hcd`（`CD` の規則）、`hsrc`（`ExtStage` 帰納）、`htop`（machine 経路 `TopShips`、子の package/`ChildShips`/`ResetNk`、root の closing の供給）、`hnoraw`（run から「top に戻らない」を出す。全体の非巡回性は十分条件の一候補で、必須とは言わない）、`hreadH`/`hreadT` の `ReaderAt env₀` + `ContainsAt` への還元（S1i の root と同様）、S1i までの `HeadIO`・`reader`/`gates` の kernel 化。

4 root の final10 の仮説: `Laws L`・`hstart`（A.P-02）、`hr`（A.P-04）、`hhead : HeadAt`（C.EN-4: `coreHead` の 2件のIO動作の義務。`CellPrem` + `HeadIO` から）、`hcell : ReadWorld cref`（CellPrem）、`hchk : CheckedStart`（`root` = 型の文、`gates`/`reader` = 1 環境の評価、`link` = DG-ENV C0）、arbiter は `hB0`/`hcont`。
次: (1) `HeadIO`（2件のIO動作の義務）。(2) `reader`/`gates` の評価を kernel の文に（`dataOfAt` の `partial` helper の外出し）。(3) 非 leaf: `NoRawBelow` を run から出す補題と `TopShips` の machine 経路（insts 付き）、`hsrc` の `ExtStage` 帰納。

## 16. S1l（Issue `sparkle-fg-circuit-pilot` の次の束）: S1i/S1j の記録訂正、counterLoop の CheckedStart を有限入力に接続、HeadIO の完全型

土台 `8b4c135b`（par/fgc-s1）。追加ファイル（既存の定理は書き換えていない。lakefile 登録は 1 回）: `Tools/ShippingFGCircuitS1lReader.lean`、`Tests/Gen5/FGCircuitPilotCheck10.lean`。既存ファイルの変更は記録訂正のみ（`Tests/Gen5/FGCircuitPilotCheck8.lean` の SNAPSHOT8b とラベル、`Tools/ShippingFGCircuitS1iChild.lean` の冒頭コメント、本書 §14）。sorry・axiom・native_decide・TRUSTED・新しい law はない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で、approved/done ではない。非 leaf の root と §15 は触っていない（S1k）。

### 16.1 作業 A: 記録訂正

- **SNAPSHOT8b**（Check8）: コンパイルしたのは private な `synth_hftPcieOutByte` 自身ではなくプローブ `hftOutProbe`（`(hftPcieLoop ..).outByte`）で、`synthesizeCombinationalCore` と外側の `synthesizeCombinational` を**別々に 2 回**実行して比べている。「ONE compile」「本体 = synth_hftPcieOutByte の」「first disjunct」の断言は外した。`PostEntry` は `dropZeroWidth` **または** `mergeChecked` の選言で、どちらの枝が成り立ったかを計算してログに出すようにした（この build: 両方 true、つまり `mergeChecked` はこの run で恒等）。**同一 run の PostEntry の証拠とは数えない**（`b` と `raw` は別の run）。
- **`S1iChild` 冒頭**: 「evaluated instead of assumed」を、評価は MetaM での観測で仮説の kernel 供給ではない、に訂正。
- **Check8 の対照の呼び分け**: SIGNATURES の head/`ReadsAt`/`CheckedStart`/find の対照は**同じ run の終点 w'**（end-world 対照）。MDLBODY の (b)(c) は無関係な独立 world `u`（independent-u 対照）。二つは別物としてラベルを付けた（SIGNATURES の 66 件は end-world 対照を含み、MDLBODY の 3 件は別集計）。
- **§14 の語**: `HeadIO` は「2件のIO動作の義務」（profile ログは複数の IO 動作の合成）、「導けない」は「現時点で供給経路が見つかっていない」、`NoRawBelow` の非巡回性は十分条件の一候補、`designTransport_of_noRawBelow` は全 n を要求し深さ 1〜6 の snapshot は供給しない、`CheckedStart` の 1 binder への束ねは減算ではない、に直した。

### 16.2 作業 B: counterLoop の CheckedStart（gates / reader）を有限入力に接続

**完全な型（Check10 で独立に書いた文面と isDefEq）。**
- 一般（どの root でも）: `EntryOfDecl d ip ui se := entryConst true false [] (.defnInfo d) ip ui se`、`GatesOnDecl d ip ui se`（`certifiedShape?` と `mixedCertifiedShape? … ip` が none）、`ReaderOnDecl lvl d ip ui se dd`（`machineShape? … = some dd.shape ∧ dataOfAt lvl … = some dd`）。`checkedEnv_of_decl : RootInEnv env₀ X ty val d → GatesOnDecl d (instancePredicate env₀) (userInliner env₀) (structEnv env₀) → ReaderOnDecl lvl d … dd → CheckedEnv lvl env₀ X ty val dd`。つまり `CheckedEnv.gates`/`reader` は、**閉じた宣言 `d`（`RootInEnv`）と環境由来の 3 引数**についての文になった。
- counterLoop: 名前付き Prop 2 つ。
  - `CounterLoopExtern`（環境に依らない閉じた 3 事実）: `packTupleInputs counterLoopValue = counterLoopValue`、`rootFloat counterLoopValue = counterLoopValue`、`counterLoopValue.find? (isAppOfArity runCircuitH 8) = none`。
  - `CounterLoopEnvFacts env₀`: `∃ d, RootInEnv env₀ counterLoop counterLoopType counterLoopValue d ∧ machineShape? false [] (.defnInfo d) (structEnv env₀) = some counterLoop.machineData.shape`、`userInliner env₀ counterLoopValue = counterLoopValue`、`userInliner env₀ counterLoopType = counterLoopType`、`instancePredicate env₀ counterLoopValue = false`、`(structEnv env₀).proj Signal.loop = none`。
  - 加えて `hlvl : lvl counterLoop.machineData.shape.body = 1000000`（`ReaderAt` は `lvl` を量化する。これまでの snapshot の fuel の前提を明示した）。
- `counterLoop_checkedEnv_of_finite lvl env₀ hlvl hx hf : CheckedEnv lvl env₀ counterLoop counterLoopType counterLoopValue counterLoop.machineData`、`counterLoop_final11`（`counterLoop_final10` の `hchk : CheckedStart` を `hlvl hx hf hlink` に替えた形。仮説: `L lvl env₀ hstart hr hhead hcell hlvl hx hf hlink`）。

**kernel が評価したもの（証明済み、標準 axiom のみ）。**
- gates: `certifiedShape?` は閉じた宣言に対して kernel が評価（`counterLoop_gates`）。`mixedCertifiedShape?` は `instancePredicate` を**値の 1 点だけ**で引く（`unifiedInstanceRoot`/`hierInstRoot` が `isInst e`）ので、`ip counterLoopValue = false` があれば none。`entryConst` が宣言自身になること（`entryOfDecl_eq`: `userInliner` が値と型を固定すれば、`machineShape?` を評価せずに `inlinedConst` が宣言に戻る）。
- reader のデータ: `mixedGatePeel`、`machRoot`（`proj Signal.loop = none` のとき）、`srcDomOf`（`Expr.find?` の事実のとき）、`machDom?`、`machOuts?`、`dataOfCore`（fuel 1000000）を経て**構造全体** `counterLoop.machineData` まで kernel が評価（`counterLoop_dataOfAt`）。これは DG_DATAOF_FREEZE が「evidence-only」とした kernel instance の 1 件に当たる（ただし 4 つの閉じた事実と `proj` の 1 点を仮説に取った条件付き）。
- 問い合わせ先の調査: `mixedCertifiedShape?` が `ip` を引くのは値の 1 点のみ、`dataOfAt` が `structEnv` を引くのは `proj Signal.loop` のみ（MetaM で引数にログを付けて実行して確認。`machineShape?` は `prodMatch` 等を多数引くが、これは仮説側）。

**行 ID ごとの残り義務（供給していない。評価は Check10 SNAPSHOT10 で 1 環境について確認しただけ）。**

| 義務 | 内容 | FG 行 |
|---|---|---|
| `hx.pack` / `hx.rootFloat` | `partial` の `packTupleInputs` / `rootFloat`（extern の `liftLooseBVars` を呼ぶ）の値。kernel は評価できない | DG-DATAOF T-X、DG-COVER S-COV-FLOAT |
| `hx.find` | `Expr.find?` は `opaque` の extern。`runCircuitH` を含まない | 行 ID 未割当（T-X と同種の extern 振る舞い。新しい行が要るなら reviewer 判断） |
| `hf.root` の `machineShape?` | `partial` の機械リーダ（`machConv` 等）。kernel は評価できない | DG-COVER、C.RK-6、C.CV-4（h_A_P06 の shape 部分） |
| `hf.root` の `RootInEnv` | `env₀` の `X` が型・値の閉じた宣言 | C.EN-4 QuoteFact、DG-ENV |
| `hf.ui_val` / `ui_ty` | `userInliner env₀` が値・型を固定（`userInliner` は環境を展開する） | DG-ENV |
| `hf.ip_val` | `instancePredicate env₀`（`@[hardware_module]` 属性表）が値で false | DG-ENV |
| `hf.proj_loop` | `userProjection? env₀ Signal.loop = none` | DG-ENV |
| `hlvl` | `lvl` の fuel | DG-DATAOF（Q5） |
| `hlink` | `ReadsAt env₀ cref w` | DG-ENV C0 |
| 変更なし | `hstart`（A.P-02）、`hr`（A.P-04）、`hhead`（C.EN-4、§16.3）、`hcell`（C.EN-4 CellPrem） | |

**減ったもの / 減っていないもの。** `CheckedEnv.gates`（`entryGatesB env₀ X = true`）と `reader`（`ReaderAt`）という env₀ 全体への評価文が、閉じた宣言と 3 引数の 1 点ずつの事実（上表）に分かれ、gates と reader のデータ部分は kernel の計算になった。`machineShape?`・`pack`・`rootFloat`・`find?` は kernel で評価できない（現在の方式では未供給。不可能性は証明していない）。仮説の個数は増えた（1 つの `CheckedStart` が 9 つの個別事実になった。内訳は `hx` 3 + `hf` 5 + `hlvl` 1 で、`hlink` は別掲（9 に含めない）。`hf.root` 自身も存在証人と複数の事実を含む 1 件なので、9 は仮説の最小単位の数ではない）ので、台帳には数えない（FG -0 +0 / T1 -0 +0）。

### 16.3 作業 C: HeadIO の完全型と許容する実行範囲

**型（`Tools/ShippingFGCircuitS1iHead.lean` の定義そのまま）。**
```lean
structure HeadIO (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) : Prop where
  getEnv : EnvFrame (liftM (IO.getEnv "SPARKLE_PROFILE") : MetaM (Option String)) mctx mref cctx cref
  log : ∀ msg, EnvFrame (liftM (profLogIO true msg : IO Unit) : MetaM Unit) mctx mref cctx cref
-- EnvFrame x mctx mref cctx cref := ∀ w a w', RunsTo x mctx mref cctx cref w a w' → envAt cref w' = envAt cref w
```
2 件の IO 動作の義務: (1) `IO.getEnv "SPARKLE_PROFILE"`、(2) `profLogIO true msg`（`msg` は全ての文字列。複数の IO 動作の合成）。`profLogIO false msg = pure ()` は証明済み（`ef_prof_false`）。成功した run（`RunsTo` は `EST.Out.ok`）だけを問うので、IO 例外で終わる run は対象外。

**許容する実行範囲（この義務が許す IO 動作。これ以外を含む `coreHead` には使えない）。**
- `IO.getEnv "SPARKLE_PROFILE"`: プロセス環境変数 `SPARKLE_PROFILE` の**読み取りのみ**。他の環境変数の読み書き、`setenv` は含まない。
- `SPARKLE_PROFILE` が**未設定**のとき: ログ動作は `pure ()`（IO なし）。
- `SPARKLE_PROFILE` が**設定されている**とき（`profLogIO true msg`）: (a) `IO.eprintln msg`（stderr への書き込み）、(b) `Sparkle.Compiler.flushStderr`（`(← IO.getStderr).flush`）、(c) `IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append`（固定パスのファイルを追記で開く）、(d) `h.putStrLn msg`、(e) `h.flush`。他のファイル・ネットワーク・サブプロセスは含まない。
- どの動作も `ST.Ref`（`cref`、`mref`）に触れず、`Core.State` の `env` を変えない、が義務の内容。

**必要になる新しい law の凍結ドラフト（【未承認・凍結前のドラフト】。供給済みとして使っていない。コードにも入れていない）。**
```
IOHeadFrame (draft, UNAPPROVED, not used):
  IOHeadAct : (α : Type) → IO α → Prop   -- 閉じた inductive。生成規則は次の 3 つの原始 + 閉包のみ
    | getEnvProfile : IOHeadAct _ (IO.getEnv "SPARKLE_PROFILE")
    | profLog       : IOHeadAct _ (profLogIO true msg)   -- ∀ msg
    | bind / pure   : 上記の bind と pure で閉じる（制御は ite のみ）
  law IOHeadFrame (mctx mref cctx cref) :
    ∀ α (x : IO α), IOHeadAct α x → EnvFrame (liftM x : MetaM α) mctx mref cctx cref
```
意味: 「列挙した IO 動作を `liftM` した MetaM は `envAt cref` を変えない」。実ランタイムでは `cref` は `ST.Ref` のセルで、列挙した動作は stderr・固定パスのファイル・環境変数の読み取りしか行わず、そのセルを参照しない、という実行モデルの主張（Lean の `IO.getEnv`/`IO.FS.Handle` は外部関数で、kernel の中身が無い）。既存の C.EN-4 `CellPrem`/`QuietStrength`/`Laws` に吸収されるか、新しい行になるかは reviewer の判断。**これが承認されるまで `HeadIO` は仮説のまま**で、`hhead`（`HeadAt`）は引き続き final の仮説である。

### 16.4 Check の出力

`kjob lake build Tests.Gen5.FGCircuitPilotCheck10`（911 jobs、exit 0。Check8 も同じ build で再実行）:
- `FGCIRCUIT10 SIGNATURES`: `checkedEnv_of_decl`、`CounterLoopExtern.mk`、`CounterLoopEnvFacts.mk`、`counterLoop_dataOfAt`、`counterLoop_gates`、`counterLoop_checkedEnv_of_finite`、`counterLoop_final11` の完全型を独立に書いて `isDefEq` で照合。**27 mutant 棄却**（ゲート/reader/lvl/extern/環境事実の欠落、別の値・型・データ・post root、`ip` の極性、`proj` を引く名前、`runCircuitH` の arity、fuel、end-world 対照＝同じ run の終点 w' での head 開始・link・結論の環境）。
- `FGCIRCUIT10 HYPS`/`REMAINING`: `counterLoop_final11` の仮説名と型。`hchk : CheckedStart`・`hgatesB`・`hquote`・`hreader` は仮説に無い。
- `FGCIRCUIT10 AXIOMS`: 13 名、標準 axiom のみ。
- `FGCIRCUIT10 SNAPSHOT10a/b/c`: 1 環境の評価（仮説の供給ではない）。(a) `CounterLoopExtern` と `CounterLoopEnvFacts` の各事実、`machineShape?` が読んだ `dataOfAt` の全体が `counterLoop.machineData`。(b) `ip` を値以外で全て true、`proj`/`fields` を `Signal.loop` 以外で何か返すように替えてもゲートとデータは不変（問い合わせ先の確認で、独立性の証明ではない）。(c) 別 root の値では別のデータ（または none）、`instancePredicate` は `httpGetByte` で true（`ip_val = false` は空虚ではない）。
- Check8（再実行）: 66 mutant（SIGNATURES）、MDLBODY 3 mutant、AXIOMS 27 名、SNAPSHOT8b は上記の訂正後の文言。

### 16.5 次

(1) `hx` の 3 事実と `machineShape?` の kernel 供給（`partial` 本体の外出しか、対応する law の凍結）。(2) `CounterLoopEnvFacts` の環境側 4 点（`ui`/`ip`/`proj`/`RootInEnv`）を `ReadsAt`＋属性表の文に落とす。(3) `HeadIO` の凍結ドラフト（§16.3）の reviewer 判断。(4) 他の 3 root（shift4Loop/counterEnableLoop/arbiterSignal）へ `X_final11` を持ち上げる（counterLoop と同じ手順。問い合わせ先は root ごとに調べ直す）。

## 17. S1m（Issue `sparkle-fg-circuit-pilot` の次の束）: `CD` の設計穴 — 利用者定義の展開と構造体射影の規則（**FREEZE DRAFT: reviewer 承認待ち**）

土台 `07752341`（par/fgc-s1）。注: 土台 07752341 には §16 が無かった（S1l は別に進め、後で merge した）。追加ファイル（既存は書き換えていない。lakefile 登録は各 lib 1 回）: `Tools/ShippingFGCircuitS1mCD.lean`、`Tests/Gen5/FGCircuitPilotCheck11.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない（`FGCIRCUIT11 AXIOMS`: 16 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。Issue の状態は変えていない。**この規則集合は FREEZE DRAFT であり、reviewer が承認するまで `HftObCD` の型にも final 定理にも使わない**（既存の `CD`・`HftObCD` は変えていない）。

### 17.1 問題と設計方針

`hcd : HftObCD = CD [] hftRootValue (MonoTy shHft) synth_hftPcieOutByte` が供給できない理由は、`CD` に (1) 利用者定義定数（`hftPcieLoop`）の適用の規則も、(2) 構造体射影（`HFTPcieOut.outByte`）の規則も**無い**ことである。これは証明の埋め残しではなく規則集合の設計穴（reviewer の判断）。そこで `CD` を**書き換えず**、新しい関係 `CDX` を足した。

- `CDX env ρ e α v` / `TDX env ρ e T` は**固定の `env : Environment`** をパラメータに持つ。実体は 1 つの帰納族 `DX env : Val → Expr → Res → Prop`（`Res.ty T` / `Res.val α v`）で、`TDX`/`CDX` はその `abbrev`。1 つの族にしたのは、関数性の証明を**導出に関する `induction`** にするため（§17.4）。
- `CD`/`TD` の 18+5 規則は**同じ型のまま** `DX` に入っている（`env` を通すだけ。Check11 が構造比較）。埋め込み `cdx_of_cd : CD ρ e α v → CDX env ρ e α v`、`tdx_of_td` を証明した（任意の `env`）。`circCV_to_X : CircCV env X α v → CircCVX env env X α v`。
- 表示対象は従来どおり **Lean の値そのもの**（各規則の値は同じ Lean 定数で組む）。新規則は値を `v` のまま次の導出へ渡す（`unf`: 結論の `v` は前提の `v`）。**新規則が元の Lean 式の意味を保つこと自体は S1m では証明していない**（下 17.2 の「対応する Lean の操作」は監査対象。S1p の訂正は §17.8）。

### 17.2 新しい 5 規則の完全な型（`Tools/ShippingFGCircuitS1mCD.lean`、`DX` のコンストラクタ）

記法: `CDX env ρ e α v` = `DX env ρ e (Res.val α v)`。以下の関数は全て Lean で書いた**カーネルが評価できる**構造再帰（`Expr.instantiate` は opaque extern なので使えない。自前の `instE`/`betaApp`/`instLE`。Check11 OPS が Lean の `instantiate1`/`Expr.beta`/`instantiateLevelParams` と一致することを実環境の定義 21 件で比較した。**これは監査であり、規則の意味保存の証明ではない**: §17.8）。

| 規則 | 型（前提 → 結論） | 対応する Lean の操作（監査対象。意味保存は今回証明していない: §17.8） |
|---|---|---|
| `unf` | `headStop e = false` → `unfoldAt env e = some e'` → `CDX env ρ e' α v` → `CDX env ρ e α v` | delta + beta。`unfoldAt env e`: `e` の頭が定数 `c`、`env.find? c = some (.defnInfo d)`、`d.levelParams.length = ls.length` のとき `betaApp (instLE d.levelParams ls d.value) (args)`。`headStop e` は頭が `CD` の primitive（`Signal.pure/register/mux/loop`、`HAdd/HAnd/HOr/Complement`、`Signal.beq`、`BitVec.ofNat` 他 14 頭）か `bvAbbrevRow` の行のときだけ true（primitive の規則が意味であり、展開しない） |
| `beta` | `headRedex env e = some e'` → `CDX env ρ e' α v` → `CDX env ρ e α v` | 頭がラムダ/`let`/射影の適用（`(fun x => b) a …`、`(let x := v; b) a …`、`(p.i) a …` で頭が `whStep` で進む）。`unf` が引数を代入して作る redex を縮める。beta/zeta/射影の頭の一歩 |
| `zeta` | `e = .letE n A v b nd` → `coreHead A = false` → `CDX env ρ (instE b v 0) α r` → `CDX env ρ e α r` | `let` の zeta（代入）。`coreHead A = false` は型の頭が `Nat/Bool/DomainConfig/BitVec/Signal` でないとき。この型は旧 `letE` 規則の `TD` が扱えないので重ならない（`coreHead_td : TDX … A T → coreHead A = true`） |
| `projStep` | `e = .proj S i x` → `whStep env x = some x'` → `CDX env ρ (.proj S i x') α v` → `CDX env ρ e α v` | 構造体引数の弱頭 1 歩（zeta、beta、頭定数の delta、射影の下の 1 歩、射影の iota） |
| `projCtor` | `e = .proj S i x` → `appFn x = .const ctor ls` → `env.find? ctor = some (.ctorInfo cv)` → `cv.induct = S` → `(appArgs x).length = cv.numParams + cv.numFields` → `(appArgs x)[cv.numParams + i]? = some fld` → `CDX env ρ fld α v` → `CDX env ρ e α v` | 構造体のコンストラクタ適用への射影（iota）。構造体の情報は `env` の `ctorInfo` から読む |

構造体射影 `HFTPcieOut.outByte dom x` は射影関数（`defnInfo`、値は `fun dom self => self.1` の `Expr.proj`）なので、`unf` で `Expr.proj` になり、`projStep`/`projCtor` が扱う。**型の付いた Lean 構造体値**（構造体型の値そのものを `ρ` に束縛する）は今回の規則に入れていない（構造体ごとに Lean の型と射影関数の行が要り、境界の行が増えるため。必要なら次の束で reviewer に諮る）。

**停止性・整礎性**: 導出は有限の木（帰納 `Prop`）であり、`unf` を使った導出が存在するとは**その導出が有限に閉じる**ことと同じ。再帰・相互再帰の定義は `unf` を繰り返すだけでは導出が閉じない（`brecOn`/`rec` に規則が無い）。**今回の走査はそこで停止する。導出は未供給**（走査は導出の不存在証明ではない）。燃料もサイズ尺度も使わない（`CD` の関数性は `sizeOf e` による整礎再帰だったが、`unf` は式を大きくするので使えない。S1m の関数性は導出の `induction`）。

### 17.3 環境との結び付き（ReadsAt / CheckedStart 流）

`CDX` の `env` は固定のパラメータである。run の環境との結び付きは**仮定**として足す: 具体的な導出は有限表 `Δ : Name → Option DefRow`（定数名 → 宇宙パラメータと値の `Expr`）と `Γ : Name → Option CtorRow` を使い、`EnvDefs env Δ`（`Δ c = some r` なら `env.find? c = some (.defnInfo d)`、`d.levelParams = r.lps`、`d.value = r.value`）と `EnvCtors env Γ` を**仮定**する。補題 `cdx_unf_tbl`（`unf` の表版）と `cdx_projCtor_tbl`（`projCtor` の表版）が、表の行から規則の前提を作る。`env := envAt cref w`（`CheckedStart` と同じ world）として、`EnvDefs`/`EnvCtors` は `hchk` 流の「表と環境の一致」で、**meta 検査（Check の SNAPSHOT: 表と環境の `ConstantInfo` の一致）**であり kernel は環境を見ない。これは `RootInEnv` と同じ種類の境界だが、**`EnvDefs`/`EnvCtors` は実 run 環境について追加の未供給内容**であり、meta 照合で支払い済みとは扱わない（S1p 訂正: §17.8）。

### 17.4 関数性（証明した）

`dx_fun : DX env ρ e r → DX env ρ e r' → r.kind = r'.kind → r = r'`（導出に関する `induction`。`kind` は型/値の別）。系: `cdx_fun : CDX env ρ e α v → CDX env ρ e α' v' → α = α' ∧ HEq v v'`、`tdx_fun`、`cdx_eq`（同じ型なら値が等しい）、`circCVX_functional : ConstValueFunctional (CircCVX env)`。規則の衝突は頭の定数・構造の違いで反駁する（`unf` と primitive は `headStop`、`unf` と `beta` は `unfoldAt_none_of_beta`、`projStep` と `projCtor` は `whStep_ctor`、`zeta` と `letE` は `coreHead_td`）。**関数性は仮定を置かずに成り立つ**。ただし `cdx_fun` は**新しい関係 `CDX` の一意性**であり、元の Lean 式との一致ではない（§17.8）（`EnvDefs` 等を使わない。`unfoldAt env e` は `env` と `e` の関数）。`ty` と `val` の導出が同じ式にあり得るので、statement は同じ kind に限る（`env` が任意なので式の頭が型であり値でもあり得る）。

### 17.5 hftPcie のどの部分項が何を要するか（Check11 SNAPSHOT11、1 環境の値）

`Check11` の recognizer は規則の関数（`unfoldAt`/`headRedex`/`whStep`/`instE`）をそのまま使い、`root` の値を走査して**規則が尽きる所**を出力する（証明ではなく走査）。観測（`hftRootValue` から）:

- 5 つのラムダの本体 `HFTPcieOut.outByte dom (hftPcieLoop dom rx v s d c)`: `unf`（射影関数 `outByte` → `Expr.proj`）→ `projStep`（`hftPcieLoop` の delta）→ `zeta` 2 回（`let ep := mmioEndpoint …; let emit := httpGetEmitter ep.writePulse`。型は構造体なので `zeta`）→ `projCtor`（`HFTPcieOut.mk` 適用、`outByte` の項）→ `HttpEmitOut.byte dom (httpGetEmitter …)` → `unf`/`projStep`（`httpGetEmitter` → `burstEmit` → `runCircuitH …`）。ここまでは新規則で**進む**（走査が 454 節点、定義 22 個を展開: `Prod.fst`、`eqK`、`httpGetByte`、バイト定数 `cG…`、`runCircuitH`、`burstEmit`）。
- **規則が尽きる所**（`MISSING`、走査の stuck。S1p 時点の更新は §20.4）: `Expr.proj Prod 0 (… (PProd#0 (List.rec …) …))` ×17。つまり `circuit do` の状態を持つ `runCircuitH` の中の **`List.rec`（再帰子。`List.brecOn` による構造再帰）の適用**。`CDX` に再帰子の規則（コンストラクタ引数の iota）が無い。これを足すか（`List` の具体値が必要）、`circuit do` のモナド（`Circuit` 型、`Signal.reg` と `<~`）を別の規則にするかが次の設計問題。
- `tdFail`（`TD` に無い束縛/let の型）: なし。

したがって **`hcd` は今回の `CDX` でも導出できない**（供給しない）。`HftObCD` は未供給のまま。次に要るのは (a) `List.rec` 等の再帰子 iota（`env` の `recInfo` の規則を読む）と、(b) 構造体値の型付き規則（必要なら）。いずれも reviewer の判断を仰ぐ（本書は設計の草案）。

### 17.6 範囲外（明記）

- **回路の核のみ**。`Dyn` への拡張はしない。利用者定義の型（型 abbrev の展開）は `TDX` に入れていない。
- 再帰子（`rec`/`casesOn`/`brecOn`/`WellFounded.fix`）、`match`、型クラス引数の解決、`Id.run`/モナドの束縛は規則に無い。
- 構造体値を `ρ` に束縛する型付き規則、`HftObCD` の型の差し替え、`hcd` の供給は今回しない。
- `EnvDefs`/`EnvCtors` と実環境の一致は meta 検査であり kernel の定理ではない。

### 17.7 Check11 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck11`、911 jobs、exit 0）

- `FGCIRCUIT11 SIGNATURES`: 新 5 規則（`DX.unf/beta/zeta/projStep/projCtor`）、埋め込み `cdx_of_cd`/`tdx_of_td`、関数性 `cdx_fun`/`tdx_fun` の完全な型を独立に書いた文面と `isDefEq`（default 透過度）で照合。旧 23 規則（`CD` 18 + `TD` 5）が `env` を通しただけで同一であることを構造比較（`CD` の `sigMux` を `sigPure` と見る control は棄却）。**23 mutant 棄却**: `unf`（stop 条件なし、stop の反転、`ρ` の初期化、結論が `e'`、unfold の向きの入れ替え）、`beta`（`unfoldAt` を使う、結論が `e'`）、`zeta`（core 条件なし、代入なし、条件が true）、`projStep`（`unfold` のみ、`proj` を捨てる）、`projCtor`（inductive の一致なし、引数個数なし、field 添字が `i` のみ、`numParams` のみ）、埋め込み（逆向き、`ρ` の初期化）、関数性（別の env、別の `ρ`、`HEq` なし）、`tdx_fun`（別の env）。
- `FGCIRCUIT11 OPS`: `betaApp`/`instE`/`instLE` が Lean の `Expr.beta`/`instantiate1`/`instantiateLevelParams` と、recognizer が展開した実環境の定義 21 個（引数は loose bvar、宇宙は sample）で一致。誤った代入を検出する control あり。
- `FGCIRCUIT11 AXIOMS`: 16 名、標準 axiom のみ。使える導出の例 `ex_projCtor`（`(3,4).1 ⇓ 3`）、`ex_unf`（`mini := Signal.pure 5` の展開）、`ex_zeta`（構造体型の `let`）が通る。
- `FGCIRCUIT11 SNAPSHOT11`/`MISSING`: 17.5 の走査結果。

### 17.8 訂正（S1p、reviewer 裁定 M2）と意味保存の経路

S1m の以下の文言は今回の証明結果ではなかったので撤回・言い換える。

1. 「健全性（定義的等式）」「各規則は定義的等式」「新規則は値を変えない」: **証明していない**。`Expr` に意味論が無いので、`unfoldAt`/`betaApp`/`instE`/`whStep` が元の Lean 項を保つことは Lean の定理として述べられていない。Check11 OPS の 21 件（`instE`/`instLE`/`betaApp` と Lean の `instantiate1`/`instantiateLevelParams`/`Expr.beta` の比較）は**監査**である。
2. `cdx_fun`/`dx_fun` は**新しい関係 `CDX` の関数性（導出の一意性）**であって、導出の値が元の Lean 項に一致することではない。
3. `projCtor` は**生の `Expr` に対する規則**である。`ctorInfo` の読み取りは、Lean の構造体射影の型の正しさ（その `Expr.proj S i x` が型付けされていること）を保証しない。同じ境界である。
4. `EnvDefs`/`EnvCtors`（実 run 環境の表）は**追加の未供給内容**である。既存の境界（`RootInEnv` 等）と同種だが、meta 照合（Check の比較）で支払い済みとは扱わない。
5. 再帰定義について「導出が存在しない」と書いた箇所（§17.2 停止性、§17.5）は「今回の走査はここで停止する。導出は未供給」に直した。走査は不存在の証明ではない。

**意味保存の経路（2 つ。どちらか）**:
- (a) 型の正しい入力・環境に対して縮約（delta/beta/zeta/射影/iota）が意味を保つこと自体を証明する。`Expr` の型付き意味論が要り、今回も未実装。
- (b) **対象 root で等式証明をカーネルに渡す**: 導出 `h : CDX env [] e α v` を組むとき `v` は規則の値から**構成される** Lean の値であり、結論の型 `HftObCD`（`v := synth_hftPcieOutByte`、元の Lean 定数）は `v` と構成された値が**カーネルの定義的等式**で一致する場合にのみ型検査を通る。つまり (b) は元の Lean 項と展開後の項の等式証明をカーネルに検査させる経路で、**規則の健全性を一般には要らない**（その root について導出が受理された時点で等式が検査済み）。ただし受理される導出が未供給の間、(b) も供給されていない。
S1p の再帰子単位は (b) で扱う（§20.3）。

## 18. S1n（Issue `sparkle-fg-circuit-pilot` の次の束）: 他の 3 leaf root への `X_final11` の持ち上げ

土台 `a24f49c4`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は各 lib 1 回）: `Tools/ShippingFGCircuitS1nRoots.lean`、`Tests/Gen5/FGCircuitPilotCheck12.lean`。sorry・axiom・native_decide・TRUSTED・新しい law はない。S1m の領域（`Tools/ShippingFGCircuitS1mCD.lean`、§17）は触っていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で、approved/done ではない。

### 18.1 証明したもの

`shift4Loop_final11`、`counterEnableLoop_final11`、`arbiterSignal_final11`（`counterLoop_final11` と同じ形。仮説: `L lvl env₀ hstart hr hhead hcell hlvl hx hf hlink`、arbiter は更に `hB0 hcont`）。それぞれ `X_final10` の `hchk : CheckedStart` を `hlvl hx hf hlink` に替えたもの。途中の定理: `X_gates`（arbiter は `_orig`/`_inl` の 2 件）、`X_srcDomOf`、`X_dataOfCore`、`X_dataOfAt`、`X_checkedEnv_of_finite`。共通: `entryOfDecl_inl`（入口定数 = 値を `Vi`、型を `T` に書き換えた宣言）、`checkedEnv_of_inl`、`dataOfAt_of_pieces`、`machRoot_of_head`。標準 axiom のみ（`#print axioms`、Check12 の AXIOMS）。

**kernel が評価したもの（`with_unfolding_all rfl`、最初の試行で全部通った）。** 3 root とも `certifiedShape?`／`mixedCertifiedShape?`（閉じた宣言、gate binder の剥離 `mixedGatePeel` を含む）、`machRoot`／`srcDomOf`、`dataOfFront`、`dataOfCore`（fuel 1000000）を経て**構造全体** `X.machineData` まで。arbiter の `dataOfCore`（binder 16、スロット含む）も通った。評価が止まった部分は**なかった**ので、「止まった部分」の記録はない。残るのは下の名前付き仮説だけ（kernel が評価できない `partial`/extern、環境への問い合わせ）。

### 18.2 counterLoop との違い（root ごとに問い合わせ先を調べ直した結果）

問い合わせ先は `dbgTrace` 付きの述語・`StructEnv` を MetaM で走らせて調べた（Check には入れていない調査。Check12 は「その点以外では不変」を確認する）。
- **`instancePredicate`**: counterLoop は値（binder なし）だが、他 3 root の値は `fun` なので、問い合わせ点は `mixedGatePeel` で剥いだ**本体** `peeledBody V`。`rootFloat`／`Expr.find?` の引数も同じ本体。`packTupleInputs` は入口の値。
- **`structEnv.proj`**: shift4Loop は `Signal.register`（本体の先頭定数）、counterEnableLoop と arbiterSignal は `Signal.loop`。`dataOfAt` が `proj` を引くのはこの 1 名だけ（`fields`／`inst`／`natOf` は `dataOfAt` では引かれない。`prodMatch` 等は `machineShape?`＝仮説側）。
- **`userInliner`**: shift4Loop／counterEnableLoop は値と型を固定する（counterLoop と同じ）。**arbiterSignal は値を変える**（private の状態定数 `stIdle` 等がリテラルになる）ので入口定数は**インライン後の宣言** `{d with value := Vi, type := T}`。`entryConst` は「元の宣言のゲートが none ∧ インライン後で `machineShape?` が some」のとき `inlinedConst` を返す（`entryOfDecl_inl`）。そのため arbiter はゲートを元の値とインライン後の値の 2 つで評価し、`instancePredicate` も 2 点（`peeledBody V`、`peeledBody Vi`）で引かれる。
- `Vi` の閉じた項: `arbiterInlinedValue`。コマンド `quote_inlined%` が**この build の `userInliner env` の出力**を `Expr` の項として定義する（`quote_value%` と同じ引用）。つまり**1 環境のスナップショット**で、`ui_val : userInliner env₀ arbiterValue = arbiterInlinedValue` が名前付き仮説。Check12 が「この build で等しい」「インライナーは arbiter の値を変える（ui_val は自明でない）」を確認する。

### 18.3 名前付き仮説（root ごと）

共通の 2 つの構造に整理した（因子化は下の 18.4）。
- `RootExtern Vi : Prop`: `pack : packTupleInputs Vi = Vi`、`rootFloat : rootFloat (peeledBody Vi) = peeledBody Vi`、`find : (peeledBody Vi).find? (isAppOfArity runCircuitH 8) = none`。（DG-DATAOF T-X、DG-COVER S-COV-FLOAT、find は行 ID 未割当で S1l と同じ扱い。`partial`／`opaque` extern でkernel は評価できない。不可能性は主張しない。）
- `RootEnvFacts env₀ X T V Vi dd projName : Prop`: `root : ∃ d, RootInEnv env₀ X T V d ∧ machineShape? false [] (.defnInfo {d with value := Vi, type := T}) (structEnv env₀) = some dd.shape`（DG-COVER、C.RK-6、C.CV-4、C.EN-4 QuoteFact。`machineShape?` は `partial` の機械リーダ）、`ui_val : userInliner env₀ V = Vi`、`ui_ty : userInliner env₀ T = T`、`ip_val : instancePredicate env₀ (peeledBody V) = false`、`ip_inl : instancePredicate env₀ (peeledBody Vi) = false`（DG-ENV）、`proj : (structEnv env₀).proj projName = none`（DG-ENV）。

| root | `hx` | `hf`（`V` → `Vi`、`projName`） | 追加 |
|---|---|---|---|
| shift4Loop | `RootExtern shift4LoopValue` | `RootEnvFacts env₀ shift4Loop shift4LoopType shift4LoopValue shift4LoopValue shift4Loop.machineData Signal.register` | — |
| counterEnableLoop | `RootExtern counterEnableLoopValue` | `… counterEnableLoopType counterEnableLoopValue counterEnableLoopValue counterEnableLoop.machineData Signal.loop` | — |
| arbiterSignal | `RootExtern arbiterInlinedValue` | `… arbiterType arbiterValue arbiterInlinedValue arbiterSignal.machineData Signal.loop` | `hB0`（`BoundaryRowsInEnv env₀`）、`hcont`（`ContainsAt env₀ cref w boundaryNames`）— `ReadsAt` は存在を運ばない |

共通: `hlvl : lvl X.machineData.shape.body = 1000000`（DG-DATAOF Q5）、`hlink : ReadsAt env₀ cref w`（DG-ENV C0）、`hstart`（A.P-02）、`hr`（A.P-04）、`hhead`（C.EN-4、`HeadIO` は §16.3 の凍結ドラフトのまま）、`hcell`（CellPrem）。shift4Loop／counterEnableLoop では `Vi = V` なので `ip_val` と `ip_inl` は同じ文の重複（弱めてはいない）。

### 18.4 共通構造への因子化

4 root の構造は同じ形（外部ヘルパ 3 事実、環境の 5 点＋root）なので、3 root 分を `RootExtern`／`RootEnvFacts` に因子化した。フィールドは**どれも落としていない**: counterLoop の `CounterLoopEnvFacts` の 5 点（root、`ui_val`、`ui_ty`、`ip_val`、`proj_loop`）に対応する全フィールドを持ち、インライナーが値を変える root のために `ip_inl` と `machineShape?` の対象宣言（インライン後）を追加しただけ（`Vi = V` のとき追加分は元と同じ文）。`counterLoop_final11` と S1l のファイルは書き換えていない（counterLoop 自身の構造は S1l のまま）。arbiter の `hx` は `arbiterInlinedValue`（入口の値）についての文で、元の値についての文ではない（Check12 の `MutCFAExternOnValue` で棄却）。

### 18.5 Check12 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck12`、913 jobs、exit 0、error 0）

- `FGCIRCUIT12 SIGNATURES`: 17 定理（`RootExtern.mk`、`RootEnvFacts.mk`、`entryOfDecl_inl`、`checkedEnv_of_inl`、ゲート 4 件、`dataOfAt` 3 件、`checkedEnv_of_finite` 3 件、3 つの `X_final11`）の完全型を独立に書いて `isDefEq`（default）で照合。**117 mutant 棄却**（検査ごとに数える）: `rootFloat`／`find?`／`packTupleInputs` の引数（本体でなく値）、`runCircuitH` の arity、`instancePredicate` を値で引いたもの（本体でない）、極性、`machineShape?` の対象（インライン前）、インライナーの引数、`proj` を引く名前、fuel、別 root の data／値／型／extern の値／head の root／post の root、arbiter のインライン前の値、fuel・extern・環境事実・`hB0`・`hcont` の欠落、end-world 対照（同じ run の終点 w' での head 開始・link・結論の環境）、他 root の最終定理。
- `FGCIRCUIT12 HYPS`/`REMAINING`: 3 つの final の仮説名と型。`hchk`・`hquiet`・`GetEnvFrame`・`hdRun`・`hsrc`・`hcd`・`htop`・`hnoraw` は仮説に無い。構造のフィールド名も検査。
- `FGCIRCUIT12 AXIOMS`: 24 名（`arbiterInlinedValue` を含む）、標準 axiom のみ。
- `FGCIRCUIT12 SNAPSHOT12a/b/c`: 1 環境の評価（仮説の供給ではない）。(a) 3 root で `RootExtern` の 3 事実、`RootEnvFacts` の各点、`machineShape?` が読んだ `dataOfAt` の全体が `X.machineData`、`EntryOfDecl` がインライン後の宣言。(b) `ip` を 2 つの本体以外で全て true、`proj`／`fields` を 1 名以外で `some`、インライナーを値・型以外で任意の項にしても、ゲート・入口定数・データは不変（問い合わせ先の確認で、独立性の証明ではない。問い合わせ点が本体であることはロギング調査で見つけたもので Check の検査ではない。値だけで true にしてもゲートは不変）。(c) `arbiterInlinedValue = userInliner arbiterValue`、インライナーが arbiter の値を変え shift4Loop／counterEnableLoop を固定すること、shift4Loop の shape に arbiter の値（gate binder 3）を渡すと none か別データ、`httpGetByte` で述語が true。**注（訂正すべき期待）**: データは `machineShape?` が読んだ shape から出るので、gate binder 数とドメインが同じ別 root の値（counterEnableLoop を shift4Loop の shape に）は同じデータを返す。値が効くのは binder 数とドメインを通してで、「別の値は別のデータ」という対照は binder 数が違う root に限る。

### 18.6 残り

(1) `hx` の 3 事実と `machineShape?` の kernel 供給（`partial` 本体の外出しか対応する law の凍結）。(2) `RootEnvFacts` の環境側（`ui`／`ip`／`proj`／`RootInEnv`）を `ReadsAt`＋属性表の文に落とす。arbiter は `arbiterInlinedValue` が 1 環境のスナップショットなので、インライナーの出力の導出（`userInliner` の kernel 評価か名前付き law）も要る。(3) `HeadIO`（§16.3）の reviewer 判断。(4) 非 leaf（§15 の `hcd`／`hsrc`／`htop`／`hnoraw`、S1m の `hcd` 規則）。

## 19. S1o（Issue `sparkle-fg-circuit-pilot` の次の束）: HeadIO の再設計（profile 無効の run 形を先に）

土台 `a24f49c4`（par/fgc-s1）。追加ファイル: `Tools/ShippingFGCircuitS1oHead.lean`、`Tests/Gen5/FGCircuitPilotCheck13.lean`（lakefile 登録は各 1 回）。既存の定理は書き換えていない（記録訂正のみ: S1iHead 冒頭コメント、S1iChild 冒頭コメント、§16.2 の 9 の内訳）。sorry・axiom・native_decide・TRUSTED・新しい law はない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**。Issue の状態は変えていない。S1m/S1n のファイルには触れていない。

### 19.1 記録訂正

- S1iHead 冒頭: 旧「not derivable」「two opaque primitives」を §14 と同期（「供給経路が見つかっていない。導出不能の証明はない」「profile ログは複数の IO 動作の合成」）。∀world のログ義務を法則として採らない旨（所見C）を追記。
- S1iChild 冒頭: 「compile of the probe の one run」を、`synthesizeCombinationalCore` と外側の `synthesizeCombinational` の**別々の 2 回の実行**の観測に同期。
- §16.2 の「1 つの `CheckedStart` が 9 つの個別事実」は `hx` 3 + `hf` 5 + `hlvl` 1。`hlink` は別掲で 9 に含めない。`hf.root` 自身も存在証人と複数の事実を含む 1 件なので、9 は仮説の最小単位の数ではない。

### 19.2 (a) `coreHead` が profile を決める箇所と、狭めた run 形

`coreHead X` の**最初の動作**が `profile := (← IO.getEnv "SPARKLE_PROFILE").isSome`。ログ動作 `logProf` は `profile` が真のときだけ `IO.eprintln`、`flushStderr`、`IO.FS.Handle.mk`、`putStrLn`、`flush` を行う。`profile` は後で `CoreSaved.profile` にも入る（環境には触れない）。

評価した 2 案:
1. **run 局所の前提（採用）**: 開始 world `w` で `IO.getEnv "SPARKLE_PROFILE"` を走らせた結果が `none` で、環境 `envAt cref` を保つ、という run の前提。実環境変数が未設定という Meta の観測は**供給に使わない**（名前付き仮説のまま）。
2. **コンパイル時/オプションの切替**（提案のみ。Elab は変更していない）: `SPARKLE_PROFILE` の読み取りとログ枝を `register_option`/`Options` の値に移す（`Core.Context.options` から読む）と、`coreHead` から `IO.getEnv` と `logProf` が消え、`profile` は純粋な値になる。baseline 保存の論拠: 既定値 `false` では `profile = false` の枝が今と同一（出力 IR・`CoreSaved` の `profile` 欄は同じ）で、IP の出力・成功の run は変わらない。ただし `SPARKLE_PROFILE` を使う既存の運用（環境変数でログを出す）は、オプション指定に変わる（または変数→オプションの橋渡しが別に要る）ので、利用者に見える変更になる。これは compiler の変更なので S1o では実装しない。reviewer 判断。
   **訂正（S1q, §21）**: 上の「`coreHead` から `IO.getEnv` と `logProf` が消え」は誤り。`Options` に移しても `profile` が真の枝（`IO.eprintln`/`flushStderr`/`Handle.mk`/`putStrLn`/`flush`）は `coreHead` に残る。消えるのは `IO.getEnv` だけで、ログ枝は `profile = false` を**純粋な設定/引数で固定**したときにだけ消える。§21 は後者を実装する。

**最小の getEnvProfile frame の正確な型**（`Tools/ShippingFGCircuitS1oHead.lean`）:
```lean
abbrev profileAct : MetaM (Option String) := liftM (IO.getEnv "SPARKLE_PROFILE")
structure GetEnvProfileAt (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) : Prop where
  unset : ∀ (o : Option String) (w1 : Void IO.RealWorld), RunsTo profileAct mctx mref cctx cref w o w1 → o = none
  env   : ∀ (o : Option String) (w1 : Void IO.RealWorld), RunsTo profileAct mctx mref cctx cref w o w1 → envAt cref w1 = envAt cref w
```
全 world の `EnvFrame` ではなく run の開始 world 1 点で、結果を `none` に限る。

### 19.3 (b) 既存の EnvFrame 補題だけでの定理

- `headAt_of_profileOff (X) (hcell : CellPrem MkRefd mref cref) (hg : GetEnvProfileAt mctx mref cctx cref w) : HeadAt X mctx mref cctx cref w`。証明: `coreHead` の run を最初の動作で `RunsTo.bind` により分け、`hg` から `o = none` と `envAt w0 = envAt w`。残りは S1i の `ef_step`（`bind`/`pure`/`ite`/`letFun`/get/set/`throwError`、すべて既存の `EnvFrame` 補題と `CellPrem`）で閉じ、ログの `if none.isSome = true` を `if_neg` で `pure ()` にする。`HeadIO` は使わない。
- `counterLoop_final9P`: `counterLoop_final9` の `hhead` を `CellPrem` + `GetEnvProfileAt` に替えた形（`HeadIO`/`hio` なし）。仮説: `L lvl env₀ hstart hr hcell hg hread hgatesB hquote hreader`。
- 閉じていないこと: `hg` は仮説のまま（`unset` は実行時のプロセス環境、`env` は `IO.getEnv` の環境保存）。`hg` が供給できる経路は未確認で、不可能性も主張しない。profile 有効の run（`o = some _`）は、この形では**保証範囲外**。

### 19.4 (c) FREEZE DRAFT（未承認。台帳に数えない。C.EN-4/Laws に吸収しない。どの定理も使わない）

ログ枝を保証範囲に残す場合の義務。stderr callback と固定 Handle 操作を分ける:
```lean
def logStderrAct (msg : String) : IO Unit := do IO.eprintln msg; Sparkle.Compiler.flushStderr
def logTailAct   (msg : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append; h.putStrLn msg; h.flush
structure LogBranchDraft (mctx mref cctx cref) : Prop where
  stderrPreserves      : ∀ msg, EnvFrame (liftM (logStderrAct msg) : MetaM Unit) mctx mref cctx cref
  fixedHandlePreserves : ∀ msg, EnvFrame (liftM (logTailAct msg) : MetaM Unit) mctx mref cctx cref
```
- `stderrPreserves` は**現在の stderr stream** の `putStr`/`flush` callback（`setStderr` で差し替え可能、`eprintln` は現 stream の `putStr` を呼ぶ）が成功する限り env を書き換えない、という条件で、一般法則ではなく callback ごとの条件として明示する（所見C）。**訂正（S1q）**: 上記は意図の記述で、型としては `stderrPreserves : ∀ msg, EnvFrame (liftM (logStderrAct msg))` は特定の callback/world の条件を持たず、`EnvFrame` は ∀ world なので、「callback ごとの条件」にはなっていない。draft は**記述専用**で、型は条件を表さない。`fixedHandlePreserves` は固定パス・固定 Handle primitive だけの義務。
- 旧 `HeadIO.log`（`∀ msg, EnvFrame (liftM (profLogIO true msg))`）は上の 2 つの連言に分かれるが、`liftM` が IO の bind を MetaM の bind に写す等式（lift の法則）は証明できていないので、同値の定理は置かない（試したが未達。新しい law を足さないため）。
- 採用する場合は追加の未払い義務として差分を再照合する。現在は計上しない。

### 19.5 Check13 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck13`、913 jobs、exit 0）

- `FGCIRCUIT13 SIGNATURES`: `GetEnvProfileAt.mk`、`headAt_of_profileOff`、`counterLoop_final9P`、`LogBranchDraft.mk`（draft）の完全型を独立に書いて `isDefEq`（default 透過度）で照合し、binder の種類も一致。**21 mutant 棄却**: ログ枝を通る形（`o.isSome`）、独立 world からの lookup、end world で自明になる env 前提、unset/env/cell/frame の欠落、frame が無関係な world、結論が end world、旧 `HeadIO` を run 局所の frame の代わりにしたもの、final9P の frame/link/結論の end world、別 root の post、draft の stderr/handle 部分の欠落・flush 欠落・別パス。
- `FGCIRCUIT13 HYPS`/`REMAINING`: `headAt_of_profileOff` = `X hcell hg`、`counterLoop_final9P` = `L lvl env₀ hstart hr hcell hg hread hgatesB hquote hreader`。`HeadIO`/`hhead`/`hio`/`hquiet`/`hdRun`/`hsrc` は前提に無い。
- `FGCIRCUIT13 NOTUSED`: 2 定理の型と値が `HeadIO`・`LogBranchDraft`・`profLogIO`・`envFrame_coreHead`・`headAt_of_cellPrem` を直接参照しない。
- `FGCIRCUIT13 AXIOMS`: 2 名、標準 axiom のみ。

### 19.6 次

(1) `hg` の供給（`IO.getEnv` の run の結果・環境保存。コンパイル時の切替案 19.2-2 を採れば `unset` は消える）。(2) draft の採否（reviewer）。(3) 他の 3 root への `final9P` 相当の持ち上げ（counterLoop と同手順）。

## 20. S1p（Issue `sparkle-fg-circuit-pilot` の次の束）: 単一環境の carrier（M1）、意味保存の経路（M2）、`List.rec` の最初の小単位

土台 `e2301cd4`（par/fgc-s1）。追加ファイル（既存の定理は書き換えていない。コメント 2 箇所のみ訂正: `Tools/ShippingFGCircuitS1mCD.lean` 冒頭の「definitional equality」「has no derivation」）: `Tools/ShippingFGCircuitS1pCD.lean`、`Tests/Gen5/FGCircuitPilotCheck14.lean`（lakefile 登録は各 1 回）。TRUSTED・axiom・sorry・native_decide・新しい law はない（`FGCIRCUIT14 AXIOMS`: 29 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。Issue の状態は変えていない。`Sparkle/Compiler/*` と HeadIO 関連ファイルには触れていない。

### 20.1 M1: 公開 carrier を 1 環境にした

S1m の `CircCVX env := fun env' X α v => … env'.find? X … CDX env [] d.value …` は引用を `env'` で読み、展開を `env` で行うため、**型の上では別環境を許す**（`circCV_to_X` だけが同じ `env`）。S1p:

- `CircCVS : ConstValueRel := fun env X α v => ∃ d, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ CDX env [] d.value α v`。引用と展開が**同じ変数 `env`**。
- 橋: `circCV_to_S : CircCV env X α v → CircCVS env X α v`（`cdx_of_cd`）、`circCVS_to_X`、`circCVX_iff_S`（`env' = env` の下で `CircCVX env env'` と `CircCVS env'` が同値。仮定が要る）、`circCVS_functional : ConstValueFunctional CircCVS`（`cdx_fun`）、`sourceDenotes_to_S`、`declConnect_to_S : DeclConnect CircCV env₀ P Tgt → DeclConnect CircCVS env₀ P Tgt`。
- **run 側**: `CircCVSAt cref w X α v := CircCVS (envAt cref w) X α v`。`circCVS_at_of_getEnv`: `RunsTo getEnv … w e w'` から `CircCVS e X α v ↔ CircCVS (envAt cref w) X α v`（`getEnv_value`。**開始 world `w`** であって終了 world `w'` ではない）。`HftObCDX env := CDX env [] hftRootValue (MonoTy shHft) synth_hftPcieOutByte`、`circCVS_hft_of_obCDX`、`circCVS_hft_run`（`env := envAt cref w`）。`HftObCDX` は**型だけで未供給**（`hcd` の供給ではない）。
- **別 env の負対照**（kernel の定理）: `circCVX_mixed`: `EnvDefs env (Δn 5)`（`mini := pure 5`）、`env'` が `X := mini` を宣言していれば、`env'` が何であれ `CircCVX env env' X (pure 5)` が成り立つ。`circCVS_rejects_mixed`: `EnvDefs env' (Δn 6)`（`env'` の `mini := pure 6`）なら `¬ CircCVS env' X (pure 5)`（`cdx_eq` と `Signal.pure` の単射性）。`miniDen 6` で `CircCVS env' X (pure 6)` は導出できる（Check14 の `circCVS_pos`）。つまり S1m の carrier は混在対を通し、単一環境の carrier は通さない。

### 20.2 M2: 意味保存の経路（§17.8 に書いた）

§17 の「健全性（定義的等式）」「新規則は値を変えない」「導出が存在しない」を撤回し、§17.8 に (a) 型の正しい入力に対する縮約の意味保存、(b) 対象 root で元の Lean 項と展開後の項の等式証明をカーネルに渡す、の 2 経路を明記した。`cdx_fun` は新関係の一意性、21 件の比較は監査、`projCtor` は raw `Expr` 規則、`EnvDefs`/`EnvCtors` は追加の未供給内容。

### 20.3 再帰子の最初の小単位（`List.rec` だけ）

方針（reviewer）: 汎用 `recInfo` 解釈・universe の拡張はしない。`runCircuitH` の `List.rec` で major が静的に `nil`/`cons` に展開できる範囲だけ。有限の回路構築リストを展開する。実行時の無制限 `List` を回路にしない。新 TRUSTED なし。

- `recStep env e`: 頭が定数 `List.rec`、`env.find? List.rec = some (.recInfo _)`、引数が 5 個以上（`α motive nilc consc major extra…`）、`major` が `recMajorWh`（`whStep` を最大 256 回）で `List.nil _` / `List.cons _ h t` に至るとき: nil なら `betaApp nilc extra`、cons なら `betaApp consc ([h, t, List.rec.{ls} α motive nilc consc t] ++ extra)`。**宇宙の水準 `ls` は入力のまま**（拡張なし）。他の再帰子（`Nat.rec`）、`casesOn`、部分適用、変数の major（`bvar`）では `none`（Check14 RECSTEP の対照）。major が constructor まで出ない箇所は `none` で止まり、`MISSING` にその major の形が出る（`describeRecStuck`）。
- 規則: 新しい帰納族 `DY env`（`DX` の全規則 + `recIota`。`DX` は編集していない。`dx_to_dy : DX env ρ e r → DY env ρ e r`）。`recIota`: `appFn e = List.rec ls`、`env.find? List.rec = recInfo ri`、`recStep env e = some e'`、`CDY env ρ e' α v` → `CDY env ρ e α v`。**`beta` と `projStep` は `headRedexR`/`whStepR` 上に置いた**（`whStep` に「射影の引数が `List.rec` の redex のとき射影の内側で `recStep`」を足しただけ。`whStepR_of_whStep`・`headRedexR_of_headRedex` で `DX` の導出はそのまま入る）。`List.rec` が射影の引数にだけ現れる hftPcie の形（`brecOn` の `PProd#0`）に必要。
- 関数性: `dy_fun`、`cdy_fun`、`tdy_fun`、`cdy_eq`、`circCVY_functional`（導出に関する `induction`。衝突の反駁に `recStep_head`、`unfoldAt_rec`、`headRedexR_rec`、`whStepR_ctor`）。仮定なし。
- **元の項との証明（経路 (b)）**: 規則 `recIota` の値は展開後の式の値であり、元の項との一致は**最終の型付けで検査される**: `HftObCDX` の `v` は `synth_hftPcieOutByte`（元の Lean 定数）で、規則が組む値がこれとカーネルで定義的に等しい導出だけが型検査を通る。その際 `List.rec` の iota は Lean の等式として **すべての引数に対して `rfl`**: `listRec_nil_eq : List.rec n c [] = n`、`listRec_cons_eq : List.rec n c (a :: xs) = c a xs (List.rec n c xs)`（universe 多相のまま）。これらは**一般の意味保存定理ではない**（`Expr` の書き換えを意味に結ぶ定理は無い）。Check14 は走査が取った各ステップ（入力の `List.rec` spine、`recStep` の結果）を Lean の `isDefEq`（default 透過度）で照合する: **2 件（distinct）すべて定義的に等しい**（loose bvar は junk 型の fvar で閉じた。型付けの検査ではなく縮約の検査）。
- **フォールバック（`Circuit` の pure/bind/next の展開補題）**: iota が constructor に届かない部分項に備え、`Circuit.pure'`/`bind`/`next` の定義から `rfl` で証明した展開補題 `circuit_pure_eq`、`circuit_bind_eq`、`circuit_next_eq` を置いた。**今回のルートでは使っていない**（`List.rec` はすべて静的 major だった）。

### 20.4 hftRootValue の走査（Check14 SNAPSHOT14、1 環境の値）

`Check14` の recognizer は規則の関数（`unfoldAt`/`headRedexR`/`whStepR`/`recStep`/`instE`）そのままで root の値を走査する（証明ではなく走査）。

- **走査は 505 節点、`List.rec` の iota を 34 回（distinct 2: 17 箇所 × `cons`、`nil` の 2 段）取る**。S1m の stuck（`proj Prod#0 of proj Prod#0 (proj PProd#0 (List.rec …))` ×17）は消えた。走査の記録と `whStepR`/`headRedexR` の一致（不一致 0）。
- **新しい stuck（今回の走査はここで停止、導出は未供給）**: `Sparkle.Core.Signal.Signal.mk [constructor]` ×17。`mkRegList` の読み出し lens `Signal.map Prod.fst (readSig s)`（`Signal.map` を `unf` した `Signal.mk { val := fun t => … }` の構造体リテラル）。`CD` の primitive 14 頭に `Signal.map` も `Signal.mk` も無い。次の設計問題は「`Signal.map` を primitive とするか（`Prod.fst`/`Prod.snd` の関数値の `CD` が要る）、`Signal.mk` を `Signal` の値の規則にするか」で reviewer の判断を仰ぐ。`tdFail`: なし。
- したがって `HftObCDX`（`hcd`）は**今回も供給していない**。

### 20.5 Check14 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck14`、912 jobs、exit 0）

- `FGCIRCUIT14 SIGNATURES`: `CircCVS` の定義、`circCV_to_S`、`circCVS_at_of_getEnv`（`envAt cref w`）、`circCVX_iff_S`、`circCVS_functional`、`circCVX_mixed`/`circCVS_rejects_mixed`、`DY.recIota`、`DY.beta`/`DY.projStep`（`whStepR`/`headRedexR`）、`dx_to_dy`、`cdy_fun` を独立に書いた文面と `isDefEq`（default 透過度）で照合。**19 mutant 棄却**（carrier: 固定の環境、非空の valuation、宇宙パラメータ条件なし、`CDX` の環境の存在量化; 橋: 固定の環境; run: 終了 world `w'`; `iff_S`: 環境の一致なし; 関数性: `CircCV`; 混在対: 値の入替、`Δn` の入替; `recIota`: `Nat.rec`、recInfo なし、結論が `e'`、`unfoldAt`; `beta`/`projStep`: 旧 `headRedex`/`whStep`; 埋め込み: 逆向き; `cdy_fun`: 別 env、`HEq` なし）。
- `FGCIRCUIT14 OLD RULES`: `DX` の 26 コンストラクタ（`beta`・`projStep` 以外）が `DY` で同一。対照（`sigMux` を `sigPure` と見る）は棄却。
- `FGCIRCUIT14 NEGATIVE CONTROL (different env)`: 2 つの具体環境（`mini := pure 5` / `pure 6`、`X := mini`）を `addDecl` で作り、同じ引用が `unfoldAt` で別の値に展開されることと、`EnvDefs` の行の一致（meta 評価）を確認。
- `FGCIRCUIT14 RECSTEP`: nil/cons/ih/2 段/extra 引数/beta した major の各ケースが期待どおり。変数の major、`Nat.rec`、部分適用、`List.casesOn` は step しない。水準は保たれる。
- `FGCIRCUIT14 AXIOMS`: 29 名、標準 axiom のみ。
- `FGCIRCUIT14 SNAPSHOT14`/`MISSING`/`TRACE`: 20.4 のとおり。equation check（Lean `isDefEq`）: 2 件中 2 件、不一致 0、例外 0。

### 20.6 証明したもの / 名前付きの仮説・未供給 / 数え方

- **証明した**: `circCV_to_S`、`circCVS_to_X`、`circCVX_iff_S`、`circCVS_functional`、`sourceDenotes_to_S`、`declConnect_to_S`、`circCVS_at_of_getEnv`、`circCVS_hft_of_obCDX`、`circCVS_hft_run`、`circCVX_mixed`、`circCVS_rejects_mixed`、`dx_to_dy`、`dy_fun`/`cdy_fun`/`tdy_fun`/`cdy_eq`、`circCVS_to_Y`、`circCVY_functional`、`whStepR_of_whStep`、`headRedexR_of_headRedex`、`whStepR_ctor`、`listRec_nil_eq`、`listRec_cons_eq`、`circuit_pure_eq`/`circuit_bind_eq`/`circuit_next_eq`。
- **名前付き仮説／未供給（新規に増えたもの・変わらないもの）**: `HftObCDX`（型のみ、`hcd` 未供給）。`EnvDefs`/`EnvCtors`（実 run 環境について追加の未供給内容）。規則の意味保存（§17.8 の経路 (a)/(b)。(b) は受理される導出が未供給の間は未供給）。`recStep` と Lean の `List.rec` の対応は、Check14 の `isDefEq` による走査ステップの監査であって定理ではない。`Signal.mk`/`Signal.map` の規則（20.4）。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。条件付きは減算しない。

### 20.7 次

(1) `Signal.map`／`Signal.mk` の規則の設計（reviewer）。(2) その後 `hcd` の導出が `HftObCDX` に届くか走査し直す（各ステップの等式は経路 (b) でカーネルに渡す）。(3) `HftObSrc`/`HftObTopCore`/`HftObNoRaw` は別。

## 21. S1q（Issue `sparkle-fg-circuit-pilot` の次の束）: プロファイル無効の入口（`profile = false` を純粋に固定）— 設計と 4 leaf root の前提差分

土台 `e2301cd4`（par/fgc-s1）。Issue の状態は変えていない。S1p のファイル（`Tools/ShippingFGCircuitS1pCD.lean`、§17/§20、Check14）には触れない。reviewer 裁定（§19.2-2 の実装）: `GetEnvProfileAt` は名前付きの run 局所条件のまま（供給でも縮約でもない）。この束は compiler 変更で、**保証対象の入口**の `profile` を `false` に固定し、その `coreHead` に `IO.getEnv` もログ実行も無い形にする。成果は引き続き**条件付き**。台帳に数えない。

### 21.1 訂正（§19.2-2 / §19.4）

- §19.2-2: `Options` へ移すだけでは `profile = true` 枝のログは `coreHead` に残る（消えるのは `IO.getEnv` の 1 件だけ）。ログ枝が消えるのは `profile` が `false` に**固定**されたときだけ。§19.2 本文に訂正を入れた。
- §19.4: `LogBranchDraft` は記述専用。`stderrPreserves` は `∀ msg, EnvFrame (liftM (logStderrAct msg))` で、`EnvFrame` は ∀ world。特定 callback/world の条件を型に持たないので「callback ごとの条件」ではない。`fixedHandlePreserves` も同様に ∀ world。draft は採否の判断対象に上げず、無効経路を優先する。

### 21.2 compiler の設計（実装は §21.4 の後。`Sparkle/Compiler/Elab.lean` に小さく追加、既存の定義は 1 文字も変えない）

`Elab.lean` の既存定義（`synthesizeCombinationalCoreWith`/`…Core`/`synthesizeCombinationalWith`/`synthesizeCombinational`/`synthesizeChild`/`sparkleChildSynth` の `initialize`）は**そのまま**。約 30 本の既存 Tools 定理が `unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith` で展開するので、引数追加や wrapper 化は避ける（測定: 展開側 30 ファイル超）。追加するのは 3 定義（翻訳器の結び目の後でないと書けないので `Elab.lean` 内、`synthesizeChild` の直前）:

```lean
/-- the guaranteed entry: `synthesizeCombinationalCoreWith … declName [] false true` with `profile := false` FIXED (no IO.getEnv, no log) -/
def synthesizeCombinationalCoreOff (declName : Name) : MetaM (Module × Design)
/-- `synthesizeCombinationalWith` over it (same post-processing) -/
def synthesizeCombinationalOff (declName : Name) : MetaM (Module × Design)
/-- command level: the setting is read OUTSIDE the entry; the guarantee starts after it -/
def synthesizeEntry (declName : Name) : MetaM (Module × Design) := do
  if (← IO.getEnv "SPARKLE_PROFILE").isSome then synthesizeCombinational declName   -- diagnostic path: OUTSIDE the guarantee
  else synthesizeCombinationalOff declName                                         -- guaranteed path
```
- `#synthesize`/`#synthesizeVerilog`/`#showVerilog` は `synthesizeCombinational` の代わりに `synthesizeEntry` を呼ぶ（3 箇所）。`SPARKLE_PROFILE` 設定時は従来と**完全に同じ**経路（診断経路。保証の外と明記）。未設定時は `profile = false` の従来経路と同じ出力（§21.6 の比較で確認）。通常の IP の成功範囲は狭めない（ログ枝は未設定時に実行されないので、成功・出力は同じ）。
- `Off` の本体は `synthesizeCombinationalCoreWith` の `parameters := []`, `symbolicMode := false`, `certifiedFrontEnd := true`, `profile := false` の特殊化で、`logProf := fun _ => pure ()`。`IO.getEnv "SPARKLE_PROFILE"` も、`IO.eprintln`/`flushStderr`/`Handle.mk` も出てこない。`synthesizeFromConst` に渡す `logProf` は no-op。
- 範囲外（変更しない）: `synthesizeHierarchical`（`#synthesizeDesign` 等）、`synthesizeCombinationalWithParameters`、`synthesizeChild`/`sparkleChildSynth` の `initialize`。子の入口は引き続き診断入口（`profile` を読む）。これは `ShippingInitFrame`/`ShippingStartAtLoad` が `initialize … (some synthesizeChild)` を手で模型化しているため、`initialize` を変えると模型との対応が崩れるからで、**非 leaf root（`synth_hftPcieOutByte`）の子**はこの束の保証対象の外のまま（子の profile 読み取りは `HeadIO`/`GetEnvProfileAt` の問題としてそのまま残る）。4 leaf root は子を持たない。
- 副作用: `Elab.lean` が変わるので、依存する全モジュールが再ビルドされる。

### 21.3 Tools 側（新ファイルだけ。既存の定理・定義は変えない）

- `Tools/ShippingFGCircuitS1qLinked.lean`: `coreHeadOff`/`coreRestOff`（`coreHead`/`coreRest` から `IO.getEnv` と `logProf` を除いた鏡像。`CoreSaved.profile := false`）、`core_eqOff`/`core_splitOff`/`core_chainOff`、`MachineDefinesLinkedOff`（`profLogIO s.profile` の所を no-op に）、`synthesizeCombinationalCore_machine_soundCOff`、`machineRunJQC_of_closesCOff`（`coreHeadOff_jqcA` を含む）、`Linked2` の 5 本の写し、`postEntryOff`/`synthesizeCombinational_checkedOff`、`PostRunOff`、`leaf_*_of_runCOff`、`hTop_of_leaf4Off`、`X_artifact_atCOff`、`X_final4DOff`。写しは証明本体を変えず、`synthesizeCombinationalCore`→`…Off`、`coreHead`→`coreHeadOff`、`MachineDefinesLinked`→`…Off`、`PostRun`→`…Off` の置換のみ（機械的）。
- `Tools/ShippingFGCircuitS1qHead.lean`: `HeadAtOff`、`envFrame_coreHeadOff`（**`CellPrem` だけ**から。`HeadIO` も `GetEnvProfileAt` も使わない）、`headAtOff_of_cellPrem`、`X_final10Off`、`X_final12`（4 root）。
- `Tests/Gen5/FGCircuitPilotCheck15.lean`: 独立に書いた完全型の `isDefEq`、mutant、HYPS、NOTUSED、AXIOMS。`Tests/Gen5/FGCircuitPilotCompare15.lean`: 出力比較用（§21.6）。

### 21.4 新しい head に載せた 4 leaf root の最終定理の型と前提の差分

最終定理は `X_final12`（X = counterLoop / shift4Loop / counterEnableLoop / arbiterSignal）。`X_final11`（S1l/S1n）との差分（counterLoop の例。他 3 root も同じ形、arbiter は `hB0 hcont` が加わるのは `X_final10` と同じ）:

| | `X_final11` + `headAt_of_profileOff`（S1o の `final9P` 系） | `X_final12`（S1q） |
|---|---|---|
| 入口の run `hr` | `RunsTo (synthesizeCombinational ``X)` | `RunsTo (synthesizeCombinationalOff ``X)` |
| head の前提 | `hhead : HeadAt X w`。供給は `CellPrem` + `GetEnvProfileAt mctx mref cctx cref w`（`unset`: getEnv の結果が `none`、`env`: getEnv が env を保つ）、または `CellPrem` + `HeadIO`（S1i） | **無い**。`HeadAtOff` は `CellPrem` だけから証明する |
| cell の前提 | `hcell : ReadWorld cref`（`CellPrem` の 1 成分） | `hcell : CellPrem MkRefd mref cref`（C.EN-4 の既存の束。`ReadWorld cref` を含む） |
| 結論の post | `PostRun mctx mref cctx cref w ``X D' b raw`（`synthesizeCombinationalCore` の run を含む） | `PostRunOff …`（`synthesizeCombinationalCoreOff` の run を含む） |
| その他 | `L lvl env₀ hstart hlvl hx hf hlink`（arbiter は `hB0 hcont` も） | **同じ**（`L lvl env₀ hstart hlvl hx hf hlink`、arbiter は `hB0 hcont` も） |

消える前提: `GetEnvProfileAt`、`HeadIO`（getEnv の `EnvFrame` 1 件と、profile ログの `EnvFrame` ∀msg の 1 件）、`hhead`。**置き換わる前提**: なし（`CellPrem` は既に S1o の `final9P` にあった）。つまり前提の数は減るが、`GetEnvProfileAt` の `unset` は「消えた」のであって「供給された」のではない: 保証は `SPARKLE_PROFILE` 未設定のコマンド経路（`synthesizeEntry` の `else` 枝）についてだけで、設定時の経路（診断）は保証の外。この区別は `synthesizeEntry` の `if` が入口の**外**にあることで型に出る（`X_final12` は `synthesizeCombinationalOff` の run について語り、`synthesizeEntry` の run については語らない）。`synthesizeEntry` の `else` 枝が実際に実行されたことは、`IO.getEnv` の結果 `none` の観測でありこの束では供給しない（run 局所の観測。名前付きのまま）。

残る名前付き仮説（不変）: `RootExtern`/`RootEnvFacts`/`hlvl`/`ReadsAt`（`hlink`）、`Laws`/`Start`/`hr`、`CellPrem`、arbiter の `BoundaryRowsInEnv`/`ContainsAt`。非 leaf の `hcd`/`hsrc`/`htop`/`hnoraw` は未供給。`EnvDefs`/`EnvCtors` は実 run 環境については未供給（S1m の裁定どおり）。

### 21.5 実装と測定（compiler diff・既存 Tools への影響）

**compiler diff（`Sparkle/Compiler/Elab.lean` のみ、追加 106 行・変更 3 行）**: 追加は `synthesizeCombinationalCoreOff`（`synthesizeCombinationalCoreWith … [] false true` の `profile := false` 固定の特殊化。`IO.getEnv "SPARKLE_PROFILE"` も `IO.eprintln`/`flushStderr`/`Handle.mk` も無く、`logProf := fun _ => pure ()`）、`synthesizeCombinationalOff`（`synthesizeCombinationalWith` と同じ後処理）、`synthesizeEntry`（`SPARKLE_PROFILE` を入口の**外**で読み、設定時は従来の `synthesizeCombinational`＝診断経路、未設定時は `synthesizeCombinationalOff`）。変更は `#synthesize`/`#synthesizeVerilog`/`#showVerilog` の 3 箇所の呼び出し（`synthesizeCombinational declName` → `synthesizeEntry declName`）だけ。既存の定義・`initialize`・他のコマンドは 1 文字も変えていない。新ファイルにしなかった理由: `Off` は翻訳器の結び目（`translateExprToWire`/`synthesizeFromConst`）の後でないと書けず、`Elab` のコマンドが呼ぶので、`Elab` が import する側のファイルには置けない。

**Tools 側（新ファイルのみ）**: `Tools/ShippingFGCircuitS1qLinked.lean`（`coreHeadOff`/`coreRestOff`、`core_eqOff`: `synthesizeCombinationalCoreOff = coreHeadOff >>= coreRestOff` が `rfl` で閉じる、`core_chainOff`、`coreHeadOff_jqcA`、`MachineDefinesLinkedOff`、`machine_run_of_coreCOff`、`machineRunJQC_of_closesCOff`、`synthesizeCombinationalCore_machine_soundCOff`）、`Tools/ShippingFGCircuitS1qEndpoint.lean`（`Linked2`/`Final4`/`Roots4`/`S1iRoots` の写し: stream/loop/wired endpoint、`hTop_of_leaf4Off`、`X_artifact_atCOff`、`X_final4DOff`、`PostRunOff`、`postEntryOff`、`synthesizeCombinationalOff_checked`。証明本体は機械的な改名のみで編集していない）、`Tools/ShippingFGCircuitS1qHead.lean`（`envFrame_coreHeadOff`・`headAtOff_of_cellPrem`: **`CellPrem` だけ**から。`X_final10Off`、`X_final12`）。

- **`HeadAt` は `CellPrem` だけから証明できた**（新しい head には getEnv もログも無く、S1i の `ef_step` 分解がそのまま通る）。`HeadIO`/`GetEnvProfileAt`/`hhead` は不要。
- 4 root の最終定理 `X_final12`: 前提は `L lvl env₀ hstart hr hcell hlvl hx hf hlink`（arbiter は `hB0 hcont` も）、`hr` は `synthesizeCombinationalOff` の run、`hcell : CellPrem MkRefd mref cref`。差分は §21.4。
- 既存の定理への影響: **既存の定義・定理は変更なし**。`Elab.lean` が変わるので全依存モジュールが再ビルドされる。再ビルドした既存ターゲット（`kjob lake build`、Elab 変更後）: `Tests.Gen5.FGCircuitPilotCheck13`（913 jobs）、`Check12`（913）、`Check11`（911）、`Check10`（911）、`Check9`（916）、`Check8`（909）、`ClosingRunCheck`（756）、`RunReadsCheck`（748）、`Flow1ReadsCheck`（843）、`DCEntryCheck`（746）、`Tools.ShippingEntrySoundness`（248）、`Tools.ShippingMachineOutcomeA3`（349）、`Tools.ShippingChildPinC`（339）、`Tools.ShippingLeafKeepCache`（599）、`Tools.ShippingMemoLawsWith`（318）— すべて exit 0。保存ログの Check 行は変更前と同じ（Check10 AXIOMS 13、Check11 16、Check12 24、Check13 2）。**失敗が 1 件**: `Tools.ShippingGen4ParamEntry` が `core_symbolic_reads`（216 行）で `(deterministic) timeout at whnf, maximum number of heartbeats (1600000)`。**土台 `e2301cd4` の単独ビルドでも同じ行で同じ失敗**なので、この束の変更による退行ではなく既存の問題（未対処。S1q では触れない）。`synthesizeCombinationalCore`/`…Core`/`coreHead` を `unfold` する約 30 の Tools ファイルは、それらの定義が不変なので影響を受けない（これが「既存の head を残す」案を採った理由）。
- `Off` と従来経路の同一性: Lean の定理としては `core_eqOff`（`Off` の構造）と、§21.6 の出力比較（5 root の IR/SV が完全一致）で確認する。従来の `coreHead` で `getEnv` の結果が `none` のときと `Off` が同じ run になる、という形の定理は置かない（`IO.getEnv` の結果が `none` である run の存在を使うことになり、`GetEnvProfileAt` を別の名前で戻すことになるため）。

### 21.6 出力比較（4 root + hftPcie、IR と SV のテキスト）

`Tests.Gen5.FGCircuitPilotCompare15`（5 つの root: counterLoop、shift4Loop、counterEnableLoop、arbiterSignal、hftPcieLoop.outByte に `#synthesize`＝IR と `#synthesizeVerilog`＝SV）のビルドログから、`scripts/gen5/fgc_s1q/extract.sh` でこのモジュールの出力だけを取り出して比べた。変更前（土台 `e2301cd4`）と変更後（`SPARKLE_PROFILE` 未設定の pod）で **1312 行が完全に一致**（`diff` 空）。hftPcie は非 leaf で、子の入口は従来の診断入口のまま（上位だけ `Off`）で、出力は同じ。

### 21.7 結果・S0 baseline で比べるもの

**Check15**（`kjob lake build Tests.Gen5.FGCircuitPilotCheck15`、918 jobs、exit 0）:
- `FGCIRCUIT15 SIGNATURES`: `core_eqOff`、`envFrame_coreHeadOff`、`headAtOff_of_cellPrem`、`counterLoop_final12`、`shift4Loop_final12`、`counterEnableLoop_final12`、`arbiterSignal_final12` の完全型を独立に書いて `isDefEq`（default 透過度）で照合し、binder の種類も一致。**45 mutant 棄却**（診断入口 `synthesizeCombinational` の run、旧 `PostRun`、`CellPrem` の代わりに `ReadWorld` だけ、cell 前提の欠落、取り除いた `GetEnvProfileAt`/`HeadIO` を戻したもの、旧 `coreHead`、end world の link/結論/frame、別 root の post、lvl/extern/facts/boundary 前提の欠落）。mutant は正規化後の式が構文的に異なり、かつ reducible 透過度で defeq でないことで棄却している（default 透過度の探索は両入口の定義を深く展開して終わらないので行わない。`same` 側は default）。
- `FGCIRCUIT15 HYPS`: 4 本の `X_final12` = `L lvl env₀ hstart hr hcell hlvl hx hf hlink`（arbiter は `hB0 hcont` も）、`headAtOff_of_cellPrem`/`envFrame_coreHeadOff` = `X hcell`。`hhead`/`hg`/`hio`/`HeadIO`/`GetEnvProfileAt` は前提に無い。
- `FGCIRCUIT15 NOGETENV`: `coreHeadOff` が `Sparkle.*`/`Tools.*` で到達する 26 個の定数に `IO.getEnv`・`IO.eprintln`・`IO.FS.Handle.mk`・`flushStderr`・`profLogIO`・文字列 `"SPARKLE_PROFILE"`・`"/tmp/sparkle-profile.log"` が無い。`synthesizeCombinationalCoreOff` と `coreRestOff` の値にも無い。対照: 旧 `coreHead` はこれらに到達し、`synthesizeCombinationalCoreWith` は文字列を持ち、`synthesizeEntry` は `SPARKLE_PROFILE` を入口の外で読んで 2 つの入口を振り分ける。
- `FGCIRCUIT15 NOTUSED`: 4 本の最終定理 + `headAtOff_of_cellPrem` + `envFrame_coreHeadOff` の値が `Tools.ShippingFGCircuit*` で到達する 293 個の定数のどれも `coreHead`/`HeadIO`/`GetEnvProfileAt`/`headAt_of_profileOff`/`envFrame_coreHead`/`headAt_of_cellPrem` に触れない。うち S1q の 51 個は旧入口・診断入口（`synthesizeCombinationalCore`/`…With`/`synthesizeCombinational`/`synthesizeCombinationalWith`/`synthesizeEntry`）に触れない。（`Tools.*` 全体への走査（4793 個）でも同じ結果を得たが、ビルドに 10 分かかるので範囲を狭めた。）
- `FGCIRCUIT15 AXIOMS`: 6 名、標準 axiom のみ。

**出力比較**: §21.6。**証明できたもの**: `HeadAt` の新しい head 版 `headAtOff_of_cellPrem`（`CellPrem` だけ）、4 root の最終定理 `X_final12`。**名前付き仮説のまま**: §21.4 末尾。**追加で名前付きにしたもの**: なし（`GetEnvProfileAt`/`HeadIO` は消えた。実環境で `else` 枝が選ばれたこと（`SPARKLE_PROFILE` 未設定）は保証の仮説ではなく、保証は `synthesizeCombinationalOff` について）。

**S0 の必要 IP baseline（`scripts/gen5/fgc_baseline/capture.sh`、327 コマンド）で比べるもの**（coder が別に実行）:
1. `SPARKLE_PROFILE` 未設定で、各コマンドの終了コード・stdout の IR/SV テキスト・stderr の警告（DRC など）を、土台 `e2301cd4` の capture と**バイト単位で比べる**。違いが出るはずがないもの: `#synthesize`/`#synthesizeVerilog`/`#showVerilog` は `Off` を通るが、本体は `profile = false` の従来経路と同じ。
2. `#synthesizeDesign`/`#writeVerilogDesign`/パラメータ付きコマンド等（`synthesizeHierarchical`/`synthesizeCombinationalWithParameters` を通るもの）は診断入口のまま（コードは不変）。これらも同じ出力のはず。
3. `SPARKLE_PROFILE=1` を付けた数本（`counterLoop`、hftPcie）で、stderr と `/tmp/sparkle-profile.log` の `[profile] …` 行の列が土台と同じ（診断経路が不変であること）。`#synthesizeVerilog` 自身が最初に出す `[profile] #synthesizeVerilog entry …` の行は従来どおり、`[profile] synthesizeCombinational … entering` 以降は診断入口が出す。
4. 実行時間: `Off` は `getEnv` 1 回とログ no-op クロージャの呼び出しを減らすだけで、差はノイズの範囲のはず（遅くなっていないこと）。
5. 失敗するコマンド（意図したエラー）も、メッセージが同じこと。`Off` の `throwError` は従来と同じ文言（`hardware modules nested deeper …`、`entryInlinerError?`）。
6. 非 leaf（子を持つ）root: 上位は `Off`、子は `sparkleChildSynth`＝`synthesizeChild`＝診断入口のまま。子の `profile` 読み取りは残る（§21.2）。出力は同じはず。

**次**: (1) `X_final12` の非 leaf root への持ち上げと、子の入口（`synthesizeChild`）の profile 固定（`initialize` の模型 `ShippingInitFrame`/`ShippingStartAtLoad` との対応を保つ形で）、(2) `synthesizeEntry` の `if` が `else` に落ちること（`SPARKLE_PROFILE` 未設定）を、保証の外の run 観測として明記し続けること、(3) 既存 Tools の `coreHead` 系定理を `Off` 版へ一般化する案（head を引数にした一般化）は、Check の固定した型を変えるので採らなかった。

## 22. S1r（Issue `sparkle-fg-circuit-pilot` の次の束）: `Signal.map Prod.fst/snd` の狭い配線規則、CDY/CDZ の単一 env 接続、Check の fail-closed 化

土台 `9a2ef5cd`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は各 1 回）: `Tools/ShippingFGCircuitS1rCD.lean`、`Tests/Gen5/FGCircuitPilotCheck16.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない（`FGCIRCUIT16 AXIOMS`: 37 名、標準 axiom のみ）。Issue の状態は変えていない。S1q の領域（Compiler profile、S1qHead、Check15、§21）には触れていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は**条件付き**。

### 22.1 設計（reviewer 裁定に従う）

`Signal.mk` 一般則・`Signal.map` 本体の解釈・汎用高階関数・universe 拡張は**入れていない**。新しい帰納族 `DZ env`（`DY` + 下記）。`dy_to_dz`（したがって `DX`/`CD`）で埋め込む。`DY`/`DX` は編集していない。

- 値の規則: `mapFst`（`Signal.map.{0} D (A×B) A (Prod.fst.{0,0} a b) s`、値は Lean の `Signal.map Prod.fst sv`）、`mapSnd`、`prodMk`、`unitVal`。型の規則: `prodTy`、`punitTy`。
- `unf`/`beta`/`projStep`/`projCtor`/`recIota` を**結果 `r : Res`（型または値）について一般化**（`HList αs` のような型を同じ delta/beta/射影/`List.rec` で展開するため）。`unf` の停止条件は `stopR r e`（値: 従来の `headStop`、型: 核の型頭 `Nat/Bool/DomainConfig/BitVec/Signal/Prod/PUnit` は展開しない）。`letE` に前提 `coreHead A = true` を追加（以前は型判定から出た。`zeta` との排他のため明示）。
- `projRec`: 構造体引数が `List.rec` の redex である射影を、その場で `recStep`（`whStepR` は別の射影/適用の下でしか進めないため。型位置の `PProd#0 (List.rec …)` で必要になった）。
- **排他性**: `mapFst`/`mapSnd` は前提 `MapStuck env e`（`e` の `unfoldAt` が `Signal.mk` 頭の項になり、`Signal.mk` が `env` の `ctorInfo`）を持つ。`unf` が同じ式に適用されても `Signal.mk` 頭の項に導出が無いこと（`dz_signalMk_false`、`mapStuck_unf_false`）で衝突しない。`prodMk`/`unitVal` は `ctorInfo` を前提にして `unf` と衝突しない。
- **Lean の等式（全信号・全時刻、`rfl`）**: `signal_map_fst_at`/`signal_map_snd_at`（`(Signal.map Prod.fst sv).val t = (sv.val t).1` 等）、`signal_map_eq`、`signal_mk_fst_eq`/`snd_eq`（展開後の `Signal.mk` 本体が規則の値）、`signal_map_pair_at`、`signal_ext'`。値は元のソースの `Signal.map` から作り、生成 IR から定義していない。
- **関数性**: `dz_fun`/`cdz_fun`/`tdz_fun`/`cdz_eq`（導出に関する `induction`、仮定なし。`whStepR_listRec` ほか新しい衝突補題）。`circCVZ_functional`。

### 22.2 CDY/CDZ の単一 env 接続（CDX は埋めない）

`HftObCDX`（S1p §20.7）は `CDX` であり、`recIota` を持つ導出では埋まらない。DX→DY→DZ の橋だけがあり、**CDY→CDX は仮定しない・証明もしない**（`HftObCDX` と `HftObCDY` が定義的に別であることを Check16 が検査）。

`CircCVY`（S1p）、`CircCVZ`、`HftObCDY env`、`HftObCDZ env`、`circCVY_to_Z`、`circCVS_to_Z`、`SourceDenotesY/Z`、`sourceDenotesS_to_Y`/`Y_to_Z`、`declConnect_of_cv`、`declConnect_S_to_Y`/`Y_to_Z`、`circCVY_hft_of_obCDY`/`circCVZ_hft_of_obCDZ`、run 側 `circCVY_at_of_getEnv`/`circCVZ_at_of_getEnv`（**開始 world `envAt cref w`**）、`circCVY_hft_run`/`circCVZ_hft_run`。消費側の完全型: `HftFinalStmtWith Ob`（S1k の `HftFinalStmt` の写しで `hcd : Ob (envAt cref w)`）、`HftFinalStmtY`/`HftFinalStmtZ`、`hftFinalStmtWith_const`（`Ob := fun _ => HftObCD` で `HftFinalStmt` に一致 = 写しの忠実性、`rfl`）。いずれも**型のみで未供給**（`hcd` の供給ではない）。

### 22.3 Check16 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck16`、exit 0）

- `SIGNATURES`: 新規則・変更した規則・`dy_to_dz`・`cdz_fun`・`CircCVZ`・`HftObCDY/Z`・`circCVZ_at_of_getEnv`・`signal_map_*_at` を独立に書いた文面と `isDefEq`（default）で照合。**31 mutant 棄却**（関数の入替、型引数の取り違え、`MapStuck` 欠落、結論の取り違え、ctor 条件欠落、stop 条件の入替、`coreHead` の欠落/反転、`recInfo` 欠落、別 env、`HEq` 欠落、DX/DY の取り違え、終了 world、時刻のずれ ほか）。`OLD RULES`: 23 コンストラクタが DY と DZ で同一。
- `PATTERN`: 実際の Lean の elaborator が `Signal.map Prod.fst s`/`Prod.snd s` に作る Expr が規則の型と一致（レベル・引数順）。展開が `Signal.mk` 頭になり `MapStuck` が成立。入替は棄却。
- `AUDIT CONTROLS`: 判定関数 `Audit.verdict` が、不一致ペア（map fst と map snd、正しいペア混在でも）、空の対象集合、traceMismatch、例外、ok≠total、Nat と Bool を**棄却**し、正しい一歩と全 ok を受理。
- **fail-closed**: 実走査の等式監査は `bad = err = traceMismatch = 0` かつ対象ペア非空でなければ `throwError`（build が落ちる）。結果: **9 ペア（`List.rec` 8 distinct + `Signal.map` 1 distinct）、ok 9、bad 0、err 0、traceMismatch 0**。Check14 の logInfo 止まりを置換。**これは監査**: 閉じていない束縛変数を型 `Nat` の junk fvar で閉じた `isDefEq` であり、型付きの導出ではない。§17.8(b) を使っても、元の root 値への型付きの導出/等式がカーネルで完成するまで**意味保存済みとは呼ばない**。
- `AXIOMS`: 37 名、標準のみ。

### 22.4 SNAPSHOT16（hftRootValue、1 環境の値。走査であり証明ではない）

2388 節点。`List.rec` の iota 272 回（distinct 8、うち `projRec` 102 回）、`mapFst` 17 箇所（distinct 1）、`mapSnd` 0、`MapStuck` 不成立 0、`prodTy` 51、型レベルの展開 510（`HList`、`List.brecOn`、`List.casesOn`、`HList.match_1` ほか）。S1p の stuck（`Signal.mk` ×17、型位置の `PProd#0 (List.rec …)`）のうち、`Signal.map Prod.fst` 由来の `Signal.mk` と `HList` の型展開は進んだ。

**次の stuck（今回の走査はここで停止、導出は未供給）**:
1. `Signal.mk [constructor]` ×17: `(fun x1 x2 => (x1, x2)) <$> Signal.register … <*> …`（`packRegister` の `bundle2`＝`Signal.seq`/`Signal.ap` の展開）。2 引数関数の `Signal.map`/`ap` で、Prod.fst/snd の狭い規則の外。reviewer の「汎用高階関数にしない」に照らし、`bundle2`（2 つの `Signal` から `Signal (A×B)` を作る配線）を同じ狭さの規則にするか、reviewer 判断。
2. `Inhabited.mk [constructor]` ×17: `instInhabitedProd` ＝ `⟨(default, default)⟩`（`Signal.loop` の `inst` 引数）。`Inhabited` 構造体値の規則（と `default` の射影）が要る。

したがって `HftObCDZ`（`hcd`）は**今回も供給していない**。

### 22.5 証明したもの / 名前付き仮説・未供給

- **証明した**: 22.1/22.2 の定理（`dy_to_dz`、`dx_to_dz`、`dz_fun` ほか、`signal_map_*`、`circCVZ_functional`、`declConnect_*`、`hftFinalStmtWith_const` など）。
- **名前付き仮説/未供給**: `HftObCDX`/`HftObCDY`/`HftObCDZ`（型のみ）、`EnvDefs`/`EnvCtors`、規則と元ソースの意味の接続（`recStep`/`MapStuck` 等の Expr 書き換えの意味保存は定理ではなく監査）、非 leaf の `hsrc`/`htop`/`hnoraw`。上記 2 つの stuck。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。条件付きは減算しない。

### 22.6 次

(1) `bundle2`/`Signal.ap` の狭い規則と `Inhabited` 構造体値の規則の設計（reviewer）。(2) その後 `HftObCDZ` に届くか走査し直す。

## 23. S1s（Issue `sparkle-fg-circuit-pilot` の次の束）: `bundle2` と `Inhabited.mk`/`default` の狭い規則（族 `DW`）

土台 `ba83ec10`（par/fgc-s1pqr）。追加ファイル（既存は書き換えていない）: `Tools/ShippingFGCircuitS1sCD.lean`、`Tests/Gen5/FGCircuitPilotCheck17.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない。Issue の状態は変えていない。成果は**条件付き**。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

### 23.1 新しい族 `DW`（reviewer 裁定 S1r §22.6 に従う）

`DW` = `DZ` の全コンストラクタ（`unf` の停止条件のみ変更）+ 3 規則。汎用 `ap` 規則・`Signal.mk` 一般則・型クラス探索・universe 拡張・新 TRUSTED は入れていない。

- `bundle2`: `Sparkle.Core.Signal.bundle2.{0} d A B a b`（引数順・レベル・同一 `d` を `he` で固定）。`d : DomainConfig`、`A B` の型、`a : Signal D A`、`b : Signal D B` の導出から、値は Lean の `bundle2 av bv`。Lean の等式（全信号・全時刻、`rfl`）: `bundle2_val_at`（`(bundle2 a b).val t = (a.val t, b.val t)`）、`bundle2_eq_mk`、**`bundle2_eq_seq`（`Signal.seq (Signal.map (fun x y => (x,y)) a) (fun _ => b)`：`seq` の `Unit` thunk は具体形のまま）**、`bundle2_eq_ap`、`seq_val_at`/`ap_val_at`、`bundle2_fst_at`/`snd_at`。**`bundle2` は `@[implemented_by bundle2Impl]` を持つ。証明したのは論理定義 `(·,·) <$> a <*> b` との一致であり、unsafe 実装との一致は証明していない。**
- `inhMk`: `Inhabited.mk.{1} T x`（`env` の `ctorInfo`）。`x ↦ v` の導出から instance 値 `⟨v⟩ : Inhabited T`。
- `inhDefault`: `Inhabited.default.{1} T inst`。`inst ↦ iv` から `iv.default`（**同じ instance**。instance 引数は消さない・canonical default に置換しない）。導出補題: `dw_default_of_mk`（`x ↦ v` ⇒ `default (Inhabited.mk x) ↦ v`）、`dw_prod_inhabited`（`Prod` instance は両成分の実際の導出から `⟨(xv, yv)⟩`）。Lean の等式: `inhabited_default_mk`、`inhabited_prod_mk`、`inhabited_inst_prod`、`inhabited_instances_differ`（同型で default の異なる 2 instance）、`loop_val_eq`（`Signal.loop` の意味が**その instance の** `default` を読む）。
- **排他性**: `bundle2` と `Inhabited.default` は `unf` の停止頭（`newStop`、`stopW r e = stopR r e || newStop e`）。`Inhabited.mk` は `ctorInfo` で `unf` と衝突しない。他の規則とは頭定数が異なる。**関数性**: `dw_fun`/`cdw_fun`/`tdw_fun`/`cdw_eq`（導出に関する `induction`、仮定なし、axiom は propext/Classical.choice/Quot.sound のみ）。
- **埋め込みの限界（正直な記録）**: 全称の `DZ → DW` は**証明していない**（できない）。`DZ` の導出で `bundle2`/`Inhabited.default` の適用を `unf` で展開するものは `DW` に写らない（任意の `env` ではその展開が停止しない保証がない）。それ以外の 35 コンストラクタは `DZ` と同一（Check17 OLD RULES が 1 つずつ照合）。したがって `HftObCDW` は `HftObCDZ` から出ない（別の義務）。

### 23.2 単一 env・consumer への接続

`CircCVW`（`CDW env [] d.value`）、`circCVW_functional`、`HftObCDW env`、`circCVW_hft_of_obCDW`、`circCVW_at_of_getEnv`/`circCVW_hft_run`（開始 world `envAt cref w`）、`HftFinalStmtW := HftFinalStmtWith HftObCDW`（S1r の `hcd : Ob (envAt cref w)`。Check17 が `HftFinalStmtWith HftObCDW` との一致を検査）。いずれも型のみで **`hcd` は未供給**。

### 23.3 走査（SNAPSHOT17）と `hcd` の状況

S1r の走査で止まっていた 2 種（`Signal.mk` ×17 = `bundle2`→`Seq.seq`→`Signal.seq`→`Signal.ap` の展開、`Inhabited.mk` ×17 = `instInhabitedProd`）は、それぞれ `bundle2` 規則・`inhMk`/`inhDefault` 規則の対象になる（Check17 SNAPSHOT17 の件数を参照）。**`hftRootValue` に対する `HftObCDW` の型付き導出（カーネル検査済み項）は今回作っていない**: 2h の pod 制限内で冷間 build（913 モジュール、約 70 分）が支配的で、導出生成器（メタプログラムで `DW` の項を組み、`EnvDefs`/`EnvCtors` 表 [展開した定義 40 件] と `List.rec` の `recInfo` 事実を仮定に取る）に着手できなかった。前提追加・保証範囲の変更・汎用化が必要で止まったのではない。次の束はこの生成器。

### 23.4 名前付き仮説・未供給

`HftObCDW`（型のみ）、`EnvDefs`/`EnvCtors`（導出時の表）、Expr 書き換えの意味保存は定理ではなく監査、`bundle2` の unsafe 実装、非 leaf の `hsrc`/`htop`/`hnoraw`。

### 23.5 検証の状況（正直な記録）

- `Tools/ShippingFGCircuitS1sCD.lean`: `lean` 直接実行（S1r までの olean に対して）で **エラー 0、sorry 0**、`dw_fun` の axiom は propext/Classical.choice/Quot.sound のみ（約 5 分）。lakefile 登録後の `kjob lake build Tools.ShippingFGCircuitS1sCD` は未実行（lakefile 変更はキャッシュ鍵を変え、冷間 build が約 70 分かかるため）。
- `Tests/Gen5/FGCircuitPilotCheck17.lean`: 草稿をコミットしたが、**未検証**。同じ olean に対する単独実行は 880 秒の timeout で出力なしに終了した（最初の SIGNATURES ブロックが重い。Check16 の同種ブロックも全体で約 10 分）。したがって Check17 の「棄却した mutant 数」「SNAPSHOT17 の件数」「#print axioms」は今回報告できない。次の束: SIGNATURES を分割（`ExpUnfW`/`ExpCircCVW` の mutant を別 run_cmd にする）して再実行。
- `hcd`（`HftObCDW` の型付き導出）は**未導出**（§23.3）。

### 23.6 S1w2: 型付き導出 `hftObCDW_of_tables` を試みた結果（**未導出**、2 つの止まりを特定）

追加: `Tools/ShippingFGCircuitS1wRun.lean`（生成器を `hftRootValue` に走らせ、表 `Δ`/`Γ` をリテラルの `Name → Option DefRow/CtorRow` として引用し、`theorem hftObCDW_of_tables (env) (hΔ : EnvDefs env Δ) (hΓ : EnvCtors env Γ) (hrec : RecFact env) : HftObCDW env` を `addDecl` で出す elab。`probe_hft_ob` は止まりを数えるだけ）、`Tools/ShippingFGCircuitS1wDerive.lean`（手動実行用。lakefile には入れていない）、`Tests/Gen5/FGCircuitPilotCheck22.lean`。生成器の修正: 評価器が問い合わせた名前の記録が `unsafeBaseIO` の順序で落ちていた（`IO.lazyPure` で修正）。TRUSTED・axiom・sorry・native_decide・新しい law はない。成果は条件付き（`hcd` は**未導出**）。

- **止まり 1（規則の水準の一般化が要る）**: `instInhabitedProd` を `unf` で展開すると `Inhabited.mk.{max 1 1}`（`instLE` は水準を正規化しない）が出る。`DW.inhMk` の頭は `[.succ .zero]` 固定なので型付けできない（生成器: `Inhabited.mk: stuck (value)`、Check22 STOP-1 が `[[max 1 1]]` を確認）。直すには `DW` に水準の同値（正規化）を許す規則を足す＝既存の族への一般化。今回は足していない。
- **止まり 2（評価の規模。有限な配線では済まない）**: 止まり 1 を probe で飛ばして進めると、`hftPcieLoop` の弱頭正規化は `whStepR` を 1 歩ずつ `DW.projStep` の導出節点にするため、約 29 000 節点（導出の深さ 49、`instE` が共有を壊すため式の木のサイズは 10⁵〜1.5×10⁶）で次の 1 歩の評価（`instE` の複製）が 28 GB を使い切って bad_alloc（`ulimit -v 28000000`）。各節点は途中の式全体を `Expr` リテラルとして項に埋め込む設計なので、導出項のサイズも同じ規模になる。部分項ごとの補題（子ごと・let ごと）に分けても、1 歩の評価が木の複製である点は変わらない。直すには共有を保つ評価規則（`let` を値として残す／環境つきの評価＝call-by-need）か、より大きい step を持つ規則が要り、規則の追加（汎用化）になる。
- 確認: Check22 の AXIOMS-A/B（評価器の健全性と表版規則は標準 axiom のみ）、FAIL-CLOSED（`hftObCDW_of_tables` は定数として存在しない）、STOP-1。Check 行数: info 4 行（AXIOMS-A, AXIOMS-B, FAIL-CLOSED, STOP-1）。
- 最終定理への接続: `HftObCDW` と `HftFinalStmtW`（§23.2）は型のみで、`hcd` は引き続き仮説。表の仮説（`EnvDefs`/`EnvCtors`/`RecFact`）への置換は導出が無いので行えない。

### 23.7 Check17 repaired (S2f)

- Line 203 failure: the **Check** was wrong, not `dw_default_of_mk`. `ExpDefaultOfMk` had an extra unused binder `{v v' : T}` (for a mutant), so even mutant 0 could not equal the theorem. The theorem states exactly the §23.1 rule (`x ↦ v`, `default (Inhabited.mk x) ↦ v`, with the `Inhabited.mk` constructor condition and `TDW t`); the expected text is unchanged in meaning, the mutants are now same-binder variants plus a `Canon` mutant.
- Other repairs: `Inhabited Environment` instance declared before use, `.{1}` escaped in `m!`, `mkAppOptM` for `Inhabited.default`, `ExpBundle2Swap` typed at one type (with a control), doc-comment before `run_cmd` removed, expected sides normalised (Exp definitions unfolded, `if mu == k` decided) before `isDefEq`.
- The snapshot traversal was exponential (a tree walk of a DAG); each (kind, expr) is now judged once, so site counts are per distinct pair. Check17's own build: 214 s. Result: 1892 nodes, audit 386/386, 0 trace mismatches, stuck: `<fuel>` 12, `Signal.mk` 10, `Inhabited.mk` 3, `Bool.false` 1 (the `<fuel>` entries are open and not explained here).

## 24. S1t（Issue `sparkle-fg-circuit-pilot` の次の束）: 非 leaf root `synth_hftPcieOutByte` の `Off` 入口上の最終文、新 carrier の結論、組み立ての証明

土台 `ba83ec10`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は各 1 回）: `Tools/ShippingFGCircuitS1tFinal.lean`、`Tests/Gen5/FGCircuitPilotCheck18.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない。S1s の領域（`Tools/ShippingFGCircuitS1sCD.lean`、Check17、§23）には触れていない。Issue の状態は変えていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**（名前付き仮説を残す）で、台帳に数えない。

### 24.1 reviewer 裁定への答え

裁定: `HftFinalStmtY/Z`（S1r §22.2）は型定義だけで、結論は旧 `RootArtifactMono`（`CD [] d.value`、環境なし）、run は旧 `synthesizeCombinational`。型を定義しても `CDZ → 旧 CD` も非 leaf の `Off` 接続も得られない。

この束でしたこと:
1. **結論側を明示的に更新した**。`SourceDenotesMonoV CV`/`RootArtifactMonoV CV`/`DeclConnectMonoV CV`/`FGCircuitConclusionMonoV CV`（`CV : CDRel := Environment → Expr → (α : Type) → α → Prop`、**環境を読む**単一 env の導出関係）。`CV := cdvOld`（`fun _ e α v => CD [] e α v`）のときは**旧定義と定義的に等しい**（`sourceDenotesMonoV_old`/`rootArtifactMonoV_old` は `Iff.rfl`）。`cdvX`/`cdvY`/`cdvZ` は `CDX/CDY/CDZ env []`。S1s の将来の family は `CDRel` を 1 つ足すだけで差し込める。
2. **run 側を `Off` に更新した**（上位 run = `synthesizeCombinationalOff`、コア義務は `synthesizeCombinationalCoreOff` と `MachineDefinesLinkedOff`、post は `PostRunOff`）。
3. **接続を証明した**（§24.3）: 名前付き義務から結論までの組み立て `synth_hftPcieOutByte_finalOff`。S1k の `synth_hftPcieOutByte_final` の `Off` + 新 carrier 版。
4. **`CDZ → 旧 CD` は提供せず、使わない**（`DZ` の規則（`recIota`・`mapFst` ほか）は `CD` に無いが、それは非導出性の証明ではない）。方向は `cdvOld → cdvX → cdvY → cdvZ` だけ（`cdvOld_to_X/X_to_Y/Y_to_Z/Old_to_Z`）。旧 carrier の結論は新 carrier の結論を含意する（`rootArtifactMono_to_Z`: old ⇒ new。4 leaf root の `X_final12` の結論をそのまま `DZ` 版に移せる）。new ⇒ old は今回は構成していない（逆向きは提供せず、使っていない。新しい規則があることは非導出性の証明ではなく、非導出性の定理は無い）。

### 24.2 最終文の完全な型（`HftFinalStmtOff Ob CV`）と、保証する範囲

```
HftFinalStmtOff (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {ι} {mref} {cref} (L : Laws mref cref) (lvl) (env₀) {mctx cctx w w' b D'}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hcd : Ob (envAt cref w))
    (hsrc : HftObSrc lvl (envAt cref w))
    (htop : ∀ p, GPt lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hnoraw : HftObNoRawOff mctx mref cctx cref w b D'),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) p, RootArtifactMonoV CV (envAt cref w) (GPt lvl (envAt cref w)) (PostRunOff … hftRoot D') hftRoot shHft mm b D' p
```
- `Ob` は carrier 義務（`HftObCDX/Y/Z` または S1s の family。型は `Environment → Prop`）、`CV` は結論の導出関係。両者の対応は文ではなく**定理の前提** `hOb : ∀ env, Ob env → HftObOf CV env`（`HftObOf CV env := CV env hftRootValue (MonoTy shHft) synth_hftPcieOutByte`）。`hftObOf_Y/Z`（`rfl`）で `HftObOf cdvY = HftObCDY`、`HftObOf cdvZ = HftObCDZ`。
- 上位 run は `Off`（保証対象の入口）。`hhead` は無い: `hcell : CellPrem` から `HeadAtOff`（S1q の `headAtOff_of_cellPrem`）と `ReadWorld` を出す。
- `HftObTopCoreOff`/`HftObNoRawOff` は S1k の `HftObTopCore`/`HftObNoRaw` の `Off` 版（`synthesizeCombinationalCore … [] false` → `synthesizeCombinationalCoreOff`、`MachineDefinesLinked` → `MachineDefinesLinkedOff`）。`hdRun` は `hchk`/`hcell` から導いて `htop` に渡す（前提ではない）。

**この文が保証すること**（4 義務と子の reader が与えられたとき）: `synthesizeCombinationalOff hftRoot` の run `(b, D')` について、(i) post を満たす `raw` が存在する、(ii) 開始 world の環境 `envAt cref w` の表から取れる package `p` があり、`p` は root の `machineData`（kD = 5）を持ち、(iii) root 宣言の値が**新 carrier の導出** `CV (envAt cref w) d.value (MonoTy shHft) mm` を持ち（`mm = synth_hftPcieOutByte`）、(iv) `p.src` の観測が `monoObs shHft mm` に等しく、(v) post を満たす任意の `raw` について `D'`（後処理済みの IR design。印刷後の design ではない。printer / SV 全体の保証とは別）上で `TopShips p n` が成り立つ。

**保証しないこと**:
1. **子の入口**。`synthesizeChild`（`sparkleChildSynth` が指す診断入口）は変えていない。子は `profile` を読み、ログを出し得る。文は子の入口を型に出さない（`hr` は上位 `Off` の run だけ）。子の合成中の IO（`IO.getEnv`・ログ・環境の変化）は `htop`/`hnoraw` の中の仮説であり、証明していない。Check18 `SCOPE` は、S1t/S1q/S1kStmt の接頭辞を持つ定数の値だけを辿る走査（コンパイラ本体も完全な依存閉包も辿らない）の範囲で、**文**（`HftFinalStmtOff`/`HftObTopCoreOff`/`HftObNoRawOff` の定義）が `synthesizeChild`/`sparkleChildSynth`/`childSynthEntry`/`synthesizeEntry`/診断入口を直接参照しないこと、**証明**が診断入口を直接参照しないこと、`synthesizeChild` が `synthesizeCombinational`（`Off` ではない）を呼ぶことを検査する。これは子の実行（child execution）が起きないことの検査ではない。注: 証明（`envFrame_coreHeadOff` と最終定理の値）は `CellPrem`（子の入口を保持する cell の状態の前提）を通じて `sparkleChildSynth` に触れる（`SCOPE-INFO` に列挙）。これは cell の内容についての**前提**であり、保証ではない。
2. **自動で非 leaf へ広げない**。4 leaf root の保証入口は `synthesizeCombinationalOff`（§21）。非 leaf の保証は上の仮説が全て供給されて初めて成り立つ条件付きの文であり、`synthesizeEntry`・旧 API・診断経路は旧入口のまま保証の外。`SPARKLE_PROFILE` 未設定で `else` 枝が選ばれたこと（§21.4）も供給していない。
3. `hcd`（`Ob`）・`hsrc`・`htop`・`hnoraw`・`hreadH/T`・`hchk`・`CellPrem`・`Laws/Start/hr` は**名前付き仮説のまま**（供給も縮約もしていない）。

### 24.3 組み立ての証明（`synth_hftPcieOutByte_finalOff`）

型: `∀ (CV : CDRel) (Ob : Environment → Prop), (∀ env, Ob env → HftObOf CV env) → HftFinalStmtOff Ob CV`。証明は S1k の `synth_hftPcieOutByte_final` と同じ形で、名前付き義務から結論を作る。インスタンス: `_Z`（`HftObCDZ`/`cdvZ`）、`_Y`、`_X`、`_old`（`fun _ => HftObCD`/`cdvOld`、旧 carrier の義務）、`_of`（`Ob := HftObOf CV`）。`hftFinalStmtOff_mono`（`CV ⊆ CV'` なら結論を移せる）。

**S1k の証明からそのまま持ち越せたもの**（carrier にも入口にも依らない）: `genGP_root_kids`（root の callee が全て leaf 行 ⇒ 表が `some p`、`p.decl`/`p.d`/`p.kD`）、kernel の事実（`root_wf/http_wf/tlp_wf`、`http_leaf/tlp_leaf`、`root_insts`、`root_kD`、`root_shape`）、`canon_row`、`startFacts_of_checked`、`EndpointLink` の組み立てと `observationsEqualMono_of_link`、`topShips_transport`、`hftRootType_shape`。

**入口の名前を替えた版が要ったもの**（S1q で作成済み。今回は使うだけ）: `postEntry` → `postEntryOff`、`root_find_of_headAt` → `root_find_of_headAtOff`、`machineDefinesLinked_of_reader_headAt` → `…_headAtOff`、`HeadAt` → `HeadAtOff`（`CellPrem` だけから）、`PostRun` → `PostRunOff`、`MachineDefinesLinked` → `…Off`。今回新たに書いたもの: `HftObTopCoreOff`/`HftObNoRawOff`（`Off` 版の義務）。

**CD 固有（旧 carrier）で新 carrier 版が要るもの**と、証明できたもの:
| 旧 | 新 | 状態 |
|---|---|---|
| `SourceDenotesMono`（`CD [] d.value`） | `SourceDenotesMonoV CV`（`CV env d.value`） | 定義。`cdvOld` で旧と `Iff.rfl` |
| `RootArtifactMono` | `RootArtifactMonoV CV` | 定義。`rootArtifactMonoV_mono`（`CV ⊆ CV'`）、`rootArtifactMono_to_Z` を証明 |
| `FGCircuitConclusionMono`/`fgCircuitConclusionMono_of_artifact` | `FGCircuitConclusionMonoV`/`fgCircuitConclusionMonoV_of_artifact` | 証明 |
| `DeclConnect`（`shapeOf` = domain binder 付きだけ） | `DeclConnectMonoV CV`（`monoShapeOf`）、`declConnectMonoV_of_rootArtifact`（root のみ）、`declConnectMonoV_mono` | 証明（callee は target にしない） |
| `sourceDenotesMono_unique`（`cd_fun`） | `sourceDenotesMonoV_unique`/`_eq`（`CDFunctional CV` が前提） | 証明。`cdvOld/X/Y/Z_functional` |
| `ObservationsEqualMono`（CD に依らない） | `observationsEqualMono_congr`、`observationsEqualMono_of_denotes` | 証明（意味の等式に沿って移る） |
| 4 leaf の `*_denotes`（`RootInEnv` + `CD` 導出 ⇒ `SourceDenotesMono`） | `sourceDenotesMonoV_mono cdvOld_to_Z` で移る | 証明（個別の新導出は不要） |
| `circCV` の `CDZ → CD` | 提供せず、使わない（非導出性の定理は無い） | 不在 |

### 24.4 関数性と、元ソースの値への導出の区別

- **関数性**（`CDFunctional`、`cdz_fun`、`sourceDenotesMonoV_unique`）: 同じ式・環境に対し、`CV` が導く型と値は**高々 1 つ**。これは関係が関数であるという性質で、証明済み（`cdvX/Y/Z/Old_functional`）。
- **元ソースの値への導出**: 導出 `CDZ env [] hftRootValue (MonoTy shHft) m` の索引 `m` を、元ソースの Lean 値 `synth_hftPcieOutByte` に**等しくする**ことは別の義務。`HftObCDZ` はこの導出そのもの（`m := synth_hftPcieOutByte` を索引に取る）で、**未供給**（S1r §22.4 の stuck: `bundle2`/`Signal.ap`、`Inhabited.mk`）。関数性があっても導出は得られず、導出があっても「規則の値が Lean 自身の定義である」ことは規則表の監査であり、`Expr` の書き換え（`recStep`/`MapStuck` 等）の意味保存は定理ではない（§22.3）。この束の文は、導出が**与えられたときに**結論へ接続する部分だけを証明する。

### 24.5 Check18 の出力

`kjob lake build Tools.ShippingFGCircuitS1tFinal`（exit 0）、`kjob lake build Tests.Gen5.FGCircuitPilotCheck18`（exit 0。土台の依存 919 jobs は冷たいビルド）。

- `FGCIRCUIT18 SIGNATURES`: `synth_hftPcieOutByte_finalOff`（全 carrier `CV`・全 `Ob` と橋 `hOb`）、インスタンス `_Z/_Y/_X/_old`、`cdvOld_to_Z`、`cdvZ_functional`、`sourceDenotesMonoV_unique`、定義 `SourceDenotesMonoV`/`RootArtifactMonoV`/`DeclConnectMonoV` の完全な型を独立に書いた文面（`ExpStmt`/`ExpThm`/…）と `isDefEq`（default）で照合し、binder の種類も一致。**60 mutant 棄却**（正規化後の式が構文的に異なり、かつ reducible 透過度で defeq でない）: `hr` が診断入口、コア義務が旧入口＋旧境界、旧 `PostRun`、旧 carrier の結論（`RootArtifactMono`）、reader / `hcd` / 結論が end world、各前提の欠落（`hcell`・`hchk`・`hreadH`・`hreadT`・`hcd`・`hsrc`・`htop`・`hnoraw`・`htop` 内の `hdRun`・橋 `hOb`）、別の root、別の post root、別宣言の data の `hchk`、carrier/義務の組の取り違え（`_Z` に `cdvY`/`cdvOld`/`HftObCDY`、`_old` に `cdvZ`、`_Y` と `_X` の入替）、`CD→CDZ` の逆向き、混在 carrier の関数性、形だけの一意性、定義から旧 carrier / params / levelParams / 形 / 観測 / post / `ShapeMatchesMono` を外したもの。`_Z` 文に対し 19 個の knob mutant も別に検査。
- `FGCIRCUIT18 HYPS`: 13 個の明示仮説 `L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd hsrc htop hnoraw`（名前と順序を検査）。`hhead`/`hdRun`/`hquiet`/`hg`/`hio`/`hgates`/`hRead`/`hE` は仮説に無い。どの仮説の型（`S1t`/`S1kStmt` の定義を 1 段展開）にも診断入口・旧 `MachineDefinesLinked`・旧 `PostRun`・`coreHead`・`HeadIO`・`HeadAt`・`synthesizeChild` は現れない。定理の明示引数は `CV Ob hOb`。
- `FGCIRCUIT18 SCOPE`: 接頭辞 S1t/S1q/S1kStmt の走査の範囲で（コンパイラ本体・完全な依存閉包は辿らない。子の実行が起きないことの検査ではない）、文（17 定数）は診断入口・子の入口のどれも直接参照しない。証明（37 定数を走査）は診断入口を直接参照しない。走査は fuel 切れで todo が残れば throwError で失敗する。対照: S1k の最終定理は診断入口（`synthesizeCombinationalCore`、`PostRun`）を直接参照する。`synthesizeChild` は `synthesizeCombinational` を呼び `synthesizeCombinationalOff` を呼ばない。`synthesizeCombinationalOff` は `synthesizeChild`/`synthesizeEntry` に触れない。`SCOPE-INFO`: 子の cell（`sparkleChildSynth`）に触れる値は `envFrame_coreHeadOff` と `synth_hftPcieOutByte_finalOff`（`CellPrem` の前提経由）。
- `FGCIRCUIT18 LOWFUEL`: fuel 3 の走査（文・証明の 2 本）は失敗する（負の対照）。本番の走査は todo を残さず完了する。
- `FGCIRCUIT18 AXIOMS`: 28 名、標準 axiom のみ。`#print axioms` も同様（`propext`・`Classical.choice`・`Quot.sound`）。

### 24.6 証明したもの / 名前付き仮説・未供給 / 次

- **証明した**: `synth_hftPcieOutByte_finalOff`（と `_Z/_Y/_X/_old/_of`、`hftFinalStmtOff_mono`）、`cdvOld_to_X/X_to_Y/Y_to_Z/Old_to_Z`、`cdv*_functional`、`sourceDenotesMonoV_mono/unique/eq`、`observationsEqualMono_congr/of_denotes`、`rootArtifactMonoV_mono`、`rootArtifactMono_to_Z`、`fgCircuitConclusionMonoV_of_artifact`、`declConnectMonoV_of_rootArtifact/mono`。
- **名前付き仮説・未供給**: `hcd`（`HftObCDX/Y/Z` と S1s の family。導出が未供給）、`hsrc`（`ExtStage … 2` の帰納）、`htop`（machine 経路の `TopShips`、子の package/`ChildShips`/`ResetNk`、root の closing）、`hnoraw`（run から出す補題が無い）、`hreadH/hreadT`、`hchk`、`CellPrem`、`Laws/Start/hr`。子の入口 `synthesizeChild` の `profile` 固定は未実施（`initialize` の模型 `ShippingInitFrame`/`ShippingStartAtLoad` との対応を保つ設計が要る。§21.2）。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。条件付きは減算しない。
- **次**: (1) `hcd` の導出（S1s の DW family / `bundle2`・`Inhabited` の規則）。(2) `hsrc`（`ExtStage` 帰納）。(3) `htop`/`hnoraw`。(4) 子の入口の `profile` 固定（`HftObTopCoreOff` の中の子の IO を縮約するため）。

## 25. S1u（Issue `sparkle-fg-circuit-pilot` の次の束）: 非 leaf root `synth_hftPcieOutByte` の `hsrc` — `ExtStage` 帰納、子の `src`、残る root 側の 1 文

土台 `90d5ec10`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は各 1 回）: `Tools/ShippingFGCircuitS1uSrc.lean`、`Tests/Gen5/FGCircuitPilotCheck19.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない。S1s の領域（`Tools/ShippingFGCircuitS1sCD.lean`、Check17、§23）には触れていない。Issue の状態は変えていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で台帳に数えない。

### 25.1 手順 1: 文の固定（完全な型を先に）

`HftObSrc`（S1k §15.2、`Tools/ShippingFGCircuitS1kStmt.lean`）は**そのまま**（Check19 が S1k の文面と同じ独立文面 `ExpObSrc` と `isDefEq`）:
```
HftObSrc lvl env := ∀ p : Pkg ι (fun _ => defaultDomain), GPt lvl env hftRoot = some p →
  ∀ i bools bits, p.src i bools bits = monoObs shHft synth_hftPcieOutByte bools bits
```
`HftObSrc` を run 非依存の部分と子の事実に**分けた**。分割の全体の型（`Tools/ShippingFGCircuitS1uSrc.lean`）:

1. **子の `src`（証明した。仮説にしない）**: 子 `httpGetByte`/`tlpCplByte` は 2 つとも `ss = []`・`insts = []` の組合せ leaf（`genSemI` の `comb` 腕）。`genSemI_comb_src`: `gi.d = d`、`d.ss = []`、`d.shape.insts = []`、`machine_result` 型の式（任意の `x : HList (tys d.ss)` で成り立つ）から `(genSemI Q X gi).src = obs`。子の `obs` は宣言側の観測 `child.machineSource defaultDomain bools bits`（kernel の `Eq.refl` で出た生成済み endpoint の項: `fun t => ((httpGetByte (bits 1 6)).val t).toNat`、`tlpCplByte (bits 1 16) … (bits 6 5)`）。
2. **`ExtStage` 帰納（証明した）**: `callee` は package の `d`/`kD`/`src` しか読まない（`calleeOut`）。そこで `CalleeAgree q q' := q.d = q'.d ∧ q.kD = q'.kD ∧ q.src = q'.src`、`AgreeAt Q Q' c`、`TablesAgree Q Q' d`（`d` の callee 名の各点でだけ）を置き、`calleeOut_agree_tables` → `callOut_agree_tables` → **`ExtStage_agree_tables`**（段数 `n` についての帰納）→ `genSemGen_agree_tables`。有限リスト一般: callee 表が `d.shape.insts` の名前で `CalleeAgree` なら全段の `ExtStage` が一致する（HFT の `k = 2` は `d.shape.insts.length`）。
3. **表側（証明した）**: `genGP_root_kids_src`（S1k の `genGP_root_kids` の拡張）: root の callee が全て leaf 行なら、`genGP` の package の `src` は `genSemI (genS K) root (g.toIn hs)` の `src`、かつ各 callee 名 `c` で `genS K c = some (genSemI (genS K) c (gc.toIn hs))`（`genS_leaf_eq`）。
4. **root 側の 1 文（名前付き仮説 `HftRootLink`）**: 静的な 2 子の表 `hftKids`（`kidSem`: 子の `d`、`kDOf d`、`initsOf d`、`src := machineSource`）、完全な型:
```
HftRootLink : Prop := ∀ {ι : Type} (gi : GenIn), gi.d = synth_hftPcieOutByte.machineData →
  ∀ (i : ι) (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) (S : Signal defaultDomain (HList (tys gi.d.ss))),
    S.val 0 = gi.inits →
    (∀ t, S.val (t+1) = evalTerms (… typedVal gi.d.nIn … (extBOf hftKids gi i bools bits S) (extOf hftKids gi i bools bits S) t (S.val t) …) gi.d.nexts) →
    ∀ t, (monoObs shHft synth_hftPcieOutByte bools bits).map (fun f => f t) = gi.d.outs.map fun o => enc o.1 (eval … (extBOf hftKids gi i bools bits S) (extOf hftKids gi i bools bits S) … o.2)
```
`extBOf/extOf hftKids gi` = `ExtStage hftKids gi … gi.d.shape.insts.length`（root は callee 2 個）。run・環境・table に依存しない（root 宣言と子の宣言の観測だけの文）。`hftGenIn : GenIn`（`machine_ok`/`machine_body`/`initOk` の kernel 事実から）があるので量化は空でない。

組み立て `hftObSrc_of_rootLink : HftRootLink → ∀ {ι} lvl env, RootReader … root → RootReader … http → RootReader … tlp → HftObSrc lvl env`。証明: `canon_row` ×3、`genGP_root_kids_src`、`genSemI` の腕の選択は `ss.isEmpty && insts.isEmpty`（両方空なら `comb` 腕）なので、root が `gen` 腕になる根拠は **`insts` が空でないこと**（kernel: `root_insts_nonempty : insts.isEmpty = false`。`ss` の中身には依らない）、したがって `genSemI` は `gen` 腕（`genSemGen`）、`TablesAgree (genS K) hftKids gi.d`（子は `genSemI_comb_src` と `genSemI_d`/`genSemI_kD`）、`CalleesCausal (genS K) gi.d`（子は `comb` 腕: `genSemI_srcCausal`）、`ExtStage_agree_tables` で `genS K` から `hftKids` に移し、`genSemGen_src_eq_of_link`（下）と `HftRootLink`。

`genSemGen_src_eq_of_link`（一般、証明した）: `src_eq_of_states`（leaf: `ExtStage … 0 = id`）の非 leaf 版。loop の再帰は `loop_state_causal`（呼び出しの値は過去の状態にも依存するので pointwise でなく causal）、causal 性は `extCausal_of_genSem`（`CalleesCausal`）。仮定は「生成された再帰に従う任意の状態列について、宣言の観測 = データの `outs` の評価」（`hlink`）の 1 つ。

### 25.2 `synth_hftPcieOutByte_finalOffL`: `hsrc` を落とした最終文（`HftFinalStmtOffL Ob CV`）

`HftFinalStmtOff Ob CV`（S1t）から `hsrc` を除き、前に `(hlink : HftRootLink)` を置いたもの。`hsrc` は `hchk` と 2 つの子の reader から `hftObSrc_of_rootLink` で導く（`startFacts_of_checked` で root の reader を出す）。インスタンス `_Z/_Y/_X/_of`。**束縛の一覧（Check19 HYPS）**:

| | 明示仮説 |
|---|---|
| S1t `HftFinalStmtOff` | `L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd hsrc htop hnoraw`（13） |
| S1u `HftFinalStmtOffL` | `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hnoraw`（13） |

`hsrc`（`lvl`・環境・table に依存する文）が `hlink`（`HftRootLink`: run・環境非依存、root 宣言の 1 文）に**置き換わった**。仮説の個数は同じ（「1 つ減った」とは言わない）。変わったのは種類: 子の `src`・`ExtStage` 帰納・table 側の `genS`/`genGP` の扱いは仮説でなくなり、root 側の宣言の事実 1 文だけが残る。

### 25.3 何が残っているか（`HftRootLink`、FG D.D-3 / DG-SEM）と、なぜ閉じなかったか

`HftRootLink` は次の 2 つの事実を合わせたもの。どちらも root 固有で、この束では証明していない（impossible とは言わない）:
- **(a) 呼び出しの引数**: `ExtStage hftKids` の段 `k` は引数を `lsrcAt gi.d …`（データの `ls` 項の評価）から取る。一方 Lean 側の root は引数を Lean の Signal 式（レジスタの値）で渡す。`ls` の評価 = Lean の引数 Signal の値、という等式は root の生成済み endpoint に**無い**（`machine_writes`/`machine_result` は `nexts`/`outs` だけ、`machineExt` は `ls` を通らず Lean の呼び出しを直接使う。`machine_causal_k` は因果性だけ）。per-call の kernel 事実として生成するか、`ls` の項と Lean の引数式の対応を作る必要がある。
- **(b) fused 状態**: root は `Tele` で融合した状態（外側 `tys [bits 6]` と内側の `Sigs`）を持ち、endpoint の `machine_writes`/`machine_result` は `castSS (TeleT.fstate …)` 上の文。`GenIn` の `d.ss` 上の状態列 `S` を Lean 側の融合状態と同一視する帰納が要る（leaf root は `machineSigma` があるが、この root には `machineSigma` が無い）。

したがって前提の分類: 子の `src`・`ExtStage` 帰納・table 側（証明）/ `HftRootLink`（名前付き仮説）/ `hcd`（`Ob`）・`htop`・`hnoraw`・`hreadH/T`・`hchk`・`CellPrem`・`Laws/Start/hr`（S1t §24.2 のまま、供給していない）。S1s の領域（`hcd` の導出）は触れていない。

### 25.4 Check19 の出力

`kjob lake build Tools.ShippingFGCircuitS1uSrc`（exit 0、`#print axioms` は `propext`・`Classical.choice`・`Quot.sound` のみ）、`kjob lake build Tests.Gen5.FGCircuitPilotCheck19`（exit 0、922 jobs、error 0）。

- `FGCIRCUIT19 SIGNATURES`: `HftObSrc`（応用定義として）、`HftRootLink`、`hftObSrc_of_rootLink`、`ExtStage_agree_tables`、`genSemI_comb_src`、`synth_hftPcieOutByte_finalOffL` と `_Z` の完全な型を、独立に書いた文面（`ExpObSrc`/`ExpLink`/`ExpSrcThm`/`ExpStageAgree`/`ExpCombSrc`/`ExpFinalL`/`ExpThmL`）を正規化（定義の展開と literal Bool の `if` の選択）したものと `isDefEq`（default）で照合し、binder の種類も一致。**67 mutant 棄却**（正規化後の式が構文的に異なり、かつ reducible 透過度で defeq でない）: `HftRootLink` について 子の入れ替え（名前ごと／`src` だけ／`data` だけ）、http の `src` が tlp の観測、表が空、段数 `k = 0/1/3`、start 前提なし、再帰前提なし、結論が別の観測、別の root の `data`（12）。`HftObSrc` は観測なし／別の宣言（2）。`hftObSrc_of_rootLink` は link 欠落、root/http/tlp の reader の欠落、root の reader が別 data、結論が別宣言（6）。`ExtStage_agree_tables` は `d`/`kD`/`src` 一致の欠落（3）。`genSemI_comb_src` は `ss = []`/`insts = []`/観測式の欠落（3）。`synth_hftPcieOutByte_finalOffL`（全 carrier）は 20、`_Z` インスタンスは別 carrier（`cdvY`/`cdvOld`）・別 `Ob`（3）と、各 knob（link 欠落、**`hsrc` を残したもの**、診断入口の `hr`、旧 carrier の結論、`hcell`/`hchk`/`hreadH`/`hreadT`/`hcd`/`htop`/`hnoraw`/`htop` 内の `hdRun` の欠落、別の root、別の post root、別宣言の data の `hchk`、reader / `hcd` / 結論が end world）（18）。
- `FGCIRCUIT19 HYPS`: `synth_hftPcieOutByte_finalOffL_Z` の明示仮説は `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hnoraw`（13。名前と順序を検査）。`hsrc`・`hhead`・`hdRun`・`hquiet`・`hg`・`hio`・`hgates`・`hRead`・`hE`・`hP` は仮説に無い。どの仮説の型（`S1t`/`S1kStmt`/`S1u` の定義を 1 段展開）にも `HftObSrc`・診断入口・旧 `MachineDefinesLinked`・旧 `PostRun`・`coreHead`・`synthesizeChild`・`sorryAx` は現れない。`hlink` は run・環境・world・`MachineDefinesLinked` に触れない（run 非依存）。定理の明示引数は `CV Ob hOb`。
- `FGCIRCUIT19 AXIOMS`: 19 名、標準 axiom のみ。
- `FGCIRCUIT19 SNAPSHOT19`: 2 つの子の `machineSource` は宣言の観測（kernel `rfl`: `fun t => ((httpGetByte (bits 1 6)).val t).toNat`、`tlpCplByte (bits 1 16) … (bits 6 5)`）、`hftKids` は 2 つの子だけ（root 名では `none`）、`hftGenIn : GenIn` が root の data 上にある（量化は空でない）、root の `insts` は `[httpGetByte, tlpCplByte]`（段数 2）、root には `machineExt` があり `machineSigma` が無い（`HftRootLink` の (b) は endpoint の事実でない）。2 つの子には `machine_next`（組合せ leaf）。

### 25.5 次

(1) `HftRootLink` を (a) 呼び出し引数の対応（per-call の kernel 事実）と (b) fused 状態の同一視に分けて閉じる（(a) は `#machine_endpoint` 側の生成に近い）。(2) `htop`/`hnoraw`、`hcd`（S1s）。


## 26. S1x（Issue `sparkle-fg-circuit-pilot` の次の束）: `hnoraw : HftObNoRawOff` を run から供給する（`NoRawBelow` を全深さで）

土台 `15fb4615`（par/fgc-s1: S1v + S1u のマージ）。追加ファイル（既存は書き換えていない。lakefile 登録は各 1 回）: `Tools/ShippingFGCircuitS1xNoRaw.lean`、`Tests/Gen5/FGCircuitPilotCheck20.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない。S1s の領域（`Tools/ShippingFGCircuitS1sCD.lean`、Check17、§23）には触れていない。Issue の状態は変えていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で台帳に数えない。

### 26.1 手順 1: 評価（先に記録する）

`HftObNoRawOff`（S1t）は、core run `(raw, D₀)` と後処理後（IR design、SV の印字ではない）`(b, D')` について (i) `∀ n, NoRawBelow D₀ raw.name (n+1) raw`、(ii) `∀ n, NoRawBelow D₀ raw.name (n+1) (checkedOptimize b)`、(iii) `b.body` のどの instance も `raw.name` を指さない、の 3 つ。`NoRawBelow` は「top に戻らない」ことで、グラフ全体の非循環は十分条件の 1 つにすぎず、要らない。`designTransport_of_noRawBelow` は全 `n` を要し、深さ 1..6 の snapshot は供給にならない。評価した結果:

1. **run が instance の target について与えるもの**: 子の module 名は子宣言から作られる（`synth c` が返す module の名前）が、**top と名前が違うことを名前の作り方（`ofDecl` の単射性）から出す道は取っていない**。代わりに、machine 経路の最後の `closeInsts`/`closeInstsG`（`Sparkle/IR/Machine.lean`、`MachineInstG.lean`）が **実行時に** 検査している: `noInstOfB m.name body && d'.modules.all (fun g => noInstOfB m.name g.body)`（「閉じる module の instance を、その module 自身と設計の全 module が持たない」）。結果 `(raw, D₀)` はこの検査を通った値なので、`raw` の body にも `D₀` の**全 module** にも `raw.name` を target にする instance は無い。既存の `closeInsts_acyclic`/`closeInstsG_acyclic`（`ShippingChildServe`）と `noRawBelow_of_noInstOf`（`ShippingGen5DCEntryS`、U-NORAW）がこれを `NoRawBelow`（全深さ）にしていたが、**core run とこの等式の接続**（S1x 以前の「Does NOT link a given core run's (raw, D)」）が無かった。
2. **`D'`（後処理済み）が top を自分の下に含み得るか**: `D' = topMap f raw D₀`（`PostEntry`）は名前が `raw.name` の module だけを差し替える。top 以外の module は `D₀` のままなので 1. の検査で自由。差し替えた top `b` は `dropZeroWidthModule raw` か、その `mergeChecked`。前者は instance 文の target を保つ（`dropZeroWidth_inst_target`: `dzStmt` は `.inst mn i conns` を `.inst mn i conns'` にするだけ）。後者は instance を含むなら `mergeChecked_inst`（`ShippingMachineShipsHier`）で `= dropZeroWidth raw`。よって `b` の instance の target は `raw` のそれに含まれ、`raw.name` ではない（`post_inst_target`、`noB_of_post`、(iii)）。`checkedOptimize b` は `hierGate b` の下で `b` と同じ instance 文を持つ（`checkedOptimize_inst_iff_gate`）。したがって `D'` は top を自分の下に含まない（`hgate` の下で）。
3. **最小の run-local な事実**: (a) 閉じる検査の結果 `NoInstOf raw.name raw.body ∧ ∀ g ∈ D₀.modules, NoInstOf raw.name g.body`（`coreOff_closed` で run から証明）、(b) 後処理後の top の文の gate `hierGate b = true`（`optimizeModule` が instance 文を保つ補題が木に無い枝（`checkedOptimize` の最後の `else o`）を避けるため。名前付きのまま）。

### 26.2 証明したもの（`Tools/ShippingFGCircuitS1xNoRaw.lean`、`kjob lake build` exit 0、標準 axiom のみ）

| 名前 | 内容 |
|---|---|
| `coreOff_closed` | `RunsTo (synthesizeCombinationalCoreOff X) … (m, d)`、`MachineDefinesLinkedOff … shape`、`MachineCloses … shape`、`shape.insts ≠ []` ⇒ `NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, NoInstOf m.name g.body`。`core_chainOff` → `synthesizeFromConst_machineR` → `synthesizeMachineCertified_returns`（`CloseCalls`）→ `closeInsts_acyclic`/`closeInstsG_acyclic`。法則 `Laws`・`JQ` は使わない |
| `coreOff_noRawBelow` | 上から `∀ k, NoRawBelow d m.name k m`（全深さ） |
| `dropZeroWidth_inst_target`、`post_inst_target`、`noB_of_post` | 後処理は instance の target を増やさない。(iii) |
| `noRawBelow_opt` | `hierGate b = true` の下で `∀ k, NoRawBelow D raw.name k (checkedOptimize b)`（(ii)） |
| `hftShape_insts_ne` | root の `shape.insts ≠ []`（S1u の kernel 事実から） |
| `hftObNoRawOff_of_run` | `hdRun`（core run の `MachineDefinesLinkedOff`）、`hcl : MachineCloses … hftRoot shape`、`hgate : HftPostGate …` ⇒ `HftObNoRawOff mctx mref cctx cref w b D'` |

`HftPostGate`（完全な型）: `∀ raw D₀ w1, RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 → PostEntry b raw D₀ D' → Sparkle.IR.RefineCheck.hierGate b = true`。

### 26.3 `hnoraw` を置き換えた最終文（束縛の一覧）

`HftFinalStmtOffLN Ob CV`（S1u の `HftFinalStmtOffL` の `hnoraw` を `hcl`・`hgate` に替えたもの）、`synth_hftPcieOutByte_finalOffLN`（全 `CV Ob hOb`）、インスタンス `_Z/_Y/_X`。**明示仮説（14）**: `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hcl hgate`（`hnoraw` は無い）。`hdRun`（core run の `MachineDefinesLinkedOff`）は S1t と同じく `hchk`/`hcell` から**内部で導く**（仮説にしない）。証明は `hftObNoRawOff_of_run hdRun hcl hgate` を `synth_hftPcieOutByte_finalOffL` の `hnoraw` に渡すだけ。

| | 明示仮説 |
|---|---|
| S1u `HftFinalStmtOffL` | `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hnoraw`（13） |
| S1x `HftFinalStmtOffLN` | `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hcl hgate`（14） |

仮説の数は 1 つ増えた（`hnoraw` が `hcl` と `hgate` の 2 つに分かれた）。変わったのは種類: `hnoraw`（`NoRawBelow` を全深さで）は、`hcl` と `hgate` から証明される形になった。**ただし `hcl : MachineCloses …` は `∀ tenv logProf w r w′` を量化する既存の強い未供給前提であり、これは対象 run だけから `hnoraw` を閉じたことではない**（対象 run 単独の事実は `RunsTo` と `MachineDefinesLinkedOff` までで、閉じる段が `none` を返さないことは全 world 前提のまま）。`hgate` も未供給。局所化は §28。

### 26.4 残っているもの（名前付き仮説。impossible とは言わない）

- **`hcl : MachineCloses … hftRoot synth_hftPcieOutByte.machineData.shape`**（FG D.T-4）: machine 経路の閉じる段が `none` を返さない。4 leaf root には生成済みの `machine_closes` がある（導出可能）が、この root には**無い**（Check19/Check20 SNAPSHOT が存在しないことを検査）。root は 2 つの call を持ち `closeInstsM/GM` を通る。`MachineCloses` は `closeInsts*` の `some` を要求するので、閉じる検査（`woCheck`・`linkedOk`・`kidsCombB` など）を子の実出力で評価する必要がある。S1iChild の `noRawBelowB` のような計算検査器で実出力を評価する道はあるが、run の結果に結ぶ部分は今回していない。
- **`hgate : HftPostGate`**（FG D.T-4）: 後処理後の top `b` が `hierGate` を満たす。`b` が `dropZeroWidth raw`（または merge）で、`raw.body` が instance と `seqStmtOk` な文だけなら成り立つはずだが、`raw` の body の形（closing が作る body）を run から導く補題は未作成。
- 子の合成中の IO（`synthesizeChild`・`sparkleChildSynth`）は `hr`/`htop` の中の仮説のまま（S1t §24.2）。`closeInstsGM` が使う `children` は `synth c`（診断入口）の結果だが、`coreOff_closed` は `CloseCalls` の存在量化だけを使い、子の run の内容には立ち入らない。

### 26.5 Check20 の出力

`kjob lake build Tools.ShippingFGCircuitS1xNoRaw`（exit 0）、`kjob lake build Tests.Gen5.FGCircuitPilotCheck20`（exit 0、923 jobs。作りを軽くした: 署名の照合を小さい `run_cmd` に分割。標準の `isDefEq`＋`whitelist` 展開の正規化）。

- `FGCIRCUIT20 SIGNATURES-A`: `HftPostGate`、`coreOff_closed` を独立に書いた文面（`GateTrue`/`ExpClosed`）と `isDefEq`（default）で照合し、binder の種類も一致。**8 mutant 棄却**（gate: 別の root／`hierBinds`／定数 true／`PostEntry` なし、closed: 閉じる前提なし／instance の前提なし／body だけの結論／旧 core の run）。
- `FGCIRCUIT20 SIGNATURES-B1`: `hftObNoRawOff_of_run`（`ExpRun`）に **6 mutant 棄却**（`hdRun` の shape が別、`hcl` の shape が別、`hcl` が別の宣言、`hdRun` が別の root、gate なし、定数 gate）。
- `FGCIRCUIT20 SIGNATURES-B2`: `synth_hftPcieOutByte_finalOffLN_Z` を独立に書いた `ExpFLN` と照合。**9 mutant 棄却**（`hcl` なし、別の shape、`hgate` なし、定数 gate、別 root の gate、carrier `cdvY`/`cdvOld`、obligation `HftObCDY`、`hnoraw` を残した S1u の文）。
- `FGCIRCUIT20 REMAINING`（2 行）: `hcl : MachineCloses … hftRoot synth_hftPcieOutByte.machineData.shape`、`hgate : HftPostGate …`。
- `FGCIRCUIT20 HYPS`: 14 個の明示仮説の名前と順序、`hnoraw`・`hsrc`・`hdRun` ほかは仮説に無い、`hcl` は `MachineCloses`、`hgate` は `HftPostGate`。仮説の「診断入口を直接参照しない」走査は、**仮説の型の定数と、`Tools.ShippingFGCircuitS1{t,kStmt,u,x}` の定義を 1 段だけ展開した定数**に対する限定的な走査であり、依存閉包全体に診断入口（`synthesizeChild` など）が現れないことの検査ではない。
- `FGCIRCUIT20 AXIOMS`: 12 名、標準 axiom のみ。
- `FGCIRCUIT20 SNAPSHOT20`: root は call 2 つ（kernel `decide`）、root に `machine_closes` は無く leaf root にはある。

Check の出力行は 8（SIGNATURES-A/B1/B2、REMAINING ×2、HYPS、AXIOMS、SNAPSHOT20）、棄却した mutant は計 23。

### 26.6 次

(1) `hcl`: 閉じる段の検査（`closeInstsG` の各 `Bool`）を、root の 2 つの子の実出力に対して評価し、`MachineCloses`（run の `none` を排除）にする。(2) `hgate`: 閉じた body の形から `hierGate`。(3) `htop`、`hcd`（S1s）、`HftRootLink`。

## 27. S1y（Issue `sparkle-fg-circuit-pilot` の次の束）: `HftRootLink` の分割の調査と Check19 の高速化（**未完: `HftRootLink` は証明していない**）

土台 `15fb4615`。Issue の状態は変えていない。S1w/S1x の領域には触れていない。TRUSTED・axiom・sorry・native_decide・新しい law はない。台帳の変更なし（FG 75 / T1 57、今回 ±0）。

### 27.1 結果（正直に）
- **`HftRootLink` は証明していない**。仮説の個数は S1u と同じ（`HftFinalStmtOffL` の 13、`hlink` を含む）。`synth_hftPcieOutByte_finalOffL` に `hlink` を落とした版はまだ無い。`Tools/ShippingFGCircuitS1yLink.lean` と Check21 は作っていない（この束では時間切れ。impossible とは言わない）。
- 調査（root の生成済み endpoint の事実、`kjob lake build` した探査で確認）: root の `machineData.ss = [bits 6]`、`machine_writes`/`machine_result` は `castSS (TeleT.fstate … (TeleT.cons [bits 4, bits 8, bits 16, bits 8, bits 32, bool] …))` 上の文で、`S : Signal (HList (tys [bits 6]))` に加えて融合状態 `Ss` を取る。`machineExt : Unit → bools → bits → Signal (HList (tys [bits 6])) → (Nat → (n:Nat) → Signal (BitVec n))`（Lean の呼び出しを状態 Signal 上で直接評価する形）。`machineExtB`・`machine_causal_k`・`machine_call_k`・`machine_ext_causal`・`machineSigma` は**無い**。
- したがって (a)（`ls` 項の評価 = Lean の引数 Signal）には、`machineExt` と `d.ls` の対応を言う per-call の事実が要る。(b)（`d.ss` の状態列 = 融合状態）には、`Ss` と `S` を結ぶ `machineSigma` 相当の事実が要る。どちらも既存の endpoint 機構（`ShippingMachineCommand.lean` の非 loop の Tele 経路、約 1924 行）に狭い証拠として足す案で、生成される IR/SV は変えない（新しい `addDecl` の定理だけを足す）方針。実装は次の束。

### 27.2 Check19 の高速化
`FGCircuitPilotCheck19` の署名ブロックは、同じ実型を mutant ごとに `norm`（定義の展開 6 回）し直していた（例: `synth_hftPcieOutByte_finalOffL` は 20 回）。実型の正規形を型ごとに 1 回だけ計算してキャッシュする（`normC`）。mutant 側の `norm` は式が違うので残る。ファイル分割は未実施。

ビルド時間: 前 約 13 分（S1u の記録）／後 **未計測**（kjob lake build はこの Pod で毎回 922 job を最初から構築し、計測が時間内に終わらなかった。キャッシュ変更が Check19 で通ること自体も未確認）。次の束で計測する。


## 28. S1z（Issue `sparkle-fg-circuit-pilot` の次の束）: `hcl` を対象 run の閉じる成功へ局所化し、`hgate` を閉じた body の形から導く

土台 `a8a007e5`。追加ファイル: `Tools/ShippingFGCircuitS1zClose.lean`、`Tests/Gen5/FGCircuitPilotCheck23.lean`（lakefile 登録は各 1 回）。S1w2（`ShippingFGCircuitS1w*`、Check17/22、§23）と S1y（`ShippingFGCircuitS1yLink`、Check19/21、§25/§27）には触れていない。新しい law・axiom・TRUSTED・sorry・native_decide はない。Issue の状態は変えていない。成果は**条件付き**で台帳に数えない。

### 28.1 方針（先に型を決める。証明は 28.3 以降）

- **`hcl` の局所化**（レビュー裁定）。`MachineCloses`（`∀ tenv logProf w r w′`）を新たに全 world で仮定するのをやめる。仮定するのは**対象 `core_chainOff` が実際に通った経路の中の 1 回の machine run**（`synthesizeMachineCertified`）の閉じる成功だけ。その run は (a) 対象 core run `RunsTo (synthesizeCombinationalCoreOff declName) … w (raw, D₀) w1` の分解（`coreHeadOff`・`getConstInfo`・`getEnv`・`synthesizeFromConst` の run が結果 `(raw, D₀)` を返す）に紐づき、(b) `tenv` はその分解の `envR`、logger は `profLogIO false`、(c) 開始 world はその `synthesizeFromConst` が 2 回目に読む `getEnv` の終了 world `w8`（`w3` から読んだ `envR'`）、(d) shape は root の `machineData.shape`。この run の中で `closeInstsGM` が子の `synth c` を実行し、その**実出力**（`children`）に対して閉じる検査（`woCheck`/`linkedOk`/`kidsCombB` …）が評価される。別の子の出力ではない。
- **`hgate` の導出**。`HftPostGate` を仮説にせず、同じ局所化された閉じる成功から、`MachineRanA`（既存。その run が `some (raw, D₀)` を返し、`closeLets`、`CloseCalls`、`ChildrenRealA` を持つ）を作り、既存の `core_hierGate_anyA`（閉じた body は「instance + `closeMachine` の `seqStmtOk` 文」、後処理 `dropZeroWidth`／`mergeChecked` が文の種類を保つ）に渡す。snapshot は供給にしない。
- 仮説の個数: `hcl`＋`hgate`（14 個中の 2 つ）が **`hclL` の 1 つ**になる（明示仮説 13）。

### 28.2 完全な型

```lean
/-- 局所化した hcl: 対象 core run が通った machine run は `none` を返さない -/
def CoreCloses (declName : Name) (shape : MachineShape)
    (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) : Prop :=
  ∀ (raw : Module) (D₀ : Design) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (raw, D₀) w1 →
    ∀ (s : CoreSaved) (wh w2 w3 w4 : Void IO.RealWorld) (envR : Environment) (ci : ConstantInfo),
      RunsTo (coreHeadOff declName) mctx mref cctx cref w s wh →
      RunsTo (getConstInfo declName) mctx mref cctx cref wh ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (profLogIO false) declName [] false true
        (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (instancePredicate envR))
        mctx mref cctx cref w3 (raw, D₀) w4 →
      ∀ (envR' : Environment) (w8 w10 : Void IO.RealWorld) (r : Option Res),
        RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w8 →
        RunsTo (synthesizeMachineCertified (fun e hint top named => translateExprToWire envR e hint top named)
          (profLogIO false) declName shape) mctx mref cctx cref w8 r w10 →
        r ≠ none

abbrev HftCoreCloses mctx mref cctx cref w := CoreCloses hftRoot synth_hftPcieOutByte.machineData.shape mctx mref cctx cref w
```

`hgate` は仮説でなく定理: `hftPostGate_of_local`

```lean
theorem hftPostGate_of_local {mref cref} (L : Laws mref cref) {mctx cctx w b D'}
    (hstart : Start L mctx cctx w)
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1)
    (hclL : HftCoreCloses mctx mref cctx cref w) :
    HftPostGate mctx mref cctx cref w b D'
```

最終文（`hcl hgate` を `hclL` 1 つに替える）:

```lean
def HftFinalStmtOffLNL (Ob) (CV) : Prop :=
  ∀ (hlink : HftRootLink) {ι} {mref} {cref} (L : Laws mref cref) (lvl) (env₀) {mctx cctx w w' b D'}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem MkRefd mref cref) (hchk : CheckedStart …) (hreadH : …) (hreadT : …)
    (hcd : Ob (envAt cref w))
    (htop : ∀ p, GPt lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hclL : HftCoreCloses mctx mref cctx cref w),
    (∃ raw, PostRunOff …) ∧ ∃ mm p, RootArtifactMonoV CV …
```

明示仮説（13）: `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hclL`。

### 28.3 対照（Check23 が `isDefEq`＋独立に書いた文面で、次のそれぞれが**同じでない**ことを確認する）

- 別の world: `w8` の代わりに `w3`（getEnv を読む前の world）／`w`（対象 run の開始 world）で machine run を始める。
- 別の shape: root の shape の代わりに `counterLoop` の shape／`httpGetByte` の shape。
- 別の出力: 結論が `r ≠ none` でなく `r = none`／`r = some (raw, D₀)`（強すぎる）／`r ≠ some (raw, D₀)`。
- 別の run: 対象 core run に紐づかない（`RunsTo core … (raw, D₀) w1` の前提なし）、分解を fresh な `tenv logProf` で量化した旧 `MachineCloses` の形。

### 28.4 証明したもの（`Tools/ShippingFGCircuitS1zClose.lean`、`kjob lake build` exit 0、標準 axiom のみ）

| 名前 | 内容 |
|---|---|
| `CoreCloses`、`HftCoreCloses` | 28.2 の型（局所化した `hcl`） |
| `coreCloses_of_machineCloses` | 全 world の `MachineCloses` ⇒ `CoreCloses`（局所化は**弱い**前提。強い前提を新たに足したのではない） |
| `synthesizeFromConst_machine_invW` | 既存 `…_invR` の写し。machine run の**開始 world を露出**（本体の `getEnv` が読む `w6`）。証明は `invR` と同じ |
| `coreOff_ranA` | `Start L`、core run、`MachineDefinesLinkedOff`、`CoreCloses` ⇒ `MachineRanA L.O …`（run が `some (raw, D₀)`、`closeLets`、`CloseCalls`、`ChildrenRealA`）。`core_chainOff` → `coreHeadOff_jqcA`/framed で `JQC (0+1)` を `w3` まで運び、`invW` で `w8` へ、`CoreCloses` で `r ≠ none` |
| `closed_of_ranA` | `MachineRanA` ⇒ `NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, …`（`closeInsts_acyclic`/`closeInstsG_acyclic`） |
| `hft_callsOk`、`hft_slots`、`hft_domB`、`hft_outTy`、`hft_nomem` | root の `machineData` の事実（kernel `decide`） |
| `hftPostGate_of_local` | **`hgate` の導出**: `coreOff_ranA` ＋ 既存 `core_hierGate_anyA`（閉じた body ＝ instance ＋ `closeMachine` の `seqStmtOk` 文、後処理の 2 枝）。`HftPostGate` は仮説でなくなった |
| `hftObNoRawOff_of_local` | `HftObNoRawOff` を `Start L`・`hdRun`・`HftCoreCloses` から |
| `HftFinalStmtOffLNL`、`synth_hftPcieOutByte_finalOffLNL`（`_Z/_Y/_X`） | 28.2 の最終文。**明示仮説 13**: `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hclL`（S1x の 14 から `hcl hgate` が `hclL` 1 つに） |

`hdRun` は S1x と同じく `hchk`/`hcell` から内部で導く。

### 28.5 残るもの（名前付き仮説。impossible とは言わない）

- **`hclL : HftCoreCloses`**（FG D.T-4）。対象 run が通った `synthesizeMachineCertified` が `none` を返さない: `closeLets` が root の transition を受理し、`closeInstsGM` の閉じる検査（`woCheck`・`linkedOk`・`kidsCombB` など）が**同じ run の中で実行された子の実出力**（`synth c`）に対して成り立つ。ここでは証明していない。対象 core run の結果 `(raw, D₀)` だけでは、machine 経路が `none` を返して fallback 経路が同じ型の `(Module × Design)` を返した場合を除外できない（`synthesizeFromConst` の定義）。証明には子の run の実出力（`hr`/`htop` の内側の IO、§24.2）に対する検査の評価が要る。
- 他の仮説（`HftRootLink`、`hcd`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws`/`Start`/`hr`）は S1x のまま。`hgate` と `hnoraw` は仮説から消えた。
- 仮説走査（Check23 HYPS）は S1w2/S1y と同じ限定走査（型の定数と、パイロットの定義の 1 段展開）。依存閉包全体に診断入口が現れないことの検査ではない。

### 28.6 Check23 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck23`、exit 0、924 jobs）

- `FGCIRCUIT23 SIGNATURES-A`: `HftCoreCloses` を独立に書いた `ExpCC`（world・env・logger・shape・出力・root を引数にしたもの）と `isDefEq`（default）で照合。**14 mutant 棄却**（別 world: `w3`／開始 world `w`、別 shape: `counterLoop`／`httpGetByte`、別出力: `= none`／`= some (raw, D₀)`／`≠ some (raw, D₀)`／`True`、別 env、別 logger、別 root、全 world の `MachineCloses`、core run なし、`synthesizeFromConst` との連結なし）。
- `FGCIRCUIT23 SIGNATURES-B`: `hftPostGate_of_local`・`hftObNoRawOff_of_local` を照合。**13 mutant 棄却**。
- `FGCIRCUIT23 SIGNATURES-C`: `synth_hftPcieOutByte_finalOffLNL_Z` を `ExpFLNL` と照合。**12 mutant 棄却**（`hcl`＋`hgate` を残した S1x の文を含む）。
- `FGCIRCUIT23 REMAINING`（1 行）: `hclL`。`FGCIRCUIT23 HYPS`: 13 個の名前と順序、`hnoraw`/`hcl`/`hgate`/`hdRun` ほかは仮説に無い、限定走査の注記つき。
- `FGCIRCUIT23 AXIOMS`: 15 名、標準 axiom のみ。

Check の出力行は 6、棄却した mutant は計 39。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は条件付き（`hclL` ほか）。

### 28.7 次

(1) `hclL`: root の 2 つの子（`httpGetByte`、`tlpCplByte`）の実出力に対し、`closeInstsGM` の検査を評価する計算検査器（S1iChild の `noRawBelowB` の型）を run の結果に結ぶ。(2) `htop`、`hcd`（S1s／S1w2）、`HftRootLink`（S1y）。

## 29. S2a（Issue `sparkle-fg-circuit-pilot` の次の束）: `hclL` — 対象 run の閉じる成功を、根のデータと子の実出力から供給する

土台 `451e3467`（par/fgc-s1）。追加ファイル: `Tools/ShippingFGCircuitS2aClose.lean`、`Tests/Gen5/FGCircuitPilotCheck24.lean`（lakefile 登録は各 1 回）。S1w2（`ShippingFGCircuitS1w*`、Check17/22、§23）と S1y（`ShippingFGCircuitS1yLink`、Check19/21、§25/§27）、S1z のファイルには触れていない（S1z の定義・定理を import して使う）。新しい law・axiom・TRUSTED・sorry・native_decide はない。snapshot は供給にしていない。Issue の状態は変えていない。成果は**条件付き**で台帳に数えない。

### 29.1 手順 1: `some`/`none` を決める Bool 検査（完全な型）

`synthesizeMachineCertified translate logProf declName shape : MetaM (Option (Module × Design))`（`Sparkle/Compiler/Elab.lean`）は、`synthesizeMixedCertified` の結果 `(t, design)` に対し:

1. `Sparkle.IR.Machine.closeLets (nLets : Nat) (t : Module) : Option Module`。`nLets = 0` なら `some t`。それ以外は `packedWire? t.body`、`letOperands` が通り、かつ `aliases.all (wireWidth t.wires pa.2 == pa.1.ty.bitWidth && 0 < pa.1.ty.bitWidth && pa.1.name != "out" && pa.2 != "out" && !(writesOf t.body).contains pa.1.name) && core != "out" && OptCheck.assignmentOrderCheck body'`。`none` なら run は `none`（fallback）。
2. `shape.insts = []` なら `some (closeMachine …)`（検査なし）。`insts ≠ []` かつ `shape.instFields.isEmpty` なら `closeInstsM` → **`closeInsts`**、`instFields ≠ []` なら `closeInstsGM` → `closeInstsG`。**根 `synth_hftPcieOutByte` は `instFields = []` なので `closeInsts` の道**（kernel `decide`、`Check24`/ビルドで確認）。
3. `closeInstsM` は `sparkleChildSynth.get` で子の `synth c`（MetaM、子ごとの実行）を走らせ `children : List (Module × Design)` を得て `closeInsts nIn kI n portNames insts children (m, d)` を評価する。`closeInsts : Option (Module × Design)` が `none` になる条件: (a) `instStmt` の各検査（`mc ← moduleByName d'.modules child.1.name`、引数数・ポート名・出力の重複 …）、(b) `topoBody m'.body` が `none`、(c) `stmts.all isInst && decide portNames.Nodup && woCheck [] m'.body && woCheck [] body && isPermOf m'.body body && decide (seqOf m'.body = seqOf body) && decide (nextKeys m'.body).Nodup && decide (m'.body.filterMap stmtMemName).Nodup && linkedOk (moduleByName d'.modules) body && children.all (fun c => decide (moduleByName d'.modules c.1.name = some c.1) && c.2.modules.all (…)) && noInstOfB m.name body && d'.modules.all (fun g => noInstOfB m.name g.body) && kidsCombB d'.modules body`。
4. 子に依存するのは (a) と (c) の `linkedOk`、`children.all …`、`noInstOfB`、`kidsCombB`（子の module の形: `isAssign` だけ、入力から読む、出力が書かれる、入力が wire で接続される）。根だけに依存するのは `closeLets` と `topoBody`/`woCheck` 系の根の body の部分。

### 29.2 手順 2/3: 何を、どこまで証明したか

方針: 既存の `machineClosesAtA_of_gateKids'`（`ShippingCallsGatePinned`、cache pin 版。`closeLets` は `letsClose_of_data`、`closeInsts` は `callsPureP_of_gateKids`）を、根の `machineData` と**子の実出力**（`RealChildA`）に対して使う。子の側の前提 `RealChildA O c y → ChildIface c n y.1 y.2`（`ChildComb`、入力数、module 名 = `ofDecl c`、design の module が空）を、`RealChildA.run` が運ぶ**子自身の run**（`synthesizeCombinational c` が `(y.1, y.2)` を返す）から導く。

| 名前 | 内容 |
|---|---|
| `machineChild_ifaceA` | `machineChild_iface`（`ShippingMachineChildRun`）の `RealChildA` 境界への移植。機械 run は `machine_run_of_coreA`、閉じは `synthesizeMachineCertified_runsA`（`BodyStepC O`、`htr_of_tele`）。以降の証明は旧版そのまま |
| `machineChild_of_realA` | `RealChildA O c y` ⇒ `ChildIface c (…) y.1 y.2`（slotless な machine 子）。`RealChildA` の `adm/cache/synth/quiet/hr` から `JQC O (dv w) w` を作り、`MachineDefines.ctx` で反射を子の文脈に移す |
| `hft_kid_iface` | 根の 2 つの子（`httpGetByte`、`tlpCplByte`）の実出力に `ChildIface c (nkOf c)`。子のデータ検査（`ok`、`machine_body`、`gateCallsOk`、`lets ≠ 0`、`insts = []`、`slots = []`、出力が `out` 1 つ、`outTy`）は kernel `decide`。子の `MachineCloses` は生成済み `X.machine_closes` |
| `hft_gateCalls`、`hft_alias`、`hft_argsN`、`hft_kids_names`、`hft_noparent`、`hft_outs_head` | 根のデータの事実（kernel `decide +kernel`）: `gateCallsOk (kDOf …)`、`letsAliasOk`、呼び出しの引数数、呼び出し先が 2 つの子のどちらか、親の名前の呼び出しが無い、出力ポート名が `i` で始まらない |
| `hft_closesAtA` | 根の `MachineClosesAtA`（任意の `JQC O n` world（`1 ≤ n`）から機械 run は `none` を返さない）。`machineClosesAtA_of_gateKids'` ＋ 上の事実。`names_inj`/`parent_ne`/`instName_ne_of_head` は既存 |
| `hftCoreCloses_of_kids` | **`HftCoreCloses`（hclL）の導出**: `Start L mctx cctx w` と `HftKidsDefine` から。`JQC (0+1)` を core の連鎖（`coreHeadOff_jqcA`、`FramedA.constInfo/env`）で `w3`、`getEnv` の frame で `w8` へ運び（`coreOff_ranA` と同じ道）、`hft_closesAtA` を `w8` の機械 run に適用 |
| `HftFinalStmtOffLNK`、`synth_hftPcieOutByte_finalOffLNK`（`_Z/_Y/_X`） | S1z の最終文の `hclL` を `hkids : HftKidsDefine …` に替えたもの。**明示仮説 13**: `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hkids`（`hclL` は仮説でなくなった） |

標準 axiom のみ（`#print axioms` と Check24 AXIOMS）。`hdRun`（根の `MachineDefinesLinkedOff`）は `hftCoreCloses_of_kids` には要らない（根の閉じる成功は shape の反射ではなく `JQC` と子の事実から出る）。

### 29.3 残る名前付き仮説（impossible とは言わない）

```lean
/-- 2 つの被呼び出し宣言の反射（FG D.T-4、子の部分）。生成済み endpoint が各被呼び出し宣言について既に取っている `MachineDefines` の前提そのもの -/
def HftKidsDefine (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  MachineDefines mctx mref cctx cref ``Sparkle.IP.Net.HTTP.httpGetByte Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape ∧
  MachineDefines mctx mref cctx cref ``Sparkle.IP.Bus.PCIe.tlpCplByte Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.shape
```

- `MachineDefines` は「その run の環境で `getConstInfo c` / `getEnv` を読んだとき、`entryConst` が証明済みの shape を与える」ことの全 world 版（`ShippingMachineEntry`）。**閉じる成功そのものではない**（`hclL` の「`none` を返さない」は上で導出済み）。根では同じ種類の事実を `CheckedStart`/`hcell` から run 局所の `MachineDefinesLinkedOff` に落としていた（S1q）。子では、子の run は `RealChildA` の任意の admissible world で走るため、環境セルが子の run の world でも同じことを `JQC` は言わない。子の反射を `hreadH`/`hreadT`（`RootReader`）と `CellPrem` から子の run の world へ運ぶには、子の run の world の環境セルが開始 world と等しいことが要る（`RealChildA` は深さと cache しか持たない）。これは次の一歩（29.5）。
- 他の仮説（`HftRootLink`、`hcd`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws`/`Start`/`hr`）は S1z のまま。

### 29.4 Check24 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck24`、exit 0、931 jobs）

- `FGCIRCUIT24 SIGNATURES-A`: `HftKidsDefine` を独立に書いた `ExpKD`（2 つの (宣言名, shape)）と `isDefEq` で照合。**8 mutant 棄却**（名前の入れ替え、両方 `httpGetByte`、両方 `tlpCplByte`、別 shape（`counterLoop`）、根の shape、別の子、片方だけ、`True`）。
- `FGCIRCUIT24 SIGNATURES-B`: `hftCoreCloses_of_kids` の束縛（`mctx mref cctx cref L w hstart hk`）と使う定数（`Start`、`HftKidsDefine`、`HftCoreCloses`；`MachineCloses`/`MachineClosesAtA`/`CoreCloses` を前提に持たない）、`synth_hftPcieOutByte_finalOffLNK_Z` の 13 仮説・`hkids` が最後・`hclL` が無い・S1z の文と違う。**5 構造検査**。
- `FGCIRCUIT24 HYPS`（13 個）、`FGCIRCUIT24 CONTROLS`（小さな module 上の純粋検査 14 件を kernel で判定、ビルドが失敗すれば反転）: 組合せ的な子は `kidsCombB` を通る／順序回路の子・入力が配線されていない子・出力が書かれない子（別の子出力）・子が無いは落ちる／親の instance は `noInstOfB` で落ちる／`closeLets` は packed wire の無い module を拒否／根の `gateCallsOk` は本来の `nDecl` で成立し別の `nDecl` で不成立／別の引数数の読みは不成立。
- `FGCIRCUIT24 REMAINING`（1 行）: `hkids`。`FGCIRCUIT24 AXIOMS`: 15 名、標準 axiom のみ。

- `FGCIRCUIT24 SIGNATURES-C`（S2e で追加）: `hftCoreCloses_of_kids` と共通の最終文 `synth_hftPcieOutByte_finalOffLNK_Z` の**完全な型**を、独立に書いた期待型（`ExpCore`、`ExpFinalK`；world/ref/context、entry、carrier/obligation、出力、結論まで）と `isDefEq`（binder kind も）で照合。実型の正規形は 1 回だけ計算して使い回す（Check19 と同じ）。束縛名を維持したまま棄却した mutant: `hftCoreCloses_of_kids` 15（別の子・入れ替え・片方だけ・`True`、前提の欠落（Start／hk）、結論の欠落、別 root、別 shape、別 world、Start の world、別 context（Meta/Core）、別 ref（Meta/Core））、最終文 25（別 carrier／別 obligation／旧 carrier、旧 entry（診断版）、旧 artifact、前提 hcd／htop／hkids の欠落、別の子仮説 4 種、別 root／post root、別出力、hcd／結論を終了 world に、別 ref／context（各 2）、別 design、結論の片方または両方の欠落）。これで「最後の仮説だけ違う」ことを型全体で機械的に示す（SIGNATURES-B の構造検査は補助）。
- 注: 上の SIGNATURES-A の `HftKidsDefine` docstring の「run-local」は contexts（と ref セル）が固定という意味だけで、world は全称（子の run の world を含む全 world 前提）。

Check の出力行は 7、棄却した mutant は 8（SIGNATURES-A）＋15＋25（SIGNATURES-C）、制御は 14（CONTROLS）＋構造検査 5。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は条件付き（`hkids` ほか）。

### 29.5 次

(1) `HftKidsDefine`: 子の run の world でも環境セルが開始 world と同じであること（`RealChildA` に環境の frame を足すのではなく、`Start` からの run 局所の連鎖で `getConstInfo c`/`getEnv` の読みを `hreadH`/`hreadT` に結ぶ）。(2) `htop`、`hcd`（S1s／S1w2）、`HftRootLink`（S1y）。

### 29.6 ビルド環境の注記

`ulimit -v 20000000 … kjob lake build` は、この Pod では大きな既存モジュールのビルドで `failed to create thread`（Lean が確保する仮想メモリ）になるため、`timeout 1500 kjob lake build TARGET` のみで実行した。メモリの上限は kjob 側（`-m`）に任せた。

## 30. S2b（Issue `sparkle-fg-circuit-pilot` の次の束）: `Inhabited.mk` の狭い水準規則（族 `DS`）、共有を保つ評価の測定、閉包環境の関係 `Sh`

土台 `9e6556e9`。追加ファイル（既存は書き換えていない。lakefile は末尾に追記のみ）: `Tools/ShippingFGCircuitS2bShare.lean`（族 `DS`）、`Tools/ShippingFGCircuitS2bMachine.lean`（閉包環境の関係 `Sh`）、`Tools/ShippingFGCircuitS2bNative.lean`（共有を保つ評価器、生成器専用・非信頼）、`Tools/ShippingFGCircuitS2bGen.lean`（`DS` 向け生成器。S1wGen の複製に計測と cap を追加）、`Tools/ShippingFGCircuitS2bRun.lean`（`deriveRoot`、`derive_expr`、`derive_hft_ob`）、`Tools/ShippingFGCircuitS2bProbe.lean`（手動 probe。lakefile 外）、`Tests/Gen5/FGCircuitPilotCheck25.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない。Issue の状態は変えていない。成果は**条件付き**（`hcd` は**未導出**）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

### 30.1 (1) `inhMk` の水準規則（完了）

- 族 `DS` = `DW` の全コンストラクタ（`ds_fun` で関数性、axiom は propext/Classical.choice/Quot.sound のみ）で、`inhMk` だけを `Inhabited.mk.{u} T x` + 証拠 `hu : lvlNat u = some 1` に一般化した。`T : Type`、同じ env の ctor 事実 `env.find? Inhabited.mk = some (.ctorInfo cv)`、`t`/`x` の型付き導出は維持。他の宇宙一般化・新 TRUSTED はない。旧規則は `u = 1` の場合（`ds_inhMk_one`、`ds_default_of_mk`）。
- **訂正（裁定の文言からの差）**: 裁定は証拠を `u.normalize = Level.succ Level.zero` とした。`Lean.Level.normalize` は `opaque`（`#print` で確認）でカーネルが評価できないため証拠にならない。代わりに**自前の閉じた水準の評価器** `lvlNat`（`zero/succ/max/imax`、`param/mvar` は `none`）を定義し、証拠は `Eq.refl`。meta の正規化判定だけで証拠を省略していない。`lvlNat u = some 1` は「閉じた水準 `u` の値が 1」、すなわち Lean の水準同値で `1` と等しい水準であることの決定手続き。水準 `u` の定数と水準 `1` の定数が同じ宣言を指す意味の保存は、S1s と同じく Expr 書き換えの監査（定理ではない）。
- 対照（Check25 LEVEL-CONTROLS / CONTROLS）: `1`, `max 1 1`, `imax 1 1` は受理。`0`, `max 1 2`, `imax 1 0`, 水準パラメータ, mvar は棄却。別 ctor（`Option.some`）と、一般化していない `Inhabited.default.{max 1 1}` は生成器が導出できない（`deriveTerm` が失敗）。
- 小さい完全な導出（Check25 SMALL-DERIVE）: `default (Bool × Bool)`（`instInhabitedProd` の展開が `Inhabited.mk.{max 1 1}` を含む。S1w2 STOP-1 の再現）を生成器で導出し、`addDecl` でカーネル受理: 8 節点、導出項 288 DAG 節点、カーネル < 1 ms、標準 axiom のみ。旧 `DW` では導出できない。
- `DS` は S1s 以降の最終文の別の義務: `HftObCDS`、`CircCVS`（`circCVS_functional`）、`circCVS_hft_run`、`HftFinalStmtS := HftFinalStmtWith HftObCDS`（`HftFinalStmtW` と同形。`hcd : HftObCDS (envAt cref w)` は**引き続き仮説**）。`DW → DS` の全称な埋め込みは証明していない（`DW.inhMk` は `ds_inhMk_one` に写るが、全構成子の写像は未証明）。

### 30.2 (2) 膨張の経路（測定）

`hftRootValue` の導出で、`projStep`（弱頭正規化を 1 歩ずつ節点にする規則）が支配する。導出の節点の内訳（native 評価器、全体 60 509 節点）: `projStep` 54 321、`unf` 1 529、`beta` 921、`letE` 561、`projCtor` 415、`recIota` 267、`projRec` 233、`zeta` 10 ほか。膨張する式の形は `proj Prod.0 (((fun _cdoK => …) a₁) a₂) a₃)`（`Circuit.bind` の継続の多引数 β。引数 `a₁ a₂ a₃` は構造体値の `have` と do 記法の束縛を含む）。最大の構造体引数: **木 17 055 208 節点 / DAG 4 598 節点**（約 3 700 倍）。つまり膨張は**式の木**の大きさで、DAG は小さい。旧評価器 `instE`（S1mCD、構造再帰で毎回木を作り直す）が各ステップで木を実体化し、memo に全ステップ分が残るため、28 GB を使い切っていた（§23.6 の「導出項も同じ規模」は未測定の推定で、下記のとおり導出項側は DAG 共有される）。

### 30.3 比較: 旧評価器 vs 共有を保つ評価器（`Expr.instantiate1`、生成器側のみ。カーネルは同じ `Eq.refl` で再検査）

小さい部分（cap 1 200 節点。OOM 直前までの同じ連鎖。`Tools/ShippingFGCircuitS2bProbe.lean`、`ulimit -v 24000000`）:

| | 旧 `instE`（木） | 新 `instantiate1`（DAG） |
|---|---|---|
| 同じ連鎖（節点数 / 最大構造体引数） | 1 201 / 木 17 055 208・DAG 4 598 | 1 201 / 同一 |
| 生成器の時間 | 37.6 s | 1.4 s |
| ピーク RSS | 9.5 GB | 2.2 GB（import 基底を含む） |
| 最大ステップのカーネル検査（`Eq.refl`、`dw_projStep_t`、DAG 4 598 の x） | 1.0 s、導出項 DAG 9 911 節点、受理 | 同じ項（生成器の結果は構造一致） |
| cap 6 000 / 12 000 | （旧は 6 000 で 41 s、29k 付近で OOM） | 9.6 s・2.5 GB / 17.6 s・2.7 GB |

全体（root、cap なし、native）: **60 509 節点、128 s、ピーク 4.2 GB、完走**（旧は 28 GB で bad_alloc）。完走した probe の止まりは 2 種: `Signal.mk` が値の頭（3 引数、`DS` に規則なし）、`Bool.false`（ctor 値の規則なし）。導出項の全体は止まりがあるので未生成。`Check25 SHARE-LADDER` は同じ現象の小規模再現（`let x := E; Prod.mk x x` の梯子 k = 16: `instE` は木 524 281 節点、`instantiate1` の結果は同じ式で DAG 38 節点）。

**カーネル側の見積り（測定ではなく外挿）**: 1 ステップのカーネル検査は式の DAG 全体を走る（4 598 節点で 1.0 s）。完走した probe の完了ステップの DAG 節点数の合計は 3.98×10⁷。同じ係数（約 0.2 ms / 節点）なら約 2〜2.5 時間のカーネル時間になる。したがって**生成器の共有だけでは足りず**（メモリは解決）、1 ステップが式全体を再走査する設計自体を変える必要がある。これが (2a) の動機。

### 30.4 決定: (2a) を継続（閉包環境）。(2b)/(2c) への切替はしない。実装は関係と関数性まで

`Tools/ShippingFGCircuitS2bMachine.lean` に**閉包環境つきの弱頭評価の関係 `Sh`**（完全な型つき）を置き、関数性 `sh_fun`（標準 axiom のみ）を証明した。要点:

- 環境の項 `Ent.val (en : Entry)`（既存の値で表せるものはそのまま）と `Ent.clo e ρ`（未評価の式 `e` と**捕捉した環境** `ρ`。de Bruijn 参照、複製なし）。`Sh env ρ e sp hn`: 環境 `ρ` の式 `e` を閉包の spine `sp` に適用し、頭正規形 `hn`（フィールドが閉包の ctor、または停止した原始頭 + 閉包引数）に達する。
- 規則: `app`（引数は評価せず閉包として積む = call-by-name。**call-by-value ではない**）、`lam`（先頭の spine 閉包を束縛）、`letZ`（`coreHead A = false` の let。`DW.zeta` が代入で扱った場合。値は閉包）、`bvarC`（閉包を辿る）、`unf`（定義の本体は閉じているので空の環境で展開）、`ctor`/`prim`/`proj`（ctor のフィールド閉包を取り出して続ける）。**代入が無いので 1 ステップの大きさは局所的**で、同じ閉包は参照で共有される（call-by-need はこの共有を導出側の名前つき補題/メモ化に載せる。`derive` の `memo` が (環境, 式) で既にそうしている）。
- 古い `zeta`/`beta`/`projStep` との重なりは、新族では**古い規則を取り除く**ことで排他（一致補題を要さない）。`DS` に載せる橋渡し規則（頭が `prim` で止まり、spine が共通環境 `ρ₀` の `args.map (clo · ρ₀)` のとき `DS ρ₀ (mkApps (const c ls) args) r` を使う、`bvarClo`、`viaSh`）の設計は上記だが**未実装**。パターンを見る原始規則（`sigAddBV` の型引数の形など）は、共通環境の場合に限って元の規則をそのまま使う。
- 未実装（正直な記録）: (a) `Sh` の `List.rec` 規則（`recIota`/`projRec` の置換。spine の再帰呼出しは `[t, consc, nilc, mot, a0]` を環境とする閉包 `List.rec #4 #3 #2 #1 #0`）、(b) 橋渡し規則を持つ族と `dt_fun`、(c) 閉包環境を作る生成器（環境項は DAG 共有、名前つき定義）、(d) root の導出。したがって **`hcd` は導出していない**。(b)(c) は新しい大きい step ではなく、`Sh` の関数性の上に積む（生成器の `memo` と `Look` の記録はそのまま使える）。
- (2b)/(2c): 上の比較は生成器のメモリが主因でカーネル時間が副因という結果で、定義本体と意味の等式を持つ再利用補題 (2b) は「ステップ数」自体を減らす補助として有望だが、今回は実装していない。(2c) は使っていない（DW の Expr 添字は置き換えていない）。

### 30.5 Check25 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck25`、exit 0、info 8 行）

AXIOMS（ds_fun 他）/ LEVEL-CONTROLS / SMALL-DERIVE（数値行 + ok の 2 行）/ SMALL-AXIOMS / CONTROLS / SHARE-LADDER / FAIL-CLOSED。

### 30.6 証明したもの / 名前付き仮説・未供給 / 数え方

- 証明: `ds_fun`/`cds_fun`/`tds_fun`/`cds_eq`、`circCVS_functional`、`ds_inhMk_one`、`ds_default_of_mk`、`sh_fun`、表版規則 `ds_*_t`（`ds_inhMk_t` は水準証拠つき）、`lvlNat` の対照。すべて標準 axiom のみ。
- 名前付き仮説（未供給）: `HftObCDS`（`hcd`）、`EnvDefs`/`EnvCtors`/`RecFact`、`hclL`、`HftRootLink`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws/Start/hr`。Expr 書き換えの意味保存（水準の同値を含む）は監査。`bundle2` の unsafe 実装。
- 次: `Sh` の `List.rec` 規則と `DS` への橋渡し（`DT` 族）、閉包環境つき生成器、`Signal.mk` と `Bool.false` の規則、その後 `hftRootValue` の型付き導出。


## 31. S2c（Issue `sparkle-fg-circuit-pilot` の次の束）: `HftRootLink` の (a) 呼び出し引数と (b) fused 状態の endpoint 証拠、分割した証明

土台 `f30cb9fe`（S1y）。Issue の状態は変えていない。S2b の領域（`Tools/ShippingFGCircuitS2bShare.lean`、Check25、§30）には触れていない。TRUSTED・axiom・sorry・native_decide・新しい law はない。

### 31.1 手順 1: (a)/(b) の事実の完全な型（先に固定）

全て `synth_hftPcieOutByte`（`Tools/ShippingFGCircuitS1kRoot.lean`、公開コピー）の鎖（`Tele`）endpoint に対する。`L := synth_hftPcieOutByte.machineInners`（`TeleT`）、`d := synth_hftPcieOutByte.machineData`、`teleState L hss i bools bits S₂ Ss t := castSS hss (L.fstate i bools bits (S₂.val t) (Tele.valsOf (L.at i bools bits) Ss t))`（融合状態、`d.ss = [bits 6] ++ L.sss`）。`callArgsOf d k := ((d.shape.insts.map (·.2.1))[k]?).getD []`（`Gen5Sem.callArgs` と同じ並び）。`callArgVals d bools bits t x args := args.map fun l => ((d.ls[l]?).map fun lt => enc lt.1 (eval (typedVal … bools bits t x の b/v) lt.2)).getD 0`（`valsOf (lsrcAt d bools bits S) args t` の `x = S.val t` での値）。

**(a) 呼び出しごと `machine_arg_k`（k = 0, 1）**:
```
∀ (i : Unit) bools bits (S : Signal defaultDomain (HList (tys [bits 6]))) (Ss : (L.at i bools bits).Sigs) (t : Nat),
  callArgVals d bools (extPre_k i bools bits S Ss) t (teleState L hss i bools bits S Ss t) (callArgsOf d k) = [Lean 側の引数の値の列]
```
`extPre_0 = bits`、`extPre_1 = extendBits bits 5 8 (machineCall_0 i bools bits S Ss)`（= `machineExt` の最初の 1 呼び出し分）。右辺は呼び出し `k` の Lean の引数 Signal の `BitVec.toNat (… .val t)`（Bool なら `encodeBool`）の列: k = 0 は `[(regsOf (tys [bits 6]) S).fst.fst.val t].toNat`、k = 1 は `[(bits 4 16).val t, Ss.2.1 の第 5/6/7/8/4 レジスタ].toNat`（`tlpCplByte` の 6 引数）。**意味**: ExtStage の段 `k` が `lsrcAt` で得る引数の値（`ls` 項の評価）は、Lean の呼び出しが渡す引数 Signal の値。

**(b) 融合状態 `machine_states`**（`Tools.ShippingMachineTeleStates.machine_states_of_tele_ext` を endpoint の事実で埋めたもの）:
```
∀ (i : Unit) bools bits, ∃ (S₂ : Signal defaultDomain (HList (tys [bits 6]))) (Ss : (L.at i bools bits).Sigs),
  teleState L hss i bools bits S₂ Ss 0 = castSS hss (happendT [bits 6] L.sss machineInits L.initsT) ∧
  (∀ t, teleState … (t+1) = evalTerms (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (machineExt i bools bits S₂ Ss) t (teleState … t) の b/v) d.nexts) ∧
  ∀ t, (machineSource i bools bits).map (fun f => f t) = d.outs.map fun o => enc o.1 (eval (同じ typedVal の b/v) o.2)
```
**意味**: 初期値（1 つ目）、遷移（2 つ目）、観測（3 つ目、`machineSource` = 宣言の観測）が、`GenIn` の `d.ss` の状態列と同じ形（`typedVal`/`evalTerms`）で、Lean 側の状態 Signal `(S₂, Ss)` と Lean の拡張 `machineExt` について成り立つ。

### 31.2 手順 2: endpoint 生成器の変更（小さな commit）

`Tools/ShippingMachineCommand.lean`（鎖 endpoint の経路 `nestedProof` と `generateCore`）に **新しい `addDecl` の定理だけ**を足した（既存の def・定理・生成される IR/SV は変えない）:
- `machine_arg_k`（k < `insts.length`）: 呼び出し `k` の引数 wire の評価 = Lean の引数 Signal の値、`reflProof` で kernel が `Eq.refl` を検査（失敗しても endpoint は元のまま: `try`/`setEnv`）。
- `machine_states`: 新しい一般定理 `machine_states_of_tele_ext`（`Tools/ShippingMachineTeleStates.lean`、`machine_trace_of_tele_ext` と同じ前提、結論はその証明が内部で作る状態列）を、`machine_sound` を作るのと同じ引数で適用（`pPre.getAppArgs`）。
- 新しい補助 `Tools/ShippingMachineTeleStates.lean`: `callArgVals`、`callArgsOf`、`teleState`、`machine_states_of_tele_ext`（axiom は標準のみ）。

`kjob lake build Tools.ShippingFGCircuitS1kRoot`（exit 0）で `synth_hftPcieOutByte.machine_arg_0/1`、`machine_states` が生成された（`SPARKLE_MACHINE_PROGRESS` の記録に `not generated` なし）。

### 31.3 手順 3: 証明の分割（`Tools/ShippingFGCircuitS2cLink.lean`）

`HftRootLink` を (a) 呼び出しごと、(b) fused 状態、に次のように分けて使う。

- **型の一致（`ExtStage` 対 Lean の拡張）— 証明済み**: 2 つの入力族は、入力位置 `p < nIn` の宣言された sort（`d.K p`）で一致すれば、`typedVal` が（sort を見て）全位置で一致し、整形な項は同じ値になる（`partial_tagree`、`typedVal_tagree`、`eval_tagree`、`nexts_tagree`、`outs_tagree`、`callArgVals_tagree`）。`ExtStage` は呼び出し結果を位置 `kD + k` の**全ての幅**に置く（`withCall`）が、Lean の `machineExt`（`extendBits`）はその呼び出しの幅にだけ置く。データの項は宣言された幅でしか読まないので、一致するのは宣言された sort だけでよい（既存の `typedVal_let_agree` は全幅の一致を要求するので使えない。新しく証明した）。
- **子の観測は入力の（その時刻・宣言された sort の）値だけで決まる — 証明済み**: `kid_pw`（子の `machine_result` と上の一致から）、`http_pw`、`tlp_pw`（`httpGetByte`/`tlpCplByte` の Lean の呼び出しの値は、引数の Signal のその時刻の値だけで決まる）。
- **1 回の呼び出し — 証明済み**: `calleeOut_eq`、`callOut_bits`（`ExtStage` の段 `k` は位置 `kD + k` に `BitVec.ofNat n (calleeOut …)` を置き、他の位置は変えない）、`calleeOut_http`/`calleeOut_tlp`（(a) の `machine_arg_k` を使うと、子に渡る `valsOf (lsrcAt …)` は引数 Signal の `toNat`、子の観測は Lean の呼び出しの値）、`stage1`/`stage2`（段 1, 2 で宣言された sort の位置が Lean の拡張 `extendBits (extendBits bits 5 8 c₀) 6 8 c₁` と一致）。
- **初期状態の一意性 — 証明済み**: `inits_unique`（`initOk` を満たす状態は 1 つ。`GenIn` の `inits` と `machine_inits` の状態が一致）。
- **組み立て `hftRootLink`**: `machine_states` の `S₂, Ss` から Lean の融合状態列 `sg t := teleState … t` を取り、`S.val t = sg t` を `t` の帰納法で示す（初期値: `inits_unique`、遷移: `hrec` と `machine_states` の遷移の右辺が `nexts_tagree` で一致）。観測は `machine_states` の第 3 成分（`machineSource` = `monoObs`）と `outs_tagree`。

### 31.4 出力比較（IR/SV 不変）

生成器の変更は新しい `addDecl` の定理（と補助 def `machineCall_k` は既存）だけ。`#synthesize`/`#synthesizeVerilog` は `Tools/*` を import しない（`Tests/Gen5/FGCircuitPilotCompare15.lean` の import は `Sparkle`・`Tests.SignalLoopTest`・`IP.*` のみ）。`git diff f30cb9fe..HEAD -- Sparkle IP Tests/SignalLoopTest.lean Tests/Gen5/FGCircuitPilotCompare15.lean` は空（変更は `Tools/ShippingMachineCommand.lean`・`Tools/ShippingMachineTeleStates.lean`・`Tools/ShippingFGCircuitS2cLink.lean`・Check21・docs・lakefile のみ）。`kjob lake build Tests.Gen5.FGCircuitPilotCompare15`（exit 0、232 jobs）。**前後のビルドログのテキスト比較はしていない**（import の分離による論証。S0 の基準線は coder が再実行する）。

### 31.5 結果（正直に）: `HftRootLink` は**証明が完了していない**
- **証明した部品**（`Tools/ShippingFGCircuitS2cLink.lean`、`kjob lake build` exit 0、axiom は標準のみ）: `partial_tagree`/`typedVal_tagree`/`eval_tagree`/`nexts_tagree`/`outs_tagree`/`callArgVals_tagree`（sort 付き一致）、`inits_unique`、`kid_pw`/`http_pw`/`tlp_pw`、`calleeOut_eq`/`callOut_bits`/`calleeOut_http`/`calleeOut_tlp`、`stage1`/`stage2`（`ExtStage hftKids` の段 1, 2 が `machine_arg_0/1` を使って Lean の拡張と宣言された sort で一致）。さらに組み立ての途中（Lean 状態列 `sg t` に対する `ExtStage` 族の一致 `hext`、`typedVal` の一致 `hagree`、状態列 `S.val t = sg t` の帰納 `hSg`）は通った（`docs/FG-CIRCUIT-PILOT-S2c-hftRootLink-draft.lean.txt` に最終版の下書きを残す。lake には載せていない）。
- **閉じていない 1 点**: 最後の観測の式 `monoObs … = outs（ExtStage 族の typedVal）`（`machine_states` の第 3 成分から `outs_tagree` で移す）は、定理全体の組み立てで `whnf` が heartbeat 上限（200000、8000000 でも 14 分で）に達した。部分ごと（`outs_tagree` の適用、`monoObs_root`）は通るので、不可能ではなく、巨大な `machineInners`/`machineData` を含む項の定義的同一視の経路の問題と見る（次は `HftRootLink` の結論部だけを独立補題にして、`TVal` を抽象変数にして呼ぶ）。したがって `synth_hftPcieOutByte_finalOffL` に `hlink` を落とした版は**作っていない**（`hlink` は名前付き仮説のまま、`HftFinalStmtOffL` の 13 個）。
- `machine_states` の型を独立文面と `isDefEq` で照合する試みも heartbeat 上限に達したため Check21 には入れていない（`machine_arg_0/1` は照合した）。
- 名前付き仮説: `HftRootLink` のみ（S1u と同じ）。新しい law/TRUSTED/sorry/native_decide/axiom はない。

### 31.6 Check21 の出力
`kjob lake build Tests.Gen5.FGCircuitPilotCheck21`（exit 0）。`FGCIRCUIT21 SIGNATURES`: `machine_arg_0`、`machine_arg_1` は独立文面と `isDefEq`（default）で一致、mutant（別の呼び出し・先行呼び出しの拡張欠落・引数の欠落）3/3 棄却（`instances` 透過度）。`FGCIRCUIT21 AXIOMS`: 12 名、標準 axiom のみ。
## 32. S2d（Issue `sparkle-fg-circuit-pilot` の次の束）: `hkids` の run 局所化 — 子の run の開始 world の環境の 2 つの事実

土台 `b7984ea2`（par/fgc-s1）。追加ファイル: `Tools/ShippingFGCircuitS2dKids.lean`、`Tests/Gen5/FGCircuitPilotCheck26.lean`（lakefile 登録は各 1 回）。S2a（§29）・S2b・S2c のファイルには触れていない（S2a の定義・定理を import して使う）。新しい law・axiom・TRUSTED・sorry・native_decide はない。Issue の状態は変えていない。成果は**条件付き**で台帳に数えない。

### 32.1 何が `HftKidsDefine` の代わりに要るか（完全な型を先に）

`HftKidsDefine`（§29.3）は 2 つの被呼び出し宣言の `MachineDefines`（全 world、子の run の `mctx cctx` で）。子の run は `RealChildA.run` の `adm/cache/synth/quiet/hr`（深さと cache だけ）で任意の admissible world で走り、環境セル `envAt cref w` は持たない。根では `CheckedStart`（`ReadsAt env₀ cref w`）と `HeadAt`/`GetEnvProfileAt` で `MachineDefinesLinkedOff` を run 局所に作った（S1q）。子も同じ形で作れるが、**子の run の開始 world の環境が開始 world のそれと一致すること**は `Laws` からも `CellPrem` からも導けない（`quiet` は不透明、class-D の `whnf`/`inferType` 等は env frame を持たない、§21）。次の 2 つに分けて名前を付けた。**「run 局所」「根から子までの連鎖で供給」という言い方は不正確だった（S2h の訂正、§32.7）**: `KidStartEnv` は根の開始 world も、到達関係も、cache の履歴への所属条件も持たず、`RealChildA.run` の前件（`adm/cache/synth/quiet/hr`）を満たす**あらゆる**子の run の開始 world `w` が同じ `e` を読む、と仮定する全称命題である（過去の run にも及ぶ。cache hit の元の run の環境を追跡・証明するものではない）。

```lean
/-- NAMED HYPOTHESIS (FG D.T-4k) -/
def KidStartEnv (O : RefLawsAOps MkRefd mref cref) (e : Environment) (c : Name) : Prop :=
  ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w' : Void IO.RealWorld) (y : Res),
    AdmCtx O.quiet mctx' cctx' → (∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r') →
    sv w = some synthesizeChild → O.quiet w →
    RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w y w' →
    ReadsAt e cref w ∧ GetEnvProfileAt mctx' mref cctx' cref w

def HftKidsStartEnv O e := KidStartEnv O e hftHttp ∧ KidStartEnv O e hftTlp     -- FG D.T-4k
def HftKidsGates e := EntryGates e hftHttp ∧ EntryGates e hftTlp                 -- FG D.T-4g
```

- (A) `ReadsAt e cref w`: 子の開始 world の Core 環境は `e = envAt cref w₀`（開始 world）と一致（find の包含と `instancePredicate/userInliner/structEnv` の等式）。`ReadsAt` は環境全体の等式より狭いが、**範囲は上記の全称のまま**（根の run の frame だけでは供給できない: 無関係な run まで含むため）。
- (B) `GetEnvProfileAt mctx' … w`: 子の `synthesizeChild` → `synthesizeCombinational` が `coreHead` で読む `IO.getEnv "SPARKLE_PROFILE"` は `none` を返し環境を変えない（根の S1o と同じ profile 無効の枝。診断入口は取らない）。
- `HftKidsGates e`: 2 つの被呼び出し宣言の entry 定数の 2 つの拒否（`certifiedShape?`/`mixedCertifiedShape?` = `none`）。根の `hchk` の gate 部に当たる。`machineShape?` の部分は既存の `hreadH`/`hreadT`（`RootReader`）がそのまま運ぶ。
- 全 world の `MachineDefines` は消えた。`HftKidsStartEnv`/`HftKidsGates` から `MachineDefines`/`HftKidsDefine`/`MachineCloses` は、Check26 の reach 走査（`Tools`/`Sparkle` 下の `defnInfo` の型と値を辿る。帰納型の構成子と定理は展開しない）の範囲では到達されない。依存閉包全体・全 world 前提についての不在は主張しない。`KidStartEnv` は shape も閉じる成功も言わない。ただし**単に `MachineDefines` を弱めたものでもない**: profile 無効（`GetEnvProfileAt`）という条件を新たに要求する（`synthesizeCombinational` の profile 無効の枝を通る条件であり、「診断入口を通らない」という説明は不正確）。

### 32.2 証明したこと

| 名前 | 内容 |
|---|---|
| `machineChild_ifaceK` | `machineChild_ifaceA` の `entry : MachineDefines` を「この子の core run の開始 world `w` だけに対する `MachineDefinesLinked`」に替えたもの。機械 run は `machine_run_of_coreC`（run 自身の `core_chain`）。それ以外の証明は `machineChild_ifaceA` と同一（コピー） |
| `machineDefinesLinked_of_readerE` | `ReadsAt e cref w`、`HeadAt X w`、`GetEnvFrame`、`RootReader lvl e X dd`、`EntryGates e X` から `MachineDefinesLinked … X dd.shape w M D w'`。`machineDefinesLinked_of_headAt` と同じ証明だが、定数の lookup は run 自身の `getConstInfo`（`ci_of_readsAt`）から取り、`RootInEnv` を要さない |
| `machineChild_of_realK` | `machineChild_of_realA` の `entry` を `KidStartEnv` ＋ reader ＋ gates ＋ `CellPrem` に替えたもの。`HeadAt` は `headAt_of_profileOff`（`CellPrem` ＋ (B)）、`GetEnvFrame` は `getEnvFrame_of_cellPrem` |
| `hft_kid_ifaceK`、`hft_closesAtK`、`hftCoreCloses_of_kidsK` | S2a の `hft_kid_iface`、`hft_closesAtA`、`hftCoreCloses_of_kids` の `hk : HftKidsDefine` を `hcell hrH hrT hg hke` に替えたもの |
| `HftFinalStmtOffLNKK`、`synth_hftPcieOutByte_finalOffLNKK`（`_Z/_Y/_X`） | S2a の最終文の `hkids` を `hkenv : HftKidsStartEnv L.O (envAt cref w)`、`hkgates : HftKidsGates (envAt cref w)` に替えたもの |

**binder 一覧（`finalOffLNKK_Z`、明示仮説 14）**: `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hkenv hkgates`（S2a は 13 個で最後が `hkids`）。`hcell`（`CellPrem`）、`hreadH`/`hreadT` は既存の仮説で、子のために新しく足したのは `hkenv`（D.T-4k）と `hkgates`（D.T-4g）だけ。標準 axiom のみ（`#print axioms` と Check26 AXIOMS）。

### 32.3 残る名前付き仮説（impossible とは言わない）

`hkenv`（FG D.T-4k: 子の開始 world の環境の `ReadsAt` と profile 無効）、`hkgates`（FG D.T-4g: 子の entry 定数の gate 2 つ、環境 `envAt cref w` 上の計算）、および S2a から変わらない `HftRootLink`（S2c）、`hcd`（S2b）、`htop`、`hreadH`/`hreadT`、`hchk`、`CellPrem`、`Laws`/`Start`/`hr`。`hkgates` は `entryGatesB` と同種の評価検査（MetaM）で、kernel では計算していない。`hkenv` の (A) は `QuietStrength`（強めた `L'`）の構成が `diag` と `RefLawsATele` の `telescope` を含まないため `Laws` から導いていない（`frameQ_plus` 等は class-D 行を除く、S1i）。(A) を `RealChildA` の world の連鎖から導くには、根の機械 run 全体の環境 frame（class-D の `whnf` 等を含む）が要る。

### 32.4 Check26 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck26`、exit 0、932 jobs）

- `FGCIRCUIT26 SIGNATURES-A`: `KidStartEnv` を独立に書いた `ExpKS` と `isDefEq` で照合。**8 mutant 棄却**（ReadsAt のみ、profile のみ、ReadsAt を終了 world で、profile を終了 world で、`ReadsAt` の代わりに環境等式、cache 前件を落とす、profile 無効入口 `synthesizeCombinationalOff`、`True`）。
- `FGCIRCUIT26 SIGNATURES-B`: `hftCoreCloses_of_kidsK` の binder と使う定数、`finalOffLNKK_Z` の 14 仮説（`hkids`/`hclL` が無い、`hkenv`/`hkgates` が最後、`MachineDefines`/`HftKidsDefine`/`MachineCloses` が新仮説から到達不能、S2a の文と違う）。**8 構造検査**。`FGCIRCUIT26 HYPS`（14 個）。
- `FGCIRCUIT26 CONTROLS`: kernel 判定 6 件（`hftHttp`/`hftTlp` が 2 つの被呼び出し宣言、互いに異なり根とも異なる、入れ替えは不成立）。
- `FGCIRCUIT26 REMAINING`（2 行: `hkenv`、`hkgates`）。`FGCIRCUIT26 AXIOMS`: 10 名、標準 axiom のみ。

Check の出力行は 8（SIGNATURES-A 1、SIGNATURES-B 1、HYPS 1、CONTROLS 1、REMAINING 2、AXIOMS 1 + 構造検査 8 / mutant 8 / 制御 6）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は条件付き。

### 32.5 次

(1) `hkgates`: 2 つの被呼び出し宣言の gate 検査（`entryGatesB` 相当）を `envAt cref w` 上で評価する Check（FG D.T-4g）。(2) `hkenv` (A): `RealChildA` の開始 world の環境が根の開始 world のそれと一致すること（機械 run の class-D 行の環境 frame、または run 局所の world の連鎖）、(B): 子の `synthesizeCombinational` の profile lookup が `none`。(3) `htop`、`hcd`（S2b）、`HftRootLink`（S2c）。

### 32.7 S2h による訂正（レビュアー裁定）

1. `KidStartEnv`（`hkenv`）は、`RealChildA` の前件を満たすすべての子の run の開始 world が同じ `e` を読むという全称命題で、根の開始 world・到達関係・cache 履歴への所属条件を持たない。したがって「run 局所」でも「根から子までの frame で供給される」でもない。供給の道は §34 の履歴つき述語（cache の初期化、miss で保存する子の run の読み、hit での取り出し）に移した。`KidStartEnv` 版の補題（`machineChild_of_realK` など）は条件つきの部品として残してある。
2. Check26 の SIGNATURES-B は旧 Check24 と同じく束縛名と定数の出現だけを見ていたので、SIGNATURES-C（`machineDefinesLinked_of_readerE`、`hftCoreCloses_of_kidsK`、`synth_hftPcieOutByte_finalOffLNKK_Z` の完全な型を独立に書いた期待型と照合）を足した（§34.5）。
3. reach 走査は `Tools`/`Sparkle` 下の `defnInfo` の型と値を辿るだけで、帰納型の構成子と定理は展開しない。「3 つの名前に到達しない」はこの走査の範囲に限る。

### 32.6 ビルド環境の注記

`timeout 1500 kjob lake build TARGET` のみ（`ulimit -v` なし）。`Tools.ShippingFGCircuitS2dKids` は約 3 分（初回、S2a の import 込み）。

## 33. S2g（Issue `sparkle-fg-circuit-pilot` の次の束）: `hkgates` — 2 つの被呼び出し宣言の gate を閉じた宣言と有限個の環境問い合わせに還元

土台 `6bfe8328`（par/fgc-s1）。追加ファイル（既存の定理は書き換えていない。lakefile 登録 2 件）: `Tools/ShippingFGCircuitS2gGates.lean`、`Tests/Gen5/FGCircuitPilotCheck27.lean`。sorry・axiom・native_decide・TRUSTED・新しい law はない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で、approved/done ではない。

### 33.1 完全な型（先に固定。Check27 が独立に書いた文面と `isDefEq`）

```
structure KidGateFacts (env : Environment) (X : Name) (T V Vi : Lean.Expr) : Prop where
  root   : ∃ d : DefinitionVal, RootInEnv env X T V d
  ui_val : userInliner env V = Vi
  ui_ty  : userInliner env T = T
  ip_val : instancePredicate env (peeled V) = false
  ip_inl : instancePredicate env (peeled Vi) = false

def HftKidsGateFacts (e : Environment) : Prop :=
  KidGateFacts e hftHttp httpType httpValue httpInlValue ∧ KidGateFacts e hftTlp tlpType tlpValue tlpInlValue
```

`T`/`V` は被呼び出し宣言（`httpGetByte`、`tlpCplByte`）の型/値の**閉じた `Lean.Expr` の quote**（`quote_decl%`、`exprToE`）、`Vi` は `userInliner env V` の quote（`arbiterInlinedValue` と同じ、この build の環境の **SNAPSHOT**。それが環境の inliner の返す値であるという事実は名前付き仮説 `ui_val`）。`peeled e` は `mixedGatePeel` で剥がした本体（インスタンス述語が最初に問われる点）。

### 33.2 証明できたもの（標準 axiom のみ。`http_gates_V`/`tlp_gates_Vi` は propext のみ）

| 名前 | 内容 |
|---|---|
| `http_gates_V`、`http_gates_Vi`、`tlp_gates_V`、`tlp_gates_Vi` | 閉じた宣言（型 `T`、値 `V` または inliner 後の `Vi`）上で `certifiedShape?` と `mixedCertifiedShape?` が `none`。**kernel 評価**（`with_unfolding_all rfl`）。インスタンス述語 `ip` は抽象のままで、証明が必要とする `ip` に関する仮説は `ip (peeled V) = false` のその 1 点だけである（証明が通ったことが根拠。「他の点は問われない」という主張ではない） |
| `entryGates_of_two` | `RootInEnv`、inliner の 2 事実、「宣言上の gate」と「inliner 後の宣言上の gate」から `EntryGates env X`。`entryConst` はどちらを返しても gate が通る（`machineShape?` の評価は不要。S1l の `entryOfDecl_inl` の `hs` を要さない） |
| `httpGate_of_facts`、`tlpGate_of_facts`、`hftKidsGates_of_facts` | `KidGateFacts` から `EntryGates`、`HftKidsGateFacts e → HftKidsGates e` |
| `HftFinalStmtOffLNKKG`、`synth_hftPcieOutByte_finalOffLNKKG`（`_Z/_Y/_X`） | S2d の最終文の `hkgates : HftKidsGates (envAt cref w)` を `hkgfacts : HftKidsGateFacts (envAt cref w)` に替えたもの |

**binder 一覧（`finalOffLNKKG_Z`、明示仮説 14）**: `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hkenv hkgfacts`（S2d の `hkgates` だけが `hkgfacts` に替わった。個数は同じ）。`hreadH`/`hreadT`（`RootReader`、`machineShape?`/`dataOfAt` の部分）は既存の仮説のまま。

### 33.3 残る名前付き仮説（impossible とは言わない）

`hkgfacts : HftKidsGateFacts (envAt cref w)`（FG D.T-4g）: 被呼び出し 2 つ × 5 事実 = **10 の環境の事実**（`envAt cref w` の 1 つの環境に対し、各事実は 1 つの閉じた項または 1 つの名前での問い合わせ）。all-world の law ではなく、`ReadsAt`/`Start`/`CheckedStart` は含まない。Check27 が build の環境で 10 事実すべてを観測（MetaM、供給ではない）。残りは S2d から変わらない `hkenv`（D.T-4k）、`HftRootLink`（S2c）、`hcd`（S2b）、`htop`、`hreadH`/`hreadT`、`hchk`、`CellPrem`、`Laws`/`Start`/`hr`。

### 33.4 Check27 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck27`、exit 0。**933 jobs は S2g の作業中のビルドの job 数**。提出 SHA を再検証したビルドは別の実行で **934 jobs**（レビュアーの再検証の数。S2k で区別を明記）。二つを同じ実行として読まない）

- `FGCIRCUIT27 SIGNATURES-A`: `KidGateFacts` の構成子の型と `HftKidsGateFacts` を独立に書いた `ExpKGF`/`ExpHK` と照合。**13 mutant 棄却**（点を値全体に、inliner 後の点を落とす、root を落とす、inliner の型の事実を落とす、値を宣言に結ばない、quote の入れ替え、名前の入れ替え、片方の被呼び出しを 2 回、片方のみ、値全体の点、`True`）。
- `FGCIRCUIT27 SIGNATURES-B`: `finalOffLNKKG_Z` の 14 仮説、`hkgfacts` が最後、`hkenv`/`hreadH`/`hreadT` は不変、`MachineDefines`/`HftKidsDefine`/`MachineCloses`/`Start`/`ReadsAt`/`CheckedStart` が `hkgfacts` から到達不能、S2d の文と違う。**17 構造検査**。`FGCIRCUIT27 HYPS`（14 個）。
- `FGCIRCUIT27 QUOTES`: 4 つの quote が宣言の型/値と `Expr.equal`、http ≠ tlp、10 事実が環境点 1（この build）と点 2（無関係な宣言を足した後）の両方で成立（**25 検査**、観測）。
- `FGCIRCUIT27 CONTROLS`（7 件）: 入れ替えた被呼び出しは事実を破る（root が両方向で偽）、gate が通らない宣言（`gateFail`: `certifiedShape?` が `some`）の検出、インスタンス述語が問い合わせに敏感（`kidWrap`: 本物の述語では mixed gate が `some`、常に false では `none`）、本物の entry 定数は両方 gate が通る。
- `FGCIRCUIT27 REMAINING`（1 行: `hkgfacts`）、`FGCIRCUIT27 AXIOMS`: 12 名、標準 axiom のみ。

Check の出力行は 7（SIGNATURES-A 1、SIGNATURES-B 1、HYPS 1、QUOTES 1、CONTROLS 1、REMAINING 1、AXIOMS 1）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は条件付き。

### 33.5 次

`hkenv` (A)/(B)（D.T-4k）、`htop`、`hcd`（S2b）、`HftRootLink`（S2c）。`ui_val` の snapshot `Vi` を `userInliner` の kernel 評価に置き換える道は未調査（`userInliner` が `partial`/extern を含むため現時点で見つかっていない）。

### 33.6 ビルド環境の注記

`timeout 1500 kjob lake build TARGET`（`ulimit -v` なし）。`Tools.ShippingFGCircuitS2gGates` は約 1 分（S2d の build 込みで）、Check27 も約 1 分。

## 34. S2h（Issue `sparkle-fg-circuit-pilot` の次の束）: 履歴つき述語 — 子の run の読みを miss で保存し hit で取り出す

土台 `6bfe8328`（par/fgc-s1）。追加ファイル: `Tools/ShippingFGCircuitS2hHist.lean`（履歴述語・不変条件・`synthesizeChild`・core）、`S2hHist2.lean`（深さ帰納・本体・closing・`MachineClosesAtH`）、`S2hHist3.lean`（消費側・cache 初期化・`hftCoreCloses_of_kidsH`・最終文）、`Tests/Gen5/FGCircuitPilotCheck28.lean`、Check26 の SIGNATURES-C、docs §32.7。共有の `RealChildA`/`JQC`/`CacheInvA` と既存補題は**変更していない**（コピーに `JQC`→`JQH O E`、`RealChildA`→`RealChildE O E` を入れた版を足した）。S2b/S2c/S2f/S2g のファイルには触れていない。新しい law・axiom・TRUSTED・sorry・native_decide はない。Issue の状態は変えていない。成果は**条件付き**で台帳に数えない。

### 34.1 定義

- `RealChildE O E c r`（帰納）: `RealChildA.run` と同じ欄 ＋ `ev : E mctx cctx w`（その結果を作った run の開始 world の証拠）、cache 欄は再び `RealChildE`（その entry を作った履歴）。`RealChildE.toA` で `RealChildA` に戻る。
- `CacheE`、`JQH O E D w := JQ O.quiet D w ∧ CacheE O E (cv w)`、`JQH.toC : JQH → JQC`。
- `KidEv mref cref e := fun mctx cctx w => ReadsAt e cref w ∧ GetEnvProfileAt mctx mref cctx cref w`（証拠。profile 無効の枝を含む）。
- **`MissE O E`**（名前付き仮説 FG D.T-4h）: 深さ `D ≥ 1` の `JQH` world で、callee の entry が cache に無いとき、呼び出しの文脈 `mctx cctx` で `E mctx cctx w`。

### 34.2 三つの接続（レビュアー指定）

| 接続 | 名前 | 内容 |
|---|---|---|
| cache 初期化 | `tripleH_clear`、`coreHeadOff_jqhA` | 根の run の頭（深さ 0）が cache を `{}` にするので、任意の `E` で `JQ O.quiet 0 w → JQH O E 1 w1`（`cacheE_empty`） |
| miss で保存 | `synthesizeChild_tripleH`、`jqh_insert_runs` | 入れ子の run の開始 world で `MissE` から `E` を得て `RealChildE.run … ev` を作り、挿入しても `JQH` は保たれる |
| hit で取り出し | 同上（hit 枝）、`machineChild_of_realE` | 返る値は cache の entry で、その `RealChildE` が自分の証拠を持つ。消費側は `ev` から `ReadsAt`/`GetEnvProfileAt` を取り出す（普遍前提 `KidStartEnv` を使わない） |

深さ帰納・本体・closing も `JQH` で作り直した: `childKeepsH_all`、`bodyStepH_of_tele`、`htrH_of_tele`、`closeInstsM_runH`/`closeInstsGM_runH`（子は `ChildrenRealE`）、`machineClosesAtH_of_pure`、`callsPureE_of_gateKids`、`machineClosesAtH_of_gateKids`。`hft_kid_ifaceH`、`hft_closesAtH`（`hft_nodup` を kernel `decide` で足した。pin 版ではなく distinct-callee 版）、`hftCoreCloses_of_kidsH`。

### 34.3 最終文

`HftFinalStmtOffLNKH`（`synth_hftPcieOutByte_finalOffLNKH_{Z,Y,X}`、標準 axiom のみ）: S2d の `hkenv : HftKidsStartEnv …` を `hmiss : MissE L.O (KidEv mref cref (envAt cref w))` に替えたもの（明示仮説 14、`hkgates` は S2g のまま）。`hkenv` 版（S2d）は条件つきの部品として残る。

### 34.4 何が変わり、何が残るか（正直な範囲）

- 変わったこと: 子の run の証拠は、無関係な run まで含む全称ではなく、**cache の全 entry が自分の証拠を持つ履歴の world** で、**run が作られる miss の時点だけ**に要求する。hit は何も要求しない（保存された証拠を使う）。profile 条件も同じ履歴の上で扱う。
- 残ること: `MissE` はその履歴 world の上ではなお全称で、world の環境が根の run に結び付いていない。つまり `hmiss` を根の run の frame から導くには、不変条件に環境（`ReadsAt e`、profile）を足して全ステップ（class-D の `whnf` 等の行と telescope 行）で保つ必要があり、これは未証明（S2d §32.3 と同じ理由）。不可能とは言わない。次の一歩は、`JQH` に環境成分を足した版と、その各行の保存補題。
- `hkgates`（S2g）、`HftRootLink`（S2c）、`hcd`（S2b/S2i）、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws/Start/hr` は変わらない。

### 34.5 Check

- **Check26 SIGNATURES-C**（追加）: `machineDefinesLinked_of_readerE`、`hftCoreCloses_of_kidsK`、`synth_hftPcieOutByte_finalOffLNKK_Z` の完全な型を独立に書いた期待型と `isDefEq`（binder kind も）で照合。実型の正規形は 1 回。棄却した mutant: readerE 13、core 25、final 34（hkenv/hkgates の環境を終了 world・独立 world に、別の ref/context、子の名前・shape の入れ替え、profile 条件なし、旧入口、別の artifact/output/design/結論 …）。reach 走査の文言は「走査の範囲」に限定。最終ラッパーが変わったらこの Check も同時に更新する。
- **Check28**（新規、出力 11 行）: DEFS-RUN（`RealChildE.run`、mutant 7）、DEFS-MISS（`MissE`、3）、DEFS-JQH（2）、SIGNATURES-INV（`coreHeadOff_jqhA` 5 + `synthesizeChild_tripleH` 6）、SIGNATURES-CORE（`hftCoreCloses_of_kidsH`、28）、SIGNATURES-FINAL（`finalOffLNKH_Z`、35）、REACH（reach 走査の範囲で `MachineDefines`/`HftKidsDefine`/`MachineCloses`/`KidStartEnv` は到達されない。依存閉包全体については主張しない）、REMAINING 3、AXIOMS（31 名、標準のみ）。
- mutant の判定は `withReducible` の `isDefEq`（`withDefault` は 25 分以上かかったので採らなかった）。

### 34.6 ビルド

`timeout 1500 kjob lake build TARGET` を 1 つずつ。各 Hist ファイルは数分以内、Check26/28 は 1〜2 分。

## 35. S2i（Issue `sparkle-fg-circuit-pilot` の次の束）: 閉包環境の関係 `Sh`（`List.rec` 規則つき）、橋渡し族 `DT`、閉包環境の生成器

土台 `5dc8972f`（S2b）。追加ファイル（既存は書き換えていない）: `Tools/ShippingFGCircuitS2iSh.lean`（`Sh`）、`Tools/ShippingFGCircuitS2iDT.lean`（族 `DT`）、`Tools/ShippingFGCircuitS2iDTFun.lean`（`dt_fun`）、`Tools/ShippingFGCircuitS2iTbl.lean`（表版規則）、`Tools/ShippingFGCircuitS2iGen.lean`（閉包環境の生成器）、`Tools/ShippingFGCircuitS2iRun.lean`（`derive_expr_t`/`derive_hft_t`）、`Tools/ShippingFGCircuitS2iProbe.lean`（手動 probe、lakefile 外）、`Tests/Gen5/FGCircuitPilotCheck29.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない。Issue の状態は変えていない。成果は**条件付き**（`hcd` は**未導出**）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

### 35.0 正直な状況（先に）

- **この束の 2h の大半は冷間 build に使われた**（`kjob lake build` は 25 分の `timeout` で 402/917 で 2 回切れ、キャッシュは再利用されなかった。3 回目はジョブ用ビルドディレクトリで `lake build` を直接 3300 秒の上限で続行し、S1pCD まで約 40 分）。FG 連鎖（S1rCD → S1sCD → S1wTbl → S2bShare → S2bGen）は 1 モジュール 4〜5 分で、**生成器（`S2iGen`/`S2iRun`）と `Check29`、root の試行は手元で一度もコンパイルできていない**。以下の「コンパイル済み」は `lean` 直接実行（olean は S2iSh/S2iDT/…のみ）で確認したものだけ。
- したがって **hftRootValue の型付き導出（`hcd`）は試行していない／導出していない。カーネル時間・ピークメモリ・項サイズの測定は無い**。S2b の 2〜2.5h の外挿が閉包環境で解消したかは**この束では未測定**（未解決として扱う）。

### 35.1 (a) `Sh`（`Tools/ShippingFGCircuitS2iSh.lean`、コンパイル済み、`sh_fun` は標準 axiom のみ）

- `Ent := val (en : Entry) | clo (e : Expr) (ρ : List Ent)`、`Cx := List Ent`、`Hn := ctor (c) (ls : List Level) (np) (sp : List Ent) | stuck (c) (ls) (sp)`（**S2b からの変更: 構成子/停止頭の水準 `ls` を `Hn` に保持**）。
- 規則: `app`（call-by-name、引数は閉包として積む）、`lam`、`letZ`（`coreHead A = false`）、`bvarC`、`unf`（定義本体は**空の環境**で展開、宣言の閉性に依る）、`ctor`（飽和、水準保持）、`prim`（`stopD c = true`）、`proj`、**新: `recNil`/`recCons`**（`List.rec.{ls} a0 mot nilc consc major extra…`。major は閉包で、`Sh` で**静的な** `List.nil`/`List.cons al hd tl` に評価。`recCons` は `consc` を `hd :: tl :: (再帰呼出し) :: extra` に適用し、再帰呼出しは閉包 `recCallE ls = List.rec.{ls} #4 #3 #2 #1 #0` を環境 `[tl, consc, nilc, mot, a0]` で捕捉。引数の複製なし）。`recIota`/`projRec` の置換。
- `stopD c := stopC c ∨ newStopC c ∨ tyStopC c ∨ c = Signal.map`（`Signal.map` を停止頭にした: 狭い配線規則 `mapFst`/`mapSnd` の頭。`Signal.mk` へ展開しない）。
- `sh_fun`: 決定性（`recNil` と `recCons` の排他は major の評価結果が異なる ctor になることから）。**`Sh` 単体は型付きのカーネル評価ではない**（型・宣言閉性・捕捉環境の整合は `DT` の規則側で担う。置換との対応は定理ではなく監査）。

### 35.2 (b) 橋渡し族 `DT`（`Tools/ShippingFGCircuitS2iDT.lean`：コンパイル済み。`Tools/ShippingFGCircuitS2iDTFun.lean`：下記）

- `DT env : Cx → Expr → Res → Prop` = `DS` の**値/型の規則**（`nat/bool/domainConfig/bitvec/signal/bvar/natLit/domDefault/bvOfNat/bvInhabited/boolInhabited/sigPure/sigRegister/sigMux/sigAddBV/sigLoop/lam/letE/sigBeqBV/sigAndBool/sigOrBool/sigNotBool/bvAbbrev/prodTy/punitTy/unitVal/prodMk/mapFst/mapSnd/inhMk/inhDefault/bundle2`、環境を `Cx` に、`lam`/`letE` は `Ent.val` を積む）から**置換規則 `unf/beta/zeta/projStep/projCtor/recIota/projRec` を取り除き**、次を足したもの:
  - `bvarClo (hb : ρ[i]? = some (Ent.clo e' ρ')) (h : DT env ρ' e' r) : DT env ρ (.bvar i) r`（閉包の意味 = 捕捉環境での式の意味）。
  - `viaSh (hv : viaOK e = true) (hsh : Sh env ρ e [] hn) (hsp : hn.head.2.2 = args.map (fun a => Ent.clo a ρ₀)) (hcan : args = [] → ρ₀ = []) (h : DT env ρ₀ (appN hn.head.1 hn.head.2.1 args) r) : DT env ρ e r`（**頭が ctor/停止頭に達し、その spine が単一の共通環境 `ρ₀` の閉包 `args.map (clo · ρ₀)`** のとき、`e` の意味は `c ls args` の `ρ₀` での意味。後者は直接規則）。`hcan` は引数なしのとき `ρ₀ = []` に正準化（関数性のため）。
  - `boolFalse`/`boolTrue`（同じ env の `ctorInfo` を持つ `Bool` の ctor 値）。
  - `mapFst`/`mapSnd` は S2b の規則から `MapStuck` の前提だけ除いた（`MapStuck` は `unf` との排他のためで、`DT` に `unf` は無く `Signal.map` は `Sh` の停止頭）。**`Signal.mk` の一般規則はない**。任意の `Nat → α` の流れを無条件に導く規則もない。
- 排他性は頭で決まる: `directHead c := stopD c ∨ c ∈ {Prod.mk, PUnit.unit, Inhabited.mk, Bool.false, Bool.true}`、`viaOK e` は `bvar`/`lam` 単体と直接頭の適用で偽。`letE`（核の型）と `Sh.letZ`（それ以外）は `coreHead A` で排他。
- `dt_fun`（関数性）: `DS` の `ds_fun` を写し、新規則（`viaSh` は `sh_fun` と `map_clo_eq` で `ρ₀`/`args` の一意性、`bvarClo`、`boolFalse/True`）を加えた。**状況は 35.5**。

### 35.3 (c) 生成器（`S2iGen`、**未コンパイル**）

- `evalSh`: `Sh` をメタ水準で走らせ証明項を作る。環境・閉包・spine はカーネル項（`Cx`/`Ent`）で**ポインタ共有**、置換と式の複製なし。**全呼出しを `(ρ, e, sp)` でメモ化**（同じ閉包は 1 回だけ評価され、証明項が共有される = 証明 DAG 上の call-by-need）。`List.rec` は静的 nil/cons、`unf` は空環境（水準パラメータなしは `instLE_nil` で `instLE` の評価を避ける。ありは `instLEShared` が DAG を保つ）。表は S2b の `record`/`Look` をそのまま使う。
- `deriveT`: 直接規則は S2b `derive` から移植、`bvarClo`、`viaSh`（`Sh` を走らせ、spine が共通環境でなければ **「closures over different environments」で失敗**、頭に規則が無ければ「has no rule」で失敗）。`derive` の `memo` は `(ty, ρ, e)`。
- 名前つき定義（部分項/証拠ごと）は**未実装**。いまは Expr のポインタ共有 + メモのみ（測定してから）。

### 35.4 (d) 新しい停止の規則

- `Bool.false`/`Bool.true`: 狭い ctor 値規則（同じ env の `ctorInfo`、型付き値 `false`/`true`）を `DT` に追加（コンパイル済み）。
- `Signal.mk`: **規則を足していない**。許可済みの配線（`Prod.fst/snd` の map、`bundle2`）は `mapFst/mapSnd/bundle2` の直接規則で、`Signal.map`/`bundle2` を `Sh` の停止頭にしたので `Signal.mk` へ展開されない。`hftRootValue` が他の `Signal.mk` を要するかは**未測定**（probe 未実行）。要するなら、正確な部分項を報告して止める方針。

### 35.5 検証の状況（正直な記録）

- コンパイル済み（`lean` 直接、olean は build ディレクトリへ）: `S2iSh`（3〜4 s、`sh_fun` は propext/Classical.choice/Quot.sound のみ）、`S2iDT`（4 s）。
- `S2iDTFun`（`dt_fun`）: **コンパイル済み（約 240 s、エラー 0、sorry 0）。`dt_fun` は propext/Classical.choice/Quot.sound のみ**（`#print axioms`）。
- `S2iTbl`/`S2iGen`/`S2iRun`/`Check29`: 未コンパイル（FG 連鎖の build が間に合わなかった）。lakefile への登録は追記のみ（キャッシュ鍵が変わるので build は未実行）。

### 35.6 測定表

| 項目 | 値 |
|---|---|
| hftRootValue の DT 節点数 / Sh 歩数 / viaSh 数 | 未測定 |
| 生成時間 / ピーク RSS | 未測定 |
| カーネル時間 / 項 DAG サイズ | 未測定 |
| S2b の外挿（2〜2.5h、1 歩あたり DAG 再走査）は解消したか | **未解決（未測定）**。設計上は 1 歩が局所（`Sh` は置換しない）なので再走査は無いが、`unf` の `instLE` 評価と、`Eq.refl` の表引き（`lookOf` の `Name` 比較）の総コストは測っていない |

### 35.7 証明したもの / 名前付き仮説 / 次

- 証明（コンパイル済み、標準 axiom のみ）: `sh_fun`、`DT` の定義と排他補題（`viaOK_*`、`map_clo_eq`）。`dt_fun` はコンパイル済み（35.5）。
- 名前付き仮説（未供給）: `HftObCDS`（`hcd`、新族 `DT` 版の義務 `HftObCDT` は**まだ定義していない**）、`EnvDefs/EnvCtors/RecFact`、`HftRootLink`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws/Start/hr`、`Sh` と置換規則の対応（監査）、Expr 書き換えの意味保存。**`hcd` は導出していない。最終結論への接続（新 Off 入口/新 carrier）は未実施**（`HftFinalStmtS` は型別名に過ぎない、という reviewer の指摘のまま）。
- 次: FG 連鎖を 1 回の長い build で通し（`timeout` を 3300 秒以上にする、または連鎖を持つキャッシュを温める）、`S2iTbl`/`S2iGen`/`S2iRun`/`Check29` をコンパイル、probe で止まりの正確な部分項（`Signal.mk` の有無）、`HftObCDT` の型を `S2iDT` に足し、`hftRootValue` の導出を測定。

## 36. S2j（Issue `sparkle-fg-circuit-pilot` の次の束）: `htop` — 非 leaf root の `TopShips` を、同じ run の事実から

土台 `6b5ba9a8`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は各 1 回）: `Tools/ShippingFGCircuitS2jCopy.lean`、`Tools/ShippingFGCircuitS2jKid.lean`、`Tools/ShippingFGCircuitS2jTop.lean`、`Tests/Gen5/FGCircuitPilotCheck30.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない（標準 axiom のみ）。S2c/S2f/S2h/S2i の領域（`HftRootLink`/endpoint 生成器、Check17、kids 履歴、`hcd`）には触れていない。Issue の状態は変えていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で台帳に数えない。

### 36.1 手順 1: instance を持つ module の `TopShips` が要る部品の完全な型（先に固定）

`htop : ∀ p, GPt lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p` の中身は、core run `(raw, D₀)`（`synthesizeCombinationalCoreOff hftRoot`）と `PostEntry b raw D₀ D'` に対する `∃ n, TopShips p n hftRoot b raw D₀`。`TopShips`（`Tools/ShippingGen2Defs.lean:288`）は `p` のデータ、`ids`/`cache`/`regs`、入力の `SourceInputs`、`ResetNk n raw D kids`（**子の reset は TopShips の前提**で、`kids` は全称）、`bodyInstOuts (childMap D.modules) b.body`、`runModuleTG (KSn (childMap D.modules) n) …` の実行と出力の一致を述べる。instance を持つ root では次の部品が要り、**1 本の経路 `oneOut_topShipsO`（`Tools/ShippingGen2OneOutTopO.lean:336`、1 出力の親）**がこれを全て取る:

| 部品 | 完全な型（`oneOut_topShipsOff` の前提、`P := GPt lvl (envAt cref w)`、`p ∈ P hftRoot`） | 供給 |
|---|---|---|
| 親のデータ | `MemParentDataOk p`、`∀ k < insts.length, (instOrigins.getD k ord).child? = none`、`insts ≠ []`、`instFields = []`、`slots ≠ []` | **証明**（`p.d = synth_hftPcieOutByte.machineData`、`p.kD = 5` を `genGP_root_kids` と `RootReader` から、`hft_memData`/`hft_ord`/`hft_instFields`/`hft_slots_ne`/`hft_insts_ne` は kernel） |
| run の入口 | `RunsTo (synthesizeCombinationalCoreOff p.decl) … (raw, D) w1`、`b = dropZeroWidth raw ∨ mergeChecked (dropZeroWidth raw)`、`MachineDefinesLinkedOff … p.decl p.d.shape w raw D w1` | **証明**（`htop` の仮説の run・`hdRun`・`PostEntry`） |
| root の closing | `MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D`（= `MachineRunJQC`: certified machine run が `some (raw, D)` を返す）。この中で `closeLets`・`CloseCalls`・`ChildrenRealA`（`coreOff_ranA`/`MachineRanA`）と `closeInsts` の `kidsCombB` が出る | **証明**（`machineRunJQC_of_closesCOff` に S2d の `hft_closesAtK`（`hkenv`・`hkgfacts`・readers・`CellPrem` から）。`dv w = 0` は `Start`） |
| 子の package | `P (insts[k]).1 = some q`（`k = 0,1`）、`q` は `.comb` 行（`ss = []`、`insts = []`） | **証明**（`kid_pkg`: canonical table の leaf 行の `genSemI` は `ss = ∧ insts = []` で `.comb`） |
| 子の `ChildShips` | `ShipsRes L P c y := RealChildA L.O c y ∧ (∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n y.1 y.2) ∧ InstClosed y`（呼ばれた子の**実際の出力** `y`） | **証明**（`kid_shipsRes`: `RealChildA` の run から `kidRunK`（S2d の `machineChild_ifaceK` の結論を core run・machine run・`D.modules = []` まで拡張した複製）で machine run を取り、`slotlessLeaf_childShips_of_ran`（`slotlessLeaf_ships` の `ChildShips` 部分、未使用の all-world `MachineDefines` を外した複製）で `ChildShips`。`InstClosed` は子の設計が空） |
| served の trace | `MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D) p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc` | **証明**（`Pkg.trace`（`ServedRealA`）を `servedP_of_real` + `traceLBX_mono` で `ServedP (ShipsRes L P)` に。子の名前は `root_insts`） |
| 幅 | `∀ k, OneOutWidth P p k`（親の call 結果 binder の幅 = 子の 1 出力の幅） | **証明**（`hft_width0/1` は kernel、子の package は `kid_pkg`） |
| 呼び出しの decoding | `∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k` | **名前付き仮説 `hdec : HftCallDec lvl (envAt cref w)`**（§36.3） |

`ResetNk` は `TopShips` の前提であって供給物ではない（`kids` は全称）。`TopShips` の n は `oneOut_topShipsOff` が `n+1` を返すので `∃ n` は `0 + 1`。

**独立した文面との照合**: Check30 が `HftCallDec`、`oneOut_topShipsOff` の完全な型、`hftTop_of_run`、最終文を、別に書いた文面と `isDefEq` で照合する（§36.5）。

### 36.2 手順 2: 証明できたもの（標準 axiom のみ）

| 名前 | 内容 |
|---|---|
| `machine_ships_hierC_runOff`、`oneOut_topShipsOff`（`S2jCopy`） | `machine_ships_hierC_run`（FitChain:1073）と `oneOut_topShipsO` の複製。**変えたのは binder の型だけ**（`synthesizeCombinationalCore X [] false` → `synthesizeCombinationalCoreOff X`、`MachineDefines …` → `MachineDefinesLinkedOff … w raw D w1`、名前）。run と entry は `soundL`/`composed` の lambda が読まないので証明本体は逐語のまま |
| `kidRunK`（`S2jKid`） | `machineChild_ifaceK`（S2d）の複製。結論を `∃ M D w1, core run ∧ post ∧ MachineRunJQC ∧ D.modules = [] ∧ (ChildComb ∧ …)` に拡張 |
| `kid_pkg` | 組合せ leaf 行（`ss = []`、`insts = []`、`RootReader`）の table の package は `.comb cp`（`cp.decl = X`、`cp.d = d`、`cp.kD = kDOf d`）。`CombPkg.extS/extBS` は恒等なので `ExtInS` は `rfl` |
| `slotlessLeaf_childShips_of_ran` | `slotlessLeaf_ships` の `ChildShips` 部分を machine run だけから |
| `kid_shipsRes` | 組合せ leaf の子の**実出力**の `ShipsRes`（上記） |
| `servedP_of_real`、`traceLBX_mono` | 一般補題 |
| `hftTop_of_run` | `htop` を `hdec` と run の事実から。13 仮説（`L lvl env₀ hstart hcell hchk hreadH hreadT hkenv hkgfacts hdec` + 暗黙 6） |
| `HftFinalStmtOffLNKKGT`、`synth_hftPcieOutByte_finalOffLNKKGT`（`_Z/_Y/_X`） | S2g の最終文の `htop` を `hdec` に替えたもの |

### 36.3 名前付き仮説 `hdec : HftCallDec lvl (envAt cref w)`（FG D.D-4 `G-CALLDEC` / T2-TIE。run 局所でなく**package の文**）

`∀ p, GPt … hftRoot = some p → ∀ k (hk : k < p.d.shape.insts.length), ∃ q, GPt … (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k`。`CallDec p q k`（`Gen2Defs.lean:211`）は、親の call `k` の引数が親の `lets` にあり、callee の port 範囲にあり、親の call 結果信号が callee の source 出力に一致する、という package の文。run も全 world も含まない（Check30 HYPS: `hdec` から `RunsTo`/`MachineDefines`/`Start`/`ShipsRes`/`TopShips` は到達不能）。既存の分解（`Tools/ShippingGen5T2Tie.lean`）: `callDec_of_callTie` ← `CallTie` ← `GenExtAtCall`（table `genGP` について **`hDT1_of_genGP` が与える**。本束では未接続）+ `CallOutRange`（`hDG_SEM_range`、**未供給**）+ T2-FIELD（callee の module が 1 出力、`callField_at`。本束で得た `ShipsRes` と run の `CallStmt` から出る）+ 静的な data 検査（`callArgsOkAt`、kernel）。次の束は `hDT1_of_genGP` の接続と `CallOutRange`。

### 36.4 最終文の binder 一覧（`synth_hftPcieOutByte_finalOffLNKKGT_Z`、明示仮説 14）

`hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd hdec hkenv hkgfacts`（S2g の `finalOffLNKKG_Z` の `htop` が `hdec` に替わった。個数は同じで位置も同じ）。`htop` は仮説でなくなった。`hnoraw`・`hclL`・`hkgates`・`hsrc`・`hhead` は仮説に無い（S2g まで）。

### 36.5 Check30 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck30`、exit 0、943 jobs）

- `FGCIRCUIT30 SIGNATURES-A`: `HftCallDec` と `oneOut_topShipsOff`（profile-free core run、run-local entry、`ShipsRes` の trace）の完全な型を独立に書いた文面と照合。**9 mutant 棄却**（呼び出しごとの callee を 1 つに固定 = 別の子の出力、call index 0 固定、別の root、callee の package を要求しない、old entry（診断 core run + all-world `MachineDefines`）、decoding の欠落、`ServedRealA`、別の design）。旧 `oneOut_topShipsO` が old-entry mutant と一致することも検査。
- `FGCIRCUIT30 SIGNATURES-B`: `hftTop_of_run` と `finalOffLNKKGT_Z` の完全な型を照合。**8 mutant 棄却**（印刷後の design `D'` 上の `TopShips`、old core run、別の宣言の top、end world の decoding、old entry の `hr`、carrier `cdvY`、`htop` を残した S2g の文、`hdec` の欠落）。
- `FGCIRCUIT30 HYPS`、`FGCIRCUIT30 REMAINING`、`FGCIRCUIT30 AXIOMS`（13 名、標準 axiom のみ）。Check の出力行は 5。

### 36.6 証明した / 名前付き仮説 / 次

- **証明**: §36.2 の表。`htop` は `hdec` だけを残して run の事実（`coreOff_ranA` の系の `MachineTaken`、`closed_of_ranA` の系の `kidsComb`（`oneOut` 内）、子の実出力の `ChildIface`/`ChildShips`、`KidStartEnv`、`hreadH/T`、`kid_pkg`）から導けた。
- **名前付き仮説（run 局所または package の文。all-world law・snapshot の供給ではない）**: `hdec`（D.D-4 G-CALLDEC）。S2g から不変: `hkenv`（D.T-4k）、`hkgfacts`（D.T-4g）、`hlink`（S2c）、`hcd`（S2b/S2i）、`hreadH/T`、`hchk`、`CellPrem`、`Laws/Start/hr`。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。条件付きは減算しない。
- 次: `hdec` の分解（`hDT1_of_genGP` の接続、`CallOutRange`、T2-FIELD、静的 data）。

### 36.7 ビルド環境の注記

`timeout 1500 kjob lake build TARGET`（`ulimit -v` なし）。S2jCopy/S2jKid/S2jTop/Check30 はそれぞれ数十秒〜1 分程度（依存は cache）。

## 36′. S2o（Issue `sparkle-fg-circuit-pilot` の次の束）: S2i の残りのコンパイル、`HftObCDT`、probe の止まり、共有の測定

（注: 番号の重複。この節は S2o の §36 で、S2q の §43 の「§36.3/§36.4」はこの節を指す。S2j の §36 は直前の節。）

土台 `a0903cd8`（S2i）。TRUSTED・axiom・sorry・native_decide・新しい law はない。Issue の状態は変えていない。成果は**条件付き**（**`hcd` は未導出**）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。S2k（最終文）・S2n（AdmDownR）の範囲には触れていない。

### 36.1 コンパイル（すべて `kjob lake build`、timeout なし、温間キャッシュ）

- `S2iTbl`: import の誤り（`Tools.ShippingFGCircuitS1wTbl` を import していなかった）を直しコンパイル（4 分、冷間分を含む）。
- `S2iGen`: `open …S2iTbl`、`mkConst` の曖昧さ（`Term.mkConst`）、`Eq.refl` の宇宙（`List Ent : Type 1`、`hsp` は `Eq.refl.{2}`）を直しコンパイル。
- `S2iRun`: 構造体リテラルの桁下げ（フィールドは `{` の桁以上）と `open …S2iTbl` を直しコンパイル。
- `Check29`: 通過（AXIOMS ok 1 行、SHARE/SHADOW/HIGHER/REC-NIL/REC-CONS/REC-IH/DEFAULT/BOOL の 8 つが kernel 検査済み・標準 axiom のみ、制御 4 つ（CTRL-ENVS/SIGNALMK/UNBOUND/REC-MAJOR）は期待したエラー文で失敗、定理は追加されない）。
- `Sh`/`DT`/`dt_fun` は標準 axiom のみ（`#print axioms`、再 build でも同じ）。

### 36.2 `HftObCDT`（`Tools/ShippingFGCircuitS2oOb.lean`）

`HftObCDT env := CDT env [] hftRootValue (MonoTy shHft) synth_hftPcieOutByte`（単一の env、元の `hftRootValue`）。補題 `hftObCDT_unique`（`cdt_eq` から値の一意性）。**定義のみ。`HftFinalStmtS` は型別名のままで、新しい Off 入口/新 carrier への接続は主張しない。**

### 36.3 probe（`Tools/ShippingFGCircuitS2iProbe.lean`、lakefile に登録して `kjob lake build` で実行）

- 最初の止まりは `Sh.letZ` が核の型の `let` を頭に置けないこと（`HFTPcieOut.outByte dom (hftPcieLoop dom …)` を評価すると、`hftPcieLoop` の本体が核の型の `let`）。**直した**: `Sh.letZ` から `coreHead A = false` を外し、`DT.letE` との排他を `viaOK (.letE _ A ..) = !coreHead A` で取り直した（`sh_fun`/`dt_fun` を再コンパイル、標準 axiom のみ、Check29 は変わらず通る）。
- 直した後の probe（cap なし）: **DT 節点 5282、Sh 歩数 72012（app 30965 / lam 19459 / bvarC 12527 / unfPoly 2095 / ctor 1738 / recCons 1228 / unf 1209 / proj 1078 / prim 731 / letZ 726 / recNil 256）、viaSh 920、生成 2.5 s、ピーク RSS 約 2.37 GB（Lean 環境込み）**。止まりは**重複除去後 13 件、3 種類**:
  1. `Signal.map` の一般関数（`Prod.fst/snd` ではない）: 値 `Signal.map #k (BitVec 8) (BitVec 1) (fun x => BitVec.extractLsb' 8 6 1 x) #17`、および `Signal.map … (BitVec 32) (BitVec 2) (fun x => BitVec.extractLsb' 32 2 2 x) (TlpRxOut.addr #35 #29)`（`#36`〜`#38`、`#43` も同形）と `(BitVec 32)(BitVec 8)(fun x => extractLsb' 32 0 8 x) (TlpRxOut.addr #50 #44)`（計 7 件。`IP.Bus.PCIe` のビット切り出し）。**許可済みの狭い配線（`Prod.fst/snd`）の外**。
  2. `Signal.mk`（4 件、`viaSh: the head Signal.mk reached by evaluation has no rule (constructor; 3 arguments)`）: `HShiftLeft.hShiftLeft (Signal dom (BitVec 16)) (BitVec 16) … (instHShiftLeftSignalBitVec …) #1 (BitVec.ofNat 16 8)`、同 32 ビット版、`HAppend.hAppend (BitVec 8) (Signal (BitVec 8)) (Signal (BitVec (8+8))) (instHAppendBitVecSignalHAddNat 8 …)`、同 24 ビット版。つまり **`hftRootValue` は `Signal` の `<<<` と `++`（インスタンスが `Signal.mk` に展開される）を要する。一般の `Signal.mk` 規則は許されないので、ここで止める**（正確な部分項は上のとおり）。
  3. `Sh: bvar 0 is bound to a value entry in head position @ #3 #0` / `#4 #0`（2 件）: `DT.lam` が積んだ値の項を頭として関数適用している部分項。DT 側の規則（値 entry を頭にした適用）が要る。`Signal.mk` とは別件。
- よって **型付き導出（`hcd`）は試みていない**（止まりがあるため `derive_hft_t` は成功しえず、成功したように見せない）。必要な規則の方針（reviewer 判断待ち）: (1) 切り出しの `Signal.map` は `extractLsb'` に限った狭い規則を許すか、(2) `<<<`/`++` の狭い規則（`Signal.mk` を一般に開けずにインスタンスごと）を許すか。どちらも許可範囲外なので足していない。

### 36.4 測定（共有、`Tests/Gen5/FGCircuitPilotCheck35.lean`、`kjob lake build`）

共有連鎖 n: `(fun x0 => (fun x1 : T0×T0.. ) … ) false`、各変数を 2 回参照、`T(k+1) = T k × T k`、値は木で 2^n 葉。

| n | DT 節点 | Sh 歩数 | 生成 ms | kernel ms | 項 DAG | 項 tree |
|---|---|---|---|---|---|---|
| 4 | 20 | 16 | 3 | 0 | 612 | 2.3e5 |
| 8 | 54 | 24 | 3 | 0 | 1084 | 4.0e7 |
| 12 | 104 | 32 | 5 | 0 | 1684 | 1.4e10 |
| 16 | 170 | 40 | 7 | 0 | 2412 | 4.6e12 |
| 20 | 252 | 48 | 9 | 0 | 3268 | 1.5e15 |
| 24 | 350 | 56 | 13 | 0 | 4252 | 4.7e17 |

DAG は n に対して**二次**（差分が 128 ずつ増える: 612, 1084, 1684, …）で、tree は指数。kernel は 0 ms と表示された（**訂正（S2q）: 「kernel 0 ms」は「共有を再走査していない」ことの証拠ではない。さらに S2q で、この `kernel ms` は定理の `addDecl` が非同期（またはディスパッチのみ）で、実際の検査時間を測っていなかったと分かった（同じ生成物で、同期の `Environment.addDeclCore` に替えると 32 ms → 7283 ms、§43.4）。したがって S2o/S2p までの `kernel ms` の数字（0〜52 ms）は検査時間の測定として無効**。DAG が n に対して二次であることと、tree が指数であることだけが、項の形についての事実）。Check29 の小例（SHARE/SHADOW/HIGHER/REC-*/DEFAULT）でも kernel 0 ms（同じく分解能以下）、DAG 80〜662。**区別（S2q、S2t で訂正）: 上の表の `kernel ms`（0〜52 ms）は非同期の `addDecl` の数字なので、小例（この表と Check29 の SHARE/SHADOW/…）の検査時間は同期では再測定しておらず「不明」である。「S2b の外挿（2〜2.5 h）が小さい例で再現しなかった」とは言えない（「測定済み」「分解能以下」と書いたのは誤り）。同期で確かめたのは §45 の根（検査 約 7 s）だけ。これと独立に、項の DAG サイズ（n に対し二次、tree は指数）は表のとおりの観測で、検査時間とは別の事実。**「根そのものの kernel 時間・項サイズ」はこの節の時点では未測定（S2q で根の項が作れた: §43、承認済み規則での再導出と同期測定は §45）。probe の生成側だけの数字（5282 節点、72012 歩、2.5 s）は上に記録した。

### 36.5 仮説・次

- 名前付き仮説（未供給）: `hcd`（`HftObCDT`）、`EnvDefs/EnvCtors/RecFact`、`HftRootLink`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws/Start/hr`、`Sh` と置換規則の対応（監査）。
- 次（判断が要る）: 36.3 の 1・2・3 の規則。1・2 は reviewer の許可（狭い規則の範囲）が前提。3 は `DT` の規則の追加（許可範囲内の見込みだが未実装）。根が通ってから kernel 時間・ピークメモリ・項サイズを測る。


（merge 注、S2u §45′.4 より）上の表の旧「kernel ms = 0」は非同期の計測で無効。Check35 の同期 kernel 保存ログは n = 4..24 で 37/43/53/62/74/90 ms（S2u の再実行では 43/40/60/59/67/82 ms、ばらつく）。これは小さな共有連鎖の時間で、根の時間ではない。

## 37. S2k（Issue `sparkle-fg-circuit-pilot` の次の束）: 統合最終文 `HftFinalStmtOffCombined` — `hmiss`（S2h）・`hkgfacts`（S2g）・`hdec`（S2j）を 1 つの最終文に（**§37 は S2k では書かれなかった。S2r が事後に記す**）

土台 `6c9f2dcf`（par/fgc-s1）。追加ファイル: `Tools/ShippingFGCircuitS2kRun.lean`（履歴 world `JQH` からの root の機械 run と served instance の複製）、`Tools/ShippingFGCircuitS2kFinal.lean`（`kid_shipsResE`、`hftTop_of_runH`、最終文）、`Tests/Gen5/FGCircuitPilotCheck31.lean`、Check27 の更新（SIGNATURES-B/C）、`Tools/ShippingFGCircuitS2kLink.lean`（**草稿。S2k の時点ではコンパイルしていない**、§42.5 参照）。新しい law・axiom・TRUSTED・sorry・native_decide はない。成果は**条件付き**で台帳に数えない。

### 37.1 内容

- `MachineRunJQH`、`machine_run_of_coreHOff`、`machineRunJQH_of_closesHOff`、`synthesizeMachineCertified_runsH`、`soundX_served_E`（S2kRun）: `machine_run_of_coreCOff` 以下の `JQC`/`RealChildA` を `JQH`/`RealChildE` に替えた複製。root の頭（深さ 0）が cache を `{}` にするので、root の run は履歴 world から取れ、served instance は `RealChildE`（自分の run の読みを持つ）。
- `kid_shipsResE`: 子（slotless 組合せ callee）の実結果が `ShipsRes` を満たす。S2j の `kid_shipsRes` の全 world 前提 `KidStartEnv` を、履歴の entry が保存した証拠（`KidEv`）に替えた。
- `hftTop_of_runH`: S2j の `hftTop_of_run` を履歴前提に適合させた版（`hkenv` → `hmiss`、`hkgates` → `hkgfacts`）。
- **`HftFinalStmtOffCombined`**（明示仮説 14）: S2d の最終文の `hkenv` を `hmiss`（FG D.T-4h）、`hkgates` を `hkgfacts`（FG D.T-4g）、`htop` を `hdec`（FG D.D-4）に、それぞれ同じ位置で替えた。`synth_hftPcieOutByte_finalOffCombined(_Z/_Y/_X)`。

### 37.2 binder 一覧（`synth_hftPcieOutByte_finalOffCombined_Z`、明示 14）

`hlink hstart hr hcell hchk hreadH hreadT hcd hdec hmiss hkgfacts`（+ `L lvl env₀`。`hlink` が先頭）。

### 37.3 Check（S2k の時点）

- Check27: SIGNATURES-A、SIGNATURES-B（構造 17）、SIGNATURES-C（`finalOffLNKKG_Z` の完全型）、QUOTES、CONTROLS、REMAINING（`hkgfacts`）、AXIOMS 12。
- Check31: SIGNATURES-TOP（`hftTop_of_runH`）、SIGNATURES-FINAL（`finalOffCombined_Z` の 14 仮説の完全型が独立文面と一致）、HYPS、REMAINING（`hmiss` D.T-4h、`hkgfacts`、…）、AXIOMS 13（標準 axiom のみ）。
- **既知の不備（レビュアー指摘、S2r §42.2 で解消）**: 一部の mutant ブロックは正例を default、mutant を reducible/instances で比較していた（同じ基準でない）。

### 37.4 残る前提と位置づけ

`hdec` は §38（S2l）で `hftCallDec_of_checked` により供給できる、`hmiss` は §39（S2m）で `hftCoreCloses_of_kidsR` の 7 仮説に替えられる、と S2k の時点で分かっていたが、この最終文はまだ `hdec` と `hmiss` を持つ。それを外した最終文が §42（S2r）の `HftFinalStmtOffCombined2`。

## 38. S2l（Issue `sparkle-fg-circuit-pilot` の次の束）: `hdec` — 非 leaf root の `HftCallDec` を 3 つの reader から証明

土台 `86230111`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は各 1 回）: `Tools/ShippingFGCircuitS2lDec.lean`、`Tests/Gen5/FGCircuitPilotCheck32.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない（標準 axiom のみ）。S2k（最終文、Check27/31、§33/§37）と S2i（`hcd`、Check29、§35）の領域には触れていない。Issue の状態は変えていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で台帳に数えない。

### 38.1 手順 1: 完全な型（先に固定）

```
theorem callDec_of_oneOutCall {ι} {dom} (P : Pkgs ι dom) (p q : Pkg ι dom) (k) (hk : k < p.d.shape.insts.length) :
  P (p.d.shape.insts[k]'hk).1 = some q → (p.d.shape.instOrigins.getD k .ord).child? = none →
  GenExtAtCall p q k hk → p.d.shape.instFields = [] →
  p.d.callsOk p.kD = true → p.d.ss.length = p.d.shape.layout.slots.length →
  callArgsOkAt p.d p.kD k q.portWidths = true → (p.d.shape.insts[k]'hk).2.1.length = q.ports.length →
  (∃ o, q.d.shape.layout.outs = [o]) → (∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width) →
  (∀ o, q.d.shape.layout.outs = [o] → (p.d.shape.binders[p.kD + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth) →
  CallDec p q k

theorem hftCallDec_of_readers {ι} (lvl : Expr → Nat) (env : Environment)
  (hreadR : RootReader lvl env hftRoot synth_hftPcieOutByte.machineData)
  (hreadH : RootReader lvl env hftHttp httpGetByte.machineData)
  (hreadT : RootReader lvl env hftTlp tlpCplByte.machineData) : HftCallDec (ι := ι) lvl env

theorem hftCallDec_of_checked {ι} {mref} {cref} (lvl) (env₀) {w} (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
  (hfind : ∃ ci, (envAt cref w).find? hftRoot = some ci) (hreadH : RootReader lvl (envAt cref w) hftHttp …) (hreadT : …) : HftCallDec (ι := ι) lvl (envAt cref w)
```

独立文面は Check32 が `isDefEq` で照合する。

### 38.2 分解（`callDec_of_callTie` ← `CallTie` ← …）の各部の供給

| 部品 | 供給 |
|---|---|
| `GenExtAtCall p q k`（`k = 0, 1`） | **証明**: `hDT1_of_genGP`（table `GPt = genGP …` に接続。`hord`＝`child? = none` は kernel の `hft_ord`） |
| `CallOutRange` | **証明**（予定の未供給を解消）: `callOutRange_of_widths` = `Pkg.src_range`（callee の source 出力は自身の layout 幅未満）+ callee の `o.ty.bitWidth = o.width`（`http_outTy`/`tlp_outTy`、kernel）+ 親の call 結果 binder の幅（`hft_width0/1`、kernel）。run も子の実出力も不要 |
| T2-FIELD（callee は出力 1 つ） | **証明**: root は `instFields = []`（`hft_instFields`）なので `callField_one` が `CallField ↔ q.outs = [o]` を与え、callee の layout の出力が 1 つであること（`http_outsLen`/`tlp_outsLen`、kernel）から。`callField_at`（`ShipsRes` 経由）は使わない = **run を要しない** |
| 静的 data | **証明**（kernel）: `hft_callsOk`、`hft_slotsLen`、`hft_args0/1`（`callArgsOkAt`）、`hft_len0'/1'`（引数個数＝callee の port 数） |
| callee の package | `kid_pkg`（S2j、table の leaf 行は `.comb`、`cp.d = d`、`cp.kD = kDOf d`） |

### 38.3 残る前提（`hdec` の供給に要るもの）

`hftCallDec_of_readers` の前提は 3 つの `RootReader` のみ: root（`hftCallDec_of_checked` では `hchk` と「root が開始環境にある」から `startFacts_of_checked`）、`hreadH`、`hreadT`。最終文には root の `hchk` と `hreadH/T` が既にあるので、**`hdec` は新しい前提を足さずに最終文の前提から出る**（S2k が `hdec` を仮説から外して `hftCallDec_of_checked` で置換できる。root が環境にある事実は `root_find_of_headAtOff`（`hr` と `hcell`）から run 局所に得られる）。run・世界・`Start`・`ShipsRes`・`TopShips` はこの文から到達不能（Check32 HYPS）。

### 38.4 Check32 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck32`、exit 0、945 jobs）

- `FGCIRCUIT32 SIGNATURES`: 3 定理の完全な型を独立に書いた文面と照合。**9 mutant 棄却**（callee の reader の入れ替え、別の root、reader の欠落、call index 0 固定、callee 固定、見つかる宣言が違う、終端 world の環境、range の行の欠落、callee の package が親自身）。
- `FGCIRCUIT32 CONTROLS`（kernel）: 入れ替えた callee・誤った call index の `callArgsOkAt` は `false`、正しい組は `true`。
- `FGCIRCUIT32 HYPS`、`FGCIRCUIT32 REMAINING`、`FGCIRCUIT32 AXIOMS`（13 名、標準 axiom のみ）。Check の出力行は 5。

### 38.5 証明した / 名前付き仮説 / 次

- **証明**: `callDec_of_oneOutCall`、`hftCallDec_of_readers`、`hftCallDec_of_checked`、kernel の静的 data 11 件。`GenExtAtCall`（`hDT1_of_genGP` 接続）、`CallOutRange`（`callOutRange_of_widths`）、T2-FIELD（`callField_one`）、`callArgsOkAt` はすべて供給済み。FG D.D-4 `G-CALLDEC` はこの root について仮説でなくなる。
- **名前付き仮説（S2l で新設なし）**: `hdec` を `hftCallDec_of_checked` で置き換えたあとに残る前提は S2j/S2g のまま: `hkenv`（D.T-4k）、`hkgfacts`（D.T-4g）、`hlink`（S2c）、`hcd`（S2b/S2i）、`hreadH/T`、`hchk`、`CellPrem`、`Laws/Start/hr`。
- 次: S2k が最終文の `hdec` を `hftCallDec_of_checked` で置き換える（`hfind` は `root_find_of_headAtOff` と `hr`・`hcell` から）。最終文は S2l では変えていない。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。条件付きは減算しない。

### 38.6 ビルド環境の注記

`kjob lake build TARGET`（短い timeout なし）。S2lDec は依存が cache で数十秒、Check32 も軽い。

## 39. S2m（Issue `sparkle-fg-circuit-pilot` の次の束）: `MissE` の置換 — 対象 root の開始 world から到達する環境の不変条件 `JQHR` を本体帰納に通す

土台 `86230111`（par/fgc-s1）。追加ファイル（既存の定理は書き換えていない。lakefile 登録 4 件）: `Tools/ShippingFGCircuitS2mReach.lean`（到達関係・強めた quiet・`ropsR`）、`S2mReach2.lean`（`JQHR`・`missR`・`jqhr_head`）、`S2mReach3.lean`（各ステップの保存・`hftCoreCloses_of_kidsR`）、`Tests/Gen5/FGCircuitPilotCheck33.lean`。S2k（最終文 §33/§37）・S2i（hcd §35）・S2l（hdec §38）のファイルには触れていない。新しい law・axiom・TRUSTED・sorry・native_decide はない。Issue の状態は変えていない。成果は**条件付き**で台帳に数えない。最終文は変えていない（定理とその前提リストだけを提供する）。

### 39.1 レビュアー裁定（S2h §34.4 への）

`MissE` は root からの到達性述語ではない: 任意の `AdmCtx`・`D ≥ 1`・`n`・`JQH` world で miss が起きる所に対する全称である。cache が空なら `JQH` の cache 条件は自明で、履歴条件だけからは固定した root 環境への `ReadsAt` は出ない。次の一歩は、**対象 root から**の到達・環境の不変条件を本体帰納に通すこと。強い `MissE` を root の frame から導かない。新しい law は足さない。

### 39.2 設計と定義（完全な型を先に）

不変条件は `quiet` 述語そのものに入れた（`StableA`/`Keeps`/`Triple` の既存の一般補題が `RefLawsAOps` に対して書かれているため、`JQH` から `hftCoreCloses` までの S2h の定理が**そのまま**使える）。

```lean
inductive LeafStep (quiet) (mref) (cref) : World → World → Prop      -- 法則が語る葉の操作 1 回
  | frame   (mctx cctx) (p : MetaM α) (w) : AdmCtx quiet mctx cctx → FramedA MkRefd p → LeafStep quiet mref cref w (endW mctx mref cctx cref p w)
  | diag    …  Diag p …       | throws … Throws p …
  | cacheSet (mctx cctx) v w u w' : AdmCtx quiet mctx cctx → RunsTo (sparkleChildCache.set v) mctx mref cctx cref w u w' → LeafStep quiet mref cref w w'
  | depthSet … (ST.Ref.set sparkleSynthDepth v) …
inductive Reached (quiet) (mref) (cref) (w₀) : World → Prop
  | start : Reached … w₀ w₀
  | step  : Reached … w₀ w → LeafStep quiet mref cref w w' → Reached … w₀ w'
abbrev quietR quiet mref cref e w₀ := fun w => quiet w ∧ ReadsAt e cref w ∧ Reached quiet mref cref w₀ w
def ropsR (O : RefLawsAOps MkRefd mref cref) hcell e w₀ hdown hD hG : RefLawsAOps MkRefd mref cref   -- quiet := quietR O.quiet …
def JQHR O hcell e w₀ hdown hD hG D w := JQH (ropsR O hcell e w₀ hdown hD hG) (KidEv mref cref e) D w
def ProfOffW mref cref w := ∀ mctx cctx, GetEnvProfileAt mctx mref cctx cref w
```

- `Reached` は**任意の MetaM コード**の終了 world ではなく、法則の葉の操作（`FramedA` の行、診断、`throwError`、cache/depth の書き込み、いずれも admissible な文脈）だけで root の開始 world `w₀` から作られる world。任意コード（環境変数を書くもの等）を許すと下の `ProfOffW` の仮説が偽になるので葉に限った。
- `JQHR` の world は、quiet で、Core 環境が `e = envAt cref w₀` を `ReadsAt` で読み、`w₀` から到達し、cache の entry は自分の作った run の開始 world の読み（`KidEv`）を持つ。`KidEv`（S2h）の第 2 成分（profile lookup が off）は `ProfOffW` と下の `ProfStepR` から出る。
- `ropsR` の各 field: `RefLawsAOps` の field 9 個。`ReadsAt` は、非 class-D の `FramedA` の行・`throwError`・cache/depth の書き込みでは `CellPrem` から（`envFrameEnd_framedA/throws/set`、既存）、`DRow` の行と診断では名前付き仮説から、到達は `Reached.step`（構成子）、quiet は `O` の field（文脈は `hdown` 経由）。

### 39.3 証明したこと（標準 axiom のみ）

| 名前 | 内容 |
|---|---|
| `ropsR` | 強めた `RefLawsAOps`。`quiet`, `diag`, `frameT`, `excOk`, `frameQ`, `cacheSetQ`, `depthSetQ`, `frame`, `cacheSet`, `depthSet` を `O` と `CellPrem` と下の仮説から構成 |
| `profOffW_of_reached` | root の `ProfOffW` と葉の step の frame (`ProfStepR`) から、到達した全 world で `ProfOffW`（`Reached` の帰納） |
| `jqhr_facts` | `JQHR` の world は `O.quiet ∧ ReadsAt e ∧ Reached ∧ ProfOffW` |
| **`missR`** | `MissE (ropsR …) (KidEv mref cref e)`: **不変条件そのものから** miss 時の証拠が出る。`ReadsAt e` は quiet 述語に入っているので world から、profile は `ProfOffW`（到達 world） |
| **`jqhr_head`**（確立） | root の run の頭 `coreHeadOff`（depth 0 で cache を `{}` にする）の後の world は `JQHR` depth `0+1`。開始 world は `readsAt_self`・`Reached.start` で `JQ (quietR …) 0 w₀`（`coreHeadOff_jqhA` を `ropsR` で使う） |
| `jqhr_bodyStep`、`jqhr_childKeeps`（保存） | 機械本体の各 step、`synthesizeChild` の miss/hit（`D ≥ 1`）が `JQHR` を保つ。S2h の `bodyStepH_of_tele`、`childKeepsH_all_of_tele` を `ropsR` と `TeleR` で |
| `jqhr_synthesizeChild`、`jqhr_core`、`jqhr_closeInstsM`、`jqhr_closeInstsGM`（保存） | `synthesizeChild` の triple（結果は保存した読みを持つ `RealChildE`）、core の entry、1 出力/一般の closing が `JQHR` を保つ |
| **`hftCoreCloses_of_kidsR`** | `hftCoreCloses_of_kidsH` の `hmiss : MissE …` を下の 7 仮説で置換（§39.5） |

### 39.4 名前付き仮説（完全な型。量化範囲は仮説ごとに異なる。S2n で訂正: 「7 件とも到達した quiet world の上だけ」は撤回した）

| 仮説 | FG 行 | 型（要旨） | 必要な所 |
|---|---|---|---|
| `DRowEnvR O e w₀` | D.T-4m1 | `∀ mctx cctx p, AdmCtx O.quiet mctx cctx → DRow p → ∀ w, O.quiet w → ReadsAt e cref w → Reached O.quiet mref cref w₀ w → ReadsAt e cref (endW mctx mref cctx cref p w)` | `ropsR.frameQ` の class-D 13 行（`whnf`/`inferType`/`isClass?`/`whnfUntil`/`instantiateForall`/`mkLambdaFVars`/`mkAppM`/`unfoldDefinition?`/`reduce`/`ioEnv`/`monoMs`/`mkExprCache`/`localMk`） |
| `DiagEnvR O e w₀` | D.T-4m2 | 同上で `Diag p` | `ropsR.diag`（診断 9 行） |
| `TeleR O e w₀` | D.T-4m3 | `RefLawsATele (quietR O.quiet mref cref e w₀) mref cref`（4 行: `forallTelescopeReducing`/`lambdaTelescope`/`withLocalDeclD`/`withLetDecl`。不変条件が quiet・`ReadsAt e`・`w₀` から到達する world に限られる） | `jqhr_bodyStep` 以降の本体（telescope 行） |
| `ProfStepR O w₀` | D.T-4m4 | `∀ w w', Reached O.quiet mref cref w₀ w → LeafStep O.quiet mref cref w w' → ProfOffW mref cref w → ProfOffW mref cref w'` | `missR` の profile（`profOffW_of_reached`） |
| `ProfOffW mref cref w`（root の開始 world） | D.T-4m5 | root の開始 world で profile lookup が unset | 同上（帰納の基底） |
| `AdmCtx (quietR O.quiet mref cref (envAt cref w) w) mctx cctx`（`hadm`） | D.T-4m6 | root の文脈が強めた quiet で admissible | `jqhr_head` 以降 |
| `AdmDownR O e w₀` | D.T-4m7 | `∀ mctx cctx, AdmCtx (quietR …) mctx cctx → AdmCtx O.quiet mctx cctx` | `ropsR` の全 field（`O` の field を使う箇所） |

**量化範囲（S2n 訂正。各仮説ごと）**: `DRowEnvR`/`DiagEnvR` だけが quiet + `ReadsAt e` + `Reached` の world に限られる。`ProfStepR` が要るのは `Reached` + `LeafStep` + `ProfOffW` だけで、quiet も `ReadsAt` も要らない。`ProfOffW` は 1 つの world についてだが、全 `mctx`/`cctx` に対する。`TeleR` は任意の不変条件・任意の継続についての法則である（`quietR` を quiet として持つが、world の範囲は不変条件が決める）。`hadm`/`AdmDownR` は world ではなく callback（文脈）の性質で、他と同じ量化範囲ではない。`Reached` は、許可された任意の葉・文脈・引数（任意の cache 書き込みを含む）についての閉包であり、特定の run の実トレースではない。この過大近似の上で保存を示すのは問題ない。

`DRow` の 13 行と `Diag` の 9 行と telescope の 4 行、profile、文脈は、`CellPrem` からも `Laws` からも供給していない（S2d §32.3 と同じ理由で、現時点で供給経路が見つかっていない。導出不能の証明ではない。`QuietStrength` の構成は class-D・`diag`・telescope を含まない）。`DRow`/`Diag` の行について要るのは全 world の frame law ではなく、**root の開始 world から葉の step で到達した quiet な world で、その行が `ReadsAt e` を保つ**という run 局所の事実（DRow/Diag に限る。telescope・文脈・profile は別。S2s 訂正）。不可能とは言わない。

### 39.5 `hftCoreCloses_of_kidsR` の前提リスト

```
hftCoreCloses_of_kidsR (L : Laws mref cref) {w} (hstart : Start L mctx cctx w) (hcell : CellPrem MkRefd mref cref) {lvl}
  (hrH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData) (hrT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
  (hg : HftKidsGates (envAt cref w))
  (hadm : AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx)
  (hdown : AdmDownR L.O (envAt cref w) w) (hD : DRowEnvR L.O (envAt cref w) w) (hG : DiagEnvR L.O (envAt cref w) w)
  (hT : TeleR L.O (envAt cref w) w) (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w) : HftCoreCloses mctx mref cctx cref w
```

`hftCoreCloses_of_kidsH`（binder 13）の `hmiss : MissE L.O (KidEv mref cref (envAt cref w))` が、上の 7 仮説（`hadm hdown hD hG hT hs h0`）に替わった。`L.T` は使っていない（`TeleR` が代わる）。`hstart.2.1`（`JQ L.O.quiet 0 w`）が root の `JQ (quietR …) 0 w` を作る。最終文（`finalOffLNKH` 系）には**接続していない**（S2k が持つ。この定理を `hftCoreCloses_of_kidsH` の代わりに入れれば、`hmiss` が上の 7 仮説に替わる）。

### 39.6 正直な範囲

- `Reached` は「root の run の実行トレース」ではなく、`w₀` から法則の葉の操作で（任意の許可された文脈・引数・cache 書き込みで）作れる world の閉包。トレースは現状定義していない。量化範囲は仮説ごとに違う（§39.4 の訂正参照: `DRowEnvR`/`DiagEnvR` は quiet+`ReadsAt`+`Reached`、`ProfStepR` は `Reached`+`LeafStep`+`ProfOffW` のみ、`TeleR` は任意の不変条件の法則、`hadm`/`AdmDownR` は callback の性質）。
- `TeleR` は `RefLawsATele` の形（`I` について全称・継続の仮定つき）の仮説で、`L.T` を `quietR` に強めたもの。telescope 行の `ReadsAt` frame を継続の仮定から切り離して小さくする道は取っていない（`L.T` からは導けない: 不変条件に cache の証拠 `RealChildE` が入り、継続が cache を伸ばすため）。
- `hadm`/`hdown` は `canUnfold?` の callback の事実。**S2n で訂正**: 「文脈が `none` なら自明」（`admCtx_none`）は個々の `AdmCtx` についてだけで、全称の `AdmDownR`（∀ mctx cctx. `AdmCtx (quietR …)` → `AdmCtx O.quiet`）は root の `canUnfold? = none` からは出ない（`InertUnfold` は quietR 上でだけ inert な callback から O.quiet の全 world の inert を与えない）。§40 参照。
- `ProfOffW`（D.T-4m5）は root の run が profile-free の入口（`synthesizeCombinationalOff`）なので root 側では今まで要らなかった。子の `synthesizeCombinational` の lookup のために新しく root の開始 world で要る。
- `MissE`（D.T-4h）は**導出した**（`missR`）。ただし導出の前提が上の仮説で、それらは未供給。`hkgates`（S2g）、`HftRootLink`（S2c）、`hcd`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws/Start/hr` は変わらない。

### 39.7 Check33（`kjob lake build Tests.Gen5.FGCircuitPilotCheck33`、exit 0、940 jobs）

同一の比較関数（unfold する定数の集合も `isDefEq` の透明度（default）も、肯定と全 mutant で同じ）。出力 15 行。

- `FGCIRCUIT33 DEFS-REACH`: `LeafStep` の 5 構成子と `Reached.start/step` の型を独立に書いた文面と照合。**12 mutant 棄却**（admissible なし、任意コードを step に、診断/throw を framed の構成子に、cache 書き込みと depth 書き込みの入れ替え、別の world からの start、leaf のない step、前の到達のない step）。
- `FGCIRCUIT33 DEFS-QUIET`: `quietR` を `ExpQuiet` と照合。**6 mutant**（到達なし、`ReadsAt` なし、quiet なし、別の root 環境、別の world からの到達、別の world の環境）。
- `FGCIRCUIT33 HYPS`: `DRowEnvR`・`DiagEnvR`・`ProfStepR`・`ProfOffW`・`AdmDownR`・`TeleR` の型を照合。**27 mutant**（結論が開始 world、前提が end world、到達/`ReadsAt`/admissible の前提なし、class を全 framed 行へ広げる/診断へ狭める、別の root 環境、別 world からの到達、葉でない任意の step、profile lookup が ON、profile の片方の成分、文脈の law の逆/自明/別環境、telescope の law を plain/到達なし/別環境の quiet で）。
- `FGCIRCUIT33 SIGNATURES-INV`: `missR`、`jqhr_head` の完全な型（binder kind も）。**12 mutant**（root の profile 事実なし、step の frame なし、reads のみ、profile のみ、profile ON、`ropsR` でなく plain な bundle、別環境、depth 0、開始 depth 1、診断の頭、plain、頭の後の world の環境）。
- `FGCIRCUIT33 SIGNATURES-CORE`: `hftCoreCloses_of_kidsR` の完全な型（binder `mctx mref cctx cref L w hstart hcell lvl hrH hrT hg hadm hdown hD hG hT hs h0`）。**17 mutant**: 各前提の脱落（13）と 4 つの対照（**profile lookup が ON**、**別の root 環境**、**root の開始 world から到達しない world（独立した world からの到達）**、**end world（結論/profile 事実が独立した world）**）。
- `FGCIRCUIT33 STEPS`: 保存補題が `ropsR`・`TeleR` を使い、`MissE`/`KidStartEnv`/`HftKidsDefine`/`MachineDefines`/`MachineCloses` を含まない（**69 構造検査**）。reach 走査の範囲（`Tools`/`Sparkle` 下の `defnInfo`、帰納型の構成子と定理は展開しない、reach set 2979）でそれらに到達しない。依存閉包全体は主張しない。
- `FGCIRCUIT33 CONTROLS`: kernel 判定 5 件（`ctl_notReached`: 到達しない world は強めた quiet の外、`ctl_reads`、`ctl_root`、`ctl_step`、`ctl_profile`: profile が off と on の両方にはならない）と、4 つの文面レベルの対照への対応表。
- `FGCIRCUIT33 REMAINING`（7 行: `hadm hdown hD hG hT hs h0`）、`FGCIRCUIT33 AXIOMS`（13 名、標準 axiom のみ）。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は条件付き。

### 39.8 次

(1) S2k: `hftCoreCloses_of_kidsR` を最終文に接続（`hmiss` を 7 仮説に替える）。(2) 7 仮説の供給: `DRowEnvR`/`DiagEnvR`（class-D・診断行の環境 frame）、`TeleR`（telescope 行）、`ProfStepR`/`ProfOffW`（process 環境）、`hadm`/`hdown`（callback）。(3) `Reached` を `RunsTo` のトレースに結ぶ道（未調査）。

### 39.9 ビルド環境の注記

`kjob lake build TARGET` を 1 つずつ（`Tools.ShippingFGCircuitS2mReach` → `Reach2` → `Reach3` → `Tests.Gen5.FGCircuitPilotCheck33`）。各 Tools ファイルは数十秒（S2h の cache 込み）、Check33 は約 1 分。

## 40. S2n（Issue `sparkle-fg-circuit-pilot` の次の束）: `AdmDownR` の橋 — 文脈に持たせる形 `AdmBoth`、橋なしの強めた法則 `opsB`、世界レベルの置換 `QuietCover`

土台 `6c9f2dcf`（par/fgc-s1）。追加ファイル（既存の定理は書き換えていない。lakefile 登録 2 件）: `Tools/ShippingFGCircuitS2nAdm.lean`、`Tests/Gen5/FGCircuitPilotCheck34.lean`。S2k・S2i のファイルには触れていない。新しい law・axiom・TRUSTED・sorry・native_decide はない。Issue の状態は変えていない。最終文は変えていない。成果は**条件付き**で台帳に数えない。`AdmDownR` を新しい TRUSTED として通してはいない。

### 40.1 レビュアー裁定と §39 の訂正

`AdmDownR O e w₀ := ∀ mctx cctx, AdmCtx (quietR …) mctx cctx → AdmCtx O.quiet mctx cctx` は含意で、`InertUnfold q f` は `q` の world 上の inert だけを言う。`quietR` 上でだけ inert な callback から `O.quiet` の全 world の inert は一般には出ない。root の `canUnfold? = none` は**その個別の** `AdmCtx`（`admCtx_none`）を与えるだけで、全称の `AdmDownR` を与えない。§39.6 の「文脈が `none` なら自明」はこの意味に訂正した（§39.6 本文を直した）。§39.4/§39.6 の量化範囲の記述（「7 件とも到達した quiet world の上だけ」）も撤回し、仮説ごとの範囲に直した（`DRowEnvR`/`DiagEnvR` = quiet+`ReadsAt`+`Reached`、`ProfStepR` = `Reached`+`LeafStep`+`ProfOffW` のみ、`ProfOffW` = 1 world・全 `mctx`/`cctx`、`TeleR` = 任意の不変条件・継続の法則、`hadm`/`AdmDownR` = callback の性質）。`Reached` は任意の許可された葉・文脈・引数（任意の cache 書き込みを含む）の閉包で、特定の run の実トレースではない（トレースは現状定義していない）。

### 40.2 完全な型（先に）

```lean
def AdmBoth (O) (e) (w₀) (mctx) (cctx) : Prop :=
  AdmCtx O.quiet mctx cctx ∧ AdmCtx (quietR O.quiet mref cref e w₀) mctx cctx

def QuietCover (O : RefLawsAOps MkRefd mref cref) (e) (w₀) : Prop :=
  ∀ w, O.quiet w → ReadsAt e cref w ∧ Reached O.quiet mref cref w₀ w

structure OpsB (O) (e) (w₀) : Prop   -- RefLawsAOps の 6 field（diag/frameT/excOk/frameQ/cacheSetQ/depthSetQ）を quiet := quietR、文脈の前提を AdmBoth にしたもの。frame/cacheSet/depthSet は未実装（AdmBoth.plain で O から再利用できるが、この構造体には数えない）
theorem opsB (hcell : CellPrem MkRefd mref cref) (hD : DRowEnvR O e w₀) (hG : DiagEnvR O e w₀) : OpsB O e w₀      -- hdown なし
theorem admBoth_of_down (hdown : AdmDownR O e w₀) (h : AdmCtx (quietR …) mctx cctx) : AdmBoth O e w₀ mctx cctx

theorem hftCoreCloses_of_kidsR' (L : Laws mref cref) {w} (hstart : Start L mctx cctx w) (hcell : CellPrem MkRefd mref cref) {lvl}
  (hrH …) (hrT …) (hg : HftKidsGates (envAt cref w))
  (hadm : AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx)
  (hcover : QuietCover L.O (envAt cref w) w)
  (hD : DRowEnvR …) (hG : DiagEnvR …) (hT : TeleR …) (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w) :
  HftCoreCloses mctx mref cctx cref w
theorem hftCoreCloses_of_cover (L) {w} (hstart) (hcell) {lvl} (hrH) (hrT) (hg)
  (hcover : QuietCover L.O (envAt cref w) w) (hs : ProfStepR L.O w) (h0 : ProfOffW mref cref w) : HftCoreCloses mctx mref cctx cref w
```

### 40.3 証明したこと（標準 axiom のみ）

| 名前 | 内容 |
|---|---|
| `AdmBoth` | 文脈に持たせる形: 元の `AdmCtx O.quiet` と強めた `AdmCtx (quietR …)` の**両方**（どちらからも他方を導かない） |
| `admBoth_none`, `admBoth_mkMetaContext` | 確立（root）: `canUnfold? = none`（`mkMetaContext_canUnfold`）の文脈は `AdmBoth` |
| `AdmBoth.lctx/localInsts/lctx_insts/config/coreCtx` | 保存: 本体の帰納が行う文脈の更新（lctx・localInstances・config・Core 文脈）で `AdmBoth` が保たれる（`admCtx_*` を両成分に） |
| **`opsB`** | `ropsR` の 6 field（diag/frameT/excOk/frameQ/cacheSetQ/depthSetQ。他の 3 field は未実装）を `AdmBoth` 文脈の上で、**`hdown` なしで**導出（元の half を `O` の field に、強めた half は使わない。class-D と診断は名前付き仮説 `hD`, `hG`） |
| `admBoth_of_down` | `AdmDownR` が入る**唯一**の場所: bundle の文脈（`AdmCtx quietR`）を `AdmBoth` に直す変換 |
| `QuietCover`, `quietR_eq_of_cover` | 世界レベルの置換: `O.quiet` の world がすべて `e` を読み root から到達している。すると `quietR = O.quiet` |
| `admDownR_of_cover`, `drowEnvR_of_cover`, `diagEnvR_of_cover`, `teleR_of_cover` | `QuietCover` の下で `AdmDownR`, `DRowEnvR`, `DiagEnvR`, `TeleR`（`L.T` そのもの）は**定理** |
| **`hftCoreCloses_of_kidsR'`** | `hftCoreCloses_of_kidsR` の `hdown` を `hcover` に替えた（他の前提は S2m のまま） |
| **`hftCoreCloses_of_cover`** | 7 前提 `hadm hdown hD hG hT hs h0` を `hcover hs h0` に替えた（`hadm` は `hstart.1`） |

### 40.4 正直な範囲（何をしていないか）

- **文脈に持たせる形は bundle の外までしか通していない。** `opsB` は `AdmBoth` 文脈の上の法則を `AdmDownR` なしで与える。しかし S2h の鎖（`hft_closesAtH` 以下、`RefLawsAOps`・`RefLawsATele`・`Keeps`・`translate_keepsA…` など 80k 行の基盤）は**1 つの bundle** `R` を取り、文脈の量化は `AdmCtx R.quiet` である。`R.quiet := quietR` の bundle の文脈は `AdmCtx quietR` だけで、`AdmBoth` ではない。`AdmBoth` を文脈の型とする鎖は作っていない。したがって `AdmDownR` を使わずに `hftCoreCloses_of_kidsR'` を `AdmBoth` 形で与えることは**まだできていない**（不可能とは言わない: 鎖を文脈の述語について一般化するか、`RealChildE.adm`・`RefLawsATele` の文脈の量化を `AdmBoth` に替えた版を作る道がある。範囲が大きく、この束では作っていない）。
- `quietR ⊊ O.quiet` のとき `AdmDownR` は callback 全体への全称なので、`O.quiet` の world で `quietR` の外のものがあるなら一般に成り立たない。`AdmDownR` を世界レベルで言い換えると `QuietCover`（の十分条件）になる（`admDownR_of_cover`）。
- `QuietCover` は callback ではなく**法則の quiet 述語**についての前提で、`L` の取り方（法則を run に到達する world の集合で述べること）に依る。供給していない。`hftCoreCloses_of_kidsR'` は `hD hG hT` を残してあるが、`QuietCover` の下では冗長（`hftCoreCloses_of_cover` で外した）。`QuietCover` は S2h §34.4 のレビュアー裁定が退けた全称 `MissE` より強い形（`O.quiet` の**全** world）ではあるが、callback に関する全称ではなく、`L` の選び方の条件である。採用するかどうかは S2k / レビュアーの判断に残す。
- `ProfStepR`/`ProfOffW`、`HftRootLink`、`hkgates`、`hcd`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws/Start/hr` は変わらない。

### 40.5 Check34（`kjob lake build Tests.Gen5.FGCircuitPilotCheck34`）

`kjob lake build Tests.Gen5.FGCircuitPilotCheck34`: exit 0、943 jobs（Reach3 を含む初回ビルド）。同一の比較関数（`Check33.cmp`: 同じ定数集合を正規化し `isDefEq` を default 透明度で、肯定と全 mutant で同じ）。出力 10 行（DEFS 1、SIGNATURES 1、STEPS 1、REMAINING 4、AXIOMS 1 + Check33 の既存行）。

- `FGCIRCUIT34 DEFS`: `AdmBoth`・`QuietCover` を独立に書いた文面と照合。**10 mutant 棄却**（片方の half のみ、含意 `AdmDownR` を組の代わりに、選言、別の環境; 到達なし、`ReadsAt` なし、自明な逆向き包含、別の環境、別の world からの到達）。
- `FGCIRCUIT34 SIGNATURES`: `hftCoreCloses_of_kidsR'`・`hftCoreCloses_of_cover` の完全な型（binder の名前・kind も）。`hftCoreCloses_of_kidsR'` **19 mutant**（各前提の脱落 12、`QuietCover` を到達なし/`ReadsAt` なし/逆向きに 3、profile ON、別の root 環境、root から到達しない world、end world）、`hftCoreCloses_of_cover` **15 mutant**（脱落 8 と同じ対照 7）。binder 名 `mctx mref cctx cref L w hstart hcell lvl hrH hrT hg hadm hcover hD hG hT hs h0`（kidsR'）・`… hg hcover hs h0`（cover）。
- `FGCIRCUIT34 STEPS`（20 構造検査）: 新しい 2 定理は `AdmDownR`・`MissE` を含まない。`opsB` は `AdmDownR` を含まず `AdmBoth` を使う。`AdmDownR` を取るのは `admBoth_of_down` だけ。
- `FGCIRCUIT34 REMAINING`（4 行: `hs`, `h0`, `hcover`, 未実施の `AdmBoth` 鎖）、`FGCIRCUIT34 AXIOMS`（報告は18名だが `AdmBoth.cctx` は存在しない名前だった。S2s で `AdmBoth.coreCtx` に直し、存在確認を入れた。§44）。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は条件付き。

### 40.6 次

(1) S2k: `hftCoreCloses_of_kidsR'`/`hftCoreCloses_of_cover` の採否（`QuietCover` を `L` の条件として採るか）。(2) 採らないなら鎖の文脈一般化: `RealChildE.adm`・`RefLawsATele`・`Keeps` 系を `AdmBoth` 形の文脈の述語で一般化し、`opsB` から直接 bundle 相当を作る。(3) `hD hG hT hs h0` の供給（S2m §39.8 と同じ）。

### 40.7 ビルド環境の注記

`kjob lake build Tools.ShippingFGCircuitS2nAdm` → `Tests.Gen5.FGCircuitPilotCheck34` を 1 つずつ。S2m の鎖（`Tools.ShippingFGCircuitS2mReach3`）が未ビルドの cache だと 900 job 超の初回ビルドになる。
## 41. S2p（Issue `sparkle-fg-circuit-pilot` の次の束）: probe の止まり 3（値 entry を頭にした項）の DT 規則

土台 `9191f88b`（S2o）。TRUSTED・axiom・sorry・native_decide・新しい law はない。Issue の状態は変えていない。成果は**条件付き**（`hcd` は未導出）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。S2k・S2n の範囲には触れていない。止まり 1（`Signal.map` の `extractLsb'`）・2（`<<<`/`++` の `Signal.mk`）の規則は足していない（reviewer 待ち）。

### 41.1 止まり 3 の正体（先に）

- 止まり 3 の 2 件（`@ #3 #0` / `@ #4 #0`）を、エラー文に spine の長さと entry を足して調べた: **spine は 0**、entry は `Signal dom (HList …)` 型の**値 entry**（`DT.lam`/`DT.letE` が積んだもの）。つまり「値 entry が**適用される**」のではなく、`Sh` が頭の項を評価した結果が**裸の値変数**（空の spine）に至る（`(fun s => … s) arg` のような恒等的な受け渡し）形。関数値 entry が適用される例は probe に**無い**（`TDt` に関数型が無く、`lam`/`letE` が積む entry は関数型にならない）。したがって規則は「値 entry を頭にした**適用**」ではなく、**空の spine の値変数を結果にする**狭い規則。
- 狭い規則: **spine 空・値 entry のときだけ**。spine が空でない値 entry（関数値の適用）は引き続き「value entry applied」で失敗（足していない。Check36 の CTRL-VALAPP）。

### 41.2 規則（変更は最小）

- `Tools/ShippingFGCircuitS2iSh.lean`: `Hn.var (ρ) (i)`（結果が環境 `ρ` の値変数 `i`）、`Hn.isVar`、`Sh.bvarV`（`ρ[i]? = some (.val en)`、spine 空、結果 `Hn.var ρ i`）。`Hn.head` は `.var` に対し `(anonymous, [], [])`（`viaSh` は `hnv : hn.isVar = false` で除外）。`sh_fun` を再証明（`bvarC` と `bvarV` は `ρ[i]?` が `clo`/`val` で排他）。
- `Tools/ShippingFGCircuitS2iDT.lean`: `viaSh` に前提 `hnv : hn.isVar = false` を足し、新規則 `viaVar (hv : viaOK e = true) (hsh : Sh env ρ e [] (Hn.var ρ₀ i)) (h : DT env ρ₀ (.bvar i) r) : DT env ρ e r`（`e` の意味は、評価が至った値変数 `#i` の `ρ₀` での意味 = `bvar` 規則）。一般の高階規則・`Signal.mk` 規則・宇宙の拡張・TRUSTED は無い。
- 排他性/関数性: `viaVar` は `viaOK e` が真の `e` だけ（直接頭・裸の `bvar`/`lam` は偽）、`viaSh` とは `hnv` で排他（同じ `Sh` 評価 → `sh_fun` で同じ `hn` → `isVar` が真と偽で矛盾）、`bvarClo`/`bvar` は `e` が裸の `bvar` のため `viaOK` が偽で排他。`dt_fun` を**再証明**（`viaVar` の自己ケースと、`viaSh`/`letE`/`bvAbbrev` との排他ケースを追加、再 build 42 s）。`#print axioms`: `sh_fun`・`dt_fun` とも propext/Classical.choice/Quot.sound のみ。
- 新ファイル `Tools/ShippingFGCircuitS2pValHead.lean`: `sh_var_val`（`Hn.var ρ₀ i` で終わる評価は `ρ₀[i]?` が値 entry）、`bvarV_spine`（値 entry の変数は空でない spine と `Hn.var` に至らない）、`var_not_head`。標準 axiom のみ。
- 生成器（`S2iGen`）: `Sh.bvarV` と `DT.viaVar` を生成（`ShRes.var`）。値 entry に spine が付くときは「value entry applied」で失敗（fail-closed）。`viaSh` に `hnv` を渡す。`viaN` は viaSh と viaVar の合計。

### 41.3 probe の再実行と測定（`kjob lake build Tools.ShippingFGCircuitS2iProbe`、cap なし）

| 項目 | S2o（§36.3） | S2p |
|---|---|---|
| DT 節点 | 5282 | 5285（`viaVar` 15 件を含む） |
| Sh 歩数 | 72012 | 72003（`bvarV` 3） |
| viaSh（+viaVar） | 920 | 935（viaSh 920 + viaVar 15） |
| 生成時間 | 2.5 s | 約 2.0 s |
| ピーク RSS | 約 2.37 GB | 約 2.38 GB（2376552 kB、Lean 環境込み） |
| 止まり（重複除去後） | 13 | **11** |

- 残る止まり 11 件: 1（`Signal.map` の `extractLsb'`）7 件、2（`Signal.mk`、`<<<` 2 件と `++` 2 件）4 件、**3（値 entry）0 件**。
- よって `derive_hft_t` はまだ成功しえず、`hcd`（`HftObCDT`）は**未導出**。根の kernel 時間・項サイズは**未測定**（止まりのため根の項が作れない）。

### 41.4 Check36（`Tests/Gen5/FGCircuitPilotCheck36.lean`、軽量）

- AXIOMS ok 1 行（`sh_fun`/`dt_fun`/`cdt_fun`/`tdt_fun`/`cdt_eq`/`sh_var_val`/`bvarV_spine` は標準 axiom のみ）。
- 正の例 3 つ（生成器が出した項を kernel が検査、同じ報告文）: VALHEAD（`let x := false; (fun y => y) x`）、VALHEAD-PAIR、VALHEAD-NEST（2 つの値束縛、異なる entry）。DAG 219 / 283 / 372。旧「kernel 0 ms」は無効（S2q の訂正）。同期測定は Check41 の同じ入力で VALHEAD 4 ms、VALHEAD-NEST 10 ms（§45.4）。
- 負の対照 3 つ（期待したエラー文で失敗、定理は追加されない。生成器の失敗であって導出不能の定理ではない）: CTRL-VALAPP（値 entry に引数: «value entry applied»）、CTRL-SIGNALMK（`Signal.mk` はなお規則なし: «has no rule»）、CTRL-UNBOUND（«not bound»）。
- Check29 も変わらず通る（AXIOMS ok 1 行、正 8、対照 4）。

### 41.5 仮説・次

- 名前付き仮説（未供給）は §36.5 のまま（`hcd`、`EnvDefs/EnvCtors/RecFact`、`HftRootLink`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws/Start/hr`、`Sh` と置換規則の対応（監査））。`Sh.bvarV` も監査対象（値変数が結果のときの意味は `bvar` 規則に委ねる）。
- 次（reviewer 判断）: 止まり 1・2 の狭い規則を許すか。許されれば残り 11 件が解け、根の導出と kernel 時間・項サイズの測定に進める。

## 42. S2r（Issue `sparkle-fg-circuit-pilot` の次の束）: 統合最終文 v2 `HftFinalStmtOffCombined2`、Check の比較方式の統一、Check37

土台 `294821af`（par/fgc-s1）。追加ファイル（既存の定理は書き換えていない。lakefile 登録は各 1 回）: `Tools/ShippingFGCircuitS2rFinal.lean`、`Tests/Gen5/FGCircuitCmp.lean`（比較の共通関数）、`Tests/Gen5/FGCircuitPilotCheck37.lean`。更新: Check21/26/27/28/30/31/32 の比較関数（定理の文面は不変）、§39 の文言、§37 の新設。S2n（AdmDownR、`S2nAdm`/`Check34`/§40）・S2p（hcd の DT 規則、§41）のファイルには触れていない。新しい law・axiom・TRUSTED・sorry・native_decide はない。Issue の状態は変えていない。成果は引き続き**条件付き**で台帳に数えない。

### 42.1 統合最終文 v2

- **(a) `hdec` を仮説から除去**: `hftTop_of_runR` の中で、実際の `hr` の core run `hrun`（`HftObTopCoreOff` の束縛）と `hcell` から作る `HeadAtOff` を `root_find_of_headAtOff` に渡して `hfind` を得て、`hftCallDec_of_checked`（§38）に入れる。**`hfind` は新しい仮説ではない**（Check37 の HYPS で `hfind` は仮説でないことと、証明項が `hftCallDec_of_checked` と `root_find_of_headAtOff` を使うことを検査）。
- **(b) `hmiss` を S2m の 7 仮説に置換**: `hftCoreCloses_of_kidsR`（§39）の前提 `hadm hdown hD hG hT hs h0`（FG D.T-4m6, m7, m1, m2, m3, m4, m5。完全な型で、未供給のまま）。子の `ShipsRes`／served 側は**同じ履歴**（`ropsR` の `RealChildE`）で運ぶ: `kid_shipsResW`（`kid_shipsResE` を強めた bundle `O'` に一般化: `O'.quiet → L.O.quiet`、admissible の下げ（`hdown`）を渡す）、`soundX_served_E (ropsR …) hT (missR h0 hs) hadm`、`machineRunJQH_of_closesHOff (ropsR …)`（開始 world の `JQ (quietR …) 0 w` は `readsAt_self`・`Reached.start`）。`MissE`・`KidStartEnv`・全 world `MachineDefines` は仮説に戻していない（`MissE` は `missR` の**導出結果**の型として証明項に現れるだけ）。`ProfStepR`/`TeleR` が `L.T` から出るとは扱っていない（`L.T` は使っていない）。
- 補助: `realChildA_weak`（`RealChildA O' → RealChildA O`、`RealChildA` の帰納）、`jqc_weak`。いずれも標準 axiom のみ。

#### binder 一覧（`synth_hftPcieOutByte_finalOffCombined(2)_Z`、明示仮説）

| | 一覧 |
|---|---|
| 前（S2k `HftFinalStmtOffCombined`、14） | `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd hdec hmiss hkgfacts` |
| 後（v2 `HftFinalStmtOffCombined2`、19） | `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd hadm hdown hD hG hT hs h0 hkgfacts` |

（`hdec` が消え、`hmiss` が同じ位置で 7 仮説に替わった: 14 − 2 + 7 = 19。）

`hftTop_of_runH`（19 binder、implicit 含む）→ `hftTop_of_runR`（24 binder: `hmiss hdec` が消え、`hkgfacts hadm hdown hD hG hT hs h0` となった）。

#### 名前付き仮説（v2 に残るもの。いずれも未供給）

`hadm`（D.T-4m6: `AdmCtx (quietR L.O.quiet mref cref (envAt cref w) w) mctx cctx`）、`hdown`（D.T-4m7: `AdmDownR`）、`hD`（D.T-4m1: `DRowEnvR`）、`hG`（D.T-4m2: `DiagEnvR`）、`hT`（D.T-4m3: `TeleR`）、`hs`（D.T-4m4: `ProfStepR L.O w`）、`h0`（D.T-4m5: `ProfOffW mref cref w`）、`hkgfacts`（D.T-4g）、`hlink`（`HftRootLink`、S2c）、`hcd`（S2b/S2i）、`hreadH/hreadT`、`hchk`、`CellPrem`、`Laws/Start/hr`。除去: `hdec`（供給済み）、`hmiss`（導出 `missR`）。

### 42.2 Check の比較方式の統一（レビュアー指摘）

指摘: Check21/26/27/28/30/31/32 では正例を default の `isDefEq`、mutant を instances/reducible で比べており、同じ基準ではなかった。

**方式**（`Tests/Gen5/FGCircuitCmp.lean`、全 Check 共通）: 正例も全 mutant も**同じ関数** `stmtEq` を通る。呼び出し側が両辺を**同じ正規化**にかける（実型は 1 回だけ正規化して cache、期待文面と各 mutant は同じ `norm`）。`normCommon` が共通の末尾: 型の `instantiateMVars`、metadata の除去、`Tests.Gen5` 下の期待文面・略記の unfold、literal Bool の `if`（`true`/`false`、2 つの `Nat` 数値の `==`）の選択、`Nat` 数値の `OfNat.ofNat Nat n _` と raw literal の同一視、構造体射影 `Prod.fst x` と `x.1` の同一視、定理の適用（証明項）を 1 定数に置換（証明無関係）、`Name` literal の定数（`hftRoot` 等）と出力 shape `shHft` の unfold。`stmtEq a e` は `Expr.eqv`（alpha 同値、**unfold も `isDefEq` もしない**ので透明度設定に依存しない）**かつ**全深さの全 binder の kind が一致。`checkSame`（正例）は `stmtEq` が偽なら、`checkDiff`（mutant）は真なら失敗する。正例が失敗した場合は最初の相違箇所を出す。

- Check21 だけは型が計算を含む（`SType.Type (.bits n)` と `BitVec n`、`tys`、`List.take`/`List.map`）ため、呼び出し側が**全文面で同じ**評価対象 `reduceH`（`SType.Type`/`match_1`/`casesOn`/`rec`、`tys`、`List.take`、`List.map`）を `normCommon` に渡して whnf（`.all`）で評価する。基準は同じ `stmtEq`。
- Check26/27/28/30/31/32: `same*/diff*` を `checkSame/checkDiff` に差し替え、実型側の `norm*` の末尾に `normCommon` を足した。Check28 の `MissE`/`JQH` の直接比較（`isDefEq` default）も同じ関数に。Check27 は real 側にも `KidStartEnv` の unfold を足した。
- 定理の文面・mutant の集合は変えていない。全 mutant は同じ関数で棄却される（出力行数も変わらない）。
- 不変の方針: 実型の正規化は 1 回（Check19 と同様に cache）。ビルドは短い（各 Check 1〜2 分）。
- 範囲外: Check33 は元から正例も mutant も同一の `cmp`（default `isDefEq`）を使っており、今回は替えていない（§39.7）。Check19 の `sameE/diffE`（default 対 reducible）は今回の指摘の 7 本の外で、替えていない。

### 42.3 Check37（`kjob lake build Tests.Gen5.FGCircuitPilotCheck37`）

出力 6 行（SIGNATURES-FINAL、NOTE、HYPS、SIGNATURES-TOP、REMAINING、AXIOMS）:

- `FGCIRCUIT37 SIGNATURES-FINAL`: `synth_hftPcieOutByte_finalOffCombined2_Z` の**完全な型**（明示 19、binder kind を全深さで）を独立に書いた `ExpFinal2` と `stmtEq` で照合。mutant **73** を同じ基準で棄却: 別の world（`hcd`/5 つの reach 前提/ゲート事実/結論の環境を end world・`env₀`・独立 world に、reach の開始 world を end/独立に、profile の事実の world を end/独立に）、別の reference/context/design、別の root/post root/出力、別の carrier（`cdvY`/`cdvOld`）/obligation、結論の脱落（片方・両方）、各前提の脱落（9）、**`hfind` を追加の仮説に**、旧 `hdec`/`hmiss`（単独・同時・`hfind` との組）、profile lookup ON、各前提の形（class-D 行の frame なし/`ReadsAt` なし/開始 world の結論、診断を class-D と同じに、telescope を plain/到達なし、文脈の law の逆/自明、profile 保存を到達なし/開始/任意 step）、ゲート事実の入れ替え・重複・片方だけ・全体 reflection・True、reader の入れ替え、Diag 入口、旧 carrier、旧い最終文 5 件（S2k/S2h/S2j/S2g/S2d）。
- `FGCIRCUIT37 HYPS`: binder 一覧（19）、仮説でないもの（`hfind hdec hmiss htop hkenv hkgates …`）、7 前提がどれも `MissE/KidStartEnv/HftKidsStartEnv/MachineDefines/HftCallDec` を含まないこと、reach 走査（7 前提とゲート事実から。定義・`Tools` 帰納型の構成子・構成子の型だけを辿る。`MissE/MachineDefines/HftKidsDefine/MachineCloses/KidStartEnv/Start/CheckedStart/ShipsRes/ChildShips/TopShips/HftCallDec` に到達しない）、証明項（`hftTop_of_runR` が `hftCallDec_of_checked`・`root_find_of_headAtOff`・`ropsR`・`missR`・`kid_shipsResW`・`soundX_served_E`・`hft_closesAtH`・`machineRunJQH_of_closesHOff` を使い、`kid_shipsResE`・`hftTop_of_runH`・`KidStartEnv`・`MachineDefines` を使わないこと、ラッパーが `hftCoreCloses_of_kidsR` を使い `hftCoreCloses_of_kidsH` を使わないこと）。
- `FGCIRCUIT37 SIGNATURES-TOP`（`hftTop_of_runR` の binder 24）、`FGCIRCUIT37 REMAINING`（上の名前付き仮説）、`FGCIRCUIT37 AXIOMS`（8 名、標準 axiom のみ）。

### 42.4 正直な範囲

- 7 仮説はすべて未供給（量化範囲は一様ではない: `hD/hG` は DRow/Diag の行、`hT` は Tele、`hs` は ProfStep、`h0` は ProfOff、`hadm/hdown` は admissibility。§39 訂正版。一括で「quiet+ReadsAt+Reached」とは呼ばない）。v2 は §39 の前提リストを最終文に**接続**しただけで、仮説を減らしたのは `hdec` だけ（`hdec` と `hfind` は実際の `hr` から）。
- 最終文の `Ob`/`CV` の carrier、`hlink`（`HftRootLink`）は変わらない。
- `Reached` は閉包であり、run のトレースではない（§39.6 の文言を修正）。
- Check の「独立に書いた文面」は同じ人が書いており、独立性は文面の別記述に限る。

### 42.5 S2kLink（`HftRootLink` の組立、タスク 4）

**未着手（時間切れ）**: 2 時間の pod 制限のため、タスク 4（`S2kLink` の `HftRootLink` 結論部を抽象 `TVal` の独立補題として閉じる、S2c §31.5）には着手していない。`Tools/ShippingFGCircuitS2kLink.lean` は S2k の草稿のまま（**コンパイルしない**、lakefile 登録済み、この束では書き換えていない）。したがって v2 の `hlink : HftRootLink` は仮説のまま（`hlink` 供給版の v2 は無い）。次の束の最初の作業。

### 42.6 台帳

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。条件付き成果は減算しない。

## 43. S2q（Issue `sparkle-fg-circuit-pilot` の次の束）: `extractLsb'` の map 規則、`<<<`/`++` の 2 インスタンス規則、根の生成と測定

土台 `5c16ea55`（S2p）。TRUSTED・axiom・sorry・native_decide・新しい law はない。Issue の状態は変えていない。S2n（AdmDownR）・S2r（統合最終文）の範囲には触れていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。**`hcd`（`HftObCDT`）は承認済み規則の範囲では未導出**（残りの止まり 2 件: §43.3）。止まり 2 件を**未承認**の規則で埋めた副ブランチ `s2q-exp-or`（ローカル、push なし）では導出でき、測定が取れた（§43.4。承認済みの成果としては数えない）。

### 43.1 規則（reviewer 裁定 (1)(2) のとおり。ほかの関数・インスタンスは拒否のまま）

- `DT.mapExtract`（`Tools/ShippingFGCircuitS2iDT.lean`）: `Signal.map (fun x : BitVec wE => BitVec.extractLsb' nE loE lenE x) s` だけ。入力型と束縛型は `BitVec wE`（`wE ↦ W`）、結果型は `BitVec lE`（`lE ↦ L`）、`extractLsb'` の幅引数 `nE` は同じ `W`、長さ引数 `lenE` は同じ `L`（= 結果幅）、`loE ↦ LO`（束縛の下で任意の `x` について導出）、`s : Signal D (BitVec W)`、領域は 1 つの `D`。値は `Signal.map (fun x => extractLsb' LO L x) sv`。幅 `W`・`lo`・`len`・領域は任意（3 つの大きさに固定していない: パラメータ族）。任意関数の map 規則ではない。
- `DT.sigShlBV`: `Signal D (BitVec W) <<< BitVec W`（インスタンス `instHShiftLeftSignalBitVec`、定数の移動量は右）。信号と定数は同じ `W`・同じ `D` で導出。
- `DT.sigAppendCL`: `BitVec m ++ Signal D (BitVec n)`（インスタンス `instHAppendBitVecSignalHAddNat`、定数が左、信号が右、出力幅 `m + n`、順序保存）。
- `Sh` の停止頭 `stopD` に `HShiftLeft.hShiftLeft`・`HAppend.hAppend` を追加（`Signal.map` と同じく `Signal.mk` へ展開しない）。`directHead` は `stopD` を含むので、`viaSh`/`viaVar` と**重ならない**（`viaOK` が偽）。`dt_fun` を**再証明**（新 3 ケース、`stopD_shl`/`stopD_append` を `clashT` に追加、再 build 52 s、標準 axiom のみ）。
- 規則の基礎の等式（`Tools/ShippingFGCircuitS2qBits.lean`、すべて標準 axiom 以下）: 任意の時刻 `t` で `extract_at`（`(…).val t = BitVec.extractLsb' lo len (sv.val t)`、`rfl`）、`shl_at`（`= av.val t <<< k`、`rfl`: 実装は `pure`/`map`/`ap` の時刻ごとの `BitVec` 演算）、`append_at`（`= c ++ bv.val t`、`rfl`）。BitVec 本来の意味の補題: `shl_at_toNat`（`toNat = (x.toNat <<< k.toNat) % 2^W`、幅で切り詰め）、`shl_at_big`（`W ≤ k.toNat` なら `0#W`: 範囲外の移動量）、`append_at_toNat`（`= c.toNat * 2^N + y.toNat`: 上位ビットが `c`）。範囲外の切り出し（`lo+len > W`）は規則に側条件を足さず、`BitVec.extractLsb'` の意味（Check38 の EXTRACT 64/60/9）。
- 構文認識の根拠: 規則の `he` は式 `e` の全体を `appN` で書き下した形との等式（`Eq.refl`）で、展開や別表現は使わない。ただし `++` の出力幅 `m + n` は `HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) m n` の形で書き、`<<<`/`++` のインスタンスは名前と引数（領域・幅）が同じであることを式の等式で要求する。

### 43.2 生成器の修正（`S2iGen`/`S2iRun`、生成器は信頼しない: カーネルが検査する）

- 厳格な形の検査: `HAdd`/`HAnd`/`HOr`/`Complement`/`Signal.beq` の枝は、頭の定数だけで選んでいた（インスタンスを見ていなかった）。根の生成物をカーネルに出したとき、`HOr.hOr` の `Signal (BitVec 16)` オペランドを Bool 専用の `sigOrBool` 規則に当てた「application type mismatch」で初めて分かった（カーネルが止めた）。各枝を「期待する式の全体との等式」に直し、外れたら「no direct rule」で失敗する（probe の止まりとして現れる）。
- **束縛名の取り違え（生成器の不具合。S2q の修正は引数側だけで、根の引用そのものの cache は残っていた。S2u で修正: §45.2）**: 引用の cache（`qE`/`unq`）は `Expr` の `BEq`（α 同値、束縛名を無視）で引くので、束縛名だけが違う `lam` が同じ引用を返し、規則に `toExpr n`（生の名前）を渡すと `Eq.refl` の両辺で名前が食い違う（根の `fun x._@…_hyg.384` と `_hyg.626`）。`Sh.lam`/`Sh.letZ`/`DT.lam`/`DT.letE`/`mapExtract` の `n`/`bi`/`nd` を、**引用した項の引数**から取るように直した。
- 測定の修正（**S2u 注記: 下の「束縛名の取り違え」の修正は不完全だった。§45.2**）: `deriveRootT` の `kernel ms` を同期の `Environment.addDeclCore`（`IO.lazyPure` で強制）に替えた。以前の `addDecl` は非同期で、検査時間を測っていなかった（§36.4 訂正）。

### 43.3 probe の再実行（承認済み規則、cap なし、`kjob lake build Tools.ShippingFGCircuitS2iProbe`）

| 項目 | S2p（§41.3） | S2q |
|---|---|---|
| 止まり（重複除去後） | 11 | **2** |
| DT 節点 / Sh 歩数 / viaSh | 5285 / 72003 / 935 | 5510 / 74392 / 980 |
| 生成 / ピーク RSS | 約 2.0 s / 2.38 GB | 約 2.4 s / 2.37 GB |
| 規則の使用数 | | `mapExtract` 7、`sigShlBV` 2、`sigAppendCL` 2 |

止まり 1（`extractLsb'` の `Signal.map` 7 件）と 2（`<<<` 2 件、`++` 2 件）は解けた。**残る止まり 2 件は新規**（これまでは先に止まっていて見えなかった）: `HOr.hOr` の `instHOrSignalBitVec`（`Signal (BitVec n) ||| Signal (BitVec n)`）、`n = 16`（`(x <<< 8) ||| (c ++ y)` の 16 ビット版）と `n = 32`（`24 ++ 8` の 32 ビット版）。第 2 型引数が `Signal d (BitVec (8+8))`（`++` の出力幅の式のまま）で、インスタンスの添字 `16` と**構文的に異なる**（`Nat` の算術で定義等価）。承認済みの規則の範囲外（`|||` は許可リストにない）なので足していない。必要な規則の方針（reviewer 判断）: `sigOrBV` を `sigAddBV` と同様に BitVec 信号の `|||` に限り、第 2 型引数は構文でなく型の導出（または `m + n = w` の定義等価の証拠）で `w` に束縛する。

### 43.4 根の生成と測定（副ブランチ `s2q-exp-or`、**未承認の `sigOrBV` を含む**。承認済みブランチでは止まり 2 件のため生成できない）

`Tools/ShippingFGCircuitS2qHft.lean`（`derive_hft_t`）、`Tools/ShippingFGCircuitS2qHftOb.lean`（`hftObCDT_Q`）、`kjob lake build`、timeout なし、温間キャッシュ:

| 項目 | 値 |
|---|---|
| DT 節点 / Sh 歩数 / viaSh | 5533 / 74392 / 980 |
| 生成時間 / 表（`Delta`/`Gamma`）| 約 2.5 s / 55 defs・11 ctors（53 ms） |
| **kernel（同期、`hftObCDT_of_tablesQ`）** | **7283 ms**（旧表示 32 ms は非同期で無効） |
| 項 DAG / tree | **737 288** / 約 7.08×10^76 |
| ピーク RSS（カーネル検査後、Lean 環境込み） | 3 283 968 kB（生成だけでは約 2.34 GB） |
| `hftObCDT_Q`（導出値が `synth_hftPcieOutByte` と定義等価であること、`HftObCDT env` の型への適合） | モジュール全体 2.7 s |
| モジュール `S2qHft` の build 全体 | 13〜14 s |

`#print axioms`: `hftObCDT_of_tablesQ`・`hftObCDT_Q` ともに propext/Classical.choice/Quot.sound のみ。`hftObCDT_Q : ∀ env (hΔ : EnvDefs env Delta) (hΓ : EnvCtors env Gamma) (hrec : RecFact env), HftObCDT env`。tree 7×10^76 に対し DAG 7.4×10^5、カーネル 7.3 s: **S2b の外挿（2〜2.5 h）は、この閉包環境の根では起きなかった**（根そのものの測定: 上の表）。§36.4 の区別（小例での未再現 / 根の未測定）のうち、根の測定が副ブランチで取れた。ただし、これは `sigOrBV` の承認前提の数字で、承認済みの成果ではない。

### 43.5 Check38（`Tests/Gen5/FGCircuitPilotCheck38.lean`、軽量、正と負で同じ報告文）

- AXIOMS ok 1 行（`sh_fun`/`dt_fun`/`cdt_eq`/`extract_at`/`shl_at`/`shl_at_toNat`/`shl_at_big`/`append_at`/`append_at_toNat` は標準 axiom のみ）。
- 正 10 行（kernel 検査済み、同期で 6〜17 ms）: EXTRACT 8/6/1、32/0/8、32/2/2、16/3/10（probe の大きさ以外）、64/60/9（範囲外: BitVec の意味）、SHL 16、SHL 32（移動量 ≥ 幅）、APPEND 8+8、8+16、SHL を領域の束縛変数の下で（同じ領域変数の全オペランド）。
- 負の対照 12 行（期待したエラー文で失敗、定理は追加されない。生成器の失敗であって導出不能の定理ではない）: EXT-WIDTH、EXT-LEN、EXT-INPUT（入力信号の幅）、EXT-OTHERFN（`fun x => x`）、EXT-NOTVAR（`#0` 以外の引数）、SHL-AMOUNT（移動量の幅）、SHL-SIGNAL（信号の幅）、SHL-DOMAIN（別の領域変数）、APP-SWAPPED（信号が左）、APP-RIGHTWIDTH、APP-OUTWIDTH（出力幅 `m + n` 違い）、APP-WRONGINSTANCE。正しい式は別の定数でも導出される（上の正の例）。
- Check36（AXIOMS 1、正 3、対照 3）と Check29（AXIOMS 1、正 8、対照 4）は変わらず通る（生成器・`dt_fun`・測定の修正後に再実行）。

### 43.6 仮説・次

- 名前付き仮説（未供給）: `hcd`（承認済みブランチでは未導出）、`EnvDefs/EnvCtors/RecFact`（`hftObCDT_Q` では仮定として残る）、`HftRootLink`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws/Start/hr`、`Sh` と置換規則の対応（監査）。`stopD` の追加（`HShiftLeft.hShiftLeft`/`HAppend.hAppend` が `Sh` で展開されなくなった）も監査対象。
- 次（reviewer 判断）: `Signal (BitVec n) ||| Signal (BitVec n)`（§43.3）を許すか。許されれば副ブランチの `sigOrBV`（第 2 型引数を無制約にした実験版）を、第 2 型引数の束縛つきの規則に直し、`dt_fun` と Check を足して承認済みブランチに入れる。

## 44. S2s/S2s3（Issue `sparkle-fg-circuit-pilot`）: 文脈述語を quiet から分離した版（reviewer 裁定 (b)）— 依存経路に沿った限定的な移植。ここまでの到達点

土台 `81c7bea0`（par/fgc-s1）。追加ファイルは `Tools/ShippingFGCircuitS2sAdm*.lean` と `Tests/Gen5/FGCircuitPilotCheck39.lean`。既存の定理・ファイルは書き換えていない（新しい law・axiom・TRUSTED・sorry・native_decide はない）。Issue の状態は変えていない。**S2s5 で目標 `hftCoreCloses_of_kidsR''`（`hdown` なし、`hadm` なし）を述べて証明した（下記 44.6）。** 残る名前付き前提 `hD hG hT hs h0` は未供給のままで、成果は条件付きで台帳に数えない。

### 44.1 設計
- `RefLawsAOpsX` / `RefLawsATeleX quiet adm` / `CtxClosed adm`（`S2sAdmChildInvA`）: 文脈の述語 `adm` を bundle が持ち、本体が行う文脈の更新（lctx・localInstances・config・Core 文脈・`canUnfold?` を保つ `withReader`）で閉じる。既存の bundle はその特殊化（`RefLawsAOps.toX`, `RefLawsATele.toX`: `adm := AdmCtx quiet`）。
- 移植はリネームのみ（名前に接尾辞 `X`、`AdmCtx O.quiet` → `O.adm`、マクロ名にも接尾辞）。`withReader` の補題は `CtxClosed.canUnfold` を使う形に一般化（TeleLocalA のみ手書きの差分）。

### 44.2 ビルド済み（各ステップで commit、`kjob lake build` exit 0）
S2s の手順 1〜14（Check34/docs 修正、`RefLawsAOpsX/ATeleX`、VCA・CacheA(RealChildA)・VertA・PathA・TranslateA・FallbackA・CanonKeyA・LegacyCachedA・WalkA・TeleCP・FrontA・TranslatePathA・ProjFieldA・LegacyHelpersA・LegacyHandlersA・LegacyImplA・DepthA・FrontCP、KWalk）に加え、S2s3 で:
- 15: `ChildLegacyTailA`（`legacyTailA_genericX`, `legacyTailA_of_stepX`）。draft は修正なしでビルドが通った。
- 16〜: `ChildComposeA`, `ChildMainA`（`core_tripleA_mainX`）, `ChildTeleLocalA`, `ChildCacheA` の**全体**（これまでは `RealChildAX` のみで `JQC`・`EQC`・`synthesizeChild_tripleC`・`closeInstsM_realA` が未移植だった）, `ChildCoreC`, `ChildRunA`, `ChildDepthC`, `ChildRunAKids`, `ChildComposeC`, `ChildRunAMain`, `ChildTeleMainA`。`FrontCP` に `childEntryA_JQC_of_childSynthAX` を追加。
標準 axiom のみ（各ファイル末尾の `#print axioms`）。

### 44.3 移植済み（S2s4/S2s5）と、まだ移植していないもの
- S2s4: `S2sAdmS2hHist2` を再生成（sorry なし）。`LawsX`/`StartX`（`O : RefLawsAOpsX`, `T : RefLawsATeleX O.quiet O.adm`, `StartX := O.adm ∧ JQCX O 0 w`）、`RunReads`、`ServedRealA`、`RunLocal`、`Linked`（選択的移植: `RefLawsAOps`/`AdmCtx`/`Laws`/… に触れる宣言と移植済み名に触れる宣言だけを接尾辞 `X` で移植し、残りは import した原本を使う。スクリプト `scripts/s2s_port2.py`）。
- S2s5（すべて `kjob lake build` exit 0、sorry なし）: `ChildPinC`（self-import とマクロ `pssetX` の見出し欠落を修正）、`CallsCloseA`、`CallsGateA`、`CallsGatePin`、`CallsGatePinned`、`ParentRanA`、`ParentTailsA`、`ParentDesignA`、`S1qLinked`（`coreHeadOff_jqcA`）、`S1tFinal`、`S1uSrc`、`S1zClose`（`synth_hftPcieOutByte_finalOffLNLX`）、`S2dKids`（`machineChild_ifaceKX`, `hftCoreCloses_of_kidsKX`）、`S2hHist3`（`hftCoreCloses_of_kidsHX`）、`S2mReach`（手書き: `LeafStepX`/`ReachedX`/`quietRX` が `adm` を持ち、`ropsRX` は `O.adm` を保つ。`AdmDownR` は不要になり削除）、`S2mReach2`（`JQHRX`, `jqhr_headX`）、`S2mReach3`（`hftCoreCloses_of_kidsRX`）、`S2nAdm`（下記 44.6）。`scripts/s2s_step.sh` と `scripts/s2s_late.txt` が移植順の記録。
- 未移植: `ImplCorA`、`LinkA`、`LoopsCP`（経路上のどのファイルも import しない）。`Bridge`・`EntryReadsLinked` は原本のまま使い、`RealChildAX` 等は移植済みの版を参照する。
- 名前付きのまま未供給: `DRowEnvRX`、`DiagEnvRX`、`TeleRX`（テレスコープ族 `RefLawsATeleX` が追加された境界）、`ProfStepRX`、`ProfOffW`。

### 44.4 Check39（`kjob lake build Tests.Gen5.FGCircuitPilotCheck39`）
Check33 と同一の比較関数 `cmp`（肯定と全 mutant で同じ）。SIGNATURE: `core_tripleA_mainX` の完全な型（binder 名 `mctx mref cctx cref O hA T declName`）を独立に書いた文面と照合、6 mutant 棄却（`AdmCtx` の文脈、旧 telescope bundle、telescope 前提なし、exception 事実なし、事前条件自明、事後条件自明）。STEPS: 移植済み 7 定理の型は `RefLawsAOpsX` を含み `AdmCtx`・旧 `RefLawsAOps`/`RefLawsATele` を含まない（対照: 元の定理は含む、`RefLawsAOps.toX` は `adm := AdmCtx quiet`）。**構造検査は型の表面の定数の走査（surface scan）で、証明閉包の検査ではない。`ReachedX` は葉の閉包の過大近似で実トレースではない。** AXIOMS: 7 名、`contains` で存在を確かめてから `collectAxioms`（存在しない名前を検査済みと報告しない）。REMAINING: 上記の未移植リスト。

### 44.6 目標 `hftCoreCloses_of_kidsR''`（S2s5）
`Tools/ShippingFGCircuitS2sAdmS2nAdm.lean`:
- `hftCoreCloses_of_kidsR'' (L : LawsX mref cref) (hstart : StartX L mctx cctx w) (hcell) (hrH hrT hg) (hD : DRowEnvRX L.O …) (hG : DiagEnvRX L.O …) (hT : TeleRX L.O …) (hs : ProfStepRX L.O w) (h0 : ProfOffW mref cref w) : HftCoreCloses mctx mref cctx cref w`。S2m の `hftCoreCloses_of_kidsR` から `hdown` を除き、`hadm` は `hstart.1`（`L.O.adm mctx cctx`）になった。理由: 文脈の述語 `L.O.adm` は bundle の欄で、文脈の更新で閉じている（`CtxClosed`）ので、強化した quiet 述語 `quietRX` の bundle `ropsRX` は `adm := O.adm` をそのまま使え、`quietR` の文脈から `O.quiet` の文脈への変換（`AdmDownR`）が要らない。
- root の `mkMetaContext` の証拠と実際の run の文脈の結合: `AdmRootX O := ∀ cctx, O.adm mkMetaContext cctx`。既存の bundle の特殊化では `admRootX_toX`（`mkMetaContext_canUnfold` から証明）、一般の bundle では `admRootX_of_none`（`canUnfold? = none` の文脈をすべて許す `adm`）。`startX_of_root` が `StartX L mkMetaContext cctx w` を `AdmRootX` と深さ 0 のキャッシュ不変式から作り、`hftCoreCloses_of_root` は文脈を実際の root 文脈 `mkMetaContext` に固定した版。
- 標準 axiom のみ（`#print axioms`）。
- Check39 を拡張: 目標の完全な型を独立に書いた文面と同じ比較関数で照合し、mutant 5 件を棄却（開始条件なし・telescope 前提なし・profile 前提 `h0` なし・結論自明・kids の gates なし）。型が `LawsX` を含み `AdmDownR`・`AdmCtx` を含まないこと（対照: S2m の原本は `AdmDownR` を含む）、path 上の 13 名の axiom（存在確認後に `collectAxioms`）。構造検査は型の表面だけで、証明の閉包ではない。
- 今後: `hD hG hT hs h0` の供給（`DRowEnvRX`/`DiagEnvRX` は run-local の事実、`TeleRX` は `RefLawsATeleX` の強化 quiet 版）。

## 45. S2t（Issue `sparkle-fg-circuit-pilot` の次の束）: 証拠付き `sigOrBV`、`dt_fun` の再証明、Check40、根 `hftObCDT` の再導出と同期測定

土台 `ea597627`。TRUSTED・axiom・sorry・native_decide・新しい law はない。Issue の状態は変えていない。S2r（最終文 v2）・S2s（AdmBoth）のファイル名は作っていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**（`EnvDefs`/`EnvCtors`/`RecFact` は未供給: 下）。副ブランチ `s2q-exp-or` の無制約な第 2 型引数はコピーしていない（参照のみ）。

### 45.1 規則 `DT.sigOrBV`（reviewer 設計裁定のとおり）と証拠 `natEvalE`

- `HOr.hOr` の型引数 3 つ: 第 1・第 3 は `Signal d (BitVec w)`、インスタンス `instHOrSignalBitVec d w`、**第 2 は `Signal d (BitVec wb)`（同じ `d`）で、`wb` は閉じた Nat 式、証拠 `hwb : natEvalE wb = some W`（`Eq.refl`、カーネルが評価）**。`d`/`w` は同じ `ρ` で `D`/`W` に導出（`hd`, `hw`）、両 operand は `Signal D (BitVec W)` に導出。
- `natEvalE`（`S2iDT`）: `OfNat.ofNat Nat n (instOfNatNat n)` と `HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) x y` だけを評価（変数・他の関数・他のインスタンスは `none`）。`natEvalE_8`、`natEvalE_add88`（`8+8 ↦ 16`）は `rfl`。**`8+8` と `16`、`24+8` と `32` の表記差は許し、幅の違いは `some W` の等式でカーネルが拒否する**（meta の `isDefEq` は証拠ではない: 生成器の `Meta.evalNat` は事前検査のみで、証拠はカーネルが検査する `Eq.refl`）。
- 意味: `Tools.ShippingFGCircuitS2qBits.or_at`（`rfl`、任意の `t` で `(av ||| bv).val t = av.val t ||| bv.val t`、axiom は propext/Quot.sound のみ）。Bool の OR（`sigOrBool`）や混合定数インスタンス（`instHOrSignalBitVec_1`、`instHOrBitVecSignal`）とは別規則。
- `dt_fun` を再証明（`sigOrBV` の 1 ケース。`sigOrBool` とはインスタンス名・型引数の `injsT`/`clashT` で重ならない。`viaSh`/`viaVar` とは `HOr.hOr` が `stopD` の頭（`directHead`）なので `viaOK` が偽で重ならない）。標準 axiom のみ。
- 生成器（`S2iGen`）: `HOr.hOr` かつインスタンスが `instHOrSignalBitVec` のとき、第 2 型引数を `Signal d (BitVec wb)` に分解し（同じ `d` でなければ失敗）、全体を期待する式との等式で検査し、operand の型と `W` の一致、`wb` の評価値と `W` の一致を検査してから規則に渡す。生成器が構文を正規化することはない（`wb` は元の式のまま引用して規則に渡す）。テスト用に `St2.lax`（`deriveTermLax`）で生成器自身の検査を切り、誤った要求をカーネルに直接渡せる。

### 45.2 Check40（`Tests/Gen5/FGCircuitPilotCheck40.lean`、軽量、`kjob lake build`）

出力 28 行（`ok` を含む行）: AXIOMS 1、正 6（`8+8` vs `16`、`24+8` vs `32`、`16` vs `16`、`2+3` vs `5`、領域の束縛変数の下、Bool OR は別規則 `sigOrBool`）、**G（生成器の拒否）12、K（生成器の検査を切ってカーネルが拒否）9**。正と負は同じ報告文（`expectErr`: 導出されない・定理が追加されない・期待した文字列）。
- G と K の両方: 相違幅（operand）、`8+8` vs 32、別領域（第 2 型引数）、別領域（operand）、第 2 型引数が `Nat`、`Signal Bool`、結果幅の変更、第 1 型引数の変更、開いた幅（変数）。K の行は `(kernel)` のエラーで終わる（カーネルの型検査が止めている。生成器の不具合では通らない）。
- G のみ（インスタンスの名前が別なので規則の入口に入らない）: 混合定数 2 種、Bool インスタンスを BitVec operand に。
- Check29（正 8 + 制御 4 + AXIOMS）、Check36、Check38 は変わらず通る（再実行済み）。

### 45.3 根 `hftObCDT` の再導出（承認済み規則のみ、`Tools/ShippingFGCircuitS2tHft.lean` / `S2tHftOb.lean`、`kjob lake build`、timeout なし）

| 項目 | 値 |
|---|---|
| 止まり | **0**（S2q の `HOr` 2 件は `sigOrBV` で解けた） |
| DT 節点 / Sh 歩数 / viaSh | 5533 / 74392 / 980 |
| 生成時間 / 表 | 2599 ms / 55 defs・11 ctors（53 ms） |
| **kernel（同期 `addDeclCore`）** | **6882 ms** |
| 項 DAG / tree | **737 294** / 約 7.08×10^76 |
| ピーク RSS（カーネル検査後、Lean 環境込み） | 3 279 072 kB |

`#print axioms`: `hftObCDT_of_tablesT`・`hftObCDT_T` ともに propext/Classical.choice/Quot.sound のみ。`hftObCDT_T : ∀ env (hΔ : EnvDefs env Delta) (hΓ : EnvCtors env Gamma) (hrec : RecFact env), HftObCDT env`。副ブランチの数字（7283 ms、DAG 737 288）と同じ桁で、この作業ブランチ上で独立に測り直した値。
**`hcd` は無条件には解けていない**: `HftObCDT env` の導出は `EnvDefs env Delta`（55 defs）、`EnvCtors env Gamma`（11 ctors）、`RecFact env`（`env` がこれらの定義・構成子・`rec` の事実を持つこと）に条件付き。

### 45.4 §36.4 の訂正

§36.4 の「小例で再現しなかったことは測定済み」「同じく分解能以下」は撤回した。同期で再測定していない小例の検査時間は**不明**で、DAG サイズの観測（二次）とは別。同期で測ったのは根のみ（§43.4 と §45.3）。

### 45.5 仮説・次

名前付き仮説（未供給）: `EnvDefs/EnvCtors/RecFact`（`hftObCDT_T` の前提）、`HftRootLink`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws/Start/hr`、`Sh` と置換規則の対応（監査）。次: 新 Off 入口・同一 env の最終 carrier への接続（`HftFinalStmtS` は型別名のまま）。

## 45′. S2u（Issue `sparkle-fg-circuit-pilot` の次の束）: 固定した期待型の kernel wrapper — 「どの入力の、どの結果の証明か」を独立に照合する

（注: 番号の重複。この節は S2u の §45。S2t の §45 は直前の節。）

土台 `ea597627`（par/fgc-s1）。追加: `Tests/Gen5/FGCircuitPilotCheck41.lean`（lakefile に登録 1 回）。変更: `Tools/ShippingFGCircuitS2bGen.lean`（引用 cache の厳密化、1 箇所）、`Tests/Gen5/FGCircuitPilotCheck29.lean`（`want` の文言）、本書。`S2iDT`/`S2iDTFun`/`S2iGen` は触れていない。TRUSTED・axiom・sorry・native_decide・新しい law はない。Issue の状態は変えていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は条件付きのまま。

### 45.1 何が問題だったか（reviewer 指摘）

`deriveRootT` は定理の宣言型を **自分の本体の `inferType`** から作る。したがって kernel が受理しても、「その定理が**どの入力 `Expr` の、どの結果**についてか」は何も確かめられていない。Check29/36/38 の報告は存在と axiom だけで、別の入力・別の結果の正しい証明を返す生成器を検出できなかった。

### 45.2 Check41 の方式（正と負で同じ手続き）

- コマンド `fixed_dt accept|reject "TAG" T input α v`: 期待型 `∀ env (hΔ : EnvDefs env T.Delta) (hΓ : EnvCtors env T.Gamma) (hrec : RecFact env), DT env [] input (Res.val α v)` を**手で書き**、`theorem T.fixed : <期待型> := T` を **kernel**（同期の `Environment.addDeclCore`）に出す。型の不一致は kernel の「declaration type mismatch」。`accept` は受理、`reject` は拒否（と定理が追加されないこと）を要求し、報告文と kernel 呼出しは同じ。
- 入力 `Expr` は生成器に渡した式（`appN` 等の補助）とは**別に**、生の `Lean.Expr.app/lam/const/…` の構成子で引用し直した。結果の型 `α` と値 `v` は普通の Lean の項（`BitVec` は `BitVec.ofNat`、`Signal` は `Signal.pure`）。結果は `Res.val α v` に入るので、結果の型の取り違えも拒否される。
- **α 同値の引用 cache（修正）**: `S2bGen.qE` の cache は `Expr` の `BEq`（α 同値、束縛名を無視）で引いていたので、束縛名だけが違う式が同じ引用を返し、**生成物の入力の `lam` の名前が元の `Expr` と変わった**（Check41 の ALPHA 例 `Prod.mk ((fun x => x) false) ((fun y => y) true)` の accept が「declaration type mismatch」になり、この cache 以外に原因が無いことを確認した。§43.2 の「引数側の修正」は根の引用そのものには効いていなかった）。修正: cache は元の式を一緒に保存し、`Expr.equal`（束縛名・binder info まで厳密）が成り立つときだけ hit とする。厳密等価で扱う方針（証明された接続ではなく、等価の判定そのものを厳密にした）。ALPHA の accept（x / y）と reject（y / x に入れ替えた α 同値だが等しくない入力）が、同じ手続きで kernel に区別される。
- 副作用: Check35 の項 DAG が各 n で +1（613/1085/…）。cache の hit が厳密になった分。

### 45.3 確認したこと（`kjob lake build Tests.Gen5.FGCircuitPilotCheck41`、exit 0、928 jobs、エラー 0）

- AXIOMS ok 1 行。生成 16 例、`accept` **16**、`reject` **25**。すべて標準 axiom のみ。
- accept（固定した入力・結果）: SHARE = (false,false)、SHADOW = (true,false)、HIGHER = (true,false)、REC-NIL = false、REC-CONS = true、REC-IH = false、ALPHA = (false,true)（名前 x / y）、値頭 VALHEAD = false、VALHEAD-NEST = (true,false)、BitVec: EXTRACT 8/6/1 of 5 = 0#1、EXTRACT 16/3/10 of 1021 = 127#10、SHL 16: 3<<<8 = 768#16、SHL 16: 3<<<20 = 0#16（移動量 ≥ 幅）、SHL 32: 3<<<4 = 48#32、APPEND 8+8: 1#8 ++ 2#8 = 258#16、APPEND 8+16: 1#8 ++ 2#16 = 65538#24。
- reject（同じ wrapper、同じ kernel 呼出し）: 別の値（SHARE を (true,true)/(false,true)、HIGHER を (false,true)、REC-NIL を true、REC-CONS を false、REC-IH を true、VALHEAD を true、EXTRACT/SHL/APPEND の値違い）、別の入力（SHARE に引数 true、EXTRACT の入力定数 4 / オフセット 2、SHL の移動量 7、APPEND のオペランド入れ替え）、捕捉環境の取り違え（SHADOW の内側/外側の入れ替え (false,true)、SHADOW の入力で `#1`→`#0`、VALHEAD-NEST の entry 入れ替え (false,true)）、結果の型違い（REC-NIL を (Bool×Bool)、EXTRACT の幅 2、APPEND の幅 8+8 / 8+16）、ALPHA の束縛名入れ替え。
- Check29（13 行 ok）/ Check36（7）/ Check38（23）は S2bGen の修正後も変わらず通る（それぞれ exit 0、エラー 0）。
- 限界（正直な記録）: 幅 32 の `3 <<< 40` を値として kernel に比較させると «deep recursion» になった（受理・拒否のどちらも判定できない）ので、32 ビットは移動量 4 の例にし、移動量 ≥ 幅は 16 ビットの例にした。32 ビット・移動量 ≥ 幅の固定期待型は**未確認**。
- 生成器が出す定理の中身が「意図した」意味と一致するかは、ここでは**期待型として書いた私の値**が基準である（Lean の `BitVec`/`Signal` の演算の kernel 評価と定義等価であることを kernel が確かめる）。これは `Sh` と置換規則の対応（監査）や、`hftRootValue` 全体の意味保存の証明ではない。

### 45.4 測定の訂正（S2u）

- Check35 n = 4..24 の同期 kernel 保存ログは 37/43/53/62/74/90 ms。§36.4 の表の旧「0 ms」をこの値に置換した。再実行（S2u）は 43/40/60/59/67/82 ms（ばらつく）。これは**小さな共有連鎖**の時間であり、**根の時間（7283 ms、§43.4、副ブランチ・未承認 `sigOrBV` 前提）ではない**。
- Check41 の同期 kernel 時間（生成器が定理を出すとき）: SHARE 33、SHADOW 32、HIGHER 43、REC-NIL/CONS/IH 42/42/50、ALPHA 38、VALHEAD 4、VALHEAD-NEST 10、EXTRACT 10/6、SHL 5/6、APPEND 7/8 ms。旧 §41.4/§36.4 の「kernel 0 ms」は無効。
- Check29 の `want`（「必須 counter」と読める文言）は、実際には**表示のみ**で、カウンタは検査側に届いていない。assert はせず、文言を「情報としてのラベル、assert していない」に直した（`Tests/Gen5/FGCircuitPilotCheck29.lean`）。どの規則が使われたかの独立な確認は、Check41 の固定した期待型（結果が規則を通さないと得られない値）に置き換えた。

### 45.5 残ること

- **S2t の根（`hftRootValue`）には、元の `hftRootValue` と期待値を固定した `HftObCDT` wrapper（同じ `fixed_dt` 方式）を必須にする**。この束では根を扱っていない（S2t の担当）。
- 名前付き仮説（未供給）は §43.6 のまま（`hcd`、`EnvDefs/EnvCtors/RecFact`、`HftRootLink`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws/Start/hr`、`Sh` と置換規則の対応（監査））。

## 46. S2v（Issue `sparkle-fg-circuit-pilot` の次の束）: `HftRootLink` を証明した、`hlink` を除いた最終文 `HftFinalStmtOffCombined3`、Check42

土台 `cb405fd8`。Issue の状態は変えていない。S2s/S2t/S2u のファイルには触れていない。追加: `Tools/ShippingFGCircuitS2vLink.lean`、`Tests/Gen5/FGCircuitPilotCheck42.lean`。書き換え: `Tools/ShippingFGCircuitS2kLink.lean`（S2k の草稿。コンパイルするようになった）。lakefile は末尾に 2 行追記。sorry・native_decide・axiom・TRUSTED・新しい law はない。`maxHeartbeats` の局所上書きは Check42 の `run_cmd`（64000000、Check37 と同じ値）のみ。証明側（S2kLink/S2vLink）は既定のまま。

### 46.1 結果: `HftRootLink` は証明済み

`Tools.ShippingFGCircuitS2kLink.hftRootLink : HftRootLink`（`kjob lake build Tools.ShippingFGCircuitS2kLink` exit 0、axiom は propext / Classical.choice / Quot.sound のみ）。

**S2c §31.5 の止まりの原因（実測）**: 組み立ての中の部分は全て通る。止まるのは最後の 1 文（`link_concl` の適用）だけだった。`diagnostics` では、`machine_states` の型の `teleState` を含む `typedVal` の定義的同一視で `TeleT.at`/`happendT`/`tys`/`Tele.valsOf`（数万回）が展開されていた。2 つの原因が重なっていた:
1. `machine_states` の型は `machineInners` を**展開した形**で持つが、私たちの状態列 `sg t` は `teleState machineInners …` と書かれる。この 2 つが `typedVal` の引数に入ると、単一化が `L` を展開せず状態を評価する。
2. 目標の `(GenIn.mk … ).d.nIn` 等（構造体射影）と `machineData.nIn` の同一視で、`machineData` の delta 展開が先に選ばれる。

**修正（S2c の計画どおり「抽象変数」にする）**:
- `states_abs`（S2kLink）: `machine_states` の結論を、融合状態を**抽象列 `X : Nat → HList (tys d.ss)`**（`X t = teleState L hss … t` の等式つき）に書き直す一般補題。`L` は一般変数なので、`machine_states` への適用は構文的一致で済む（`src` だけは `fun i b bi => machineSource i b bi` と明示。メタ変数のままだと高階単一化が止まる）。以降の `hext`/`hagree`/`hSg` は `X`（= `sg`）だけを使い、`machineInners` は `X t = teleState machineInners …` の 1 本の変換（`hsg'`）でしか現れない。
- `link_concl`（S2k の草稿どおり）: `TVal` を抽象変数にした結論部の独立補題（`outs_tagree` から）。
- 最後は `rw [monoObs_root]` のあと、目標と `key` の**両方に `dsimp only`**（`GenIn.mk … .d` の射影を落とす）してから `exact key`。

### 46.2 `hlink` を除いた最終文（binder 前後）

`Tools.ShippingFGCircuitS2vLink.HftFinalStmtOffCombined3`（`synth_hftPcieOutByte_finalOffCombined3_{Z,Y,X}`、`kjob lake build Tools.ShippingFGCircuitS2vLink` exit 0、axiom は標準のみ）。証明は `synth_hftPcieOutByte_finalOffCombined2 … hftRootLink …` の 1 行。

| | 一覧 |
|---|---|
| 前（v2 `HftFinalStmtOffCombined2`、19） | `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd hadm hdown hD hG hT hs h0 hkgfacts` |
| 後（v3 `HftFinalStmtOffCombined3`、18） | `L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd hadm hdown hD hG hT hs h0 hkgfacts` |

残る名前付き仮説: `hadm hdown hD hG hT hs h0`（FG D.T-4m6…m5）、`hkgfacts`（D.T-4g）、`hcd`（S2b/S2i）、`hreadH/hreadT`、`hchk`、`CellPrem`、`Laws/Start/hr`。**`hlink` は仮説でなくなった**。

### 46.3 `machine_states` の完全型（レビュアー指摘）

- 一般補題 `machine_states_of_tele_ext` の完全な型を、独立に書いた `ExpStatesGen` と `FGCircuitCmp.stmtEq` で照合（binder kind を全深さで、instance binder も含む）。
- 特殊化 `Tools.ShippingFGCircuitS2vLink.root_states`: 根について、`S₂`/`Ss`/融合状態列 `X`（`X t = teleState machineInners root_hss …`）、初期状態 `X 0 = castSS … (happendT … machineInits …)`、遷移 `X (t+1) = evalTerms … machineExt … nexts`、観測 `machineSource = outs`。`ExpRoot` と照合。`root_hss`（`[bits 6] ++ machineInners.sss = machineData.ss`）は名前付き定理（`show … from rfl` は証明項の扱いが比較で非対称になる）。
- `synth_hftPcieOutByte.machine_states` の値の頭が一般補題の適用であることと、`root_states` の証明項が `machine_states` と `states_abs` を使うことを検査。
- 注意: 生成された `machine_states` 自体の型（`machineInners` を展開した巨大な形）との**直接の**文面照合はしていない（S2c と同じ理由。ここでは一般補題 + 特殊化に分けた）。

### 46.4 Check42（`kjob lake build Tests.Gen5.FGCircuitPilotCheck42`）

`FGCIRCUIT42` 出力 4 行（SIGNATURES-FINAL3、SIGNATURES-LINK、SIGNATURES-STATES、AXIOMS）。比較は Check37 と同じ `normCommon` + `FGCircuitCmp.stmtEq`（正例も mutant も同じ関数）。
- FINAL3: `_Z/_Y/_X` の完全な型を、Check37 の独立な `ExpFinal2` 族から `HftRootLink` の binder だけ取り除いたもの（`dropLink`）と照合。mutant **75**: Check37 の 66 個（`dropLink` 同様）＋carrier 3、v2（`hlink` つき）の文面、実際の v2 定理の型、旧い最終文 5。
- LINK: `hftRootLink` の型を独立に書いた `ExpLink` と照合、mutant 3（初期状態の前提なし、`GenIn` データ前提なし、観測が `t+1`）。
- STATES: 一般補題 `ExpStatesGen`（mutant 3）、`root_states` `ExpRoot`（mutant 3）。
- AXIOMS: 最終文 3、`hftRootLink`、`link_concl`、`states_abs`、`root_states` が標準 axiom のみ。

### 46.5 範囲と正直な注意

- `ExpLink`/`ExpStatesGen`/`ExpRoot` は元の文面の**書き写し**（同じ人が書いた別の記述）で、独立性は文面の別記述に限る。
- 生成器・IR/SV は変えていない（`Tools/ShippingMachineCommand.lean` は未変更）。
- 名前付き仮説からは `hlink` だけが消えた。7 仮説 + `hkgfacts` 等は未供給のまま。
- ビルドの所要: S2kLink 約 4 分（依存の再ビルド込み）、モジュール自体は約 1 分以内。scratch では、isolated build の `.olean` に `lean` を直接かけて数秒で反復した。

### 46.6 台帳

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

パイロット最終文の未供給 binder: `hlink` 1 件を解消し、19 → 18（台帳の行数とは別欄）。他は仮説のまま。

reviewer 訂正（2026-11-07）: FG の減算はしない。D.D-3（GP carrier）は台帳 8649968e の scripts/gen2/PREMISE_LEDGER.md §12.16 GPFIX（ad239809）で既に減算済みで、§12.24 の FG 75 に反映されている。`HftRootLink` はこの非 leaf root 固有の意味接続の残義務で、解消は実質的な進歩だが、未解消の FG 行 1 件と一対一に対応しないので D.D-3 を二度引かない（初版の「FG 74（今回 FG -1）」は誤り）。

## 47. S2w（Issue `sparkle-fg-circuit-pilot`）: 共通比較器 `FGCircuitCmp` の修正（reviewer 変更依頼 1・2）と回帰対照

土台 `cb405fd8`。変更: `Tests/Gen5/FGCircuitCmp.lean`、新規 `Tests/Gen5/FGCircuitCmpRegress.lean`（lakefile 登録 1 回）、Check37 の文言、§42 の文言。定理・Check の mutant 集合は不変。新しい law・axiom・TRUSTED・sorry・native_decide はない。Issue の状態は変えていない。

### 47.1 比較器の変更
- **証明無関係を型で決める**: 旧版は定数名が `_proof_` で始まるだけの項を `proofIrrelevant` に置換していた（`def _proof_a : Nat := 0` と `def _proof_b : Nat := 1` が同じ項に消える偽陽性。Lean kernel の欠陥ではなく期待型照合の偽陽性）。名前判定を**削除**。置換は、頭が定理（`thmInfo`）または `Eq.refl`/`rfl` の適用で、かつ `Meta.isProof`（型が `Prop`）が成り立つ項だけ。置換先は `proofIrrelevant P`（`P` はその型。命題の情報を保つ）なので、別の命題の証明は別の項のまま。`Meta.transform` は束縛変数を fvar で開くので `inferType` が未束縛 bvar を見ない（推論が失敗した項は保持）。型で正当化できないもの（データの `def`）は保持。
- **`litBool?` と `OfNat`**: `BEq.beq Nat inst a b` は `inst` が `synthInstance (BEq Nat)` と構造一致または default の `isDefEq` で一致する場合だけ数値の `==` として評価。`OfNat.ofNat Nat n inst` は `inst` が `instOfNatNat n` と一致する場合だけ raw literal に。非標準（常に `false` の `BEq Nat`、別の `OfNat` instance）は標準と同一視せず、項を保持する（`if` は選ばない）。`litBool?`/`iteLit` は MetaM になった。
- `stmtEq` 本体は unfold も `isDefEq` もしない（`Expr.eqv` と全深さの binder kind）。unfold/whnf/instance 確認は前段の `normCommon`（両辺に同じに適用）が行う。この区別を `FGCircuitCmp` と §42 の説明に明記した。

### 47.2 回帰対照（`FGCircuitCmpRegress`、`run_cmd` 内）
- `_proof_a`/`_proof_b`（Nat、値 0/1）は**別**（単独でも `Nat.succ` の下でも）。
- 同じ命題の証明 2 つ（`rfl` / `by decide`）は**等しい**。別の命題の証明は**別**。束縛変数の下の証明（型が束縛変数を含む）も同様に動く。
- 標準 `BEq Nat`: `if 3 == 3` は then、`3 == 4` は else。常に `false` の `BEq Nat` は標準扱いされず（`3 == 3` を選ばない）。標準 `OfNat Nat` は raw literal、`⟨n+1⟩` の custom instance は raw literal と**別**。
- 出力: `FGCIRCUITCMPREGRESS controls: all passed`。

### 47.3 再実行した Check（同じ修正版の比較器、提出 SHA で 1 つずつ `kjob lake build`）
Check21 / 26 / 27 / 28 / 30 / 31 / 32 / 37、すべて build 成功、AXIOMS は標準のみ。mutant 棄却数は変更前と同じ（Check21 は 3/3、Check37 は完全型 73 ほか）。

### 47.4 文言
Check37 の REMAINING と docstring、§42 の「7 run-local」を一括で `quiet+ReadsAt+Reached` と呼ばない形に直した（量化範囲は DRow/Diag、ProfStep、ProfOff、Tele、admissibility で違う）。

### 47.5 S2x: `litBool?` の標準 `BEq Nat` を固定した定義に（reviewer 変更依頼）
- **変更**: `litBool?` は `synthInstance (BEq Nat)` を使わない。標準 instance は定数項 `stdBEqNat := instBEqOfDecidableEq Nat instDecidableEqNat` の引用（`FGCircuitCmp`）で、local/global の instance 登録に依存しない。`isStdInst`（構造一致、または default の `isDefEq`）で比較する。`OfNat` は従来どおり `instOfNatNat n` の引用。標準判定のどこにも環境依存の instance 検索はない。
- **回帰対照**（`FGCircuitCmpRegress`）: 非標準の `badBEq`（常に `false`）を `attribute [local instance 2000] badBEq` で section 内に**登録**する。前提として `synthInstance (BEq Nat)` が `badBEq` を返すことを確認し、検索で得た instance での `3 == 3` は then 枝を選ばず、固定した標準 instance では then（`3 == 3`）／else（`3 == 4`）が選ばれる。section の外では `stdBEqNat` が検索結果と一致することも確認（引用が正しい標準 instance である証拠）。出力: `FGCIRCUITCMPREGRESS controls: all passed (... standard/always-false BEq (also with it registered as a local instance), ...)`。
- **再 build**（修正版 Cmp、全 966 jobs 成功、AXIOMS は標準のみ）: Check21 3、26 SIG-A 8、27 SIG-A 13／SIG-C 35、28 CORE 28／FINAL 35、30 SIG-A 9／SIG-B 8、31 FINAL 62、32 9、37 FINAL 73 の mutant を棄却。変更前と同数。

## 48. S2y（Issue `sparkle-fg-circuit-pilot`）: `hftObCDT_T` を v3 の `hcd` へ接続した最終文 v4、Check43

土台 `26fb676a`。Issue の状態は変えていない。S2s*/Check39/§44 のファイル名は作らず、`hdown` には触れていない。追加: `Tools/ShippingFGCircuitS2yFinal.lean`、`Tests/Gen5/FGCircuitPilotCheck43.lean`（lakefile 末尾に 2 行）。sorry・native_decide・axiom・TRUSTED・新しい law はない。FG は狭めていない。

### 48.1 v4 `Tools.ShippingFGCircuitS2yFinal.HftFinalStmtOffCombined4`

v3 `HftFinalStmtOffCombined3` の `hcd : Ob (envAt cref w)` を、**同じ環境 `envAt cref w`・同じ Off 入口・同じ root・同じ値（`hftRootValue`）・同じ出力の carrier** のまま次の 3 つに明示置換した。carrier は `hftObCDT_T` が作る T: `cdvT := fun env e α v => CDT env [] e α v`（`HftObOf cdvT env` は定義上 `HftObCDT env`）。
- `hΔ : EnvDefs (envAt cref w) hftObCDT_of_tablesT.Delta`（55 defs）
- `hΓ : EnvCtors (envAt cref w) hftObCDT_of_tablesT.Gamma`（11 ctors）
- `hrec : RecFact (envAt cref w)`（`List.rec` が `recInfo`）

`synth_hftPcieOutByte_finalOffCombined4 : HftFinalStmtOffCombined4`（`kjob lake build Tools.ShippingFGCircuitS2yFinal` exit 0、974 jobs、axiom は propext / Classical.choice / Quot.sound のみ）。証明: `synth_hftPcieOutByte_finalOffCombined3 cdvT HftObCDT (fun _ h => h) … (hftObCDT_T _ hΔ hΓ hrec) …` の 1 つ。Z/Y/X 版ではなく T 版 1 つ（v3 の `Ob`/`CV` 引数をそのまま使った）。

### 48.2 binder の前後

| | 一覧 |
|---|---|
| 前（v3、18） | `L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd hadm hdown hD hG hT hs h0 hkgfacts` |
| 後（v4、20） | `L lvl env₀ hstart hr hcell hchk hreadH hreadT hΔ hΓ hrec hadm hdown hD hG hT hs h0 hkgfacts` |

`hcd`（不透明な `Ob` 一般）が消え、中身のある 3 条件に具体化された。binder の**個数**は 18 → 20 だが、未供給の内容は「1 つの CDT 導出の存在」から「環境が 55 defs / 11 ctors / `List.rec` を持つこと」という有限の環境事実に変わった。個数の減少は主張しない。

### 48.3 供給した条件と仮説として渡した条件

- **供給（証明）**: `HftObCDT env` そのもの（`hftObCDT_T`: 5533 節点の導出を `hΔ hΓ hrec` から組み立て）。`hcd` はこれで置き換えた。
- **仮説のまま渡した（3 つとも）**: `hΔ` `hΓ` `hrec`。
- **v4 の既存仮説からの導出: 現時点では供給していない**（reviewer 訂正 2026-11-07: 初版の「導けない」「よって新しい前提が要る」は断言しすぎ。`RunsTo` の結果型に問い合わせの事実が出ないことは、run の分解から導けないことの証明にならない。非導出を言うなら既存仮説をすべて満たす反例が別に要る）。調べた範囲: `hstart`（`AdmCtx ∧ JQC`）、`hr`（`RunsTo` の run）、`hchk`（`CheckedStart`: `root`・`gates`・`reader` と `ReadsAt env₀ cref w`）、`hreadH/hreadT`（`RootReader`）はいずれも root の定数 1 つ（`env.find? hftRoot`、`entryGatesB`、`dataOfAt` の出力）と環境の導出引数の一致だけを述べ、`Delta` の 55 定数・`Gamma` の 11 構成子・`List.rec` の `env.find?` は述べない。`hr` の run が行う `getConstInfo` はこの文の中に事実としては出てこない（run の結果型 `(b, D')` と `PostRunOff` を通すだけ）。run の分解からの導出は試していない。**追加の law/TRUSTED は足していない**。`RecFact` は「`List.rec` が recInfo」という標準 Lean 環境の事実だが、任意の `Environment` 値については証明できないので仮説のまま。

### 48.4 Check43（`kjob lake build Tests.Gen5.FGCircuitPilotCheck43`、exit 0、983 jobs）

比較は Check37/42 と同じ `norm37` + `FGCircuitCmp.stmtEq`（正例も mutant も同じ関数、binder kind を全深さで）。独立に書いた `ExpFinal4`（Check37 の `ExpFinal2` から `HftRootLink` を除き、`hcd` を 3 条件に、各条件に環境 knob）と `synth_hftPcieOutByte_finalOffCombined4` の完全型が一致し、**mutant 41 を棄却**（出力 `FGCIRCUIT43 SIGNATURES-FINAL4 … 41 mutants rejected`、`FGCIRCUIT43 AXIOMS: 2 names, standard axioms only`、AXIOMS の前に両名の存在を確認）。
- 環境の取り違え: 各条件（defs/ctors/rec）の環境を終了 world `eE` / `env₀` に（6）、3 つ全部を `eE`/`env₀` に（2）、run と無関係な world に（3）、結論の環境 2 つと reach の環境の取り違え（3）。
- root / 値 / carrier: root・post root・出力 shape の変更（3）、carrier を Z/Y/X/old/old artifact に（5。T の代わりに Z/Y/X を使うと不一致）、diag 入口。
- 条件: 3 条件を 1 つずつ落とす（3）、3 つ全部を落とす、`Delta`/`Gamma` を空表に（2）、`hcd` を追加で残す（同じ env・終了 world・`hcd` のみ、3）、他の premise の削除（adm、kgf、c1、c2）、`hlink` の再追加。
- 旧文: v3 Z/Y/X と v2 Z の完全型（4）。
- 値を差し替える mutant は無い（reviewer 訂正 2026-11-07: 初版の「`keepHcd` の内側で作れている」は誤り。`ExpFinal4` の `keepHcd` の内側でも `hftRootValue` と `synth_hftPcieOutByte` は固定で、値を変える knob も実例も無い）。`keepHcd` は `hcd` 併存の対照で、値変更の対照ではない。3 条件は値を述べない（値は `hftObCDT_of_tablesT` の導出に固定）。`ExpFinal4` は v3 の文面の別記述であり、`Delta`/`Gamma` は生成物なので名前で参照している（表の中身の監査は §45 の通り別）。

### 48.5 台帳

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。台帳の行は減らしていない（reviewer が決める）。パイロット最終文の binder は 18 → 20（`hcd` 1 → `hΔ hΓ hrec` 3）。成果は引き続き**条件付き**。

## 49. S2z（Issue `sparkle-fg-circuit-pilot`）: v4 の環境 3 条件を入口の検査から供給した v5、Check44

土台 `f533cd16`。Issue の状態は変えていない。S2s*/Check39/§44/`hdown`/`AdmBoth` には触れていない。sorry・native_decide・axiom・TRUSTED・新しい law は無い（標準 axiom のみ）。

### 49.1 検査（step 1、純粋）
`Sparkle/Compiler/EnvTableCheck.lean`: `defsOkB`/`ctorsOkB`/`recOkB`。環境の `find?` を読み、定義の levelParams と value（`ExprDecEq.exprDecEq`）、構成子の `induct`/`numParams`/`numFields`、`List.rec` が recInfo であることを `EnvDefs`/`EnvCtors`/`RecFact` が述べるとおりに比べる。`Tools/ShippingFGCircuitS2zEnvCheck.lean`: `hftEnvCheckB_sound : hftEnvCheckB env = true → EnvDefs env Delta ∧ EnvCtors env Gamma ∧ RecFact env`（同じ `env`、`Delta`/`Gamma` は `hftObCDT_of_tablesT` の表、55 defs / 11 ctors）。Check44 A: 実環境（root を含む）で true、行の値・levelParams・存在しない定数・numFields・numParams・inductive・種類の取り違え・`Init` だけの環境で false。

### 49.2 入口の検査（step 2）
- `Sparkle/Compiler/PilotEnvTables.lean`（生成物・非信頼。生成器 `Tools/ShippingFGCircuitS2zGenTables.lean`）: 表の行を Lean のソースにしたもの、`startEnvOk declName env`（pilot root なら表と環境を照合、他の宣言は true）。
- `Tools/ShippingFGCircuitS2zPin.lean`: 生成した行が `hftDeltaL`/`hftGammaL`（= `Delta`/`Gamma` の行）と一致することを kernel（`decide +kernel`）で証明。`startEnvOk_sound : startEnvOk hftRoot env = true → EnvDefs ∧ EnvCtors ∧ RecFact`。注: 生成器の初版は `Expr` の `BEq`/`Hashable`（束縛名を無視する）で共有を畳んでいて kernel の照合に落ちた。構造全体（束縛名を含む）で畳むように直した。
- `Sparkle/Compiler/Elab.lean`（+3 行）: `synthesizeCombinationalCoreOff` の既存の `entryInlinerError?` の枝の後に `else if !(startEnvOk declName env) then throwError …`。失敗は誤り（黙った fallback なし）。`Tools/ShippingFGCircuitS1qLinked.lean` の写し `coreRestOff` と `core_chainOff` を同様に直し、`core_envOkOff`（成功した core run は `getEnv` の結果 `envR` で検査を通した）を追加。
- `Tools/ShippingFGCircuitS2zFinal.lean`: `startEnvOk_of_run`（`hcell` と Off の run から `startEnvOk hftRoot (envAt cref w) = true`。head・`getConstInfo`・`getEnv` が Core の環境を保つ `headAtOff_of_cellPrem`/`envFrame_getConstInfo` を使う）。`HftFinalStmtOffCombined5` / `synth_hftPcieOutByte_finalOffCombined5` = v4 から `hΔ hΓ hrec` を除いた文。

### 49.3 binder の前後
v4（20）`… hreadT hΔ hΓ hrec hadm …` → v5（17）`L lvl env₀ hstart hr hcell hchk hreadH hreadT hadm hdown hD hG hT hs h0 hkgfacts`。`hΔ hΓ hrec` は仮説でなくなった。代わりに入口の検査が compile の成功の一部になった（pilot root 以外の宣言は検査なし）。台帳の減算は reviewer が決める。

### 49.4 出力の同一性と時間
同じ build の中で root に対し `synthesizeCombinationalOff`（検査あり）と変更していない `synthesizeCombinational` を走らせ、module と design の `repr` が一致（77654 / 89425 文字）。前者 315 ms、後者 307 ms（1 回だけの測定で、検査単独の費用とは見なさない。検査自体の時間は測っていない）。

S2z agent の作業時点（e66f6d63 の commit 前）では、baseline 比較と既存 Check の再実行は未実施だった。統合時（2026-11-07、e66f6d63）に次を行った:
- 既存 Check: kjob-run-src-fgc-m2v-5e11 exit 0（1034 jobs）。S2zFinal と、登録済みの pilot Check 44 個すべて（Check15 など `synthesizeCombinationalCoreOff` の形を見るものを含む）。clean な worktree での Lean 検証（dirty=false）。
- 出力 baseline: S1q と同じ手順（scripts は par/fgc-s1q-cmpnew の `scripts/gen5/fgc_baseline/` を未 commit で worktree に置いた。そのため比較用 Job は dirty=true で、未追跡はこの scripts だけ。主要な測定 script と inventory は par/fgc-s1q-cmpnew 版と同じ）。kjob-run-src-fgc-cmp2z-5d2f（AllTests と IP の build の後に `cmp_profile_off.sh`、CAP_PROFILE=0）を S1q で受理した cmpnew-c2ee と比べると、272 ファイル中 268 の出力がバイト一致、output_baseline.tsv の 50 行の 1–9 列（sha256 含む）が一致、exit は全ファイル一致。残り 4 ファイルは両方とも同じ『IP の olean が無い』エラー（path だけ違う）で、`cmp_rerun4.sh`（kjob-run-src-fgc-cmp2z-2a35）の再取得が cmpnew-3a92 の fgc_cmp_off4 とバイト一致（4 件とも exit 0）。

### 49.5 Check44（`kjob lake build Tests.Gen5.FGCircuitPilotCheck44`、exit 0）
`FGCIRCUIT44 CONTROLS: ok`、`FGCIRCUIT44 SIGNATURES …46 mutants rejected`、`FGCIRCUIT44 AXIOMS: 5 names, standard axioms only`。同じ `FGCircuitCmp.stmtEq`（正例も mutant も）。`hftEnvCheckB_sound`・`startEnvOk_sound`・`startEnvOk_of_run`・v5 の完全型を独立に書いた文と照合。mutant: 検査結果が別の環境・終了 world、表の行を落とす、3 条件のうち 1 つだけを結論にする、検査を別の関数に、root 違い、診断入口、`hcell` 欠落、v4（条件が残る）、条件 1 つだけ残した v5、`hcd` 併存など。

### 49.6 範囲
- pilot root 以外では検査は常に true で、保証は pilot root についてのみ。
- 表の検査は環境の `find?` の事実で、`Environment` 全体の導出ではない。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 50. S3a2（Issue `sparkle-fg-circuit-pilot`、状態は変えていない）: v5 の `hkgfacts` を入口の検査から供給した v6、Check45

土台 `d64e65af`。S2s*/Check39/§44/`hdown`/`AdmBoth` には触れていない。sorry・native_decide・axiom・TRUSTED・新しい law は無い（標準 axiom のみ）。

### 50.1 生成器の修正（S3a が 20 分以上終わらなかった原因）
`Tools/ShippingFGCircuitS2zGenTables.lean` の `internE` は節点ごとに hash-cons するが部分項の cache が無く、共有された `Expr` の DAG を木として歩いていた。部分項そのものを鍵にした memo（`GS.memo`）を足した。鍵は `EKey`: 等号は `Expr.equal`（束縛名・binder info を含む完全な構造。`Expr` 自身の `BEq` = alpha 同値ではない）、hash は `Expr.hash`（束縛名を無視するので、等しい鍵は等しい hash）。ポインタ鍵は使っていない。memo は再計算を避けるためのもの。ただし節点 ID は一般には構造だけで一意ではなく走査順にも依るので、「出力が変わらない」ことの根拠は構造の議論ではなく、今回の生成物のバイト一致と kernel pin（S3aKids）である。確認: 新しい生成器の `genSource` は commit 済みの `Sparkle/Compiler/PilotEnvTables.lean` とバイト一致（184265 バイト、`cmp`）。S2zPin は変更なしに build 済み。
単独 probe（scratch、timeout 付き）: `httpType` 25 節点 1 ms、`httpValue` 296 節点 2 ms、`httpInlValue` 382 節点 2 ms。`Tools.ShippingFGCircuitS3aGenKids` の build は 0.6 秒。生成物 `Sparkle/Compiler/PilotKidTables.lean` は 35781 バイト（6 項の再出力。名前付き定数との比較には切り替えなかった: `Elab.lean` は `Tools` の `httpType` などを import できず（循環）、定数を参照できないため。小さいので項を再出力するままにした）。

### 50.2 (1) `hkgfacts` — 供給した
- `Sparkle/Compiler/KidFactsCheck.lean`（S3a step1a）: `kidRowOkB env inl ip peel X T V Vi` と `kidRowOkB_sound`。`Expr` の等号は `ExprDecEq.exprDecEq`（束縛名を含む構造）。
- `Sparkle/Compiler/PilotKidTables.lean`（生成物・非信頼）: 2 つの callee の型・値・inline 後の値、`kidsOkB`、`startKidsOk declName env inl ip peel`（root なら `kidsOkB`、他の宣言は true）。関数 3 つは引数で、Elab が実物を渡す。
- `Sparkle/Compiler/Elab.lean`: `gatePeeledBody`（= `Tools…S2gGates.peeled`、`rfl`）、`import PilotKidTables`、`synthesizeCombinationalCoreOff` の `startEnvOk` の枝の後に `else if !(startKidsOk declName env (userInliner env) (instancePredicate env) gatePeeledBody) then throwError …`（+5 行程度。失敗は誤り、fallback なし。pilot root だけを縛る従来の形のまま）。`S1qLinked`: `coreRestOff` / `core_chainOff` を同様に直し、`core_kidsOkOff`（成功した core run は `getEnv` の結果 `envR` で `startKidsOk declName envR (userInliner envR) (instancePredicate envR) gatePeeledBody` を通した）を追加。
- `Tools/ShippingFGCircuitS3aKids.lean`: 生成した 6 項が `httpType/httpValue/httpInlValue/tlp…` と一致することを kernel（`decide +kernel`）で pin、`startKidsOk_sound : startKidsOk hftRoot env (userInliner env) (instancePredicate env) gatePeeledBody = true → HftKidsGateFacts env`（同じ `env`）。
- `Tools/ShippingFGCircuitS3aFinal.lean`: `startKidsOk_of_run`（`hcell` と Off の run から、`envAt cref w` で上の検査が true。`startEnvOk_of_run` と同じ head・`getConstInfo`・`getEnv` の環境保存の鎖）、`HftFinalStmtOffCombined6` / `synth_hftPcieOutByte_finalOffCombined6`。
保証の範囲: pilot root の Off 入口のみ。他の root に対して検査が true でも保証ではない。生成表は kernel で pin（生成器は信頼しない）。

### 50.3 binder の前後
v5（17）`L lvl env₀ hstart hr hcell hchk hreadH hreadT hadm hdown hD hG hT hs h0 hkgfacts` → v6（16）`… h0`（`hkgfacts` を除いた）。

### 50.4 (2) `hreadH` / `hreadT` — まだ供給していない（不可能とは言わない）
`RootReader lvl env X d` は `entry₀` / `machineShape?` / `dataOfAt lvl E (structEnv env) d.shape = some d` で、`dataOfAt` は `partial` の `packTupleInputs` / `rootFloat` を呼ぶ。実行時の Bool 検査で同じ opaque 定数の結果を調べること自体はできる。供給できていない理由は 3 つで、いずれも未着手の仕事であって不可能の証明ではない:
1. `lvl : Expr → Nat` は最終文の自由な binder で、`dataOfCore` が `readN` の段数 `lvl shape.body` として使う。run も `Elab` も `lvl` を計算しないので、検査はある具体的な `lvl₀` についてしか書けず、全ての `lvl` についての `RootReader lvl …` にするには `readN` の段数に関する一般の単調性が要る（`ShippingGen5ReadKinds` にあるのは quotation 上の `readN_mono_on_quotes` だけ）。または `lvl₀` に特化した v7（lvl binder を落とす）という文の変更になり、これは決めていない。
2. `dataOfAt` / `machineShape?` / `entry₀` は `Tools` 側（`Elab` を import）にあり、`Elab.lean` の入口の guard から呼べない（循環）。guard に載せるには、それらを小さい新ファイルへ移す（`Tools.ShippingGen5DataOf` の依存は大きい）か、検査を入口の外（`Tools` 側の関数を呼ぶ後段）に置く必要がある。
3. 期待値 `machineData`（`Term` を含む依存型の値）を表として生成し、構造等号とその健全性を証明する必要がある（`MachineData` の lawful な等号は未実装）。
次の一歩の候補: (a) `readN` の単調性の一般化、または lvl₀ 特化の文にするかの判断（ユーザー/reviewer）、(b) `dataOfAt` の依存の切り出し。

### 50.5 Check45（`kjob lake build Tests.Gen5.FGCircuitPilotCheck45`、exit 0）
`FGCIRCUIT45 CONTROLS: ok`（実環境で true、型・値・inline 値の改変・callee 入れ替え・存在しない定数・何もしない inliner・型を固定しない inliner・instance predicate が全点/各点で true・2 つ目の callee・`Init` だけの環境で false）、`FGCIRCUIT45 REPR`、`FGCIRCUIT45 SIGNATURES …38 mutants rejected`、`FGCIRCUIT45 AXIOMS: 5 names, standard axioms only`。同じ `FGCircuitCmp.stmtEq`（正例も mutant も）。`startKidsOk_sound`・`startKidsOk_of_run`・v6 の完全型を独立に書いた文と照合。mutant: 別の root・結果 false・結論が別の環境・恒等 inliner・常に false の instance predicate・peel なし・callee 入れ替え/重複/片方のみ/全体値・`True`・検査が別の環境・終了 world・env₀・inliner が別の world・診断入口・`hcell` 欠落、kept hypotheses（v5 = binder を残した版、v4、`hcd` 併存、条件 1 つだけ残す）、carrier、premise の欠落。名前の存在確認つき。
既存 Check: `Check15/18/19/20/23/24/26/28/30`（`synthesizeCombinationalCoreOff` の形を見るもの）を再 build、いずれも exit 0。それ以外の Check とベース出力 baseline は、agent の作業時点では未実施だった。
**対象 SHA `58328c91` での事後検証（coder、agent 作業後）**: `kjob-run-src-fgc-m3a-29b5` exit 0。S3aFinal・S3aKids・S2zFinal と `Tests.Gen5.FGCircuitPilotCheck*` 45 個すべてを build（"Build completed successfully (1045 jobs)"、各 AXIOMS 行は標準 axiom のみ）。

### 50.6 出力の同一性と時間
同じ build の中で root に対し `synthesizeCombinationalOff`（2 つの検査あり）と変更していない `synthesizeCombinational` を走らせ、module と design の `repr` が一致（77654 / 89425 文字、§49.4 と同じ数）。前者 306–308 ms、後者 297–298 ms（2 回の build で各 1 回。検査単独の費用は測っていない。費用の主張ではない）。
**出力 baseline（対象 SHA `58328c91`、coder の事後検証）**: `kjob-run-src-fgc-cmp3a-e696` exit 0。272 件中 268 件が cmpnew-c2ee とバイト一致、`output_baseline.tsv` の 1–9 列は 50 行で一致、136 個の終了コードはすべて一致。差のあった 4 件（MultiOutputSubModuleHangRepro・GHASHHWSynth・SLIPTest・UsbWebServerSynth）は再実行 `kjob-run-src-fgc-cmp3a-b263` で cmpnew-3a92 とバイト一致。よって 272/272。これは agent 作業時点の記録との差（当時は未実施）を埋める事後記録である。
build の所要: Elab 変更後の依存全体の再 build（Check45 の前段）で 14 分（初回のキャッシュなし）。

### 50.7 範囲
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。台帳の減算は reviewer が決める。
- `hreadH` / `hreadT` は上のとおり未供給。残る義務: `hreadH hreadT hadm hdown hD hG hT hs h0`、`hchk`、`CellPrem`、`Laws/Start/hr`。

## 51. S3b（Issue `sparkle-fg-circuit-pilot`）: `hreadH` / `hreadT` の供給 — reader 移動量の測定と停止

土台 `58328c91`。reviewer 判断 (b): 最終文を具体的な `lvl₀ : Expr → Nat` に特化してよい（任意 lvl の単調性は先行条件にしない）。`lvl₀` は「既存入口が固定している level」ではなく、追加する reader 検査が採用する決定的な検証用 fuel 設定として定義し、root の `hchk`・子 2 つの `RootReader`・結論の `GPt` に同じ `lvl₀` を使う。実装方針は reader/比較器を小さい compiler 側ファイルへ分離すること。ただし移動量が大きければ停止して最小依存範囲を書く、という条件に従った。

### 51.1 測定（`dataOfAt ∪ machineShape?` の推移的な定数依存）
`Tools.ShippingGen5DataOf` を build（`kjob lake build Tools.ShippingGen5DataOf`、exit 0、13m41s）後、scratch の `run_cmd`（源木には置かない）で `dataOfAt`・`machineShape?` から定義・型・値に現れる定数を推移的にたどった（定理は除く）。モジュール別の定数数:
- `Sparkle.Compiler`: Elab 362、ExprDecEq 144、MachRawSurface 22、MachInstOrigin 10、MachMemory 1、MachTupleIn 1（これらは Elab 側／compiler 側で、移動不要）。
- `Tools`（移動が要る）: ShippingReaderTerm 77、ShippingMachineAuto 55、ShippingUnifiedSource 54、ShippingReaderNodes2 41、ShippingGen5DataOf 35、ShippingGen5DataOfPure 28、ShippingReaderApp 23、ShippingReaderInputs 23、ShippingMachineDenote 19、ShippingMachineCommand 17、ShippingScalarSoundness 15、ShippingMachineRef 8、ShippingEntrySoundness 4、ShippingMachineEntry 3、ShippingMixedSourceBridge 1、ShippingMuxTypeSoundness 1。計 約 404 定数、16 モジュール。
モジュール閉包で見ると `Term`/`SType` を含む `ShippingReaderTerm` だけで Tools 52 ファイル・約 34K 行、`ShippingGen5DataOf` は 140 ファイル・約 89K 行を import し、いずれも `Sparkle.Compiler.Elab` に到達する（Elab を import する Tools ファイルは 1034）。

### 51.2 判断: 停止
`Elab.lean` の入口 guard から `dataOfAt`（`readN`・`Term`・`MachineData`・`typedFields`・`splitLets`・`bitsBeq`・`d.ok` を含む）を呼ぶには、上の約 404 定数を `Sparkle/Compiler` 側の小ファイル群へ移し、名前空間（`Tools.ShippingReaderTerm` 等）を参照する後続の Tools 側の証明（`dataOfFrom_sound`、`RootReader`、`GenData` 系、その上の S1*–S3a の鎖）をすべて追従させる必要がある。これは「Tools 全体の移動を避ける」の範囲を超える大きさで、名前だけ似た複製（検査用に別 reader を書く）は reviewer の指示（旧 `dataOfAt` と一致の証明が要る）に反するので作っていない。よって deliverable 1–5（compiler 側 reader/比較器、一致と soundness、入口 guard、v7、Check46）は着手せず、ここで止めた。

最小依存集合（再開時の出発点）:
1. 型・構文: `SType`/`Term`/`AnyTerm`（ReaderTerm）、`MachineShape`/`MachineData`/`mkData`/`packed`/`ok`（MachineAuto・DataOfPure）、`MixedGateBinder`（UnifiedSource）。
2. reader: `readN`・`kindsCfg`（ReaderApp・ReaderNodes2）、`typedFields`/`splitLets`/`splitFields`/`bitsBeq`（DataOf・DataOfPure）、`dataOfFront`（DataOf・MachineCommand）。
3. `machineShape?`・`entryConst`・`structEnv` は既に Elab 側。
4. 比較器: 方針は「Bool 比較 → `RootReader` の要求する `some d`」。`MachineData` 全体の LawfulBEq は不要。shape・dom・幅/型 index・各 `Term`・順序を落とさない。
再開するなら 1–2 をまず証明を持たない定義だけ（約 404 定数のうち定義部）を `Sparkle/Compiler/PilotReader*.lean` へ移し、Tools 側は `abbrev`/`export` で同名を再公開して旧証明を保つ案が最小。その場合 `Term` 周りの `deriving`/instance の位置が壊れないかを先に確認する。これは未着手で、可否の確定ではない。

### 51.3 範囲
- 追加の Elab 変更・新しい Check・binder 変更は無い（v6 の 16 binder のまま）。供給していないもの: `hreadH` / `hreadT`（上のとおり）、`hadm hdown hD hG hT hs h0`、`hchk`、`CellPrem`、`Laws/Start/hr`。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 52. S3c（Issue `sparkle-fg-circuit-pilot`、状態は変えていない）: `hadm` / `hdown` を除いた最終文 v7、Check46

土台 `45e5ccc9`。`Sparkle/`（compiler）は変更していない。sorry・axiom・native_decide・TRUSTED・新しい law は無い（標準 axiom のみ）。v6 以前は書き換えていない。

### 52.1 発見: 閉じ方は core だけでなく top の経路にも `hdown` を使っていた
v6 の証明は `finalOffLNL`（S1z）に 2 つの事実を渡す: `HftCoreCloses`（S2m の `hftCoreCloses_of_kidsR`）と `htop`（S2r の `hftTop_of_runR`）。`hdown` は両方で使われていた（`ropsR`、`kid_shipsResW` の `hadmW`、`jqc_weak`）。S2s5 の X 版は core 側（`hftCoreCloses_of_kidsR''`）だけだったので、top 側を X へ移した。

### 52.2 追加したもの（すべて `kjob lake build` exit 0、sorry なし）
- `Tools/ShippingFGCircuitS2sAdmS2kRun.lean`（`scripts/s2s_port2.py` による選択的移植 + 手書き 1 補題 `JQHX.toCX`）: `MachineRunJQHX`、`machineRunJQH_of_closesHOffX`、`soundX_served_EX`。
- `Tools/ShippingFGCircuitS2sAdmS2jKid.lean`（同上）: `kidRunKX` のみ（`S2jKid` の他の宣言は `Laws` に依るので移植せず）。`S2jCopy`（`oneOut_topShipsOff`、`ShipsRes L`、`MachineTaken L`）は移植していない: 結論側の `L : Laws` はそのままにして、履歴側だけ X にした（下記）。
- `Tools/ShippingFGCircuitS3cTop.lean`: `Laws.toX`（`⟨L.O.toX, L.T.toX⟩`）、`realChildAX_weak`/`jqcX_weak`（X → 既存、文脈の述語が `AdmCtx L.O.quiet` そのものなので文脈の弱化は恒等）、`realChildA_toX`/`jqc_toX`（既存の `JQC` → X）、`kid_shipsResWX`、`hftTop_of_runRX`（`hadm`・`hdown` なしの `hftTop_of_runR`）。
- `Tools/ShippingFGCircuitS3cFinal.lean`: `leafStep_ofX`/`reached_ofX`（`ReachedX` with `adm := AdmCtx quiet` から `Reached`）、`drowEnvRX_of_R`/`diagEnvRX_of_R`/`profStepRX_of_R`、v7 `HftFinalStmtOffCombined7` と `synth_hftPcieOutByte_finalOffCombined7`。閉じ方: `synth_hftPcieOutByte_finalOffLNLX`（X、S2s5）に `L.toX`、`htop := hftTop_of_runRX`、`hclL := hftCoreCloses_of_kidsR''` を渡す。`hcd`/`hlink`/`hkgfacts` は v5/v6 と同じ導出（`startEnvOk_sound (startEnvOk_of_run …)`、`startKidsOk_sound`）。
- 根の文脈: `StartX L.toX mctx cctx w := ⟨hstart.1, jqc_toX hstart.2⟩`。`hstart.1 : AdmCtx L.O.quiet mctx cctx` は v6 が既に持つ `hstart` の一部で、X の文脈述語 `L.toX.O.adm` は定義上これと同じ。したがって `AdmRootX`/`admRootX_toX`（`mkMetaContext` 固定）は使っていない（v6/v7 の文は任意の `mctx` について述べている）。`hftCoreCloses_of_root` ではなく `hftCoreCloses_of_kidsR''` を使った理由はこれ。

### 52.3 binder の前後
v6（16）`L lvl env₀ hstart hr hcell hchk hreadH hreadT hadm hdown hD hG hT hs h0`
v7（14）`L lvl env₀ hstart hr hcell hchk hreadH hreadT hD hG hT hs h0`
`hadm`・`hdown` は除いた。**新しい binder は無い。** ただし 1 つの前提の命題が変わった:
- `hD hG hs`: v6 の命題のまま（`DRowEnvR`/`DiagEnvR`/`ProfStepR`）。X 形（`DRowEnvRX L.toX.O` など）は `ReachedX`/`LeafStepX`（`adm := AdmCtx quiet`）と既存の `Reached`/`LeafStep` が同値なので、証明した橋 `drowEnvRX_of_R` 等で得る。差は無い。`h0`（`ProfOffW`）は同一。
- **`hT`（変わった）**: v6 は `TeleR L.O e w`（= `RefLawsATele (quietR …)`、文脈 `AdmCtx (quietR …)` に対する continuation 法則）。v7 は `TeleRX L.toX.O e w`（= `RefLawsATeleX (quietRX …) (AdmCtx L.O.quiet)`、文脈 `AdmCtx L.O.quiet` に対する法則）。`TeleR` から `TeleRX` へは、`hdown`（`AdmCtx quietR → AdmCtx quiet`）に相当する文脈の橋が要る（`TeleRX` の方が広い文脈を要求する）。**現時点でこの橋は未供給**（`hdown` なしには出ない、橋は作れない、とは言わない: 非導出性は証明していない）。**これは「`hdown` を出し、より広い文脈の `hT` を入れた」交換であり、binder 数は 2 減ったが前提の総量の減少とは言えない。reviewer の判断（台帳に数えるか）が要る。** `hT` は S2s5 §44.6 の「名前付きのまま未供給」の 1 つで、`RefLawsATeleX` の法則そのもの（`L.T` と同じ形）の強化 quiet 版。
- 供給した/していないもの: `hadm`（`hstart.1` から）と `hdown`（不要になった）は消えた。供給していない: `hreadH hreadT`（§51）、`hchk`、`hcell`、`hD hG hT hs h0`、`Laws/Start/hr`。

### 52.4 Check46（`kjob lake build Tests.Gen5.FGCircuitPilotCheck46`、exit 0）
Check の行から引用:
- `FGCIRCUIT46 BINDERS (9 implicit + explicit): v6 (25 = 9 + 16) … v7 (23 = 9 + 14) …; v7 = v6 minus [hadm, hdown]; hT keeps its name but is stated at TeleRX`（binder 名のリストを v6 から `hadm`/`hdown` を除いたものと比較して一致）。
- `FGCIRCUIT46 SIGNATURES: … 25 mutants rejected`（各前提の欠落 11、`hT` を v6 の `TeleR` 形にしたもの、`hadm`/`hdown`/両方を戻したもの、到達環境の違い 2、別の root、別の post-run root、結論の一部を落としたもの 2、診断入口、carrier Z、v6 と v5 の定理の型）。同じ `FGCircuitCmp.stmtEq`。期待型 `Exp7` は独立に書いた（`hT` の X 形 `ExpTX` は `quietRX`/`Laws.toX` の射影を使って書いたので、`TeleRX` 自体の展開とのみ独立で、`quietRX` の定義には独立ではない。`Laws.toX` の `adm`/`quiet` が `AdmCtx L.O.quiet`/`L.O.quiet` であることは `rfl` の 2 補題で示した）。
- `FGCIRCUIT46 AXIOMS: 7 names, standard axioms only ([Quot.sound, Classical.choice, propext]); no sorryAx, no native_decide`。

### 52.5 範囲・台帳
- 構造検査は型の表面で、証明の閉包ではない（axiom は `collectAxioms`）。
- 既存 Check の再 build と出力 baseline は、**agent 時点では未実施**（`Sparkle/` は未変更、Elab 側の変更なし）。merge 後の完了記録は §55.3。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。binder の変更は台帳の減算ではない（reviewer が決める）。

## 53. S3b2（Issue `sparkle-fg-circuit-pilot`）: `hreadH` / `hreadT` の供給 — 経路 (B): 実際の `dataOfAt` 検査を引数で渡す pilot 入口、v7r、Check46r

土台 `45e5ccc9`（par/fgc-s1 `3978c529` ＋ S3b 文書 §51）。reviewer 裁定 (B)（§51 の約 404 定義の一括移動 (A) は採らない）に従った。TRUSTED・axiom・sorry・native_decide・新しい law はない。Issue の状態は変えていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。binder の変更は台帳の減算としては数えていない（reviewer が決める）。

### 53.1 構成（既存の入口・既存の v6 は変えていない）
- `Sparkle/Compiler/Elab.lean`（追加のみ、削除 0 行）: `synthesizeCombinationalCoreOffR (readerOk : Environment → Name → Bool)` — 既存の `synthesizeCombinationalCoreOff` と同じ本体で、S2z の `startEnvOk`、S3a の `startKidsOk` の guard のあと、本体の前に **同じ `env` で** `readerOk env declName` の guard を足したもの（false は `throwError`「…reader check of this entry; refusing to synthesize」、fallback なし）。`synthesizeCombinationalOffR readerOk` は既存の `synthesizeCombinationalOff` と同じ後処理。`synthesizeCombinationalCoreOff` / `synthesizeCombinationalOff` / `synthesizeEntry`（`#synthesize` / `#synthesizeVerilog` / `#showVerilog` が使う）は 1 文字も変えていない。**reviewer の訂正のとおり、通常の `#synthesize` 系は `Off` を使うので、(B) の拡張保証は下の pilot 入口にだけ付き、既存 `Off` にも任意 `readerOk` の run にも広げていない。**
- `Tools/ShippingFGCircuitS3b2Reader.lean`: `lvl₀`、`MachineData` の構造比較 `mdBeq`（`layoutBeq` / `shapeBeq` / `anysBeq` / `termsBeq`。shape・dom・`nIn`・位置表・`ss`・`ls`・`outs` の各 `Term`（sort と term の両方）・`nexts`・**順序**を落とさない）と `mdBeq_eq : mdBeq a b = true → a = b`（`MachineData` 全体の `LawfulBEq` ではない）。`rootReaderB lvl env X d`（`entry₀` → `machineShape?` → **実際の** `dataOfAt lvl` を呼び、返り値を `mdBeq` で `d` と比較）と `rootReaderB_sound : rootReaderB … = true → RootReader lvl env X d`。reader の複製は書いていない（`dataOfAt` / `machineShape?` / `entry₀` 自体を呼ぶ）。
- `lvl₀ := fun e => e.approxDepth.toNat`: この検査が採用する具体的・決定的な検証用 fuel 設定（`readN` の段数 = 本体の入れ子の深さ。「既存入口が固定している level」ではない）。root の `hchk`、子 2 つの `RootReader`、結論の `GPt` に同じ `lvl₀` を使う。
- `Tools/ShippingFGCircuitS3b2Exp.lean`: `httpGetByte.machineData` / `tlpCplByte.machineData` は `#machine_endpoint` が `addDecl` で足した定数で**コンパイル済みコードがない**（Bool 検査から呼べない）。そこで同じ値を別名 `httpMD` / `tlpMD` で `addAndCompile` した複製を作り、`httpMD_eq : httpMD = httpGetByte.machineData := rfl`（axiom なし）。値の複製であって reader の複製ではない。
- `Tools/ShippingFGCircuitS3b2Core.lean`: `coreRestOffR`、`core_eqOffR`、`coreR_chain`（head → `getConstInfo` → `getEnv` が返す `envR` → 4 つの guard（inliner error なし、`startEnvOk`、`startKidsOk`、**`readerOk envR declName`**）→ 本体 → finally）、`RunsTo.try_finally_intro`、橋 `coreR_to_core`（検査付き core の成功 run は、同じ入力・開始 world・終了 world・Module・Design での**既存 core** の成功 run）、`offR_to_off`（`Off` へ同様。同じ後処理）。純粋な検査は生成結果を変えない、を定理にした。
- `Tools/ShippingFGCircuitS3b2Final.lean`: `pilotReaderOk env X := X == hftRoot && rootReaderB lvl₀ env hftHttp httpMD && rootReaderB lvl₀ env hftTlp tlpMD`。
  - (1) `pilotReaderOk_sound`: `pilotReaderOk env X = true → X = hftRoot ∧ RootReader lvl₀ env hftHttp httpGetByte.machineData ∧ RootReader lvl₀ env hftTlp tlpCplByte.machineData`（**同じ env**、実 `dataOfAt`、子の `machineData`）。
  - (2) `readerOk_of_run`: 検査付き入口の root への成功 run は、**その開始環境 `envAt cref w`** で `readerOk … hftRoot = true`（任意の `readerOk`。`startKidsOk_of_run` と同じ head / getConstInfo / getEnv の環境保存）。
  - pilot 入口 `pilotEntry := synthesizeCombinationalOffR pilotReaderOk`、`pilotArtifact`（**1 回の run** が返した Module / Design と、その Module から作った Verilog 文）、コマンド `#synthesizeVerilogPilot`（返り値の同じ artifact を印刷し、再合成しない）。
  - (4) `synth_hftPcieOutByte_finalOffCombined7R`（`HftFinalStmtOffCombined7R`）: `hr` が `synthesizeCombinationalOffR pilotReaderOk hftRoot` の run のとき、v6 の結論（同じ `PostRunOff`、`RootArtifactMonoV cdvT … (GPt lvl₀ …)`）。証明は (2)→(1)→ 橋 `offR_to_off` → 既存 v6 を `lvl₀` で適用。**固定 wrapper に検査の soundness 仮説は残っていない**（定理で渡した）。

### 53.2 binder の前後
- v6（16, 未変更）: `L lvl env₀ hstart hr hcell hchk hreadH hreadT hadm hdown hD hG hT hs h0`。
- v7r（13）: `L env₀ hstart hr hcell hchk hadm hdown hD hG hT hs h0`。外れたのは `lvl`（`lvl₀` に特化）、`hreadH`、`hreadT`。`hr` は検査付き入口の run、`hchk` は `lvl₀`。これは単に `lvl` binder を落としたのではなく、特化の橋（v6 を `lvl₀` で適用）と完全型 Check が付いている。台帳への数え方は reviewer が決める。

### 53.3 供給したもの / していないもの
- 供給: `hreadH` / `hreadT`（pilot 入口の run に対して、`lvl₀` で、定理 (1)(2) から）。
- していない: `hadm hdown hD hG hT hs h0`、`hchk`、`CellPrem`、`Laws/Start/hr`（残る仮説。v6 と同じ）。
- **通常経路は未接続**: `#synthesize` / `#synthesizeVerilog` / `#showVerilog` と既存 `Off` の run は v7r の対象外（reader 検査を通らない）。通常経路への一般化・接続は残作業。
- reader を compiler へ移すことが将来必須とはまだ言えない。注入方式でも root 別の表（root ごとの `readerOk` と、その root の子の `machineData` の表）への一般化は設計できる。S3 一般化はこの境界を保って判断し、いま大量移動を先行条件にしない。

### 53.4 測定・注記
- Elab 変更後の依存全体の cold build: `Tools.ShippingFGCircuitS3aFinal` まで 31 分 46 秒（単一 foreground build）。Elab 自体は 1 分 7 秒。
- 実環境で `pilotReaderOk env hftRoot = true`（検査単独は 1 ms 未満）。同じ root で pilot 入口 / 既存 `Off` / `fun _ _ => true` の `OffR` の module+design の `repr` は一致（77654 / 89425 文字、§50.6 と同じ数）、pilot の Verilog 文は既存入口の Module から作った文と一致（11345 文字）。pilot 入口 361 ms、既存 `Off` 323 ms（各 1 回、費用の主張ではない）。
- **`lvl` について（正直な記録）**: この 2 つの子では Bool 検査は定数 lvl 0, 1, 3, 10 でも `lvl₀` でも true になる。つまり Bool 検査は lvl を区別しない。どの lvl を認証したかは**文**（`pilotReaderOk_sound` の `RootReader lvl₀ …`、v7r の `lvl₀`）で固定され、Check46r の mutant（lvl 0 / `lvl₀`+1 を reader / `hchk` / `GPt` に入れた文）で区別している。
- 実際の失敗経路: `fun _ _ => false` の `OffR` は「…does not pass the reader check of this entry; refusing to synthesize」で失敗（fallback なし）。pilot 入口を別の宣言（`hftHttp`）に使うと同じ guard で拒否される。

### 53.5 Check46r（`kjob lake build Tests.Gen5.FGCircuitPilotCheck46r`、exit 0、1009 jobs）
- `FGCIRCUIT46R CONTROLS: ok`（実環境 true／別の root・子を root・子の取り違え 2 方向・存在しない定数／`mdBeq` の各成分を改変した 8 件（`nIn` `dom` `bposL` `vwL` `ls` `outs` `shape.body` `shape.binders`）／`Init` だけの環境で false。lvl は上のとおり区別しない）。
- `FGCIRCUIT46R OUTPUT`（上の一致と明示エラー）。
- `FGCIRCUIT46R SIGNATURES: … 45 mutants rejected`: `pilotReaderOk_sound`・`readerOk_of_run`・`offR_to_off`・`coreR_to_core`・`synth_hftPcieOutByte_finalOffCombined7R` の完全型を独立に書いた文と、同一の比較関数 `FGCircuitCmp.stmtEq`（正例も mutant も）で照合。mutant: 検査を `True`／常に false、検査を別 env で走らせる／別 env について結論、lvl 0／`lvl₀`+1（reader・`hchk`・`GPt`）、reader を前提に戻した版（lvl 0 も）、別 root／post root／出力 shape、到達・結論の環境を終了 world／env₀、旧入口を仮定にした版、子の名前・データの取り違え、子の重複、root のデータを子に、root 等式なし、橋の終了 world／開始 world／Module／Design／宣言／context／診断入口／core／逆向き、cell 前提の欠落、v6 の文。
- `FGCIRCUIT46R AXIOMS: 10 names, standard axioms only`（存在確認つき）。
- 追加 Elab を含む再 build として `Check15/18/19/20/23/24/26/28/30/44/45` を build、いずれも exit 0（各 AXIOMS 行は標準 axiom のみ）。全 Check と出力 baseline の再実行は、**agent 時点では未実施**（coder の作業）。merge 後の完了記録は §55.3。

### 53.6 残作業（記録）
1. 通常経路（`synthesizeEntry` → `Off`）への接続と、root 別の `readerOk` 表への一般化。
2. 任意 lvl に対する保証（Bool 検査は lvl を区別しない。lvl₀ 以外については `readN` の段数の単調性が要る）。
3. `hadm hdown hD hG hT hs h0`、`hchk`、`CellPrem`、`Laws/Start`。

## 54. S3d（Issue `sparkle-fg-circuit-pilot`）: v7r と v7 の合成 v8（pilot 入口、`hadm`/`hdown`/`lvl`/`hreadH`/`hreadT` なし）、Check47

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。引数の変更は別記録（下記）で、判断は reviewer。

### 54.1 文 v8（`Tools/ShippingFGCircuitS3dFinal.lean`、`synth_hftPcieOutByte_finalOffCombined8`）
`hr` は `synthesizeCombinationalOffR pilotReaderOk hftRoot` の run（pilot 入口）。水準は全箇所 `lvl₀`（`hchk`・結論の `GPt`）。`hT` は `TeleRX`（v7 と同じ）。証明は `pilotReaderOk_sound (readerOk_of_run hcell hr)` から 2 つの `RootReader`（lvl₀）を得て、`offR_to_off hr` で通常 Off の run にし、v7 を `lvl := lvl₀` で適用するだけ。v7・v7r は無変更。

### 54.2 引数の一覧（9 個の暗黙引数 ι mref cref mctx cctx w w' b D' を除く明示引数）
- v6 (16): L lvl env₀ hstart hr hcell hchk hreadH hreadT hadm hdown hD hG hT hs h0（hT = TeleR）
- v7 (14): L lvl env₀ hstart hr hcell hchk hreadH hreadT hD hG hT hs h0（hT = TeleRX、hr = 通常 Off）
- v7r (13): L env₀ hstart hr hcell hchk hadm hdown hD hG hT hs h0（hT = TeleR、hr = pilot 入口、lvl₀）
- **v8 (11)**: L env₀ hstart hr hcell hchk hD hG hT hs h0（hT = TeleRX、hr = pilot 入口、lvl₀）
- v8 = v7r − [hadm, hdown] = v7 − [lvl, hreadH, hreadT]。

### 54.3 何を供給し、何を供給していないか
- 供給: `hreadH` / `hreadT`（pilot 入口の検査 `pilotReaderOk` が run で通ったこと → `pilotReaderOk_sound` + `readerOk_of_run`、lvl₀・同じ環境 `envAt cref w`）。`hadm` / `hdown`（v7 の文脈述語経路で不要）。`lvl`（lvl₀ に固定）。
- 供給していない（残る前提）: `hstart`（`Start L ..`）、`hcell`、`hchk`、`hD hG hT hs h0`、`env₀`。
- v7r ∪ v7 に無い新しい前提: なし。引数が増えた箇所もない。
- 引き継いだ変更点: (a) `hT` は TeleR より広い `TeleRX`（S52 のとおり、`hdown` なしでは橋が無い）。(b) 保証は pilot 入口の run に限る（既存の Off や任意の `readerOk` の run には広げない）。(c) 水準は lvl₀ のみ（Bool 検査は lvl を区別しない、S53.6）。
- `hstart : Start L mctx cctx w` は従来どおり任意 bundle `L` 上（`L.toX` への特殊化は v7 の証明内部で明示）。`hr` と `hstart` の mctx / cctx / w は同じ変数で型が固定される（Check47 の startCtx / startWorld 対照）。

### 54.4 Check47（`Tests/Gen5/FGCircuitPilotCheck47.lean`）
- `FGCIRCUIT47 SIGNATURES`: v8 の完全型を独立に書いた `Exp8` と `FGCircuitCmp.stmtEq` で照合。再利用は `Check46.ExpTX`（TeleRX は quietRX / Laws.toX 経由でしか書けないため）のみ、と当時は記した（**旧版・§55.1／§56 で置換**: 現在の Check47 は `Check46.ExpTX` を使わない）。32 個の mutant を拒否（各前提の欠落、検査 True の入口、通常 Off の入口、別 root／別 post root、start の context／world が run と別、TeleR、hadm／hdown／両方／reader を戻した版、`hchk`・`GPt` の別水準、到達環境、結論の一部欠落、別 carrier、v6／v7／v7r の型）。
- `FGCIRCUIT47 BINDERS`: v6 25 / v7 23 / v7r 22 / v8 20（暗黙 9 を含む）。v8 = v7r − [hadm,hdown] = v7 − [lvl,hreadH,hreadT]、v7r = v6 − [lvl,hreadH,hreadT] を名前の列で検査。
- `FGCIRCUIT47 AXIOMS`: 6 names、標準 axiom のみ。

## 55. S3e（Issue `sparkle-fg-circuit-pilot`、状態は変えていない）: Check47 の要件（hT の独立な期待型、子 reader／開始 env／出力／carrier の対照）と文書訂正

### 55.1 Check47 の変更（`Tests/Gen5/FGCircuitPilotCheck47.lean`。`Tools/` の定理の文は不変）
- **hT の独立な期待型 `ExpTXind`/`ExpQuietX`**: `Check46.ExpTX` を使わない。`TeleRX` の命題を `RefLawsATeleX (ExpQuietX L.O.quiet (AdmCtx L.O.quiet) mref cref e w₀) (AdmCtx L.O.quiet) mref cref` と書いた。`adm` は `AdmCtx L.O.quiet`、強化 quiet は `quiet w ∧ ReadsAt e cref w ∧ ReachedX quiet adm mref cref w₀ w` と別に書き（`quietRX` ではない）、`Laws.toX`・`RefLawsAOps.toX` の射影は、実の型と期待型の**両方**に同じ正規化 `projToX`（定義の展開で `L.toX.O.quiet` を `L.O.quiet`、`L.toX.O.adm` を `AdmCtx L.O.quiet` に読む）をかける。肯定例も mutant も同一の比較 `FGCircuitCmp.stmtEq`。
  - **訂正（S3e 補修）**: 初版の記述「両側に同じ `projToX`」は実装どおりでなかった（実の型は `norm47`、期待型 `F8_real` と mutant は `norm37` だけを通していた。現期待型には `toX` 射影が無いため v8 の証明の欠陥ではない）。補修後は実の型・`F8_real`・全 mutant・v6／v7／v7r の型が**同じ一つの関数 `normC`**（= `norm47` を 2 回、2 回目は展開後の期待文に現れる `toX` 射影も読む）を通る。再 build: exit 0、`55 mutants rejected`、BINDERS 20／AXIOMS 標準のみ（変更なし）。
- hT の mutant（同じ比較で拒否）: 旧 `TeleR`（`RefLawsATele` の強化 quiet）／元の quiet だけの法則（`L.T` の型 `RefLawsATele L.O.quiet`、`L.T.toX` の型 `RefLawsATeleX L.O.quiet (AdmCtx L.O.quiet)`）／文脈を強化 quiet から作ったもの／強化 quiet から到達または `ReadsAt` を落としたもの。
- 追加した対照（同じ比較）: 子 reader（入口の検査 `chkOf`: 子のデータの取り違え／名前の取り違え／片方の子を別水準／root 等式なし。reader を前提に戻した版の名前の取り違え／片方の子を別水準）、開始 env（`hchk` を run の開始 env／終了 env で、結論を `env₀`／終了 env で）、出力（結論が別の Module／別の Design／両方、別の artifact 名）、carrier（`cdvZ` に加え `cdvOld`）、旧入口（`synthesizeCombinationalOff`、検査 True。既存）。S3d の mutant は全て残した。
- 結果の数は §55.4 に Check 自身の行から引用する。

### 55.2 文書訂正
- §52.3: 「`hdown` なしには出ない／橋は作れない」を「現時点でこの橋は未供給」に直した（非導出性は証明していない）。
- §52.5・§53.5: 再 build と出力 baseline が未実施なのは agent 時点であると明記し、merge 後の完了記録（§55.3）への参照を足した。
- `Tools/ShippingFGCircuitS3cTop.lean` の `hftTop_of_runRX` の docstring を旧 7 前提／`ropsR` の記述から X 版（`hD hG hT hs h0` が `DRowEnvRX`／`DiagEnvRX`／`TeleRX`／`ProfStepRX` を `L.toX.O` で、`ropsRX`、`hadm`・`hdown` なし）に更新した（コメントのみ、文は不変）。

### 55.3 merge 後の coder の検証記録（agent 時点では未実施だったもの）
- `kjob-run-src-fgc-m3b2-aba1`: exit 0、73ade833 で 1110 jobs、pilot Check 47 本すべて。
- 出力 baseline `kjob-run-src-fgc-cmp3b2-4f46`: exit 0。268/272 は `cmpnew-c2ee` とバイト一致、残り 4 は `cmpnew-3a92` とバイト一致で、272/272。`output_baseline.tsv` の列 1–9 は同一。
- `kjob-run-src-fgc-mg3c-57bc`: exit 0、5606b06a で 1115 jobs、pilot Check 48 本すべて。

### 55.4 結果（Check の行から）
`kjob lake build Tests.Gen5.FGCircuitPilotCheck47`、exit 0（S3cTop の docstring 変更後の再 build を含む）。Check の行から:
- `FGCIRCUIT47 SIGNATURES: … equals the independently written Exp8 under ONE criterion (FGCircuitCmp.stmtEq …); 55 mutants rejected`（S3d の 32 から 55 に増加。hT の独立期待型は Check47 内の `ExpTXind`/`ExpQuietX`）。
- `FGCIRCUIT47 BINDERS`: v6 25 / v7 23 / v7r 22 / v8 20（不変）。
- `FGCIRCUIT47 AXIOMS: 6 names, standard axioms only`。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 56. S3f2（Issue `sparkle-fg-circuit-pilot`）: `hchk` の供給 — `pilotReaderOk2`、v9（9 引数、`env₀`・`hchk` なし）、Check48

S3e 補修（Check47 の実型・`F8_real`・全 mutant を同じ一つの正規化 `normC` に通す。§55.1・§54.4・Check47 冒頭コメント・`hftTop_of_runRX` の docstring を訂正）は別コミット（594e8e7b）。`Sparkle/` は変えていない。v7r・v8・`pilotReaderOk` は不変。

### 56.1 構成（新規ファイルのみ。lakefile に lean_lib 3 件）
- `Tools/ShippingFGCircuitS3f2Exp.lean`: ルートの `synth_hftPcieOutByte.machineData` の実行可能コピー `rootMD`（S3b2Exp と同じ `compile_data_copy`）。`rootMD_eq : rootMD = synth_hftPcieOutByte.machineData := rfl`（元の定数とのカーネル等式）。
- `Tools/ShippingFGCircuitS3f2Final.lean`:
  - `rootDefB env X ty val`: `env.find? X = some (.defnInfo d)` かつ `d.levelParams.isEmpty`、`d.type = ty`、`d.value = val`（`Expr` の構造的決定手続き `exprDecEq`）。`rootDefB_sound` は `∃ d, RootInEnv env X ty val d`。
  - `readerAt_of_rootReader`: **RootReader → ReaderAt の橋**（定理。`entry₀` は関数なので見つかった entry のデータは同じ）。
  - `pilotReaderOk2 env X := pilotReaderOk env X && rootDefB env X hftRootType hftRootValue && entryGatesB env X && rootReaderB lvl₀ env X rootMD`。
  - `pilotReaderOk2_sound`: 真なら `X = hftRoot`、子 2 つの `RootReader`（従来どおり）、そして `CheckedEnv lvl₀ env hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData`（`root` は `rootDefB_sound`、`gates` は `entryGatesB` そのもの、`reader` は `rootReaderB_sound` + `rootMD_eq` + 橋）。同じ環境、fallback なし、不一致・none は false。
  - `pilotEntry2 := synthesizeCombinationalOffR pilotReaderOk2`、`#synthesizeVerilogPilot2`（run 自身の artifact を印字）。既存の `#synthesizeVerilogPilot` も残した。
  - **v9** `HftFinalStmtOffCombined9` / `synth_hftPcieOutByte_finalOffCombined9`: 引数 `L hstart hr hcell hD hG hT hs h0`（暗黙 9 個を除く明示 9 個）。`hr` は `synthesizeCombinationalOffR pilotReaderOk2 hftRoot` の run。結論は v8 と同じ。
- 証明: `readerOk_of_run`（任意の `readerOk`）で run の開始 env `envAt cref w` での `pilotReaderOk2 … = true` を得て、`pilotReaderOk2_sound` から `CheckedEnv` と子 reader を得る。**`env₀ := envAt cref w` に特殊化**し、`link : ReadsAt env₀ cref w` は `readsAt_self`。run は `offR_to_off` で既存 Off の run にして v7 に `lvl := lvl₀`、`hchk := ⟨CheckedEnv, readsAt_self⟩`、子 reader を渡す。

### 56.2 引数の前後
- v8（11 個）: `L env₀ hstart hr hcell hchk hD hG hT hs h0`（`hstart` `hr` `hcell` を含め 11）。
- v9（9 個）: `L hstart hr hcell hD hG hT hs h0` = v8 − [`env₀`, `hchk`]（Check48 BINDERS で名前の列を検査）。

### 56.3 何を供給し、何を供給していないか
- 供給: `hchk` の `env`（root の `defnInfo`／`levelParams = []`／型／本体、`entryGatesB`、root の実 `dataOfAt` at `lvl₀` と `machineData`（`mdBeq`））は run の guard `pilotReaderOk2` から。`link` は `readsAt_self`（`env₀` を run の開始 env に特殊化）。`env₀` の外側 binder。
- 新しい前提: なし（`CheckedStart.link` の新前提も、無関係な snapshot も、環境等式も足していない）。新 axiom／law／sorry／native_decide なし。
- 既存 guard の再利用: `startEnvOk`／`startKidsOk` は root の表（`Delta` の `levelParams` と `value`、構成子、`List.rec`）を与えるが、root の**型**と `entryGatesB`、`dataOfAt` は与えない。表の行からの橋を作るより、`rootDefB` で root を 1 度直接検査する方が小さいので、`pilotReaderOk` との重複検査（root 名）以外は足している。`startEnvOk` の結果は v7 の経路で従来どおり使う。
- 供給していない（残る前提）: `hstart`、`hr`（pilot 入口の run）、`hcell`、`hD hG hT(TeleRX) hs h0`。保証は新しい pilot 入口（`pilotReaderOk2`）の run に限る（既存 Off や任意 `readerOk` の run には広げない）。水準は `lvl₀` のみ（Bool 検査は水準を区別しない、Check48 CONTROLS に記録）。TeleRX／Laws／CellPrem を新 axiom で払ったことにはしていない。
- 次の作業（この単位では未着手）: `hD/hG/hT/hs/h0` が実際に使う操作との対応づけ。まず profile 無効の `h0`/`hs` と診断の `hG` の供給可否、小さい実装変更の可否。

### 56.4 Check48（`kjob lake build Tests.Gen5.FGCircuitPilotCheck48`、exit 0）— Check の行から
- `FGCIRCUIT48 BINDERS`: v8 20 = 9 + 11、v9 18 = 9 + 9、v9 = v8 − [env₀, hchk]。
- `FGCIRCUIT48 SIGNATURES`: v9 の完全型を独立に書いた `Exp9` と照合（実型・期待型・全 mutant を `norm48`＝Check47 の `normC` 一本に通す）。**50 mutant 拒否**（各前提の欠落、v8 の `pilotReaderOk`／通常 Off／True の検査／root reader・gates・root 定義・子の検査を欠いた版／root reader を別水準・別 `machineData` にした版、別 root、別 post-run root、開始 context／world、到達環境・結論の環境を終了／別 env、hT の各 mutant、`GPt` の別水準、別 Module／Design／artifact 名、結論の一部、carrier、`env₀`・`hchk`（開始／終了 env・別水準）を戻した版、`env₀` だけを戻した版、v6／v7／v7r／v8 の型）。`pilotReaderOk2_sound` と橋の型も独立な期待型と照合し、**19 mutant 拒否**（root 名・型・本体・データ、検査／子／root の環境、水準、子の取り違え、`CheckedEnv` なし、逆向きの橋など）。
- `FGCIRCUIT48 CONTROLS`: 実環境で真（全体・各 conjunct）。負対照: 別の root 名／子を root／存在しない定数、root の型・本体の改変・入れ替え・入れ子の 1 箇所の改変、`levelParams = [u]`、theorem、gates が偽になる宣言（`fun a => a` の Bool gate）、root データの 8 成分の改変・別の `machineData`・別名、`Init` だけの環境。正の対照: root のコピー（別名・実の型と本体）は真。水準 0/1/3/10 と `lvl₀` で root reader は全て真（Bool 検査は水準を区別しない）。
- `FGCIRCUIT48 OUTPUT`: 新入口の `Module`/`Design` の repr ＝ 既存 Off ＝ `pilotReaderOk` 入口（77654 / 89425 文字）、印字される Verilog は run 自身の Module のもの（11345 文字、既存入口と同一）。負対照（別宣言の artifact、Module 名の改変、Design の改変は不一致、別宣言は reader-check エラー）。
- `FGCIRCUIT48 AXIOMS`: 6 names、標準 axiom のみ。
- 出力 baseline（全体）: **再実行は不要**（今回の差分根拠による再利用）。`git diff --stat 73ade833 c135f714 -- Sparkle/` は空（`Sparkle/` は 73ade833 と c135f714 の間で不変）なので、73ade833 での 272/272 baseline `kjob-run-src-fgc-cmp3b2-4f46` がそのまま適用される。pilot 入口の出力比較は Check48 OUTPUT。c135f714 は `kjob-run-src-fgc-m3f2-ebbb`（exit 0、1120 jobs）で検証済み。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。引数の変更（v8 11 → v9 9）は別記録で、台帳の増減には数えない。reviewer の判断を待つ。


## 57. S3g（Issue `sparkle-fg-circuit-pilot`）: 残り仮説 `hD / hG / hT / hs / h0` の監査 — 実際の Off run のどの操作を拘束するか、供給の可否（証明前の記録）

土台 `c135f714`。`Sparkle/` は変えていない。新 law・axiom・sorry・native_decide・TRUSTED なし。この節は**監査だけ**で、v10 は作っていない（§57.4 の判定: 調査範囲では、定理または Tools 側検査として供給した項目はない。供給できないことの証明ではない）。コンパイラ変更が要る項目は §57.3 に記述し、変更はしていない（reviewer の判断待ち）。

### 57.1 前提: 「Off run」とは何を実行するか（Elab.lean の行）
- 根 run: `synthesizeCombinationalCoreOffR`（9096–9172、`pilotReaderOk2` を `readerOk` に渡す）。本体は `synthesizeFromConst … (fun _ => pure ())`（9158 付近。`logProf := fun _ => pure ()`）。**根の `profLog` は構文上存在しない**（Off では `emitLeaves`/`synthesizeFromConst` の `logProf` 呼び出し 2167, 2175, 5375–5459 は全て `pure ()`）。根の head に `IO.getEnv "SPARKLE_PROFILE"` はない（`coreHeadOff`）。
- **子**は `sparkleChildSynth`（1042, 5270, 5293, 5712）経由で `synthesizeChild`（9210 付近）→ **`synthesizeCombinational`（profile 版）**→ `synthesizeCombinationalCoreWith`。ここは **Off ではない**: 先頭（5515）で `profile := (← IO.getEnv "SPARKLE_PROFILE").isSome` を**実行**し、`logProf`（5516–5522: `IO.eprintln`、`flushStderr`、`IO.FS.Handle.mk "/tmp/sparkle-profile.log"`、`putStrLn`、`flush`）は `profile = true` のときだけ動く。5523 の `logProf "entering"` と 5375–5459, 2167–2175 の呼び出しは `profile = false` では no-op。
- 翻訳器 `translateExprToWire`（根も子も共通で実行）: 7028（`SPARKLE_TRANSLATE_LIMIT` の `IO.getEnv`）、7040–7066（`callN % 10000 == 0` で `SPARKLE_PROFILE` を `IO.getEnv`、設定時のみ `IO.eprintln`/`flushStderr`/`Handle.mk`/`putStrLn`/`flush`）、6286（`SPARKLE_NO_LOOPCACHE`）、6505–6515（`SPARKLE_DEBUG_HWCALL` を `IO.getEnv`、設定時のみ `IO.eprintln` + `flushStderr`）。`ppExpr` は 683/688/717/5799/7456（直後に `throwError`、エラー経路）と 7115（`try ppExpr ty catch`、fvar の zeta 不成立の分岐。**成功 run で通らないとは言えない**）。`trace[sparkle.compiler]` は多数（6〜6700 台）。
- 後処理の `IO.getEnv "SPARKLE_NO_REGDEDUP"`（5692, 9189）は run の外（core の後）。

### 57.2 監査表
範囲の注意: `h0` は**根の開始世界 1 つ**での事実、`hs` は**到達世界から葉ステップ 1 つ**ごと、`hD`/`hG` は**到達世界×admissible 文脈×その族の全操作**、`hT` は**テレスコープ 4 行の継続則**（不変量 `I`・継続 `k` に全称）。混ぜない。

| | (a) 命題 | (b) 使う操作（Off run）と証明段 | (c) Off run に操作は存在するか | (d) 候補供給 |
|---|---|---|---|---|
| **h0** | `ProfOffW mref cref w`（S2mReach.lean:57）= `∀ mctx cctx, GetEnvProfileAt mctx mref cctx cref w`: 世界 `w`（根の開始世界 `w₀`）から `IO.getEnv "SPARKLE_PROFILE"` を走らせると `none` を返し Core env を変えない | **子 head の 5515 の lookup**（`synthesizeCombinational` 経由）。証明: `profOffW_of_reachedX`（S2mReach2:82）の `start` → `missRX`（S2mReach2:109, `KidEv` の profile 成分）→ `synthesizeChild_tripleH'X`（`jqhr_synthesizeChildX`, S2mReach3:126）。根自身の head は使わない（`coreHeadOff`）。 | **lookup は存在する**（子ごと、深さ ≥ 1 の各 miss）。`profile` が真のときのログ枝だけが存在しない（定義上 `headAt_of_profileOff` がその枝を `if_neg` で消す）。つまり h0 は「実行されない経路」ではなく「実行される lookup が `none` を返す」事実 | **調査範囲では未供給**。`IO.getEnv` は `@[extern] opaque` だが、opaque であることだけでは非導出性の証明にならない（S3g 訂正）。区別する: (i) `IO.getEnv` を実行して結果を検査する run についての**条件付き事実**（その run の結果が `none` なら…）と、(ii) 開始世界 `w₀` での `GetEnvProfileAt`・全葉ステップでの保存は別の主張で、(i) から (ii) は出ない。Tools 側の既存検査は `Environment → Name → Bool` の純関数で、process 環境を検査できない（この限定は妥当）。IO で入口が検査して `w₀` の `GetEnvProfileAt` に結ぶ橋は、調査範囲では新しい法則になる（禁止）。コンパイラ変更なら §57.3 案 A |
| **hs** | `ProfStepRX O w₀`（S2mReach.lean:129）: `ReachedX` な `w` から葉ステップ `w → w'`（`LeafStepX`: framed / diag / throws / cacheSet / depthSet）で `ProfOffW w → ProfOffW w'` | `profOffW_of_reachedX` の `step`。上と同じ `missRX` 以降 | h0 と同じ lookup が使う。葉ステップ自体は全ステップ（`ioEprintln`/`Handle.mk`/`setStderr` 系の Diag を含む）が存在 | **調査範囲では未供給**。葉ステップが環境変数を書かないことは、各操作（`IO.FS.Stream` のクロージャ、`Handle.mk` ほか）に世界の意味論を与える話で、`hG` と同じ根（非導出性を示したのではない）。Diag の族が閉じていること（`Diag` は `ioEprintln s` などを任意 `s` で許す）は型として分かるが、それは `ProfOffW` の保存を与えない。§57.3 案 A が入れば子 head の lookup が消え、`h0`/`hs` は**この経路では**不要（翻訳器 7040 の lookup は `DRow.ioEnv`（hD）で扱われ、`ProfOffW` は使われていない） |
| **hG** | `DiagEnvRX O e w₀`（S2mReach.lean:118）: `∀ mctx cctx p, adm → Diag p → ∀ w, quiet ∧ ReadsAt e ∧ ReachedX → ReadsAt e (endW … p w)` | `ropsRX.diag`（S2mReach.lean、`ropsRX` の `diag` フィールド）→ 以降の全 `childKeepsH_all_of_teleX`/`closeInstsM_runHX`。 | **Off run に診断の操作は存在し得る**: ① 子 head の `logProf`（5516–5522, `profile` 真のみ）、② 7040–7066 の tick（`SPARKLE_PROFILE` 設定時のみ）、③ 6509–6515（`SPARKLE_DEBUG_HWCALL` 設定時のみ。**別の変数で、`h0` は何も言わない**）、④ `ppExpr`（上記）。`hG` は「設定されているときのログ枝」を含む全称なので、`h0` があっても `hG` は定理にならない（`Diag` は `ioEprintln s` を任意 `s`・任意 stderr で許し、S1o の裁定どおり `setStderr` 済みの stream の `putStr` が cache を書き得る） | **調査範囲では未供給**。調査範囲では小さな実装変更で消える経路は見つかっていない（供給不能の主張ではない。③ は `SPARKLE_DEBUG_HWCALL` を読む別枝で、Off 入口が固定する `profile := false` の外。消すにはこの枝の除去 or Off の翻訳器の複製が要り、小さくない）。§57.3 案 B に記述 |
| **hD** | `DRowEnvRX O e w₀`（S2mReach.lean:112）: 上と同形で `DRow p`（`ioEnv n`/`monoMs`/`mkExprCache`/`localMk`/`whnf`/`inferType`/`isClass?`/`whnfUntil`/`instantiateForall`/`mkLambdaFVars`/`mkAppM`/`unfoldDefinition?`/`reduce`） | `ropsRX.frameQ` の `DRow` 分岐（`by_cases hnd : DRow p`） | 存在する（翻訳器全体が `whnf`/`inferType` 等を呼ぶ。`ioEnv` は 6286/6509/7028/7040 ほか） | **調査範囲では未供給**。`whnf`/`inferType`/`reduce` が Core env を保つことは `Lean.Meta` の実装の定理（opaque/partial を含む）で、小さくない。`ioEnv`/`monoMs` は IO extern（世界の意味論なし）。`mkExprCache`/`localMk` は新規 ref の確保で、`CellPrem` の `Fresh` 成分から原理的には出るが、`hD` を族ごとに分割する別の型（v10 の binder 変更）が要り、残りの行（`ioEnv`/`monoMs`/Meta 系）が `hD` に残るので**減る個数は 0**（binder は同じ名前のまま狭まるだけ）。今回は行わない |
| **hT** | `TeleRX O e w₀ := RefLawsATeleX (quietRX …) O.adm mref cref`（S2mReach.lean:123）: `forallTelescopeReducing`/`lambdaTelescope`/`withLocalDeclD`/`withLetDecl` の継続則。不変量 `I` と継続 `k` に全称、`I` は quiet と cv/sv/dv 保存を満たすもの | `jqhr_bodyStepX hT`（S2mReach3）、`childKeepsH_all_of_teleX`、`closeInstsM_runHX`/`closeInstsGM_runHX` | 存在する（翻訳器が telescope と local decl を使う） | **調査範囲では未供給**。`Lean.Meta` の telescope 実装についての法則。新 axiom で払ったことにはしない（§56.3 のまま）。reader 移動の同型の作業ではなく、`Lean.Meta` の意味論を作る作業 |

### 57.3 小さなコンパイラ変更（**実施していない。reviewer の判断を要する**）
- **案 A（h0/hs の子 head の lookup を消す）**: 子の実行が `synthesizeChild`（9210 付近）→ `synthesizeCombinational`（`CoreWith`, 5515）なので、Off の根 run が起動する子だけを profile 固定の経路（`synthesizeCombinationalCoreOff` の変種。`logProf := fun _ => pure ()`、`IO.getEnv` なし）で走らせる。【S3j 注: 以下の「`sparkleChildSynth` の登録先を Off の入口が呼ぶ間だけ別の関数にする」（一時 Ref 変更が必要）は S3g 時点の**旧案の候補**であり、必要条件ではない。§58.3 が義務を列挙し、S3h は採用しなかった（案 2 は不採用、案 3 を当面採用）】実現の一案は `sparkleChildSynth`（1042）の登録先を Off の入口が呼ぶ間だけ別の関数にすること（旧案）で、`initialize sparkleChildSynth.set (some synthesizeChild)`（9220 付近）、`synthesizeChild`、`synthesizeCombinationalOff`/`…CoreOff`/`…CoreOffR`（9019, 9096）、`synthesizeEntry`（9205–9208）の変更を伴う。出力は profile 未設定ならログ以外同一でなければならない（`#synthesize`/`#synthesizeVerilog`/`#showVerilog` の出力 baseline 272/272 の再実行が必要）。**効果は限定的**: 子 head の lookup が消えるだけで、翻訳器 7040 の lookup と `hG` の診断（③ 含む）は残る。`h0`/`hs` の 2 個が不要になる見込みだが、証明側では `missRX` の `KidEv` 定義と `childKeepsH` 一式（S2mReach2/3、S2dKids 等の `coreHeadOff` 周辺）を子の Off 版の head に付け替える必要があり、**小さくない**（単独の見積りでは 1 枚のコンパイラ変更 + 十数ファイルの再証明）。
- **案 B（hG）**: ③ の `SPARKLE_DEBUG_HWCALL` 枝と 7040 の tick を Off の run から除く（翻訳器を `profile`/`debug` 引数付きにして Off が固定する）。翻訳器の全再帰呼び出しへの引数追加で、Elab.lean の数百行に及ぶ。**小さくない**。
- どちらも**実施せず**、reviewer の裁定を待つ。

### 57.4 判定（Step 2 の範囲）
- h0 / hs（profile 無効）: 調査範囲で未供給 or 案 A。供給した定理・検査はない。
- hG: 調査範囲で未供給 or 案 B。供給なし。
- hD / hT: 調査範囲で未供給。
- 上の「未供給」は調査範囲の記述で、非導出性（供給不能）の証明ではない。
- よって v10・Check49 はこの時点では作らない（binder を減らす提供物がない。偽の v10 は作らない）。v9 は不変。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 58. S3h（Issue `sparkle-fg-circuit-pilot`）: 案 A（pilot 専用の profile-free 子経路）— 最小の関数境界の調査と停止（実装なし）

土台 `a3e6912d`（= `5e456b5e` + docs §56/§57 訂正の 1 コミット）。`Sparkle/`・`Tools/`・`Tests/` は**変えていない**。新 law・axiom・sorry・native_decide・TRUSTED なし。共有 compiler 変更: **なし**（したがって通常 272/272 の再比較は今回は不要）。v10・Check49 は**作っていない**（偽の v10 は作らない）。

### 58.1 子が pilot の根から呼ばれる経路は 2 本あり、どちらも大域 `IO.Ref sparkleChildSynth` を読む
1. 機械経路: `synthesizeFromConst`（5368）→ `synthesizeMachineCertified`（5313）→ `closeInstsM`／`closeInstsGM`（5267／5290、`sparkleChildSynth.get`、5270／5293）。
2. 翻訳器経路: `Rec.synthesizeCombinational`（6422、`childSynthEntry`＝5712 が `sparkleChildSynth.get`）→ `handleDefinitionUnfold`（6491、6507・6559 付近で `isHardwareModule`）と `translateInstanceOrFallback`（8796、`childSynthEntry` を 8802・8820）。呼び出し側は `translateExprToWire env`（8961）の knot の内側で、`Rec.*` の handler 群（8966–9002 のラッパ）が `translateExprToWire` を section variable として受ける（5793）。

どちらの経路も呼ぶ先は `synthesizeChild`（9217）＝ `sparkleChildCache`（名前だけが key。9218）→ `synthesizeCombinational`（profile 版：`CoreWith` 5515 の `IO.getEnv "SPARKLE_PROFILE"`）。

### 58.2 「明示的な child callback」を実装する場合の関数境界（測定）
- 機械経路だけなら小さい: `closeInstsM`／`closeInstsGM`／`synthesizeMachineCertified`／`synthesizeFromConst` に `synth` 引数を足し、`CoreOffR` の変種から渡す（既存の定義は既定値＝`sparkleChildSynth.get` で不変にできる）。
- **翻訳器経路は小さくない**: `Rec.synthesizeCombinational`（6422）は `Rec` の section の定義で、callback を渡すには section variable を 1 つ足す（5793）ことになる。使う def は `Rec.synthesizeCombinational` を呼ぶ `handleDefinitionUnfold`（6491）とその呼び出し側の連鎖（`translateExprToWireApp` 6894、`translateExprToWireImpl` 7020、8966–9002 のラッパ、`translateStep`／`translateInstanceOrFallback`）。これらは全て引数が 1 つ増え、定義の形が変わる。`Rec.handleDefinitionUnfold`／`Rec.synthesizeCombinational`／`Rec.translateExprToWireImpl` を参照する `Tools/`・`Tests/` は **54 ファイル**、`sparkleChildSynth`／`synthesizeChild`／`childSynthEntry` を参照する `Tools/` は **146 ファイル**（`grep -l`）。これらの定理の文・`rfl` 等式・`unfold` が影響を受ける。「共有 compiler は小さく」「通常 Off／synthesizeEntry／initialize は不変」の条件のもとで、翻訳器の knot（`translateExprToWire env`）を callback 付きで二重化する案は、`Rec` 全体の複製に近い。
- 結論: **最小の関数境界は機械経路には切れるが、翻訳器経路には切れていない**。pilot の子は両経路から呼ばれ得る（`childKeepsH` 系は機械経路、`KidEv`／`missRX` は `synthesizeChild` 経由で両方を含む）ので、機械経路だけに callback を渡しても、翻訳器経路の子は profile 版のまま残る。この場合 `h0`／`hs` を外すことはできない。

### 58.3 共有 `IO.Ref` を一時的に set する案（実装していない）— 採るなら証明すべきこと
callback が翻訳器経路で小さく実現できないため、残る案はこの形になる。reviewer の条件（「そのまま承認するものではない」）のとおり、実装前に義務を書く:
1. 例外: run が throw したとき `sparkleChildSynth` が元の値へ戻ること（`try … finally`）と、`MetaM` の例外・`catch` 経路（翻訳器の rollback `snapshotWireCaches` は ref を戻さない。5745 付近の注記）。
2. 再入: 根の run 中に `synthesizeChild` が再入する（深さ ≥ 2）とき、pilot 用の値が子の中でも保たれ、`depth` 復元（`sparkleSynthDepth`）と干渉しないこと。
3. 並行実行: 別の `#synthesizeVerilog` が並行して走ると ref を読み得る（Lean の `elab` は並行し得る）。この排他を証明するか、並行しない根拠が要る。
4. 復元: 出口で ref が入口の値に等しい（成功・失敗の両方）。
5. 読み取り world: `sparkleChildSynth.get` が読む world と、そこに入る関数が `Core` env を変えないこと。Hoare 三つ組の `ReadsAt` に ref の値を追加する必要があり、`CellPrem`／`Fresh` の枠組み（`hcell`）への影響を確かめる。
6. cache: `sparkleChildCache` は名前だけが key で、通常経路（profile 版）と同じ cache を共有する。pilot の子 entry が新経路の実 run だけから来る（旧 diagnostic 経路の結果が混入しない）ことは、cache の初期値＝`{}`（depth 0 でクリア、9126）と、その間に別の entry が書かないこと（上の 3 と同根）から出す必要がある。
7. 証明の再接続: 子を変えると `offR_to_off`（`Tools/ShippingFGCircuitS3b2Core.lean`）の「一般の OffR→旧 Off の橋」は使えない。新しい子の入口に対する `KidEv`／`missRX`（S2mReach2:109）・`childKeepsH`・`closeInstsM_runHX`・closing／top／最終 artifact を再接続する（§57.3 の見積り: 十数ファイル）。
8. `h0`／`hs` が本当に消えるかは、実装後の完全型で判定する（`KidEv` の profile 成分を子の head に付け替えると、別の全称仮説が出る可能性がある。出たらその名前で報告し、`h0`／`hs` の付け替えとは数えない）。

### 58.4 停止の理由と、reviewer に要る判断（実装前）
- 欠けているもの（正確な文）: 「`Rec.synthesizeCombinational`（6422）が使う子の synthesizer を、`sparkleChildSynth`（大域 ref）ではなく呼び出し側の引数から受け取る」翻訳器 knot の定義と、それを使う `Tools/` の再証明。または 58.3 の 1–6 の義務を全て満たす ref 一時 set の定義と証明。どちらも、現在の「共有 compiler は小さく」の条件の外にある。
- 選択肢（reviewer が選ぶ）:
  1. 翻訳器の `Rec` 全体に callback の section variable を足す（共有 compiler の大きな変更、54＋ファイルの再証明、通常 272/272 の再比較）。
  2. ref 一時 set（58.3 の義務を全て証明。小さな Elab 変更だが並行実行の義務が最も重い）。
  3. 案 A を採らず、`h0`／`hs` を現行どおり明示の仮説として残す（v9 のまま）。
- `hD`／`hG`／`hT` は今回も触れていない。`hG` は案 A が通っても解けたと数えない（翻訳器の tick／debug／`ppExpr` が残る）。TRUSTED・解決済み行にはしていない。
- 追加の実行は不要な調査だった（コードの読み取りと `grep -l` のみ）。ビルド・Check は実行していない（`Sparkle/`・`Tools/`・`Tests/` が不変のため、§56 の記録と Check48 の結果がそのまま適用される）。

### 58.5 【S3j 追記・reviewer 指摘】S3h の評価の限界（上の 58.2–58.4 を読むときの注記）
- **54／146 は参照ファイル数であり、再証明が必須な件数とはまだ確定していない。** `grep -l` が数えたのは `Rec.handleDefinitionUnfold`／`Rec.synthesizeCombinational`／`Rec.translateExprToWireImpl`（54）または `sparkleChildSynth`／`synthesizeChild`／`childSynthEntry`（146）を**名前で参照しているファイル**であって、callback を足したときに文・`rfl` 等式・`unfold` が実際に壊れるファイルの数ではない。
- **wrapper／`rfl` 維持の経路は未検証。** callback を持つ内部定義と、旧名・旧引数の特殊化 wrapper（既定の callback `= sparkleChildSynth.get` を渡す）で定義的等式を保てる可能性は試していない。将来 選択肢 1 を再開するときは、小さい代表（例: `Rec.handleDefinitionUnfold` 1 つ）で wrapper の `rfl` 維持を先に試し、実際に壊れる範囲を測ってから見積りを出す。
- **選択肢 1 が S3 一般化に必須とは断言しない。** §58.4 の選択肢 1 は `h0`／`hs` をこの経路で外すための一案で、S3 の一般化に必須だとは示していない。
- **§58 は「pilot の成功 run が 2 本の経路の両方を通る」ことを示していない。** 58.1 が示したのは、一般に 2 本の経路が `sparkleChildSynth` を読むこと（コード上の存在）であり、固定した pilot（`hftRoot`）の成功 run が両方を実際に通ることは別の主張で、証明も測定もしていない。経路排除の証拠が無い間は、機械側だけを変えても `h0`／`hs` は外れない（§58.2 の結論）。
- §57.3 の「`sparkleChildSynth` の登録先を呼び出し間だけ別の関数にする（一時 Ref 変更が必要）」は S3g 時点の旧案の候補で、§58.3 の義務を満たす形では採用していない（S3h は案 3 を当面採用、案 2 は不採用）。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。binder の変更なし（v9 の 9 引数のまま）。


## 59. S3i（Issue `sparkle-fg-circuit-pilot`）: 残り仮説 `L`（Laws）・`hstart`（Start）・`hcell`（CellPrem）の棚卸し — 命題・消費する操作・同時に成立する適用条件・FG/T1 行・供給候補

土台 `aa9bff12`。docs のみ。`Sparkle/`・`Tools/`・`Tests/` は変えていない。ビルドも Check も実行していない（grep と読み取りのみ）。新 law・axiom・sorry・native_decide・TRUSTED なし。v9 は不変（9 引数 `L hstart hr hcell hD hG hT hs h0`、`Tools/ShippingFGCircuitS3f2Final.lean:115–128`）。

reviewer 方針（`hD/hG/hT` を恒久的な外部境界として終わらせず、使用操作の限定・既存法則からの供給・実装変更の経路を残す。CellPrem/Laws/Start は同時に成立する具体的な適用条件と対応する FG/T1 行を整理する。残義務を隠した一般化より、この pilot の前提を閉じることを優先）に沿い、この節は **`L`・`hstart`・`hcell` の 3 束** を field 単位で扱う（`hD/hG/hT/hs/h0` は §57/§58 の記録のまま。ここでは 3 束との関係のみ §59.7 に書く）。

規約: 「供給できない」とは書かない。供給の欄は (1) 既存定理、(2) run から導ける定理（スケッチ。証明していない）、(3) Tools 側検査（(B) パターン）、(4) 小さな compiler 変更（行番号）、(5) 「調査範囲では未供給」＋足りないもの、のいずれか。(2) は**証明していない**スケッチであり、成否は実装時に決まる。

### 59.0 読み方（共通の記法と事実）

- `E(p,w) := endW mctx mref cctx cref p w`（`Tools/ShippingChildInv.lean:300`）、`Δ(p,w) := cv E = cv w ∧ sv E = sv w ∧ dv E = dv w`（`cv/sv/dv` は `Tools/ShippingChildBndCore.lean:43/45/47`＝ref `sparkleChildCache`/`sparkleChildSynth`/`sparkleSynthDepth` の読み出し）。
- **`L : Laws mref cref` は v9 の全称 binder（証人）**であり、`quiet` はその field（データ。`Tools/ShippingChildInvA.lean:263` の `RefLawsAOps.quiet`）。したがって `quiet` を何にするかは `L` の側の選択で、`hstart` の `quiet w` と `L` の他の field は同じ `quiet` を共有する（束ねられている）。v7 以降の証明は `L.toX`（`Tools/ShippingFGCircuitS3cTop.lean`、`⟨L.O.toX, L.T.toX⟩`）を使い、`adm := AdmCtx quiet`。`RefLawsAOpsX.adm_closed`（`Tools/ShippingFGCircuitS2sAdmChildInvA.lean:39` 以降）は既存定理 `admCtx_closed`（同ファイル）で供給済みで、`L` の追加前提にはならない。
- 実行環境の共通事実（Elab.lean）:
  - 根の run `synthesizeCombinationalCoreOffR`（9096–9172）: 9098 `sparkleSynthDepth.get`、9126（`depth == 0` のとき）`sparkleChildCache.set {}`（ほか側 ref の `set {}` 9115–9140）、9142 `sparkleSynthDepth.set (depth+1)`、9164 `sparkleSynthDepth.modify (· - 1)`（finally）、`readerOk`＝`pilotReaderOk2` は 9142 以降の `doSynth` 内（`getConstInfo`/`getEnv`）。
  - 子: `synthesizeChild`（9217–9220、`sparkleChildCache.get` → miss なら `synthesizeCombinational` → `sparkleChildCache.modify (·.insert n r)`）。`sparkleChildSynth.get` は 5270・5293（機械経路 `closeInstsM`/`closeInstsGM`）と 5712（翻訳器経路 `childSynthEntry`）。子の head は 5544（depth get）・5621（cache set {}）・5641（depth set）。`initialize sparkleChildSynth.set (some synthesizeChild)` は 9222（モジュール初期化時 1 回）、宣言は 1042。
  - telescope 系の呼び出し箇所（翻訳器が到達し得る）: 5439・6568・1879・1936・1999・2033・8594（`Lean.Meta.lambdaTelescope`/`forallTelescopeReducing`）、141・150・8017（`withLocalDeclD`/`withLetDecl`）。**この root の run がどの箇所を実際に通るかは列挙していない**。
- 台帳（FG 75 / T1 57。本体 8649968e §12.24 はこの tree に無い。§8 と同じ注意）の行 ID は `Tools/ShippingGenFGLedgerPremises.lean` の文面の注記から取る: `L`＝**A.P-01（= T1L-01）**（40 行）、`Start`＝**A.P-02**（50 行、`EntryWitness` は Start と run A.P-04 と ReflectsAll D.D-1 を 1 つにまとめた束）、`CellPrem`＝**C.EN-4**（41 行）。【S3j 訂正】§8 の表は `Laws L` を A.P-02 と書いていたが誤り。台帳本体（`scripts/gen2/PREMISE_LEDGER.md` 8649968e の 56–57、99–100、164、325–326 行を coder が確認）で `Laws` = A.P-01（= T1L-01。merged B.F-3, D.E-10。同台帳に「非空虚な Laws の値は、この調査では見つからなかった」）、`Start`（AdmCtx ∧ JQC）= A.P-02（= T1L-02。merged A.P-03, C.RR-1, B.F-2, D.E-11, D.D-6）、`CellPrem` = C.EN-4。Lean 側の注記（`ShippingGenFGLedgerPremises.lean`）が正しく、§8 を直した。**field 単位の行 ID は tree 内に無い**ので、field の (d) 欄は「束の行」を書き、「field 単位の行なし」と明記する。
- 既存の関連定理: `Tools/ShippingHeapModel.lean` の `HeapLaws.model`／`heapLaws_sat`／`heapLaws_nonempty`（334–432）は、抽象 heap（3 つの追跡 cell ＋ `other n`）上で RefLawsCore の ref のみの断片を満たす**無矛盾性**。実 `Void IO.RealWorld`・`ST.Ref` の世界（`@[extern] opaque`）への橋は無く、`RefLawsAOps`/`RefLawsATele`（`FramedA`・telescope 継続）とも別の型。よって「L が充足可能」の根拠にはなるが、実 run への供給ではない。

### 59.1 この root の run に対する「同時に成立する」適用条件（3 束共通。(c) 欄はこれを参照する）

v9 の結論が意味を持つのは、次が**同じ世界 `w`（根の開始世界）・同じ run `hr` で同時に**成り立つときだけである。

| 記号 | 条件 | 何が決めるか |
|---|---|---|
| W1 | `hr : RunsTo (synthesizeCombinationalOffR pilotReaderOk2 hftRoot) mctx mref cctx cref w (b,D') w'` | コマンド `#synthesizeVerilogPilot2`（`Tools/ShippingFGCircuitS3f2Final.lean:143`）が `pilotEntry2`（111）を呼ぶ。`inlinerFuelGuard`（147）が先に走る。run の guard が真であることが `pilotReaderOk2`（91）の健全性で `CheckedEnv`・子 reader を与える |
| W2 | **深さ**: 開始時 `dv w = 0`（`sparkleSynthDepth` が 0）。9098 で読まれ、9126 の cache クリアと 9142 の `depth+1` の分岐を決める | `Start.JQC 0` の `dv` 成分 |
| W3 | **子の合成関数**: `sv w = some synthesizeChild`（`sparkleChildSynth` が 9222 の登録値）。5270/5293/5712 で読まれる | `Start.JQ` の `sv` 成分。通常は `initialize` が 1 回設定し、この run の前に別の経路が上書きしないこと |
| W4 | **cache 状態**: 開始時の `sparkleChildCache` の値 `cv w` は実子の結果だけ（`CacheInvA`）。ただし run は 9126 で `{}` にクリアする。深さ ≥ 1 の各子は `synthesizeChild`（9218）で hit/miss | `Start.JQC` の cache 成分。run 内では `cacheSet` で `{}` に確定する |
| W5 | **文脈**: `mctx.canUnfold?` の callback が inert（または `none`）。コマンド経路は `liftTermElabM` の既定の `Meta.Context`。翻訳器内の telescope／`withLocalDecl*` の継続文脈は `adm`（`admCtx_lctx` 等、`ChildInvA.lean:96–112`）で保たれる | `Start.AdmCtx`、`L.T.*` の継続の仮定 |
| W6 | **quiet**: `L.O.quiet w`。run の各 leaf 操作の後も `quiet` が保たれる（`frameQ`）。診断（`ioEprintln`、`Handle.mk` 等）が追跡 3 ref と quiet を壊さない世界（stderr が cell を書く stream に差し替えられていない等。§57 の `hG` と同根） | `Start.JQ.quiet`、`L.O.*` の全 field |
| W7 | **環境**: 実 run の `ReadsAt (envAt cref w)`、`mref ≠ cref`、`ReadWorld cref` 等の cell 前提（`hcell`）。v9 は `env₀ := envAt cref w` で `readsAt_self` | `hcell` |
| W8 | **profile**: `SPARKLE_PROFILE` 未設定（子 head の 5515 の lookup）。`h0`/`hs` の領域 | 3 束の外（§57/§58） |

W2〜W7 は互いに独立ではない: W2/W3/W4/W6 は `JQC 0 w` の 4 成分で 1 つの world 述語、W6 は `L` の `quiet` と、W7 は `hcell` と、同じ world `w`（と同じ `mref cref`）の上で成立する必要がある。**v9 はこれらが同時に成り立つ具体的な world を 1 つも与えていない**（全称）。

### 59.2 `L : Laws`（束の行: A.P-01 = T1L-01。field 単位の行なし）

`Laws := { O : RefLawsAOps MkRefd mref cref, T : RefLawsATele O.quiet mref cref }`（`Tools/ShippingGen2Defs.lean:46`）。`O` の定義は `Tools/ShippingChildInvA.lean:263`、`T` は 301。`FramedA Fresh p`（139–179）は許される MetaM 操作の族（`cacheGet`/`synthGet`/`depthGet`/`side*`/`ioEnv`/`constInfo`/`env`/`fvarThrowUnknown`/class-D の `whnf` ほか/`metaGet`/`coreModifyTrace`/`metaModify`/`mkExprCache`/`localMk`…）。

| field | (a) 命題（`AdmCtx quiet mctx cctx` の下、`w` は `quiet w` から） | (b) 使う操作（Elab.lean 行）と消費する証明段 | (c) 適用条件（§59.1） | (d) 行 | (e) 候補供給 |
|---|---|---|---|---|---|
| `O.quiet` | データ（`Void IO.RealWorld → Prop`）。命題ではない | 全 field と `Start` が参照 | W6。選び方は証人の自由（`fun _ => False` なら `Start` が偽、`fun _ => True` なら `diag` が `setStderr` 済み stream で偽になり得る §57） | A.P-01 | **未供給**（供給対象は quiet の「具体的な選び方」）。具体選択の候補: `quiet w := (cv/sv/dv の不変量 ∧ stderr が cell を書かない)`。後者の述語化が足りないもの。調査範囲では実世界の述語を与えていない |
| `O.diag` | `Diag p → Δ(p,w) ∧ quiet E(p,w)` | `ioEprintln`・`Handle.mk`・`putStrLn`・`flush`・`ppExpr` 等（子 head 5516–5522＝profile 真のみ、翻訳器 7040–7066/6509–6515＝環境変数設定時のみ、`ppExpr` 7115 ほか）。`ropsRX.diag`（`S2sAdmS2mReach`）、`ChildKeeps`、`S3cFinal` | W6、W8。Off run では多くが「設定時のみ」の枝（§57.1） | A.P-01（`hG`＝FG D.T-4m2 は別行） | **調査範囲では未供給**。`Diag` は `ioEprintln s` を任意 stream で許すので、ref 前提だけからは出ない。小さな変更で枝を消す案は §57.3 案 B（小さくない） |
| `O.frameT` | `Throws p → Δ ∧ quiet E` | 投げる操作（`throwError` 系）。`ChildKeeps`/`ChildInv`/`ChildBalance` | W6 | A.P-01 | (2) スケッチ: `Throws p` は世界を変えずに投げる操作の族であれば `E(p,w) = w` の形で `Δ`・`quiet` は自明。`Throws` の定義（`ChildInv.lean:281`）を読んで**各構成子が世界を変えないこと**を確認する必要がある（未確認）。確認できれば既存定理の拡張で供給（`ReadWorld` 等の cell 前提は不要の見込み） |
| `O.excOk` | `Op p → p … w = .error e w' → OkExc e`（`quiet w`） | 例外のクラス。`ChildVCA`/`ChildKeeps`/`ChildBalance` | W6。`OkExc`（クラス）は例外の中身の述語 | A.P-01 | **調査範囲では未供給**: 例外クラスは `Lean.Meta` 実装が投げる例外の形（`Op p` の各操作）の述語で、`ChildInvA.lean:77` の注記の `O-cancel`（中断例外）が未決。足りないもの: 各 `Op` 構成子の throw 形の列挙 |
| `O.frameQ` | `FramedA Fresh p → quiet E(p,w)` | 全 framed 操作の後の quiet 保存。`ChildCacheA`/`ChildKeeps`/`S2hHist` | W6 | A.P-01 | **調査範囲では未供給**（`quiet` の選択次第で意味が決まる。選択が決まれば、frame 系 field と同じ cell 前提に帰着する見込み） |
| `O.cacheSetQ` | `RunsTo (sparkleChildCache.set v) … w u w' → quiet w → quiet w'` | 9126・5621・9220（`modify`＝`ST.Ref.modify`）。`ChildBndCore`/`S2hHist` | W4、W6 | A.P-01 | 同上（quiet 依存） |
| `O.depthSetQ` | 同上（`sparkleSynthDepth.set`） | 9142・5641・9164 | W2、W6 | A.P-01 | 同上 |
| `O.frame` | `FramedA Fresh p → Δ(p,w)` | 非 class-D の framed 行。`ChildKeeps`（15 箇所）・`ChildHarness`・`ChildInvA` | W6、W7。`side*`/`get`/`constInfo`/`env` は追跡 3 ref を変えない、が命題の中身 | A.P-01 | (2) スケッチ: `side*` 行は「別 cell の set は追跡 ref の読みを変えない」＝ref 間の `SetFrame`（`StRefCorrespondence.lean:47`）が要る。**現在の `CellPrem` は `SetFrame r cref`（Core 状態 ref に対する枠）しか持たず、追跡 3 ref と side ref の間の `SetFrame` は含まない**（`EnvFrame3.lean:58–62`）。したがって既存 `CellPrem` からは出ない。足りないもの: 追跡 3 ref × 24 side ref（`SideRef`、`ChildInv.lean:69`）× `MkRefd` ref の間の `SetFrame`（読み取りは `ReadWorld`）。これは `hcell` の拡張（C.EN-4 の行の拡張）であり、**L の前提を hcell 側の前提に置き換えるだけで総数は減らない**。class-D 行（`whnf` 等）は別（`hD`） |
| `O.cacheSet` | `RunsTo (sparkleChildCache.set v) … → quiet w → cv w' = v ∧ sv w' = sv w ∧ dv w' = dv w` | 9126（`set {}`）、5621、9220 | W4 | A.P-01 | (2) スケッチ: `cv w' = v` は **cache ref の `SetGet`**（`StRefCorrespondence.lean:44`）、他 2 成分は追跡 ref 間の `SetFrame`。**`CellPrem` は `SetGet cref` しか持たず、cache/synth/depth の `SetGet` は無い**（9 番目の `SetGet cref` は Core ref）。上と同じ置き換えになる |
| `O.depthSet` | `sparkleSynthDepth.set v → cv w' = cv w ∧ sv w' = sv w ∧ dv w' = v` | 9142、5641 | W2 | A.P-01 | 同上 |
| `T.telescope` | `forallTelescopeReducing ty k` の継続則: 不変量 `I`（`I → quiet`、`cv/sv/dv` 保存と quiet 保存で閉じる）に対し、継続 `k` が各 `adm` 文脈で `Keeps I` なら全体が `Keeps I` | 5439・6568・1936・1999・2033・8594（telescope）。`jqhr_bodyStepX hT`（S2mReach3）、`childKeepsH_all_of_teleX` | W5、W6 | A.P-01（`hT`＝FG D.T-4m3 は強化版で別行） | **調査範囲では未供給**。`Lean.Meta.forallTelescopeReducing` は `partial`/`@[extern]` を含む Meta 実装についての継続則。足りないもの: `Lean.Meta` の telescope の世界遷移の意味（`withNewLocalInstances`/`lctx` 更新、`cleanup`）。new axiom で払わない（§56.3） |
| `T.lamTelescope` | `lambdaTelescope e k cleanup` の同形 | 5439・1879 | 同上 | A.P-01 | 同上 |
| `T.localDecl` | `withLocalDeclD n ty k` の同形 | 141・（8017 は `CompilerM` 版が 150 経由） | 同上 | A.P-01 | 同上 |
| `T.letDecl` | `withLetDecl n ty v k` の同形 | 150・8017 | 同上 | A.P-01 | 同上 |
| `adm_closed`（`L.toX` で必要） | `CtxClosed (AdmCtx quiet)` | 文脈更新 `admCtx_lctx` 等 | W5 | no row（FG 回路ローカル） | **既存定理**: `admCtx_closed`（`S2sAdmChildInvA.lean`、`ChildInvA.lean:96–112` の `admCtx_*` を使う）。供給済み |

`L` 全体の注意:
- **`L` の 14 field は 1 つの `quiet` を共有する 1 束**（A.P-01 の 1 行。field 単位の行は tree に無い）。`frame`/`cacheSet`/`depthSet`/`frameQ` の ref 部分（上の 4 行）は、追跡 3 ref・side ref・`MkRefd` ref 間の `ReadWorld`/`SetFrame`/`SetGet` から導ける見込み（スケッチ）だが、それらは `hcell`（C.EN-4）に**追加の前提として移る**ので、v9 の binder 数は `L` が減っても `hcell` が増えない保証はない（同じ型の前提 ＝ 実 `ST.Ref` の意味）。
- `diag`/`excOk`/telescope 4 行/class-D は Lean 実装（IO extern・`partial`・`@[extern]`）の意味に依り、既存定理・Tools 側検査では出ない。調査範囲では未供給。
- 実装変更の経路（(4)）: `L` を縮める最小の変更は、Off 経路の追跡 ref の使用を**純粋な状態**で受ける関数にすることだが、これは §58 の callback 案と同じ規模（`Rec` 全体、54＋ファイル）で、共有 compiler の「小さく」の条件の外。小さい変更では `L` の field は消えない。

### 59.3 `hstart : Start L mctx cctx w`（束の行: A.P-02）

`Start L mctx cctx w := AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w`（`Tools/ShippingGen2Defs.lean:52`）。`JQC O D w := JQ O.quiet D w ∧ CacheInvA O (cv w)`（`Tools/ShippingChildCacheA.lean:120`）、`JQ quiet D w := quiet w ∧ sv w = some synthesizeChild ∧ dv w = D`（`Tools/ShippingChildVCA.lean:53`）、`CacheInvA O m := ∀ c r, m.get? c = some r → RealChildA O c r`（同 CacheA）。

| field | (a) 命題 | (b) 操作と消費段 | (c) 適用条件 | (d) 行 | (e) 候補供給 |
|---|---|---|---|---|---|
| S1 `AdmCtx quiet mctx cctx` | `∀ f, mctx.canUnfold? = some f → InertUnfold quiet f` | 全 `L.*` field の `adm` 前提。`S3cTop.lean` の `StartX := ⟨hstart.1, jqc_toX hstart.2⟩`、`hftTop_of_runRX`、`hftCoreCloses_of_kidsR''` | W5。コマンド経路は `liftTermElabM` の既定 `Meta.Context`（`canUnfold? := none`。**Lean の既定の確認は未実施**、要確認） | A.P-02（Start の束） | **(1) 既存定理** `admCtx_none`（`ChildInvA.lean:82`）: `mctx.canUnfold? = none → AdmCtx quiet mctx cctx`。**(3) Tools 側検査**: `pilotEntry2` を `do unless (← read).canUnfold?.isNone do throwError …; synthesizeCombinationalOffR pilotReaderOk2 declName` に変え、v10 の `hr` をこの wrapper の run にする。`RunsTo.bind`（`EntrySoundness.lean:946`）で分解し、`read` の RunsTo 補題（新規、小）で `mctx.canUnfold? = none` を得る。**Tools 側のみ**（compiler 変更なし）。現在の v9 の `hr` は `synthesizeCombinationalOffR` 自体の run なので文の変更になる |
| S2 `quiet w` | `L.O.quiet w` | `JQ` の第 1 成分。`cacheSet`/`depthSet` の前提（`quiet w`）として最初の `set` から消費 | W6 | A.P-02（`quiet` は A.P-01 の `L` と共有） | **調査範囲では未供給**。`quiet` が `L` の field（§59.2 `O.quiet`）なので、`L` の具体選択が決まるまで述べられない |
| S3 `sv w = some synthesizeChild` | `readOf sparkleChildSynth w = some synthesizeChild` | 5270・5293・5712 の `sparkleChildSynth.get`（子 entry が none なら `closeInstsM` は none を返す）。`RealChildA.run.synth`（`ChildCacheA.lean:105`）、`missRX` | W3。`initialize`（Elab 9222）の設定値が run まで保たれる | A.P-02 | **調査範囲では未供給**。関数値（クロージャ）の等号は決定不能で、Bool の Tools 検査にできない。(4) 小さな compiler 変更案: `depth == 0` のとき 9126 の並びに `sparkleChildSynth.set (some synthesizeChild)` を足す（同じ値の再設定。出力不変の見込み、要 272/272 の再比較）。**ただし** `sv w₁ = some synthesizeChild`（set 後の世界）を得るには `sparkleChildSynth` の `SetGet` が要り（`CellPrem` に無い。§59.2 の `cacheSet` と同じ）、証明も開始世界を `set` 後に移す再構成になる。S3 が `hcell` 側の前提に移るだけで減らない見込み。並行する別の elab が同 ref を書く場合の排他は §58.3 の 3 と同根 |
| S4 `dv w = 0` | `readOf sparkleSynthDepth w = 0` | 9098 の `depth ← get` と 9126/9142 の分岐。`JQ` の `dv` 成分、`depthSet` の初期 | W2 | A.P-02 | **(3) Tools 側 wrapper 検査**: S1 と同じ wrapper に `unless (← sparkleSynthDepth.get) == 0 do throwError …` を足す。wrapper の run から、`ReadWorld`（`hcell.1` の depth cell の `ReadWorld`、`StRefCorrespondence.lean:41`）で world が変わらないことと、get の戻り値＝`readOf sparkleSynthDepth w`（`readOf_get`、同 :52 付近）から `dv w = 0` を導く（スケッチ）。**Tools 側のみ。ただし `ReadWorld` の depth cell は既に `hcell` が持つので新しい前提なし**。compiler の `depth` 分岐（9098）の 1 本目は読み取りなので、wrapper 無しでは導けない |
| S5 `CacheInvA O (cv w)` | 開始時の cache 値が実子の結果だけ | `RealChildA` の `cache` 成分。`JQC 0` からの `jqc_toX`、`kid_shipsResWX` | W4。run は 9126 で `cache.set {}` するので、開始値は実質使われない | A.P-02 | **(2) run から導けるスケッチ**: 9126 の `sparkleChildCache.set {}` の後は `L.O.cacheSet`（`cv w' = {}`）と `cacheInvA_empty`（`ChildCacheA.lean`）から成り立つ。ただし、証明が `JQC 0 w` を開始世界 `w` で消費しているので、**開始世界を 9126 の後の `w₁` に移す再構成**（`offR_to_off`、`S2mReach2` の `start`／`missRX`、`profOffW_of_reachedX` の `start`）が要る。再構成後は `Start` の S5 だけが消え、他は残る。ここで使う `cacheSet` は `L` の field（§59.2、`SetGet` を要する）なので、`L`/`hcell` の前提は減らない。難易度: 中（`Tools/` の十数ファイルの開始世界の付け替え。§58.3 の 7 と同種） |

`hstart` 全体の注意:
- A.P-02 は `EntryWitness`（`Start` と run A.P-04 と `ReflectsAll` D.D-1 を 1 行にまとめたもの。`Premises.lean:50`）の行で、**field 単位ではなく束**。S1・S4 を (3) で外しても A.P-02 の行は S2・S3・S5 が残るので、行は減らない（reviewer の「残義務を隠さない」に従い、減ったと数えない）。
- 具体的な「同時に成立する」例: 開始世界は、(i) `lake env lean`/LSP が `import Sparkle…` を終えた直後、(ii) `sparkleSynthDepth = 0`（以前の synthesize が `finally` で `modify (· - 1)` 済み。例外終了でも `try … finally` 9160 付近で戻る）、(iii) `sparkleChildSynth = some synthesizeChild`（9222 の初期化のみ）、(iv) `canUnfold? = none`、(v) 標準の stderr。これを 1 つの world `w` についての 1 本の主張にするのが `JQC 0 w ∧ AdmCtx` で、**(ii) の「前の run が終わった」は別 run の事後状態の主張であって、この run の `hr` からは出ない**。

### 59.4 `hcell : CellPrem MkRefd mref cref`（束の行: C.EN-4）

`CellPrem Fresh mref cref := CellOK cref sparkleChildCache ∧ CellOK cref sparkleChildSynth ∧ CellOK cref sparkleSynthDepth ∧ (∀ r, SideRef r → CellOK cref r) ∧ (∀ σ r, Fresh σ r → CellOK cref r) ∧ ReadWorld mref ∧ SetFrame mref cref ∧ mref.ref ≠ cref.ref ∧ ReadWorld cref ∧ SetGet cref`（`Tools/ShippingGen5EnvFrame3.lean:58`）。`CellOK cref r := ReadWorld r ∧ r.ref ≠ cref.ref ∧ SetFrame r cref`（同 :55）。`ReadWorld r := ∀ w, getW r w = w`、`SetFrame r r' := r.ref ≠ r'.ref → ∀ v w, readOf r' (setW r v w) = readOf r' w`、`SetGet r := ∀ v w, readOf r (setW r v w) = v`（`Tools/ShippingStRefCorrespondence.lean:41/44/47`。いずれも「実ランタイムの PREMISE」と注記されている）。

実 run での消費（v9 の経路）: `readerOk_of_run`（`S3b2Final.lean:80`）の `headAtOff_of_cellPrem`（`S1qHead.lean:43`＝`envFrame_coreHeadOff`、`ReadWorld cref`・cache/synth/depth の `CellOK`）と `envFrame_getConstInfo ∘ getEnvFrame_of_cellPrem`（`S1hFrame.lean`）。`ropsR/ropsRX`（`S2mReach.lean:102–146`）は `envFrameEnd_framedA`（`EnvFrame3.lean` の E2）と `envFrameEnd_set`（`hcell.1.2.1`/`hcell.2.2.1.2.1` ほか）を使う。

| field | (a) 命題 | (b) 操作（Elab 行） | (c) 適用条件 | (d) 行 | (e) 候補供給 |
|---|---|---|---|---|---|
| C1 `CellOK cref sparkleChildCache` | `ReadWorld cache ∧ cache.ref ≠ cref.ref ∧ SetFrame cache cref` | 9126・5621（set）、9218・9220（get/modify） | W7: `sparkleChildCache` は `initialize`（1034）で確保された別 cell で、`cref`（Core 状態）とは別の ST.Ref | C.EN-4（束） | **調査範囲では未供給**。`ReadWorld`／`SetFrame` は `ST.Ref.get/set` の（extern）意味。`ref ≠` は 2 つの ref の同一性で、`initialize` された IO.Ref と `cref` の関係。足りないもの: 実 `ST.Ref` の get/set の世界遷移の意味（`@[extern] opaque`） |
| C2 `CellOK cref sparkleChildSynth` | 同形 | 5270・5293・5712（get）、9222（init） | 同上 | C.EN-4 | 同上 |
| C3 `CellOK cref sparkleSynthDepth` | 同形 | 9098・9142・9164（get/set/modify） | 同上 | C.EN-4 | 同上 |
| C4 `∀ SideRef r, CellOK cref r` | 24 個の side ref（`ChildInv.lean:69`）について同形 | 側 cache の `set {}`（9115–9140）、`sparkleCallCounter`/`sparkleWhnfCalls` 等の `modify` | 同上。24 個の ref 全てが `initialize` 済みの別 cell | C.EN-4 | 同上。**ref ごとの `≠`（24 個）は `decide` ではなく `initialize` の同一性**で、Lean の `initialize` が別の cell を割り当てることの主張 |
| C5 `∀ Fresh r, CellOK cref r`（`Fresh := MkRefd`） | `∀ σ r, MkRefd σ r → CellOK cref r`。`MkRefd σ r`（`ChildFresh.lean:44`）は `r` が**任意の** mctx・world・cref の組での `IO.mkRef` の返り値（∃ の外に world が無い） | `mkExprCache`（168）・`localMk` 等の `IO.mkRef`（translator の run-local ref） | W7 だが、命題は「**ある run で mkRef された ref すべて**」への全称で、この root の run に限定されていない。run 局所化（`MkRefd` を現在の run の履歴に限る）は文の変更で、`FramedA.localMk`・`ropsR` の `hFresh` に波及 | C.EN-4 | **調査範囲では未供給**。足りないもの: 「`mkRef` が返す cell は既存の cell と別」という実 ST の意味。run 局所化は `MkRefd` の定義変更（`ChildFresh.lean:44`）と `ChildHarness`/`ChildInvA` の再証明（見積りは調べていない） |
| C6 `ReadWorld mref` | `∀ w, getW mref w = w`（Meta 状態の get は世界を変えない） | `metaGet`（`FramedA.metaGet`）、`getEnv` 経路 | W7 | C.EN-4 | 調査範囲では未供給 |
| C7 `SetFrame mref cref` | `mref.ref ≠ cref.ref → ∀ v w, readOf cref (setW mref v w) = readOf cref w` | `metaModify`（Meta 状態の更新） | W7 | C.EN-4 | 同上 |
| C8 `mref.ref ≠ cref.ref` | 2 つの ref は別 cell | 全 Meta/Core 操作 | W7 | C.EN-4 | 同上。具体 `mref`/`cref` は `liftTermElabM` が与える（v9 は全称） |
| C9 `ReadWorld cref` | `∀ w, getW cref w = w` | `getEnv`（`readerOk_of_run` の `envAt` の同定。`hcell.2.2.2.2.2.2.2.2.1`）| W7 | C.EN-4 | 同上 |
| C10 `SetGet cref` | `∀ v w, readOf cref (setW cref v w) = v` | Core 状態の更新 | W7 | C.EN-4 | 同上 |

`hcell` 全体の注意:
- 10 conjunct（C1〜C10。C4 は 24 個、C5 は無限個の ref に対する全称）は **C.EN-4 の 1 行に束ねられている**。
- 全て `ST.Ref`（`@[extern]` の `Void IO.RealWorld` 世界上）の `get/set/modify` の意味についての前提で、`Tools/ShippingStRefCorrespondence.lean` が「PREMISE for the real runtime」と注記している。**kernel の中身が無い関数についての主張**（§16.3/§17 の `HeadIO` と同じ種類）で、`IO.getEnv`（h0）や `Lean.Meta`（`hD/hT`）とは別の層（ref の層）。
- 経路 (A) 既存定理: **なし**（`HeapModel` は抽象 heap の無矛盾性のみ）。(B) Tools 側検査: **なし**（process の cell 同一性は純関数 `Environment → Name → Bool` で検査できない。§57 と同じ）。(C) compiler 変更: 追跡 ref を使わない純粋な状態の経路にすると C1〜C5 は消えるが、これは §58 の `Rec` 全体の変更と同じ規模。小さな変更は見つかっていない。
- C9（`ReadWorld cref`）は v9 の証明が実際に最も使う成分（`readerOk_of_run`、`headAtOff_of_cellPrem`）。run から導く案（(2)）: `getEnv` を実行した直後の world が同じことは、`getEnv` を定義どおりに展開すれば `ST.Ref.get` の結果で、世界の同一性は `ReadWorld cref`（C9）そのもの。したがって C9 は run からは出ず前提のまま。

### 59.5 FG/T1 行との対応（まとめ）

| 束 | 行 | 束ねられている範囲 | 備考 |
|---|---|---|---|
| `L`（14 field ＋ `adm_closed`） | A.P-01（= T1L-01）。【S3j 訂正済】§8 の表の A.P-02 は誤りで、台帳本体でも A.P-01 | 14 field は `quiet` を共有する 1 束。`hD/hG/hT`（FG D.T-4m1/4m2/4m3）・`hs`（D.T-4m4）は `L` の field の**強化版（到達世界・環境への制限）**で別の名前の行 | field 単位の T1 行は tree に無い。`adm_closed` は行なし（FG 回路ローカル、既存定理で供給済み） |
| `hstart`（S1〜S5） | A.P-02 | `EntryWitness` の一部（A.P-04 の run、D.D-1 と同じ行）。`quiet`（S2）は A.P-01 と共有 | S1・S4 は run の Tools 側 wrapper で行から外せる見込みだが、行自体は S2・S3・S5 が残る |
| `hcell`（C1〜C10） | C.EN-4 | CellPrem 全体。`HeadIO`／`QuietStrength`／`L` の一部の吸収先（本書 §16.3、632 行目）として使われた | C.EN-4 は QuoteFact・ReadKeeps（C.RK-1）とは別の行 |

台帳本体（8649968e §12.24）が tree に無いので、上は **コードと本書の注記に現れた ID** であり、台帳の行番号との突き合わせは reviewer に残す。

### 59.6 `L`・`hstart`・`hcell` の相互依存（同時に成り立たせる必要）

- `quiet`（`L.O.quiet`）は `hstart.2`・`L` の全 field で共有。`quiet` を決めずに `hstart` だけを減らしても `quiet w` が残る。
- `L.O.frame/cacheSet/depthSet`（および `quiet` 保存）の ref 部分と `hcell`（C1〜C10）は**同じ種類の前提**（ref 間の `ReadWorld`/`SetFrame`/`SetGet`）。`CellPrem` が `L` の `frame` 族を導くには追跡 3 ref × side ref × `MkRefd` ref の間の `SetFrame`、追跡 ref の `SetGet` が足りない（§59.2）。足すと C.EN-4 の行が大きくなる。
- `hstart` の S4/S1 を Tools 側 wrapper に移す手は `hcell` の既存 field（C3 の `ReadWorld` depth、`readOf_get`）しか使わない（S4）。S1 は `read` の補題だけ。

### 59.7 `hD/hG/hT/hs/h0` との関係（再掲。新しい主張ではない）

`hD/hG/hT`（FG D.T-4m1/4m2/4m3）は `L` の field の到達世界・環境版なので、`L` の `diag`/class-D/telescope 4 行が「調査範囲では未供給」である限り、同じ理由で残る。`hs/h0`（D.T-4m4）は `SPARKLE_PROFILE` の process 環境の話で `L`/`hcell` とは別（§57/§58）。したがって **この節の供給（S1・S4）は v9 の binder 名を減らさない**（`hstart` の中身が狭まる）。

### 59.8 要約表

| 項目 | 命題（要点） | 行 | 候補供給 | 種別 | v9 から消えるもの |
|---|---|---|---|---|---|
| S1 `AdmCtx` | `canUnfold?` が inert | A.P-02 | `admCtx_none` ＋ wrapper の `canUnfold?.isNone` 検査 | (1)+(3) Tools のみ | `hstart.1`（`hstart` は S2〜S5 に狭まる）|
| S4 `dv w = 0` | 開始 depth 0 | A.P-02 | wrapper の depth 検査 ＋ `ReadWorld`（`hcell` C3）＋ `readOf_get` | (3) Tools のみ | `hstart` の `dv` 成分 |
| S5 cache 半分 | 開始 cache が実子のみ | A.P-02 | 9126 の `set {}` ＋ `L.O.cacheSet` ＋ `cacheInvA_empty`（開始世界を `w₁` へ付け替え） | (2) スケッチ（中） | `hstart` の cache 成分（`cacheSet` は `L` のまま） |
| S3 `sv` | `sparkleChildSynth = synthesizeChild` | A.P-02 | 調査範囲では未供給。(4) 9126 並びに set 1 行 ＋ `SetGet`（`hcell` 拡張）| (4)＋前提の移動 | 移るだけ（減らない見込み） |
| S2 `quiet w`／`O.quiet` | 世界の述語 | A.P-02/A.P-01 | 調査範囲では未供給（選び方の問題） | — | なし |
| `O.frameT` | throws は世界不変 | A.P-01 | (2) `Throws` の定義の各構成子を確認 | (2) スケッチ（小） | `L.O.frameT`（要確認） |
| `O.frame/frameQ/cacheSet/depthSet/*SetQ` | ref の frame・get-after-set | A.P-01 | (2) `hcell` の拡張（追跡 ref の `SetGet`、ref 間 `SetFrame`）から | (2) 前提の移動 | 移るだけ（`L` の ref 部分 → `hcell`。総数は減らない） |
| `O.diag`/`excOk`、`T.*`（4）| IO extern・例外クラス・Meta telescope | A.P-01 | 調査範囲では未供給 | — | なし |
| `adm_closed` | `CtxClosed (AdmCtx quiet)` | no row | `admCtx_closed`（供給済み） | (1) | 既に外れている |
| C1〜C10 `hcell` | `ST.Ref` の `ReadWorld`/`SetFrame`/`SetGet`/`≠` | C.EN-4 | 調査範囲では未供給（`HeapModel` は無矛盾性のみ） | — | なし |

### 59.9 次の単位の推奨順（最小の供給から。各々が v9 から何を消すか）

1. **S3j（Tools のみ、小）: wrapper 入口の開始検査で `hstart` の S1・S4 を外す。** `pilotEntry2` を `canUnfold?.isNone`・`sparkleSynthDepth.get == 0` を検査してから `synthesizeCombinationalOffR pilotReaderOk2` を呼ぶ wrapper `pilotEntry3` にし、v10 の `hr` を `RunsTo (pilotEntry3 hftRoot) …` とする（`RunsTo.bind` で分解。新規の補題は `read` と `get` の RunsTo の 2 つ）。消えるもの: `hstart.1`（`AdmCtx`）、`hstart` の `dv w = 0`。残る: S2・S3・S5。**binder 名は変わらない**（`hstart` が狭まる）ので、A.P-02 の行は減らない（数えない）。出力・compiler は不変（wrapper は pilot の入口のみ。`#synthesizeVerilogPilot2` の出力比較は Check48 OUTPUT の形で再確認）。注意: `RunsTo` の読み取りが `ReadWorld` を要する点（hcell の既存 field で足りる）、`inlinerFuelGuard` の位置は wrapper の外のまま。
2. **S3k（Tools のみ、小〜中）: `O.frameT` の確認と、`Throws` の各構成子が世界を変えないことの定理化。** 成功すれば `L.O.frameT` が既存定理から出る（要確認。失敗なら理由を記録）。減るもの: `L` の 1 field（binder 名は `L` のまま、`L` が狭まる）。
3. **S3l（Tools のみ、中）: `hstart` の S5（cache 半分）の run からの導出。** 開始世界を 9126 の `set {}` の後へ付け替える再構成（`offR_to_off`、`start`/`missRX` の接続）。減るもの: `hstart` の cache 成分。`L.O.cacheSet` を使うので `L` は減らない。
4. **S3m（`hcell` の拡張設計、docs＋小さな Tools）: `L` の ref 部分（`frame/cacheSet/depthSet/*Q`）を `hcell` の拡張（追跡 ref の `SetGet`、ref 間 `SetFrame`）に移す。** 減るもの: `L` の ref 部分の field。増えるもの: `hcell` の field（C.EN-4 の行が大きくなる）。総数が減らないので、reviewer の判断（行の数え方）が先。
5. **S3n 以降（小さくない。reviewer 判断待ち）**: `h0/hs`（§58.4 の 1/2/3）、`hG`（§57.3 案 B）、`hD/hT/diag/excOk/telescope`（`Lean.Meta` の意味、または Off 経路を純粋な状態にする書き換え。戦略 §5 の「当面選ばない」）、`hcell` C1〜C10 と `hstart` S3（実 `ST.Ref`／`initialize` の意味。run 局所化や `mkRef` の意味）。いずれも「調査範囲では未供給」。

全体の見立て（断定ではない）: 1〜3 は Tools 側で行える見込みだが、**v9 の 9 binder の名前は 1 つも減らない**（`hstart`・`L` が狭まるだけ）。binder を実際に減らすのは 5 の項目で、それらはどれも `Lean.Meta`/`IO`/`ST.Ref` の実装の意味か compiler の大きな変更に依る。この pilot の前提を閉じる方針（reviewer）に対して、**残義務は `L`・`hcell`（実 `ST.Ref` の意味）と `hD/hG/hT/hs/h0`（Lean 実装の意味）の 2 群に集約され、`hstart` の一部だけが run から導ける**、というのがこの棚卸しの結果である。

### 59.10 範囲・台帳
- 読んだもの: `Tools/ShippingFGCircuitS3f2Final.lean`、`Tools/ShippingGen2Defs.lean`、`ShippingChildInvA.lean`、`ShippingFGCircuitS2sAdmChildInvA.lean`/`AdmLawsX.lean`、`ShippingChildCacheA.lean`、`ShippingChildVCA.lean`、`ShippingChildFresh.lean`、`ShippingGen5EnvFrame3.lean`、`ShippingStRefCorrespondence.lean`、`ShippingHeapModel.lean`（冒頭と `HeapLaws`）、`ShippingGenFGLedgerPremises.lean`、`Sparkle/Compiler/Elab.lean` の該当行、本書 §8・§44 周辺・§52–§58、`docs/FG-CIRCUIT-STRATEGY-2026-11-06.md`。台帳本体 8649968e §12.24 は tree に無い。
- 確認していない: `Throws`/`Op` の各構成子の定義（`ChildInv.lean:281–`）、`admCtx_closed` の厳密な位置、`liftTermElabM` の既定 `canUnfold?` と stderr の隔離（`withIsolatedStreams` 等）、field 消費箇所の網羅（上の「消費する証明段」は `grep` の上位ファイルで、全 call site ではない）。
- 変更: この docs のみ。`Sparkle/`・`Tools/`・`Tests/` は不変。v9・Check48 は不変。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 60. S3j（Issue `sparkle-fg-circuit-pilot`）: §59 の供給候補のうち小さな Lean 補題にできたもの — 検査付き入口 `pilotEntry3`、v10（`hstart` を未供給の 3 成分に狭めた版）、Check50

土台 `061b2e88`（= par/fgc-s1 `aa9bff12` + §59）。**変更したもの**: `Tools/ShippingFGCircuitS3jStart.lean`・`…S3jFinal.lean`・`…S3jThrows.lean`・`Tests/Gen5/FGCircuitPilotCheck50.lean`（新規。`lakefile.lean` に `lean_lib` 4 件）と docs（§8・§57.3・§58.5・§59 の訂正、本節）。`Sparkle/`（compiler）・v9（`Tools/ShippingFGCircuitS3f2Final.lean`）・既存 Check・既存の定義は**不変**。新 law・axiom・sorry・native_decide・TRUSTED なし。コミット（古い順）: `49035530` pilotEntry3 と run 補題、`edc57d16` v10、`07e31173` jqc_after_head、`0bda40ba` frameT と拒否補題、`f8a11506` pilotArtifact3 と空虚 L の補題、`03c04d2d` Check50、続く 1 件（Check50 の補助補題の署名と docs 訂正）、本節。

### 60.0 結果の要約（供給したもの／していないもの）

| 項目 | 結果 | 種別 |
|---|---|---|
| S1 `AdmCtx`（`hstart.1`） | **供給した**（`admCtx_of_pilotEntry3`）。run の `canUnfold?.isNone` 検査 + 既存 `admCtx_none` | 既存定理 + Tools 側検査（MetaM wrapper） |
| S4 `dv w = 0` | **供給した**（`dv_of_pilotEntry3`）。run の depth 読み取りの検査。**開始 world `w` のまま**（文の開始 world は動かしていない） | Tools 側検査 + `ReadWorld`（`hcell` の既存 field） |
| S5 cache 半分 | **補題として供給した**（`jqc_after_head`・`jqc_after_head_of_pilotEntry3`: core head の後の world `w1` で `JQC L.O 1 w1`、cache 半分を含む）。**ただし v10 の文からは外せていない**: `hcache` が残る（§60.3） | 既存定理 `coreHeadOff_jqcA`（`L.O.cacheSet` を使う）の組み立て。**`L` の field に依る** |
| S2 `quiet w`、S3 `sv w = some synthesizeChild` | 未供給（v10 の `hquiet`・`hsynth`） | 調査範囲では未供給（§59.3 のまま） |
| `L.O.frameT` | **field の命題を補題にした**（`frameT_of_readWorld`）。`ReadWorld mref` と `ReadWorld cref`（`hcell` の 2 field）だけから。**`L` は binder のまま**（他の 13 field は不変。field の補題は構造体を作らない） | 定義から計算（`rfl` 2 本）+ `ReadWorld` |
| v10 | **作った**（11 引数: `L hquiet hsynth hcache hr hcell hD hG hT hs h0`）。`hstart` の 5 conjunct のうち 2 つが消えた | v9 の合成 |
| `L` 全体、`hcell`、`hD hG hT hs h0` | **不変・未供給**（調査範囲では） | — |

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。**A.P-02（Start）は行を外していない**: `quiet`・`sv`・cache 半分が残る。A.P-01（`L`）・C.EN-4（`hcell`）も行は同じ（`frameT` の補題は `L` の 14 field のうち 1 つの命題の供給で、`L` は binder のまま）。行の数え方は reviewer が決める。

### 60.1 `mctx` はどこから来るか — 検査は「その run の」`mctx` を見ている

- 実行経路: `elab "#synthesizeVerilogPilot3"`（`Tools/ShippingFGCircuitS3jFinal.lean`、`#synthesizeVerilogPilot2` と同形）→ `liftCoreM (resolveGlobalConstNoOverload id)` → `Lean.Elab.Command.liftTermElabM (do inlinerFuelGuard declName; pilotArtifact3 declName)` → `pilotEntry3`。Lean の `liftTermElabM` は term action を `… |>.run mkMetaContext {}` で走らせるので、入口の Meta context は `Command.mkMetaContext`（その上で `x` 自身の更新）。これは `Tools/ShippingStartWorldA.lean` の冒頭が記録している **Lean ソースの読み**で、定理ではない。そこで証明済みなのは `mkMetaContext.canUnfold? = none`（`mkMetaContext_canUnfold := rfl`）だけ。
- **`Environment → Name → Bool` の検査（`readerOk`・`pilotReaderOk2`）は `Meta.Context` を見られない**（引数が環境と名前だけの純関数）。したがって `mctx` の検査は `readerOk` には入れられず、MetaM の wrapper に置く。これが `pilotEntry3`（`Tools/ShippingFGCircuitS3jStart.lean:22`）:
  ```
  def pilotEntry3 (declName : Name) : MetaM (Module × Design) := do
    let ctx ← readThe Meta.Context
    unless ctx.canUnfold?.isNone do throwError "…"
    let depth ← sparkleSynthDepth.get
    unless depth == 0 do throwError "…"
    synthesizeCombinationalOffR pilotReaderOk2 declName
  ```
- **「同じ `mctx`」であることの根拠**: `RunsTo (m >>= f) mctx … ` は `m` も `f a` も同じ `mctx` で走る（`RunsTo.bind`）ので、`readThe Meta.Context` の返り値は `RunsTo` の引数 `mctx` そのもの（`runsTo_readThe`・`runsTo_readThe_bind`）で、その後の `synthesizeCombinationalOffR` の run も同じ `mctx`。`pilotEntry3_run` はこれを `mctx.canUnfold? = none` として出す。つまり v10 の `mctx`（結論の `PostRunOff mctx …` と共通）が検査された文脈である。
- 残る限界: (a) `liftTermElabM` が `mkMetaContext` から始まるという読みは定理ではない（run_cmd の文脈では Check50 が `canUnfold?.isNone` を実行して確認した）。(b) `AdmCtx` は `Core.Context` に何も要求しない（`ChildInvA.lean` の注記どおり）ので検査していない。(c) 検査は `canUnfold? = none` で、`some f` の文脈を `InertUnfold` で受ける形ではない（その文脈は拒否される: `pilotEntry3_refuses_canUnfold`）。
- §59.10 の「確認していない」のうち、`liftTermElabM` の既定 `canUnfold?` は上のとおり（ソースの読み + run_cmd での実行確認）。stderr の隔離は今回も確認していない。

### 60.2 `dv w = 0` — どの world か

- `pilotEntry3` は depth を**開始 world `w` で読む**（`sparkleSynthDepth.get`）。`runsTo_get` は返り値 `= readOf r w`・終了 world `= getW r w` を出す。`dv w`（`Tools/ShippingChildBndCore.lean:47`）は定義が `readOf sparkleSynthDepth w` なので、`dv_of_pilotEntry3 : … → dv w = 0` は `pilotEntry3_run` の第 2 成分そのもの。
- 内側の `synthesizeCombinationalOffR pilotReaderOk2` が走り出す world は `getW sparkleSynthDepth w`。**`ReadWorld sparkleSynthDepth`**（`hcell` の C3 の第 1 成分、`hcell.2.2.1.1`）で `= w` となる（`entry2_of_pilotEntry3`）。よって **文の開始 world を動かさない**: v10 の `w` は wrapper の開始 world で、`PostRunOff mctx mref cctx cref w …`・`envAt cref w`・`hD hG hT hs h0` は v9 と同じ `w`。core head の後の world（depth 1）は別物で、`jqc_after_head` が扱う。
- `hcell` は v9 にも在ったので新しい前提ではないが、v10 の証明は C3 の `ReadWorld` を**新たに使う**。

### 60.3 cache 半分 — 補題はできたが、文からは外せていない（正確な欠け）

- できたこと: `jqc_after_head`（`S3jStart.lean:118`）。`AdmCtx`・`quiet w`・`sv w`・`dv w = 0` と core head の run `coreHeadOff X` から、head 後の world `w1` で `JQC L.O 1 w1`、すなわち `CacheInvA L.O (cv w1)` を含む。中身は既存 `coreHeadOff_jqcA`（`D = 0`、`Or.inl rfl`: depth 0 では cache の前提を消費しない）。cache の段は `coreHeadOff` の `sparkleChildCache.set {}`（depth 0 の分岐）と **`L.O.cacheSet`**（`tripleC_clear` 経由）。**これは `L` の field を使う**ので、Start のこの部分は「無から」ではなく `L` から供給される（`L` は binder のまま）。`jqc_after_head_of_pilotEntry3` は run から head の run を取り出し（`coreR_chain`）同じ結論を出す。**開始 world の cache（`cv w`）は一切仮定していない**。
- 実行での観測（Check50 OUTPUT、**1 回の観測に限る**）: 開始 cache を非空（`hftHttp` の artifact を入れた）にして `pilotEntry3` を走らせても artifact は同一だった。**これは `CacheInvA` が不要という一般の証明ではない**（非空の cache も `CacheInvA` を満たし得る）。cache 半分を除く一般の根拠は `jqc_after_head` と S3k の最終接続（§61）である。〔S3l で表現を限定〕
- **文から外せていない理由（欠けている文）**: v9 の証明の連鎖は `Start`（`StartX`）を **開始 world `w`** で消費する。連鎖の各定理は `hstart : StartX L mctx cctx w`（または `Start`）を引数に取る: `synth_hftPcieOutByte_finalOffLNLX`（`S2sAdmS1zClose.lean:222`、文は `HftFinalStmtOffLNLX`:203）、`coreOff_ranAX`/`hftPostGate_of_localX` ほか `S2sAdmS1zClose.lean` の 4 件（128・171・186・207 行）、`S2sAdmS2dKids.lean`（272・303）、`S2sAdmS2hHist3.lean`（184・215）、`S2sAdmS2mReach3.lean`（185）、`S2sAdmS1uSrc.lean`（104）、`S2sAdmS1tFinal.lean`（89）、`S2sAdmS2nAdm.lean`（96。`hftCoreCloses_of_kidsR''`）、`S3cTop.lean`（128。`hftTop_of_runRX`）、`S3cFinal.lean`（`hstartX := ⟨hstart.1, jqc_toX hstart.2⟩`）。**grep で読んだ範囲の直接の使用は `hstart.1`（adm）と `hstart.2.1`（`JQX` 部分）だけで、`hstart.2.2`（cache 半分）は使われていない**（`coreHeadOff_jqcAX … hstart.1 hstart.2.1 (Or.inl rfl) hh` の形）。ただしこれらは `hstart` を下位の定理へ丸ごと渡すので、**下位まで `.2.2` が使われないことは確かめていない**。
- 欠けている文（正確に）: `HftFinalStmtOffLNLX Ob CV`（`S2sAdmS1zClose.lean:203`）の `hstart : StartX L mctx cctx w` を 2 つの引数 `hadm : L.O.adm mctx cctx` と `hjq : JQ L.O.quiet 0 w`（cache 半分なし）に替えた文 `HftFinalStmtOffLNLX'` と、その証明の連鎖（上の ~12 宣言の `StartX` を `adm ∧ JQ` に替えた複製）。これが通れば v10 から `hcache` を外せる（head の後の `JQC 1` は `jqc_after_head` が与える）。**既存の文を変えると旧 Check（型を独立に照合している）が壊れるので、複製として別ファイルに作る必要がある**。見積りは出していない（連鎖の宣言数は ~12、各々は既存の証明の `hstart.2.1` の取り出し直し）。**次の単位の候補**。
- したがって v10 は `hcache : CacheInvA L.O (cv w)` を名前付きの未供給仮説として残している。「`Start` の cache 半分が供給できた」とは数えない。

### 60.4 `L.O.frameT`（任意項目）— 各 `Throws` 構成子は世界を変えない

- `Throws`（`Tools/ShippingChildInv.lean:281`）の構成子は 2 つ: `err msg : throwError msg`（MetaM）と `coreErr msg : liftM (throwError msg : CoreM α)`。Lean 4.32.1 の `throwError` は `getRef`（Core context の読み出し）、`addMessageContext`（`getEnv`＝Core 状態 ref の `get`、`getMCtx`＝Meta 状態 ref の `get`、`lctx`・`opts` は context の読み出し）、`throw` の順。`S3jThrows.lean` の `throwError_run`・`coreThrowError_run` は、この run が「Core 状態の `get`（と、MetaM 版では Meta 状態の `get`）の後に `error` を返す」ことを `rfl` で示す。
- `endW_throws`: `ReadWorld mref` と `ReadWorld cref`（`hcell.2.2.2.2.2.1`、`hcell.2.2.2.2.2.2.2.2.1`）の下で `endW … p w = w`（`Throws p`）。`frameT_of_readWorld` はこれから field `RefLawsAOps.frameT` の命題（`AdmCtx` の仮定は使わない）を、**任意の `quiet`** について出す。
- **`L` は binder のまま**: この補題は field の命題を `hcell` の 2 field に帰着させるもので、`L` の構造体は作らない。他の 13 field・`T` の 4 field は未供給。`L` を作るなら `frameT` は追加の仮定を要さない、という記録（frameT は `L` の中の独立な仮定ではなく `hcell` の C6・C9 に既に含まれている）。`hcell` は `ST.Ref` の意味の前提（§59.4）のまま。

### 60.5 v10 — 文と binder（v9 との field 単位の比較）

`HftFinalStmtOffCombined10`（`Tools/ShippingFGCircuitS3jFinal.lean:76`、定理 `synth_hftPcieOutByte_finalOffCombined10`:92。証明は `start_of_residual` + `entry2_of_pilotEntry3` + v9）:

```
∀ {ι} {mref} {cref} (L : Laws mref cref) {mctx cctx w w' b D'}
  (hquiet : L.O.quiet w) (hsynth : sv w = some synthesizeChild) (hcache : CacheInvA L.O (cv w))
  (hr : RunsTo (pilotEntry3 hftRoot) mctx mref cctx cref w (b, D') w')
  (hcell : CellPrem MkRefd mref cref) (hD …) (hG …) (hT …) (hs …) (h0 …), <v9 と同じ結論>
```

| binder | v9 | v10 |
|---|---|---|
| `hstart` | `Start L mctx cctx w` = `AdmCtx L.O.quiet mctx cctx` ∧ `quiet w` ∧ `sv w = some synthesizeChild` ∧ `dv w = 0` ∧ `CacheInvA L.O (cv w)` | **なし**。5 conjunct のうち `AdmCtx` と `dv w = 0` は `hr`（wrapper の run）の検査から出る |
| `hquiet` / `hsynth` / `hcache` | — | 残った 3 conjunct（それぞれ独立の名前付き仮説。隠した束ではない） |
| `hr` | `synthesizeCombinationalOffR pilotReaderOk2 hftRoot` の run | `pilotEntry3 hftRoot` の run（同じ run に 2 つの検査が付く。成功 run の集合は狭まる） |
| `L`・`hcell`・`hD hG hT hs h0` | — | **不変**（型は v9 と同一） |

`Start` の 5 conjunct を v10 自身の変数で展開して照合した結果（Check50 BINDERS）: v10 の仮説に残る = `quiet w`・`sv w = some synthesizeChild`・`CacheInvA (cv w)`、消えた（run の検査が供給）= `AdmCtx`・`dv w = 0`。

**空虚な `L`（`quiet := False`）は充足例に数えない**: `vacuousLaws`（`RefLawsAOps.quietFalse`・`RefLawsATele.quietFalse` で作る）では `hquiet` が全 world で偽（`vacuous_no_hquiet`）、`Start` も偽（`vacuous_no_start`）。〔S3l 訂正〕`vacuousLaws` の docstring の「残差の前提のどれも満たさない」は、**`hquiet` が偽なので前件全体が充足不能**という意味である（`hsynth`・`hcache` が個別に偽であることは示していない）。

一方 **検査が供給する `AdmCtx` は `quiet := False` でも真**（`vacuous_adm_trivial`＝`admCtx_quietFalse`）なので、検査は `quiet` について何も言わず、`hquiet` を別の仮説に残している。v10 の証明項は（推移的に 25340 個の定数を辿って）`vacuousLaws`・`quietFalse`・`admCtx_quietFalse(_writer)`・`frame_quietFalse_vacuous` のどれも使っていない（Check50 VACUITY）。つまり v10 は `hquiet` を満たす `L` についての主張で、空虚な `L` に依っていない。

### 60.6 Check50（`Tests/Gen5/FGCircuitPilotCheck50.lean`）の行（Check 自身の出力から）

- `FGCIRCUIT50 SIGNATURES`: v10 の完全な型 = 独立に書いた `Exp10`（`FGCircuitCmp.stmtEq`、`norm50` 1 本）、**52 mutants 却下**（各前提の削除、入口 = 検査なし／`canUnfold?` のみ／depth のみ／通常 Off／検査の向きを逆、別の Meta context、別の開始 world、残差 3 前提を別 world・終了 world・別の形（全 world quiet、`sv = none`、**空 cache**）に、検査が出す conjunct や `Start` 全体を仮説に戻す、結論の環境・tele・level・出力・artifact・carrier、v9／v8／v7 の型）。新補題 17 件の完全な型 = 独立に書いた期待型、**54 mutants 却下**。
- `FGCIRCUIT50 BINDERS`: v9（18 = 9 + 9）`[ι, mref, cref, L, mctx, cctx, w, w', b, D', hstart, hr, hcell, hD, hG, hT, hs, h0]`; v10（20 = 9 + 11）`[ι, mref, cref, L, mctx, cctx, w, w', b, D', hquiet, hsynth, hcache, hr, hcell, hD, hG, hT, hs, h0]`; Start の 5 conjunct のうち残る `[quiet w, sv w = some synthesizeChild, CacheInvA (cv w)]`、消えた `[AdmCtx, dv w = 0]`。
- `FGCIRCUIT50 VACUITY`: 上のとおり（25340 定数、空虚な証人への依存なし）。
- `FGCIRCUIT50 OUTPUT`: S3j の入口 = S3f2 の入口 = 通常 Off の入口の module+design repr が同一（77654 / 89425 文字）。run 自身の Module から出した Verilog も同一（11345 文字）。制御: 別宣言の artifact／改変した Module は不一致、実際の `run_cmd` の文脈は `canUnfold?` が none・depth 0、**`canUnfold?` の callback を入れた文脈では S3j の入口は明示エラーを返し（S3f2 の入口は走る）**、depth 1 でも明示エラー（**wrapper 自身は depth を書かず 1 のまま**であることを、テストの `set savedDepth` が戻す前に確認する。戻しているのは wrapper ではなくテスト側）、**非空の開始 cache の 1 実行でも artifact は不変**（1 回の観測であり、cache 半分の除去の根拠ではない。§60.3・§61）。
- `FGCIRCUIT50 AXIOMS`: 20 名、標準の公理のみ（`propext`・`Classical.choice`・`Quot.sound`）。sorryAx・native_decide なし。
- 「別の開始 world」は、world が抽象（`Void IO.RealWorld`）なので実行での対照は作れず、文の型の mutant（`F10Mu_runWorld`、`quietOther`/`synthOther`/`cacheOther` ほか）で却下した。「別の `mctx`」は実行（callback 入りの文脈で拒否）と型（`F10Mu_runCtx`、`pilotEntry3_refuses_canUnfold`）の両方。「depth ≠ 0」は実行（depth 1 で拒否）と型（`pilotEntry3_refuses_depth`）の両方。

### 60.7 何が供給され、何が残ったか（まとめ）

- 供給した: `AdmCtx`（`hstart.1`）、`dv w = 0`、（補題として）core head 後の cache 半分、`frameT` の命題。
- 残った（名前付き）: `hquiet`・`hsynth`・`hcache`（`Start` の残り。A.P-02）、`L`（A.P-01）、`hcell`（C.EN-4）、`hD hG hT hs h0`。いずれも「調査範囲では未供給」で、供給不能の主張ではない。
- v10 の `hr` は wrapper の run なので、v10 が語るのは「2 つの検査を通った run」だけ。実コマンドの経路（`#synthesizeVerilogPilot3`）はその run を作る。既存のコマンド `#synthesizeVerilog`・`#synthesizeVerilogPilot`・`#synthesizeVerilogPilot2` は不変で、v10 の対象外。

### 60.8 範囲・compiler 変更・次

- compiler（`Sparkle/`）の変更: **なし**。小さな compiler 変更が必要と判断した項目もない（S3 `sv`（§59.3 の案）は今回触れていない）。
- 次の候補（小さい順）: (1) §60.3 の `HftFinalStmtOffLNLX'` 連鎖（`hcache` を外す。Tools のみ、複製）。(2) `hsynth`（S3）は `sparkleChildSynth` の `SetGet` を `hcell` に足す設計が要る（§59.3、reviewer 判断）。(3) `hquiet`（`quiet` の具体的な選択）は未着手。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 61. S3k（Issue `sparkle-fg-circuit-pilot`）: `hcache` を v10 から外す — 開始 world の `Start` を消費する宣言の監査（§61.1）、複製した鎖、v11、Check51

土台 `fb8b6d8e`（S3j）。

### 61.1 監査: v10 の証明経路で開始 world の `Start` / `StartX` を消費する宣言

方法: v10 の定理 `synth_hftPcieOutByte_finalOffCombined10` から定数の推移閉包（24871 件）を取り、(a) 型が `Start`・`StartX`・`JQC`・`JQCX`（またはそれらを値に持つ文の定義）を直接含む宣言を列挙し、(b) 開始 world に対する `Start` を引数に取るものについて証明本体の `hstart` の使用を全て読んだ。定義: `Start L mctx cctx w = AdmCtx L.O.quiet mctx cctx ∧ JQC L.O 0 w`、`JQC O D w = JQ O.quiet D w ∧ CacheInvA O (cv w)`、`JQ quiet D w = quiet w ∧ sv w = some synthesizeChild ∧ dv w = D`。`StartX` は `L.O.adm mctx cctx ∧ JQCX L.O 0 w`（`JQCX = JQ ∧ CacheInvAX (cv w)`）。したがって `hstart.1` = AdmCtx（X では adm）、`hstart.2.1` = JQ（quiet・sv・dv）、`hstart.2.2` = **cache 不変量**。

| # | 宣言（ファイル） | 使う連言 | cache `.2.2` |
|---|---|---|---|
| 1 | `synth_hftPcieOutByte_finalOffCombined9`（S3f2Final）| `hstart` を v7 へ丸ごと渡す | 渡すだけ |
| 2 | `synth_hftPcieOutByte_finalOffCombined7`（S3cFinal）| `hstart.1`、`hstart.2`（全体）→ `hstartX := ⟨hstart.1, jqc_toX hstart.2⟩`、`hftTop_of_runRX` へ `hstart` | **`jqc_toX hstart.2` で StartX の cache 半分を作る**（作るだけ。下流で読まれない: 3–10）|
| 3 | `hftTop_of_runRX`（S3cTop:128）| `hstart.1`（adm、4 箇所）、`hstart.2.1.2.2`（dv = 0）、`hstart.2.1.1`（quiet）、`hstart.2.1.2`（sv ∧ dv）| 使わない |
| 4 | `hftCoreCloses_of_kidsR''`（S2nAdm:96）| `hstart.1`、`hstart` を 5 へ | 使わない |
| 5 | `hftCoreCloses_of_kidsRX`（S2mReach3:185）| `hstart.2.1`（`jqhr_headX` の `hjq : JQ`）のみ。`hadm` は別引数 | 使わない |
| 6 | `synth_hftPcieOutByte_finalOffLNLX`（S1zClose:222）| `hstart` を 7・8・9 へ | 渡すだけ |
| 7 | `hftObNoRawOff_of_localX`（S1zClose:186）| `hstart` を 8・9 へ | 渡すだけ |
| 8 | `hftPostGate_of_localX`（S1zClose:171）| `hstart` を 9 へ | 渡すだけ |
| 9 | `coreOff_ranAX`（S1zClose:128）| `hstart.1`（adm、5 箇所）、`hstart.2.1`（`coreHeadOff_jqcAX … (Or.inl rfl)` の `hw : JQ`）| 使わない（`D = 0 ∨ CacheInvAX …` は `Or.inl rfl`）|
| 10 | `synth_hftPcieOutByte_finalOffLX`（S1uSrc:122）| `hstart` を 11 へ | 渡すだけ |
| 11 | `synth_hftPcieOutByte_finalOffX`（S1tFinal:109）| **`hstart` を本体で一度も使わない**（introduce されるのみ）| 使わない |

下位の補題（S3j が確かめていなかった範囲）: 3・5・9 が `hstart` の一部として渡す先は `coreHeadOff_jqcAX`（`hw : JQ O.quiet D w`、`hc : D = 0 ∨ CacheInvAX`）、`jqhr_headX`（`hadm`、`hjq : JQ O.quiet 0 w₀`）、`machineRunJQH_of_closesHOffX`（`hA : O.adm`）、`keepsA_framedX`（`hA`）、`synthesizeFromConst_machine_invWX`・`synthesizeMachineCertified_runsAX`・`htr_of_teleX`・`bodyStepC_of_teleX`・`soundX_served_EX`・`oneOut_topShipsOff`・`hft_closesAtHX`（いずれも `hstart.1` の adm のみ）。**どれも `Start`/`StartX`/`JQC`/`JQCX` を開始 world で取らない**（型を読んだ。`JQ` と adm だけ）。

結論: **開始 world の cache 不変量 `CacheInvA L.O (cv w)` は、v10 の証明経路のどこでも読まれない**。唯一の「使用」は #2 の `jqc_toX hstart.2`（`Start` を `StartX` の形にするための再包装）で、その `StartX` の cache 半分は #6–#11 が `.2.1` と `.1` だけを取り出すため消費されない。head の後の `JQC 1` は `coreHeadOff_jqcAX` が `Or.inl rfl` で与える（開始 cache 不要）。よって手順 2（複製）に進む。複製するのは、型に `hstart : Start/StartX` を持つ宣言 #1–#11 のみ（文を変える必要があるもの）で、`hadm` と JQ のみの `hjq : JQ L.O.quiet 0 w` に替える。下位補題は再利用する。

### 61.2 複製した鎖（`Tools/ShippingFGCircuitS3kChain.lean`、`lakefile.lean` に `lean_lib`）

§61.1 の #1–#11 を、`hstart` を `hadm`（文脈述語。`Laws` 版は `AdmCtx L.O.quiet mctx cctx`、`LawsX` 版は `L.O.adm mctx cctx`）と JQ のみの `hjq : JQ L.O.quiet 0 w` に替えて複製した（接尾辞 `_k`、各々の元の namespace を開き直した。選択的移植）。置換は機械的: `hstart.1 ↦ hadm`、`hstart.2.1 ↦ hjq`（`hstart.2.1.1/.2/.2.2 ↦ hjq.1/.2/.2.2`）、`hstart` を渡す所は `hadm hjq`。証明の他の部分は元と同じ。手で直したのは 3 点だけ: (1) `hftCoreCloses_of_kidsRX_k` は元から別引数 `hadm` を持つので `hjq` のみ、(2) v7 の `hstartX := ⟨hstart.1, jqc_toX hstart.2⟩`（cache 半分を作っていた唯一の箇所）を削除し `hadm hjq` を直接渡す、(3) `JQ` の open。複製は `HftFinalStmtOffLNLX_k`、`HftFinalStmtOffCombined7_k`、`HftFinalStmtOffCombined9_k`（文の定義）と、定理 `synth_hftPcieOutByte_finalOffX_k`、`…LX_k`、`…LNLX_k`、`coreOff_ranAX_k`、`hftPostGate_of_localX_k`、`hftObNoRawOff_of_localX_k`、`hftCoreCloses_of_kidsRX_k`、`hftCoreCloses_of_kidsR''_k`、`hftTop_of_runRX_k`、`…Combined7_k`、`…Combined9_k`。原本・既存 Check・下位補題は不変。初回のビルドで通った（`L.toX` の defeq も含めて）。

### 61.3 v11（`Tools/ShippingFGCircuitS3kFinal.lean`）

`HftFinalStmtOffCombined11`（定理 `synth_hftPcieOutByte_finalOffCombined11`）: v10 から `hcache` を除いた文。binder は `L hquiet hsynth hr hcell hD hG hT hs h0`（10 個）。結論・`hr`（`pilotEntry3` の run）・他の前提は v10 と同じ。証明は `jq_of_residual`（`AdmCtx` は run の `canUnfold?` 検査、`quiet w` は `hquiet`、`sv w` は `hsynth`、`dv w = 0` は run の depth 検査 → `AdmCtx ∧ JQ L.O.quiet 0 w`）+ `entry2_of_pilotEntry3` + 複製 v9。`v11_post_head_jqc` は v11 の前提そのもの（`hquiet hsynth hr hcell`）から core head 後の world で `JQC L.O 1`（cache 半分を含む）を `jqc_after_head_of_pilotEntry3` で出す: 開始 world の cache を仮定しない。公理は標準のみ（`#print axioms`）。

### 61.4 Check51（`Tests/Gen5/FGCircuitPilotCheck51.lean`）の行（Check 自身の出力から）

- `FGCIRCUIT51 SIGNATURES`: v11 の完全な型 = 独立に書いた `F11_real`（Check50 の `F10` 族で cache 前提を省いたもの）、`FGCircuitCmp.stmtEq`、`norm51` 1 本、**54 mutants 却下**（`hcache` を開始 world／別 world／空 cache／終了 world で戻す、各前提の削除、S3f2／通常 Off／検査の半分／depth 1 の入口、別の run 文脈・開始 world、`Start` の連言や `Start` 全体を仮説に、結論の環境・tele・level・出力・artifact・carrier、v10／v9／複製 v9／v8／v7 の型）。複製した鎖の主要補題 10 件（`…Combined9_k`、`…Combined7_k`、`…LNLX_k`、`coreOff_ranAX_k`、`hftObNoRawOff_of_localX_k`、`hftCoreCloses_of_kidsR''_k`、`hftTop_of_runRX_k`、`hftCoreCloses_of_kidsRX_k`、`jq_of_residual`、`v11_post_head_jqc`）の完全な型 = 独立に書いた期待型（元の文に start 仮説のノブだけを持たせたもの。v9 のノブ 3 = **元の v9 の型**と一致することも確認）、**65 mutants 却下**（`hadm` なし、`hjq` なし、元の `Start`/`StartX`、cache を `JQC`/`JQCX` として `hjq` の中に戻す、`hjq` を終了 world・depth 1 に、`hjq` に加えて別の cache 仮説、`jq_of_residual` の結論に dv を欠く、など）。
- `FGCIRCUIT51 BINDERS`: v9（18 = 9 + 9）、v10（20 = 9 + 11）`[ι, mref, cref, L, mctx, cctx, w, w', b, D', hquiet, hsynth, hcache, hr, hcell, hD, hG, hT, hs, h0]`、v11（19 = 9 + 10）`[ι, mref, cref, L, mctx, cctx, w, w', b, D', hquiet, hsynth, hr, hcell, hD, hG, hT, hs, h0]`。**v11 = v10 − [hcache]**。`Start` の 5 連言を v11 自身の変数で照合: v11 の仮説 `[quiet w, sv w = some synthesizeChild]`、run の検査が供給 `AdmCtx`・`dv w = 0`、**もう前提でない** `CacheInvA (cv w)`。
- `FGCIRCUIT51 VACUITY`: v11 の証明項（25335 定数）は `vacuousLaws`・`RefLawsAOps.quietFalse`・`RefLawsATele.quietFalse`・`admCtx_quietFalse(_writer)`・`frame_quietFalse_vacuous` のどれにも到達しない。同じ走査は元の鎖（v9・v7・`hftTop_of_runRX`・kids の closing・LNLX・`coreOff_ranAX`・`hftPostGate/hftObNoRaw`・LX・X・`jqc_toX`・`start_of_residual`・v10 の 14 宣言）にも到達しない（証明は複製だけを通る。`INDEPENDENCE`）。空虚な `L` が充足例でないことは S3j の `vacuous_no_hquiet`（`hquiet` は全 world で偽）による: v11 は `hquiet` を満たす `L` についての主張。
- `FGCIRCUIT51 AXIOMS`: 14 名、標準の公理のみ。sorryAx・native_decide なし。

### 61.5 何が供給され、何が残ったか

- 今回不要化した（文から消えた）: `CacheInvA L.O (cv w)`（開始 world の cache 条件、`hcache`）。開始 world の cache 条件を証明したのではなく、それを必要としない定理に変えた。head 後の `JQC 1` は `L.O.cacheSet`（`tripleC_clear`）で head 後に確立する（`L` の field に依る。`L` は binder のまま）。（reviewer 指摘による訂正: 旧記述「今回供給した」）
- 残った（名前付き・不変）: `hquiet`・`hsynth`（`Start` の JQ 部分。A.P-02）、`L`（A.P-01）、`hcell`（C.EN-4）、`hD hG hT hs h0`。いずれも「調査範囲では未供給」で、供給不能の主張ではない。
- v11 の `hr` は v10 と同じ wrapper の run（`pilotEntry3`）。実行経路・出力は v10 と同じ（compiler `Sparkle/` は不変）。
- 制約: 複製した鎖は元の証明の機械的置換で、元の `Start`（cache 付き）版は残っている（既存 Check の文は不変）。`hftCoreCloses_of_root` など鎖外の宣言は複製していない。

### 61.6 範囲・compiler 変更・次

- 変更: `Tools/ShippingFGCircuitS3kChain.lean`・`…S3kFinal.lean`・`Tests/Gen5/FGCircuitPilotCheck51.lean`（新規。`lakefile.lean` に `lean_lib` 3 件）と本節。`Sparkle/`・v9・v10・既存 Check・既存の文は**不変**。新 law・axiom・sorry・native_decide・TRUSTED なし。
- 次の候補: `hsynth`（S3: `sparkleChildSynth` の `SetGet` を `hcell` に足す設計、§59.3、reviewer 判断）、`hquiet`（`quiet` の具体的な選択）。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。A.P-02（Start）は `quiet`・`sv` が残るので行は外さない（数え方は reviewer が決める）。

## 62. S3l（Issue `sparkle-fg-circuit-pilot`）: Check50 の表現補修、`hsynth`・`hquiet` の供給経路の調査（供給できず、欠けている文を明示）

土台 `c2362658`（S3k）。**変更**: `Tests/Gen5/FGCircuitPilotCheck50.lean`（表現と depth 検査の追加）、`Tools/ShippingFGCircuitS3jFinal.lean`（`vacuousLaws` の docstring のみ。文・定義は不変）、docs（§60 の訂正、本節）。`Sparkle/`・v9〜v11・既存の文は**不変**。新 law・axiom・sorry・native_decide・TRUSTED なし。**v12 と Check52 は作っていない**（`hsynth`・`hquiet` のどちらも供給できなかったため。下記）。

### 62.1 Check50 の補修（Tests と docs のみ。文は不変）

- OUTPUT の「非空の開始 cache でも artifact 不変」を **1 回の観測**に限定した。非空 cache も `CacheInvA` を満たし得るので、これは `CacheInvA` 不要の一般証明ではない。cache 半分の一般の除去根拠は `jqc_after_head` と S3k の最終接続（§61）。
- depth: 復元しているのは**テスト側の `set savedDepth`**で、wrapper ではない。wrapper 自身の挙動を見るため、復元の**前**に depth が 1 のまま（wrapper は depth を書かない）ことを検査する行を足した。
- `vacuousLaws` の docstring: 「`hquiet` が偽なので前件全体が充足不能」。`hsynth`・`hcache` が個別に偽とは示していない（§60.5 にも訂正を入れた）。

### 62.2 `hsynth`: `sv w = some synthesizeChild`（`w` = wrapper の開始 world）

`sv w` は `readOf sparkleChildSynth w`、型は `Option (Name → MetaM (Module × Design))`（Elab.lean:1042）。`initialize sparkleChildSynth.set (some synthesizeChild)`（Elab.lean:9222）が設定する。

調べた経路と結果:

1. **wrapper で読んで検査する**: 関数値は `BEq`/`DecidableEq` を持たない。取れる検査は `isSome`（`= some synthesizeChild` より弱い。`some f` の `f` が別の関数でも通る）まで。**不十分**。
2. **ポインタ等価**（`ptrAddrUnsafe`/`ptrEq`）: 論理的には opaque で、調査した範囲では `ptrEq a b = true → a = b` を与える既存の定理は**未供給**（その形の補題を追加する場合は新しい仮定になり、本件では採らない。axiom 禁止）。**採らない**。
3. **run から導く**: 成功した run は `sv w = none` や別関数でも成り得る（`sparkleChildSynth.get` が none のとき 5270・5293 は `return none` で、別の経路で成功する可能性を排除できない。これは none 時の別経路の可能性の指摘であって、この固定 root での成功反例の証明ではない）。`hcell` の `CellOK cref sparkleChildSynth` は `ReadWorld`・`ref ≠ cref.ref`・`SetFrame` で、**値には何も言わない**。調査範囲では `hr` と `hcell` から `sv w = some synthesizeChild` は**未供給**（導けないことの証明ではない）。
4. **initialize を通す構造的な経路**: 「開始 world は初期化後」は world についての主張であって、この run の `hr` からは出ない（§59.3 の注意のまま）。
5. **wrapper が自分で `sparkleChildSynth.set (some synthesizeChild)` する**（調査範囲で、Tools 側のみで実装できる経路として見つかったもの。ほかに無いことの証明ではない）。出力は不変の見込み（初期化値と同じ値の再設定）。ただし:
   - 設定後の world `ws := setW sparkleChildSynth (some synthesizeChild) w` で `sv ws = some synthesizeChild` を得るには **`SetGet sparkleChildSynth`**（`∀ v w, readOf r (setW r v w) = v`）が要る。`CellPrem` の 9 番目の `SetGet cref` は Core 状態 ref の話で、追跡 3 ref の `SetGet` は**無い**。
   - `dv ws = 0`・`cv` の不変、`envAt cref ws = envAt cref w`、`hD hG hT hs h0` の world も `w` から `ws` に移る。`SetFrame sparkleChildSynth sparkleSynthDepth`・`SetFrame sparkleChildSynth sparkleChildCache`・`ReadWorld` 系の追加（および `hD hG hT hs h0` を `ws` で言い直すか、`ws = w` 相当の前提）が要る。
   - これは **既存 `hcell` だけからは出ない新しい未供給内容の追加**であり、`hsynth` を `CellPrem` の新 field に置き換えるだけである。reviewer 指針（SetGet を足すだけの案は新しい未供給）に従い、**供給とは数えず実装していない**。

**必要になる場合の候補の型と増減（実装していない。候補であり、`envAt`・`quiet`・各残前提の `ws` への移送まで十分と検証した完全な境界ではない）**: `CellPrem'` := `CellPrem` ∧ `SetGet sparkleChildSynth` ∧ `SetFrame sparkleChildSynth sparkleSynthDepth` ∧ `SetFrame sparkleChildSynth sparkleChildCache`（field +3）。wrapper `pilotEntry4 X := do (checks of pilotEntry3); sparkleChildSynth.set (some synthesizeChild); synthesizeCombinationalOffR pilotReaderOk2 X`。v12 の binder は `hsynth` が消え、`hcell` が `CellPrem'` に替わる（binder 数 10 → 9、ただし未供給の field が +3。**FG 行の減算にはならない**）。残りの premise は `ws` で言い直しが要る。compiler 変更（`Sparkle/` の ref の隣に tag を置く案: 例えば `sparkleChildSynthTag : IO.Ref Bool` を `initialize` で `synthesizeChild` と同時に設定し wrapper が読む）は**関数値の同一性を tag の同一性に置き換えるだけ**で、tag と ref が同時に書かれる不変量が新たに要る。かつ `Sparkle/` は今回の範囲外。**説明のみで、この項目はここで止めた。**

### 62.3 `hquiet`: `L.O.quiet w`

- `quiet : Void IO.RealWorld → Prop` は **`L : Laws` の field（データ）**で、v11 の `L` は全称の binder である。`hquiet` は「**その `L` が選んだ** `quiet` が `w` で成り立つ」であって、実世界の特定の述語ではない。
- `quiet` は**抽象 field**であり、stderr などの性質は、想定する具体化に課す要件であって `quiet` の定義そのものではない。
- 想定する具体化の操作的な意味（§59.1 W6、§59.2）: 追跡 3 ref（`sparkleChildCache`・`sparkleChildSynth`・`sparkleSynthDepth`）の `Δ` を保つ範囲で、run の各 leaf 操作（診断 `ioEprintln`・`Handle.mk`、`ppExpr`、side ref の set など）の後も保たれる述語。stderr が cell を書く stream に差し替えられていない、という世界の性質を含む（§57 の `hG` と同根）。この世界の性質（具体化の要件）は **ref の値ではなく IO の stream/handle の状態**で、wrapper が `MetaM` から読める ref ではない。
- **wrapper の検査で同じ run の `quiet` を立てられるか: できない。** (a) `quiet` は `L` の抽象述語で、wrapper が読める量ではない。(b) `L` の他の 13 field（`diag`・`frameQ`・`cacheSetQ`・`depthSetQ`・`frame` ほか。§59.2）が同じ `quiet` で成り立つことも同時に要る。`quiet := fun _ => True` を選べば `hquiet` は自明だが `diag` が偽になり得（§59.2 `O.quiet` 行）、`quiet := fun _ => False` なら `hquiet` が偽（`vacuous_no_hquiet`）。**具体的な `quiet` と `Laws` の field の同時の証明が必要で、これは `L` 全体（A.P-01）の供給**であり、`hquiet` 単独の項目ではない。
- したがって欠けている文: ある具体の `quiet₀ : Void IO.RealWorld → Prop` について `Laws mref cref` の値 `L₀`（`L₀.O.quiet = quiet₀`）が構成でき、かつ実 run の開始 world で `quiet₀ w` が成り立つこと。**未供給**。

### 62.4 v12・Check52

どちらも作っていない（供給された項目が無いため。「v12 は `hsynth` か `hquiet` のどちらかが供給されたときだけ」）。v11 の 10 binder `L hquiet hsynth hr hcell hD hG hT hs h0` のまま。

### 62.5 範囲・台帳

- **非空虚な Laws / CellPrem / quiet が実 run について同時に成り立つこと（`hquiet`・`hsynth`・`L`・`hcell`・`hD hG hT hs h0`）は、今回も未供給**。quiet=False の拒否と依存の走査（Check50/51）は、そうした充足例を与えたことにはならない。
- compiler（`Sparkle/`）の変更: なし。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 63. S3m（Issue `sparkle-fg-circuit-pilot`）: 案 A（非空虚性）— `CellPrem`・`Laws` を field 別に構成・反駁。最初の阻害 field、設計の出口

土台 `cbc80365`（S3l）。**変更**: `Tools/ShippingFGCircuitS3mField.lean`（新規）、`Tests/Gen5/FGCircuitPilotCheck53.lean`（新規）、lakefile の lean_lib 2 件、docs（§62.2/62.3 の表現限定を先に 1 コミット、本節）。`Sparkle/`・v9〜v11・既存の文は**不変**。新 law・axiom・sorry・native_decide・TRUSTED なし。**v12 は作っていない**。

### 63.1 結論（先に）

- **非空虚な `CellPrem`・`Laws`・`quiet` と v11 の他の前件（`hsynth hD hG hT hs h0 hr`）の同時充足は、既存の opaque な IO 定義の上では構成できなかった。** 構成できた field は **0**。
- **最初の阻害 field（`CellPrem`）**: `hcell` の第 1 conjunct `ReadWorld sparkleChildCache`（§63.3）。
- **最初の阻害 field（`Laws`）**: `L.O.diag`。`quiet` が `False` 以外の世界を 1 つでも持つなら、`diag` の最小の事例 `Diag.ioGetStderr` が、opaque な `IO.getStderr` についての文 `StderrKeeps quiet` を要求する（§63.4）。
- **矛盾は見つからなかった**。上の 2 つは「未供給」であり「矛盾」ではない（opaque 定数は型以外に制約を持たないので、論理の中では `ReadWorld`・`StderrKeeps` の真偽どちらも反証できない。これは `opaque` の意味についての説明で、kernel で検査したのは §63.2 (B) の「opaque である」「文がそこに到達する」まで）。
- 調査範囲に限った主張である。他の経路が無いことの証明ではない。

### 63.2 設定（手順 1）と、4 分類

同じ `mref cref mctx cctx` と開始 world `w` の上の `pilotEntry3` の run（v11 の `hr`）を設定とした。`w : Void IO.RealWorld` は**抽象**で、`Void` は opaque な `Void.nonemptyType σ` の `type`、`Void.mk` も opaque。world を動かすのは `ST.Prim.Ref.get/set/mkRef`（opaque、実体は `inhabitedFromRef` で、kernel は展開しない）と `IO.getStderr` など（opaque / `extern`）だけで、`ST.Ref.ref : ST.RefPointed.type` の `ST.RefPointed` も opaque な `NonemptyType`。既存 API が `readOf / setW / ST.Ref.get / set` について証明させるのは、`readOf_get`（`get` の値は `readOf r w`、世界は `getW r w`）、`runsTo_get` 類の**定義の展開**だけで、`ReadWorld`・`SetGet`・`SetFrame` は**前提**（`PREMISE for the real runtime`）として定義されている。実際の `initialize sparkleChildCache` 等も opaque 定数（`Check53 OPAQUE`）。

| 分類 | 内容 | 状態 |
|---|---|---|
| (a) 純粋な模擬モデルの充足 | `readWorld_shape_both`（`∀ w, g w = w` の形は明示状態の上で充足も反証も可能）。既存の `Tools/ShippingHeapModel.lean`（ref のみの断片の模擬 heap。自前の `RunsTo`・`M σ α` で、`Tools.ShippingEntrySoundness.RunsTo` との**橋は無い**） | 実 pilot の証人ではない。新しい模擬 heap は作っていない |
| (b) 既存 opaque IO 定義についての定理 | `cellPrem_iff_fields`（`CellPrem` = 10 top-level = 16 atomic conjunct）、`readWorld_cache_unfold`、`cellPrem_false_of_subsingleton`、`endW_getStderr`、`stderrKeeps_of_ops` / `_of_laws`（`diag` の事例）、`stderrKeeps_of_id`、`diag_stderr_at_depth0` | kernel 検査済（Check53） |
| (c) 実ランタイムとの対応 | **無い**。`Void IO.RealWorld` は実行時には消える token で、`ReadWorld`・`SetFrame`・`StderrKeeps` の「実ランタイムで真」は、論理側のどこにも接続されていない | 未接続 |
| (d) MetaM 実行の観測 | Check53 (E): この compile process で depth=0、`sparkleChildSynth` が some、cache 0 件（今回の限定として cache=0 なら空）、`IO.getStderr` の前後で **観測量 3 つ（`cache.size`・`synth.isSome`・`depth`）が一致**（関数値の同一性も cache 全構造も比較していない。「3 cell 不変」とは書かない）、`pilotEntry3 hftRoot` が `run_cmd` の文脈でエラー無く返る。**論理的な内容は無い**（world が token なので `ReadWorld` 等は観測できず、`hr` の開始 world は Lean の項ではない） | 観測のみ |

`hr` の証拠について: 論理側に `RunsTo (pilotEntry3 X) mctx mref cctx cref w a w'` の**項は無い**。`pilotEntry3` は depth の `get` の値（opaque）が `0` であること、`mref` の状態から環境を引くこと、数百の opaque IO を経ることを要し、既存 API に `readOf mref w` や `setW` の結果についての `SetGet mref` も無い（`CellPrem` の `SetGet` は `cref` のみ）。(d) の観測は同じ文脈の run が実際に成功したことを示すが、それは (b) の `hr` の証拠ではない。

### 63.3 `hcell`（`CellPrem`）の field 別（手順 2）

`CellPrem Fresh mref cref` は 10 の top-level conjunct（`CellOK` 3 つ、`SideRef` の全称、`Fresh` の全称、`ReadWorld mref`・`SetFrame mref cref`・`mref.ref ≠ cref.ref`・`ReadWorld cref`・`SetGet cref`）で、`CellOK cref r := ReadWorld r ∧ r.ref ≠ cref.ref ∧ SetFrame r cref` を開くと 16 の atomic conjunct（`cellPrem_iff_fields`）。

| # | field | 状態 |
|---|---|---|
| 1 | `ReadWorld sparkleChildCache` | **阻害（未供給）。最初の阻害 field** |
| 2–16 | 残り 15（`cache.ref ≠ cref.ref`、`SetFrame cache cref`、synth・depth の 3 つ組、`SideRef`・`Fresh` の全称、`mref`・`cref` の 5 つ） | **試していない**（ルーリング: 最初の阻害 field で止める） |

**完全な型**: `ReadWorld (r : IO.Ref σ) := ∀ w : Void IO.RealWorld, getW r w = w`、`getW r w := match (ST.Ref.get r : ST IO.RealWorld σ) w with | .mk _ w' => w'`。ここで `r = sparkleChildCache : IO.Ref (Std.HashMap Name (Module × Design))`、`σ` はその `HashMap`。**量化範囲**: 全ての `w : Void IO.RealWorld`（到達可能な world に限らない）。**opaque な primitive**: `ST.Prim.Ref.get`（`ST.Ref.get` は `liftM <| Prim.Ref.get`）、`sparkleChildCache`（`initialize` による opaque 定数）、`Void.nonemptyType`。文の到達する opaque 定数は Check53 (B) に列挙（`ST.Prim.Ref.get`・`sparkleChildCache`・`Void.nonemptyType`・`IO.RealWorld.nonemptyType`、型の `HashMap Name` 由来の `mixHash`・`String.hash`）。`Prim.Ref.get` の定義式（`inhabitedFromRef r`）は opaque のため kernel は展開しない。既存 API に `ReadWorld` を与える定理は無い。

付記（同じ境界の別の field を試したのではなく、2 の型を読んで分かること）: field 2・15 の `r.ref ≠ cref.ref` / `mref.ref ≠ cref.ref` は、`ST.RefPointed.type` の**相異なる 2 点**を要する。調査範囲で API から見つけた点は `Classical.choice ST.RefPointed.property` の 1 点だけで、相異なる 2 点を与える手段は**調査範囲では未供給**（構成不能と断言はしない。`cref` は run が与える変数）。`cellPrem_false_of_subsingleton` は**条件付き反駁**: `ST.RefPointed.type` が subsingleton ならどの `mref cref` でも `¬ CellPrem`。実ランタイムでは ref は別物だが、論理にはそれを言う文が調査範囲で見つからなかった。矛盾ではない（subsingleton は仮定であって、示されていない）。

### 63.4 `Laws L` の field 別（手順 3）

`Laws := { O : RefLawsAOps MkRefd mref cref, T : RefLawsATele O.quiet mref cref }`。`RefLawsAOps` は 10 field（`quiet`（データ）・`diag`・`frameT`・`excOk`・`frameQ`・`cacheSetQ`・`depthSetQ`・`frame`・`cacheSet`・`depthSet`）、`RefLawsATele` は 4 field（`telescope`・`lamTelescope`・`localDecl`・`letDecl`）。

| field | 状態 |
|---|---|
| `quiet` | 選択可能。`False` は既に拒否済（`vacuous_no_hquiet`）。非 `False` の候補として「`dv w = 0`」（追跡 ref の述語）を取った |
| `diag` | **阻害（未供給）。最初の阻害 field** |
| `frameT … depthSet`（8）、`T` の 4 | **試していない**（`quiet := False` では全て空虚に成り立つが、それは非空虚ではない） |

**完全な型**（`diag`）: `∀ {mctx cctx α}, AdmCtx quiet mctx cctx → ∀ (p : MetaM α), Diag p → ∀ w, quiet w → (cv (endW mctx mref cctx cref p w) = cv w ∧ sv (endW …) = sv w ∧ dv (endW …) = dv w) ∧ quiet (endW mctx mref cctx cref p w)`。**量化範囲**: 全ての許容文脈、全ての `Diag p`（`profLog`・`ppExpr`・`ioEprintln`・`msgToString`（`OkMsg` のみ）・`ioGetStderr`・`stderrFlush`・`ioHandleMk`・`ioHandlePutStrLn`（任意の `Handle`）・`ioHandleFlush`（任意の `Handle`））、`quiet` な全ての world。

最小の事例 `p := liftM IO.getStderr` で、`endW … p w = stderrW w`（`endW_getStderr`、`rfl`）。したがって（`stderrKeeps_of_ops`、**構成した定理**）任意の `L : Laws` で `StderrKeeps L.O.quiet`:
`∀ w, quiet w → (cv (stderrW w) = cv w ∧ sv (stderrW w) = sv w ∧ dv (stderrW w) = dv w) ∧ quiet (stderrW w)`。`stderrW w` は opaque な `IO.getStderr : BaseIO Stream` が返す世界で、**API は型以外の情報を持たない**。つまり非 `False` の `quiet` が `w` で成り立つなら、`w` で `IO.getStderr` が 3 値と `quiet` を保つという opaque primitive についての文が必要になる（`diag` からの必要条件の抽出）。強い十分条件の例は `∀ w, stderrW w = w`（`stderrKeeps_of_id`: world 全体の同一性は `StderrKeeps` が要求するより強く、「最小」ではない）。`diag_stderr_at_depth0` は `O.quiet w ↔ dv w = 0` と depth=0 を**仮定した**含意であり、非空虚な `quiet` の構成でも同値の証明でもない。`quiet = (dv = 0)` が `depthSetQ` による任意 depth への更新を保てるかも必要で、`Laws` の具体候補として確立したとは書かない。いずれも未供給。

**矛盾との区別**: `quiet := False` 以外で `Laws` の field 同士が kernel で反駁できる組合せは**見つからなかった**。`diag` から `StderrKeeps` が出る（含意）ことは、矛盾ではない。

**構造的な観察（未検証）**: 非空虚な有効な `quiet` 全体の和（最大の `quiet`）を取って `Laws.O` を「構成」する案は、`AdmCtx` が `quiet` について反単調でない（`InertUnfold` の結論が `quiet w'` を含む）ため、`O` の field の和閉包がそのままは成り立たない。Lean では検査していない（読みのみ）。

### 63.5 設計の出口（候補。実装していない。新 TRUSTED は採用済みではない）

**(1) opaque な実行モデルが障害 → 明示状態の意味論と実装対応の境界（手順 4）**

- **最小の明示状態**: `Tools/ShippingHeapModel.lean` の `Heap`（追跡 3 cell・side cell・run-local cell・診断環境 `reg`）と `M σ α`（状態関数 + 例外）。ここでは `get_set_same`・`get_set_other`・`runsTo_getM`（read は heap を変えない）・ref のみの field 類似が**証明済**（`CellPrem` の `ReadWorld`・`SetGet`・`SetFrame` に当たる）。
- **実装対応の境界（新 TRUSTED 資料の候補。採用しない）**: ある抽象化 `abs : Void IO.RealWorld → Heap` と、各 leaf 操作（追跡 3 ref と 24 の `SideRef` の `get/set/modify`、`mkRef`、`Diag` の 9 構成子、`throwError` の 2 構成子）についての simulation 文: `RunsTo (leaf) … w a w' → ModelRun leaf (abs w) a (abs w')`。実 IO は残す（`IO.getStderr`・`Handle`・`ppExpr` は実 primitive のまま、その simulation 文が境界）。
- **現在の境界との比較**: 現在は `CellPrem`（16）と `Laws`（`O` 9 + `T` 4）が `Void IO.RealWorld` 上の**直接の文**（未供給）。置き換えは、これらを (i) 模擬 heap 上の証明済の法則と (ii) leaf 操作ごとの simulation 文（上の 24+3 個の ref 操作 3 種、`mkRef`、`Diag` 9、`Throws` 2 程度）に分ける。**減る**のは「世界上で `ReadWorld`・`SetFrame` を各 ref について主張する」部分、**増える**のは `abs` と simulation の対応。**`IO.getStderr` 等の `Diag` の効果**（`StderrKeeps`）は simulation 文として残る（模擬 heap では `reg` の効果として明示される）ので、未供給の内容が**消える**のではなく、**どの primitive が何をするか**に局在化される。規模は文の数で言えば同程度、見える単位が leaf 操作になる。`hr` は引き続き `RunsTo` の run で、`abs` を通して模擬 heap の run に移る。**橋（上の simulation）が無い限り模擬モデルは実 pilot の証人ではない**。

**(2) 任意操作・任意文脈の量化が障害 → 対象実行への制限（手順 5）**

- `Laws.O.diag` の `∀ p, Diag p` は任意の `Handle`（`ioHandlePutStrLn h`・`ioHandleFlush h`）と任意の `msgToString m`（`OkMsg` のみ）を含み、`AdmCtx` も任意の許容文脈を含む。最小の制限は、`Laws` の操作の量化を **`pilotEntry3 declName` の run が実際に行う leaf 操作の集合**（run の構造から決まる有限集合: `Reach` 系が既に持つ到達操作）と、**run が到達する文脈**に限ること。`hr` が与える run に対して、`diag` は run の `ioEprintln`・`ppExpr`・`Handle.mk`（固定パス）等だけを言えばよく、任意の `h` を言わなくてよい。
- 保たれる必要がある IP: v11 の結論（artifact・環境・出力）と `hquiet` / `hsynth` / `hcell` が run のどの操作に使われるかの対応。**この制限をしても `StderrKeeps` 型の文（`IO.getStderr` が cell を保つ）は run が `getStderr` を行う限り残る**。つまり (2) は文の数を減らすが、opaque primitive の効果についての未供給は残る。(1) と組み合わせて初めて局在化できる、というのが現時点の読み（検証していない）。

### 63.6 監査記述の限定の確認

§62.2 の「唯一の経路」「出ない」、pointer 等価の補題を与えれば直ちに axiom、は「調査範囲で未供給」へ、none 時の別経路の指摘は固定 root の成功反例の証明ではない、と限定した。`CellPrem'` の +3 は候補で、`envAt`・`quiet`・各残前提の `ws` への移送まで十分と検証した完全な境界ではない。§62.3 の `quiet` は抽象 field で、stderr の性質は想定する具体化の要件であって定義そのものではない（本節の `StderrKeeps` はその要件を、`diag` の事例として明示したもの）。

### 63.7 検査（Check53）・範囲・台帳

- Check53（`Tests/Gen5/FGCircuitPilotCheck53.lean`）: (A) 構成した 5 定理の完全な型が独立に書いた型と一致し、mutant 9 件を拒否、(B) 10 の primitive が opaque 定数であり、第 1 field の文・`stderrW`・`StderrKeeps` が定義を辿って到達する opaque 定数の列挙（API の定理は探索しない。「API に定義式がない」「他に opaque はない」は走査の証明内容ではなく、調査範囲で未発見という意味。S3n で、fuel 切れで todo が残れば throwError に修正し、fuel=3 の負対照を追加）、(C) field の数（`CellPrem` 10/16、`RefLawsAOps` 10、`RefLawsATele` 4、`diag` が `quiet` の次）、(D) AXIOMS は標準のみ（9 名）、(E) MetaM の観測（(d)）。
- 新しい証明範囲の対象（`Tools.ShippingFGCircuitS3mField`、`Tests.Gen5.FGCircuitPilotCheck53`）だけを build した。compiler（`Sparkle/`）は不変で、出力 baseline は再実行していない。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 64. S3n（Issue `sparkle-fg-circuit-pilot`）: Check53 修正（reviewer 修正依頼 1–3）と E1 の最小試作 — 明示状態モデル + 小さな接続（対応仮説は**書き出しただけ**で採用しない）

土台 `cb923479`（S3m）。**変更**: Check53 / `Tools/ShippingFGCircuitS3mField.lean` のコメント・§63 の表現（先に 1 コミット、文は不変）、新規 `Tools/ShippingFGCircuitS3nModel.lean`・`Tools/ShippingFGCircuitS3nBridge.lean`・`Tests/Gen5/FGCircuitPilotCheck54.lean`、lakefile の lean_lib 3 件、本節。`Sparkle/`・v9〜v11・既存の定理の文は**不変**。新 law・axiom・sorry・native_decide・TRUSTED なし。対応仮説は名前付きの Prop（`def`）で、どれも採用していない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。モデル内の証明や対応仮説への置換は台帳の減算ではない。

### 64.0 結果の要約

- **Check53 修正**: `opaquesOf` は fuel 切れで todo が残れば `throwError`（部分結果を返さない）。fuel=3 の負対照を追加。OPAQUE の出力は「定義を辿る走査で調査範囲では定義式が見つからなかった」に限定し、「API に定義式がない」「他に opaque はない」は走査の証明内容にしない（API の定理は走査しない）。OBSERVATION は比較した観測量 3 つ（`cache.size`・`synth.isSome`・`depth`）の一致に限定（関数値・cache 全構造は比較していない。cache=0 なら空）。`stderrKeeps_of_id` は world 全体の同一性という強い十分条件で「最小」ではない、`diag_stderr_at_depth0` は `O.quiet w ↔ dv w = 0` と depth=0 を**仮定した**含意で非空虚な quiet の構成でも同値の証明でもない、`quiet = (dv = 0)` が `depthSetQ` による任意 depth への更新を保てるかも必要で `Laws` の具体候補として確立したとは書かない、相異なる 2 点は「調査範囲で未供給」（構成不能と断言しない）、`cellPrem_false_of_subsingleton` は条件付き反駁、とコメントと §63 を直した。
- **E1 モデル**（`Tools/ShippingFGCircuitS3nModel.lean`）: 既存 `ShippingHeapModel` を再利用して、診断出力 + 環境変数の成分、`getStderr`/`getEnv`/`eprintln`、`mref`/`cref`/side の別位置、具体初期状態、非 `False` の quiet、成功実行を**モデルの定理**として証明した。
- **接続**（`Tools/ShippingFGCircuitS3nBridge.lean`）: `Rel`、leaf ごとの対応仮説（`GetCorr`/`SetCorr`/`StderrCorr`/`EnvCorr`）、初期対応 `InitCorr` を書き出し、**向きは「実 run 成功 → 対応するモデル run 成功（同じ返却値・関連する終了状態）」**。仮説の下で `pure`・`bind` の合成と get/set/getStderr の小さな合成 `bridge_small` を証明した。最終結論を仮定する橋ではない。
- これらは新モデルと対応仮説についての定理であり、既存の opaque な型の `CellPrem` / `Laws` そのものを得たとは呼ばない。`CellPrem`・`Laws`・v11 の前提は 1 つも減っていない。

### 64.1 `ShippingHeapModel` を再利用するか — 再利用した（理由と限界）

再利用した理由: (i) 追跡 3 cell（cache・synth・depth）が型付き `Ref`（`Ref.cache : Ref σ σ.C` 等）で、side cell `other n` と別の構成子（`hget`/`hset` の `get_set_same`・`get_set_other` が既に証明済）。(ii) `M σ α`（状態関数 + 例外）、`bindM`、`RunsTo`、`endW`、`cv/sv/dv` が実側の `RunsTo`/`endW`/`cv/sv/dv` と同じ形。(iii) 診断環境 `reg : σ.P` が既にある。(iv) `Sig` が内容型に対して一般なので、接続側では `C := Std.HashMap Name Res`、`S := Option (Name → MetaM Res)` と**実の型そのもの**を入れられ、`Rel` を抽象関数でなく**等式**にできる（抽象化が単射でない問題を避ける）。

追加したもの: `P := DiagEnv`（出力の行リスト `stderr` と環境変数の連想リスト `env`）、`mref = other 0`・`cref = other 1`・side `= other 2` の別位置、`getStderrM`（ストリーム値は**モデル化せず** `Unit`）・`getEnvM`・`eprintlnM`、quiet `quietM h := (環境に SPARKLE_DEBUG が無い)`。

限界（正直に）: 既存 `Sig` の `O` は 1 つなので、`mref`/`cref`/side の 3 位置は**同じ型 `Nat`**（位置は別だが型では区別されない。追跡 3 ref は `C`/`S`/`Nat` で型付き）。実の `Meta.State`/`Core.State` の中身はモデル化していない。

### 64.2 モデル内で証明したこと（`Tools.ShippingFGCircuitS3n`）

- 読戻し・非干渉: `readback_depth/cache/mref`、`set_mref_frame`（`mref` の write は `cref`・side・追跡 3 cell を変えない）、`set_depth_frame`（depth の write は cache・synth・`mref`・`cref` を変えない）。
- 診断 leaf は追跡 heap を保つ: `getStderr_keeps`（終了 heap が同一）、`getEnv_keeps`（同一 heap + 返値は環境の lookup）、`eprintln_keeps`（追跡 3 cell・他 cell・環境・quiet を保ち、出力成分だけ末尾に 1 行増える）。
- 具体初期状態 `s0`（cache `[10]`、synth `some 7`、depth 0、環境は `HOME` のみ）。`quiet_s0 : quietM s0`、`quiet_fails_sLoud : ¬ quietM sLoud`（`SPARKLE_DEBUG` を設定した状態）、`quiet_nonconst`（quiet は `False` でも `True` でもない）。`heapLaws_with_quietM`: 既存の ref のみの `HeapLaws`（モデル上のもの。`RefLawsCore` ではない）が**この quiet で**充足される。
- 成功実行 `exec_ok`: `prog`（depth の get/set、cache の get/set、getStderr、`mref` の set、`getEnv "HOME"`、`eprintln "done"`）が `s0` から `(0, some "/root")` を返し、終了状態は depth 1、cache `[20, 10]`、synth `some 7`、`mref` 5、`cref` 0、出力 `["done"]`、quiet 保持。kernel の `rfl`/`decide`（閉じたデータ）で確認、native_decide なし。

### 64.3 接続: `Rel` と対応仮説（書き出した文。採用していない）

実側は `Void IO.RealWorld` の世界と `mctx mref cctx cref` の下の `RunsTo`、モデル側は `Heap realSig`（`realSig := sigOf (Std.HashMap Name Res) (Option (Name → MetaM Res))`）。

```
Rel h w            := cv w = h.cache ∧ sv w = h.synth ∧ dv w = h.depth
Corr … RA m p      := ∀ w w' h a, Rel h w → RunsTo m mctx mref cctx cref w a w' →
                        ∃ b h', RunsTo(model) p h b h' ∧ RA a b ∧ Rel h' w'
GetCorr r rm       := Corr … (· = ·) (ST.Ref.get r : MetaM σ) (getM rm)
SetCorr r rm       := ∀ v, Corr … (· = ·) (ST.Ref.set r v : MetaM Unit) (setM rm v)
StderrCorr         := Corr … (fun _ _ => True) (liftM IO.getStderr : MetaM IO.FS.Stream) getStderrM
EnvCorr k          := Corr … (· = ·) (liftM (IO.getEnv k) : MetaM (Option String)) (getEnvM k)
InitCorr w0        := ∃ h0, Rel h0 w0 ∧ quietM h0
```

- **向き**: 実 run の成功 → モデル run の成功（返却値は `RA`、`get`/`set`/`getEnv` は等しい、`getStderr` はストリーム値を比較しない）。モデル → `RunsTo` の向きは **mutant として Check54 が拒否**する。
- **結果・エラー・終了状態**: 結果は `RA`、終了状態は `Rel h' w'`。エラー: `get`/`set` は `ST`（実 run が必ず成功: `refGet_runs`/`refSet_runs`）、`getStderr` は `BaseIO`（`runsTo_getStderr`、本節で証明）で、モデル leaf も `.error` を返さないため、この範囲ではエラーの対応は空（`throwError`/例外は**未モデル化**、§64.5）。`IO.getEnv` は `BaseIO` と見ているが、`EnvCorr` を使う橋の証明は書いていない。
- `Rel` は追跡 3 ref の中身だけを関係づける。`mref`/`cref`/side ref・診断出力・環境は `Rel` に入っていない（実側に対応する Lean の項がない）。`StderrCorr`/`EnvCorr` の仮説は「モデルの環境成分が実プロセスの環境である」ことを含む。
- いずれの仮説も `realProg`・`modelProg`・`pilotEntry3`・`Laws`・`CellPrem`・v11 の結論を含まない（Check54 (D) が定義の使用定数を検査）。

### 64.4 橋の補題（仮説の下で証明）と、v11 のどの前提へ渡せるか

証明した補題: `runsTo_set`、`runsTo_getStderr`（実の leaf の走行）、`corr_pure`、`corr_bind`（部分の対応が合成される。継続の対応は関連する中間値の組ごと）、`bridge_small`（`get depth; set depth (d+1); getStderr; pure d` について `GetCorr depth`・`SetCorr depth`・`StderrCorr` の下で、実 run の成功 → モデル run の成功・**同じ返却値**・`Rel`）、`modelProg_spec`、`real_small_consequence`（実 run の返値は開始 depth、終了 depth は +1、cache と synth は不変 — モデルを通して得た実 run の帰結）、`stderrKeeps_of_corr`。

- **逆向きの含意（`CellPrem` の field ⇒ 対応仮説）**: `getCorr_of_readWorld`・`getCorr_depth`（`ReadWorld r` から `GetCorr`）、`setCorr_depth`（`SetGet`・`SetFrame`×2・ref の不等 2 つから `SetCorr`）。つまり対応仮説は `CellPrem` の field より**弱い**（`Rel` の像の上の値の文）。逆に `GetCorr` から `ReadWorld r`（`∀ w, getW r w = w`）は出ない: `Rel` は世界を決めず、`w' = w` を言わない。
- **渡せるもの（1 つ）**: `Laws.diag` の `Diag.ioGetStderr` の事例が要求する `StderrKeeps` を、`Rel` から作る quiet `quietR w := ∃ h, Rel h w ∧ quietM h` について、`StderrCorr` の下で（`stderrKeeps_of_corr`）。これは §63 で抽出した `diag` からの**必要条件 1 つ**を、この quiet について対応仮説に置き換えたもので、`StderrCorr` を供給したことにはならない。
- **渡せないもの**: (a) `CellPrem` の field の本体: `ReadWorld`/`SetFrame`/`SetGet` は**全ての world**に対する世界の等式を言うが、橋は `Rel` の像だけの値の文しか与えない（v11 の `hcell` を `Rel` の像の上に狭められる保証は今ない）。ref の不等 `r.ref ≠ cref.ref` も出ない。(b) `Laws.O.diag` 全体・他の 8 つの `Laws.O` field・`T` の 4 行。`stderrKeeps_of_corr` は `L.O.quiet := quietR` となる `Laws` を作らない（その `L` を作るには全 field が要る）。(c) `hr`（`pilotEntry3` の実 run）: 橋は run の各 leaf のモデル化を要し、`pilotEntry3` 全体のモデル run は未構成。(d) `hquiet`・`hsynth`・`hD`・`hG`・`hT`(TeleRX)・`hs`・`h0`: 触れていない。

### 64.5 未モデル化の一覧（抽象 handler 仮説に隠さず、`Laws` 完成とも言わない）

`Laws` / `CellPrem` のうち、このモデルと橋が**扱っていない**もの:

1. `SideRef`（24）の get/set/modify/modifyGet: モデルには `other n` の get/set/modify があるが、実の side ref との `Rel`・`Corr` は無い。
2. 新しい ref（`IO.mkRef` と `Fresh`）: モデルに `alloc` はあるが、実の `mkRef` との対応は無い。
3. 例外: `Throws`（`throwError` の 2 構成子）、`frameT`、`excOk`（`OkExc`・`OkEnv`・`OkMsg`）。モデルの `throwM` は橋に入れていない。
4. Meta 操作: `whnf`、`inferType`、`getConstInfo`、`getEnv`（Meta）、`readThe`、`ppExpr` 等の `Framed` の Meta primitive 構成子。
5. `Diag` の他の構成子: `profLog`、`ppExpr`、`ioEprintln`（モデルの `eprintlnM` はあるが `Corr` 仮説と橋は無い）、`msgToString`（`OkMsg`）、`stderrFlush`、`ioHandleMk/PutStrLn/Flush`。`IO.getStderr` はストリーム値を比較していない。`ioEnv`（`EnvCorr` は書いたが橋は未証明）。
6. `RefLawsATele` の 4 行: `telescope`、`lamTelescope`、`localDecl`、`letDecl`。
7. `Laws.O` の field のうち `frameQ`、`cacheSetQ`、`depthSetQ`、`frame`、`cacheSet`、`depthSet` の**実 world 上の文**。モデル上の ref のみの対応物 `HeapLaws` は既存だが、実の文の充足ではない。cache・synth の `SetCorr`（depth と同じ証明で書けるが書いていない）。
8. `mref`/`cref`（`ST.Ref` の `Meta.State`/`Core.State`）の実との対応と、`CellPrem` の `ReadWorld mref`・`SetFrame mref cref`・`mref.ref ≠ cref.ref`・`ReadWorld cref`・`SetGet cref`。
9. `modify`/`modifyGet` の leaf（モデルに `modifyM` があるが橋は無い）、`if`/`try-finally`/`for` 等の結合子の `Corr` 補題（`pure`・`bind` のみ証明）。
10. 開始 world `w0` の実在（`InitCorr` は仮説）と、`hr` を `pilotEntry3` のモデル run に落とすこと。fuel・`partial` ハンドラ。

### 64.6 検査（Check54、Check 自身の出力から）と build

- `Tests/Gen5/FGCircuitPilotCheck54.lean`: `FGCIRCUIT54 SIGNATURES: 11 theorems (…) equal their independently written types, 20 mutants rejected (…the bridge in the WRONG direction (model success -> real success), a vacuous return relation, a dropped StderrCorr hypothesis, an unrelated end state, …); Rel and Corr unfold to the independent spellings (Iff.rfl)`。`FGCIRCUIT54 EXEC`（`s0` で quiet が成り立ち `sLoud` で失敗、`prog` の成功実行）。`FGCIRCUIT54 NEGATIVE`（wrong ref、失敗する quiet、write leaf は追跡 depth を変える）。`FGCIRCUIT54 HYPS: 8 correspondence definitions … none mentions realProg, modelProg, … pilotEntry3, Laws, CellPrem or a v11 conclusion`。`FGCIRCUIT54 AXIOMS: 24 names, standard axioms only ([Quot.sound, Classical.choice, propext]); no sorryAx, no native_decide`。
- Check53 再 build: `FGCIRCUIT53 SIGNATURES: 5 constructed theorems … 9 mutants rejected`、`FGCIRCUIT53 OPAQUE: … the scan with fuel 3 throws (negative control), the scans below finish with an empty todo …`、`FGCIRCUIT53 AXIOMS: 9 names, standard axioms only`。
- 新しい対象（`Tools.ShippingFGCircuitS3nModel`、`Tools.ShippingFGCircuitS3nBridge`、`Tests.Gen5.FGCircuitPilotCheck54`、再 build した `Tests.Gen5.FGCircuitPilotCheck53`）だけを build した。compiler は不変。

### 64.7 費用の見積りと、残る対応の境界（reviewer の判断用。全体の移植の前）

**見積り（粗い）**: 本節の小接続は約 300 行（モデル約 150、橋約 200）。`Laws`/`CellPrem` の全体を同じ形で移植すると、未モデル化一覧の項目ごとに leaf 1 つあたり `Corr` 仮説 + 橋補題が 30〜60 行（`SideRef` 24、`Diag` 残り 8、Meta primitive 十数個、telescope 4、例外、`mkRef`、`modify`）で、合計 2,500〜4,000 行、加えて `pilotEntry3` の run 全体をモデル run へ落とす結合子（`ite`・`try-finally`・`for`・`match`）の `Corr` 補題と、v11 の `hr`/`hcell`/`hquiet` を `Rel` の像に狭める v12 の再定式化が必要。主要なリスクは量よりも、`Rel` の像に狭めた v11 前提が成り立つかどうかが未確認なこと。

**残る対応の境界**（このまま全体を移植しても残る。上の定義の文のとおり）:
- leaf ごとの `GetCorr`/`SetCorr`（追跡 3 ref、side ref、`mref`/`cref`、fresh ref）、`StderrCorr`、`EnvCorr`、（未定義の）例外・Meta primitive・Handle・telescope の `Corr`。いずれも**実の opaque primitive**（`ST.Prim.Ref.get/set`、`IO.getStderr`、`IO.getEnv`）についての文で、モデルでは証明されない。`getCorr_of_readWorld`/`setCorr_depth` が示すように、これらは `CellPrem` の field から導けるほど弱いが、`CellPrem` を供給するものではない。
- `InitCorr`: `hr` の開始 world がモデルの具体初期状態に `Rel` で対応すること。
- 結論: E1 は `Laws`/`CellPrem` の未供給を**消さず**、「全 world についての世界の等式」を「`Rel` の像の上の leaf ごとの値の文」へ**言い換える**。この言い換えが新 TRUSTED の候補としてレビュー可能な小ささに収まるかどうかが、全体の移植の費用対効果の判断点（新 TRUSTED の採用はしていない。具体的な残余対応文が出た後の判断）。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 65. S3o（Issue `sparkle-fg-circuit-pilot`）: S3n の橋の整合性欠陥の反駁と修正（oracle 付き `RelE`）、モデル内の同時充足、案 2 の比較資料

土台 `43a40e05`（S3n）。**変更**: 新規 `Tools/ShippingFGCircuitS3oFix.lean`、`Tests/Gen5/FGCircuitPilotCheck55.lean`、`docs/FG-CIRCUIT-BOUNDARY-COMPARISON.md`（未採用の比較資料）、lakefile の lean_lib 2 件、S3n の橋のコメント（旧 `EnvCorr`/`InitCorr`/`quietR` を反駁済みと印した。文は不変）、本節。`Sparkle/`・v9〜v11・既存の定理の文は不変。新 law・axiom・sorry・native_decide・TRUSTED なし。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

### 65.1 反駁（kernel 定理、Check55 が検査）

- `envCorr_inconsistent`（`_of_run` は run を与えた形）: 旧 `EnvCorr mctx mref cctx cref k` から `False`。旧 `Rel` は環境を縛らないので、`hEmpty`（`reg.env = []`）と `hSome`（`reg.env = [(k,"v")]`）が**同じ `w`** に関係する。旧 `Corr` は関係する全 `h` を量化するので、1 つの実 `getEnv k` の成功 run の戻り値 `a` が `none` と `some "v"` の両方に等しくなる。実 run は任意の world から存在する（`runsTo_getEnv`: `IO.getEnv` は `BaseIO`）。したがって旧 `EnvCorr` は実 `getEnv` の成功と**両立しない**。
- `oldInit_any_world`、`oldQuietR_eq_true`: 旧 `InitCorr w ∧ quietR w` は**任意の `w`** で成立し（cache/synth/depth を `w` から読み、環境は `[]`）、`quietR = fun _ => True`。`quietM` が `sLoud` で偽という小モデルの非自明性から、`quietR` の非自明性は従わない。`SPARKLE_DEBUG` のモデル例は `SPARKLE_PROFILE`・`DEBUG_HWCALL`・stream callback の安全性の証拠ではない。

### 65.2 修正（`RelE env`、環境 oracle を run 全体で固定）

```
RelE env h w   := cv w = h.cache ∧ sv w = h.synth ∧ dv w = h.depth ∧ h.reg.env = env
CorrE env … RA m p := ∀ w w' h a, RelE env h w → RunsTo m … w a w' →
                        ∃ b h', MRunsTo p h b h' ∧ RA a b ∧ RelE env h' w'
EnvCorrE env k := CorrE env … (· = ·) (liftM (IO.getEnv k)) (getEnvM k)
InitCorrE env w0 := ∃ h0, RelE env h0 w0 ∧ quietM h0       quietRE env w := ∃ h, RelE env h w ∧ quietM h
```

- oracle `env : List (String × String)` は `CorrE` の**パラメータ**で、leaf ごとに選び直せない。`corrE_bind`（仮説・継続の仮説・結論が同じ `env`）、`corrE_pure`、`bridge_smallE`、`real_small_consequenceE`、`getCorrE_depth`、`setCorrE_depth`、`stderrKeeps_of_corrE` を再証明。同一 oracle の 2 回読みは `bridge_env_twice`/`real_env_twice`（両方が `lookupEnv env k`）。`envCorrE_returns`: `EnvCorrE env k` は実戻り値を `lookupEnv env k` に固定する。
- 一般形 `GCorr`（任意の世界型・任意の実 run 関係）と `gcorr_bind`/`gcorr_pure`。`CorrE` は `GCorr` と `rfl` で等しい（`corrE_eq_gcorr`）。
- 対照: `relE_env_unique`/`relE_not_both`（同じ oracle の下で環境の異なる 2 状態は同じ world に関係しない）、`envCorrE_observation_committed`（oracle が `k` 未設定なら実の観測 `some v` は不可）。
- **モデル内の同時充足**（`Toy.simultaneous_sat`）: toy 意味論（世界は cache/synth/depth/環境のレコード、leaf の run 関係は手書き）で、1 つの oracle・1 つの開始 world・quiet なモデル heap・`GetCorr`/`SetCorr`（全値）/`StderrCorr`/`EnvCorr`（全キー）・合成プログラムの対応（`gcorr_bind`）・成功 `getEnv "HOME"`（`some "/root"`）が同時に成立。**モデル内の事実であり、実 pilot の証人ではない**（実の `getEnv` は opaque）。

### 65.3 修正版 `InitCorrE`/`quietRE` が実 world について制約すること・しないこと

- `initCorrE_iff`/`quietRE_iff`: `InitCorrE env w0 ↔ quietRE env w0 ↔ lookupEnv env "SPARKLE_DEBUG" = none`。`quietRE_world_independent`: **world に依存しない**。制約するのは oracle で、実プロセスとの接続は `EnvCorrE env k` の仮説だけが担う。`quietRE_oracle_nonconst`: oracle `[]` で成立し `[("SPARKLE_DEBUG","1")]` で不成立（oracle についての非自明な制約）。
- 制約しない: `SPARKLE_DEBUG` 以外の環境キー、`SPARKLE_PROFILE`・`DEBUG_HWCALL`・stream callback、`Laws.O.quiet` の抽象 field 全体、出力成分、`mref`/`cref`/side ref。oracle が run 中に変わらないことは仮説の内容で、証明ではない。
- `RelE` は世界の量化範囲を狭めない（任意の `w` に対し `w` から読んだ `h` が関係する）。変わるのは文の中身（世界の等式 → 値の文）。

### 65.4 検査（Check55、Check 自身の出力から）

`FGCIRCUIT55 SIGNATURES: 15 theorems equal their independently written types, 39 mutants rejected (…)`。`FGCIRCUIT55 REFUTE: 2 refutations as kernel theorems: envCorr_inconsistent (…), oldInit_any_world / oldQuietR_eq_true (…)`。`FGCIRCUIT55 CONTROL: …`、`FGCIRCUIT55 BIND: …`、`FGCIRCUIT55 SIMULTANEOUS: Toy.simultaneous_sat — … (a model-internal fact, not the real pilot)`、`FGCIRCUIT55 HYPS: 9 corrected definitions (…) are plain definitions (no axiom); none mentions a program, Laws, CellPrem, a v11 conclusion or the old Rel/Corr/EnvCorr/quietR; EnvCorrE reaches RelE (the oracle), the old EnvCorr does not`、`FGCIRCUIT55 AXIOMS: 36 names, standard axioms only ([Quot.sound, Classical.choice, propext]); no sorryAx, no native_decide`。新しい対象（`Tools.ShippingFGCircuitS3oFix`、`Tests.Gen5.FGCircuitPilotCheck55`、コメントを足した `Tools.ShippingFGCircuitS3nBridge`）だけを build した。

### 65.5 案 2 の比較資料

`docs/FG-CIRCUIT-BOUNDARY-COMPARISON.md`（未採用。reviewer 確認後にユーザーへ）。(a) 現行 `Laws`/`CellPrem` の条件付き保証、(b) 修正版 `Corr`、(c) 返された IR と元ソースの対応を kernel で検査する証明書／checker の実現可能性（調査のみ）を、未証明の文・利用者への保証（同じ元ソース・同じ返された artifact）・維持する IP・残る台帳行・操作の種類と量化範囲・費用（既知と未知、2,500〜4,000 行は coder の未検証の見積り）で比較した。(c) の主要な未確認は 4 点（pilot root への `#machine_endpoint` の適用、純粋な組立関数の有無、子 instance の接続、ソース側 `CD`/`CDX`）。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 66. S3p（Issue `sparkle-fg-circuit-pilot`）: 案 (c)（証明書／checker）の実現可能性調査 — S3o の未確認 4 点を確定し、証明書の文・欠けている部品・最短経路の再比較

土台 `59a49445`（S3o）。**調査と文書のみ**: `Sparkle/`・`Tools/`・`Tests/` は変更していない。コミットしない scratch ファイル（作業ツリーの外）で `kjob lake env lean` の読み取り専用プローブを走らせた。プローブは (i) 既存の定数の有無と型の表示、(ii) 既存の生成コマンドを scratch 環境で root に適用（生成物は scratch の環境内にだけ残り、保存していない）、(iii) コンパイラ入口を `run_cmd` で 3 回走らせた出力の比較、(iv) `IO.Ref` の閉じた項の構成。ログ・計測データはソースツリーに置かない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

**【S3s 注】** 本節の次の記述は §67.9 で置き換える（本文は書き換えていない）: §66.2 の「ない。`pureBuild src = M` は書けない」→「調査範囲で既存定義を未発見、新実装は可能。鍵は validator の健全性」。§66.4 の `CD`／`CDX` に関する経緯と「未確認 4 点」の状態 → §67.9 (7) の表。§66.6 M5 の「後処理後の形を受け入れる」→ §67.1（`b₀` は raw）。§66.8 の「供給の道がない」→「調査範囲で未供給」。

reviewer 裁定（(c)）: 元ソースの意味と返された IR の対応を kernel 検査できる証明／証明書を生成し、コンパイラの IO 全体を正しいと仮定しない経路の実現可能性。候補調査であり新規全面実装は不要。成功 run のモデル化が FG への最小経路かを比較する。いずれも元ソースと同一 artifact を固定し、単なる IR 型検査で代替しない。

各主張に出所の種類を付ける: **[読]** ファイルを読んだ、**[プローブ]** 今回の scratch 実行で確かめた（1 つの環境・1 つの base の値で、任意の run についての kernel の文ではない）、**[未]** 未確認／見積り。

### 66.1 未確認 1: `#machine_endpoint`（と `machine_sound`／`machine_ships_*` 生成器）は insts 付きの pilot root に適用できるか

**答え: `#machine_endpoint` は適用できる（既に適用済み）。適用できないのは、その先の生成物（`machine_closes`、`machine_ships*`、`machine_composedT*`／`machine_ships_hier`）。`#machine_linked` と `#machine_composed` は root に対して通る。**

- **[読]** `Tools/ShippingFGCircuitS1kRoot.lean:22` が `#machine_endpoint Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte` を実行している（S1k 以来、build 済み）。root は `causalProof` 系の分岐ではなく、`generateCore`（`Tools/ShippingMachineCommand.lean`）の `r.nested || !r.shape.loops.isEmpty` の分岐を通る。`nested = true`、`loops = 0`、`runs = 3`、`slots = 17`、`lets = 45`、`insts = [httpGetByte, tlpCplByte]`、`instFields = []`（[プローブ] `readMachine` の値）。
- **[プローブ]** root の名前空間の定数 21 個: `machineBody`、`machineCall_0/1`、`machineData`、`machineExt`、`machineInits`、`machineInners`、`machineResult`、`machineSource`、`machine_arg_0/1`、`machine_body`、`machine_inits`、`machine_inst_0/1`、`machine_ok`、`machine_result`、`machine_sound`、`machine_source`、`machine_states`、`machine_writes`。**無いもの**: `machine_closes`、`machine_ships`、`machine_ships_wired`、`machine_ships_comb`、`machine_composedT`、`machine_composedTRG*`、`machine_ships_hier`、`machine_design_*`。
- **[読]** `machine_ships` が出ない理由（コマンドの設計）: `Tools/ShippingMachineCommand.lean:2728` の `if r.shape.insts.isEmpty then …`（コメントは "not for a module with instances (the gates are for assign + register modules)"）。`machine_ships_wired`／`_comb` は同じ `if` の内側にあるので同様に出ない。`machine_closes` は `closeEndpoint` が `closesTheorem?`（`MachineData.letsOk` 等）で作る形で、**呼び出し（instance）があるデータには作れない**。
- **[プローブ]** scratch 環境で各コマンドを root に適用した結果:

| コマンド | 結果 | エラー本文／出所 |
|---|---|---|
| `#machine_linked` | **通る** | `Tools/ShippingMachineLinkedCommand.lean:306`。`root.machine_linked` が生成され、axiom は `propext`/`Classical.choice`/`Quot.sound` のみ |
| `#machine_composed` | **通る** | `Tools/ShippingGateChildCommand.lean:250`。`root.machine_composed` が生成、axiom は同じ |
| `#machine_closes` | 失敗 | `MachineCloses is not derived from the data (a call, a `let` that is the variable of a `let` with a driven field, or no machine endpoint)`（`Tools/ShippingMachineClosesGen.lean:119`） |
| `#machine_composedTS` | 失敗 | `…machine_sound: no wired twin for its head`（`Tools/ShippingMachineSeqCommand.lean:90`） |
| `#machine_composedTRG` | 失敗 | 同上 |
| `#machine_composedT`（mem 経路） | 失敗 | `…machine_sound is not built from machine_trace_of_loop_causal or machine_trace_of_comb_calls`（`Tools/ShippingMachineMemCommand.lean:104`） |
| `#machine_ships_hier` | 失敗 | `no wired twin for its head`（`Tools/ShippingMachineShipsHierCommand.lean` が `endpointParts` で同じ分岐に入る） |

  root の `machine_sound` の頭は `machine_trace_of_tele_ext`（チェーン endpoint）。`endpointParts`（`Tools/ShippingMachineSeqCommand.lean:71`）が wired 双子を探す頭は `machine_trace_of_loop_causal`／`_of_comb_calls`／`_of_data_causal` の 3 つで、`tele_ext` は含まれない（[読]）。

- **[読]** `root.machine_sound` の型: 前提は `mctx mref cctx cref w w' m design`、`hr : RunsTo (synthesizeCombinationalCore root [] false) … (m, design) w'`、`entry : MachineDefines …`、`closes : MachineCloses …`。結論は `MachineTraceWith`（**top の module `m` だけ**。子の出力は自由な入力 `machineExt`）。つまり endpoint は**生成されるが run を経由する**（`hr`、`entry`、`closes`）。`closes` は root では生成できない（上表）ので、閉じる文は FG 側（`MachineClosesAtHX`、`machineClosesAtH_of_gateKidsX`、`Tools/ShippingFGCircuitS2sAdmS2hHist3.lean:130`）で供給している。

**S3o §5.4 の 1 への答え**: 「`insts` 付き shape で `dataOfAt` が正しいデータを返すか」は S1k §15.1 で確認済み（`machineData` リテラルと全構造で等しい）。今回の新しい事実は、**生成が通る範囲の境界**が `machine_sound`／`machine_linked`／`machine_composed` までで、その全てが run の 11 binder（`mctx mref cctx cref w w' m design hr entry closes`）を取ること。

### 66.2 未確認 2: IR の Module（と Design）を、機械データまたはソースから組む純粋関数はあるか

**答え: ない。** `pureBuild src = M` の形の kernel 等式は、今あるものでは書けない。

- **[読]** module を作る関数は `synthesizeMachineCertified`（`Sparkle/Compiler/Elab.lean:5313`、`MetaM`）。その中身は: (1) `synthesizeMixedCertified`（2967、`MetaM`）が `mkFreshFVarId` で binder の id を作り、`IO.mkRef` で wire のキャッシュを作り、`emitLeaves`（2159）→ translator `translateExprToWire env`（8961）を `CompilerM`（MetaM の上）で走らせ、`finishSynth`（2220）で閉じる。(2) `closeLets`（`Sparkle/IR/Machine.lean:179`）と `closeMachine`（98）は**純粋**。(3) instance のある場合 `closeInstsGM`（5290、`MetaM`）が `sparkleChildSynth`（`IO.Ref`）から子の module を取り、純粋な `closeInstsG`（`Sparkle/IR/MachineInstG.lean:115`）に渡す。つまり**純粋なのは仕上げの `closeLets`／`closeMachine`／`closeInstsG` だけ**で、中核（Term から wire 文への lowering）は stateful。
- **[読]** translator `translateExprToWire` は fuel 付きの**普通の定義**（`partial` ではなく、方程式がある。8961）で、これまでの run 側の健全性証明はそれを使っている。ただし型は `CompilerM String`（`MetaM` 上）で、状態は `CircuitState` と、`Elab.lean` の 29 個の `initialize` のうち wire 名キャッシュ等のグローバル `IO.Ref`（`sparkleWireWidthCache`、`sparkleLetWireCache`、`sparkleWireCanon`、…）。translator 本体（`translateExprToWireImpl` の節）は `Elab.lean` の約 7020〜8960 行（約 1,900 行）。
- **[読]** 既存の健全性の文は module の**等式**ではなく**存在**の形: `MachinePreserves`（`Tools/ShippingMachineEntry.lean:774`）は `∃ ids cache, ∀ … ∃ regs lets, MachineWired … m dsn regs lets ∧ …`。`ids`（`FVarId` の列）と `cache`（`IO.Ref`）は**名前付けの証人**で、module `m` が何かを決める等式ではない。`MachineTraceWithB`（`Tools/ShippingMachineAuto.lean:260`）も同じ。したがって run から取れる `m` についての kernel の文は「ある ids/cache に対して `m` が trace を満たす」であり、`m = build …` ではない。
- **[プローブ]** 純粋な後処理は純粋: `dropZeroWidthModule`（`Sparkle/IR/ZeroWidth.lean:113`）、`mergeChecked`（`RefineCheck.lean:260`）、`checkedOptimize`（387）、`toVerilogDesign`（`Sparkle/Backend/Verilog.lean:499`）。つまり**raw module から出荷 Verilog までは純粋関数**で、欠けているのは「ソース／データ → raw module」だけ。
- **[プローブ]** `IO.Ref` の閉じた項は構成できる: `⟨Classical.choice ST.RefPointed.property, ⟨{}⟩⟩ : IO.Ref (Std.HashMap Nat Nat)`（axiom は標準の 3 つ）。したがって `MachinePreserves` 型の存在文の `cache` の証人を閉じた項で与えることは可能（`ExprStructMap String` でも同じ形のはず — **[未]** 今回は `HashMap Nat Nat` でだけ確認）。
- **[プローブ]** 純粋な組立関数の代わりに **artifact の値そのもの**を閉じた項にすることの規模: root の top module は 256 文・260 wire・入力 7・出力 1、子は `httpGetByte` 88 文、`tlpCplByte` 159 文、`toVerilogDesign` の出力は約 15,000 文字（Design の組み方は scratch 内の近似で、出荷物のバイト列そのものではない）。kernel で扱える大きさである可能性が高い（**[未]** 実際の kernel 検査時間は測っていない）。
- **[プローブ]** 決定性: 同じ環境で root に対し `synthesizeEntry` を 2 回、`pilotEntry3` を 1 回走らせ、3 つの出力（module 構造と Verilog 文字列）が一致した。**1 環境・1 base の値**。別の環境・別プロセス・別の `lake` ビルドでの一致は確かめていない。

足りないもの（名前を付ける）: `pureBuild : MachineData → Module × Design`（または、返された module を `MachineData` に照らして判定する純粋 checker `ModuleMatches`）と、その健全性定理。後者は translator の lowering 規則（Term → `assign`／`register`／`inst`）を純粋に再記述することになる（66.6 の部品 M1）。

### 66.3 未確認 3: 子 instance の接続 — `#machine_linked`／`#machine_composed`／`machine_linkedT` は root の 2 つの子を run の仮定なしで覆うか

**答え: 覆うが、run の仮定は外れない。** どちらも root の 2 つの子（`httpGetByte`、`tlpCplByte`）を扱う文として生成されるが、`hr`・`entry`・`closes` を取る。

- **[プローブ]** `root.machine_linked` と `root.machine_composed` の前提は同じ 11 binder（`mctx mref cctx cref w w' m design hr entry closes`）。結論は `∃ ids cache regs lets, … MachineWired … ∧ ∀ i bools bits T seed st0 mems, (seed の前提 4 つ) → (子の前提) → ∃ envs, … ∧ ∀ j k o f, outs[k]? = some o → machineSource … [k]? = some f → envs[j] o.name = f j`。つまり**連結された run**（各 instance がデザイン内で名前から引かれる module で評価される）が source の出力を示す、という文。
- **子の前提（最後の 1 つの含意）**: `∀ k args mc st, (insts の k 番目の引数 = some args) → st ∈ m.body → CallStmt … k args mc st → moduleByName design.modules mc.name = some mc → …`
  - `machine_linked`: `… → ChildFn mc (childRange child.machineData) (childValue child.machineSource child.machineData.bsIn …)`。`ChildFn`（`Tools/ShippingMachineCompose.lean`）は「module `mc` が子の source 関数を引数 port 上で計算する」という文。**子の module `mc` がその関数を計算することは仮定**。
  - `machine_composed`: 同じ位置が `k < 2 ∧ [MachineRun httpGetByte shape, MachineRun tlpCplByte shape].getD k False mc`。`MachineRun c shape mc`（`Tools/ShippingGateChild.lean:357`）は `∃ mctx mref cctx cref w w' design, RunsTo (synthesizeCombinational c) … (mc, design) w' ∧ MachineDefines … ∧ MachineCloses …`、つまり「`mc` はある run が `c` に対して返した module」。**子の run の存在を仮定する形**で、親の `hr`・`entry`・`closes` とは別の 3 組の run 前提。
- **[読]** `machine_linkedT_*`（`Tools/ShippingMachineCallsLinkedTG.lean` ほか）、`machine_linked_callsServed1`（`Tools/ShippingGen2OneOut.lean:158`）、S2jCopy の `machine_ships_hierC_runOff`／`oneOut_topShipsOff` は FG 側の root への適用で、いずれも `L : Laws`、`hr`、`hkc`（`kidsCombB` を run の closing から）、`CellPrem`（`hcell.2.2.1.1` など）から作る `MachineRunJQC` 等を取る。`machine_linked_callsServed1` は `hsimple : p.d.shape.instFields = []`（root は `instFields = []` で満たす）を要する。
- **結論**: 「接続」の kernel の文は root について**既にある**（生成物 2 つ、FG 側の連鎖）が、**どれも top の module `m` と子の module `mc` を run の出力として扱う**。子の module が artifact（`D₀.modules`）のどれと一致するかは `moduleByName design.modules mc.name = some mc` で design に結ばれ、その design も `hr` の出力。`hr` なしで同じ文を得るには、`mc` が `D₀` の具体的な module であることと `ChildFn mc …` を、純粋 checker から出す必要がある（部品 M3）。

### 66.4 未確認 4: ソース側（`CD`／`CDX`）— root で使える denotation と、「元ソースの意味 = 返された IR の意味」を述べる既存定理

**答え: 使える denotation は `CDT`（`cdvT`）で、導出は閉じている。「ソースの意味 = 返された IR の意味」を述べる定理は v11（と同形の v4）で、前提は 10 binder（`L hquiet hsynth hr hcell hD hG hT hs h0`）。**

- **[読]** 経緯: `CD`（`Tools/ShippingFGCircuit.lean:61`）には利用者定義定数と構造体射影の規則がなく、root の `CD` 導出は作れなかった（S1k §15.1）。以後 `CDX`（S1m）、`CDY`（S1p）、`CDZ`（S1r）、`CDT`（`Tools/ShippingFGCircuitS2iDT.lean`、表駆動）に拡張され、現在の最終定理が使う搬送は `cdvT`（`Tools/ShippingFGCircuitS2yFinal.lean:41`）。`hftObCDT_T`（`Tools/ShippingFGCircuitS2tHft.lean`）が root の `HftObCDT` を、環境の事実 `EnvDefs`／`EnvCtors`／`RecFact`（`Tools/ShippingFGCircuitS1mCD.lean:672`、`ShippingFGCircuitS1wTbl.lean:41`）から証明している。
- **[読]** 述語: `SourceDenotesMonoV CV env X [] sh mm := ∃ d, env.find? X = some (.defnInfo d) ∧ … ∧ CV env d.value (MonoTy sh) mm`（`Tools/ShippingFGCircuitS1tFinal.lean:41`）。**`Environment` の値 `env` と定義 `d.value`（`Expr`）についての文**で、`env` は run が読んだ環境（v11 では `envAt cref w`）。`RootArtifactMonoV` は `P X = some p ∧ SourceDenotesMonoV … ∧ ObservationsEqualMono sh mm p ∧ ∀ raw, Post b raw → ∃ n, HasConcretePackage p n X b raw D`（46 行）。
- **[読]** v11 `HftFinalStmtOffCombined11`（`Tools/ShippingFGCircuitS3kFinal.lean:37`、`synth_hftPcieOutByte_finalOffCombined11` で証明済み）の前提と結論:
  - 前提: `L : Laws mref cref`、`hquiet : L.O.quiet w`、`hsynth : sv w = some synthesizeChild`、`hr : RunsTo (pilotEntry3 hftRoot) … (b, D') w'`、`hcell : CellPrem MkRefd mref cref`、`hD : DRowEnvR`、`hG : DiagEnvR`、`hT : TeleRX`、`hs : ProfStepR`、`h0 : ProfOffW`。
  - 結論: `(∃ raw, PostRunOff … hftRoot D' b raw) ∧ ∃ mm p, RootArtifactMonoV cdvT (envAt cref w) (GPt lvl₀ (envAt cref w)) (PostRunOff …) hftRoot shHft mm b D' p`。
  - 内訳: ソース側（`SourceDenotesMonoV`、`ObservationsEqualMono`）は**環境 `envAt cref w`** にだけ依存し、`hr` は環境を決めるために入る。artifact 側（`HasConcretePackage`＝`TopShips` で `raw`／`b`／`D'` の run）が **`hr` とその全前提を要する部分**。
- **[読]** 閉じたソース側の既存定理（run なし）: `root.machine_states`（`∃ S₂ Ss, teleState … ∧ …`、前提は `i bools bits` だけ）、`root.machine_source`（宣言が body の状態ループの結果であること。`Eq.refl` を kernel が検査）、`hftRootLink : HftRootLink`（`Tools/ShippingFGCircuitS2kLink.lean:61`）。これらは**定数 `synth_hftPcieOutByte` そのもの**（kernel の環境の定数）についての文で、`Environment` の値も `CD` の導出も使わない。
- **証明書の経路への含意**: 証明書の「元ソースの意味」は、`CDT` の導出（`Expr` 上）ではなく、**生成された `machineSource`（定数 `synth_hftPcieOutByte` の意味、`Eq.refl` 検査済み）**にできる。FG の文面（`SourceDenotesMonoV` 形）と同一でないので、FG の定義にこれを数えてよいかは reviewer の判断（66.8）。

### 66.5 証明書経路が root について与える文（前提を全て名前付きで）

#### 形 (c1): オフラインの証明書（コンパイラの IO を何も仮定しない）

記号: `R := Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte`、`d := R.machineData`、`(b₀, D₀)` は 1 回の実行で得た artifact を閉じた項にしたもの（66.2: 256＋88＋159 文）、`V₀` は出荷 Verilog のバイト列のリテラル。新規の部品は `CheckRoot`（純粋 checker）と `checkRoot_sound`（その健全性）。

```
theorem checkRoot_sound :                       -- 一般定理（新規。全データ・全 module）
  ∀ (d : MachineData) (b : Module) (D : Design), d.ok = true → CheckRoot d b D = true →
    ∃ ids cache regs lets, MachineWired … b D regs lets ∧
      ∀ i bools bits T seed st0 mems, SourceInputs … → … →
        ∃ envs, runModuleT (D.modules から子を引く) b … = some envs ∧
          ∀ j k o f, d.shape.layout.outs[k]? = some o → (machineSource の出力)[k]? = some f → envs[j] o.name = f j

theorem hft_cert :                              -- root への適用（kernel の rfl／decide のみ）
  [R.machine_ok の d.ok = true]                 -- 既存（Eq.refl、kernel 検査済み）
  ∧ CheckRoot R.machineData b₀ D₀ = true        -- 新規 checker を閉じた項に適用（`decide`／`rfl`）
  ∧ toVerilogDesign (b₀ :: D₀.modules …) = V₀   -- 出荷物との突合（`rfl`）
```

結論は `checkRoot_sound` と `hft_cert` から `(b₀, D₀)` が `R` の `machineSource` を示すこと。

**前提の一覧（全て）**:

| 前提 | 必要か | 理由 |
|---|---|---|
| `hr`（`pilotEntry3`／`synthesizeCombinationalCore` の run） | **不要** | artifact は閉じた項。run は文に現れない |
| `L : Laws`、`hquiet`、`hsynth`、`hcell : CellPrem`、`hD hG hT hs h0` | **不要** | コンパイラの IO（`getEnv`、診断出力、`mkRef` 等）についての文が現れない |
| `entry : MachineDefines`、`closes : MachineCloses` | **不要** | これらは run の中身についての文。checker は `d` と `(b₀, D₀)` だけを見る |
| `d.ok = true`、`machine_body`／`machine_inits`／`machine_writes`／`machine_result`／`machine_source` | 要る（**既に生成・kernel 検査済み**） | データが source の宣言を正しく読んでいることの kernel 検査（`Eq.refl`）。`unq` は意図的に未検証で、受理の根拠は等式 |
| `CheckRoot d b₀ D₀ = true` | 要る（**新規**） | 返された module が `d` の項を実装している検査（66.6 の M1・M2） |
| `checkRoot_sound`（kernel 済みの定理） | 要る（**新規**） | checker が true なら trace が成り立つ |
| 出荷物の突合 `toVerilogDesign … = V₀` | 要る（kernel の `rfl`）。**ただし `V₀` が実際に出荷されるファイルのバイト列であることは kernel の外の運用** | artifact を固定する手段 |
| `(b₀, D₀)` が root を `pilotEntry3` に通した出力であること | **kernel の中では言えない** | 66.7 |

#### 形 (c2): コンパイラ内の checker（検査失敗なら throw）

`pilotEntry3` の末尾で `CheckRoot` を呼び、false なら例外にする。成功した run について「末尾で checker が `(b, D')` に対して true だった」ことを run の bind 分解で言う。**この形は `hr` を要する**（run の末尾の構造）。`Laws`／`CellPrem` が全体として要るかは [未]: checker が読む環境が `envAt cref w` と一致するための frame（`GetEnvFrame` 相当）が要る見込みで、それが `Laws` 全体を再び要求するかは確かめていない。(c2) は FG の文面（`compileCircuit … = .ok artifact` の全称）に近いが、63 節の阻害（`CellPrem`）を避けられる保証はない。

#### 66.5 の問いへの答え

- **`hr`、`L`、`CellPrem` は要るか**: (c1) は**要らない**（コンパイラの IO について何も仮定しない）。(c2) は `hr` と、少なくとも checker が読む環境の frame が要る（`L`・`CellPrem` の全体が要るかは [未]）。
- (c1) が代わりに要求するもの: `CheckRoot` の健全性定理（新規）と、`(b₀, D₀)` が実際に出荷される artifact であること（kernel の外）。

### 66.6 欠けている部品（具体的な部品と大きさ）— 既知と未知を分ける

**既知（測った量）**

| 項目 | 値 | 出所 |
|---|---|---|
| root artifact | top 256 文・260 wire・入力 7・出力 1、子 88 文と 159 文、Verilog 約 15,000 文字 | [プローブ] |
| translator の規模 | `Elab.lean` 全体 9,862 行、`translateExprToWireImpl` の節は約 1,900 行、グローバル `initialize` 29 | [読] |
| 既存の run 側の健全性（この step の相当部分） | `ShippingMachineEntry` 2,492、`ShippingMixedSourceBridge` 345、`ShippingScalarSoundness` 169、`ShippingMuxLoweringSoundness` 147（計 3,153 行）、`ShippingEntrySoundness` 1,823 | [読] `wc -l` |
| 既存の module→module checker とその健全性 | `RefineCheck` 424＋`ShippingRefineSoundness` 1,075、`HierCheck` 308、`ShippingMachineShipsHier` 889、`ShippingShipsHierFree` 217（**build されていない旨のコメントあり**） | [読] |
| 既存の連結・子 | `ShippingMachineCompose` 925、`ShippingMachineChild` 512、`ShippingMachineLinked` 396、`ShippingMachineComposedT` 140、`ShippingMachineTeleNest` 483 | [読] |
| source 側の閉じた部品 | `machine_states`、`machine_source`、`hftRootLink`（`S2kLink` 129 行） | [読]／[プローブ] |
| 既に動く生成 | `#machine_endpoint`（root とその 2 つの子）、`#machine_linked`、`#machine_composed` | [プローブ] |

**欠けている部品**

| # | 部品 | 内容 | 大きさ |
|---|---|---|---|
| M1 | root の top module の checker `CheckTop`（`d` の項 ↔ `b₀` の wire 文） | Term（`bits`／`bool`）から出る `assign`／`register` の形を pure に照合し、wire 名の対応（`ids`／`cache` 由来の名前）を内部で復元する translation validator | **[未]** 行数は見積れない。比較の目安は上の「run 側の健全性 3,153 行」（run の構造を使う部分と演算の意味の補題が混ざっており、後者がどれだけ再利用できるかは未確認） |
| M2 | top の `register`／`inst` 部分（`closeMachine`、`closeInstsG` の形） | `Sparkle/IR/Machine.lean`・`MachineInstG.lean` の純粋関数の形の照合。ここは純粋関数なので比較的小さい見込み | **[未]** |
| M3 | 子 2 個の module（88／159 文）が子の source 関数を計算する `ChildFn mc P F` | 子は組合せ（`slots = 0`）なので、同じ validator の組合せ版。既存の `machine_child`（`ShippingMachineChild`）は run から作る | **[未]** M1 の特殊例なら追加は小さいが、`P`（`childRange`）の値域の扱いは確かめていない |
| M4 | 連結定理（top の open trace と子の `ChildFn` から linked trace）の適用 | 既存の `machine_linked_calls`／`machine_linked_ofB`（`Compose`）をそのまま使う見込み。run の前提を外した版が要る | **[未]** 既存の定理を再利用するだけなら小さい。run なしで使えるかは未確認（`hkc` が run から来る定理がある） |
| M5 | raw → 出荷 module の後処理（`dropZeroWidth`、`mergeChecked`、`checkedOptimize`）の扱い | (c1) は**返された `b₀` を直接**検査するので後処理をモデル化せずに済む。ただし checker は**後処理後の形**（merge／register dedup 済み）を受け入れる必要がある。`refineCheck` は assign＋register module 用で、instance を含む module には `hierRefineCheck`（`HierCheck`）。root の `machine_ships_hier` の生成器は通らない（66.1） | **[未]** この点が (c1) の最大の隠れた費用になり得る: validator が最適化後の形を扱えない場合、raw を検査して `hierRefineCheck` で `b₀` に移す二段になる |
| M6 | artifact のシリアライズ（`ToExpr` 相当）と `V₀` の埋め込み | 約 500 文の `Module`／`Design` を閉じた項へ。`ToExpr` の derive があるかは未確認 | 小さい見込み（**[未]**）。kernel 検査時間は未測定 |
| M7 | 出荷物との突合 | `toVerilogDesign b₀ …` を kernel で評価し `V₀` と `rfl`。文字列 15k 字 | 小さい見込み（**[未]**） |
| M8 | FG の文としての位置づけ | (c1) の `hft_cert` は「全称の `compile = ok`」ではなく「この artifact」の文 | **[未]** reviewer の判断 |

**未知（行数を見積れないもの）**: M1 の validator の設計（実際に root が使う演算の範囲、translator の lowering の癖——`machNorm`、sign 演算、wire の再利用——を網羅できるか）、M5（最適化後の形）、M3 の値域、M4 の run なし化、kernel 検査時間。**上の既知の量はどれも (c) の総行数の見積りではない。**

### 66.7 同じ返された artifact を固定するか

- **(c1)**: **値としては固定する**（`(b₀, D₀)` と `V₀` の閉じた項。IR の型検査ではなく、`machineSource` との trace の一致）。ただし「`(b₀, D₀)` が root を `pilotEntry3` に通した出力である」という**等式は kernel の中で言えない**（66.2: 純粋な組立関数がない。コンパイラは kernel で評価できない）。その結びは運用: (i) base SHA のコンパイラで一度ダンプする、(ii) 出荷ファイルが `V₀` と一致することを突合する、(iii) コンパイラの変更で出力が変われば再生成。決定性の実測: 同環境で 3 回（`synthesizeEntry` 2、`pilotEntry3` 1）の出力が一致（[プローブ]、1 環境）。
- **(c2)**: **成功した各 run の返り値**を固定する（`hr` が `(b, D')` を決める）。ただし `hr` に `Laws`／`CellPrem` 型の前提が残るか [未]。
- 現行 (a)／(b): `hr` が `(b, D')` を決める。同一 artifact だが前提が供給できない（S3m、65 節）。

### 66.8 (a)・(b)・(c) の再比較 — この pilot（root 1 件）で FG に最短なのはどれか

| 観点 | (a) 現行 | (b) 修正版 Corr | (c1) 証明書 | (c2) checker in compiler |
|---|---|---|---|---|
| コンパイラの IO を仮定するか | `Laws`／`CellPrem` 全体 | leaf 対応仮説の集合 | **しない** | 末尾の frame のみ（範囲 [未]） |
| 供給できない前提が残るか | 残る（S3m: `ReadWorld` 全 world 等） | 残る（leaf ごとの opaque primitive） | **残らない見込み**（ただし M1 の成否に依存） | 残る可能性（frame） |
| 同一 artifact | 前提の下で yes | v12 が作れれば yes | 値として yes、compiler の出力であることは kernel の外 | yes（成功 run） |
| FG の文面に合うか | yes | yes | **no**（artifact 固定の文。reviewer の判断） | ほぼ yes |
| 既に動く部品 | v11 の鎖 | S3n／S3o の小モデル（4 leaf） | `#machine_endpoint`、`machine_states`、`hftRootLink`、`#machine_linked`／`#machine_composed`（全て root で通る） | 同左 |
| 新規に要る最大の部品 | `Laws`／`CellPrem` の供給（不可能に見える） | 2,500〜4,000 行（既知部分の外挿。未知は含まない）と v12 の再定式化 | **M1（validator）＋ M5（最適化後の形）** | M1 に加え末尾 frame |
| 費用の確度 | 高い確度で「完成しない」 | 低い（未知が多い） | **低い**（M1・M5 が未知） | 低い |

**読み（確度つき）**:

1. **(a) は最短ではない。確度: 高い。** 供給の道がない（S3m）。root の endpoint が全て run の 11 binder を取る（66.1・66.3）ので、(a) を延長しても `hr` を外せない。
2. **(b) と (c1) のどちらが短いかは決められない。確度: 低い。** S3o の読み（「(c) の可能性が高い」）は、「純粋な組立関数の有無で決まる」とした。今回その答えは**否**（66.2）。S3o §5.4 は「否なら (c) は新規実装になり、(b) より安いとは言えなくなる」としていた。したがって**この条件で S3o の暫定の読みは弱まった**: (c1) の唯一の大きな新規部品 M1（validator）は、translator の lowering を純粋に再記述する作業で、既存の run 側の健全性（3,153 行相当）と同じ桁になり得る。一方 (c1) には (b) にない利点がある: **IO の対応仮説が文に現れない**（供給不能な前提が構造上残らない）、既存の生成・連結・source 側の部品が root で通る（66.1・66.3・66.4）、artifact の規模が小さい（66.2）。
3. **(c1) の本当の隠れた費用は M5（最適化後の形）と FG の文面（M8）。** M5 は validator が merge／register dedup 済みの module を受け入れられるかで、受け入れられなければ raw の検査＋`hierRefineCheck` の二段になる。M8 は reviewer の判断で、(c1) を FG に数えないなら (c1) は FG への経路ではない。
4. **「成功 run のモデル化」（(a)／(b)）が FG への最小経路か**: **最小とは言えない。確度: 中。** (b) は IO の各 primitive について**供給できない文**を最後まで残す（65 節）。(c1) はそれを文から消すが、代わりに「validator の健全性」という**新規だが原理的に証明可能な**部品を要する。供給不能な前提が残る経路より、証明可能な部品が多い経路のほうが FG に到達できる可能性は高いが、行数は (b) より小さいとは言えない。
5. **最短の次の一手の候補（実装でなく、さらに小さい調査）**: (i) M5 の確認 — root の `b₀` が `refineCheck`／`hierRefineCheck` の正規形に入るか（`refineCheck m m` が true か）を scratch で測る、(ii) M1 の範囲の確認 — root の top module が使う `Operator` と `Stmt` の種類の集合（256 文の内訳）を数え、既存の演算の意味の補題がそれをどれだけ覆うかを数える、(iii) M8 を reviewer に確認する。この 3 つで (c1) の費用の桁が決まる。

**推奨は出さない。** 確度の言い方: 「(a) は最短でない」は高、「(c1) が (b) より短い」は低（S3o より弱い）、「(c1) は IO の仮定を文から消す」は高（構造上）、「(c1) が FG に数えられる」は reviewer の判断で未定。

### 66.9 再現のための記録

- 作業ツリーの変更は `docs/FG-CIRCUIT-PILOT.md`（本節）と `docs/FG-CIRCUIT-BOUNDARY-COMPARISON.md`（S3p 更新）だけ。プローブのファイルは作業ツリーの外（scratch）で、コミットしていない。
- プローブで確かめた事実（1 つの環境・この base）: root の定数 21 個の一覧（66.1）、各コマンドの成否とエラー本文（66.1 の表）、`root.machine_sound`／`machine_linked`／`machine_composed` の前提と結論の形（66.1・66.3）、root の shape（`nested=true loops=0 runs=3 slots=17 lets=45 instFields=0 insts=2`）、artifact の規模と決定性（66.2・66.7）、`IO.Ref` の閉じた項（66.2）。
- 確かめていないこと: 別の環境・別プロセスでの artifact の一致、`ExprStructMap String` の `IO.Ref` の閉じた項、`Module`／`Design` の `ToExpr`、kernel での検査時間、M1〜M5 の行数、`CheckRoot` が最適化後の形を受け入れられるか。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。


## 67. S3q（Issue `sparkle-fg-circuit-pilot`）: 比較資料の訂正・Check55 の表現・M5／M1 の調査・案 (c) の最小試作の設計（実装なし）

土台 `8b7953d1`（S3p）。**文書と Check55 の表現だけ**を変えた（`Sparkle/`・`Tools/` は未変更、定理の文は未変更）。コミットしない scratch ファイル（作業ツリーの外）で `kjob lake env lean` の読み取り専用プローブを走らせた（root の定数の型の読み出し、root を `pilotEntry3` に通した返却値の検査、既存の検査器の適用、演算子と文の集計）。ログ・計測データはソースツリーに置いていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

出所の種類（§66 と同じ）: **[読]** ファイルを読んだ、**[プローブ]** scratch での読み取り専用実行（1 環境・この base の値。任意の run についての kernel の文ではない）、**[未]** 未確認／見積り。

### 67.0 やったこと

1. **比較資料の訂正**（`docs/FG-CIRCUIT-BOUNDARY-COMPARISON.md`、reviewer 裁定の「資料修正」）: §4.8（受入範囲: `Toy.RelT` と実 `RelE` の差、`EnvCorrE` の残る強さ、今 TRUSTED 採用しない）、§3 の「証明も反証もできない」「道がない」を「調査範囲で未供給」へ、§5.1a（root の `machine_*` 21 定数の実際の型: ソース端点と run 付きの端点を分類）、§5.4（古い `CD`/`CDX` と現行 `CDT` の混同を除去。`hftObCDT_T` と S2z の表検査は現在の成果で、(c) で再利用するための環境対応だけが未解決）、§5.7（局所成果は受理、FG 全体・全行減算にしない）、§6（(c1)/(c2) を「完成後の見込み」と「現時点の欠け」に分離。2,500〜4,000 行は既知部分の外挿で未知を含まないことを維持）、§5.11（M5・M1 の結果）。
2. **Check55 の表現**（`Tests/Gen5/FGCircuitPilotCheck55.lean`、コミット `de43fd68`）: HYPS は禁止名の**直接参照**の検査で、任意の v11 結論を認識する閉包監査ではない旨を表示に明記。`usesRelE` の深さ 6 探索は (found, cut) を返すようにし、EnvCorrE が RelE に届くこと（正の主張）は届かなければ**失敗**、旧 EnvCorr については「深さ 6 で未検出」（探索が深さで打ち切られたかも併記）と表示し、非到達の証明とは言わない。statement は変更していない。
3. **M5・M1 の調査**（§67.1・§67.2）。
4. **(c) の最小試作の設計**（§67.3〜§67.6）。実装なし。

**§66 の記述のうち、S3q の測定で読み替えるもの**（§66 の本文は書き換えていない）: (i) §66.6 M5 の「checker は後処理後の形（merge／register dedup 済み）を受け入れる必要がある」→ **root の返却 module `b₀` は raw（merge も zero-width 除去も何も変えていない）**で、後処理後の形を受け入れる必要は返却の段階では無い（§67.1）。(ii) §66.8 の「供給の道がない（S3m）」→ **調査範囲で供給できていない**（不可能の証明ではない）。

### 67.1 M5: root の返却 module は既存の検査器に入るか（[プローブ]、[読]）

`pilotEntry3 synth_hftPcieOutByte` を 1 回走らせた値 `(b₀, D₀)` について（D₀.modules は 2 つの子で、top は D₀ に入っていない）。**詳細な表は比較資料 §5.11**。要点:

1. **`b₀` は raw そのもの**。`b₀ == raw`（`synthesizeCombinationalCoreOffR pilotReaderOk2` の出力）、`dropZeroWidthModule raw == raw`、`mergeChecked (dropZeroWidthModule raw) == raw`。`mergeDuplicates raw ≠ raw` なので merge の候補はあったが採用されていない。構造的な理由は kernel 済みの `mergeChecked_inst`（`Tools/ShippingMachineShipsHier.lean:69`: inst を含む module では `mergeChecked` は入力を返す）。**最適化（`checkedOptimize`）は返却ではなく印字（`verilogOf`）の段階**。
2. top `b₀`（256 文）: `refineCheck b₀ b₀ = false`（inst 文は `seqStmtOk` でない）、`seqGate = false`、`hierGate = true`、`hierBinds = true`、`hierRefineCheck b₀ b₀ = true`、`shipsHierCheck (childMap D₀.modules) b₀ = true`（`machine_ships_hierC` の checker 前提）。出荷形 `checkedOptimize b₀` は **89 文**で `b₀` と**異なる**（`deinline` 後の候補を `hierRefineCheck` が受理）。出荷形の `seqCheck`（`moduleWof`）は true、幅の一致も true。
3. 子（assign のみ、88／159 文）: `refineCheck m m = true`、`simpleBody = true`。`checkedOptimize m == m`（optimizer の候補は 7／18 文に縮むが不受理で入力を返す）。出荷形の `seqCheck` は true。
4. **失敗する形**: top に対する `refineCheck`／`seqGate` 系（`machine_ships`、`machine_ships_checked`、`machine_ships_wired`、`machine_ships_comb`。いずれも `insts = []` 等の前提を持ち、かつ全て run（`hr`）付きの定理。root には生成されない、§66.1）。**通る形**: `hierBinds`／`hierRefineCheck`／`shipsHierCheck`／出荷形の `seqCheck`。
5. **fallback**（reviewer: 最適化形を拒否して既証明の未最適化 artifact へ戻す安全な経路は一律に禁止しない）:
   - コンパイラの fallback は**既にある**（`mergeChecked`／`checkedOptimize` は検査失敗で入力 module を返し、throw しない）。root の merge は実際にこの fallback で入力に戻っている。
   - (c) が検査する `b₀` は未最適化の raw なので、IR レベルでは戻り先と `b₀` が同じ値。**追加の fallback 実装は要らない**。ただし**「既証明」の未最適化 artifact は root の top に現時点で存在しない**（既存の証明は全て run 付き。M1 が無いと `b₀` の意味保存は証明できない）。
   - root だけ最適化せずに `b₀` を印字する fallback は**小さい**（`checkedOptimize b₀` → `b₀` の分岐 1 つ）が、**出力の SV は今日と異なる**（top が 89 → 256 文。子は同じ）。**IP のベースライン（出力テキスト比較）は変わる**（意味は同じでも文字列は同じでない）。全 module に及ぼすと全 IP の出力が変わるので、使うなら対象を限定する。
   - 出荷形（89 文）まで kernel で覆う場合の既存部品: `hierRefineCheck_linkedH`（`Tools/ShippingHierOptRunH.lean:412`、`b₀` → 出荷形の移送。設計側の前提 `linkedWF`・`kidsLocal`・`hOutM` 等を要する）、SV 側は `hier_pipeline_transfer`（`Tools/ShippingHierSVSoundness.lean:494`。前提 `hcomb : o.body.all combStmtI = true`）。**【S3s 確定】** `combStmtI`（`Tools/ShippingHierSVSoundness.lean:404`）は `assign` と `inst` だけ `true`、`register` を含む他の文は `false` である [読]。top は register 17 を含むので、**17 register の top に `hier_pipeline_transfer` を直接適用することは範囲外**（旧文の「未確認」はこの確定で置き換える。§67.9）。

### 67.2 M1: root の module の演算子・文の形と、既存の checker／補題の被覆（[プローブ]、[読]）

**文**（top 256）: `assign` 237、`register` 17（全て clock `clk`、同期 reset `rst`、初期値 0）、`inst` 2。**子**: `httpGetByte` 88 文 = assign 88、`tlpCplByte` 159 文 = assign 159。`memory`・assertion・parameter は無い。**式**（全て 2 引数の `concat`、3 引数の `mux`、2 引数の二項演算、非負の `const`）:

| 形 | top (256) | 子 88 | 子 159 |
|---|---|---|---|
| `ref` | 426 | 122 | 255 |
| `slice` | 66 | 13 | 51 |
| `concat`（2 引数） | 64 | 12 | 42 |
| `mux`（3 引数） | 42 | 17 | 30 |
| `eq` | 19 | 17 | 15 |
| `and` | 10 | 0 | 0 |
| `or` | 6 | 0 | 0 |
| `add` | 3 | 0 | 0 |
| `shl` | 2 | 0 | 0 |
| `const` | 25 | 29 | 21 |

出荷形の top（89 文: assign 70、register 17、inst 2）も同じ演算子の集合（`mux` 23、`and` 49、`const` 64、`concat` 2、…）。**root 全体の演算子は `mux`・`eq`・`and`・`or`・`add`・`shl` の 6 種**。`sub`・`mul`・`xor`・`not`・`neg`・`lt`/`le`/`gt`/`ge`（`_u`/`_s`）・`shr`・`asr`・`sliceDim`・`index` は無い。

**被覆**（純粋 checker／kernel 済みの補題が、これらの形を覆うか）:

| 形 | IR の評価意味（`Semantics.evalOp`／`evalExpr`）[読] | IR→IR の純粋 checker: `refineCheck` の正規形 `rNormE`（健全性 `refineCheck_transfer`）[読] | IR→SV の検査 `seqCheck`（`sf4Check`）[プローブ: 3 module とも true] | run 側の lowering の補題（Term → 文）[読／名前検索] |
|---|---|---|---|---|
| `const`・`ref` | あり | あり（`0 ≤ v < 2^w`、`ref` は定義の展開） | あり | — |
| `mux` | あり | `rMux` | `sf4Check` の `mux` の枝 | `emitMuxResult_correct`（`Tools/ShippingMuxLoweringSoundness.lean`） |
| `and`・`or`・`add`・`shl` | あり | `rBinOk` に含まれる（`rBin`） | `sf4Check` の二項の枝（`and`/`or` は `perOp`、`shl` は shl の経路） | `Binary.emit_correct`（`Tools/ShippingScalarSoundness.lean`: `add sub mul and or xor shr shl`） |
| `eq` | あり | `rBinOk` に含まれる | 二項の枝 | 比較の補題 `Tools/ShippingCompareLoweringSoundness.lean`（`eq` がその種別に当たるかは**名前でしか確かめていない [未]**） |
| `slice` | あり | `rSlice` | 通る（プローブ） | 名前検索では**見つからない [未]** |
| `concat`（2 引数） | あり | あり（`concat [a, b]` のみ） | 通る（プローブ） | 名前検索では**見つからない [未]** |
| `register` 17（同期 reset、init 0） | `runModule` | `refineCheck` は register を扱うが、**top には inst があるので top の `refineCheck` は false**（top は `hierRefineCheck` で検査） | あり | — |
| `inst` 2 | `runModuleH`（子の呼び出し） | `hierRefineCheck`（開いた module に取り出して `refineCheck`） | `seqCheck` は inst 文に条件を置かない | — |

**読み**: (i) **IR→IR と IR→SV の既存の純粋 checker は、root の演算子の集合を全て覆う**。ただし **`refineCheck` が true なのは子 2 module だけで、top では false**（inst 文が `seqStmtOk` でない。§67.1 の 2）。top は階層検査（`hierRefineCheck`／`shipsHierCheck`、いずれも true）で検査される。`seqCheck`（出荷形）は 3 module とも true。**【S3s 訂正】** 旧文の「`refineCheck` と `seqCheck` の両方が 3 module で true」は top の `refineCheck` false と矛盾していたので、この文に置き換える。なお、これらの true は**測定値**であり、意味保存の移送ではない（§67.9）。(ii) **覆われないのは M1 そのもの**: 「`MachineData`（ソース宣言から読んだ項）から module の文への対応」を判定する純粋 checker は既存に無い。run 側の lowering の補題は `mux`・`add`/`and`/`or`/`shl`（と、未確認だが比較）にはあるが、`slice`・`concat` の補題は名前検索で見つからず、いずれも run 側の補題であって純粋 checker の健全性としては使えない。(iii) したがって M1 の演算子ごとの新規の対応規則は、**6 種の二項／三項演算と `slice`・`concat`（2 引数）・`const`・`ref`・`register`・`inst` の 12 程度の形**に限られ、既存の「全演算子」の網羅は要らない（**ただし行数は見積らない**: 規模の目安は §66.6 の 3,153 行のまま）。

### 67.3 案 (c) の最小試作（設計のみ）: この root についての完全な文

**記号**: `R := Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte`（名前 `` `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte ``）。`d := R.machineData : MachineData`。子 `K₀ := Sparkle.IP.Net.HTTP.httpGetByte`、`K₁ := Sparkle.IP.Bus.PCIe.tlpCplByte`（それぞれ `machineData`・`machineSource` を持つ）。

**ソース宣言と値**（既存、kernel 検査済み、run を含まない — 比較資料 §5.1a）: 宣言 `R rxByte rxValid sopTlp dataDword cplId := (hftPcieLoop …).outByte`（`Signal defaultDomain (BitVec 8)`）。値は `R.machineSource : Unit → (Nat → Signal Bool) → (Nat → (n : Nat) → Signal (BitVec n)) → List (Nat → Nat)`。`R.machine_ok : d.ok = true`、`R.machine_source : machineSource i bools bits = machineResult i (resOn (fusedBody …))`（`Eq.refl`）、`R.machine_states : ∀ i bools bits, ∃ S₂ Ss, teleState … ∧ …`。

**返される Module・Design（子接続を含む）**: 1 回の実行（`pilotEntry3 R`）が返した値を閉じた項にした `b₀ : Module`（256 文）、`D₀ : Design`（`D₀.modules` = [子 `K₀` の module（88 文）、子 `K₁` の module（159 文）]）。生成器は**信頼しない**（kernel が受理した文だけが根拠）。

**保存される意味**（IR の意味。run なし。`R.machine_composed`／`machine_linked` の結論の形を土台にし、子の前提を**仮説でなく結論側**に移す）:

```lean
/-- (新規) 返された (b, D) が R の源の意味を持つ。子接続を含む。
    ids / cache / regs / lets は名付けの証人（存在量化）。 -/
def RootShows (b : Module) (D : Design) : Prop :=
  ∃ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs lets : List String),
    ids.Nodup ∧ ids.length = d.shape.binders.length ∧ regs.Nodup ∧ regs.length = d.ss.length ∧
    lets.length = d.letBs.length ∧
    MachineWired R d.shape ids cache b D regs lets ∧
    -- 子接続（【S3s 改訂】下の「裁定2 の反映」を満たす形。S3q の初版は含意だけで、検索失敗で空虚になり得た）
    (∀ k, k < 2 → ∃ args mc st,
        (d.shape.insts.map (·.2.1))[k]? = some args ∧ st ∈ b.body ∧
        CallStmt (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
          ((machPorts R ids cache d.shape.binders).map (·.name)) k args mc st ∧
        moduleByName D.modules mc.name = some mc ∧
        ChildFn mc (childRange (kid k).machineData) (childValue (kid k).machineSource (kid k).machineData.bsIn defaultDomain)) ∧
    (∀ st ∈ b.body, IsInst st → ∃ k, k < 2 ∧ ∃ args mc, CallStmt … k args mc st) ∧   -- 全 inst の被覆
    -- kid 0 = K₀（httpGetByte）、kid 1 = K₁（tlpCplByte）。順序固定。getD の既定値 (fun _ => True)／(fun _ => 0) は使わない
    -- 親の連結された run が源の出力を示す
    ∀ (i : Unit) bools bits (T : Nat) seed st0 mems,
      (seed の 4 前提: SourceInputs … / seed t st r = st r (r ∈ regs) / seed t st "rst" = 0 / st0 r = f.init) →
      ∃ envs, runModuleH (weOf b) (childMap D.modules) b.body seed T st0 mems = some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) k o f,
          d.shape.layout.outs[k]? = some o → (R.machineSource i bools bits)[k]? = some f →
          envs[j] o.name = f j
```

（`machine_composed` と異なる点: 子の `MachineRun`（子の run の存在）という**仮説**を、`ChildFn`（子 module が子の源の関数を計算するという IR の文）の**結論側の conjunct**にした。`machine_linked` の子の前提と同じ文を、仮説から結論へ移した形。上のコードは `R.machine_composed` の型（[プローブ]）から書き写した設計で、**まだ Lean で型検査していない [未]**。特に seed の 4 前提の正確な形・`ChildFn` の引数は、実装時に `machine_linked` の型に合わせる。）

**【S3s: reviewer 裁定2 の反映】** ChildFn を結論の連言にする設計は可。ただし**単なる含意（「見つかれば ChildFn」）は、検索が失敗すると空虚に成り立つ**ので、次を `RootShowsAt` に保持する（上のコードの修正点）:

1. **全 call・全 inst の被覆と `moduleByName` の接続**。(i) 全ての呼び出し `k < 2` について、引数・文 `st ∈ b.body`・`CallStmt`・`moduleByName D.modules mc.name = some mc` を満たす `mc` が**存在する**（存在を結論に入れる）。(ii) `b.body` の全ての `inst` 文が、ある `k < 2` の `CallStmt` に対応する（余分な inst が無い）。(iii) そのうえで `ChildFn mc …`。`MachineWired` の `d.shape.insts` との長さ一致（`= 2`）も結論側に持つ。
2. **この root の `instFields = []`**（[プローブ]：`readMachine` の値）。これは `machine_linked_callsServed1` の `hsimple : p.d.shape.instFields = []`（§66.3）と同じ前提で、`CheckRoot` が検査する条件（`S.d.shape.instFields = []`）に入れる。**一般の `SourceData` にはこの制限を明示する**: `checkRoot_sound` は `instFields = []` の `SourceData` についての定理であり、`instFields ≠ []` の場合は**被覆を証明していない**（証明するか、`CheckRoot` が `false` を返す）。
3. **2 つの子の範囲・順序・入力幅の固定**: `kid 0 = K₀ = httpGetByte`、`kid 1 = K₁ = tlpCplByte`（順序固定）。`childRange`／`childValue` は `kid k` の `machineData`（`bsIn` の入力幅）から取り、**`getD` の既定値（`fun _ => True`／`fun _ => 0`）に逃げない**。`k < 2` の外は結論に現れない。各子の入力幅は freeze 時に `machineData.bsIn` から固定して書く（本節では値を書かない [未]。`tlpCplByte` は入力 6 ポート、§67.5）。
4. **seed／初期値／reset = 0 の正確な前提**: `RootShowsAt` の run 部分の前件は、次の 4 つを**そのまま**述べる（`machine_linked` の型に合わせて確定）: (a) `SourceInputs`（入力 `bools`／`bits` が `seed` の入力 port に現れる）、(b) `∀ t st, ∀ r ∈ regs, seed t st r = st r`（register の値は state から）、(c) `∀ t st, seed t st "rst" = 0`（reset は常に 0）、(d) `∀ r, st0 r = f.init`（初期値が宣言の init）。**この 4 つが同時に満たされる具体例を freeze に載せる**（前件が充足不能だと文が空虚になるため。具体例は `st0`・`seed` の定義と、4 つの成立の kernel 検査）。**[未]**：今回は書いていない。
5. **`SourceData.srcEq` に IR の正しさを入れない**。`srcEq` は「元の `R` の値」と `machineSource` の接続だけを述べる: `R.machine_source`（`machineSource` = 状態ループの結果）、`R.machine_states`（`∃ S₂ Ss, teleState …`）、`hftRootLink`（`CDT` の観測と `machineData` の出力の対応、§67.5）。`b`／`D` についての主張（`MachineWired`、`ChildFn`、`runModuleH` の結果）は `srcEq` に入れず、`CheckRoot = true` からの結論 `RootShowsAt` に限る。入れると、`checkRoot_sound` の仮説が結論を含み循環する。

**この root への主張（kernel の閉じた項だけ。`hr`・`L`・`CellPrem`・`entry`・`closes` を含まない）**:

```lean
theorem hft_cert : RootShows b₀ D₀ :=
  checkRoot_sound R.machineData [K₀.machineData, K₁.machineData] R.machine_ok … b₀ D₀ cert₀ (by decide)
-- cert₀ : 閉じた証明書の項（untrusted generator の出力）。`by decide` は CheckRoot … = true の kernel 評価
```

**検査器 `CheckRoot` が取るもの**: ソース束 `S`（`declName`・`MachineData`・各子の `MachineData`・`machineSource` の等式 `machine_source` を満たすこと）、返された `b : Module`、`D : Design`、**証明書 `cert`**（信頼しないヒント: `ids`・`regs`・`lets` の名前、top の各 wire 文がソースの項のどの節点に当たるかの対応表、子の module と呼び出しの対応）。`CheckRoot : SourceData → Module → Design → Cert → Bool`（純粋）。

**健全性の文の形**（一般。root 固定ではない）:

```lean
theorem checkRoot_sound :
  ∀ (S : SourceData) (b : Module) (D : Design) (cert : Cert),
    S.ok = true →               -- machine_ok 等（Bool、既存の検査）
    S.srcEq →                   -- machine_source の等式（Prop、既存の kernel 済み定理から供給）
    CheckRoot S b D cert = true →
    RootShowsAt S b D           -- RootShows の S についての一般化
```

証明生成器・`cert` の作り方の正しさは仮定しない（任意の `cert` について成り立つ）。根拠は「生成された `cert₀` で `CheckRoot … = true` が kernel に受理された」こと。

**「検査した同じ artifact だけを返す」接続**（採用入口。(c1) の offline では不要で、(c2) として後続）: 

```lean
def certifiedReturn (declName : Name) (S : SourceData) : MetaM (Module × Design) := do
  let (b, D) ← pilotEntry3 declName          -- 既存の入口（run のまま）
  let cert ← buildCert S b D                 -- untrusted（純粋、または MetaM）
  unless CheckRoot S b D cert do throwError "certificate check failed"   -- 検査失敗は拒否（成功扱いにしない）
  pure (b, D)                                -- 検査したその (b, D) だけを返す

theorem certifiedReturn_sound :
  RunsTo (certifiedReturn declName S) mctx mref cctx cref w (b, D) w' →
  ∃ cert, CheckRoot S b D cert = true       -- RunsTo.bind／ite／pure の分解のみ（checker は純粋で world に依存しない）
```

`S` は閉じた束（S2z の `pin_*` と同じ流儀: 生成した行を `decide +kernel` で固定）で、**run 時の env から読まない**。そのため末尾の `getEnv` の frame（`Laws`/`CellPrem` 相当）は要らない。「`S` が利用者の環境の宣言 `R` と同じものか」の対応は別に残る（§67.5 の未解決）。

**【S3s 訂正・reviewer 裁定】fallback について**: S3q の初版は「拒否の代わりに `pure (b, D)` を残す変形として足せる」と書いたが、**これは不可**。`CheckRoot S b D cert` が false だった**同じ artifact `(b, D)`** をそのまま返すと、`certifiedReturn_sound`（返された `(b, D)` は検査に通った）が破れる。許される形は次の 2 つだけ:
- (1) **拒否**（上のスケッチのとおり `throwError`。成功として返さない）。
- (2) **同じ `S` について別に証明済みの fallback artifact `(b', D')` を返す**。その分岐も `certifiedReturn_sound` の結論に含める（結論を `CheckRoot S b D cert = true`（検査通過の枝）**または** `FallbackProved S b' D'`（fallback の枝。`(b', D')` が `S` について別途証明済み）の選言にし、各枝を証明する）。`FallbackProved` を満たす `(b', D')` が実際に存在することの証明が要る。
現在のコードには fallback は**未実装**（スケッチは (1) のみ）で、S3r の作業を止めない。root では「既証明の未最適化 artifact」は存在しない（§67.1 の 5）ので、(2) は現時点では空の選択肢である。

**FG の文との差**（reviewer: 対象/前件が変わるなら新旧の差と消費者を示して正式に変更）:

| | 現行 FG（v11 `HftFinalStmtOffCombined11`） | (c1) の最小試作 |
|---|---|---|
| 対象 | `pilotEntry3 hftRoot` の**成功 run が返す任意の** `(b, D')` | **1 つの具体的な閉じた** `(b₀, D₀)` |
| 前件 | 10 binder（`L hquiet hsynth hr hcell hD hG hT hs h0`） | なし（`S.ok`・`S.srcEq`・`CheckRoot = true` は全て kernel 検査済みの閉じた事実） |
| 元ソースの意味 | `SourceDenotesMonoV cdvT (envAt cref w) …`（`Environment` 値と `CDT` の導出） | `R.machineSource`（kernel の定数の意味。`Eq.refl` 検査済み） |
| artifact 側 | `HasConcretePackage`（run `hr` 経由） | `RootShows b₀ D₀`（IR の run なし） |
| 消費者 | v11 の結論を使う後続（`RootArtifactMonoV`） | 新しい `hft_cert`。現行 FG の消費者には**そのままは渡せない**（対象が「任意の成功 run」から「この artifact」に変わる）。FG 全体・全行減算にしない（reviewer 裁定） |

### 67.4 IR の証明・SV 文字列の一致・SV の意味保存の区別

| 層 | 主張 | 試作の範囲 | 根拠 |
|---|---|---|---|
| **IR の意味保存** | `RootShows b₀ D₀`（IR の `runModuleH` が源の出力を示す） | **含む**（`checkRoot_sound` の結論） | `CheckRoot = true` の kernel 評価＋健全性 |
| **SV 文字列の一致** | `toVerilogDesign … (checkedOptimize b₀) … = V₀`（出荷物のバイト列のリテラル） | 任意（artifact を固定する手段）。**意味保存とは呼ばない** | `rfl`／`decide`。ハッシュ一致だけでは kernel 内の意味保存と呼ばない |
| **SV の意味保存** | 出荷 SV を構文解析した意味が IR の意味と一致する | **含まない**（後続）。`combStmtI`（`Tools/ShippingHierSVSoundness.lean:404`）は assign／inst だけ true で register は false なので、**register 17 を含む top に既存の `hier_pipeline_transfer` を直接適用することは範囲外**（S3s で確定。§67.9） | 既存の `seqCheck`・`semFragCheck`・`hierRefineCheck` が root で true であることは**測定値**であって、意味保存の証明ではない |

さらに、**出荷形と返却形が違う**（§67.1: top は 256 文 → 89 文）ので、IR の意味保存は「返却形 `b₀`」について証明し、出荷形への移送は `hierRefineCheck`＋`hierRefineCheck_linkedH` を使う別の段になる。

### 67.5 再利用するものと新規のもの（大きさは分かっているものだけ）

| 部品 | 再利用／新規 | 内容・用途 | 大きさ |
|---|---|---|---|
| `R.machineData`・`machine_ok`・`machine_source`・`machine_states`・`machine_arg_*`・`machine_inst_*` | 再利用 | ソース宣言と値、run なし | 生成済み（kernel 済み）。1 宣言の検査 0.1〜1.5 秒（`Coverage.md` の測定、別の宣言） |
| `hftRootLink`（`Tools/ShippingFGCircuitS2kLink.lean`） | 再利用（FG の `RootArtifactMonoV` 形の文にしたい場合） | `CDT` の観測と `machineData` の出力の対応 | 129 行 |
| `hftObCDT_T`（S2t）＋ S2z の表検査（`hftEnvCheckB_sound`、`pin_*`、`startEnvOk_sound`） | 再利用（**`env` の値についての文**） | `HftObCDT env` を同じ `env` の表検査から供給 | S2tHftOb 16、S2zEnvCheck 73、S2zPin 35、`EnvTableCheck` 80、`PilotEnvTables` 1,328（生成） |
| S3a／S3b2 の検査（`dataOfAt` 検査を引数で渡す入口、`coreR_chain`） | 再利用（採用入口の接続 (c2) の部品） | run 側の env の読みの鎖 | S3b2Core 137、S3aFinal 93、S3f2Final 159 |
| `pilotEntry3`（検査付き入口） | 再利用 | 返却する (b, D') を作る | S3jStart 140 |
| `shipsHierCheck`・`hierRefineCheck`・`hierRefineCheck_linkedH`・`refineCheck_transfer`・`seqCheck` | 再利用（出荷形の移送・SV の検査） | 全て root で true（測定） | 既存 |
| `MachineWired`・`ChildFn`・`childRange`・`childValue`・`runModuleH`・`childMap` | 再利用（文の語彙） | `RootShows` の部品 | 既存 |
| **`CheckRoot` と `checkRoot_sound`（M1・M2）** | **新規** | 返された module を `MachineData` に照らす translation validator と健全性 | **行数の見積りなし**（目安: 既存の run 側 3,153 行。覆う形は §67.2 の 12 程度） |
| 子の検査（M3: `ChildFn mc P F`）と連結（M4） | **新規** | 子 2 つの module が子の源の関数を計算する。`ChildFn` は全環境への量化（`P` の範囲）なので、**列挙では閉じない**（`tlpCplByte` は入力 6 ポート）。M1 の組合せ版として検査する | 見積りなし |
| `ToExpr`（`Module`／`Design`）、artifact の閉じた項の生成器（M6） | **新規** | `Module`・`Design` は `deriving Repr, BEq, DecidableEq` のみ（`ToExpr` 無し）。`Expr` は入れ子の帰納型（`List Expr`）で自動導出の可否は**未確認 [未]** | 見積りなし（artifact 自体は 256＋88＋159 文） |
| `MachineWired` の名付けの証人（`ids : List FVarId`、`cache : IO.Ref`、`Allocated`） | **新規（検査可能性が未確認）** | `machPorts` は `start (entryCompilerState false cache) …` を**純粋に**評価するので `cache` は閉じた項でよい（§66.2 の `IO.Ref` の閉じた項）。ただし `NameHints.Allocated x`（命題）の判定が**決定可能かは未確認 [未]** | 見積りなし |
| 出荷物の突合（M7） | 新規・任意 | `V₀` のリテラルと `rfl`。意味保存とは別（§67.4） | 約 15,000 文字（近似） |
| `env` の値と kernel の定数 `R` の対応（源環境・宣言の固定） | **未解決** | `dataOfAt env R` が固定した `S` と一致することの検査（S2z の `pin_*` の流儀）と、その健全性 | 見積りなし |

### 67.6 最初の実装ステップ（1 単位で足りる大きさ）: 「artifact の閉じた項化と、既存の純粋検査の kernel 評価」

新しい checker は**書かない**。M6（artifact の固定）と、「既存の検査が閉じた項の上で kernel で評価できるか・何秒か」を先に決める。

1. **生成器（untrusted）**: `pilotEntry3 R` を 1 回走らせた `(b, D)` から、`b₀ : Module`・`D₀ : Design`（閉じた項）を定義として追加するコマンド。`Module`／`Design` の `ToExpr`（手書き、`Stmt`・`Expr`（入れ子）・`Port`・`Type`・`DimExpr`）を含む。生成した項が**同じ run の値と `==` であること**を、生成時に実行して確認し、食い違えばビルドを失敗させる（artifact の固定の運用上の根拠。kernel の外）。
2. **kernel で評価する既存の検査**（全て [プローブ] で true だったもの）: `hierBinds b₀`、`hierRefineCheck b₀ (deinline b₀ (optimizeModule b₀))`、`shipsHierCheck (childMap D₀.modules) b₀`、`refineCheck K m m`（子 2 つ）、`mergeChecked b₀ = b₀`、`dropZeroWidthModule b₀ = b₀`、出荷形の `seqCheck`。`decide`／`rfl`／`decide +kernel` のどれで通るか、**kernel の評価時間と閉じた項の大きさ**を記録（ログはソースツリーに置かず、結果を文書にだけ書く）。
3. **出力**: 通った検査の一覧と、通らなかったものの理由（`ToExpr` の導出不能、kernel の時間切れ、`decide` の深さ等）。**受入は「閉じた項が作れて、既存の検査の kernel 評価が通る（または通らない理由が分かる）」こと**。`CheckRoot` と `checkRoot_sound` は次の単位。

この 1 単位が答えるもの: M6（`ToExpr`）と kernel の時間・規模、M5 の出荷形の kernel 評価。答えないもの: M1（`CheckRoot`）、M3・M4、SV の意味保存、`env` の対応。

### 67.7 Check55 の表示（コミット `de43fd68` を build した出力。`kjob lake build Tests.Gen5.FGCircuitPilotCheck55`、1071 job、成功）

- `FGCIRCUIT55 HYPS: 9 corrected definitions (RelE, CorrE, GetCorrE, SetCorrE, StderrCorrE, EnvCorrE, InitCorrE, quietRE, GCorr) are plain definitions (no axiom); a DIRECT-REFERENCE check (the constants of each definition's type and value; NOT a closure audit, it does not recognize an arbitrary v11 conclusion): none directly references the 14 listed forbidden constants (the programs realProg/modelProg/realEnvProg/modelEnvProg/prog, pilotEntry3, Laws, CellPrem, rootDefB_sound, the old Rel/Corr/EnvCorr/quietR/InitCorr); within a depth-6 search EnvCorrE reaches RelE (the oracle); within the same depth-6 search the old EnvCorr was NOT found to reach RelE (search cut by the depth bound: true; this is not a proof of non-reachability)`
- 他の行（SIGNATURES 15 定理・39 変異体、REFUTE、CONTROL、BIND、SIMULTANEOUS、AXIOMS 36 名・標準 axiom のみ）は変更なし。**旧 EnvCorr の探索は深さ 6 で打ち切られた（cut = true）**ので、以前の「旧 EnvCorr は RelE に届かない」という表示は非到達の証明ではなかった。

### 67.8 まだ確かめていないこと

別の環境・別プロセスでの artifact の一致（決定性は 1 環境の測定）、`Module`／`Design` の `ToExpr` の導出可否、kernel での検査時間と閉じた項の大きさ、`NameHints.Allocated` の決定可能性、`combStmtI` が register を含むか、`slice`・`concat`・`eq` の lowering の補題の有無（名前検索のみ）、`RootShows` の Lean での型検査、M1〜M4 の行数。**この節の `RootShows`・`CheckRoot`・`checkRoot_sound`・`certifiedReturn` は設計であって、Lean に書いていない。**（`combStmtI` が register を含むか、は S3s で確定: 含まない。§67.9。）

### 67.9 S3s（reviewer 裁定の反映。文書のみ）

土台 `28dd20ff`。`Sparkle/`・`Tools/`・`Tests/` は未変更。§68 は S3r が書く（ここでは足さない）。

**(1) 3 段の分離**。次の 3 段は別の義務で、ある段の Check が true という**測定**だけで次の段へ「移送済み」としない。

| 段 | 対象 | 義務 | 現状 |
|---|---|---|---|
| ① IR 返却形 | `pilotEntry3` が返す raw `b₀`（top 256 文、子 88／159 文）の意味 | `RootShowsAt`（`CheckRoot` の健全性） | 設計のみ。未実装 |
| ② 最適化形 | 出荷形 `checkedOptimize b₀`（top 89 文）と `b₀` の対応 | `hierRefineCheck_linkedH` 等（設計側の前提 `linkedWF`・`kidsLocal`・`hOutM` を要する） | `hierRefineCheck` 等は true と**測定**しただけ。移送は未適用 |
| ③ SV 意味 | 出荷 SV の意味と IR の意味 | `hier_pipeline_transfer` 等 | 下記のとおり top には直接適用できない |

**確定した事実 [読]**: `combStmtI`（`Tools/ShippingHierSVSoundness.lean:404`）は `.assign` と `.inst` だけ `true`、それ以外（`register` を含む）は `false`。`hier_pipeline_transfer` の前提 `o.body.all combStmtI = true` は、register 17 を持つ root の top（返却形 256 文も出荷形 89 文も）では成立しない。したがって **17 register の top への `hier_pipeline_transfer` の直接適用は範囲外**。S3q の「未確認」はこの事実で置き換える。③ を root について得るには、register を扱う別の経路（新規）が要る [未]。

**(2) §67.2 の矛盾の修正**。「`refineCheck` が 3 module で true」は誤り。top の `refineCheck` は **false**、子 2 つは true。top は階層検査（`hierBinds`／`hierRefineCheck`／`shipsHierCheck`）で検査される（§67.1 の 2、§67.2 の読み (i)）。

**(3) fallback の訂正**。§67.3 の「拒否の代わりに `pure (b, D)` を残す」は不可（`certifiedReturn_sound` が破れる）。許されるのは拒否、または同じ `S` について別に証明済みの fallback artifact を返し、その枝も `certifiedReturn_sound` に含める形。現行コードに未実装なので S3r を止めない。

**(4) 裁定2 の反映**: §67.3 の「S3s: reviewer 裁定2 の反映」（被覆、`instFields = []`、一般 `SourceData` の制限、2 子の固定、seed 前提とその同時充足、`srcEq` の範囲）。

**(5) 純粋 builder について**: §66.2 の「ない。`pureBuild` は書けない」は、**「調査範囲では既存の定義を発見していない。新実装は可能」**に読み替える。(c) の鍵は純粋 builder ではなく、**validator（`CheckRoot`）の健全性**: `checkRoot_sound` を任意の `S`・`b`・`D`・`cert` について証明する。生成器（untrusted）は任意でよい。

**(6) `hftObCDT_T` は run-free だが無条件ではない**。`hftObCDT_T (env) (hΔ : EnvDefs env Δ) (hΓ : EnvCtors env Γ) (hrec : RecFact env) : HftObCDT env`（`Tools/ShippingFGCircuitS2tHftOb.lean:10`）。前提:
- `EnvDefs env Δ`: `Δ c = some r` の各 `c` について、`env.find? c = some (.defnInfo d)` かつ `d.levelParams = r.lps` かつ `d.value = r.value`（`Tools/ShippingFGCircuitS1mCD.lean:672`）。
- `EnvCtors env Γ`: `Γ c = some r` の各 `c` について、`env.find? c = some (.ctorInfo cv)` かつ `cv.induct`・`cv.numParams`・`cv.numFields` が `r` と一致（同 681）。
- `RecFact env`: `∃ ri, env.find? ``List.rec = some (.recInfo ri)`（`Tools/ShippingFGCircuitS1wTbl.lean:41`）。
**実 env との対応**: これらは `Lean.Environment` の値 `env` についての文で、run-free（`hr` を含まない）が、`env` が（run が読んだ）実際の環境であり、表 `Δ`／`Γ` の行がその環境の宣言と一致することを**別に**供給する必要がある。S2z の `hftEnvCheckB`／`startEnvOk_sound` が、決定可能検査 `startEnvOk hftRoot env = true` から**同じ `env`** についてこの 3 条件を与える（kernel 済み）が、検査対象の `env` が kernel の定数 `R` の環境と同じであること（源環境・宣言の固定）は (c) では未解決のまま（§67.5）。

**(7) 歴史的な「未確認 4 点」・旧 CD／CDX の結論の上書き**。§66 の「未確認 4 点」（§66.1〜§66.4）と S3o の原文は歴史的記録で、現在の要約は次のとおり。superseded を明記する:
| 点 | 旧い記述 | 現在の要約 |
|---|---|---|
| 1 `#machine_endpoint` | 未確認 | root に適用済み・通る。生成物は `machine_sound` まで run 付き（§66.1） |
| 2 純粋な組立関数 | 「ない。`pureBuild` は書けない」（§66.2） | **調査範囲で既存定義を未発見。新実装は可能**（上の (5)）。鍵は validator の健全性 |
| 3 子の接続 | 未確認 | 既存は run 付き。run なしの文は `RootShowsAt` の ChildFn 連言として新規に要る（(4)） |
| 4 ソース側 `CD`／`CDX` | 「`CD` に規則が無く導出は作れない」「`hcd` 未完了」 | **superseded**: 現行は `CDT`（`cdvT`）。`hftObCDT_T` で導出は閉じている。ただし無条件でなく (6) の前提つき |

**(8) 方針**: この文書は比較を示すもので、(a)／(b) の TRUSTED 採用を今求めるものではない。(c) の最小実験（S3r、続いて M1）は委任範囲で継続し、既知の費用を得てから、必要な保証変更・新 TRUSTED だけを具体的に判断に出す。E1 全面移植は保留、新 TRUSTED は未承認。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 68. S3r（Issue `sparkle-fg-circuit-pilot`）: 案 (c) の第 1 段 — 返却 artifact `(b₀, D₀)` を閉じた項にし、既存の純粋検査を kernel で評価する

土台 `28dd20ff`（S3q）。新しい checker は書いていない。`Sparkle/` は未変更、既存の定理の文も未変更。追加は `Tools/ShippingFGCircuitS3r{Gen,Artifact,Kernel,Obs}.lean` と `Tests/Gen5/FGCircuitPilotCheck56.lean`（lakefile に各 `lean_lib`）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。**1 artifact の証明書は局所成果であり、台帳の減算ではない。**

### 68.1 作ったもの

1. **生成器（信頼しない）** `Tools/ShippingFGCircuitS3rGen.lean`。`Module`／`Design` に `ToExpr` は無く、`Expr` は入れ子（`List Expr`）なので、**手書きのソース印字器**（`Module`／`Stmt`／`Expr`／`HWType`／`DimExpr`／`Operator`／`ResetKind` の各構成子と全フィールドを明示）にした。コマンド `#gen_pilot_artifact "path"` が elaboration 時に `pilotEntry3 hftRoot`（v11 が覆うのと同じ入口）を走らせ、返った `(b, D)` を `path` に書く。ビルドでは走らせない（1 回手で実行し、出力をコミット）。
2. **生成物（信頼しない、コミット済み、先頭に明記）** `Tools/ShippingFGCircuitS3rArtifact.lean`（647 行）: `pilotB0 : Module`（top、256 文）、`pilotK0`／`pilotK1`（子、88／159 文）、`pilotD0 : Design`（`modules = [pilotK0, pilotK1]`）。**追加**: `pilotS0 : Module` = 同じ run で計算した出荷形 `checkedOptimize b`（89 文）。これは要求の `(b₀, D₀)` に加えた項で、理由は §68.3（optimizer が kernel で展開できない）。
3. **観測** `Tools/ShippingFGCircuitS3rObs.lean`: `run_cmd` が入口をもう一度走らせ、`(b, D) == (pilotB0, pilotD0)`、`checkedOptimize b == pilotS0` を**コンパイル済みの `BEq`** で比較する（食い違えばビルド失敗）。改変した 3 つのコピー（先頭文を落とす、名前を変える、出荷形の body を逆順）が run と異なることも確認。**これは観測であって kernel の事実ではない**（実行されるコードの結果。1 環境・1 run）。同じ run の値に対するコンパイル済みの `shipsHierCheck` と `seqCheck`（子 2 つと出荷形）も観測として true を記録（kernel では評価できない、§68.3）。
4. **kernel の事実** `Tools/ShippingFGCircuitS3rKernel.lean`（`decide +kernel` または `rfl`。`native_decide` なし）。

### 68.2 kernel で通ったもの（閉じた項についての、既存の純粋検査の出力）

| 事実 | 結果 | kernel 時間（1 run、profiler の差分） |
|---|---|---|
| 形: top 256 文、出荷形 89 文、子 88／159 文 | 通る | < 0.1 秒 |
| `hierBinds pilotB0 = true` | 通る | 約 40 秒 |
| `hierRefineCheck pilotB0 pilotB0 = true` | 通る | 約 37 秒 |
| `refineCheck pilotK0 pilotK0 = true`（88 文） | 通る | 約 3.5 秒 |
| `refineCheck pilotK1 pilotK1 = true`（159 文） | 通る | 約 16 秒 |
| `mergeChecked pilotB0 = pilotB0` | 通る | 約 2 秒 |
| `hierRefineCheck pilotB0 pilotS0 = true`（出荷形を optimizer の出力として検証する、`checkedOptimize` が実行するのと同じ検査） | 通る | 約 37 秒 |
| `shipsHierCheck` の各 conjunct（`hierBinds`、`linkedWF`、`instNames` の `Nodup`、`noSelfRead`、`outsExtracted`、`rst` の存在、`instOutWidthsOk`）を、`checkedOptimize b` を閉じた項 `pilotS0` に置き換えて書き下した Bool 式 | 通る | 約 39 秒 |
| `pilotD0.modules = [pilotK0, pilotK1]` | `rfl` | 無視できる |
| 負の対照: 出荷形の先頭文を落とす、全 register の初期値を 1 にする → `hierRefineCheck pilotB0 _ = false`。子の先頭文を落とす → `refineCheck _ _ = false`。変更した項が元と異なる | 通る | 約 35、3、3、14、0 秒 |

kernel 型検査の合計は 1 run で約 229 秒（Kernel モジュールのビルド全体は 230 秒前後。cold/warm の差は測っていない）。閉じた項の大きさ（`Expr.sizeWithoutSharing`、1 run）: `pilotB0` 14,071、`pilotS0` 7,417、`pilotK0` 4,709、`pilotK1` 8,767、`pilotD0` 19（子への参照のみ）。生成ファイル 647 行。Check56 内の新規の `decide +kernel`（別の型にして再評価させた）は `refineCheck K0 K0` が 5.0 秒、`hierRefineCheck b0 b0` が 41.0 秒（elaboration を含む、1 run）。**時間は 1 つのマシンの 1 run で、上限ではない**。

### 68.3 kernel で評価できなかったもの（測定した事実。`native_decide` には切り替えていない）

- **`checkedOptimize`／`shipsHierCheck`／`hierCheck`**: `decide +kernel` が「`Decidable` インスタンスが `isTrue`／`isFalse` に簡約されない」で止まる。原因は `Sparkle.IR.Optimize.optimizeModule` が `partial def`（および `HashMap`）で、kernel から不透明なこと。`checkedOptimize` は `optimizeModule` を呼ぶので同様。そのため **`shipsHierCheck (childMap D₀.modules) pilotB0 = true` は kernel の事実として得ていない**。代わりに §68.2 のとおり出荷形を閉じた項 `pilotS0` として与え、同じ conjunct を書き下して通した（`pilotS0 = checkedOptimize pilotB0` は観測であり kernel の事実ではない）。**要求の項目のうちこれは字面どおりには満たせていない**（reviewer の判断を仰ぐ点）。
- **`seqCheck`**（子・出荷形）: `sf4Check` の `sanitizeName n == n` が `String.all` を使い、kernel は **`"abc".all (·.isAlphanum)` ですら簡約できない**（`decide +kernel` が止まる）。S3q が true を得たのはコンパイル済みの評価。kernel では評価できず、観測（Obs）として記録するに留める。
- **派生 `BEq`（`Module`／`Expr`）の `==`**: kernel で簡約できない（止まる）。`DecidableEq`（`decide (a = b)`）は簡約できる。負の対照の「変更した項は異なる」は `decide (… = …) = false` で行った。

したがって、**kernel の事実として得た既存検査は `refineCheck`／`hierBinds`／`hierRefineCheck`／`mergeChecked` と、optimizer を除いた `hierCheck` の conjunct**。SV 側（`seqCheck` 系）と optimizer を含む検査は、現行の `Sparkle/` の定義のままでは kernel では評価できない。次の段（M1）が出荷形・SV 側まで kernel で覆うなら、`String.all` を kernel で簡約できる形にする（`Sparkle/` の変更）か、`CheckRoot` を別に書く必要がある。

### 68.4 何が確立し、何が観測のままか

- **確立（kernel）**: 閉じた項 `pilotB0`／`pilotK0`／`pilotK1`／`pilotD0`／`pilotS0` について §68.2 の事実。AXIOMS は標準のみ（Check56）。
- **観測のまま**: (i) その項が `pilotEntry3 hftRoot` の返した値であること、(ii) `pilotS0 = checkedOptimize pilotB0`、(iii) コンパイル済みの `shipsHierCheck`／`seqCheck` が true。1 環境・1 run の `BEq`。生成器は信頼せず、kernel が受理したのは項についての検査の出力である。
- **確立していないもの**: 意味保存（`RootShows`）。§68.2 の事実は checker の出力であり、`CheckRoot` の健全性定理に結びついていない。SV 文字列の一致・SV の意味保存も含まない。源環境／宣言の固定（`R.machineData` と `b₀` の対応）も未着手。現行 FG の v11 の消費者には渡せず、FG 全体・全行の減算にはしない。

### 68.5 次の段（M1: ソースから module への checker）に必要なもの

1. `CheckRoot : SourceData → Module → Design → Cert → Bool` と `checkRoot_sound`（§67.3 の設計）。覆う形は §67.2 の 12 程度（`mux`・`eq`・`and`・`or`・`add`・`shl`・`slice`・`concat`・`const`・`ref`・`register`・`inst`）。
2. kernel 評価できる検査器であること（§68.3）: `String.all`／`optimizeModule` に依存しない。出荷形の扱いは、(a) 返却形 `b₀`（raw）についてだけ証明して出荷形への移送を `hierRefineCheck_linkedH` に委ねる、(b) `pilotS0` を閉じた項として検査する、のどちらか。
3. 子の検査（M3: `ChildFn`）と連結（M4）、`env` の宣言と kernel の定数 `R` の対応（S2z の `pin_*` の流儀）。
4. 採用入口 `certifiedReturn`（検査したその `(b, D)` だけを返す）は (c2) として後続。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 69. S3t（Issue `sparkle-fg-circuit-pilot`）: 案 (c) の M1 第 1 段 — 証明書設計の文の完全型検査（freeze 提案）と、組合せ子 1 つの validator の健全性

土台 `b8fbe491`（S3r を `par/fgc-s1` に merge）。コミットは `62b1bc76`（freeze 草稿）から本節まで。`Sparkle/` は変更していない。既存の定理の文も変更していない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。**1 つの artifact、1 つの子の結果は局所成果で、台帳の減算ではない**（reviewer 裁定）。

### 69.0 要約

- **freeze 提案（Lean で型検査済み）**: `SourceData`／`SrcEq`／`RootShowsAt`／`CheckRoot`／`checkRoot_sound` の文（`def … : Prop`、証明は書いていない）／`certifiedReturn`（`CheckRoot` で守り、false なら拒否、fallback なし）。`Tools/ShippingFGCircuitS3tSpec.lean`。
- **同時充足の例**: 具体の `rootS`（このルートの `SourceData`）について `rootS.ok = true`（kernel）、**`rootS.SrcEq` を証明**（IR を含まない）、`RootShowsAt` の seed 前提 4 つの同時充足（artifact の 17 register について、任意の入力値で）。`CheckRoot = true` は**示していない**（下の 69.5）。
- **組合せ子の validator の健全性**: `checkComb`／`checkComb_sound`（`Tools/ShippingFGCircuitS3tComb.lean`）。任意の module・任意の入力について、`checkComb s m = true` なら module の IR 意味（`evalAssigns`、宣言幅）が成功し、各出力 port の値がソース項の値に等しい。覆う演算は `ref`／`const`／`eq`／`mux`／`slice`／`concat`（2 部）。**閉じた子 `pilotK0`（`httpGetByte`、88 文）を kernel（`decide +kernel`）で受理**し、9 つの負の対照を拒否。`pilotK1`（`tlpCplByte`）は**受理されない**（scratch の試行で `checkK1 pilotK1 = false`、コミットしていない。`ofData` は `some`、入力・出力の個数・相異・幅と `stepT` は通るので、出力 port の項がソース項と食い違う。原因は未分析。健全性には影響しない不完全性）。
- **Check57**（`Tests/Gen5/FGCircuitPilotCheck57.lean`）: 完全型の署名を独立に書いた期待型と照合、負の対照（構造 validator 12 + 組合せ validator 9）、同時充足、kernel 時間と大きさ、AXIOMS 標準のみ（226 定理）。**`kjob lake build Tests.Gen5.FGCircuitPilotCheck57` が成功（1073 job、exit 0）**。

### 69.1 freeze 提案: 文の全体

**`SourceData`**（このルートについての構造。`SrcEq` が全フィールドを root の生成定数に固定する）:

```lean
structure SourceData where
  declName : Name                       -- = hftRoot
  d : MachineData                       -- = synth_hftPcieOutByte.machineData
  declObs : bools → bits → List (Nat → Nat)   -- 宣言自身の観測（monoObs shHft R）
  portNames : List String               -- 各 binder の port／wire の名前（**検査される主張**、69.1 の注）
  kidMod : List String                  -- 2 つの子の module 名（呼び出し順）
  kidInW kidOutW : List (List Nat)      -- 子の入力幅（[[6], [16,16,8,8,32,5]]）と出力幅（[[8],[8]]）
  kD : Nat                              -- root 自身の入力 binder の数（= 5）
def SourceData.ok : SourceData → Bool   -- d.ok ∧ instFields = [] ∧ insts.length = 2 ∧ 子 2 つ ∧ portNames は
                                        -- binder 数・相異・rst を含まない ∧ kD ≤ …
```

2 つの子は `kidData = [httpGetByte.machineData, tlpCplByte.machineData]`、`kidFs = [childValue …（各子の machineSource と bsIn）]` で**順序固定、長さ 2、`getD` の既定値なし**。`instFields = []` は `ok` が要求する（一般の `SourceData` についても、`instFields ≠ []` なら `ok = false`、すなわち被覆を証明していない場合は検査器が false を返す、という形で明示した）。

**`SrcEq`**（**IR の正しさを含まない**。`b`／`D`／`MachineWired`／`ChildFn`／`runModuleH` は一切現れない）:
`SrcCore ∧ CallsEq`。
- `SrcCore`: `declName = hftRoot`、`d = machineData`、`declObs = machineSource`（`monoObs_root`、`rfl`）、**全入力について状態の証人 `S₂ Ss` が存在**（`machine_states`／`root_states`。`Wit` は状態が reset から始まり `nexts` で進み `machineSource` を示す、という命題）、子の幅、`kD = 5`。
- `CallsEq`: 証人の状態で、call `k` の引数値が子の範囲に入り、子のソース関数 `kidFs[k]` の値が root の拡張 `machineExt` の対応する位置の値に等しい（`machine_linked` が `lsrc` について課す前提と同じ、ソースだけの文）。

**`RootShowsAt S b D`**（run なし、全入力。`machine_composed` の結論の形から、子の `MachineRun` **仮説**を結論の連言 `ChildFn` に移した）:

```lean
def RootShowsAt (S : SourceData) (b : Module) (D : Design) : Prop :=
  S.d.shape.instFields = [] ∧ S.d.shape.insts.length = 2 ∧
  -- top の port: root 自身の入力（主張された名前）、clk、rst、layout の出力
  (b.inputs.filter (clk/rst 以外)).map (·.name) = S.portNames.take S.kD ∧ "clk" ∈ … ∧ "rst" ∈ … ∧
  b.outputs = S.d.shape.layout.outs.map (…) ∧ linkedOk (moduleByName D.modules) b.body = true ∧
  ∃ regs, regs.Nodup ∧ regs.length = S.d.ss.length ∧ (∀ r ∈ regs, r ∈ portNames の register 範囲) ∧
    (register k は slot k の幅・init の register 文で、入力でない) ∧ (全 register 文はどれかの slot のもの) ∧
    -- 全 call の被覆（存在を結論に入れる）と ChildFn（結論の連言）
    (∀ k < 2, ∃ args mc st kd f, insts[k] = args ∧ st ∈ b.body ∧ CallStmt … k args mc st ∧
       moduleByName D.modules mc.name = some mc ∧ kidData[k]? = some kd ∧ kidFs[k]? = some f ∧
       ChildFn mc (childRange kd) f) ∧
    -- 全 inst 文の被覆（余分な inst は無い）
    (∀ mn iname conns, .inst mn iname conns ∈ b.body → ∃ k < 2, …同じ結論…) ∧
    -- run: 全入力、状態の証人、T、seed、st0、mems
    ∀ i bools bits S₂ Ss, Wit … → ∀ T seed st0 mems,
      (a) 入力 port（主張された名前）が源の入力 posEnc を運ぶ → (b) register は状態から読む →
      (c) seed t st "rst" = 0 → (d) regs[k] = r ∧ slots[k] = f → st0 r = f.init →
      ∃ envs, runModuleH … = some envs ∧ envs.length = T ∧ ∀ j k o f, outs[k] = o → machineSource[k] = f → envs[j] o.name = f j
```

reviewer 裁定2 との対応: (i) **被覆**: 全 `k < 2` の call と `b.body` の全 `inst` 文（検索の失敗は文を**偽**にする。空虚にならない）。(ii) **`moduleByName` の接続**: 各 call の `moduleByName D.modules mc.name = some mc`。(iii) **`instFields = []`**: `RootShowsAt` の最初の連言、および `SourceData.ok`。(iv) **2 子の範囲・順序・入力幅の固定**: `kidData`／`kidFs`（`childRange`／`childValue`）、`kidInW`。(v) **seed／初期値／reset = 0 の正確な前提と同時充足**: (a)–(d)、69.2。(vi) **`srcEq` に IR の正しさを入れない**: 上のとおり。

**設計の変更（S3q の草稿からの差分と理由）**: S3q は `ids`／`cache`／`machPorts`（コンパイラの名前割り当て）を含む `MachineWired` をそのまま結論に置く案だった。S3t の最初の型検査版（`62b1bc76`）はそうしたが、**割り当て名が kernel で評価できない**ことが分かった（下の G1）。そこで `RootShowsAt` を、データが**主張する**名前 `S.portNames`（検査器が module と照合する）で述べる形に改めた。`SourceInputs`（`Admissible`、割り当て器に依存）は前提 (a) から外し、(a) は「主張された名前の port が源の入力 `posEnc` を運ぶ」という IR 側だけの文にした。`MachineWired` の他の連言（register 文、出力、linked 順、被覆）は同じ内容を `S.portNames` で述べ直した。コンパイラの割り当て器との対応（`names = machPorts …`）は、この検査器の健全性には不要で、消費者側の別の課題として残る。

**`CheckRoot : SourceData → Module → Design → Cert → Bool`**（純粋）: `structuralOk ∧ bodyOk`。
- `Cert`（信頼しないヒント）: 2 つの `inst` 文の body 内添字 `callAt`、register 名（slot 順）`regs`。
- `structuralOk`（**書いた**）: `S.ok`、`callAt` は 2 つの相異な添字、各 call の `inst` 文の接続が `CallStmt` の形（子の引数 port ↔ 割り当て名の引数 wire、出力 port ↔ call の wire、clk/rst なし、port 幅が固定された幅）で `moduleByName` が見つけた module のもの、`inst` 文はちょうど 2 つ、register（cert の名前、slot の幅・init、clk・rst、他の register 文なし、入力でない）、top の port（入力・clk・rst・出力）、`linkedOk`。
- **`bodyOk`（未実装、常に false）**: 文を源の項に照らす本体の検査（M1 本体）。**そのため `CheckRoot` は全入力で false で、`certifiedReturn` は今は常に拒否する**。freeze は「文と構造部分」を固定するもので、本体が検査済みという主張ではない。

**`checkRoot_sound` の文**（`CheckRootSoundStmt : Prop`、証明は**書いていない**。`sorry` なし）: `∀ S b D cert, S.ok = true → S.SrcEq → CheckRoot S b D cert = true → RootShowsAt S b D`。現在は `bodyOk = false` なので、この文は（`CheckRoot = true` が起きないので）空虚に成り立つ。**空虚に成り立つ現状を、`bodyOk` を書いた後に実質的な文にするための固定点**として置く。

**`certifiedReturn S mk declName`**: `pilotEntry3 declName` を走らせ、返った `(b, D)` について `CheckRoot S b D (mk b D)` が false なら `throwError "certificate check failed"`、true なら**その** `(b, D)` を返す。fallback なし（裁定）。`certifiedReturn_sound` の文（`CertifiedReturnSoundStmt`: `RunsTo (certifiedReturn …) … (b, D) … → ∃ cert, CheckRoot S b D cert = true`）も型検査だけ（証明なし）。

### 69.2 同時充足の例（`Tools/ShippingFGCircuitS3tSpec.lean`／`…S3tSat.lean`／`…S3tCalls.lean`／`…S3tCert.lean`）

| 事実 | 証明 |
|---|---|
| `rootS.ok = true`（`d.ok`、`instFields = []`、2 call、69 個の相異な名前など） | `decide +kernel` |
| `rootS.SrcCore`: 各フィールドが root の定数、`monoObs_root`、全入力の証人（`root_states` から）、幅 | `rfl`／既存定理 |
| `rootS.CallsEq`: call 0（`httpGetByte`）と call 1（`tlpCplByte`）の引数値が範囲内で、子の関数の値が拡張の値に等しい | `machine_arg_k`＋「decode は encode の逆」＋子の pointwise。定義の簡約は `kernel_rfl`（証明項 `Eq.refl lhs`、kernel が検査する未信頼の tactic、axiom なし） |
| **`rootS.SrcEq`** | 上の 2 つから |
| seed 前提 (a)–(d) の同時充足（一般: `premises_satisfiable`。`SourceData.ok` と、相異な `regs` が主張された名前の register 範囲にあることから、任意の入力値 `val t q` について `seed`、`st0` が存在） | 一般の補題（association list による seed、`regs` と入力名の分離） |
| 具体例 `example_premises`: artifact の 17 register（`cert0.regs`）について、任意の入力値で (a)–(d) が同時に成り立つ | `cert0.regs` の相異と範囲は `decide +kernel` |
| `structuralOk rootS pilotB0 pilotD0 cert0 = true`（閉じた artifact と証明書 `cert0`） | `decide +kernel`（約 4.6 秒、1 run） |

`cert0` は信頼しない生成物（`pilotB0` の 2 つの `inst` 文の添字 173、238 と、17 個の register 名）。

### 69.3 組合せ子の validator と健全性（`Tools/ShippingFGCircuitS3tComb.lean`、`…S3tCombRun.lean`）

**ソース項** `CTerm`: `var p w`（ソース位置と幅）、`lit w v`、`eq a b`、`mux c a b`、`slice a hi lo`、`cat a b`。`den V : CTerm → Nat`（位置の値 `V` での値）、`width`、`wf`（`eq` の幅一致、`mux` の条件幅 1 と分岐幅一致、`slice` が範囲内）。補題 `den_lt`: `wf` な項の値は幅に収まる。

**validator** `checkComb (s : CSrc) (m : Module) : Bool`（`CSrc` = 入力 port のソース位置と出力 port ごとの項）: 入力は相異・個数一致・各々が port 幅で宣言、body は assign のみ、body を順に翻訳して全て通る（assign 先の**宣言幅**が定義の幅に等しいこと（出力 port は例外）、`ref` は宣言幅が定義の幅に等しいこと、`slice` は全幅なら項そのもの・literal なら literal に畳む）、各出力 port の翻訳が**ソース項に等しく**、port 幅がその項の幅。

**`checkComb_sound`**: `checkComb s m = true` なら、**任意の** `V`（ソース位置の値）・`mems`・`env`（入力 port が `V` の値を運ぶ）について、`∃ env', evalAssigns (declWidth m) mems m.body env = some env' ∧ ∀ i p c, outputs[i] = p → s.outs[i] = c → env' p.name = c.den V`。証明は、式の翻訳（`toC`、`toCList` の相互再帰）の健全性（幅の一致・値・`wf`）、文の列の翻訳 `stepT` の健全性、入力表の健全性。slice／concat／eq の補題は不足していなかった（`Sparkle.IR.Semantics` の `evalExpr`／`evalOp` の展開と `Nat` の補題だけで足りた）。

**源との接続**: `ofData`（`MachineData` の `outs`／`ls` から、位置を `nIn` で入力と `let` に分け、`let` を代入して `CTerm` にする）。`httpGetByte` の `outs`／`ls` は `bitsInput`／`bitsLit`／`compare .eq`／`mux` だけで、`ofData` が `some`。**`ofData` の項が `typedVal` の与える値を表すこと（`CTerm.den` と `Term.eval` の対応）は証明していない**。証明したのは validator の健全性（ソース項 `CSrc` に対して）で、`MachineData` との橋は次の段。

**kernel**: `checkK0 pilotK0 = true`（`httpGetByte` の `MachineData` から `ofData` で読んだ項に対する `checkComb`、閉じた子 88 文）は `decide +kernel`（Check57 の 1 run で約 7.0 秒、elaboration を含む）。負の対照（全て `decide +kernel`）: 先頭文を落とす、最後の文（出力の代入）を落とす、定数 71 → 72、全 mux の 2 つの分岐を入れ替える、wire `_gen_b0` の宣言幅を 9 にする、出力 port を 7 bit にする、出力 port の名前を変える、**もう一方の子**の module を入れる、誤った源の出力項。変更した項が元と異なること（`neg_distinct`）。

### 69.4 構造 validator の負の対照（`Tools/ShippingFGCircuitS3tCert.lean`）

`structuralOk rootS pilotB0 pilotD0 cert0 = true` に対し、次は全て false（kernel）: 子 1 つ目／2 つ目の欠落、子の名前の入れ替え（module を相手の名前で与える）、子 2 の入力幅を 15 にする、出力 port を 7 bit にする、全 register の reset 値を 1 にする、top から `rst` 入力を除く、証明書 `callAt = [238, 173]`（入れ替え）・`[173, 173]`（重複）・register 名の並べ替え（slot と幅が合わない）、データの子の入力幅を 7 にする、データの子の個数を 1 にする。`CheckRoot rootS pilotB0 pilotD0 cert0 = false`（`bodyOk` が未実装のため）も kernel で確認。

初版の `regOk` は register の**幅**を見ておらず、register 名の並べ替え（全 init が 0）を受理した。slot の幅を照合するように直した（reviewer 裁定の「register／slot 添字の束縛」）。

### 69.5 確立していないもの・欠けている文

- **G1（allocator の名前）**: コンパイラの名前割り当て `machPorts …`（`inputWire`／`sanitizeName`／`NameHints.clean`）の結果は **kernel で評価できない**（`String.replace`／`String.all` が整礎再帰 `WellFounded.opaqueFix` で、`decide +kernel` が止まる。`CircuitM.sanitizeName "rxByte" = "rxByte"` ですら）。したがって、欠けている文は「`∃ ids cache, ids.Nodup ∧ ids.length = 69 ∧ (machPorts hftRoot ids cache binders).map (·.name) = rootPortNames`」。これを `RootShowsAt`／`SrcEq` に入れると同時充足の例が証明できないので、69.1 のとおり設計を改め、割り当て器への依存を外した。**割り当て器の名前との対応は未確立**（`SourceInputs`／`MachineWired` の名前を前提とする既存の定理との接続に必要。`Sparkle/` の `String` 関数を kernel で簡約できる形にするか、`String.replace`／`clean` の仕様補題を証明するかの選択）。
- **`bodyOk`**（M1 本体）: root の 256 文（assign 237、register 17、inst 2）を源の項に照らす検査は書いていない。覆う形は 12 程度（§67.2）。組合せ子の validator（69.3）は、その assign のみの部分（`mux`／`eq`／`ref`／`slice`／`concat`／`const`）を子 1 つについて示したもので、root の top（`and`／`or`／`add`／`shl`、register の next、inst の出力 wire、状態の読み）は覆っていない。
- **`checkRoot_sound` の証明**: 文だけ。`bodyOk = false` の間は空虚。
- **`certifiedReturn_sound` の証明**: 文だけ。
- **`CTerm` と `typedVal` の橋**、および `checkComb_sound` の結論と `ChildFn mc (childRange kd) (childValue …)` の接続: 未着手（`ChildFn` は `evalAssigns` を使い、`childValue` は子の `machineSource` を `decB`／`decV` で復号して読む）。
- `pilotK1`（`tlpCplByte`）は `checkComb` に受理されない（69.0）。
- **`kernel_rfl`**: `Tools/ShippingFGCircuitS3tCalls.lean` の未信頼の tactic（目標 `a = b` に証明項 `Eq.refl a` を割り当てる。kernel が `a ≡ b` を検査し、成り立たなければ定理の追加が失敗する）。elaborator の `rfl` が root の大きな生成項で終わらないため。新しい axiom／law／TRUSTED ではない（`Lean.ofReduceBool` なし、AXIOMS は標準のみ）。
- 時間と大きさは 1 つのマシンの 1 run で、上限ではない: kernel 時間（Check57、elaboration を含む）`checkK0 pilotK0 = true` 約 7.0 秒、`structuralOk … = true` 約 4.6 秒、`rootS.ok = true` 約 2.3 秒。項の大きさ（`sizeWithoutSharing`）: `checkComb_sound` 18,251、`rootS_callsEq` 35,737、`premises_satisfiable` 14,378、`cert0` 139。閉じた子 `pilotK0` は 4,709（§68.2）。モジュールのビルド（1 run）: Spec 約 5 秒、Sat 約 1 秒、Calls 約 5 秒、Comb 約 3 秒、CombRun 約 37 秒、Cert 約 43 秒、Check57 は依存込みで約 2 分。

**記録補足（S3u で追記、reviewer）**: (1) `SrcEq` が `SourceData` の全 field を固定するわけではない。`declName`／`d`／`declObs`／`kidInW`／`kidOutW`／`kD` は root の生成定数に固定されるが、**`portNames` と `kidMod` は claim**（validator が module に照らして検査するだけ）。(2) Check57 の署名の型 ascription は**関数の型の確認**であり、`SrcCore`／`CallsEq`／`structuralOk` の本文全体の独立な比較ではない。独立比較は `RootShowsAt` の別記述（`Iff.rfl`）と `CheckRootSoundStmt`／`CertifiedReturnSoundStmt` の再記述に限る。(3) `CertifiedReturnSoundStmt` は checker 受理の抽出だけで、`declName` と `S.declName` の対応は述べない（最終の利用者向け source-preservation wrapper で同一宣言を固定／検査する）。

### 69.6 Check57 の出力（Check 自身の行）

`FGCIRCUIT57 AXIOMS: 226 theorems of the S3t modules (Spec, Sat, Cert, Calls, Comb, CombRun), standard axioms only ([Quot.sound, Classical.choice, propext]); no sorryAx, no Lean.ofReduceBool (no native_decide)`。`FGCIRCUIT57 NEGATIVE CONTROLS: structural validator on the root 12 … + CheckRoot refuses; combinational validator on pilotK0 9 …`。`FGCIRCUIT57 SIGNATURES: …`（署名は独立に書いた期待型と照合、`RootShowsAt` は独立に書き直した文と `Iff.rfl`）。`FGCIRCUIT57 SATISFIABILITY: rootS.ok = true; rootS.SrcEq proved; the four seed premises … at the artifact's 17 registers …; CheckRoot = true is NOT shown`。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 70. S3u（Issue `sparkle-fg-circuit-pilot`）: S3t の freeze 境界 2 点 — 返された Design の top（P1-1）と top 入力の型・幅（P1-2）

土台 `8ed3fcc4`（S3t）。`Sparkle/` は変更していない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。1 つの root／子の結果は局所で、台帳の減算ではない。`bodyOk = false` と `certifiedReturn` の拒否は維持（空虚な `checkRoot_sound` を受理済みとして提示しない）。

### 70.1 P1-1: 返された Design の top、module 名の重複、top/子の名前衝突

`RootShowsAt` の結論に `D.topModule = b.name ∧ (D.modules.map (·.name)).Nodup ∧ ∀ m ∈ D.modules, m.name ≠ b.name` を追加。`structuralOk` に `designOk b D`（同じ 3 条件の Bool 版）を追加。`moduleByName` は `find?`（同名の最初）であり、名前が相異なれば名前ごとに唯一の module、子の名前の lookup が top を返すことはない。負の対照（kernel）: top 名だけ別名にする（`neg_other_top`）、module 名の重複（`neg_dup_module`）、子の名前を top と同じにする（`neg_kid_named_top`）。

### 70.2 P1-2: top 入力の型と幅

- 各 claimed name がどの外部入力か: **`portNames` の先頭 `kD` 個が、この順で、root の入力 binder（`d.bsIn` の先頭 `kD` 個）に 1 対 1 に対応**する（`srcInPorts`）。型は `kindTy`（`bool` → 1 bit、`bits n` → `n` bit）。
- `RootShowsAt` は `b.inputs = topInPorts …`（上の入力の後に `clk`／`rst` を各 1 bit）と、IR の意味が実際に読む `declWidth b n = w`（`wires` 宣言、各ソース入力について `w = kindW`）を結論に持つ。`structuralOk` は `topInOk`（同じ 2 条件）を検査。入力名の一意性は `b.inputs` の完全一致と `S.ok`（`portNames` が Nodup、`rst`／`clk` を含まない、先頭 `kD` に domain binder がない）から従う。`clk`／`rst` は artifact の `wires` に宣言がなく（`declWidth` は 0）、型は `b.inputs` の完全一致で固定する。
- seed 前提 (a) との整合: 前提 (a) の値 `posEnc …` は宣言幅に収まる（`Tools.ShippingFGCircuitS3tSat.posEnc_fits`: `bits n` なら `< 2^n`、`bool` なら `< 2`）。4 前提の同時充足 `premises_satisfiable` は新しい `S.ok` の下で再証明。
- 負の対照（kernel）: 入力幅を変える（port と wire 両方 `neg_narrow_in`／port のみ `neg_narrow_in_port_only`／wire のみ `neg_narrow_in_wire_only`）、入力の入れ替え（`neg_swap_inputs`）、入力名の重複（`neg_dup_input`）、`clk` を 2 bit にする（`neg_wide_clk`）、claimed name に `clk`（`neg_claim_clk`）。

### 70.3 再証明したもの

`structuralOk rootS pilotB0 pilotD0 cert0 = true`（`struct_ok`、kernel）、`rootS.ok = true`、`rootS.SrcEq`（変更なし）、4 前提の同時充足、既存の 12 の対照。`CheckRoot rootS pilotB0 pilotD0 cert0 = false`（`bodyOk` 未実装）。

### 70.4 新しい freeze 提案

S3t の §69.1 の文のうち `SourceData.ok`（`clk` を含まない、先頭 `kD` に domain binder なし）、`RootShowsAt`（上の 2 群の結論）、`structuralOk`（`designOk`／`topInOk`）を本節の定義で置き換えた型を freeze 対象とする。`bodyOk` の実装と、実 artifact の `CheckRoot = true` および soundness を同じ提出で確認するまでは、`checkRoot_sound` を機械受理しない。

**受理の記録（reviewer、S3u/S3v の審査）**: `615b4b90` の `RootShowsAt`、`SourceData.ok`、`structuralOk` と、それらが使う helper 定義を freeze 対象として受理した。helper は `kindW`、`kindTy`、`inWidths`、`srcInPorts`、`topInPorts`、`topInWidths`、`topInOk`、`designOk`、`callOk`、`regsOk`、`linkedOk`、`moduleByName`、`childRange`、`childValue`、`ChildFn`、`kidData`、`kidFs`、`Cert` で、いずれも `Tools/ShippingFGCircuitS3tSpec.lean` とその import にある。

この受理には次の限定がある。
- `SourceData.SrcEq` はこの root に特化した文で、任意のソースに対する一般の保証とは呼ばない。
- `bodyOk = false` の骨格と、空虚な `CheckRootSoundStmt` は受理の対象外。`bodyOk` とその健全性は、実 artifact の `CheckRoot = true` と合わせて後続で受理する。
- `CertifiedReturnSoundStmt` は checker の受理を取り出すところまでの文。利用者向け wrapper で同じ `declName` に接続する部分は後続の作業。
- 現在の freeze は reset = 0 の IR 保証で、reset の assert や SV の意味には広げない。

### 70.5 記録補足（S3t から）

§69.5 に追記済み: `portNames`／`kidMod` は claim、Check57 の型 ascription は関数の型のみ、`CertifiedReturnSoundStmt` は `declName` と `S.declName` の対応を述べない。

### 70.6 Check57 の出力（Check 自身の行）

`FGCIRCUIT57 AXIOMS: 250 theorems of the S3t modules (Spec, Sat, Cert, Calls, Comb, CombRun), standard axioms only …`。`NEGATIVE CONTROLS: structural validator on the root 12 + 3 design-top … + 7 input-boundary …`。`kjob lake build Tests.Gen5.FGCircuitPilotCheck57` は exit 0（1073 job）。`structuralOk … = true` の fresh kernel 検査は約 3.7 秒、`rootS.ok` 約 2.3 秒（1 run）。Cert のビルドは約 65 秒。

### 70.7 まだ無いもの

`bodyOk`、`checkRoot_sound` の証明（S3t と同じ）。`SourceData` の claimed name が allocator の名前と一致する保証は不要（Q1 裁定）だが、旧 `MachineWired`／FG 消費者との橋は別の互換性義務。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 71. S3v（Issue `sparkle-fg-circuit-pilot`）: 閉じた子 1 つ（`pilotK0` = `httpGetByte`）を端から端まで閉じる — `CTerm` → `Term.eval`/`typedVal` → `machineSource` → `ChildFn`

土台 `8ed3fcc4`（S3t）。新規ファイルのみ: `Tools/ShippingFGCircuitS3vBridge.lean`、`Tools/ShippingFGCircuitS3vChild.lean`、`Tests/Gen5/FGCircuitPilotCheck58v.lean`（lakefile に各 `lean_lib`）。S3tSpec／S3tCert／Check57 と `Sparkle/` は変更していない。既存の定理の文も変更していない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。**1 つの子の結果は局所成果で、台帳の減算ではない**。

### 71.1 範囲（正確に）

- 対象は `httpGetByte`（`pilotK0`、88 文）**だけ**。`pilotK1`（`tlpCplByte`、`checkComb` が受理しない）と root の `bodyOk` は対象外。
- 橋 `ofData_sound` は**一般の補題**で、仮定は `MachineData` についての**決定可能な事実**だけ: `d.ss.length = 0`（`ofData` は `d.ss = []` を検査しない）、`Frag`（下）、そして値の側の `(W p w).toNat = V p % 2 ^ w`（入力位置の値が `V` で実現されること）。**一般形を仮定としては置いていない**。`httpGetByte` についてはこれら全部を kernel（`decide +kernel`、フィールドごとの閉じた事実）で証明した。
- **注（reviewer）**: `Frag` は `tC` が覆わない構成子（`binary` など）に既定で `true` を返す。したがって `Frag` だけでは対応する構文の集合を判定しない。対応範囲は `Frag = true` と `tC`／`ofData` の成功（覆わない構成子では `tC` が `none` を返す）の組で決まる。`ofData_sound` は成功を前提に置くので健全性に問題はないが、`Frag = true` だけを根拠に `binary` 等が供給済みと扱ってはいけない。
- `Frag d t`: `tC` が覆う形（`bitsInput`／`bitsLit`／`boolLit`／`compare .eq`／`mux`／`slice`／`concat`）に限り、`slice` の長さ > 0、`boolInput` を含まない、`bitsInput` は入力位置（`vpos j < nIn`）か「`d.ls` の対応する `let` の sort が `.bits w`」であるもの。これが、`tC` が非入力位置を `Nat` 減算で `let` に写すことの正当化（`ss.length = 0` と合わせて位置の算術 `nIn + ss.length + (p - nIn - ss.length) = p` が成り立つ）と、slice 長 0 の幅の食い違い（`hi - lo + 1`）を排除する。

### 71.2 証明したこと

1. **`tC_sound`／`letsC_sound`／`ofData_sound`**（Bridge）: `ofData d = some s` のとき、`s.inPos = inputPositions d`、`s.outs.length = d.outs.length`、各出力 `k` について `Rel V o.1 (Term.eval … o.2 を letTV d x B W で) c`、すなわち `c.den V = enc o.1 (eval …)` かつ `c.width = sortW o.1`。`letTV d x B W` は `typedVal` を 1 時刻で書いたもの（`typedVal_eq : … = letTV … := rfl`）。`let` の翻訳 `letsC` と型付き値 `letVal` を同時に帰納し、`let` 位置は `TVal.set`／`set_v_eq`／`set_v_ne` で追う。
2. **`k0_childFn`**（Child）: `ChildFn pilotK0 (childRange kd0) (childValue httpGetByte.machineSource kd0.bsIn defaultDomain)`（`kd0 = httpGetByte.machineData`）。全入力、run の前提なし。証明は `checkComb_sound`（`checkK0 pilotK0 = true` から `ofData kd0 = some s ∧ checkComb s pilotK0 = true` を取り出す）＋ `ofData_sound`（`V q := vals.getD (portIdx bs q) 0`、`W := decV`、`B := decB`）＋ `httpGetByte.machine_result`（`machineSource` を時刻 0 で評価したものが `enc (eval (typedVal …))`）。入力 port が 1 つ（`clk`/`rst` でない、幅 6）、`inputPositions = [1]`、`portIdx bs 1 = 0`、範囲の仮定から `env p0.name < 2^6` を `inRange_get` で得る。
3. **`k0_childFn_slot`**: `∃ kd f, kidData[0]? = some kd ∧ kidFs[0]? = some f ∧ ChildFn pilotK0 (childRange kd) f`（`rfl` で上へ）。これが `RootShowsAt` の call 0 の連言の形。

### 71.3 Check58v（`kjob lake build Tests.Gen5.FGCircuitPilotCheck58v`、exit 0）

- 完全型: `k0_childFn` を `ChildFn`／`childValue`／`childRange`／`argPorts` を使わずに書き直した型（`Zip₂` の範囲、`filter` した入力、`decB`／`decV` を展開した信号）へ型注釈（不一致はコンパイルエラー。一致した）。橋 `ofData_sound`、`letTV = typedVal` も同様。
- 負の対照: 変更した定数、mux の分岐入れ替え、出力の代入の欠落（検査器が拒否）、**もう一方の子の module**・**もう一方の子のデータ**（`checkWith tlpCplByte.machineData pilotK0 = false`）、`ChildFn pilotK0 (childRange kd0) (fun _ => 0)` は**偽**（引数 1 で module は 71）、**変異 module（71→72）は同じ `ChildFn` を満たさない**（`eval1` の kernel 評価と `k0_childFn` から）。
- 出力（Check 自身の行）: `FGCIRCUIT58V AXIOMS: 72 theorems of the S3v modules (Bridge, Child), standard axioms only ([Quot.sound, Classical.choice, propext]); k0_childFn depends on [propext, Classical.choice, Quot.sound]; no sorryAx, no Lean.ofReduceBool (no native_decide)`。`FGCIRCUIT58V NEGATIVE CONTROLS: 7 — …`。`FGCIRCUIT58V SIGNATURES: …`。`FGCIRCUIT58V SCOPE: ONE closed child (pilotK0 = httpGetByte, 88 statements) for ALL inputs in its range, no run premise; … pilotK1 (tlpCplByte) and the root's bodyOk are NOT covered; ledger unchanged`。
- 大きさ（`sizeWithoutSharing`、1 run）: `tC_sound` 603、`letsC_sound` 1,039、`ofData_sound` 15,176、`k0_childFn` 42,949。kernel（elaboration を含む、1 run）: `Frag` の確認 4 ms、`eval1 pilotK0 = some 71` 310 ms。ビルドは各ファイル 1 分未満（依存の replay を除く）。`decide +kernel` は全部フィールドごとで、machineData 全体にはかけていない。

### 71.4 残り（確立していないもの）

- **`pilotK1`（`tlpCplByte`）**: `checkComb` が受理しない（§69.0）。第 1 の違いの診断（(ii)）は未着手。単なる比較の緩和は不可（証明付きの狭い正規化のみ）。
- **top の `bodyOk` と `checkRoot_sound`**（(iii)）。`k0_childFn_slot` は call 0 の `ChildFn` の連言だけを供給する。call 1 の連言、`RootShowsAt` の他の連言は未供給。
- freeze の境界修正（P1-1／P1-2）は S3u の担当。この節は `S3tSpec`／`S3tCert`／`Check57` を触っていない。
- 橋は `Frag` の外（Bool 入力、状態、`binary`／`concatLit*`／`zextMap` 等）には適用できない。広げる場合は `tC` の被覆とともに `tC_sound` を拡張する。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 73. S3y（Issue `sparkle-fg-circuit-pilot`）: 最初の一般接続 — `checkData_sound`（G1）と `certifiedEntryC_sound`（G2）

土台 `8d587684`。新規ファイルのみ: `Tools/ShippingFGCircuitS3yGen.lean`、`Tools/ShippingFGCircuitS3yEntry.lean`、`Tests/Gen5/FGCircuitPilotCheck60.lean`（lakefile に各 `lean_lib`）。`Sparkle/`、S3t／S3v／S3w のファイル、既存の定理の文は変更していない。S3w（`pilotK1`／`checkCombN`／`FragW`）には触れていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。**1 つの子を例にした一般定理の導入であり、台帳の減算ではない**（行が外れるのは最終 binder 差分でレビュアが決める）。

### 73.1 一般の文（Lean で型付け・証明済み）

- `dataValue d x vals`: `d` **だけ**から定義した意味。`d.outs[0]` の項に `Term.eval` を、`letTV d x (decB d.bsIn vals) (decV d.bsIn vals)`（`typedVal` の 1 時刻版）の上で適用し `enc` する。モジュール・`ofData`・`CTerm` は使わない。`x` は状態値（`circOk` の下では `d.ss = []` で一意）。
- `DataShows d m := ∀ x, ChildFn m (childRange d) (dataValue d x)`。
- `circOk d`（Bool）: `d.ss = []`、出力 1 つ、全 `let` と出力が `Frag`。`portsOk d m`（Bool）: ポート数 = 非 domain binder 数、`clk`/`rst` なし、各ポートの幅 = binder の幅、`inputPositions` の i 番目の `portIdx` = i、出力 1 つ。`checkData d m := circOk d && portsOk d m && (ofData d の成功 ∧ checkComb s m)`。root 固有の定数はない。
- **G1 `checkData_sound : ∀ d m, checkData d m = true → DataShows d m`**。G1 は data と module についての文で run を含まない（`Laws`／`CellPrem` は使わない）。`ofData_sound`（S3v）＋`checkComb_sound`（S3t）から。S3v の `k0_childFn` が子ごとに供給していた事実（ポート数・幅・`portIdx`・出力数・fragment）は `circOk`／`portsOk` の Bool 検査になった（`portsOk_spec` が命題に戻す）。
- `k0_checkData : checkData kd0 pilotK0 = true`（kernel、閉じた項）＋ `dataValue_k0`（`httpGetByte.machine_result`、宣言ごとの結び付け）から **`k0_childFn'`** を再導出（`k0_childFn` と同じ型）。
- **入口** `certifiedEntryC lvl declName`: `readData` で `d` を読み、**既存の** `synthesizeCombinationalCoreOff declName` を無変更で走らせ、`checkData d b && designOk b D` が偽なら throw（フォールバックなし）、真なら同じ `(b, D)` を返す。
- **G2 `certifiedEntryC_sound`**: 成功した run `RunsTo (certifiedEntryC lvl declName) … (b, D) w'` から、`∃ d w₁ w₂`、同じ run で `readData` が `d` を返し、無変更の入口がその後に同じ `(b, D)` を返し、`checkData d b = true ∧ designOk b D = true ∧ DataShows d b`。証明は `RunsTo` の bind／if／throwError／pure の反転だけ（`runsTo_pure` のみ新規）。前提は run の成功（`RunsTo (certifiedEntryC …)`）であり、G2 は run 前提を不要にするものではない。**データ対 IR の範囲に限り**、SrcEq／ChildFn／環境照合を束縛変数に置き換えず `checkData` がその run 自身の `d` と `(b, D)` で決める。G2 は `readData` の正しさ（`d` が宣言のデータであること）を証明しない: それは DeclDenotes（S3z）。
- **ガード** `certifiedEntryC_refuses`: どの `d` でも検査が偽（または `designOk` が偽）なら、その `(b, D)` を返す成功 run は存在しない。

### 73.2 `MachineData` の MetaM 読み取りの欠け（正確に）

`Sparkle/` には `MachineData` を返す MetaM 関数が**ない**（`MachineData` は `Tools` の構造体。`Sparkle.Compiler.Elab.machineShape?` は `MachineShape` を返す純関数。`f.machineData` は `#machine_endpoint` が生成する定数）。新しい読み取りを `Sparkle/` に作らず、最も近い既存の読み取り（`RootReader` が述べるもの）を `Tools/ShippingFGCircuitS3yEntry.lean` の `readData` に書いた: `entry₀ env X`、`machineShape? false [] E (structEnv env)`、`dataOfAt lvl E (structEnv env)`。`lvl` は引数（G2 は任意の `lvl` で成り立つ）。`getEnv` の反転は不要（`readData` の run は存在量化で渡すだけ）。

### 73.3 DeepElab／Cdo から何を再利用し、何を再利用しないか

- 再利用したもの: **現在の一般 comb validator**（`checkComb_sound`、`ofData_sound`）、`ChildFn`／`childRange`／`decB`／`decV`／`inRange_get`、`k0` の証明の構造（`portIdx`／範囲の議論）、既存の `designOk`（S3t）、`RunsTo` の反転補題。
- **再利用していないもの**: DeepElab の `CExpr.compile_correct`（演算子ごと）と `Cdo.irState_eq`／`Cdo.elab_general` は**まだ使っていない**。ソースは `MachineData`（`Frag` の部分言語）であり Cdo ではない。演算子（and／or／add／shl／sub／lt…）の CTerm 意味補題としての再利用は §73.5(b)、レジスタの帰納は (c)。
- 元の run の証明（v11／FG スキーマ）は**この入口には使っていない**: 検査付き入口は別の入口で、旧入口の証明は旧入口のものとして残る。

### 73.4 既存 FG 最終結論との対応（**未接続一覧**。G1／G2 の入口・結論は FG のものと異なるため、どの行もここからは外れない）

| FG／v11 の前提・結論 | 検査付き入口 | 状態 |
|---|---|---|
| A.P-01 Laws (L) | G1／G2 の証明は使わない。ただし FG の入口・結論と別物なので行は残る | 未接続 |
| A.P-02 Start（AdmCtx ∧ JQC、hquiet／hsynth） | 証明は使わない。行は残る | 未接続 |
| A.P-04 core run `hr` | G2 は run の成功を前提に使う（`hr` 不要ではない）。行は残る | 未接続 |
| C.EN-4 CellPrem、hD／hG／hT／hs／h0 | 証明は使わない。行は残る | 未接続 |
| A.P-06 MachineDefines／DeclDenotes | **まだ必要**: 読んだ `d` が宣言のデータであり、宣言の Signal 関数が `dataValue` であること（`machine_result`／`machine_source`、宣言ごとに生成） | 未接続（一般の front-end 定理か入口での検査が未決） |
| G3 ReflectsAll（machine route）、B.G-* reflection Props | 同上（machine route） | 未接続 |
| TopShips（結論） | `DataShows` は組合せモジュールの IR レベル・子インターフェース形。階層・レジスタ・インスタンスの `TopShips` は §73.5 | 未接続 |
| 最適化（IR → `checkedOptimize b`） | G1／G2 は**返された `b`** について。印字される最適化後の形は S3r の `hierRefineCheck` の観測だけで接続 | 未接続（新しい主張なし） |
| SV | 範囲外。変更なし | 未接続 |

IR・最適化・SV は上のとおり別々。**この表は台帳の行を一つも外していない**。FG 全体の結論までの橋と必要 IP の受入は、別の完了条件として扱う。

### 73.5 必要 IP の baseline（完了条件の一部。**この単位では未実施**）

検査付き入口は旧入口と別物なので、(i) 成功時の健全性（G1／G2、本節）と (ii) 必要 IP で `certifiedEntryC` が**成功すること**（検査が、コンパイラが返すものを受理する）かつ出力が旧入口と変わらないこと、は別々に確認する。(ii) は未測定: 今回の `Frag` と `ofData` の被覆（`eq`／`mux`／リテラル／`slice`／`concat`、状態なし）の外（`binary`、Bool 入力、レジスタ、インスタンス等）では `checkData` は偽になり、入口は throw する。`pilotK1`（`tlpCplByte`）は `checkComb` が受理せず（§69.0）、S3w が扱う。

### 73.6 残り

- (b) 演算子（and／or／add／shl／sub／lt…）: DeepElab の演算子ごとの `compile_correct` と run 側の lowering 補題を CTerm の意味補題として再利用（`tC`／`ofData` の被覆と `Frag` を広げる）。S3w の `checkCombN`／`FragW` との合流。
- (c) レジスタ（`d.ss ≠ []`）: `ofData` を状態位置・`stepT` をレジスタ文へ一般化し、`Cdo.irState_eq` の帰納の形（t に関する 1 回の帰納）で `DataShowsSeq`（初期値・リセット 0、受理済み freeze と同じ）。
- (d) インスタンス: `RootShowsAt` の call coverage の一般化（`S.portNames` をデータ由来の名前に）、子の `DataShows` が `ChildFn` の連言（k0／k1 は G1 の例）。freeze の構造部分（`designOk`／`topInOk`／`callOk`）の root 定数を外した一般版。
- (e) DeclDenotes: 宣言ごとの生成定理（`machine_result`）が現状。入口で検査するか、既存の `machine_source` 生成器の一般定理にするかは**未決**（coder が reviewer に持ち帰る）。
- 必要 IP baseline（73.5）。
- 新しい TRUSTED は採用していない。`sorry`／`axiom`／`native_decide` なし。

### 73.7 Check60（`kjob lake build Tests.Gen5.FGCircuitPilotCheck60`、exit 0）の出力（Check 自身の行）

- `FGCIRCUIT60 AXIOMS: 20 theorems of the S3y modules (Gen, Entry, this Check), standard axioms only ([Quot.sound, Classical.choice, propext]); checkData_sound depends on [propext, Classical.choice, Quot.sound]; certifiedEntryC_sound depends on [propext, Classical.choice, Quot.sound]; no sorryAx, no Lean.ofReduceBool (no native_decide)`
- `FGCIRCUIT60 CONTROLS: 7 rejections by the general check (…)`; `DataShows` は非自明（`dataValue kd0 inits [1] = 71`、定数関数は偽、変異 module（71→72）は `DataShows` でない）、ガード（偽の検査は成功 run を許さない。誤った design の top の例も）。
- `FGCIRCUIT60 SIGNATURES`: `checkData_sound`（`dataValue` 展開済みの完全型）、`checkData`／`circOk` の展開、`certifiedEntryC_sound` と入口の本体、`k0_childFn'` を独立に書いた型へ型注釈。
- 大きさ（`sizeWithoutSharing`、1 run）: `portsOk_spec` 23,764、`checkData_sound` 38,343、`k0_childFn'` 2,554、`certifiedEntryC_sound` 20,205、`certifiedEntryC_refuses` 2,521。`decide +kernel` の `checkData kd0 pilotK0 = true` は約 2.9 s（elaboration 込み、1 run）。machineData 全体への `decide +kernel` は使っていない。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

### 73.8 S3y2 addendum（レビュア裁定の反映）

土台 `7da2992b`。変更ファイル: `Tools/ShippingFGCircuitS3yGen.lean`、`Tools/ShippingFGCircuitS3yEntry.lean`、`Tests/Gen5/FGCircuitPilotCheck60.lean`。`Sparkle/` と S3z／S3w のファイル、既存定理の文は変更していない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。1 root／1 child の結果は局所的で台帳の減算ではない。

**(裁定 5) 最初の断片の契約を checker に明示**
- `ChildFn`／`dataValue : List Nat → Nat` は**単一出力**。複数出力の IP は**後続の一般化の残件**（出力ごとの値関数）。
- `circOk d` = `circOk0`（状態なし、出力 1 つ、`let`／出力が `Frag`）∧ 各出力の `sortW > 0`。`circOk_spec` が命題に戻す。
- `portsOk d m` = `portsOk0`（ポート数 = 非 domain binder 数、`clk`/`rst` なし、各ポート幅 = binder 幅（順序どおり）、`inputPositions`／`portIdx` の i 番目 = i、出力ポート 1 つ）∧ 非 domain の入力 binder は全て `BitVec n`（`0 < n`）∧ 出力ポート幅 = 出力 sort の幅。`inKindOk`: `.bits n`（`0<n`）のみ。**Bool 入力は拒否**（`Frag` に `boolInput` がなく、未使用の Bool 入力が素通りするのを防ぐ）、幅 0 の入力も拒否。入力 0 個（定数回路）は許す（引数列は `[]`）。`portsOk_spec`／`checkData_contract` が命題に戻す。
- 拒否の kernel 対照（Check60 B2）: Bool 入力、幅 0 入力、余分な入力ポート、入力幅違い、出力ポート 2 つ、出力ポート幅違い、出力リスト空、出力 2 つ、幅 0 の出力。
- 空虚さの対照: `childRange_nonempty`（全データで全 0 の引数列が範囲内。範囲が空になるデータは存在しない）、`kd0` で `[1]` が範囲内（`k0_range_one`）、通る検査の出力リストは非空（`checkData_contract`）、`dataValue kd0 … [1] = 71`、誤った値関数は `ChildFn pilotK0` を満たさない（`wrong_value_fails`: `f [1] ≠ 71` なら偽、`dataShows_k0_succ_fails`: 値 +1 は偽、`flip_not_dataShows`）。

**(裁定 1) 文言**: G1／G2 について「hr 不要」とは記録しない。G1 は run を含まない data／module の文、**G2 は run の成功（`RunsTo (certifiedEntryC …) … (b, D) w'`）を前提に使う**。`readData` が成功 run を持たなければ `certifiedEntryC` も持たない（`certifiedEntryC_no_read`、新規）。検査が偽なら成功 run はない（`certifiedEntryC_refuses`）。

**(裁定 2) 文言**: §73.1 の「SrcEq／ChildFn／環境照合」の文はデータ対 IR の範囲に限定した。G2 は `readData` が返す `d` が宣言のデータであること、元の Lean 宣言と同じ run の `readData` 一致・意味保存を**証明しない**（DeclDenotes、S3z）。`MachineData`＋`typedVal`（`dataValue`）は中間意味であり、FG の最終ソース（元 Lean の Signal）ではない。最終の接続定理では DeclDenotes を供給する。

**(裁定 6)** §73.4 は**未接続一覧**として維持。「候補」表記を除き、どの行も外していない。FG 全体の結論までの橋と必要 IP の受入は別の完了条件。

Check60（`kjob lake build Tests.Gen5.FGCircuitPilotCheck60`、exit 0）の行: `FGCIRCUIT60 AXIOMS: 34 theorems of the S3y modules (Gen, Entry, this Check), standard axioms only`、`FGCIRCUIT60 CONTRACT: …`（新規）。大きさ（`sizeWithoutSharing`）: `portsOk_spec` 12,399、`circOk_spec` 8,737、`checkData_contract` 15,581、`checkData_sound` 40,247、`certifiedEntryC_sound` 20,205、`certifiedEntryC_refuses` 2,521、`certifiedEntryC_no_read` 1,529。`checkData kd0 pilotK0 = true` の `decide +kernel` は約 2.8 s（1 run）。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。
