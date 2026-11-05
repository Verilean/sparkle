# AUDIT U-A2 freeze（B-AUD: E-6 `hF` を A.P-06 と C.CV-4 から）

Issue: `sparkle-aud-ua2`（親 `sparkle-audit-carrier`）。base: `par/aud-ua1` 0d979146。docs only。リポジトリの Lean ソースは編集していない（scratch のみ）。
読んだもの: `scripts/gen5/AUDIT_CARRIER_FREEZE.md`（§2 AuditE6、§4 U-A2）、`Tools/ShippingGenFGLedgerPremises.lean`（`h_C_CV4`, `h_A_P06`）、`Tools/ShippingMachineEntry.lean:2345`（`MachineDefines`）、`Tools/ShippingGen5NameKids4.lean`、`Tools/ShippingEntryReadsLinked.lean`（`core_chain`）、`Tools/ShippingGen5FG.lean`（`EntryWitness`）。
「見つからなかった」は、この調査では供給元・経路が見つからなかったという意味で、不可能・導出不能とは書かない。mutant は使っていない。
新しい前提・law・TRUSTED 境界・FG/保証の変更は提案しない（run 存在は §3 で前提候補として明示するだけで、置くかは reviewer/ユーザーの承認後）。
台帳: FG 102 / T1 56（今回 0/0）。

## 0. 結論（先に）
1. `h_C_CV4` の固定値 `false [] true` と `hF` の `sm ps ai` は **一致する**。`MachineDefines` の結論は `machineShape? false [] E senv = some shape` で、`h_C_CV4` の仮定部分と同じ `false []`。`hF` は `∃ n sm ps ci senv ai` なので `sm := false, ps := [], ai := true, ci := entryConst …, senv := structEnv envR'` と取れる。範囲を絞る必要はない（scratch で証明まで通した、§2）。
2. scratch で次が sorry なし（公理は標準 3 つのみ）で elaborate できた: `hF`（= `AuditE6 P Reach`）は、`h_C_CV4`、`h_A_P06`（の `Reach` 上の形）、および「3 つの run の存在」`RunsExistAt` から出る。
3. 3 つの run の存在: **top（`declName`）の分は A.P-04 の run（`EntryWitness`、`parameters = []` の枝）と `Start` から証明できた**（`core_chain`、scratch、sorry なし）。**top 以外の到達宣言 `c` の分は、この調査では供給元・経路が見つからなかった**。よって新しい前提の候補が +1（`RunsExistAt` の非 top 版、1 本の閉じた命題）。U-A1 の −4 とは相殺しない。
4. 台帳の見込み（受理後）: E-6 は消える（FG −1）が、非 top の run 存在が +1 なら FG の正味は 0。U-A1 の −4（条件付き）は別に数える。

## 1. hF の完全型
`autoImplicit false` で elaborate。`#check` の出力を写した:
```
@AuditE6 : {ι : Type} → {dom : ι → Sparkle.Core.Domain.DomainConfig} → Pkgs ι dom → (Name → Prop) → Prop
```
本体（U-A1 の `Tools/ShippingGen5AuditUA1.lean` と同じ。再掲）:
```lean
def AuditE6 : Prop :=
  ∀ c, Reach c → ∀ sp, SOf P c = some sp →
    ∃ (n : Nat) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo)
      (senv : StructEnv) (ai : Bool),
      Tools.ShippingReaderFuel.machineShapeF n sm ps ci senv ai = some (some sp)
```

## 2. hF を出す定理の完全型（scratch で elaborate、証明つき）
`#check @auditE6_of_defines` の出力:
```
@auditE6_of_defines : ∀ {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
  {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop),
  CV4Stmt →
    (∀ (c : Name), Reach c → ∀ (q : Pkg ι dom), P c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape) →
      (∀ (c : Name), Reach c → (P c).isSome = true → RunsExistAt L c) → AuditE6 P Reach
```
`#print axioms`: `[propext, Classical.choice, Quot.sound]`。第 1 仮定 `CV4Stmt` は `h_C_CV4` の束縛の本文そのもの（`∀ E senv sp, machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)`）。第 2 仮定は `h_A_P06` を `Reach` 上に置いた形（FG の `Reach := TgtRun …` を一般の `Reach` にしただけで、他は同文）。第 3 仮定が §3 の run 存在。
証明の筋: `P c = some q` から `sp = q.d.shape`、`RunsExistAt` の run を `h_A_P06` に渡して `machineShape? false [] … = some sp`（`MachineDefines` の第 3 成分）を得て、`h_C_CV4` に渡し、`⟨n, false, [], _, _, true, hn⟩`。
定義（scratch）:
```lean
def CV4Stmt : Prop := ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
  machineShape? false [] E senv = some sp →
  ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp)

def RunsExistAt (L : Laws mref cref) (c : Name) : Prop :=
  ∃ (mctx' : Meta.Context) (cctx' : Core.Context),
    Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' ∧
    ∃ (w1 : Void IO.RealWorld) (ci : ConstantInfo) (w2 w5 : Void IO.RealWorld) (envR : Environment)
      (w6 w7 : Void IO.RealWorld) (envR' : Environment) (w8 : Void IO.RealWorld),
      RunsTo (getConstInfo c) mctx' mref cctx' cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx' mref cctx' cref w5 envR w6 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx' mref cctx' cref w7 envR' w8
```
一致の確認: `MachineDefines` の第 3 成分は `machineShape? false [] (entryConst …) (structEnv envR') = some shape`。`h_C_CV4` は `machineShape? false [] E senv` を仮定に取る。`sm = false`、`ps = []` が両方で同じなので `h_C_CV4` がそのまま適用でき、`ai = true` は `h_C_CV4` の結論の固定値で、`hF` が `ai` を存在量化しているので支障がない。別の `(sm, ps)` の宣言（`parameters ≠ []` の枝など）には `h_C_CV4` は適用しない。ただし `MachineDefines` 自体が `false []` 固定なので、`hF` を `MachineDefines` から作る限りこの範囲は変わらない。

## 3. 3 つの run（getConstInfo, getEnv×2）の存在: 新しい前提になるか
`MachineDefines` は「任意の run について」の形（`∀ w1 ci w2 … , RunsTo … → …`）なので、結論を使うにはその run が存在すると示す必要がある。
| 対象 | 結果 | 根拠 |
|---|---|---|
| top（`declName`）、`parameters = []` の枝 | **導出できた** | scratch の `runsExist_top`（sorry なし、標準公理のみ）: `EntryWitness` の run `synthesizeCombinational declName` に `synthesizeCombinational_parts` と `ShippingEntryReadsLinked.core_chain` を当てて `getConstInfo declName` と `getEnv` の run を得る。context は `Start` の `AdmCtx`。2 つ目の `getEnv` は 1 つ目の run を再利用（`MachineDefines` は 3 run を独立に量化するので同じ run を渡してよい） |
| top、`synthesizeCombinationalWithParameters` の枝 | この調査では未確認 | `core_chain` は `[] false` の Core 用。パラメータ付きの Core の run は調べていない |
| 到達した非 top の `c`（`TgtRun` の呼び出し先） | **供給元・経路がこの調査では見つからなかった** | 呼び出し先の run は親の run の中で `RealChild` として現れる（`entryLink_real` は `RealChild mref cref c y` から run を取り出す）。しかし「`TgtRun` で到達した `c` に `RealChild` が存在する」という補題は見つからなかった。`DG-ENV` の `ReadsAt` / C0（C.EN-6）という名前の定義は base の `Tools/` に見つからなかった。`EnvAt`（`ShippingEnvRead`）は「どの getEnv run も `envP` を返す」で、run の存在は言わない |
判定: 非 top の分は **新しい前提の候補として +1**（`RunsExistAt L c` を `TgtRun` 上の非 top の `c` に対して置く 1 本の閉じた命題）。U-A1 の −4 とは相殺しない。run の存在は `getConstInfo c` が成功すること（`c` が環境にあること）も含むので、DeclConnect / 環境の側から出せる可能性はあるが、その経路はこの調査では見つからなかった。
選択肢（reviewer の判断）:
- (a) +1 として置く（`h_A_P06` の隣に `RunsExistAt` の非 top 版を 1 行）。
- (b) 別 Issue で `RealChild` の存在（親の run が呼び出し先を実際にコンパイルする）を run の定義から導く単位を作る。結果が出れば +1 は 0 に戻る。
- (c) `h_A_P06` を「run が存在するなら」の形で既に読んでいるなら、`hF` 側の仮定を `∀ run` 形に変えて run 存在を要らなくする案: ただし `hF` は存在量化（`∃ n …`）なので、run が存在しない `c` では供給できない。この案は `AuditE6` の型の変更（承認済みの文の変更）になるので、ここでは採らない。

## 4. 台帳
- 消える行: **E-6**（`hF`）。ただし条件は「`h_C_CV4`・`h_A_P06` が既存行のまま」「`RunsExistAt` が供給される」。
- 増える行: 非 top の `RunsExistAt` が +1（上記 (a) の場合）。(b) で導出できれば 0。
- 台帳: FG 102 / T1 56（今回 FG -0 +0 / T1 -0 +0）。条件付き台帳（受理後の見込み）: FG −1 +1（E-6 −1、run 存在 +1）で正味 0。U-A1 の −4 は別の見込み。T1 は変えない（`h_C_CV4` は FG 側の行、T1L-43 と同じ前提と台帳が書くが、この単位は数を動かさない）。
- E0 の 4 条件:
  1. 出力（`CV4Stmt`、`RunsExistAt`、`auditE6_of_defines`、`runsExist_top`）を後続が使う: U-A3 以降が `AuditE6` を使う。後続 Issue の登録は他 Issue の状態を変えない規則のため未実施（承認後）。
  2. 消える行 ID: E-6。見込み差分: FG −1 +1。
  3. 後続の最初の 1 単位の freeze を 1 往復以内に出す: 実装単位 U-A2-impl（`auditE6_of_defines` と `runsExist_top` の 2 定理、新規 Lean 1 ファイル 約 40 行）は scratch で証明済みなので、承認後すぐ出せる。
  4. 新しい前提が増えるならその数を減算見込みと並べる: 増分 +1（非 top の run 存在）、この単位の減算見込み −1。**正味 0 で、E0 の「見込みが増分より大きい」を満たさない**。(b) が成功すれば満たす。したがって E0 の例外としては主張しない。

## 5. 主張しないこと
`h_C_CV4` の充足（C.CV-4 の供給元）、`h_A_P06` の供給、非 top の run 存在の供給、`parameters ≠ []` の枝、FG・T1・M5 の完了は主張しない。示したのは、上記 3 仮定から `AuditE6` が出ることと、`h_C_CV4` の固定値が一致することだけ。

## 付録: scratch の全文（`kjob lake env lean`、ソースツリー外）
```lean
import Tools.ShippingGen5AuditUA1
import Tools.ShippingEntryReadsLinked
set_option autoImplicit false
namespace Tools.ShippingGen5AuditCarrier
open Lean Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5FG
open Tools.ShippingEntrySoundness (RunsTo)
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig}
  {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- the h_C_CV4 binder body (C.CV-4) -/
def CV4Stmt : Prop := ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
  machineShape? false [] E senv = some sp →
  ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp)

/-- the three runs of MachineDefines at c, in one admissible context -/
def RunsExistAt (L : Laws mref cref) (c : Name) : Prop :=
  ∃ (mctx' : Meta.Context) (cctx' : Core.Context),
    Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' ∧
    ∃ (w1 : Void IO.RealWorld) (ci : ConstantInfo) (w2 w5 : Void IO.RealWorld) (envR : Environment)
      (w6 w7 : Void IO.RealWorld) (envR' : Environment) (w8 : Void IO.RealWorld),
      RunsTo (getConstInfo c) mctx' mref cctx' cref w1 ci w2 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx' mref cctx' cref w5 envR w6 ∧
      RunsTo (Lean.getEnv : MetaM Environment) mctx' mref cctx' cref w7 envR' w8

theorem auditE6_of_defines (L : Laws mref cref) (P : Pkgs ι dom) (Reach : Name → Prop)
    (h_C_CV4 : CV4Stmt)
    (h_A_P06 : ∀ c, Reach c → ∀ q : Pkg ι dom, P c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
        Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hrun : ∀ c, Reach c → (P c).isSome = true → RunsExistAt L c) :
    AuditE6 P Reach := by
  intro c hc sp hS
  simp only [SOf] at hS
  cases hP : P c with
  | none => rw [hP] at hS; cases hS
  | some q =>
    rw [hP] at hS
    have e : q.d.shape = sp := Option.some.inj hS
    subst e
    obtain ⟨mctx', cctx', hadm, w1, ci, w2, w5, envR, w6, w7, envR', w8, r1, r5, r7⟩ := hrun c hc (by simp [hP])
    obtain ⟨-, -, hm⟩ := h_A_P06 c hc q hP mctx' cctx' hadm w1 ci w2 w5 envR w6 w7 envR' w8 r1 r5 r7
    obtain ⟨n, hn⟩ := h_C_CV4 _ _ _ hm
    exact ⟨n, false, [], _, _, true, hn⟩


/-- top entry (parameters = []): runs from EntryWitness -/
theorem runsExist_top (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop) (L : Laws mref cref)
  (declName : Name) (mctx : Meta.Context) (cctx : Core.Context) (w w' : Void IO.RealWorld)
  (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design)
  (hst : Start L mctx cctx w)
  (hrun : RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w') : RunsExistAt L declName := by
  obtain ⟨M, D₁, w1, hcore, -, -⟩ := Tools.ShippingGateChildComb.synthesizeCombinational_parts hrun
  obtain ⟨s, w1, envR, ci, w2, w3, w4, -, hg, he, -, -⟩ := Tools.ShippingEntryReadsLinked.core_chain hcore
  exact ⟨mctx, cctx, hst.1, _, ci, _, _, envR, _, _, envR, _, hg, he, he⟩
end Tools.ShippingGen5AuditCarrier
```
