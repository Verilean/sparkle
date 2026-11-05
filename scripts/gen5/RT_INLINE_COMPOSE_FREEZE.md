# RT inline compose freeze: `userInliner` の `NoPh ∧ BvarLt 0` 保存と inline 枝・`entryConst` の `ShapeInputs'`

Issue: `sparkle-rt-inline-compose`（親 `sparkle-gen5-dg-readertrace`）。base: `par/rt-int1` 6af6f9f6、作業ブランチ `kjob/rt44`（探索ブランチ）。調査: `scripts/gen5/RT_INLINE_SURVEY.md` §1.5、`RT_INLINE_P1_FREEZE.md`、`RT_ABBREV_S1_FREEZE.md`。
**台帳: FG 103（U1 −3 は受理待ちで FG 100）/ T1 56（今回 FG -0 +0 / T1 -0 +0）。** 新しい台帳前提は足さない（下の §1）ので reviewer には出さない。

## 1. 前提の扱い

* 取るだけの仮説（`Tools/Assume/` には登録しない）:
  * `DeclValuePh env`（既存 N1-a の候補）、`ReplaceAgrees`（U-1）、`HeadBetaAgrees0`（U-2）: S1 で既に freeze 済みの文。
  * `PassPh env`: S2 の葉 `pass_ph`（別 Issue `sparkle-rt-pass-total`）。`MachRecUnfold.pass` が `NoPh ∧ BvarLt 0` を保つ文を、`DeclValuePh env → RecRulePh env →` の下で言う仮説。
  * `RecRulePh env`: 別 Issue `sparkle-rt-recrule` の freeze 待ち。ここでは同 Issue の候補文（survey §1.4）を仮置きで定義するだけで、あちらの freeze が出たら定義を差し替える（名前の衝突に注意）。
* 上の 2 つ（`PassPh`、`RecRulePh`）が、この単位で新しく名前の出る前提の全部。台帳への加算・付け替えは別 Issue 側の判断であり、この文書では数えない（今回 0/0）。
* 範囲外: ユーザー承認が要る全域化、`GenWF` の強化、FG の縮小、共有定義・コンパイラの編集。

## 2. 完全型

scratch（`set_option autoImplicit false`、新規ファイルを import して `#check`）の出力を写したもの。名前空間は `Tools.ShippingGen5ReaderTrace`。

```
RecRulePh : Lean.Environment → Prop
PassPh : Lean.Environment → Prop
inl_step_ph : ∀ (env : Lean.Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env →
    ∀ (e : Lean.Expr),
      NoPh e = true →
        BvarLt 0 e = true →
          NoPh
                (match
                  Sparkle.Compiler.Elab.inlineDefs (Sparkle.Compiler.Elab.userDefinition? env)
                    (Sparkle.Compiler.Elab.userProjection? env) Sparkle.Compiler.Elab.inlineDepth e
                    Sparkle.Compiler.Elab.inlineBudget with
                | some (e', snd) => e'
                | none => e) =
              true ∧
            BvarLt 0
                (match
                  Sparkle.Compiler.Elab.inlineDefs (Sparkle.Compiler.Elab.userDefinition? env)
                    (Sparkle.Compiler.Elab.userProjection? env) Sparkle.Compiler.Elab.inlineDepth e
                    Sparkle.Compiler.Elab.inlineBudget with
                | some (e', snd) => e'
                | none => e) =
              true
rounds_ph : ∀ (env : Lean.Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env →
    RecRulePh env →
      PassPh env →
        ∀ (inl : Lean.Expr → Lean.Expr) (isRec : Lean.Name → Bool),
          (∀ (e : Lean.Expr), NoPh e = true → BvarLt 0 e = true → NoPh (inl e) = true ∧ BvarLt 0 (inl e) = true) →
            ∀ (k : Nat) (e : Lean.Expr),
              NoPh e = true →
                BvarLt 0 e = true →
                  NoPh (Sparkle.Compiler.Elab.userInliner.rounds env inl isRec k e) = true ∧
                    BvarLt 0 (Sparkle.Compiler.Elab.userInliner.rounds env inl isRec k e) = true
userInliner_ph : ∀ (env : Lean.Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env →
    RecRulePh env →
      PassPh env →
        Tools.Assume.AbbrevExtern.ReplaceAgrees →
          Tools.Assume.AbbrevExtern.HeadBetaAgrees0 →
            ∀ (e : Lean.Expr),
              NoPh e = true →
                BvarLt 0 e = true →
                  NoPh (Sparkle.Compiler.Elab.userInliner env e) = true ∧
                    BvarLt 0 (Sparkle.Compiler.Elab.userInliner env e) = true
inlinedConst_defn_ph : ∀ (env : Lean.Environment),
  Tools.Assume.EnvDeclValue.DeclValuePh env →
    RecRulePh env →
      PassPh env →
        Tools.Assume.AbbrevExtern.ReplaceAgrees →
          Tools.Assume.AbbrevExtern.HeadBetaAgrees0 →
            ∀ (c : Lean.Name) (ci0 : Lean.ConstantInfo),
              env.find? c = some ci0 →
                ∀ (d : Lean.DefinitionVal),
                  Sparkle.Compiler.Elab.inlinedConst (Sparkle.Compiler.Elab.userInliner env) ci0 =
                      Lean.ConstantInfo.defnInfo d →
                    NoPh d.value = true ∧ BvarLt 0 d.value = true
shapeInputs_of_decl' : Tools.Assume.N3Extern.ZeroLitAgrees0 →
  Tools.ShippingLetsReaderInv.LiftAgrees →
    Tools.ShippingLetsReaderInv.Inst1Agrees →
      ∀ (env : Lean.Environment) {ci : Lean.ConstantInfo},
        (∀ (d : Lean.DefinitionVal),
            ci = Lean.ConstantInfo.defnInfo d → NoPh d.value = true ∧ BvarLt 0 d.value = true) →
          Tools.Assume.PackTupleBridge.PackTupleInputsBridge →
            Tools.Assume.NormNodePh.RawNodePh (Sparkle.Compiler.Elab.structEnv env) →
              Tools.Assume.NormNodePh.NormNodePh (Sparkle.Compiler.Elab.structEnv env) →
                ∀ {sm : Bool} {ps : List (String × Nat)} {n : Nat},
                  ShapeInputs' (nDeclOfCi ci) (Sparkle.Compiler.Elab.structEnv env) sm ps ci n
shapeInputs_of_inline' : Tools.Assume.N3Extern.ZeroLitAgrees0 →
  Tools.ShippingLetsReaderInv.LiftAgrees →
    Tools.ShippingLetsReaderInv.Inst1Agrees →
      ∀ (env : Lean.Environment),
        Tools.Assume.EnvDeclValue.DeclValuePh env →
          RecRulePh env →
            PassPh env →
              Tools.Assume.AbbrevExtern.ReplaceAgrees →
                Tools.Assume.AbbrevExtern.HeadBetaAgrees0 →
                  ∀ {c : Lean.Name} {ci0 : Lean.ConstantInfo},
                    env.find? c = some ci0 →
                      ∀ {ci : Lean.ConstantInfo},
                        ci = Sparkle.Compiler.Elab.inlinedConst (Sparkle.Compiler.Elab.userInliner env) ci0 →
                          Tools.Assume.PackTupleBridge.PackTupleInputsBridge →
                            Tools.Assume.NormNodePh.RawNodePh (Sparkle.Compiler.Elab.structEnv env) →
                              Tools.Assume.NormNodePh.NormNodePh (Sparkle.Compiler.Elab.structEnv env) →
                                ∀ {sm : Bool} {ps : List (String × Nat)} {n : Nat},
                                  ShapeInputs' (nDeclOfCi ci) (Sparkle.Compiler.Elab.structEnv env) sm ps ci n
shapeInputs_of_entryConst' : Tools.Assume.N3Extern.ZeroLitAgrees0 →
  Tools.ShippingLetsReaderInv.LiftAgrees →
    Tools.ShippingLetsReaderInv.Inst1Agrees →
      ∀ (env : Lean.Environment),
        Tools.Assume.EnvDeclValue.DeclValuePh env →
          RecRulePh env →
            PassPh env →
              Tools.Assume.AbbrevExtern.ReplaceAgrees →
                Tools.Assume.AbbrevExtern.HeadBetaAgrees0 →
                  ∀ {c : Lean.Name} {ci0 : Lean.ConstantInfo},
                    env.find? c = some ci0 →
                      ∀ (certifiedFrontEnd symbolicMode : Bool) (parameters : List (String × Nat))
                        (isInst : Lean.Expr → Bool) (projs : Sparkle.Compiler.Elab.StructEnv),
                        Tools.Assume.PackTupleBridge.PackTupleInputsBridge →
                          Tools.Assume.NormNodePh.RawNodePh (Sparkle.Compiler.Elab.structEnv env) →
                            Tools.Assume.NormNodePh.NormNodePh (Sparkle.Compiler.Elab.structEnv env) →
                              ∀ {sm : Bool} {ps : List (String × Nat)} {n : Nat},
                                ShapeInputs'
                                  (nDeclOfCi
                                    (Sparkle.Compiler.Elab.entryConst certifiedFrontEnd symbolicMode parameters ci0
                                      isInst (Sparkle.Compiler.Elab.userInliner env) projs))
                                  (Sparkle.Compiler.Elab.structEnv env) sm ps
                                  (Sparkle.Compiler.Elab.entryConst certifiedFrontEnd symbolicMode parameters ci0 isInst
                                    (Sparkle.Compiler.Elab.userInliner env) projs)
                                  n
```

`rounds_ph` は `userInliner` 内の局所 `rounds`（`userInliner.rounds env inl isRec k e`）についての一般形で、`inl` が保存すれば成り立つ。`userInliner_ph` はそれを `inl := inlineDefs …`（P1 の `inlineDefs_user_ph`）で具体化する。

## 3. 証明方針

* `rounds_ph`: `k` の `Nat` 帰納。`k+1`: `e' := pass …`、`PassPh` で `Good e'`。`if e' == e` の両腕: 真なら `e`、偽なら IH + `hinl`。
* `userInliner_ph`: `inl_step_ph` で `e1`。`relevantClosure` の `Bool` の場合分け: 真は `rounds_ph`、偽は `e1` のまま。続いて `inlAbbrevs_ph`（S1）と `inlFoldNat_ph`。
* `inlinedConst_defn_ph`: `ci0` で場合分け。`.defnInfo d0` なら `d.value = userInliner env d0.value`、`DeclValuePh` で `d0.value` が `NoPh ∧ BvarLt 0`。他は矛盾。`type` は `ShapeInputs'` の入力に現れない（survey §0）。
* `shapeInputs_of_decl'`: `shapeInputs_of_direct'`（Direct2）の本体のうち、`hdecl` を直接取る形。
* `shapeInputs_of_inline'`: `inlinedConst_defn_ph` で `hdecl` を作り `shapeInputs_of_decl'`。
* `shapeInputs_of_entryConst'`: `entryConst` の `if` で場合分け。`ci0` のまま（直接枝: `DeclValuePh` から `hdecl`）か `inlinedConst`（inline 枝）。

## 4. 主張しないこと

* 仮説（`DeclValuePh`、`ReplaceAgrees`、`HeadBetaAgrees0`、`PassPh`、`RecRulePh`）が受理されるソースで成り立つことは示さない。条件付き・中間結果。
* sorry を含む間は受理・台帳に数えない。mutant を使う場合は signature / defeq での棄却で、意味的反例ではない。
