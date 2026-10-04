# Serre–Markov Lean: 完成版引継ぎ

2026-10-04、回収後の再開確認。

現在のプロジェクトは `/workspace/scratch/41606fe60bc9/lean-project`。Lean 4.24.0 / mathlib v4.24.0。Git管理ではない。配布ZIPはソース・依存固定ファイル・再生成用コード・検証ログを含む。配布Lean本体と依存キャッシュは含めない。

`SerreMarkov.lean` は `FullClassification` を import する。標準 `lake build` と依存公理監査を再実行し、3470 jobs、8286定理宣言、1232定義等で成功した。宣言数には自動生成補助宣言を含む。許可公理は `propext`, `Classical.choice`, `Quot.sound` のみ。

主な入口は `SerreMarkov/FullClassification.lean`。`full_classification`、`canonical_orbit_map_bijective`、`all_forgetful_fibers_finite`、`prime_square_power_unique_representative`、`finite_fibers_and_unbounded`、`mutationEquivalentTest_correct`、`latticeEquivalentTest_correct` を参照する。

通常環境では `lake exe cache get` の後に `./scripts/verify.sh`。大きな証明書を順にチェックする。キャッシュ済みなら `lake build` で標準ターゲットと監査を確認できる。小さい実行例は `lake env lean -j2 scripts/decision_examples.lean`。

Work環境の実行ファイル探索補正は `tooling/ENVIRONMENT.md`。通常環境では不要。

詳細な数学・証明経路・依存関係は `blueprint/README.md` から辿る。日本語LuaLaTeX PDF、標準Lean Blueprint HTML、宣言のソース行へのリンク、Blueprint固有の宣言・公理監査を同梱する。再生成してから `scripts/package_verified.py` で配布物を更新する。

回収時の `recovery/STATUS.md`、`GAPS.md` は過去の確認状態を記録した資料である。現在の確認状態は本ファイル、`STATUS.md`、`STATUS_ja.md` と新しい検証ログを使う。原稿の主結論は別の直接代数証明で形式化した。原稿の全補題・元の幾何的証明・dg付録の逐語的形式化ではない。
