# Serre–Markov Lean 回収・引継ぎ

2026-10-04。今回の権限は回収・保存・状態確認だけ。新しい証明・定理文の弱化・原稿の数学的変更は行っていない。

## 現在地

- プロジェクト: `/workspace/scratch/41606fe60bc9/lean-project`
- Git リポジトリではない（git status は not a git repository）。コミットによる作業履歴は存在しない。
- 原稿: `paper/serre_markov_20261004_v4/paper/serre_markov_ja.tex` と PDF。
- Lean 4.24.0、mathlib v4.24.0。正確な依存は `lean-toolchain` と `lake-manifest.json`。

## 回収物

- `serre_markov_recovered_sources.tar.gz`: 既存782ファイル。プロジェクト全ソース、標準 import 外の未確認ファイル、試験ソース、探索コード、原稿、入力ZIP、既存ログを保存。
- `serre_markov_compiled_checkpoint.zip`: プロジェクト自身のコンパイル済み成果。配布Lean本体・依存キャッシュを含めない。復元時は同じバージョンを使う。
- `FILE_INVENTORY.json` / `.md`: 全回収ファイルのパス・サイズ・SHA-256。依存配布物は作成成果として数えていない。git履歴がないため、各ファイルの作成者・作成か編集かは厳密には特定できない。
- `DECLARATIONS.json` / `.md`: 全作業ソースの Definition / Lemma / Theorem 等の名前と位置。ソース宣言一覧であり認証一覧とは区別。
- `COMPILED_SOURCE_DECLARATIONS.json`: 標準ビルドの import closure 内のソース宣言4682件。
- `VERIFIED_THEOREMS.txt`: カーネル公理監査が確認した8059定理宣言（自動生成補助定理を含む）。
- `DEFAULT_BUILD_FILES.txt`: 標準ビルドの342ソース。
- `OUTSIDE_DEFAULT_BUILD.txt`: 標準ビルド外の10モジュール。
- `PAPER_MAP.md`, `STATUS.md`, `GAPS.md`: 原稿対応・確認結果・残課題。
- `PLACEHOLDERS.json`: コメントと文字列を除外した sorry/admit/axiom 等の検査結果。
- `probe-logs`, `PROBE_CHECKS.json`: 作業用 Lean ファイルの個別再確認。
- `HISTORICAL_ERRORS.json`: 既存ログの過去エラー。現在の失敗と混同しない。

## 最後に確実に成功したチェックポイント

今回の `lake build`、exit 0、3460 jobs。`lake-build-current.log` の末尾に8059定理・1118定義等の監査成功を記録。許可公理は propext, Classical.choice, Quot.sound のみ。

旧記録では `full-build-sorted-four.log` に8021定理・1112定義等、3457 jobs の成功がある。今回の方が新しい確認。

## 再現コマンド

普通の Elan 環境ではプロジェクトで `lake exe cache get` の後に `lake build`。`scripts/verify.sh` は標準ビルド外の大きな証明書と FullClassification も対象にするため、標準ビルドとは検証範囲が違う。

現在環境では:

```sh
cd /workspace/scratch/41606fe60bc9/lean-project
export SERRE_MARKOV_LEAN_ROOT=/workspace/scratch/41606fe60bc9/lean-runtime-test/lean-4.24.0-linux
export SERRE_MARKOV_PROC_SELF_FIX=1
./tooling/with_lean.sh lake build
```

PID namespace と /proc の不一致を shim で回避する。詳細は `tooling/ENVIRONMENT.md`。これは Lean の論理を変更するものではない。

## 次の担当者への制限

新しい形式化を始めない。ユーザーの再開指示があるまで成果保存と現状確認だけを行う。FullClassification のソースがあるだけで主定理形式化完成と報告しない。未完のソースを削除せず、定理の前提も変更しない。

定義等の完全なカーネル宣言名一覧: VERIFIED_DEFINITIONS.txt（1118件）。追加の DefaultDeclarationAudit の再実行も exit 0、公理監査成功。これは監査だけで新しい数学的定理を追加していない。
