# 公開手順と最終確認

このパッケージは公開準備版です。GitHub での CI と公開はまだ実行していません。

## 採用する形

一つの public repository に固定済み Lean ソース、証明書、Blueprint ソース、再生成手順を置きます。main に push すると、同じ commit で Lean 全体・公理監査・Blueprint 宣言監査・依存構造を検証し、HTML と LuaLaTeX PDF を再生成してリンクを検査します。全段階が成功した場合のみ Pages に配置します。Pull request では検証のみ行います。

Pages には Blueprint 本文、依存グラフ、Lean 宣言のソース行リンク、PDF、検証資料、commit 情報を公開します。成功バッジは実際の CI 成功後に追加します。既存ログは過去の確認記録であり、新しい CI が通ったという意味ではありません。

## 公開前に記入する情報

1. GitHub の OWNER と REPO（推奨名 serre-markov-lean）。
2. 著者・貢献者の正式表記。CITATION.cff の植田一石/Kazushi Ueda は確認用の案です。共同著者があれば追加します。
3. ライセンスは MIT（自作コード）＋CC BY 4.0（解説本文）で指定済みです。LICENSE に範囲、LICENSES/ に全文を収録しました。
4. 原論文への正式リンク。原稿全文はこの添付物に含まれないため、新たに同梱していません。

## GitHub への登録

ZIP を展開して serre_markov_lean に入ります。README に案内が必要なら、公開 URL が決まってから追記します。

```bash
git init
git add .
git commit -m "Prepare Serre-Markov formalization and Blueprint publication"
git branch -M main
git remote add origin https://github.com/uedakazushi/serre-markov-lean.git
git push -u origin main
```

GitHub の Settings → Pages → Source を GitHub Actions にします。Actions の Verify and publish を確認してください。初回検証は巨大な証明書のため長時間かかりえます。350 分で打ち切る設定で、時間・メモリ不足なら大きい runner で検証します。失敗した段階を調べ、検証を省略して公開しないでください。

成功後の URL は https://uedakazushi.github.io/serre-markov-lean/ です。本文、グラフ、宣言リンク、PDF、日本語表示を実際のブラウザで確認します。カスタムドメインやユーザー Pages は URL が異なります。

## 初回 Release

初回 CI と実サイト確認後に v0.1.0 などの版をタグ付けし、GitHub Release にソース ZIP、Blueprint PDF、検証資料を添付します。タグは成功した commit に付けます。Zenodo 等で DOI を取得する場合は、その確定 DOI を CITATION.cff に追加し、引用対象の版を明記します。以後は release と進行中の main を区別します。

ブランチ保護で verify を必須にすると、変更後の検証漏れを防げます。公開版の workflow は、初回稼働確認後に利用 Actions と Elan 導入スクリプトを確認済み commit SHA に固定すると、依存の更新を管理しやすくなります。

## この環境で確認したこと

Lean の数学ソースは変更していません。元 ZIP に成功したビルド・公理監査記録があることを確認しました。今回の環境には lake がなく、Lean 再コンパイルと GitHub Actions の実行は未確認です。構造検査、HTML リンク検査、配信用ステージ作成は PUBLICATION_CHECKS.json に記録します。

## 指定済み公開先

https://github.com/uedakazushi/serre-markov-lean （現在 private）。GitHub の既存チェックポイントを保持した別ブランチで添付版を取り込みます。レビュー・CI成功後に main に統合し、Settings で public に切り替えます。Pages の有効化も GitHub の設定で行います。

生成 HTML/PDF はリポジトリでは追跡せず、CI が作って artifact と Pages に渡します。ZIP には元の閲覧用成果物を保持しています。MathJax 3.2.2 は CI で取得し、元配布物の全ファイルの SHA256 と一致することを確認してから同梱します。これにより閲覧時の外部 CDN を不要にします。
