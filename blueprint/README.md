# Serre–Markov 分類の Lean Blueprint

整数六つ組の分類について、定義、証明経路、数学的な依存関係、検証済みの
Lean 宣言の対応を説明する。対象は日本語原稿 v4 であり、主分類・格子同型・
全忘却ファイバー・停止する判定手続きを扱う。原稿の全補題や元の双曲幾何の
証明、dg 圏の実現付録まで形式化したという意味ではない。

HTML は `web/index.html`、PDF は `print/print.pdf`、LuaLaTeX 原稿は `src/print.tex` である。
宣言リンクは同梱の Lean ソースの該当行を開く。HTML のチェック印は、その
宣言と証明が形式化済みであることを示し、日本語の説明文を別途機械検証した
という意味ではない。

## 検証した対応と依存関係

本 Blueprint は 163 個の実在する Lean 宣言を 165 箇所で参照する。
`verification/lean_references.json` は、コンパイル済み環境での宣言の実在、
元モジュール、宣言行、ソースハッシュ、公理依存の検査結果を記録する。
推移的な公理依存として許可するのは `propext`、`Classical.choice`、
`Quot.sound` だけである。

数学的な節点は **65 個**である。TeX に明示した依存を重複なく数えると
**182 辺**となり、全ラベル・参照・依存先の存在と非循環性を検査している。
`verification/structure.json` に完全な辺集合を保存する。

HTML の依存グラフでは標準プラグインが推移的に冗長な辺を省くため、表示は
同じ **65 節点・113 辺**である。元の 182 辺はすべて表示グラフの経路で
再現され、表示グラフに元の辺集合以外の直接辺はない。これは本文で選んだ
数学的依存の表示であり、Lean コンパイラが生成する全補助宣言の依存グラフ
ではない。

依存グラフには、各ノードから定義・定理へ移動できる静的 SVG も含める。
対話グラフの表示が完了すると静的表示を隠す。MathJax とソース案内の
JavaScript は同梱するため、閲覧時に外部 CDN への接続は不要である。

## 再生成に必要な環境

Lean 4.24.0・mathlib v4.24.0 はプロジェクトの固定ファイルを使用する。
Python 側で今回検証した版は次のとおりである。

| パッケージ | 版 |
|---|---|
| leanblueprint | 0.0.20 |
| plasTeX | 3.1 |
| plastexdepgraph | 0.0.5 |
| pygraphviz | 2.0.3 |

Graphviz とその開発用ヘッダー、LuaLaTeX、LuaTeX-ja、latexmk、日本語
フォントを別途用意する。Python パッケージは例えば次で導入できる。

```sh
python3 -m pip install -r blueprint/requirements.txt
```

この配布物は Git リポジトリであることを要求しない。標準の
`leanblueprint` CLI は Git リポジトリを要求するため、ここでは
plasTeX と latexmk を直接呼び出す。

## 再生成の順序

以下は Lean プロジェクトのルートから実行する。まず数学の検証を行う。
大きい証明書を初めて検証する場合は、逐次ビルドする
`./scripts/verify.sh` を使う。

```sh
lake build
python3 blueprint/scripts/verify_lean_refs.py
python3 blueprint/scripts/check_structure.py
```

次に Blueprint を生成する。

```sh
cd blueprint/src
plastex -c plastex.cfg web.tex
latexmk -lualatex -outdir=../print print.tex
cd ../..
python3 blueprint/scripts/build_lean_links.py --verify-links
python3 blueprint/scripts/postprocess_web.py
python3 blueprint/scripts/check_html_links.py
```

HTML は `blueprint/web/`、PDF は `blueprint/print/print.pdf` に出力される。
`postprocess_web.py` は日本語指定、Lean 宣言リンクの明示的な
`index.html`、同梱 MathJax、概観図、静的依存グラフを整える。
`web/vendor/mathjax/` に同梱した MathJax の es5 ファイル群を維持する。
HTML 出力ディレクトリを削除した場合は、そのファイル群を復元してから
後処理を実行する。

`build_lean_links.py` は成功した宣言監査のデータを使い、元ソースが
変わっていないことを確認してから、宣言案内と行番号付きソース HTML を
生成する。本文の宣言リンク全件を検査する。宣言案内は JSON をネットワーク
取得せず、同梱 JavaScript を読むため、`web/index.html` を直接開く場合にも
ソースリンクは機能する。静的 HTTP サーバーを使って閲覧することもできる。

```sh
python3 -m http.server --directory blueprint/web 8000
```

その場合は `http://localhost:8000/` を開く。ソースや Blueprint を変更した
場合は、ビルド、宣言監査、構造検査、HTML/PDF 生成、ソースリンク生成、
HTML 後処理の順に再実行し、検証ログとソースハッシュを更新する。

Work Mode 固有の Lean 実行環境の回避策が必要な場合は、プロジェクトの
`tooling/ENVIRONMENT.md` と `scripts/README.md` を参照する。

## 検証資料

- `verification/lean_references.log`：Lean 宣言の実在と公理依存の検査。
- `verification/lean_references.json`：宣言の位置と入力・ソースのハッシュ。
- `verification/structure.json`：65 数学ノード、182 明示依存、ラベル・参照・DAG。
- `verification/lean_links.json`：宣言リンクの対応とソースページ生成。
- `verification/dependency_graph.dot`：113 表示辺の静的 SVG 入力。
- `verification/web_postprocess.json`：HTML 後処理と静的グラフの結果。

これらはコンパイル済みの実装と文書の対応を調べる資料である。
原稿全体の第三者による査読や、未形式化の幾何的補題の検証を意味しない。
