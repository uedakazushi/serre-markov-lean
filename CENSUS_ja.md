# 指数12の有限置換分類の形式化

主定理は `SerreMarkov.IndexTwelve.complete_index_twelve_census_two_cycles` です。頂点集合は `Fin 12`、
\[
\beta=(0\,1\,2)(3\,4\,5)(6\,7\,8)(9\,10\,11)
\]
を固定しています。任意の写像 \(\alpha\) について、

- \(\alpha^2=1\)、\(\alpha\) に固定点がないこと、
- \(\alpha,\beta\) の実際の生成元語によって任意の二頂点を結べること、
- \(\alpha\beta\) が、全12頂点を覆う二つの互いに素な非空単純巡回で記述されること

を仮定すると、\(\beta\) を保つ同時共役による代表元が五つの表の中に一意に存在することを証明しています。結論の共役は具体的な全単射 `g : Fin 12 → Fin 12` です。

完全性は一般的なパートナー列挙の帰納法 `enumerateInvolutions_complete` によって保証しています。これは有限台を持つ任意の固定点なし対合を扱う補題です。`allMatchingInvolutions_complete` により対象となる全ての \(\alpha\) が候補列に入ります。

次に、証明書の \(\alpha\) 列がこの再帰的候補列と等しいことを `census_projection_eq_enumeration` で証明しています。関数を12個の自然数の列へ写す符号化の単射性を証明し、最初のパートナーの選び方による11個の枝（各945件）を個別にカーネル検査してから、一般的なリスト分割定理によって結合しています。全体の巨大な関数列を一度に比較する必要はありません。候補列の長さが10,395であることも `allMatchingInvolutions_length` で証明しています。`scripts/generate_census.py` と `scripts/generate_census_coverage.py` は補助プログラムであり、その正しさを前提にはしていません。

各候補には、次のいずれかの証明書が付いています。

| 証明書 | 内容 | 検査された個数 |
|---|---|---:|
| 非推移性 | 両生成元で不変な全射二色写像 | 675 |
| 二巡回条件との矛盾 | \(\alpha\beta\) で不変な全射四色写像 | 5,184 |
| 五代表元への帰着 | \(\alpha,\beta\) を実際に同時共役する全単射 | 4,536 |

個数は `census_witness_counts` でカーネル検査しています。二色証明書が語による推移性と矛盾すること、四色証明書が二つの巡回軌道による被覆と矛盾することは、一般補題として証明しています。有限 Boolean 検査の意味は `WitnessCheck_correct` で証明され、その上で全証明書を `decide +kernel` で検査しています。`native_decide` やコンパイラを信用する公理は使用していません。

五代表元の相違は、\((\alpha\beta)^n\) の固定点数（\(n=1,2,3,4\)）の共役不変性によります。これにより、代表元の存在だけでなく一意性も得ています。各代表元の条件と二巡回のリストも別に証明されています。

任意の \(\beta\) に対する版は `SerreMarkov.IndexTwelve.arbitrary_beta_census_unique` です。\(\beta^3=1\) かつ固定点がないことから巡回型が \(3^4\) であることを証明し、Mathlib の巡回型による置換の共役分類によって上記の固定 \(\beta\) へ正規化します。同じ置換によって \(\alpha\)、語による推移性、二つの巡回軌道による被覆を運び、五代表元の存在と一意性を得ます。この正規化と transport は `BetaNormalization.lean`、分類との接続は `ArbitraryBetaCensus.lean` にあります。

この主定理の対象は有限置換問題です。`PSL₂(ℤ)` の部分群との対応、および Serre 格子からこの有限問題へ帰着する大域的幾何は、この主定理の仮定や結論に含まれていません。

別モジュール `ModularCosets.lean` で、実際の抽象提示群 `⟨s,t | s²=t³=1⟩` の群作用と剰余類の橋を証明しました。推移的置換対から stabilizer の指数 `12` と十二点への同変な同値を得て、逆に指数 `12` の部分群から作った置換対の stabilizer が元の部分群に等しいことを証明しています。同時置換共役と群内の stabilizer 共役も同値です。

`SerreMarkov.ModularCosets.abstract_subgroup_census_unique` は、この抽象群の任意の指数 `12` 部分群について、`s,t` の剰余類作用に固定点がなく、`st` が高々二つの実際の軌道で剰余類空間を覆うなら、五つの具体的な `representativeSubgroup` の共役類の中に一意に入ることを述べます。五代表すべての仮定と、代表の非共役性も証明済みです。

抽象提示群と実際の `PSL₂(ℤ)` の同型は `ModularPingPong.presentationPSLEquiv` で完成しました。整数Euclidによる生成と自由積のping-pongを使うカーネル証明です。`ModularPSLCensus.subgroup_census_unique` により、実PSL部分群についても上記の指数・固定点・巡回軌道条件の下で五共役類の存在と一意性を証明しました。任意正側格子から実PSL部分群を構成する整数化も完成していますが、その部分群が指数12などの条件を満たすこと、および群共役から実変異軌道への復元は未証明です。

再検査は `lake build SerreMarkov.ArbitraryBetaCensus` です。証明書を再生成する場合は、プロジェクトのルートで `python scripts/generate_census.py` と `python scripts/generate_census_coverage.py` を実行してから同じ Lean ビルドを行います。証明書と枝の比較のモジュールは鎖状に依存させ、巨大な並列ビルドを避けています。

`CensusAudit.lean` の `#print axioms` により、完全列挙・証明書列との同一性・全証明書の検査・主定理は `propext`, `Classical.choice`, `Quot.sound` のみに依存することを確認しました。`sorryAx` や `Lean.ofReduceBool` は含まれません。

抽象群の橋と部分群分類は `lake build SerreMarkov.ModularCosets`、その公理監査は `lake env lean ModularCosetsAudit.lean` で再検査できます。こちらも使用公理は同じ三つのみです。

ここで未形式化として挙げた正側格子から指数・固定点・カスプ条件への帰着と、群共役から実変異軌道への復元は、原稿の元の幾何的証明を再現するための工程である。主分類は最小高さ・順序帰着・普遍多項式証明書・有限終端分類を使う `PositiveClassificationFull` の代数的経路で完成し、`FullClassification` に全三型・ファイバー・決定手続きへ接続したため、この幾何的工程を必要としない。この有限 census、明示条件下の部分群分類、無条件の正側主分類は、それぞれ別の定理として区別する。原稿の幾何補題や dg 付録まで形式化済みという意味ではない。
