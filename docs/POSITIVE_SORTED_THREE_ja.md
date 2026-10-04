# 整列した第一係数 3 の停止点

`SerreMarkov/PositiveSortedThreeLarge.lean` は、正の chamber の解で
`a = 3`、`d ≤ c`、長さ 3 以下の全変異語で高さが下がらない場合に、
`d ≤ 8 ∨ f ≤ 5` を証明する。元の高さの上界を仮定しない。

公開補題は namespace `SerreMarkov.PositiveSortedThreeLarge` 内の次の二つ。

- `a_three_sorted_large_impossible`：上記条件に `9 ≤ d` と `6 ≤ f` を加えると矛盾。
- `a_three_sorted_small_boundary`：上記条件から `d ≤ 8 ∨ f ≤ 5`。

`PositiveThreeTriangles.a_three_incident_bounds` により `4 ≤ b,e` が従うので、
排除する領域を `(a,b,c,d,e,f) = (3,4+B,9+D+C,9+D,4+E,6+F)`、
`B,C,D,E,F ≥ 0` と書く。`q2 = 4` と `q2 = -4` の双方に対し、
非負多項式と実際の短い変異語の高さ不等式を用いた次数 6 の恒等式を
有理数上で生成し、分母を払って Lean の整数多項式恒等式として検証した。
探索器の出力を信頼する必要はない。

再現用ファイル：

- `scripts/search_positive_sorted_three_large.py`
- `scripts/certificates/positive_sorted_three_large_plus.json`
- `scripts/certificates/positive_sorted_three_large_minus.json`
- `scripts/generate_positive_sorted_three_large.py`

正式な `lake build SerreMarkov.PositiveSortedThreeLarge` は成功。
`PositiveSortedThreeAudit.lean` で公開両補題の依存公理を確認し、
`propext`、`Classical.choice`、`Quot.sound` のみだった。
この補題の結論を、既に検証済みの有限 endpoint 分類へ接続することで
整列した `a = 3` の枝を閉じられる。他の第一係数の枝の分類は別モジュールで扱う。
