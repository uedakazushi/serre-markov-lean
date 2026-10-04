# コンパイル診断

標準 lake build は成功。以下は独立した試験ファイルの今回の失敗。既存証明ソースは変更していない。

## AdjEntryTest.lean

```text
/workspace/scratch/41606fe60bc9/AdjEntryTest.lean:44:81: error: unsolved goals
z : Six
⊢ z.a * z.f ^ 2 - 4 * z.a + 2 * z.b * z.d - z.b * z.e * z.f - z.c * z.d * z.f + 2 * z.c * z.e =
    z.c * 2 * z.e - (z.a * 2 * 2 - z.a * z.f * z.f - z.b * z.d * 2 + z.b * z.f * z.e + z.c * z.d * z.f)

```

## CoreCheck.lean

```text
Nat.strongRecOn.{u} {motive : Nat → Sort u} (n : Nat) (ind : (n : Nat) → ((m : Nat) → m < n → motive m) → motive n) :
  motive n
/workspace/scratch/41606fe60bc9/CoreCheck.lean:3:7: error(lean.unknownIdentifier): Unknown constant `Nat.strongInductionOn`
/workspace/scratch/41606fe60bc9/CoreCheck.lean:4:7: error(lean.unknownIdentifier): Unknown constant `Nat.strong_induction_on`
/workspace/scratch/41606fe60bc9/CoreCheck.lean:5:7: error(lean.unknownIdentifier): Unknown constant `Nat.strongRec`
Int.add_zero (a : Int) : a + 0 = a
Int.natCast_add (n m : Nat) : ↑(n + m) = ↑n + ↑m
Int.natCast_one : ↑1 = 1

```

## その他

12秒の個別確認で成功5件、エラー2件、時間切れ25件。時間切れはコンパイル不能を意味しない。残りの作業用ファイルは未確認。全結果は PROBE_CHECKS.json。標準 import 外10モジュールの拡張ビルドは大きな証明書が完了しなかったため中断し、成功とも数学的失敗とも認定しない。
