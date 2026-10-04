import SerreMarkov.PositiveThreeSixPart00
import SerreMarkov.PositiveThreeSixPart01
import SerreMarkov.PositiveThreeSixPart02
import SerreMarkov.PositiveThreeSixPart03
import SerreMarkov.PositiveThreeSixPart04
import SerreMarkov.PositiveThreeSixPart05
import SerreMarkov.PositiveThreeSixPart06
import SerreMarkov.PositiveThreeSixPart07
import SerreMarkov.PositiveThreeSixPart08
import SerreMarkov.PositiveThreeSixPart09
import SerreMarkov.PositiveThreeSixPart10
namespace SerreMarkov.PositiveThreeSix
theorem all_blocks_checked (b j : ℕ) (hb : 4≤b) (hb' : b≤14)
    (hj : 10*j≤cBound b) : blockCheck b j=true := by
  interval_cases b
  · norm_num [cBound] at hj
    have hjMax : j ≤ 15 := by omega
    interval_cases j
    · exact checked_4_0
    · exact checked_4_1
    · exact checked_4_2
    · exact checked_4_3
    · exact checked_4_4
    · exact checked_4_5
    · exact checked_4_6
    · exact checked_4_7
    · exact checked_4_8
    · exact checked_4_9
    · exact checked_4_10
    · exact checked_4_11
    · exact checked_4_12
    · exact checked_4_13
    · exact checked_4_14
    · exact checked_4_15
  · norm_num [cBound] at hj
    have hjMax : j ≤ 11 := by omega
    interval_cases j
    · exact checked_5_0
    · exact checked_5_1
    · exact checked_5_2
    · exact checked_5_3
    · exact checked_5_4
    · exact checked_5_5
    · exact checked_5_6
    · exact checked_5_7
    · exact checked_5_8
    · exact checked_5_9
    · exact checked_5_10
    · exact checked_5_11
  · norm_num [cBound] at hj
    have hjMax : j ≤ 9 := by omega
    interval_cases j
    · exact checked_6_0
    · exact checked_6_1
    · exact checked_6_2
    · exact checked_6_3
    · exact checked_6_4
    · exact checked_6_5
    · exact checked_6_6
    · exact checked_6_7
    · exact checked_6_8
    · exact checked_6_9
  · norm_num [cBound] at hj
    have hjMax : j ≤ 8 := by omega
    interval_cases j
    · exact checked_7_0
    · exact checked_7_1
    · exact checked_7_2
    · exact checked_7_3
    · exact checked_7_4
    · exact checked_7_5
    · exact checked_7_6
    · exact checked_7_7
    · exact checked_7_8
  · norm_num [cBound] at hj
    have hjMax : j ≤ 7 := by omega
    interval_cases j
    · exact checked_8_0
    · exact checked_8_1
    · exact checked_8_2
    · exact checked_8_3
    · exact checked_8_4
    · exact checked_8_5
    · exact checked_8_6
    · exact checked_8_7
  · norm_num [cBound] at hj
    have hjMax : j ≤ 6 := by omega
    interval_cases j
    · exact checked_9_0
    · exact checked_9_1
    · exact checked_9_2
    · exact checked_9_3
    · exact checked_9_4
    · exact checked_9_5
    · exact checked_9_6
  · norm_num [cBound] at hj
    have hjMax : j ≤ 5 := by omega
    interval_cases j
    · exact checked_10_0
    · exact checked_10_1
    · exact checked_10_2
    · exact checked_10_3
    · exact checked_10_4
    · exact checked_10_5
  · norm_num [cBound] at hj
    have hjMax : j ≤ 4 := by omega
    interval_cases j
    · exact checked_11_0
    · exact checked_11_1
    · exact checked_11_2
    · exact checked_11_3
    · exact checked_11_4
  · norm_num [cBound] at hj
    have hjMax : j ≤ 3 := by omega
    interval_cases j
    · exact checked_12_0
    · exact checked_12_1
    · exact checked_12_2
    · exact checked_12_3
  · norm_num [cBound] at hj
    have hjMax : j ≤ 2 := by omega
    interval_cases j
    · exact checked_13_0
    · exact checked_13_1
    · exact checked_13_2
  · norm_num [cBound] at hj
    have hjMax : j ≤ 1 := by omega
    interval_cases j
    · exact checked_14_0
    · exact checked_14_1
end SerreMarkov.PositiveThreeSix
