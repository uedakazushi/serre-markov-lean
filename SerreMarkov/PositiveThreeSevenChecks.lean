import SerreMarkov.PositiveThreeSevenPart00
import SerreMarkov.PositiveThreeSevenPart01
import SerreMarkov.PositiveThreeSevenPart02
import SerreMarkov.PositiveThreeSevenPart03
import SerreMarkov.PositiveThreeSevenPart04
import SerreMarkov.PositiveThreeSevenPart05
import SerreMarkov.PositiveThreeSevenPart06
import SerreMarkov.PositiveThreeSevenPart07
import SerreMarkov.PositiveThreeSevenPart08
import SerreMarkov.PositiveThreeSevenPart09
import SerreMarkov.PositiveThreeSevenPart10
import SerreMarkov.PositiveThreeSevenPart11
import SerreMarkov.PositiveThreeSevenPart12
import SerreMarkov.PositiveThreeSevenPart13
namespace SerreMarkov.PositiveThreeSeven
theorem all_blocks_checked (b j : ℕ) (hb : 4≤b) (hb' : b≤17)
    (hj : 10*j≤cBound b) : blockCheck b j=true := by
  interval_cases b
  · norm_num [cBound] at hj
    have hjMax : j ≤ 22 := by omega
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
    · exact checked_4_16
    · exact checked_4_17
    · exact checked_4_18
    · exact checked_4_19
    · exact checked_4_20
    · exact checked_4_21
    · exact checked_4_22
  · norm_num [cBound] at hj
    have hjMax : j ≤ 16 := by omega
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
    · exact checked_5_12
    · exact checked_5_13
    · exact checked_5_14
    · exact checked_5_15
    · exact checked_5_16
  · norm_num [cBound] at hj
    have hjMax : j ≤ 14 := by omega
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
    · exact checked_6_10
    · exact checked_6_11
    · exact checked_6_12
    · exact checked_6_13
    · exact checked_6_14
  · norm_num [cBound] at hj
    have hjMax : j ≤ 12 := by omega
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
    · exact checked_7_9
    · exact checked_7_10
    · exact checked_7_11
    · exact checked_7_12
  · norm_num [cBound] at hj
    have hjMax : j ≤ 10 := by omega
    interval_cases j
    · exact checked_8_0
    · exact checked_8_1
    · exact checked_8_2
    · exact checked_8_3
    · exact checked_8_4
    · exact checked_8_5
    · exact checked_8_6
    · exact checked_8_7
    · exact checked_8_8
    · exact checked_8_9
    · exact checked_8_10
  · norm_num [cBound] at hj
    have hjMax : j ≤ 9 := by omega
    interval_cases j
    · exact checked_9_0
    · exact checked_9_1
    · exact checked_9_2
    · exact checked_9_3
    · exact checked_9_4
    · exact checked_9_5
    · exact checked_9_6
    · exact checked_9_7
    · exact checked_9_8
    · exact checked_9_9
  · norm_num [cBound] at hj
    have hjMax : j ≤ 8 := by omega
    interval_cases j
    · exact checked_10_0
    · exact checked_10_1
    · exact checked_10_2
    · exact checked_10_3
    · exact checked_10_4
    · exact checked_10_5
    · exact checked_10_6
    · exact checked_10_7
    · exact checked_10_8
  · norm_num [cBound] at hj
    have hjMax : j ≤ 7 := by omega
    interval_cases j
    · exact checked_11_0
    · exact checked_11_1
    · exact checked_11_2
    · exact checked_11_3
    · exact checked_11_4
    · exact checked_11_5
    · exact checked_11_6
    · exact checked_11_7
  · norm_num [cBound] at hj
    have hjMax : j ≤ 6 := by omega
    interval_cases j
    · exact checked_12_0
    · exact checked_12_1
    · exact checked_12_2
    · exact checked_12_3
    · exact checked_12_4
    · exact checked_12_5
    · exact checked_12_6
  · norm_num [cBound] at hj
    have hjMax : j ≤ 5 := by omega
    interval_cases j
    · exact checked_13_0
    · exact checked_13_1
    · exact checked_13_2
    · exact checked_13_3
    · exact checked_13_4
    · exact checked_13_5
  · norm_num [cBound] at hj
    have hjMax : j ≤ 4 := by omega
    interval_cases j
    · exact checked_14_0
    · exact checked_14_1
    · exact checked_14_2
    · exact checked_14_3
    · exact checked_14_4
  · norm_num [cBound] at hj
    have hjMax : j ≤ 3 := by omega
    interval_cases j
    · exact checked_15_0
    · exact checked_15_1
    · exact checked_15_2
    · exact checked_15_3
  · norm_num [cBound] at hj
    have hjMax : j ≤ 2 := by omega
    interval_cases j
    · exact checked_16_0
    · exact checked_16_1
    · exact checked_16_2
  · norm_num [cBound] at hj
    have hjMax : j ≤ 2 := by omega
    interval_cases j
    · exact checked_17_0
    · exact checked_17_1
    · exact checked_17_2
end SerreMarkov.PositiveThreeSeven
