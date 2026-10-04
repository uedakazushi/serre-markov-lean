import SerreMarkov.PositiveThreeFivePart00
import SerreMarkov.PositiveThreeFivePart01
import SerreMarkov.PositiveThreeFivePart02
import SerreMarkov.PositiveThreeFivePart03
import SerreMarkov.PositiveThreeFivePart04
import SerreMarkov.PositiveThreeFivePart05
import SerreMarkov.PositiveThreeFivePart06
import SerreMarkov.PositiveThreeFivePart07
namespace SerreMarkov.PositiveThreeFive
theorem all_blocks_checked (b j : ℕ) (hb : 4≤b) (hb' : b≤11)
    (hj : 10*j≤cBound b) : blockCheck b j=true := by
  interval_cases b
  · norm_num [cBound] at hj
    have hjMax : j ≤ 10 := by omega
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
  · norm_num [cBound] at hj
    have hjMax : j ≤ 7 := by omega
    interval_cases j
    · exact checked_5_0
    · exact checked_5_1
    · exact checked_5_2
    · exact checked_5_3
    · exact checked_5_4
    · exact checked_5_5
    · exact checked_5_6
    · exact checked_5_7
  · norm_num [cBound] at hj
    have hjMax : j ≤ 6 := by omega
    interval_cases j
    · exact checked_6_0
    · exact checked_6_1
    · exact checked_6_2
    · exact checked_6_3
    · exact checked_6_4
    · exact checked_6_5
    · exact checked_6_6
  · norm_num [cBound] at hj
    have hjMax : j ≤ 5 := by omega
    interval_cases j
    · exact checked_7_0
    · exact checked_7_1
    · exact checked_7_2
    · exact checked_7_3
    · exact checked_7_4
    · exact checked_7_5
  · norm_num [cBound] at hj
    have hjMax : j ≤ 4 := by omega
    interval_cases j
    · exact checked_8_0
    · exact checked_8_1
    · exact checked_8_2
    · exact checked_8_3
    · exact checked_8_4
  · norm_num [cBound] at hj
    have hjMax : j ≤ 3 := by omega
    interval_cases j
    · exact checked_9_0
    · exact checked_9_1
    · exact checked_9_2
    · exact checked_9_3
  · norm_num [cBound] at hj
    have hjMax : j ≤ 2 := by omega
    interval_cases j
    · exact checked_10_0
    · exact checked_10_1
    · exact checked_10_2
  · norm_num [cBound] at hj
    have hjMax : j ≤ 1 := by omega
    interval_cases j
    · exact checked_11_0
    · exact checked_11_1
end SerreMarkov.PositiveThreeFive
