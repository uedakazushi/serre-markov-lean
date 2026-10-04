import SerreMarkov.PositiveThreeFourPart00
import SerreMarkov.PositiveThreeFourPart01
import SerreMarkov.PositiveThreeFourPart02
import SerreMarkov.PositiveThreeFourPart03
import SerreMarkov.PositiveThreeFourPart04
import SerreMarkov.PositiveThreeFourPart05
import SerreMarkov.PositiveThreeFourPart06
import SerreMarkov.PositiveThreeFourPart07
import SerreMarkov.PositiveThreeFourPart08
import SerreMarkov.PositiveThreeFourPart09
import SerreMarkov.PositiveThreeFourPart10
import SerreMarkov.PositiveThreeFourPart11
import SerreMarkov.PositiveThreeFourPart12
import SerreMarkov.PositiveThreeFourPart13
import SerreMarkov.PositiveThreeFourPart14
import SerreMarkov.PositiveThreeFourPart15
import SerreMarkov.PositiveThreeFourPart16
import SerreMarkov.PositiveThreeFourPart17
import SerreMarkov.PositiveThreeFourPart18
import SerreMarkov.PositiveThreeFourPart19
namespace SerreMarkov.PositiveThreeFour

theorem all_blocks_checked (b k j : ℕ) (hb : 4≤b) (hb' : b≤8) (hk : k<4) (hj : j<11) :
    blockCheck b k j=true := by
  interval_cases b <;> interval_cases k <;> interval_cases j
  · exact checked_4_0_0
  · exact checked_4_0_1
  · exact checked_4_0_2
  · exact checked_4_0_3
  · exact checked_4_0_4
  · exact checked_4_0_5
  · exact checked_4_0_6
  · exact checked_4_0_7
  · exact checked_4_0_8
  · exact checked_4_0_9
  · exact checked_4_0_10
  · exact checked_4_1_0
  · exact checked_4_1_1
  · exact checked_4_1_2
  · exact checked_4_1_3
  · exact checked_4_1_4
  · exact checked_4_1_5
  · exact checked_4_1_6
  · exact checked_4_1_7
  · exact checked_4_1_8
  · exact checked_4_1_9
  · exact checked_4_1_10
  · exact checked_4_2_0
  · exact checked_4_2_1
  · exact checked_4_2_2
  · exact checked_4_2_3
  · exact checked_4_2_4
  · exact checked_4_2_5
  · exact checked_4_2_6
  · exact checked_4_2_7
  · exact checked_4_2_8
  · exact checked_4_2_9
  · exact checked_4_2_10
  · exact checked_4_3_0
  · exact checked_4_3_1
  · exact checked_4_3_2
  · exact checked_4_3_3
  · exact checked_4_3_4
  · exact checked_4_3_5
  · exact checked_4_3_6
  · exact checked_4_3_7
  · exact checked_4_3_8
  · exact checked_4_3_9
  · exact checked_4_3_10
  · exact checked_5_0_0
  · exact checked_5_0_1
  · exact checked_5_0_2
  · exact checked_5_0_3
  · exact checked_5_0_4
  · exact checked_5_0_5
  · exact checked_5_0_6
  · exact checked_5_0_7
  · exact checked_5_0_8
  · exact checked_5_0_9
  · exact checked_5_0_10
  · exact checked_5_1_0
  · exact checked_5_1_1
  · exact checked_5_1_2
  · exact checked_5_1_3
  · exact checked_5_1_4
  · exact checked_5_1_5
  · exact checked_5_1_6
  · exact checked_5_1_7
  · exact checked_5_1_8
  · exact checked_5_1_9
  · exact checked_5_1_10
  · exact checked_5_2_0
  · exact checked_5_2_1
  · exact checked_5_2_2
  · exact checked_5_2_3
  · exact checked_5_2_4
  · exact checked_5_2_5
  · exact checked_5_2_6
  · exact checked_5_2_7
  · exact checked_5_2_8
  · exact checked_5_2_9
  · exact checked_5_2_10
  · exact checked_5_3_0
  · exact checked_5_3_1
  · exact checked_5_3_2
  · exact checked_5_3_3
  · exact checked_5_3_4
  · exact checked_5_3_5
  · exact checked_5_3_6
  · exact checked_5_3_7
  · exact checked_5_3_8
  · exact checked_5_3_9
  · exact checked_5_3_10
  · exact checked_6_0_0
  · exact checked_6_0_1
  · exact checked_6_0_2
  · exact checked_6_0_3
  · exact checked_6_0_4
  · exact checked_6_0_5
  · exact checked_6_0_6
  · exact checked_6_0_7
  · exact checked_6_0_8
  · exact checked_6_0_9
  · exact checked_6_0_10
  · exact checked_6_1_0
  · exact checked_6_1_1
  · exact checked_6_1_2
  · exact checked_6_1_3
  · exact checked_6_1_4
  · exact checked_6_1_5
  · exact checked_6_1_6
  · exact checked_6_1_7
  · exact checked_6_1_8
  · exact checked_6_1_9
  · exact checked_6_1_10
  · exact checked_6_2_0
  · exact checked_6_2_1
  · exact checked_6_2_2
  · exact checked_6_2_3
  · exact checked_6_2_4
  · exact checked_6_2_5
  · exact checked_6_2_6
  · exact checked_6_2_7
  · exact checked_6_2_8
  · exact checked_6_2_9
  · exact checked_6_2_10
  · exact checked_6_3_0
  · exact checked_6_3_1
  · exact checked_6_3_2
  · exact checked_6_3_3
  · exact checked_6_3_4
  · exact checked_6_3_5
  · exact checked_6_3_6
  · exact checked_6_3_7
  · exact checked_6_3_8
  · exact checked_6_3_9
  · exact checked_6_3_10
  · exact checked_7_0_0
  · exact checked_7_0_1
  · exact checked_7_0_2
  · exact checked_7_0_3
  · exact checked_7_0_4
  · exact checked_7_0_5
  · exact checked_7_0_6
  · exact checked_7_0_7
  · exact checked_7_0_8
  · exact checked_7_0_9
  · exact checked_7_0_10
  · exact checked_7_1_0
  · exact checked_7_1_1
  · exact checked_7_1_2
  · exact checked_7_1_3
  · exact checked_7_1_4
  · exact checked_7_1_5
  · exact checked_7_1_6
  · exact checked_7_1_7
  · exact checked_7_1_8
  · exact checked_7_1_9
  · exact checked_7_1_10
  · exact checked_7_2_0
  · exact checked_7_2_1
  · exact checked_7_2_2
  · exact checked_7_2_3
  · exact checked_7_2_4
  · exact checked_7_2_5
  · exact checked_7_2_6
  · exact checked_7_2_7
  · exact checked_7_2_8
  · exact checked_7_2_9
  · exact checked_7_2_10
  · exact checked_7_3_0
  · exact checked_7_3_1
  · exact checked_7_3_2
  · exact checked_7_3_3
  · exact checked_7_3_4
  · exact checked_7_3_5
  · exact checked_7_3_6
  · exact checked_7_3_7
  · exact checked_7_3_8
  · exact checked_7_3_9
  · exact checked_7_3_10
  · exact checked_8_0_0
  · exact checked_8_0_1
  · exact checked_8_0_2
  · exact checked_8_0_3
  · exact checked_8_0_4
  · exact checked_8_0_5
  · exact checked_8_0_6
  · exact checked_8_0_7
  · exact checked_8_0_8
  · exact checked_8_0_9
  · exact checked_8_0_10
  · exact checked_8_1_0
  · exact checked_8_1_1
  · exact checked_8_1_2
  · exact checked_8_1_3
  · exact checked_8_1_4
  · exact checked_8_1_5
  · exact checked_8_1_6
  · exact checked_8_1_7
  · exact checked_8_1_8
  · exact checked_8_1_9
  · exact checked_8_1_10
  · exact checked_8_2_0
  · exact checked_8_2_1
  · exact checked_8_2_2
  · exact checked_8_2_3
  · exact checked_8_2_4
  · exact checked_8_2_5
  · exact checked_8_2_6
  · exact checked_8_2_7
  · exact checked_8_2_8
  · exact checked_8_2_9
  · exact checked_8_2_10
  · exact checked_8_3_0
  · exact checked_8_3_1
  · exact checked_8_3_2
  · exact checked_8_3_3
  · exact checked_8_3_4
  · exact checked_8_3_5
  · exact checked_8_3_6
  · exact checked_8_3_7
  · exact checked_8_3_8
  · exact checked_8_3_9
  · exact checked_8_3_10
end SerreMarkov.PositiveThreeFour
