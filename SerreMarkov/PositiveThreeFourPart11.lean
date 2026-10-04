import SerreMarkov.PositiveThreeFourBase

namespace SerreMarkov.PositiveThreeFour
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked_6_3_0 : blockCheck 6 3 0=true := by decide +kernel
theorem checked_6_3_1 : blockCheck 6 3 1=true := by decide +kernel
theorem checked_6_3_2 : blockCheck 6 3 2=true := by decide +kernel
theorem checked_6_3_3 : blockCheck 6 3 3=true := by decide +kernel
theorem checked_6_3_4 : blockCheck 6 3 4=true := by decide +kernel
theorem checked_6_3_5 : blockCheck 6 3 5=true := by decide +kernel
theorem checked_6_3_6 : blockCheck 6 3 6=true := by decide +kernel
theorem checked_6_3_7 : blockCheck 6 3 7=true := by decide +kernel
theorem checked_6_3_8 : blockCheck 6 3 8=true := by decide +kernel
theorem checked_6_3_9 : blockCheck 6 3 9=true := by decide +kernel
theorem checked_6_3_10 : blockCheck 6 3 10=true := by decide +kernel
end SerreMarkov.PositiveThreeFour
