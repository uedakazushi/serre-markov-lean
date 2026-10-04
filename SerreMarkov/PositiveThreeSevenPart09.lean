import SerreMarkov.PositiveThreeSevenBase
namespace SerreMarkov.PositiveThreeSeven
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_13_0 : blockCheck 13 0=true := by decide +kernel
theorem checked_13_1 : blockCheck 13 1=true := by decide +kernel
theorem checked_13_2 : blockCheck 13 2=true := by decide +kernel
theorem checked_13_3 : blockCheck 13 3=true := by decide +kernel
theorem checked_13_4 : blockCheck 13 4=true := by decide +kernel
theorem checked_13_5 : blockCheck 13 5=true := by decide +kernel
end SerreMarkov.PositiveThreeSeven
