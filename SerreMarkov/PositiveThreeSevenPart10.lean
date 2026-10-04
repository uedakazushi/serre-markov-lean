import SerreMarkov.PositiveThreeSevenBase
namespace SerreMarkov.PositiveThreeSeven
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_14_0 : blockCheck 14 0=true := by decide +kernel
theorem checked_14_1 : blockCheck 14 1=true := by decide +kernel
theorem checked_14_2 : blockCheck 14 2=true := by decide +kernel
theorem checked_14_3 : blockCheck 14 3=true := by decide +kernel
theorem checked_14_4 : blockCheck 14 4=true := by decide +kernel
end SerreMarkov.PositiveThreeSeven
