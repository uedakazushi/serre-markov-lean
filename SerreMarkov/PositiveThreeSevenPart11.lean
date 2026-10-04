import SerreMarkov.PositiveThreeSevenBase
namespace SerreMarkov.PositiveThreeSeven
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_15_0 : blockCheck 15 0=true := by decide +kernel
theorem checked_15_1 : blockCheck 15 1=true := by decide +kernel
theorem checked_15_2 : blockCheck 15 2=true := by decide +kernel
theorem checked_15_3 : blockCheck 15 3=true := by decide +kernel
end SerreMarkov.PositiveThreeSeven
