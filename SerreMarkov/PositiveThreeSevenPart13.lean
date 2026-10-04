import SerreMarkov.PositiveThreeSevenBase
namespace SerreMarkov.PositiveThreeSeven
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_17_0 : blockCheck 17 0=true := by decide +kernel
theorem checked_17_1 : blockCheck 17 1=true := by decide +kernel
theorem checked_17_2 : blockCheck 17 2=true := by decide +kernel
end SerreMarkov.PositiveThreeSeven
