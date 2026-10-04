import SerreMarkov.PositiveThreeSevenBase
namespace SerreMarkov.PositiveThreeSeven
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_16_0 : blockCheck 16 0=true := by decide +kernel
theorem checked_16_1 : blockCheck 16 1=true := by decide +kernel
theorem checked_16_2 : blockCheck 16 2=true := by decide +kernel
end SerreMarkov.PositiveThreeSeven
