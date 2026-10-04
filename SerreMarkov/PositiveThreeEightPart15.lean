import SerreMarkov.PositiveThreeEightBase
namespace SerreMarkov.PositiveThreeEight
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_19_0 : blockCheck 19 0=true := by decide +kernel
theorem checked_19_1 : blockCheck 19 1=true := by decide +kernel
theorem checked_19_2 : blockCheck 19 2=true := by decide +kernel
theorem checked_19_3 : blockCheck 19 3=true := by decide +kernel
end SerreMarkov.PositiveThreeEight
