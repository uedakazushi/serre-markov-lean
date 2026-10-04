import SerreMarkov.PositiveThreeFiveBase
namespace SerreMarkov.PositiveThreeFive
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem checked_8_0 : blockCheck 8 0=true := by decide +kernel
theorem checked_8_1 : blockCheck 8 1=true := by decide +kernel
theorem checked_8_2 : blockCheck 8 2=true := by decide +kernel
theorem checked_8_3 : blockCheck 8 3=true := by decide +kernel
theorem checked_8_4 : blockCheck 8 4=true := by decide +kernel
end SerreMarkov.PositiveThreeFive
